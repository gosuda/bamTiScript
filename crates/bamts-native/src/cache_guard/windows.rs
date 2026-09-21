use std::{
    ffi::OsStr,
    fs::{self, File, OpenOptions},
    io::{self, Read, Write},
    mem::size_of,
    os::windows::{ffi::OsStrExt, fs::OpenOptionsExt, io::AsRawHandle},
    path::{Path, PathBuf},
    ptr,
    sync::atomic::{AtomicU64, Ordering},
    time::{SystemTime, UNIX_EPOCH},
};

use windows::{
    Wdk::Storage::FileSystem::{
        FILE_RENAME_INFORMATION, FileRenameInformation, NtSetInformationFile,
    },
    Win32::{
        Foundation::{CloseHandle, HANDLE, HLOCAL, LocalFree, RtlNtStatusToDosError},
        Security::{
            ACCESS_ALLOWED_ACE, ACE_HEADER, ACL,
            Authorization::{
                ConvertSidToStringSidW, ConvertStringSecurityDescriptorToSecurityDescriptorW,
                ConvertStringSidToSidW, GetSecurityInfo, SDDL_REVISION_1, SE_FILE_OBJECT,
            },
            CONTAINER_INHERIT_ACE, CopySid, CreateWellKnownSid, DACL_SECURITY_INFORMATION,
            EqualSid, GENERIC_MAPPING, GetAce, GetLengthSid, GetSecurityDescriptorControl,
            GetTokenInformation, INHERIT_ONLY_ACE, MapGenericMask, OBJECT_INHERIT_ACE,
            OWNER_SECURITY_INFORMATION, PSECURITY_DESCRIPTOR, PSID, SE_DACL_PRESENT,
            SECURITY_ATTRIBUTES, TOKEN_QUERY, TOKEN_USER, TokenUser, WinBuiltinAdministratorsSid,
            WinCreatorOwnerSid, WinLocalSystemSid,
        },
        Storage::FileSystem::{
            CreateDirectoryW, DELETE, FILE_ALL_ACCESS, FILE_APPEND_DATA, FILE_ATTRIBUTE_DIRECTORY,
            FILE_ATTRIBUTE_REPARSE_POINT, FILE_ATTRIBUTE_TAG_INFO, FILE_DELETE_CHILD,
            FILE_FLAG_BACKUP_SEMANTICS, FILE_FLAG_OPEN_REPARSE_POINT, FILE_GENERIC_EXECUTE,
            FILE_GENERIC_READ, FILE_GENERIC_WRITE, FILE_SHARE_READ, FILE_WRITE_ATTRIBUTES,
            FILE_WRITE_DATA, FILE_WRITE_EA, FileAttributeTagInfo, GetFileInformationByHandleEx,
            READ_CONTROL, WRITE_DAC, WRITE_OWNER,
        },
        System::{
            IO::IO_STATUS_BLOCK,
            SystemServices::{ACCESS_ALLOWED_ACE_TYPE, ACCESS_DENIED_ACE_TYPE},
            Threading::{GetCurrentProcess, OpenProcessToken},
        },
    },
    core::{PCWSTR, PWSTR},
};

use super::{CacheGuardError, HeldArchive};

const MAX_CHAIN_DEPTH: usize = 32;
const MAX_NAME_ATTEMPTS: usize = 128;
const COMPARE_BUFFER_BYTES: usize = 64 * 1024;
// Windows Modules Installer owns protected system directories, including the
// system-drive root on current Windows images. It is not a private-cache owner.
const TRUSTED_INSTALLER_SID: &str =
    "S-1-5-80-956008885-3418522649-1831038044-1853292631-2271478464";
static NEXT_INVOCATION_ID: AtomicU64 = AtomicU64::new(0);

#[derive(Clone, Copy)]
enum DirectoryPolicy {
    Ancestor,
    Cache,
}

#[derive(Debug)]
pub struct PrivateCacheRoot {
    path: PathBuf,
    _chain: Vec<File>,
    trusted: TrustedSids,
}

#[derive(Debug)]
pub struct GuardedDir {
    path: PathBuf,
    hold: Option<File>,
    cleanup: DirectoryCleanup,
}

#[derive(Clone, Copy, Debug)]
enum DirectoryCleanup {
    Keep,
    Remove,
}

impl GuardedDir {
    #[must_use]
    pub fn path(&self) -> &Path {
        &self.path
    }

    pub fn close_and_remove(self) {
        drop(self);
    }
}
impl Drop for GuardedDir {
    fn drop(&mut self) {
        drop(self.hold.take());
        if matches!(self.cleanup, DirectoryCleanup::Remove) {
            let _ = fs::remove_dir_all(&self.path);
        }
    }
}

#[derive(Debug)]
pub struct GuardedFile {
    path: PathBuf,
    _hold: File,
}

impl GuardedFile {
    #[must_use]
    pub fn path(&self) -> &Path {
        &self.path
    }
}

#[derive(Debug)]
struct TrustedSids {
    user: OwnedSid,
    system: OwnedSid,
    administrators: OwnedSid,
    creator_owner: OwnedSid,
    trusted_installer: OwnedSid,
}

#[derive(Debug)]
struct OwnedSid {
    words: Vec<usize>,
}

impl OwnedSid {
    fn with_byte_capacity(byte_len: usize) -> Self {
        Self {
            words: vec![0; byte_len.div_ceil(size_of::<usize>())],
        }
    }

    fn as_sid(&self) -> PSID {
        PSID(self.words.as_ptr().cast_mut().cast())
    }

    fn as_mut_sid(&mut self) -> PSID {
        PSID(self.words.as_mut_ptr().cast())
    }
}

impl PrivateCacheRoot {
    pub fn acquire(path: &Path) -> Result<Self, CacheGuardError> {
        let trusted = TrustedSids::current()?;
        let parent = path
            .parent()
            .ok_or_else(|| CacheGuardError::NotADirectory {
                path: path.to_owned(),
            })?;
        fs::create_dir_all(parent).map_err(|source| CacheGuardError::io(parent, source))?;
        if !path.exists() {
            create_private_directory(path, &trusted)?;
        }

        let canonical =
            fs::canonicalize(path).map_err(|source| CacheGuardError::io(path, source))?;
        let ancestors: Vec<PathBuf> = canonical.ancestors().map(Path::to_owned).collect();
        if ancestors.len() > MAX_CHAIN_DEPTH {
            return Err(CacheGuardError::io(
                &canonical,
                io::Error::new(io::ErrorKind::InvalidData, "cache path is too deep"),
            ));
        }

        let mut chain = Vec::with_capacity(ancestors.len());
        for ancestor in ancestors.iter().rev() {
            let file = open_pinned_path(ancestor, true)?;
            let policy = if ancestor == &canonical {
                DirectoryPolicy::Cache
            } else {
                DirectoryPolicy::Ancestor
            };
            validate_handle(&file, ancestor, true, policy, &trusted)?;
            chain.push(file);
        }
        Ok(Self {
            path: canonical,
            _chain: chain,
            trusted,
        })
    }

    #[must_use]
    pub fn root_path(&self) -> &Path {
        &self.path
    }

    pub fn guard_child_dir(&self, name: &OsStr) -> Result<GuardedDir, CacheGuardError> {
        validate_single_component(name, &self.path)?;
        let path = self.path.join(name);
        match fs::create_dir(&path) {
            Ok(()) => {}
            Err(error) if error.kind() == io::ErrorKind::AlreadyExists => {}
            Err(source) => return Err(CacheGuardError::io(&path, source)),
        }
        let hold = open_pinned_path(&path, true)?;
        validate_handle(&hold, &path, true, DirectoryPolicy::Cache, &self.trusted)?;
        Ok(GuardedDir {
            path,
            hold: Some(hold),
            cleanup: DirectoryCleanup::Keep,
        })
    }

    pub fn create_invocation_dir(&self, prefix: &str) -> Result<GuardedDir, CacheGuardError> {
        validate_single_component(OsStr::new(prefix), &self.path)?;
        let timestamp = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .map_err(|source| {
                CacheGuardError::io(
                    &self.path,
                    io::Error::other(format!("system clock precedes the Unix epoch: {source}")),
                )
            })?
            .as_nanos();
        let invocation = NEXT_INVOCATION_ID.fetch_add(1, Ordering::Relaxed);
        for attempt in 0..MAX_NAME_ATTEMPTS {
            let path = self.path.join(format!(
                ".{prefix}-{}-{timestamp}-{invocation}-{attempt}",
                std::process::id()
            ));
            match fs::create_dir(&path) {
                Ok(()) => {
                    let hold = open_pinned_path(&path, true)?;
                    validate_handle(&hold, &path, true, DirectoryPolicy::Cache, &self.trusted)?;
                    return Ok(GuardedDir {
                        path,
                        hold: Some(hold),
                        cleanup: DirectoryCleanup::Remove,
                    });
                }
                Err(error) if error.kind() == io::ErrorKind::AlreadyExists => continue,
                Err(source) => return Err(CacheGuardError::io(&path, source)),
            }
        }
        Err(CacheGuardError::NameAttemptsExhausted {
            parent: self.path.clone(),
        })
    }

    pub fn materialize_archive(
        &self,
        directory: &GuardedDir,
        file_name: &str,
        expected: &[u8],
    ) -> Result<HeldArchive, CacheGuardError> {
        validate_single_component(OsStr::new(file_name), directory.path())?;
        let path = directory.path().join(file_name);
        if let Ok(mut file) = open_pinned_path(&path, false) {
            validate_handle(&file, &path, false, DirectoryPolicy::Cache, &self.trusted)?;
            if bytes_equal(&mut file, expected)
                .map_err(|source| CacheGuardError::io(&path, source))?
            {
                return Ok(HeldArchive::held(GuardedFile { path, _hold: file }));
            }
            drop(file);
            fs::remove_file(&path).map_err(|source| CacheGuardError::io(&path, source))?;
        }

        write_archive_atomic(directory.path(), &path, expected)?;
        let mut file = open_pinned_path(&path, false)?;
        validate_handle(&file, &path, false, DirectoryPolicy::Cache, &self.trusted)?;
        if !bytes_equal(&mut file, expected).map_err(|source| CacheGuardError::io(&path, source))? {
            return Err(CacheGuardError::ArchiveMismatch { path });
        }
        Ok(HeldArchive::held(GuardedFile { path, _hold: file }))
    }

    pub fn verify_executable(&self, path: &Path) -> Result<(), CacheGuardError> {
        let file = open_pinned_path(path, false)?;
        validate_handle(&file, path, false, DirectoryPolicy::Cache, &self.trusted)
    }

    pub fn fallback_user_key() -> Result<String, CacheGuardError> {
        let user = current_user_sid()?;
        sid_to_string(user.as_sid(), Path::new("<current-user>"))
    }
}

impl TrustedSids {
    fn current() -> Result<Self, CacheGuardError> {
        Ok(Self {
            user: current_user_sid()?,
            system: well_known_sid(WinLocalSystemSid)?,
            administrators: well_known_sid(WinBuiltinAdministratorsSid)?,
            creator_owner: well_known_sid(WinCreatorOwnerSid)?,
            trusted_installer: parse_sid(TRUSTED_INSTALLER_SID)?,
        })
    }

    fn owner_is_trusted(&self, candidate: PSID, policy: DirectoryPolicy) -> bool {
        [
            self.user.as_sid(),
            self.system.as_sid(),
            self.administrators.as_sid(),
        ]
        .into_iter()
        .any(|trusted| equal_sid(candidate, trusted))
            || (matches!(policy, DirectoryPolicy::Ancestor)
                && equal_sid(candidate, self.trusted_installer.as_sid()))
    }

    fn mutation_is_trusted(&self, candidate: PSID, policy: DirectoryPolicy) -> bool {
        self.owner_is_trusted(candidate, policy)
            || equal_sid(candidate, self.creator_owner.as_sid())
    }
}

fn validate_single_component(name: &OsStr, parent: &Path) -> Result<(), CacheGuardError> {
    let path = Path::new(name);
    if name.is_empty() || path.components().count() != 1 || path.file_name() != Some(name) {
        return Err(CacheGuardError::io(
            parent,
            io::Error::new(
                io::ErrorKind::InvalidInput,
                "cache child name must be one component",
            ),
        ));
    }
    Ok(())
}

fn open_pinned_path(path: &Path, directory: bool) -> Result<File, CacheGuardError> {
    let mut options = OpenOptions::new();
    options
        .read(true)
        .access_mode(FILE_GENERIC_READ.0 | READ_CONTROL.0)
        // Deny directory writes as well as deletion: a writable directory
        // handle could install a junction after its no-reparse validation.
        .share_mode(FILE_SHARE_READ.0)
        .custom_flags(
            FILE_FLAG_OPEN_REPARSE_POINT.0
                | if directory {
                    FILE_FLAG_BACKUP_SEMANTICS.0
                } else {
                    0
                },
        );
    options
        .open(path)
        .map_err(|source| CacheGuardError::io(path, source))
}

fn validate_handle(
    file: &File,
    path: &Path,
    require_directory: bool,
    policy: DirectoryPolicy,
    trusted: &TrustedSids,
) -> Result<(), CacheGuardError> {
    let handle = HANDLE(file.as_raw_handle());
    let mut tag = FILE_ATTRIBUTE_TAG_INFO::default();
    // SAFETY: `handle` comes from a live `File`; `tag` is a writable buffer of the stated size.
    unsafe {
        GetFileInformationByHandleEx(
            handle,
            FileAttributeTagInfo,
            ptr::from_mut(&mut tag).cast(),
            size_of::<FILE_ATTRIBUTE_TAG_INFO>() as u32,
        )
    }
    .map_err(|error| CacheGuardError::io(path, io::Error::from_raw_os_error(error.code().0)))?;
    if tag.FileAttributes & FILE_ATTRIBUTE_REPARSE_POINT.0 != 0 {
        return Err(CacheGuardError::ReparsePoint {
            path: path.to_owned(),
        });
    }
    let is_directory = tag.FileAttributes & FILE_ATTRIBUTE_DIRECTORY.0 != 0;
    if require_directory != is_directory {
        return Err(CacheGuardError::NotADirectory {
            path: path.to_owned(),
        });
    }
    validate_security(handle, path, policy, trusted)
}

fn validate_security(
    handle: HANDLE,
    path: &Path,
    policy: DirectoryPolicy,
    trusted: &TrustedSids,
) -> Result<(), CacheGuardError> {
    let mut owner = PSID(ptr::null_mut());
    let mut dacl: *mut ACL = ptr::null_mut();
    let mut descriptor = PSECURITY_DESCRIPTOR(ptr::null_mut());
    // SAFETY: all output pointers remain valid until the returned descriptor is freed below.
    let status = unsafe {
        GetSecurityInfo(
            handle,
            SE_FILE_OBJECT,
            OWNER_SECURITY_INFORMATION | DACL_SECURITY_INFORMATION,
            Some(&mut owner),
            None,
            Some(&mut dacl),
            None,
            Some(&mut descriptor),
        )
    };
    if status.0 != 0 {
        return Err(CacheGuardError::io(
            path,
            io::Error::from_raw_os_error(status.0 as i32),
        ));
    }
    let result = inspect_security_descriptor(descriptor, owner, dacl, path, policy, trusted);
    // SAFETY: GetSecurityInfo allocated `descriptor` with LocalAlloc on success.
    unsafe {
        LocalFree(Some(HLOCAL(descriptor.0)));
    }
    result
}

fn inspect_security_descriptor(
    descriptor: PSECURITY_DESCRIPTOR,
    owner: PSID,
    dacl: *mut ACL,
    path: &Path,
    policy: DirectoryPolicy,
    trusted: &TrustedSids,
) -> Result<(), CacheGuardError> {
    if owner.is_invalid() || !trusted.owner_is_trusted(owner, policy) {
        return Err(CacheGuardError::UntrustedOwner {
            path: path.to_owned(),
            owner: sid_to_string(owner, path).unwrap_or_else(|_| "<invalid-sid>".to_owned()),
        });
    }
    let mut control = 0_u16;
    let mut revision = 0_u32;
    // SAFETY: `descriptor` is the live self-relative descriptor returned by GetSecurityInfo.
    unsafe { GetSecurityDescriptorControl(descriptor, &mut control, &mut revision) }
        .map_err(|error| CacheGuardError::io(path, io::Error::from_raw_os_error(error.code().0)))?;
    if control & SE_DACL_PRESENT.0 == 0 || dacl.is_null() {
        return Err(CacheGuardError::MissingDacl {
            path: path.to_owned(),
        });
    }

    // SAFETY: `dacl` points into the live descriptor and its header is present.
    let ace_count = unsafe { (*dacl).AceCount };
    for index in 0..u32::from(ace_count) {
        let mut raw = ptr::null_mut();
        // SAFETY: index is bounded by AceCount and `raw` is an output pointer.
        unsafe { GetAce(dacl, index, &mut raw) }.map_err(|error| {
            CacheGuardError::io(path, io::Error::from_raw_os_error(error.code().0))
        })?;
        // SAFETY: every ACE begins with a complete ACE_HEADER.
        let header = unsafe { &*(raw.cast::<ACE_HEADER>()) };
        let ace_type = u32::from(header.AceType);
        if ace_type == ACCESS_DENIED_ACE_TYPE {
            continue;
        }
        if ace_type != ACCESS_ALLOWED_ACE_TYPE {
            return Err(CacheGuardError::UnsupportedAce {
                path: path.to_owned(),
                ace_type: header.AceType,
            });
        }
        // SAFETY: ACCESS_ALLOWED_ACE_TYPE guarantees the fixed allowed-ACE prefix.
        let ace = unsafe { &*(raw.cast::<ACCESS_ALLOWED_ACE>()) };
        let mut mask = ace.Mask;
        let mapping = GENERIC_MAPPING {
            GenericRead: FILE_GENERIC_READ.0,
            GenericWrite: FILE_GENERIC_WRITE.0,
            GenericExecute: FILE_GENERIC_EXECUTE.0,
            GenericAll: FILE_ALL_ACCESS.0,
        };
        // SAFETY: both pointers refer to initialized local values.
        unsafe { MapGenericMask(&mut mask, &mapping) };
        if !ace_grants_mutation(policy, mask, header.AceFlags) {
            continue;
        }
        let trustee = PSID(ptr::from_ref(&ace.SidStart).cast_mut().cast());
        if !trusted.mutation_is_trusted(trustee, policy) {
            return Err(CacheGuardError::UntrustedWriteAce {
                path: path.to_owned(),
                trustee: sid_to_string(trustee, path)
                    .unwrap_or_else(|_| "<invalid-sid>".to_owned()),
            });
        }
    }
    Ok(())
}

fn ace_grants_mutation(policy: DirectoryPolicy, mask: u32, flags: u8) -> bool {
    let mutation_mask = match policy {
        DirectoryPolicy::Ancestor => DELETE.0 | FILE_DELETE_CHILD.0 | WRITE_DAC.0 | WRITE_OWNER.0,
        DirectoryPolicy::Cache => {
            FILE_WRITE_DATA.0
                | FILE_APPEND_DATA.0
                | FILE_WRITE_EA.0
                | FILE_WRITE_ATTRIBUTES.0
                | FILE_DELETE_CHILD.0
                | DELETE.0
                | WRITE_DAC.0
                | WRITE_OWNER.0
        }
    };
    if mask & mutation_mask == 0 {
        return false;
    }
    let effective_here = flags & (INHERIT_ONLY_ACE.0 as u8) == 0;
    let inherits_to_cache_child = matches!(policy, DirectoryPolicy::Cache)
        && u32::from(flags) & (OBJECT_INHERIT_ACE.0 | CONTAINER_INHERIT_ACE.0) != 0;
    effective_here || inherits_to_cache_child
}

fn create_private_directory(path: &Path, trusted: &TrustedSids) -> Result<(), CacheGuardError> {
    let user = sid_to_string(trusted.user.as_sid(), path)?;
    let sddl = format!("O:{user}D:P(A;OICI;FA;;;{user})(A;OICI;FA;;;SY)(A;OICI;FA;;;BA)");
    let wide_sddl = wide(OsStr::new(&sddl));
    let mut descriptor = PSECURITY_DESCRIPTOR(ptr::null_mut());
    // SAFETY: `wide_sddl` is NUL terminated and descriptor is an output pointer.
    unsafe {
        ConvertStringSecurityDescriptorToSecurityDescriptorW(
            PCWSTR(wide_sddl.as_ptr()),
            SDDL_REVISION_1,
            &mut descriptor,
            None,
        )
    }
    .map_err(|error| CacheGuardError::io(path, io::Error::from_raw_os_error(error.code().0)))?;
    let attributes = SECURITY_ATTRIBUTES {
        nLength: size_of::<SECURITY_ATTRIBUTES>() as u32,
        lpSecurityDescriptor: descriptor.0,
        bInheritHandle: false.into(),
    };
    let wide_path = wide(path.as_os_str());
    // SAFETY: path is NUL terminated and attributes references the live descriptor.
    let result = unsafe { CreateDirectoryW(PCWSTR(wide_path.as_ptr()), Some(&attributes)) };
    // SAFETY: the conversion API allocated the descriptor with LocalAlloc.
    unsafe {
        LocalFree(Some(HLOCAL(descriptor.0)));
    }
    result.map_err(|error| CacheGuardError::io(path, io::Error::from_raw_os_error(error.code().0)))
}

fn write_archive_atomic(
    parent: &Path,
    destination: &Path,
    bytes: &[u8],
) -> Result<(), CacheGuardError> {
    for attempt in 0..MAX_NAME_ATTEMPTS {
        let temporary = parent.join(format!(
            ".bamts-archive-{}-{attempt}.tmp",
            std::process::id()
        ));
        let mut file = match OpenOptions::new()
            .write(true)
            .access_mode(FILE_GENERIC_WRITE.0 | DELETE.0)
            // The same-parent rename requires the staging identity and parent
            // to stay fixed until publication, even against another owner process.
            .share_mode(0)
            .create_new(true)
            .open(&temporary)
        {
            Ok(file) => file,
            Err(error) if error.kind() == io::ErrorKind::AlreadyExists => continue,
            Err(source) => return Err(CacheGuardError::io(&temporary, source)),
        };
        if let Err(source) = file.write_all(bytes).and_then(|()| file.sync_all()) {
            drop(file);
            let _ = fs::remove_file(&temporary);
            return Err(CacheGuardError::io(&temporary, source));
        }
        let renamed = rename_archive_in_place(&file, destination);
        drop(file);
        match renamed {
            Ok(()) => return Ok(()),
            Err(_error) if destination.exists() => {
                let _ = fs::remove_file(&temporary);
                return Ok(());
            }
            Err(source) => {
                let _ = fs::remove_file(&temporary);
                return Err(CacheGuardError::io(destination, source));
            }
        }
    }
    Err(CacheGuardError::NameAttemptsExhausted {
        parent: parent.to_owned(),
    })
}

// The synchronous file was created in destination's guarded parent, and the
// destination has a validated single-component name. A native leaf-only rename
// changes that entry without reopening its write-denying parent. Win32 path
// renames resolve a target directory instead and conflict with the parent pin.
fn rename_archive_in_place(file: &File, destination: &Path) -> io::Result<()> {
    let name: Vec<u16> = destination
        .file_name()
        .expect("validated archive component")
        .encode_wide()
        .collect();
    let name_bytes = u32::try_from(std::mem::size_of_val(name.as_slice())).map_err(|_| {
        io::Error::new(
            io::ErrorKind::InvalidInput,
            "archive name exceeds NT length",
        )
    })?;
    let length = size_of::<FILE_RENAME_INFORMATION>() + name_bytes as usize;
    let length_u32 = u32::try_from(length).map_err(|_| {
        io::Error::new(
            io::ErrorKind::InvalidInput,
            "archive rename exceeds NT length",
        )
    })?;
    let mut storage = vec![0_usize; length.div_ceil(size_of::<usize>())];
    let information = storage.as_mut_ptr().cast::<FILE_RENAME_INFORMATION>();
    let mut status = IO_STATUS_BLOCK::default();
    // SAFETY: pointer-aligned zeroed storage holds the header and UTF-16 tail.
    // Its null RootDirectory and false ReplaceIfExists select a same-parent,
    // non-replacing rename. The live synchronous file has DELETE access; both
    // buffers remain valid until the synchronous syscall returns.
    let result = unsafe {
        (*information).FileNameLength = name_bytes;
        ptr::copy_nonoverlapping(
            name.as_ptr(),
            ptr::addr_of_mut!((*information).FileName).cast::<u16>(),
            name.len(),
        );
        NtSetInformationFile(
            HANDLE(file.as_raw_handle()),
            &mut status,
            information.cast(),
            length_u32,
            FileRenameInformation,
        )
    };
    if result.is_ok() {
        Ok(())
    } else {
        // SAFETY: this maps a returned NT status to its Win32 error code.
        let code = unsafe { RtlNtStatusToDosError(result) };
        Err(io::Error::from_raw_os_error(code as i32))
    }
}

fn bytes_equal(file: &mut File, expected: &[u8]) -> io::Result<bool> {
    if file.metadata()?.len() != expected.len() as u64 {
        return Ok(false);
    }
    let mut buffer = [0_u8; COMPARE_BUFFER_BYTES];
    let mut offset = 0;
    while offset < expected.len() {
        let count = file.read(&mut buffer)?;
        if count == 0 || buffer[..count] != expected[offset..offset + count] {
            return Ok(false);
        }
        offset += count;
    }
    Ok(true)
}

fn current_user_sid() -> Result<OwnedSid, CacheGuardError> {
    let path = Path::new("<current-user>");
    let mut token = HANDLE(ptr::null_mut());
    // SAFETY: token is a valid output pointer; the pseudo process handle is always valid here.
    unsafe { OpenProcessToken(GetCurrentProcess(), TOKEN_QUERY, &mut token) }
        .map_err(|error| CacheGuardError::io(path, io::Error::from_raw_os_error(error.code().0)))?;
    let result = read_token_user(token, path);
    // SAFETY: OpenProcessToken returned an owned handle on success.
    let _ = unsafe { CloseHandle(token) };
    result
}

fn read_token_user(token: HANDLE, path: &Path) -> Result<OwnedSid, CacheGuardError> {
    let mut size = 0_u32;
    // SAFETY: null buffer with zero size is the documented size-query call.
    let _ = unsafe { GetTokenInformation(token, TokenUser, None, 0, &mut size) };
    if size == 0 {
        return Err(CacheGuardError::io(path, io::Error::last_os_error()));
    }
    let words = (size as usize).div_ceil(size_of::<usize>());
    let mut buffer = vec![0_usize; words];
    // SAFETY: the usize allocation is pointer-aligned and exposes at least `size` writable bytes.
    unsafe {
        GetTokenInformation(
            token,
            TokenUser,
            Some(buffer.as_mut_ptr().cast()),
            size,
            &mut size,
        )
    }
    .map_err(|error| CacheGuardError::io(path, io::Error::from_raw_os_error(error.code().0)))?;
    // SAFETY: the aligned successful TokenUser query initialized a TOKEN_USER at the buffer start.
    let source = unsafe { (*(buffer.as_ptr().cast::<TOKEN_USER>())).User.Sid };
    copy_sid(source, path)
}

fn well_known_sid(
    kind: windows::Win32::Security::WELL_KNOWN_SID_TYPE,
) -> Result<OwnedSid, CacheGuardError> {
    let path = Path::new("<well-known-sid>");
    let mut size = 0_u32;
    // SAFETY: null SID is the documented size-query call.
    let _ = unsafe { CreateWellKnownSid(kind, None, None, &mut size) };
    if size == 0 {
        return Err(CacheGuardError::io(path, io::Error::last_os_error()));
    }
    let mut buffer = OwnedSid::with_byte_capacity(size as usize);
    // SAFETY: the pointer-aligned buffer has the size requested by the first call.
    unsafe { CreateWellKnownSid(kind, None, Some(buffer.as_mut_sid()), &mut size) }
        .map_err(|error| CacheGuardError::io(path, io::Error::from_raw_os_error(error.code().0)))?;
    Ok(buffer)
}

fn parse_sid(value: &str) -> Result<OwnedSid, CacheGuardError> {
    let path = Path::new("<sid>");
    let value = wide(OsStr::new(value));
    let mut sid = PSID(ptr::null_mut());
    // SAFETY: value is NUL terminated and sid is a valid output pointer.
    unsafe { ConvertStringSidToSidW(PCWSTR(value.as_ptr()), &mut sid) }
        .map_err(|error| CacheGuardError::io(path, io::Error::from_raw_os_error(error.code().0)))?;
    let result = copy_sid(sid, path);
    // SAFETY: ConvertStringSidToSidW allocated sid with LocalAlloc on success.
    unsafe {
        LocalFree(Some(HLOCAL(sid.0)));
    }
    result
}

fn copy_sid(source: PSID, path: &Path) -> Result<OwnedSid, CacheGuardError> {
    // SAFETY: source comes from a successful Windows SID query or conversion.
    let size = unsafe { GetLengthSid(source) };
    let mut output = OwnedSid::with_byte_capacity(size as usize);
    // SAFETY: the pointer-aligned output has at least the size reported for source.
    unsafe { CopySid(size, output.as_mut_sid(), source) }
        .map_err(|error| CacheGuardError::io(path, io::Error::from_raw_os_error(error.code().0)))?;
    Ok(output)
}

fn equal_sid(left: PSID, right: PSID) -> bool {
    // SAFETY: both pointers address complete SID byte buffers for this call.
    unsafe { EqualSid(left, right) }.is_ok()
}

fn sid_to_string(value: PSID, path: &Path) -> Result<String, CacheGuardError> {
    if value.is_invalid() {
        return Err(CacheGuardError::io(
            path,
            io::Error::new(io::ErrorKind::InvalidData, "invalid SID"),
        ));
    }
    let mut string = PWSTR::null();
    // SAFETY: value is a live SID and string is a valid output pointer.
    unsafe { ConvertSidToStringSidW(value, &mut string) }
        .map_err(|error| CacheGuardError::io(path, io::Error::from_raw_os_error(error.code().0)))?;
    // SAFETY: the conversion API returned a NUL-terminated LocalAlloc string.
    let result = unsafe { string.to_string() }.map_err(|error| {
        CacheGuardError::io(path, io::Error::new(io::ErrorKind::InvalidData, error))
    });
    // SAFETY: ConvertSidToStringSidW allocated this string with LocalAlloc.
    unsafe {
        LocalFree(Some(HLOCAL(string.as_ptr().cast())));
    }
    result
}

fn wide(value: &OsStr) -> Vec<u16> {
    value.encode_wide().chain([0]).collect()
}

#[cfg(test)]
mod tests {
    use super::{
        CONTAINER_INHERIT_ACE, DELETE, DirectoryPolicy, FILE_DELETE_CHILD, FILE_WRITE_DATA,
        INHERIT_ONLY_ACE, OBJECT_INHERIT_ACE, PrivateCacheRoot, TrustedSids, WRITE_DAC,
        ace_grants_mutation, parse_sid, well_known_sid,
    };
    use std::{
        fs,
        time::{SystemTime, UNIX_EPOCH},
    };

    fn fresh_root() -> std::path::PathBuf {
        let nonce = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .expect("system clock")
            .as_nanos();
        std::env::temp_dir().join(format!(
            "bamts-cache-guard-test-{}-{nonce}",
            std::process::id()
        ))
    }

    #[test]
    fn trusted_installer_is_trusted_only_for_ancestors() {
        let trusted = TrustedSids::current().expect("trusted SIDs");
        let installer = trusted.trusted_installer.as_sid();
        assert!(trusted.owner_is_trusted(installer, DirectoryPolicy::Ancestor));
        assert!(trusted.mutation_is_trusted(installer, DirectoryPolicy::Ancestor));
        assert!(!trusted.owner_is_trusted(installer, DirectoryPolicy::Cache));
        assert!(!trusted.mutation_is_trusted(installer, DirectoryPolicy::Cache));
    }

    #[test]
    fn system_ancestor_exception_preserves_the_exact_trust_boundary() {
        let trusted = TrustedSids::current().expect("trusted SIDs");
        let other_service =
            parse_sid("S-1-5-80-956008885-3418522649-1831038044-1853292631-2271478465")
                .expect("distinct service SID");
        let everyone = well_known_sid(windows::Win32::Security::WinWorldSid).expect("Everyone SID");
        for policy in [DirectoryPolicy::Ancestor, DirectoryPolicy::Cache] {
            for owner in [&trusted.user, &trusted.system, &trusted.administrators] {
                assert!(trusted.owner_is_trusted(owner.as_sid(), policy));
                assert!(trusted.mutation_is_trusted(owner.as_sid(), policy));
            }
            for untrusted in [&other_service, &everyone] {
                assert!(!trusted.owner_is_trusted(untrusted.as_sid(), policy));
                assert!(!trusted.mutation_is_trusted(untrusted.as_sid(), policy));
            }
            assert!(!trusted.owner_is_trusted(trusted.creator_owner.as_sid(), policy));
            assert!(trusted.mutation_is_trusted(trusted.creator_owner.as_sid(), policy));
        }
    }

    #[test]
    fn inherit_only_cache_ace_is_checked_for_descendant_mutation() {
        let inherit_only = INHERIT_ONLY_ACE.0 as u8;
        let object_inherit = OBJECT_INHERIT_ACE.0 as u8;
        let container_inherit = CONTAINER_INHERIT_ACE.0 as u8;

        assert!(ace_grants_mutation(
            DirectoryPolicy::Cache,
            FILE_WRITE_DATA.0 | WRITE_DAC.0,
            inherit_only | object_inherit,
        ));
        assert!(ace_grants_mutation(
            DirectoryPolicy::Cache,
            FILE_DELETE_CHILD.0,
            inherit_only | container_inherit,
        ));
        assert!(!ace_grants_mutation(
            DirectoryPolicy::Ancestor,
            FILE_WRITE_DATA.0,
            inherit_only | object_inherit,
        ));
        assert!(!ace_grants_mutation(
            DirectoryPolicy::Cache,
            DELETE.0,
            inherit_only,
        ));
    }

    #[test]
    fn fallback_key_uses_the_current_sid() {
        let key = PrivateCacheRoot::fallback_user_key().expect("current user SID");
        assert!(key.starts_with("S-1-"), "{key}");
    }

    #[test]
    fn archive_reuse_verifies_and_repairs_bytes() {
        let root_path = fresh_root();
        let root = PrivateCacheRoot::acquire(&root_path).expect("private root");
        let runtime = root
            .guard_child_dir(std::ffi::OsStr::new("runtime"))
            .expect("runtime dir");
        {
            let archive = root
                .materialize_archive(&runtime, "runtime.lib", b"expected")
                .expect("initial archive");
            assert_eq!(fs::read(archive.path()).expect("read archive"), b"expected");
        }
        fs::write(runtime.path().join("runtime.lib"), b"poison").expect("poison fixture");
        {
            let archive = root
                .materialize_archive(&runtime, "runtime.lib", b"expected")
                .expect("repaired archive");
            assert_eq!(fs::read(archive.path()).expect("read archive"), b"expected");
        }
        drop(runtime);
        drop(root);
        fs::remove_dir_all(root_path).expect("remove fixture");
    }

    #[test]
    fn guarded_archive_publication_preserves_directory_and_file_pins() {
        use std::os::windows::fs::OpenOptionsExt;

        let root_path = fresh_root();
        let root = PrivateCacheRoot::acquire(&root_path).expect("private root");
        let runtime = root
            .guard_child_dir(std::ffi::OsStr::new("runtime"))
            .expect("runtime dir");
        let runtime_path = runtime.path().to_owned();
        let staged = runtime_path.join("staged.lib");
        let published = runtime_path.join("runtime-\u{1f680}.lib");
        let open_directory_writer = |path: &std::path::Path| {
            fs::OpenOptions::new()
                .write(true)
                .custom_flags(super::FILE_FLAG_BACKUP_SEMANTICS.0)
                .open(path)
        };
        assert_eq!(
            open_directory_writer(runtime.path())
                .expect_err("a junction writer must be denied on the still-empty directory")
                .raw_os_error(),
            Some(32)
        );
        assert!(
            fs::rename(runtime.path(), root.root_path().join("moved")).is_err(),
            "a held directory must not be renamed"
        );

        let archive = root
            .materialize_archive(&runtime, "runtime-\u{1f680}.lib", b"expected")
            .expect("hold published archive");
        assert!(fs::write(archive.path(), b"poison").is_err());
        assert!(fs::remove_file(archive.path()).is_err());
        assert!(fs::rename(archive.path(), &staged).is_err());
        assert_eq!(
            fs::read(archive.path()).expect("read held archive"),
            b"expected"
        );
        drop(archive);
        fs::write(&published, b"released").expect("release permits archive write");
        drop(runtime);
        drop(open_directory_writer(&runtime_path).expect("release permits directory write open"));
        drop(root);
        fs::rename(&published, &staged).expect("release permits archive rename");
        fs::rename(&runtime_path, root_path.join("moved"))
            .expect("release permits directory rename");
        fs::remove_dir_all(root_path).expect("remove fixture");
    }

    #[test]
    fn invocation_directories_are_fresh_and_removable_after_close() {
        let root_path = fresh_root();
        let root = PrivateCacheRoot::acquire(&root_path).expect("private root");
        let first = root
            .create_invocation_dir("bamts-run")
            .expect("first invocation");
        let first_path = first.path().to_owned();
        let second = root
            .create_invocation_dir("bamts-run")
            .expect("second invocation");
        let second_path = second.path().to_owned();
        assert_ne!(first_path, second_path);
        drop(first);
        drop(second);
        assert!(!first_path.exists());
        assert!(!second_path.exists());
        drop(root);
        fs::remove_dir_all(root_path).expect("remove fixture");
    }
}

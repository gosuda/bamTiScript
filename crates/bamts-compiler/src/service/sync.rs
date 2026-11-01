use bamts_cancel::CancellationToken;
use std::{
    path::Path,
    sync::{Arc, RwLock},
};

use crate::source::Utf16Pos;

use super::{
    Completion, DiagnosticEntry, DocumentSnapshot, Location, QuickInfo, RenameResult, ServiceError,
    ServiceSnapshot, ServiceState, filesystem::FileSystem,
};

/// Thread-safe synchronous access to one canonical [`ServiceState`].
pub struct SyncService<F: FileSystem> {
    state: Arc<RwLock<ServiceState<F>>>,
}

impl<F: FileSystem> Clone for SyncService<F> {
    fn clone(&self) -> Self {
        Self {
            state: Arc::clone(&self.state),
        }
    }
}

impl<F: FileSystem> SyncService<F> {
    #[must_use]
    pub fn new(filesystem: F) -> Self {
        Self {
            state: Arc::new(RwLock::new(ServiceState::new(filesystem))),
        }
    }

    pub fn open(
        &self,
        path: impl AsRef<Path>,
        text: impl Into<Arc<str>>,
        version: u64,
    ) -> Result<Arc<DocumentSnapshot>, ServiceError> {
        self.open_with_cancel(path, text, version, CancellationToken::new())
    }

    pub fn open_with_cancel(
        &self,
        path: impl AsRef<Path>,
        text: impl Into<Arc<str>>,
        version: u64,
        cancel: CancellationToken,
    ) -> Result<Arc<DocumentSnapshot>, ServiceError> {
        self.state
            .write()
            .map_err(|_| ServiceError::LockPoisoned)?
            .open_with_cancel(path, text, version, &cancel)
    }

    pub fn update(
        &self,
        path: impl AsRef<Path>,
        text: impl Into<Arc<str>>,
        version: u64,
    ) -> Result<Arc<DocumentSnapshot>, ServiceError> {
        self.update_with_cancel(path, text, version, CancellationToken::new())
    }

    pub fn update_with_cancel(
        &self,
        path: impl AsRef<Path>,
        text: impl Into<Arc<str>>,
        version: u64,
        cancel: CancellationToken,
    ) -> Result<Arc<DocumentSnapshot>, ServiceError> {
        self.state
            .write()
            .map_err(|_| ServiceError::LockPoisoned)?
            .update_with_cancel(path, text, version, &cancel)
    }

    pub fn close(&self, path: impl AsRef<Path>) -> Result<(), ServiceError> {
        self.close_with_cancel(path, CancellationToken::new())
    }

    pub fn close_with_cancel(
        &self,
        path: impl AsRef<Path>,
        cancel: CancellationToken,
    ) -> Result<(), ServiceError> {
        self.state
            .write()
            .map_err(|_| ServiceError::LockPoisoned)?
            .close_with_cancel(path, &cancel)
    }

    pub fn snapshot(&self) -> Result<ServiceSnapshot, ServiceError> {
        Ok(self
            .state
            .read()
            .map_err(|_| ServiceError::LockPoisoned)?
            .snapshot())
    }

    pub fn completions(
        &self,
        path: impl AsRef<Path>,
        position: Utf16Pos,
    ) -> Result<Vec<Completion>, ServiceError> {
        self.completions_with_cancel(path, position, CancellationToken::new())
    }

    pub fn completions_with_cancel(
        &self,
        path: impl AsRef<Path>,
        position: Utf16Pos,
        cancel: CancellationToken,
    ) -> Result<Vec<Completion>, ServiceError> {
        self.state
            .write()
            .map_err(|_| ServiceError::LockPoisoned)?
            .completions_with_cancel(path, position, &cancel)
    }

    pub fn definition(
        &self,
        path: impl AsRef<Path>,
        position: Utf16Pos,
    ) -> Result<Option<Location>, ServiceError> {
        self.definition_with_cancel(path, position, CancellationToken::new())
    }

    pub fn definition_with_cancel(
        &self,
        path: impl AsRef<Path>,
        position: Utf16Pos,
        cancel: CancellationToken,
    ) -> Result<Option<Location>, ServiceError> {
        self.state
            .write()
            .map_err(|_| ServiceError::LockPoisoned)?
            .definition_with_cancel(path, position, &cancel)
    }

    pub fn quick_info(
        &self,
        path: impl AsRef<Path>,
        position: Utf16Pos,
    ) -> Result<Option<QuickInfo>, ServiceError> {
        self.quick_info_with_cancel(path, position, CancellationToken::new())
    }

    pub fn quick_info_with_cancel(
        &self,
        path: impl AsRef<Path>,
        position: Utf16Pos,
        cancel: CancellationToken,
    ) -> Result<Option<QuickInfo>, ServiceError> {
        self.state
            .write()
            .map_err(|_| ServiceError::LockPoisoned)?
            .quick_info_with_cancel(path, position, &cancel)
    }

    pub fn references(
        &self,
        path: impl AsRef<Path>,
        position: Utf16Pos,
    ) -> Result<Vec<Location>, ServiceError> {
        self.references_with_cancel(path, position, CancellationToken::new())
    }

    pub fn references_with_cancel(
        &self,
        path: impl AsRef<Path>,
        position: Utf16Pos,
        cancel: CancellationToken,
    ) -> Result<Vec<Location>, ServiceError> {
        self.state
            .write()
            .map_err(|_| ServiceError::LockPoisoned)?
            .references_with_cancel(path, position, &cancel)
    }

    pub fn rename(
        &self,
        path: impl AsRef<Path>,
        position: Utf16Pos,
        new_name: &str,
    ) -> Result<RenameResult, ServiceError> {
        self.rename_with_cancel(path, position, new_name, CancellationToken::new())
    }

    pub fn rename_with_cancel(
        &self,
        path: impl AsRef<Path>,
        position: Utf16Pos,
        new_name: &str,
        cancel: CancellationToken,
    ) -> Result<RenameResult, ServiceError> {
        self.state
            .write()
            .map_err(|_| ServiceError::LockPoisoned)?
            .rename_with_cancel(path, position, new_name, &cancel)
    }

    pub fn diagnostics(
        &self,
        path: impl AsRef<Path>,
    ) -> Result<Vec<DiagnosticEntry>, ServiceError> {
        self.diagnostics_with_cancel(path, CancellationToken::new())
    }

    pub fn diagnostics_with_cancel(
        &self,
        path: impl AsRef<Path>,
        cancel: CancellationToken,
    ) -> Result<Vec<DiagnosticEntry>, ServiceError> {
        self.state
            .write()
            .map_err(|_| ServiceError::LockPoisoned)?
            .diagnostics_with_cancel(path, &cancel)
    }
}

#[cfg(test)]
mod tests {
    use std::{fs, sync::Arc};

    use super::SyncService;
    use crate::service::{ServiceError, filesystem::OsFileSystem};

    #[test]
    fn sync_api_preserves_version_failures_across_clones() {
        let root = crate::service::test_support::fresh_dir("bamts-sync-service");
        let service = SyncService::new(OsFileSystem::new(&root).expect("filesystem"));
        service
            .open("a.ts", Arc::<str>::from("const a = 1;"), 1)
            .expect("open");
        assert!(matches!(
            service
                .clone()
                .update("a.ts", Arc::<str>::from("const a = 2;"), 1),
            Err(ServiceError::VersionOutOfOrder { .. })
        ));
        assert_eq!(
            service
                .snapshot()
                .expect("snapshot")
                .documents()
                .next()
                .expect("document")
                .version(),
            1
        );
        fs::remove_dir_all(root).expect("remove root");
    }
}

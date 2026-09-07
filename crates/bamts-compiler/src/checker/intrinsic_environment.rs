//! The checker-visible names supplied by the target's intrinsic environment.
//!
//! This is deliberately a closed inventory. A failed lookup remains a checker
//! error; adding a name here is the explicit compatibility decision.
//!
//! Each entry is tagged with the `Lib` that first declares it in the
//! TypeScript 7.0.2 `lib.*.d.ts` files. The environment includes an entry
//! only when its declaring lib is in the active [`LibSet`], modeling tsc's
//! `lib` / `target` scoping.

use crate::emitter::ScriptTarget;

/// A category of TypeScript lib files that is relevant for global scoping.
///
/// Each variant aggregates the `lib.*.d.ts` files from the TypeScript 7.0.2
/// authority that introduce the same set of globals. The mapping from lib
/// file stems to these categories is grounded in the `declare` lines of the
/// authority `lib/` directory.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub(crate) enum Lib {
    /// Keywords and ambient globals always available regardless of `lib`
    /// (`undefined`, `globalThis`, `global`, `process`).
    Always,
    /// `lib.es5.d.ts` — ES5 core globals, utility types, and `Intl`.
    Es5,
    /// `lib.es2015.*.d.ts` — Proxy, Reflect, Map, Set, Symbol, Promise,
    /// Iterable, Iterator, Generator, and friends.
    Es2015,
    /// `lib.es2017.sharedmemory.d.ts` — `Atomics`, `SharedArrayBuffer`.
    Es2017SharedMemory,
    /// `lib.es2018.asynciterable.d.ts`, `lib.es2018.asyncgenerator.d.ts` —
    /// `AsyncIterable`, `AsyncIterator`, `AsyncGenerator`.
    Es2018AsyncIterable,
    /// `lib.es2019.array.d.ts` — `FlatArray`.
    Es2019Array,
    /// `lib.es2020.bigint.d.ts` — `BigInt`, `BigInt64Array`, `BigUint64Array`.
    Es2020BigInt,
    /// `lib.es2021.weakref.d.ts` — `WeakRef`, `FinalizationRegistry`.
    Es2021WeakRef,
    /// `lib.es2021.promise.d.ts` — `AggregateError`.
    Es2021Promise,
    /// `lib.es2025.float16.d.ts` — `Float16Array`.
    Es2025Float16,
    /// `lib.es2025.iterator.d.ts` — `Iterator` as a value (constructor).
    Es2025Iterator,
    /// `lib.esnext.disposable.d.ts` — `DisposableStack`,
    /// `AsyncDisposableStack`, `SuppressedError`.
    EsnextDisposable,
    /// `lib.esnext.temporal.d.ts` — `Temporal`.
    EsnextTemporal,
    /// `lib.dom.d.ts` — DOM globals (`document`, `window`, `Event`, …).
    Dom,
    /// `lib.webworker.importscripts.d.ts` — `importScripts`.
    WebworkerImportscripts,
    /// `lib.scripthost.d.ts` — `WScript`, `WSH`.
    Scripthost,
    /// `lib.decorators.legacy.d.ts` — decorator types.
    DecoratorsLegacy,
}

impl Lib {
    #[must_use]
    const fn bit(self) -> u32 {
        1u32 << (self as u32)
    }
}

/// A bitset of active [`Lib`] categories.
///
/// When no explicit `lib` is given, the set is derived from `target` via
/// [`LibSet::default_for_target`]. An explicit `@lib:` replaces the default
/// with [`LibSet::from_lib_names`].
#[derive(Clone, Copy, Debug, Default, Eq, Hash, PartialEq)]
pub(crate) struct LibSet(u32);

impl LibSet {
    /// An empty set — no globals resolve.
    pub(crate) const EMPTY: Self = Self(0);

    /// The set containing every category — used when lib scoping is disabled.
    pub(crate) const ALL: Self = Self((1 << 17) - 1);

    #[must_use]
    pub(crate) const fn contains(self, lib: Lib) -> bool {
        (self.0 & lib.bit()) != 0
    }

    #[must_use]
    pub(crate) const fn with(mut self, lib: Lib) -> Self {
        self.0 |= lib.bit();
        self
    }

    /// Derives the default lib set for a target, matching tsc 7.0.2's
    /// `<target>.full` expansion. Host libs (`Dom`, `WebworkerImportscripts`,
    /// `Scripthost`) are included in every default; `DecoratorsLegacy` is
    /// pulled in by `es5`; ES feature libs accumulate with the target.
    #[must_use]
    pub(crate) const fn default_for_target(target: ScriptTarget) -> Self {
        let mut set = Self::EMPTY
            .with(Lib::Always)
            .with(Lib::Es5)
            .with(Lib::DecoratorsLegacy)
            .with(Lib::Dom)
            .with(Lib::WebworkerImportscripts)
            .with(Lib::Scripthost);
        if (target as u8) >= (ScriptTarget::Es2015 as u8) {
            set = set.with(Lib::Es2015);
        }
        if (target as u8) >= (ScriptTarget::Es2017 as u8) {
            set = set.with(Lib::Es2017SharedMemory);
        }
        if (target as u8) >= (ScriptTarget::Es2018 as u8) {
            set = set.with(Lib::Es2018AsyncIterable);
        }
        if (target as u8) >= (ScriptTarget::Es2019 as u8) {
            set = set.with(Lib::Es2019Array);
        }
        if (target as u8) >= (ScriptTarget::Es2020 as u8) {
            set = set.with(Lib::Es2020BigInt);
        }
        if (target as u8) >= (ScriptTarget::Es2021 as u8) {
            set = set.with(Lib::Es2021WeakRef).with(Lib::Es2021Promise);
        }
        if (target as u8) >= (ScriptTarget::Es2025 as u8) {
            set = set.with(Lib::Es2025Float16).with(Lib::Es2025Iterator);
        }
        if (target as u8) >= (ScriptTarget::EsNext as u8) {
            set = set.with(Lib::EsnextDisposable).with(Lib::EsnextTemporal);
        }
        set
    }

    /// Builds a lib set from explicit `lib` names (as in `@lib: es2015,dom`),
    /// expanding each named lib to its category and accumulating lower ES
    /// versions. Host libs are added only when explicitly named.
    #[must_use]
    pub(crate) fn from_lib_names(names: &[impl AsRef<str>]) -> Self {
        let mut set = Self::EMPTY.with(Lib::Always).with(Lib::DecoratorsLegacy);
        for name in names {
            let lower = name.as_ref().to_ascii_lowercase();
            match lower.as_str() {
                "es5" | "es3" => {
                    set = set.with(Lib::Es5);
                }
                "es6" | "es2015" => {
                    set = set.with(Lib::Es5).with(Lib::Es2015);
                }
                "es7" | "es2016" => {
                    set = set.with(Lib::Es5).with(Lib::Es2015);
                }
                "es2017" => {
                    set = set
                        .with(Lib::Es5)
                        .with(Lib::Es2015)
                        .with(Lib::Es2017SharedMemory);
                }
                "es2018" => {
                    set = set
                        .with(Lib::Es5)
                        .with(Lib::Es2015)
                        .with(Lib::Es2017SharedMemory)
                        .with(Lib::Es2018AsyncIterable);
                }
                "es2019" => {
                    set = set
                        .with(Lib::Es5)
                        .with(Lib::Es2015)
                        .with(Lib::Es2017SharedMemory)
                        .with(Lib::Es2018AsyncIterable)
                        .with(Lib::Es2019Array);
                }
                "es2020" => {
                    set = set
                        .with(Lib::Es5)
                        .with(Lib::Es2015)
                        .with(Lib::Es2017SharedMemory)
                        .with(Lib::Es2018AsyncIterable)
                        .with(Lib::Es2019Array)
                        .with(Lib::Es2020BigInt);
                }
                "es2021" => {
                    set = set
                        .with(Lib::Es5)
                        .with(Lib::Es2015)
                        .with(Lib::Es2017SharedMemory)
                        .with(Lib::Es2018AsyncIterable)
                        .with(Lib::Es2019Array)
                        .with(Lib::Es2020BigInt)
                        .with(Lib::Es2021WeakRef)
                        .with(Lib::Es2021Promise);
                }
                "es2022" | "es2023" | "es2024" => {
                    set = set
                        .with(Lib::Es5)
                        .with(Lib::Es2015)
                        .with(Lib::Es2017SharedMemory)
                        .with(Lib::Es2018AsyncIterable)
                        .with(Lib::Es2019Array)
                        .with(Lib::Es2020BigInt)
                        .with(Lib::Es2021WeakRef)
                        .with(Lib::Es2021Promise);
                }
                "es2025" => {
                    set = set
                        .with(Lib::Es5)
                        .with(Lib::Es2015)
                        .with(Lib::Es2017SharedMemory)
                        .with(Lib::Es2018AsyncIterable)
                        .with(Lib::Es2019Array)
                        .with(Lib::Es2020BigInt)
                        .with(Lib::Es2021WeakRef)
                        .with(Lib::Es2021Promise)
                        .with(Lib::Es2025Float16)
                        .with(Lib::Es2025Iterator);
                }
                "esnext" => {
                    set = set
                        .with(Lib::Es5)
                        .with(Lib::Es2015)
                        .with(Lib::Es2017SharedMemory)
                        .with(Lib::Es2018AsyncIterable)
                        .with(Lib::Es2019Array)
                        .with(Lib::Es2020BigInt)
                        .with(Lib::Es2021WeakRef)
                        .with(Lib::Es2021Promise)
                        .with(Lib::Es2025Float16)
                        .with(Lib::Es2025Iterator)
                        .with(Lib::EsnextDisposable)
                        .with(Lib::EsnextTemporal);
                }
                // Sub-lib stems that introduce new top-level globals.
                "esnext.temporal" => {
                    set = set.with(Lib::EsnextTemporal);
                }
                "esnext.disposable" => {
                    set = set.with(Lib::EsnextDisposable);
                }
                "es2025.float16" => {
                    set = set.with(Lib::Es2025Float16);
                }
                "es2017.sharedmemory" => {
                    set = set.with(Lib::Es2017SharedMemory);
                }
                // Sub-lib stems that refine existing interfaces but declare no
                // new top-level globals beyond what the parent lib provides.
                "es2015.core"
                | "es2015.generator"
                | "es2015.iterable"
                | "es2015.promise"
                | "es2015.proxy"
                | "es2015.reflect"
                | "es2015.symbol"
                | "es2015.symbol.wellknown"
                | "es2021.intl"
                | "es2023.intl"
                | "es2024.intl"
                | "es2025.intl"
                | "esnext.date"
                | "esnext.intl"
                | "es2024.arraybuffer"
                | "es2024.sharedmemory"
                | "webworker.asynciterable"
                | "webworker.iterable" => {}
                "dom" => {
                    set = set.with(Lib::Dom);
                }
                "dom.iterable" | "dom.asynciterable" => {}
                "webworker.importscripts" => {
                    set = set.with(Lib::WebworkerImportscripts);
                }
                "webworker" => {
                    set = set.with(Lib::Dom).with(Lib::WebworkerImportscripts);
                }
                "scripthost" => {
                    set = set.with(Lib::Scripthost);
                }
                "decorators" | "decorators.legacy" => {
                    set = set.with(Lib::DecoratorsLegacy);
                }
                _ => {}
            }
        }
        set
    }
}

/// Module-scoped host bindings selected by compiler options.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum ModuleEnvironment {
    Standard,
    CommonJs,
}

/// A name paired with the lib that declares it.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct LibEntry {
    name: &'static str,
    lib: Lib,
}

/// Names installed before source declarations are bound.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct GlobalEnvironment {
    values: &'static [LibEntry],
    types: &'static [LibEntry],
    module: ModuleEnvironment,
    libs: LibSet,
}

impl GlobalEnvironment {
    #[must_use]
    pub(super) const fn standard(libs: LibSet) -> Self {
        Self {
            values: STANDARD_VALUES,
            types: STANDARD_TYPES,
            module: ModuleEnvironment::Standard,
            libs,
        }
    }

    #[must_use]
    pub(super) const fn commonjs(libs: LibSet) -> Self {
        Self {
            values: STANDARD_VALUES,
            types: STANDARD_TYPES,
            module: ModuleEnvironment::CommonJs,
            libs,
        }
    }

    #[must_use]
    pub fn values(self) -> Vec<&'static str> {
        self.values
            .iter()
            .filter(|entry| self.libs.contains(entry.lib))
            .map(|entry| entry.name)
            .collect()
    }

    #[must_use]
    pub fn types(self) -> Vec<&'static str> {
        self.types
            .iter()
            .filter(|entry| self.libs.contains(entry.lib))
            .map(|entry| entry.name)
            .collect()
    }

    #[must_use]
    pub fn module_values(self) -> Vec<&'static str> {
        match self.module {
            ModuleEnvironment::Standard => Vec::new(),
            ModuleEnvironment::CommonJs => COMMONJS_WRAPPER_VALUES.to_vec(),
        }
    }

    /// Returns `true` when `lib` is in the active lib set. Intrinsic
    /// refinements declared by a later `lib.*.d.ts` (for example the
    /// `es2015.core` `DateConstructor` overload) gate on this.
    #[must_use]
    pub(crate) fn has_lib(&self, lib: Lib) -> bool {
        self.libs.contains(lib)
    }

    /// Names for which tsc emits TS2583 ("Cannot find name X. Do you need
    /// to change your target library?") instead of the generic TS2304 when
    /// the name is a known global absent from the active lib set. This is a
    /// hardcoded list in tsc, not derivable from the Lib category alone:
    /// `Proxy` (Es2015) gets TS2304, but `Map` (also Es2015) gets TS2583.
    const TS2583_NAMES: &[&str] = &[
        "BigInt",
        "BigInt64Array",
        "BigUint64Array",
        "Atomics",
        "SharedArrayBuffer",
        "Map",
        "Set",
        "Reflect",
        "WeakMap",
        "WeakSet",
        "AsyncGenerator",
        "AsyncGeneratorFunction",
        "AsyncIterable",
        "AsyncIterableIterator",
        "AsyncIterator",
        "Iterator",
    ];

    /// Returns `true` when a value name is a known lib-gated global that tsc
    /// reports as TS2583 (not TS2304) when absent from the active lib set.
    #[must_use]
    pub fn is_lib_gated_value(&self, name: &str) -> bool {
        if !Self::TS2583_NAMES.contains(&name) {
            return false;
        }
        self.values
            .iter()
            .any(|entry| entry.name == name && !self.libs.contains(entry.lib))
    }

    /// Returns `true` when a type name is a known lib-gated global that tsc
    /// reports as TS2583 (not TS2304) when absent from the active lib set.
    #[must_use]
    pub fn is_lib_gated_type(&self, name: &str) -> bool {
        if !Self::TS2583_NAMES.contains(&name) {
            return false;
        }
        self.types
            .iter()
            .any(|entry| entry.name == name && !self.libs.contains(entry.lib))
    }
}

const COMMONJS_WRAPPER_VALUES: &[&str] =
    &["module", "exports", "require", "__filename", "__dirname"];

// `Function` is the sole declaration-only value. It permits library source
// checking without claiming that the runtime installs the constructor.
//
// Each entry is tagged with the `Lib` that first declares it in the
// TypeScript 7.0.2 `lib.*.d.ts` authority files. The tag controls whether
// the name is installed when a given `lib` set is active.
const STANDARD_VALUES: &[LibEntry] = &[
    LibEntry {
        name: "undefined",
        lib: Lib::Always,
    },
    LibEntry {
        name: "NaN",
        lib: Lib::Es5,
    },
    LibEntry {
        name: "Infinity",
        lib: Lib::Es5,
    },
    LibEntry {
        name: "isFinite",
        lib: Lib::Es5,
    },
    LibEntry {
        name: "isNaN",
        lib: Lib::Es5,
    },
    LibEntry {
        name: "parseFloat",
        lib: Lib::Es5,
    },
    LibEntry {
        name: "parseInt",
        lib: Lib::Es5,
    },
    LibEntry {
        name: "decodeURI",
        lib: Lib::Es5,
    },
    LibEntry {
        name: "encodeURI",
        lib: Lib::Es5,
    },
    LibEntry {
        name: "escape",
        lib: Lib::Es5,
    },
    LibEntry {
        name: "eval",
        lib: Lib::Es5,
    },
    LibEntry {
        name: "decodeURIComponent",
        lib: Lib::Es5,
    },
    LibEntry {
        name: "encodeURIComponent",
        lib: Lib::Es5,
    },
    LibEntry {
        name: "unescape",
        lib: Lib::Es5,
    },
    LibEntry {
        name: "Object",
        lib: Lib::Es5,
    },
    LibEntry {
        name: "Function",
        lib: Lib::Es5,
    },
    LibEntry {
        name: "Boolean",
        lib: Lib::Es5,
    },
    LibEntry {
        name: "Symbol",
        lib: Lib::Es2015,
    },
    LibEntry {
        name: "Error",
        lib: Lib::Es5,
    },
    LibEntry {
        name: "AggregateError",
        lib: Lib::Es2021Promise,
    },
    LibEntry {
        name: "EvalError",
        lib: Lib::Es5,
    },
    LibEntry {
        name: "RangeError",
        lib: Lib::Es5,
    },
    LibEntry {
        name: "ReferenceError",
        lib: Lib::Es5,
    },
    LibEntry {
        name: "SyntaxError",
        lib: Lib::Es5,
    },
    LibEntry {
        name: "TypeError",
        lib: Lib::Es5,
    },
    LibEntry {
        name: "URIError",
        lib: Lib::Es5,
    },
    LibEntry {
        name: "Number",
        lib: Lib::Es5,
    },
    LibEntry {
        name: "Date",
        lib: Lib::Es5,
    },
    LibEntry {
        name: "String",
        lib: Lib::Es5,
    },
    LibEntry {
        name: "RegExp",
        lib: Lib::Es5,
    },
    LibEntry {
        name: "Array",
        lib: Lib::Es5,
    },
    LibEntry {
        name: "Uint8Array",
        lib: Lib::Es5,
    },
    LibEntry {
        name: "ArrayBuffer",
        lib: Lib::Es5,
    },
    LibEntry {
        name: "DataView",
        lib: Lib::Es5,
    },
    LibEntry {
        name: "Int8Array",
        lib: Lib::Es5,
    },
    LibEntry {
        name: "Uint8ClampedArray",
        lib: Lib::Es5,
    },
    LibEntry {
        name: "Int16Array",
        lib: Lib::Es5,
    },
    LibEntry {
        name: "Uint16Array",
        lib: Lib::Es5,
    },
    LibEntry {
        name: "Int32Array",
        lib: Lib::Es5,
    },
    LibEntry {
        name: "Uint32Array",
        lib: Lib::Es5,
    },
    LibEntry {
        name: "Float32Array",
        lib: Lib::Es5,
    },
    LibEntry {
        name: "Float64Array",
        lib: Lib::Es5,
    },
    LibEntry {
        name: "Map",
        lib: Lib::Es2015,
    },
    LibEntry {
        name: "Set",
        lib: Lib::Es2015,
    },
    LibEntry {
        name: "WeakMap",
        lib: Lib::Es2015,
    },
    LibEntry {
        name: "WeakSet",
        lib: Lib::Es2015,
    },
    LibEntry {
        name: "Atomics",
        lib: Lib::Es2017SharedMemory,
    },
    LibEntry {
        name: "JSON",
        lib: Lib::Es5,
    },
    LibEntry {
        name: "Proxy",
        lib: Lib::Es2015,
    },
    LibEntry {
        name: "Reflect",
        lib: Lib::Es2015,
    },
    LibEntry {
        name: "SharedArrayBuffer",
        lib: Lib::Es2017SharedMemory,
    },
    LibEntry {
        name: "BigInt",
        lib: Lib::Es2020BigInt,
    },
    LibEntry {
        name: "BigInt64Array",
        lib: Lib::Es2020BigInt,
    },
    LibEntry {
        name: "BigUint64Array",
        lib: Lib::Es2020BigInt,
    },
    LibEntry {
        name: "Float16Array",
        lib: Lib::Es2025Float16,
    },
    LibEntry {
        name: "WeakRef",
        lib: Lib::Es2021WeakRef,
    },
    LibEntry {
        name: "FinalizationRegistry",
        lib: Lib::Es2021WeakRef,
    },
    LibEntry {
        name: "DisposableStack",
        lib: Lib::EsnextDisposable,
    },
    LibEntry {
        name: "AsyncDisposableStack",
        lib: Lib::EsnextDisposable,
    },
    LibEntry {
        name: "Iterator",
        lib: Lib::Es2025Iterator,
    },
    LibEntry {
        name: "Intl",
        lib: Lib::Es5,
    },
    LibEntry {
        name: "Temporal",
        lib: Lib::EsnextTemporal,
    },
    LibEntry {
        name: "Math",
        lib: Lib::Es5,
    },
    LibEntry {
        name: "Promise",
        lib: Lib::Es2015,
    },
    LibEntry {
        name: "SuppressedError",
        lib: Lib::EsnextDisposable,
    },
    LibEntry {
        name: "global",
        lib: Lib::Always,
    },
    LibEntry {
        name: "globalThis",
        lib: Lib::Always,
    },
    LibEntry {
        name: "structuredClone",
        lib: Lib::Dom,
    },
    LibEntry {
        name: "console",
        lib: Lib::Dom,
    },
    LibEntry {
        name: "process",
        lib: Lib::Always,
    },
    LibEntry {
        name: "setTimeout",
        lib: Lib::Dom,
    },
    LibEntry {
        name: "clearTimeout",
        lib: Lib::Dom,
    },
    LibEntry {
        name: "setInterval",
        lib: Lib::Dom,
    },
    LibEntry {
        name: "clearInterval",
        lib: Lib::Dom,
    },
    LibEntry {
        name: "queueMicrotask",
        lib: Lib::Dom,
    },
    LibEntry {
        name: "fetch",
        lib: Lib::Dom,
    },
    LibEntry {
        name: "requestAnimationFrame",
        lib: Lib::Dom,
    },
    LibEntry {
        name: "cancelAnimationFrame",
        lib: Lib::Dom,
    },
    LibEntry {
        name: "alert",
        lib: Lib::Dom,
    },
    LibEntry {
        name: "confirm",
        lib: Lib::Dom,
    },
    LibEntry {
        name: "prompt",
        lib: Lib::Dom,
    },
    LibEntry {
        name: "atob",
        lib: Lib::Dom,
    },
    LibEntry {
        name: "btoa",
        lib: Lib::Dom,
    },
    LibEntry {
        name: "window",
        lib: Lib::Dom,
    },
    LibEntry {
        name: "document",
        lib: Lib::Dom,
    },
    LibEntry {
        name: "navigator",
        lib: Lib::Dom,
    },
    LibEntry {
        name: "self",
        lib: Lib::Dom,
    },
    LibEntry {
        name: "top",
        lib: Lib::Dom,
    },
    LibEntry {
        name: "parent",
        lib: Lib::Dom,
    },
    LibEntry {
        name: "frames",
        lib: Lib::Dom,
    },
    LibEntry {
        name: "location",
        lib: Lib::Dom,
    },
    LibEntry {
        name: "history",
        lib: Lib::Dom,
    },
    LibEntry {
        name: "screen",
        lib: Lib::Dom,
    },
    LibEntry {
        name: "performance",
        lib: Lib::Dom,
    },
    LibEntry {
        name: "crypto",
        lib: Lib::Dom,
    },
    LibEntry {
        name: "indexedDB",
        lib: Lib::Dom,
    },
    LibEntry {
        name: "localStorage",
        lib: Lib::Dom,
    },
    LibEntry {
        name: "sessionStorage",
        lib: Lib::Dom,
    },
    LibEntry {
        name: "caches",
        lib: Lib::Dom,
    },
    LibEntry {
        name: "customElements",
        lib: Lib::Dom,
    },
    LibEntry {
        name: "matchMedia",
        lib: Lib::Dom,
    },
    LibEntry {
        name: "importScripts",
        lib: Lib::WebworkerImportscripts,
    },
    LibEntry {
        name: "WScript",
        lib: Lib::Scripthost,
    },
    LibEntry {
        name: "WSH",
        lib: Lib::Scripthost,
    },
    LibEntry {
        name: "Event",
        lib: Lib::Dom,
    },
    LibEntry {
        name: "CustomEvent",
        lib: Lib::Dom,
    },
    LibEntry {
        name: "EventTarget",
        lib: Lib::Dom,
    },
    LibEntry {
        name: "MessageChannel",
        lib: Lib::Dom,
    },
    LibEntry {
        name: "MessagePort",
        lib: Lib::Dom,
    },
    LibEntry {
        name: "MutationObserver",
        lib: Lib::Dom,
    },
    LibEntry {
        name: "Notification",
        lib: Lib::Dom,
    },
    LibEntry {
        name: "WebSocket",
        lib: Lib::Dom,
    },
    LibEntry {
        name: "Worker",
        lib: Lib::Dom,
    },
    LibEntry {
        name: "SharedWorker",
        lib: Lib::Dom,
    },
    LibEntry {
        name: "XMLHttpRequest",
        lib: Lib::Dom,
    },
    LibEntry {
        name: "FormData",
        lib: Lib::Dom,
    },
    LibEntry {
        name: "Blob",
        lib: Lib::Dom,
    },
    LibEntry {
        name: "File",
        lib: Lib::Dom,
    },
    LibEntry {
        name: "FileReader",
        lib: Lib::Dom,
    },
    LibEntry {
        name: "Headers",
        lib: Lib::Dom,
    },
    LibEntry {
        name: "Request",
        lib: Lib::Dom,
    },
    LibEntry {
        name: "Response",
        lib: Lib::Dom,
    },
    LibEntry {
        name: "URL",
        lib: Lib::Dom,
    },
    LibEntry {
        name: "URLSearchParams",
        lib: Lib::Dom,
    },
    LibEntry {
        name: "TextEncoder",
        lib: Lib::Dom,
    },
    LibEntry {
        name: "TextDecoder",
        lib: Lib::Dom,
    },
    LibEntry {
        name: "AbortController",
        lib: Lib::Dom,
    },
    LibEntry {
        name: "AbortSignal",
        lib: Lib::Dom,
    },
    LibEntry {
        name: "DOMException",
        lib: Lib::Dom,
    },
    LibEntry {
        name: "Node",
        lib: Lib::Dom,
    },
    LibEntry {
        name: "NodeList",
        lib: Lib::Dom,
    },
    LibEntry {
        name: "Element",
        lib: Lib::Dom,
    },
    LibEntry {
        name: "HTMLElement",
        lib: Lib::Dom,
    },
    LibEntry {
        name: "Document",
        lib: Lib::Dom,
    },
    LibEntry {
        name: "Image",
        lib: Lib::Dom,
    },
    LibEntry {
        name: "Option",
        lib: Lib::Dom,
    },
    LibEntry {
        name: "webkitURL",
        lib: Lib::Dom,
    },
];

// These are the library names the checker can recognize in a type position.
// The current type algebra intentionally models their details as recovery
// types, but their presence remains explicit and separate from value bindings.
//
// Each entry is tagged with the `Lib` that first declares the *type*
// (interface/type/class) in the TypeScript 7.0.2 `lib.*.d.ts` authority.
const STANDARD_TYPES: &[LibEntry] = &[
    LibEntry {
        name: "Boolean",
        lib: Lib::Es5,
    },
    LibEntry {
        name: "Number",
        lib: Lib::Es5,
    },
    LibEntry {
        name: "String",
        lib: Lib::Es5,
    },
    LibEntry {
        name: "Symbol",
        lib: Lib::Es5,
    },
    LibEntry {
        name: "BigInt",
        lib: Lib::Es2020BigInt,
    },
    LibEntry {
        name: "PropertyKey",
        lib: Lib::Es5,
    },
    LibEntry {
        name: "Array",
        lib: Lib::Es5,
    },
    LibEntry {
        name: "ReadonlyArray",
        lib: Lib::Es5,
    },
    LibEntry {
        name: "ConcatArray",
        lib: Lib::Es5,
    },
    LibEntry {
        name: "Readonly",
        lib: Lib::Es5,
    },
    LibEntry {
        name: "Partial",
        lib: Lib::Es5,
    },
    LibEntry {
        name: "Required",
        lib: Lib::Es5,
    },
    LibEntry {
        name: "Record",
        lib: Lib::Es5,
    },
    LibEntry {
        name: "Pick",
        lib: Lib::Es5,
    },
    LibEntry {
        name: "Omit",
        lib: Lib::Es5,
    },
    LibEntry {
        name: "Exclude",
        lib: Lib::Es5,
    },
    LibEntry {
        name: "Extract",
        lib: Lib::Es5,
    },
    LibEntry {
        name: "NonNullable",
        lib: Lib::Es5,
    },
    LibEntry {
        name: "ReturnType",
        lib: Lib::Es5,
    },
    LibEntry {
        name: "Parameters",
        lib: Lib::Es5,
    },
    LibEntry {
        name: "ConstructorParameters",
        lib: Lib::Es5,
    },
    LibEntry {
        name: "InstanceType",
        lib: Lib::Es5,
    },
    LibEntry {
        name: "ThisParameterType",
        lib: Lib::Es5,
    },
    LibEntry {
        name: "OmitThisParameter",
        lib: Lib::Es5,
    },
    LibEntry {
        name: "ThisType",
        lib: Lib::Es5,
    },
    LibEntry {
        name: "Awaited",
        lib: Lib::Es5,
    },
    LibEntry {
        name: "Uppercase",
        lib: Lib::Es5,
    },
    LibEntry {
        name: "Lowercase",
        lib: Lib::Es5,
    },
    LibEntry {
        name: "Capitalize",
        lib: Lib::Es5,
    },
    LibEntry {
        name: "Uncapitalize",
        lib: Lib::Es5,
    },
    LibEntry {
        name: "Promise",
        lib: Lib::Es5,
    },
    LibEntry {
        name: "PromiseLike",
        lib: Lib::Es5,
    },
    LibEntry {
        name: "Map",
        lib: Lib::Es2015,
    },
    LibEntry {
        name: "ReadonlyMap",
        lib: Lib::Es2015,
    },
    LibEntry {
        name: "Set",
        lib: Lib::Es2015,
    },
    LibEntry {
        name: "ReadonlySet",
        lib: Lib::Es2015,
    },
    LibEntry {
        name: "WeakMap",
        lib: Lib::Es2015,
    },
    LibEntry {
        name: "WeakSet",
        lib: Lib::Es2015,
    },
    LibEntry {
        name: "Date",
        lib: Lib::Es5,
    },
    LibEntry {
        name: "RegExp",
        lib: Lib::Es5,
    },
    LibEntry {
        name: "Atomics",
        lib: Lib::Es2017SharedMemory,
    },
    LibEntry {
        name: "JSON",
        lib: Lib::Es5,
    },
    LibEntry {
        name: "Math",
        lib: Lib::Es5,
    },
    LibEntry {
        name: "Error",
        lib: Lib::Es5,
    },
    LibEntry {
        name: "AggregateError",
        lib: Lib::Es2021Promise,
    },
    LibEntry {
        name: "EvalError",
        lib: Lib::Es5,
    },
    LibEntry {
        name: "RangeError",
        lib: Lib::Es5,
    },
    LibEntry {
        name: "ReferenceError",
        lib: Lib::Es5,
    },
    LibEntry {
        name: "SyntaxError",
        lib: Lib::Es5,
    },
    LibEntry {
        name: "TypeError",
        lib: Lib::Es5,
    },
    LibEntry {
        name: "URIError",
        lib: Lib::Es5,
    },
    LibEntry {
        name: "SuppressedError",
        lib: Lib::EsnextDisposable,
    },
    LibEntry {
        name: "Object",
        lib: Lib::Es5,
    },
    LibEntry {
        name: "Function",
        lib: Lib::Es5,
    },
    LibEntry {
        name: "CallableFunction",
        lib: Lib::Es5,
    },
    LibEntry {
        name: "NewableFunction",
        lib: Lib::Es5,
    },
    LibEntry {
        name: "Iterable",
        lib: Lib::Es2015,
    },
    LibEntry {
        name: "Iterator",
        lib: Lib::Es2015,
    },
    LibEntry {
        name: "AsyncIterable",
        lib: Lib::Es2018AsyncIterable,
    },
    LibEntry {
        name: "IterableIterator",
        lib: Lib::Es2015,
    },
    LibEntry {
        name: "AsyncIterableIterator",
        lib: Lib::Es2018AsyncIterable,
    },
    LibEntry {
        name: "AsyncIterator",
        lib: Lib::Es2018AsyncIterable,
    },
    LibEntry {
        name: "Generator",
        lib: Lib::Es2015,
    },
    LibEntry {
        name: "AsyncGenerator",
        lib: Lib::Es2018AsyncIterable,
    },
    LibEntry {
        name: "ArrayLike",
        lib: Lib::Es5,
    },
    LibEntry {
        name: "ArrayBuffer",
        lib: Lib::Es5,
    },
    LibEntry {
        name: "ArrayBufferLike",
        lib: Lib::Es5,
    },
    LibEntry {
        name: "ArrayBufferView",
        lib: Lib::Es5,
    },
    LibEntry {
        name: "DataView",
        lib: Lib::Es5,
    },
    LibEntry {
        name: "SharedArrayBuffer",
        lib: Lib::Es2017SharedMemory,
    },
    LibEntry {
        name: "Int8Array",
        lib: Lib::Es5,
    },
    LibEntry {
        name: "Uint8Array",
        lib: Lib::Es5,
    },
    LibEntry {
        name: "Uint8ClampedArray",
        lib: Lib::Es5,
    },
    LibEntry {
        name: "Int16Array",
        lib: Lib::Es5,
    },
    LibEntry {
        name: "Uint16Array",
        lib: Lib::Es5,
    },
    LibEntry {
        name: "Int32Array",
        lib: Lib::Es5,
    },
    LibEntry {
        name: "Uint32Array",
        lib: Lib::Es5,
    },
    LibEntry {
        name: "BigInt64Array",
        lib: Lib::Es2020BigInt,
    },
    LibEntry {
        name: "BigUint64Array",
        lib: Lib::Es2020BigInt,
    },
    LibEntry {
        name: "Float16Array",
        lib: Lib::Es2025Float16,
    },
    LibEntry {
        name: "Float32Array",
        lib: Lib::Es5,
    },
    LibEntry {
        name: "Float64Array",
        lib: Lib::Es5,
    },
    LibEntry {
        name: "AbortSignal",
        lib: Lib::Dom,
    },
    LibEntry {
        name: "URL",
        lib: Lib::Dom,
    },
    LibEntry {
        name: "URLSearchParams",
        lib: Lib::Dom,
    },
    LibEntry {
        name: "TextEncoder",
        lib: Lib::Dom,
    },
    LibEntry {
        name: "TextDecoder",
        lib: Lib::Dom,
    },
    LibEntry {
        name: "NoInfer",
        lib: Lib::Es5,
    },
    LibEntry {
        name: "TemplateStringsArray",
        lib: Lib::Es5,
    },
    LibEntry {
        name: "PropertyDescriptor",
        lib: Lib::Es5,
    },
    LibEntry {
        name: "TypedPropertyDescriptor",
        lib: Lib::Es5,
    },
    LibEntry {
        name: "IteratorResult",
        lib: Lib::Es2015,
    },
    LibEntry {
        name: "FlatArray",
        lib: Lib::Es2019Array,
    },
    LibEntry {
        name: "HTMLElement",
        lib: Lib::Dom,
    },
    LibEntry {
        name: "HTMLElementTagNameMap",
        lib: Lib::Dom,
    },
    LibEntry {
        name: "ElementTagNameMap",
        lib: Lib::Dom,
    },
    LibEntry {
        name: "DocumentEventMap",
        lib: Lib::Dom,
    },
    LibEntry {
        name: "WeakRef",
        lib: Lib::Es2021WeakRef,
    },
    LibEntry {
        name: "FinalizationRegistry",
        lib: Lib::Es2021WeakRef,
    },
    LibEntry {
        name: "Temporal",
        lib: Lib::EsnextTemporal,
    },
    LibEntry {
        name: "Intl",
        lib: Lib::Es5,
    },
    LibEntry {
        name: "RequestInit",
        lib: Lib::Dom,
    },
    LibEntry {
        name: "ResponseInit",
        lib: Lib::Dom,
    },
    LibEntry {
        name: "ClassDecorator",
        lib: Lib::DecoratorsLegacy,
    },
    LibEntry {
        name: "PropertyDecorator",
        lib: Lib::DecoratorsLegacy,
    },
    LibEntry {
        name: "MethodDecorator",
        lib: Lib::DecoratorsLegacy,
    },
    LibEntry {
        name: "ParameterDecorator",
        lib: Lib::DecoratorsLegacy,
    },
    LibEntry {
        name: "ImportMeta",
        lib: Lib::Es5,
    },
];

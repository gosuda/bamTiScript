//! The lane workers compile on the main thread, and the compiler recurses. Linux
//! and macOS give that thread 8 MiB and `link.exe` gives it 1 MiB, on which a deep
//! conformance case would end a worker with a crash instead of a result.

fn main() {
    println!("cargo:rerun-if-changed=build.rs");
    if std::env::var_os("CARGO_CFG_TARGET_ENV").is_some_and(|environment| environment == "msvc") {
        println!("cargo:rustc-link-arg-bins=/STACK:8388608");
    }
}

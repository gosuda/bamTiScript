#![forbid(unsafe_code)]

pub mod api_server;
pub mod args;
pub mod cli;
pub mod context;
pub mod diagnostics;
pub mod driver;
pub mod lsp;
pub mod output;
#[cfg(any(target_env = "msvc", test))]
mod windows_link;

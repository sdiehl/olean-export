use crate::olean::SUPPORTED;
use std::{
    fmt::Display,
    io,
    path::{Path, PathBuf},
};

/// Everything that can go wrong loading oleans or writing an export.
#[derive(Debug, thiserror::Error)]
#[non_exhaustive]
pub enum Error {
    #[error(transparent)]
    Io(#[from] io::Error),
    #[error("module {0} not found on LEAN_PATH")]
    ModuleNotFound(String),
    #[error("not an olean file")]
    NotOlean,
    #[error("unsupported olean format {0}")]
    Format(u8),
    #[error(
        "built by Lean {0}, but only 4.{lo} to 4.{hi} are supported",
        lo = SUPPORTED.start(),
        hi = SUPPORTED.end()
    )]
    UnsupportedLean(String),
    /// The file is malformed, or the environment it describes is inconsistent.
    #[error("{0}")]
    Corrupt(String),
    #[error("{}: {source}", path.display())]
    File { path: PathBuf, source: Box<Self> },
    #[error(transparent)]
    Threads(#[from] rayon::ThreadPoolBuildError),
}

pub type Result<T, E = Error> = std::result::Result<T, E>;

pub(crate) fn corrupt(msg: impl Display) -> Error {
    Error::Corrupt(msg.to_string())
}

pub(crate) fn at(path: &Path) -> impl FnOnce(Error) -> Error + '_ {
    move |e| Error::File {
        path: path.to_owned(),
        source: Box::new(e),
    }
}

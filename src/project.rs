use std::path::{Path, PathBuf};

use thiserror::Error;

/// Represents the project directory, which contains the project configuration
/// in the form of YAML files.
pub struct ProjectDir {}

impl ProjectDir {
    /// Loads the project directory from the provided path.
    /// This parses all the YAML files in the directory and constructs the
    /// internal representation of the project.
    pub fn load_dir(path: &Path) -> Result<Self, Vec<LoadError>> {
        todo!()
    }
}

#[derive(Debug, Error)]
pub enum LoadError {
    #[error("The provided path is not a directory")]
    PathNotDirectory,

    #[error("IO error occurred while loading the project directory. {0}")]
    IoError(#[from] std::io::Error),

    #[error("Directory contains file that is not recognized by Permute framework: `{0}`")]
    NotPermuteFile(PathBuf),
}

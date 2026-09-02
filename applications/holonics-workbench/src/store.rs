use std::fs;
use std::path::Path;

use crate::runtime::WorkbenchError;

pub fn read(path: &Path) -> Result<Vec<u8>, WorkbenchError> {
    fs::read(path).map_err(|error| WorkbenchError::Io {
        path: path.to_path_buf(),
        reason: error.to_string(),
    })
}

pub fn write(path: &Path, bytes: &[u8]) -> Result<(), WorkbenchError> {
    if let Some(parent) = path
        .parent()
        .filter(|parent| !parent.as_os_str().is_empty())
    {
        fs::create_dir_all(parent).map_err(|error| WorkbenchError::Io {
            path: parent.to_path_buf(),
            reason: error.to_string(),
        })?;
    }
    fs::write(path, bytes).map_err(|error| WorkbenchError::Io {
        path: path.to_path_buf(),
        reason: error.to_string(),
    })
}

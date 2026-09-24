use std::fs;
use std::path::Path;

use crate::runtime::WorkbenchError;

pub fn read(path: &Path) -> Result<Vec<u8>, WorkbenchError> {
    fs::read(path).map_err(|error| WorkbenchError::Io {
        path: path.to_path_buf(),
        reason: error.to_string(),
    })
}

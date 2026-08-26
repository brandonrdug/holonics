use std::{fs, path::Path};

use serde::Serialize;
use sha2::{Digest, Sha256};

pub fn read(path: impl AsRef<Path>) -> Result<Vec<u8>, String> {
    let path = path.as_ref();
    fs::read(path).map_err(|error| format!("read {}: {error}", path.display()))
}

pub fn write(path: impl AsRef<Path>, bytes: &[u8]) -> Result<(), String> {
    let path = path.as_ref();
    fs::write(path, bytes).map_err(|error| format!("write {}: {error}", path.display()))
}

pub fn write_json(path: impl AsRef<Path>, value: &impl Serialize) -> Result<Vec<u8>, String> {
    let path = path.as_ref();
    let mut bytes = serde_json::to_vec_pretty(value).map_err(|error| error.to_string())?;
    bytes.push(b'\n');
    write(path, &bytes)?;
    Ok(bytes)
}

pub fn digest(bytes: impl AsRef<[u8]>) -> String {
    Sha256::digest(bytes.as_ref())
        .iter()
        .map(|octet| format!("{octet:02x}"))
        .collect()
}

pub fn value_digest(value: &impl Serialize) -> Result<String, String> {
    serde_json::to_vec(value)
        .map(digest)
        .map_err(|error| error.to_string())
}

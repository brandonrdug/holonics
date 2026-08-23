use std::fs;
use std::path::{Path, PathBuf};

use serde::Serialize;
use serde_json::{json, Value};
use sha2::{Digest, Sha256};

pub fn digest(bytes: &[u8]) -> String {
    Sha256::digest(bytes)
        .iter()
        .map(|octet| format!("{octet:02x}"))
        .collect()
}

pub fn digest_paths(paths: &[PathBuf]) -> Result<String, String> {
    let mut hasher = Sha256::new();
    for path in paths {
        let bytes = fs::read(path).map_err(|error| format!("read {}: {error}", path.display()))?;
        hasher.update(path.to_string_lossy().as_bytes());
        hasher.update((bytes.len() as u64).to_le_bytes());
        hasher.update(digest(&bytes).as_bytes());
    }
    Ok(hasher
        .finalize()
        .iter()
        .map(|octet| format!("{octet:02x}"))
        .collect())
}

pub fn write_json(path: &Path, value: &impl Serialize) -> Result<Vec<u8>, String> {
    let mut bytes = serde_json::to_vec_pretty(value).map_err(|error| error.to_string())?;
    bytes.push(b'\n');
    fs::write(path, &bytes).map_err(|error| format!("write {}: {error}", path.display()))?;
    Ok(bytes)
}

pub fn read_json(path: &Path) -> Result<(Vec<u8>, Value), String> {
    let bytes = fs::read(path).map_err(|error| format!("read {}: {error}", path.display()))?;
    let value = serde_json::from_slice(&bytes)
        .map_err(|error| format!("parse {}: {error}", path.display()))?;
    Ok((bytes, value))
}

pub fn regular_files(directory: &Path) -> Result<Vec<PathBuf>, String> {
    fn visit(path: &Path, returned: &mut Vec<PathBuf>) -> Result<(), String> {
        for entry in fs::read_dir(path).map_err(|error| error.to_string())? {
            let entry = entry.map_err(|error| error.to_string())?;
            let path = entry.path();
            if path.is_dir() {
                visit(&path, returned)?;
            } else if path.is_file() {
                returned.push(path);
            }
        }
        Ok(())
    }
    let mut returned = Vec::new();
    visit(directory, &mut returned)?;
    returned.sort();
    Ok(returned)
}

pub fn write_manifest(directory: &Path) -> Result<Value, String> {
    let mut paths = regular_files(directory)?;
    paths.retain(|path| path.file_name().is_none_or(|name| name != "MANIFEST.json"));
    let mut rolled = Sha256::new();
    let mut files = Vec::new();
    for path in paths {
        let relative = path
            .strip_prefix(directory)
            .map_err(|error| error.to_string())?
            .to_string_lossy()
            .into_owned();
        let bytes = fs::read(&path).map_err(|error| error.to_string())?;
        let sha256 = digest(&bytes);
        rolled.update(relative.as_bytes());
        rolled.update((bytes.len() as u64).to_le_bytes());
        rolled.update(sha256.as_bytes());
        files.push(json!({"path": relative, "octets": bytes.len(), "sha256": sha256}));
    }
    let manifest = json!({
        "schema": "holonics.r5.product-manifest.v1",
        "truth_status": "measured",
        "files": files,
        "rolled_sha256": rolled.finalize().iter().map(|octet| format!("{octet:02x}")).collect::<String>(),
    });
    write_json(&directory.join("MANIFEST.json"), &manifest)?;
    Ok(manifest)
}

pub fn descriptors() -> Vec<String> {
    let Ok(entries) = fs::read_dir("/proc/self/fd") else {
        return Vec::new();
    };
    let mut paths = entries
        .flatten()
        .filter_map(|entry| fs::read_link(entry.path()).ok())
        .map(|path| path.to_string_lossy().into_owned())
        .collect::<Vec<_>>();
    paths.sort();
    paths.dedup();
    paths
}

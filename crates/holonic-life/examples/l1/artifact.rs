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

pub fn write_json(path: impl AsRef<Path>, value: &impl Serialize) -> Result<Vec<u8>, String> {
    let path = path.as_ref();
    let mut bytes = serde_json::to_vec_pretty(value).map_err(|error| error.to_string())?;
    bytes.push(b'\n');
    fs::write(path, &bytes).map_err(|error| format!("write {}: {error}", path.display()))?;
    Ok(bytes)
}

pub fn regular_files(directory: &Path) -> Result<Vec<PathBuf>, String> {
    fn visit(path: &Path, files: &mut Vec<PathBuf>) -> Result<(), String> {
        for entry in fs::read_dir(path).map_err(|error| error.to_string())? {
            let entry = entry.map_err(|error| error.to_string())?;
            let path = entry.path();
            if path.is_dir() {
                visit(&path, files)?;
            } else if path.is_file() {
                files.push(path);
            }
        }
        Ok(())
    }
    let mut files = Vec::new();
    visit(directory, &mut files)?;
    files.sort();
    Ok(files)
}

pub fn manifest(directory: &Path) -> Result<Value, String> {
    let mut files = regular_files(directory)?;
    files.retain(|path| path.file_name().is_none_or(|name| name != "MANIFEST.json"));
    let mut rolled = Sha256::new();
    let mut identities = Vec::new();
    for path in files {
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
        identities.push(json!({"path": relative, "octets": bytes.len(), "sha256": sha256}));
    }
    let returned = json!({
        "schema": "holonics.l1.product-manifest.v1",
        "truth_status": "measured",
        "files": identities,
        "rolled_sha256": rolled.finalize().iter().map(|octet| format!("{octet:02x}")).collect::<String>(),
    });
    write_json(directory.join("MANIFEST.json"), &returned)?;
    Ok(returned)
}

pub fn descriptors() -> Vec<String> {
    let Ok(entries) = fs::read_dir("/proc/self/fd") else {
        return Vec::new();
    };
    let mut targets = entries
        .flatten()
        .filter_map(|entry| fs::read_link(entry.path()).ok())
        .map(|path| path.to_string_lossy().into_owned())
        .collect::<Vec<_>>();
    targets.sort();
    targets.dedup();
    targets
}

use std::fs;
use std::path::Path;

use serde::Serialize;
use serde_json::{json, Value};
use sha2::{Digest, Sha256};

pub fn read_json(path: &Path) -> Result<(Vec<u8>, Value), String> {
    let bytes = fs::read(path).map_err(|error| format!("read {}: {error}", path.display()))?;
    let value = serde_json::from_slice(&bytes)
        .map_err(|error| format!("decode {}: {error}", path.display()))?;
    Ok((bytes, value))
}

pub fn write_json(path: &Path, value: &impl Serialize) -> Result<(), String> {
    let bytes = serde_json::to_vec_pretty(value).map_err(|error| error.to_string())?;
    fs::write(path, bytes).map_err(|error| format!("write {}: {error}", path.display()))
}

pub fn digest(bytes: &[u8]) -> String {
    Sha256::digest(bytes)
        .iter()
        .map(|octet| format!("{octet:02x}"))
        .collect()
}

pub fn write_manifest(directory: &Path) -> Result<Value, String> {
    let mut paths = fs::read_dir(directory)
        .map_err(|error| error.to_string())?
        .filter_map(Result::ok)
        .map(|entry| entry.path())
        .filter(|path| {
            path.is_file() && path.file_name().is_some_and(|name| name != "MANIFEST.json")
        })
        .collect::<Vec<_>>();
    paths.sort();
    let files = paths
        .iter()
        .map(|path| {
            let bytes = fs::read(path).map_err(|error| error.to_string())?;
            Ok(json!({
                "path": path.file_name().unwrap().to_string_lossy(),
                "octets": bytes.len(),
                "sha256": digest(&bytes),
            }))
        })
        .collect::<Result<Vec<_>, String>>()?;
    let rolled = files
        .iter()
        .flat_map(|file| file["sha256"].as_str().unwrap_or("").bytes())
        .collect::<Vec<_>>();
    let manifest = json!({
        "schema": "holonics.r3.product-manifest.v1",
        "truth_status": "implemented-exact",
        "files": files,
        "rolled_sha256": digest(&rolled),
    });
    write_json(&directory.join("MANIFEST.json"), &manifest)?;
    Ok(manifest)
}

pub fn descriptors() -> Vec<String> {
    let mut paths = Vec::new();
    if let Ok(entries) = fs::read_dir("/proc/self/fd") {
        for entry in entries.flatten() {
            if let Ok(target) = fs::read_link(entry.path()) {
                paths.push(target.to_string_lossy().into_owned());
            }
        }
    }
    paths.sort();
    paths.dedup();
    paths
}

pub fn traces(words: &[u32], lengths: &[u32], stride: usize) -> Result<Vec<Vec<u32>>, String> {
    if words.len() != lengths.len() * stride {
        return Err("the returned trace rectangle is inconsistent".to_owned());
    }
    lengths
        .iter()
        .enumerate()
        .map(|(at, length)| {
            let length = *length as usize;
            if !(2..=stride).contains(&length) {
                return Err("a returned recurrence did not close".to_owned());
            }
            Ok(words[at * stride..at * stride + length].to_vec())
        })
        .collect()
}

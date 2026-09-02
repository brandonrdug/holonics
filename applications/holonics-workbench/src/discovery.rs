use std::collections::BTreeMap;
use std::fs;
use std::path::{Path, PathBuf};

use serde::{Deserialize, Serialize};

use crate::runtime::WorkbenchError;

const DISCOVERY_FILE_LIMIT: usize = 20_000;
const DISCOVERY_DEPTH_LIMIT: usize = 8;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum WorkbenchResourceKind {
    Directory,
    ModelConfiguration,
    ShardedWeightIndex,
    Onnx,
    CirculationSnapshot,
    MorphologyPackage,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct WorkbenchResource {
    pub kind: WorkbenchResourceKind,
    pub label: String,
    pub path: PathBuf,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct WorkbenchDiscovery {
    pub root: PathBuf,
    pub resources: Vec<WorkbenchResource>,
    pub visited_files: usize,
    pub truncated: bool,
}

pub fn workspace_root(start: &Path) -> PathBuf {
    let mut cursor = start.to_path_buf();
    loop {
        if cursor.join("Cargo.toml").is_file() && cursor.join("blueprint/THE_ROADMAP.md").is_file()
        {
            return cursor;
        }
        let Some(parent) = cursor.parent() else {
            return start.to_path_buf();
        };
        cursor = parent.to_path_buf();
    }
}

pub fn home_directory() -> Option<PathBuf> {
    std::env::var_os("HOME").map(PathBuf::from)
}

pub fn artifact_root() -> Result<PathBuf, WorkbenchError> {
    let home = home_directory().ok_or_else(|| {
        WorkbenchError::Owner(
            "the operating environment supplied no home directory for Workbench artifacts"
                .to_owned(),
        )
    })?;
    Ok(home.join(".local/share/holonics-workbench"))
}

pub fn list_directory(directory: &Path) -> Result<Vec<WorkbenchResource>, WorkbenchError> {
    let mut entries = fs::read_dir(directory)
        .map_err(|error| WorkbenchError::Io {
            path: directory.to_path_buf(),
            reason: error.to_string(),
        })?
        .filter_map(Result::ok)
        .filter_map(|entry| {
            let path = entry.path();
            if path.is_dir() && !ignored_directory(&path) {
                Some(WorkbenchResource {
                    kind: WorkbenchResourceKind::Directory,
                    label: entry.file_name().to_string_lossy().into_owned(),
                    path,
                })
            } else {
                classify_file(&path).map(|kind| WorkbenchResource {
                    kind,
                    label: entry.file_name().to_string_lossy().into_owned(),
                    path,
                })
            }
        })
        .collect::<Vec<_>>();
    entries.sort_by(|left, right| {
        let left_directory = left.kind == WorkbenchResourceKind::Directory;
        let right_directory = right.kind == WorkbenchResourceKind::Directory;
        right_directory
            .cmp(&left_directory)
            .then_with(|| left.label.to_lowercase().cmp(&right.label.to_lowercase()))
    });
    Ok(entries)
}

pub fn discover(root: &Path) -> Result<WorkbenchDiscovery, WorkbenchError> {
    let root = root.canonicalize().map_err(|error| WorkbenchError::Io {
        path: root.to_path_buf(),
        reason: error.to_string(),
    })?;
    let mut resources = Vec::new();
    let mut pending = vec![(root.clone(), 0usize)];
    let mut visited_files = 0usize;
    let mut truncated = false;
    while let Some((directory, depth)) = pending.pop() {
        if depth > DISCOVERY_DEPTH_LIMIT {
            truncated = true;
            continue;
        }
        let listing = fs::read_dir(&directory).map_err(|error| WorkbenchError::Io {
            path: directory.clone(),
            reason: error.to_string(),
        })?;
        for entry in listing.flatten() {
            let path = entry.path();
            if path.is_dir() {
                if !ignored_directory(&path) {
                    pending.push((path, depth + 1));
                }
                continue;
            }
            visited_files = visited_files.saturating_add(1);
            if visited_files > DISCOVERY_FILE_LIMIT {
                truncated = true;
                pending.clear();
                break;
            }
            if let Some(kind) = classify_file(&path) {
                resources.push(WorkbenchResource {
                    kind,
                    label: path
                        .strip_prefix(&root)
                        .unwrap_or(&path)
                        .display()
                        .to_string(),
                    path,
                });
            }
        }
    }
    resources.sort_by(|left, right| left.label.cmp(&right.label));
    Ok(WorkbenchDiscovery {
        root,
        resources,
        visited_files,
        truncated,
    })
}

pub fn classify_file(path: &Path) -> Option<WorkbenchResourceKind> {
    let name = path.file_name()?.to_string_lossy().to_lowercase();
    if name.ends_with(".safetensors.index.json") {
        Some(WorkbenchResourceKind::ShardedWeightIndex)
    } else if name.ends_with(".snapshot.json") {
        Some(WorkbenchResourceKind::CirculationSnapshot)
    } else if name.ends_with(".morphology.json") || name.ends_with(".package.json") {
        Some(WorkbenchResourceKind::MorphologyPackage)
    } else if name.ends_with(".onnx") {
        Some(WorkbenchResourceKind::Onnx)
    } else if name == "config.json"
        || name.ends_with(".config.json")
        || (path.extension().and_then(|extension| extension.to_str()) == Some("json")
            && path
                .parent()
                .and_then(Path::file_name)
                .is_some_and(|parent| parent == "configurations"))
    {
        Some(WorkbenchResourceKind::ModelConfiguration)
    } else {
        None
    }
}

pub fn dominant_source_extension(root: &Path) -> Result<String, WorkbenchError> {
    let mut counts = BTreeMap::<String, usize>::new();
    let mut pending = vec![(root.to_path_buf(), 0usize)];
    let mut visited = 0usize;
    while let Some((directory, depth)) = pending.pop() {
        if depth > DISCOVERY_DEPTH_LIMIT || visited >= DISCOVERY_FILE_LIMIT {
            continue;
        }
        let listing = fs::read_dir(&directory).map_err(|error| WorkbenchError::Io {
            path: directory.clone(),
            reason: error.to_string(),
        })?;
        for entry in listing.flatten() {
            let path = entry.path();
            if path.is_dir() {
                if !ignored_directory(&path) {
                    pending.push((path, depth + 1));
                }
            } else {
                visited = visited.saturating_add(1);
                if let Some(extension @ ("rs" | "lean" | "md")) =
                    path.extension().and_then(|value| value.to_str())
                {
                    *counts.entry(extension.to_owned()).or_default() += 1;
                }
            }
        }
    }
    counts
        .into_iter()
        .max_by(
            |(left_extension, left_count), (right_extension, right_count)| {
                left_count
                    .cmp(right_count)
                    .then_with(|| right_extension.cmp(left_extension))
            },
        )
        .map(|(extension, _)| extension)
        .ok_or_else(|| {
            WorkbenchError::Owner(format!(
                "no Rust, Lean, or Markdown source material under {}",
                root.display()
            ))
        })
}

fn ignored_directory(path: &Path) -> bool {
    let Some(name) = path.file_name().and_then(|name| name.to_str()) else {
        return false;
    };
    name.starts_with('.') || matches!(name, "target" | "output" | "node_modules")
}

#[cfg(test)]
mod tests {
    use std::fs;

    use tempfile::tempdir;

    use super::*;

    #[test]
    fn directory_browser_and_discovery_return_only_actionable_resources() {
        let temporary = tempdir().expect("temporary");
        fs::create_dir(temporary.path().join("models")).expect("directory");
        fs::write(temporary.path().join("config.json"), b"{}").expect("config");
        fs::write(temporary.path().join("notes.txt"), b"cold").expect("notes");
        fs::write(temporary.path().join("model.onnx"), b"onnx").expect("onnx");
        let listed = list_directory(temporary.path()).expect("listing");
        assert_eq!(listed.len(), 3);
        assert_eq!(listed[0].kind, WorkbenchResourceKind::Directory);
        let discovered = discover(temporary.path()).expect("discover");
        assert_eq!(discovered.resources.len(), 2);
        assert!(!discovered.truncated);
    }
}

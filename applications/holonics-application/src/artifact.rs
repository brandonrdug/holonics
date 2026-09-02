use std::fs::{self, OpenOptions};
use std::io::Write;
use std::path::{Component, Path, PathBuf};

use serde::{de::DeserializeOwned, Serialize};

use crate::ApplicationError;

pub(crate) const MANIFEST_FILE: &str = "workspace.json";

#[derive(Debug)]
pub(crate) struct ArtifactStore {
    root: PathBuf,
}

impl ArtifactStore {
    pub fn create(root: &Path) -> Result<Self, ApplicationError> {
        fs::create_dir_all(root).map_err(|error| io(root, error))?;
        let root = root.canonicalize().map_err(|error| io(root, error))?;
        Ok(Self { root })
    }

    pub fn open(root: &Path) -> Result<Self, ApplicationError> {
        let root = root.canonicalize().map_err(|error| io(root, error))?;
        if !root.is_dir() {
            return Err(ApplicationError::Workspace(
                "the explicit workspace root is not a directory".to_owned(),
            ));
        }
        Ok(Self { root })
    }

    pub fn root(&self) -> &Path {
        &self.root
    }

    pub fn manifest_path(&self) -> PathBuf {
        self.root.join(MANIFEST_FILE)
    }

    pub fn read(&self, relative: &str) -> Result<Vec<u8>, ApplicationError> {
        let path = self.resolve_existing(relative)?;
        fs::read(&path).map_err(|error| io(&path, error))
    }

    pub fn read_json<T: DeserializeOwned>(&self, relative: &str) -> Result<T, ApplicationError> {
        serde_json::from_slice(&self.read(relative)?)
            .map_err(|error| ApplicationError::Wire(error.to_string()))
    }

    pub fn read_manifest<T: DeserializeOwned>(&self) -> Result<T, ApplicationError> {
        let path = self.manifest_path();
        let bytes = fs::read(&path).map_err(|error| io(&path, error))?;
        serde_json::from_slice(&bytes).map_err(|error| ApplicationError::Wire(error.to_string()))
    }

    pub fn write_new(&self, relative: &str, bytes: &[u8]) -> Result<PathBuf, ApplicationError> {
        let path = self.resolve_new(relative)?;
        if let Some(parent) = path.parent() {
            fs::create_dir_all(parent).map_err(|error| io(parent, error))?;
            self.ensure_contained(parent)?;
        }
        let mut file = OpenOptions::new()
            .create_new(true)
            .write(true)
            .open(&path)
            .map_err(|error| {
                if error.kind() == std::io::ErrorKind::AlreadyExists {
                    ApplicationError::ExistingArtifact(path.clone())
                } else {
                    io(&path, error)
                }
            })?;
        file.write_all(bytes).map_err(|error| io(&path, error))?;
        file.sync_all().map_err(|error| io(&path, error))?;
        Ok(path)
    }

    pub fn write_json_new<T: Serialize>(
        &self,
        relative: &str,
        value: &T,
    ) -> Result<PathBuf, ApplicationError> {
        let bytes = serde_json::to_vec_pretty(value)
            .map_err(|error| ApplicationError::Wire(error.to_string()))?;
        self.write_new(relative, &bytes)
    }

    pub fn replace_manifest<T: Serialize>(&self, value: &T) -> Result<(), ApplicationError> {
        self.replace_json_at(MANIFEST_FILE, value)
    }

    pub fn replace_json<T: Serialize>(
        &self,
        relative: &str,
        value: &T,
    ) -> Result<(), ApplicationError> {
        self.replace_json_at(relative, value)
    }

    fn replace_json_at<T: Serialize>(
        &self,
        relative: &str,
        value: &T,
    ) -> Result<(), ApplicationError> {
        let bytes = serde_json::to_vec_pretty(value)
            .map_err(|error| ApplicationError::Wire(error.to_string()))?;
        let destination = self.resolve_relative(relative)?;
        let parent = destination.parent().ok_or_else(|| {
            ApplicationError::Workspace("replacement artifact has no parent".to_owned())
        })?;
        fs::create_dir_all(parent).map_err(|error| io(parent, error))?;
        self.ensure_contained(parent)?;
        let name = destination
            .file_name()
            .and_then(|name| name.to_str())
            .ok_or_else(|| {
                ApplicationError::Workspace("artifact filename is not UTF-8".to_owned())
            })?;
        let mut ordinal = 0u64;
        let temporary = loop {
            let candidate = parent.join(format!(".{name}.next-{}-{ordinal}", std::process::id()));
            match OpenOptions::new()
                .create_new(true)
                .write(true)
                .open(&candidate)
            {
                Ok(mut file) => {
                    file.write_all(&bytes)
                        .map_err(|error| io(&candidate, error))?;
                    file.sync_all().map_err(|error| io(&candidate, error))?;
                    break candidate;
                }
                Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => {
                    ordinal = ordinal.checked_add(1).ok_or_else(|| {
                        ApplicationError::Workspace(
                            "manifest temporary-file ordinal overflow".to_owned(),
                        )
                    })?;
                }
                Err(error) => return Err(io(&candidate, error)),
            }
        };
        fs::rename(&temporary, &destination).map_err(|error| io(&destination, error))?;
        Ok(())
    }

    pub fn absolute(&self, relative: &str) -> Result<PathBuf, ApplicationError> {
        let path = self.resolve_relative(relative)?;
        Ok(path)
    }

    fn resolve_existing(&self, relative: &str) -> Result<PathBuf, ApplicationError> {
        let path = self.resolve_relative(relative)?;
        let canonical = path.canonicalize().map_err(|error| io(&path, error))?;
        if !canonical.starts_with(&self.root) {
            return Err(ApplicationError::RootEscape(path));
        }
        Ok(canonical)
    }

    fn resolve_new(&self, relative: &str) -> Result<PathBuf, ApplicationError> {
        let path = self.resolve_relative(relative)?;
        if path.exists() {
            return Err(ApplicationError::ExistingArtifact(path));
        }
        Ok(path)
    }

    fn resolve_relative(&self, relative: &str) -> Result<PathBuf, ApplicationError> {
        let relative_path = Path::new(relative);
        if relative.is_empty()
            || relative_path.is_absolute()
            || relative_path
                .components()
                .any(|component| !matches!(component, Component::Normal(_)))
        {
            return Err(ApplicationError::RootEscape(relative_path.to_path_buf()));
        }
        let path = self.root.join(relative_path);
        let mut cursor = self.root.clone();
        for component in relative_path.components() {
            let Component::Normal(component) = component else {
                return Err(ApplicationError::RootEscape(path));
            };
            cursor.push(component);
            if cursor.exists()
                && fs::symlink_metadata(&cursor)
                    .map_err(|error| io(&cursor, error))?
                    .file_type()
                    .is_symlink()
            {
                return Err(ApplicationError::RootEscape(cursor));
            }
        }
        Ok(path)
    }

    fn ensure_contained(&self, path: &Path) -> Result<(), ApplicationError> {
        let canonical = path.canonicalize().map_err(|error| io(path, error))?;
        if !canonical.starts_with(&self.root) {
            return Err(ApplicationError::RootEscape(path.to_path_buf()));
        }
        Ok(())
    }
}

fn io(path: &Path, error: std::io::Error) -> ApplicationError {
    ApplicationError::Io {
        path: path.to_path_buf(),
        reason: error.to_string(),
    }
}

#[cfg(test)]
mod tests {
    use serde::{Deserialize, Serialize};
    use tempfile::tempdir;

    use super::*;

    #[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
    struct Fixture {
        value: u64,
    }

    #[test]
    fn explicit_root_refuses_escape_and_overwrite_and_replaces_control_atomically() {
        let temporary = tempdir().expect("temporary");
        let store = ArtifactStore::create(temporary.path()).expect("store");
        store
            .write_json_new("artifacts/one.json", &Fixture { value: 1 })
            .expect("artifact");
        assert!(matches!(
            store.write_json_new("artifacts/one.json", &Fixture { value: 2 }),
            Err(ApplicationError::ExistingArtifact(_))
        ));
        assert!(matches!(
            store.write_new("../outside", b"refuse"),
            Err(ApplicationError::RootEscape(_))
        ));
        #[cfg(unix)]
        {
            let outside = tempdir().expect("outside");
            std::os::unix::fs::symlink(outside.path(), temporary.path().join("escape"))
                .expect("symlink");
            assert!(matches!(
                store.write_new("escape/outside", b"refuse"),
                Err(ApplicationError::RootEscape(_))
            ));
        }
        store
            .replace_json("control.json", &Fixture { value: 3 })
            .expect("first control");
        store
            .replace_json("control.json", &Fixture { value: 4 })
            .expect("second control");
        assert_eq!(
            store.read_json::<Fixture>("control.json").expect("control"),
            Fixture { value: 4 }
        );
    }
}

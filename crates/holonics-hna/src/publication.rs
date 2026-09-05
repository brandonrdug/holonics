//! Atomic, no-overwrite publication of exterior HNA artifacts.

use std::{
    fs::{self, File, OpenOptions},
    io::{self, Write},
    path::{Path, PathBuf},
};
use thiserror::Error;

#[derive(Debug, Error)]
pub enum PublicationError {
    #[error("publication target already exists: {path}")]
    ExistingTarget { path: PathBuf },
    #[error("publication failed before destination was created at {path}: {source}")]
    BeforePublication { path: PathBuf, source: io::Error },
    #[error("destination was published but durability is unconfirmed at {path}: {source}")]
    PublishedDurabilityUnconfirmed { path: PathBuf, source: io::Error },
}

impl PublicationError {
    pub fn path(&self) -> &Path {
        match self {
            Self::ExistingTarget { path }
            | Self::BeforePublication { path, .. }
            | Self::PublishedDurabilityUnconfirmed { path, .. } => path,
        }
    }
}

#[derive(Debug)]
pub struct PublicationReceipt<T> {
    pub path: PathBuf,
    pub bytes: u64,
    pub value: T,
}

struct TemporaryFileGuard {
    path: Option<PathBuf>,
}

impl Drop for TemporaryFileGuard {
    fn drop(&mut self) {
        if let Some(path) = self.path.take() {
            let _ = fs::remove_file(path);
        }
    }
}

/// Stream one newly-created artifact beside its destination, then publish it atomically without
/// replacing an existing target. The writer borrows the temporary file and cannot take ownership
/// of native model state. Once the hard-link publication succeeds, later failures are reported as
/// durability uncertainty because the destination now exists.
pub fn publish_new<T, W>(
    path: impl AsRef<Path>,
    writer: W,
) -> Result<PublicationReceipt<T>, PublicationError>
where
    W: FnOnce(&mut File) -> io::Result<T>,
{
    let path = path.as_ref().to_path_buf();
    let parent = parent_directory(&path).map_err(|source| PublicationError::BeforePublication {
        path: path.clone(),
        source,
    })?;
    let name = path
        .file_name()
        .ok_or_else(|| PublicationError::BeforePublication {
            path: path.clone(),
            source: io::Error::new(io::ErrorKind::InvalidInput, "publication has no filename"),
        })?
        .to_string_lossy();
    if path.exists() {
        return Err(PublicationError::ExistingTarget { path });
    }

    let mut ordinal = 0u64;
    let (temporary, mut file) = loop {
        let candidate = parent.join(format!(".{name}.hna-next-{}-{ordinal}", std::process::id()));
        match OpenOptions::new()
            .read(true)
            .write(true)
            .create_new(true)
            .open(&candidate)
        {
            Ok(file) => break (candidate, file),
            Err(error) if error.kind() == io::ErrorKind::AlreadyExists => {
                ordinal =
                    ordinal
                        .checked_add(1)
                        .ok_or_else(|| PublicationError::BeforePublication {
                            path: path.clone(),
                            source: io::Error::new(
                                io::ErrorKind::AlreadyExists,
                                "temporary ordinal overflow",
                            ),
                        })?;
            }
            Err(source) => {
                return Err(PublicationError::BeforePublication {
                    path: path.clone(),
                    source,
                })
            }
        }
    };
    let mut temporary_guard = TemporaryFileGuard {
        path: Some(temporary.clone()),
    };
    let result = writer(&mut file);
    let value = match result {
        Ok(value) => value,
        Err(source) => {
            return Err(PublicationError::BeforePublication { path, source });
        }
    };
    file.flush()
        .map_err(|source| PublicationError::BeforePublication {
            path: path.clone(),
            source,
        })?;
    file.sync_all()
        .map_err(|source| PublicationError::BeforePublication {
            path: path.clone(),
            source,
        })?;
    let bytes = file
        .metadata()
        .map(|metadata| metadata.len())
        .map_err(|source| PublicationError::BeforePublication {
            path: path.clone(),
            source,
        })?;
    drop(file);

    if let Err(source) = fs::hard_link(&temporary, &path) {
        if source.kind() == io::ErrorKind::AlreadyExists {
            return Err(PublicationError::ExistingTarget { path });
        }
        return Err(PublicationError::BeforePublication { path, source });
    }
    if let Err(source) = fs::remove_file(&temporary) {
        return Err(PublicationError::PublishedDurabilityUnconfirmed { path, source });
    }
    temporary_guard.path = None;
    if let Err(source) = sync_directory(&parent) {
        return Err(PublicationError::PublishedDurabilityUnconfirmed { path, source });
    }
    Ok(PublicationReceipt { path, bytes, value })
}

fn parent_directory(path: &Path) -> io::Result<PathBuf> {
    let parent = path.parent().ok_or_else(|| {
        io::Error::new(
            io::ErrorKind::InvalidInput,
            "publication has no parent directory",
        )
    })?;
    Ok(if parent.as_os_str().is_empty() {
        PathBuf::from(".")
    } else {
        parent.to_path_buf()
    })
}

#[cfg(test)]
thread_local! {
    static FAIL_DIRECTORY_SYNC: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

fn sync_directory(path: &Path) -> io::Result<()> {
    #[cfg(test)]
    FAIL_DIRECTORY_SYNC.with(|fault| {
        if fault.replace(false) {
            Err(io::Error::other("injected directory sync failure"))
        } else {
            Ok(())
        }
    })?;
    OpenOptions::new().read(true).open(path)?.sync_all()
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::{
        io::ErrorKind,
        panic::AssertUnwindSafe,
        sync::atomic::{AtomicBool, Ordering},
    };
    use tempfile::tempdir;

    #[test]
    fn successful_stream_is_atomic_and_receipted() {
        let dir = tempdir().unwrap();
        let path = dir.path().join("artifact.bin");
        let receipt = publish_new(&path, |file| {
            file.write_all(b"hello")?;
            Ok(7u8)
        })
        .unwrap();
        assert_eq!(receipt.path, path);
        assert_eq!(receipt.bytes, 5);
        assert_eq!(receipt.value, 7);
        assert_eq!(fs::read(&path).unwrap(), b"hello");
    }

    #[test]
    fn failing_or_partial_writer_leaves_destination_absent() {
        let dir = tempdir().unwrap();
        let path = dir.path().join("artifact.bin");
        let result = publish_new(&path, |file| {
            file.write_all(b"partial")?;
            Err::<(), _>(io::Error::other("fault"))
        });
        assert!(matches!(
            result,
            Err(PublicationError::BeforePublication { .. })
        ));
        assert!(!path.exists());
    }

    #[test]
    fn existing_target_is_refused_and_unchanged() {
        let dir = tempdir().unwrap();
        let path = dir.path().join("artifact.bin");
        fs::write(&path, b"old").unwrap();
        let result = publish_new(&path, |file| file.write_all(b"new"));
        assert!(matches!(
            result,
            Err(PublicationError::ExistingTarget { .. })
        ));
        assert_eq!(fs::read(&path).unwrap(), b"old");
    }

    #[test]
    fn destination_race_inside_writer_is_refused_and_contender_survives() {
        let dir = tempdir().unwrap();
        let path = dir.path().join("artifact.bin");
        let contender = path.clone();
        let result = publish_new(&path, move |file| {
            file.write_all(b"staged")?;
            fs::write(&contender, b"contender")?;
            Ok(())
        });
        assert!(matches!(
            result,
            Err(PublicationError::ExistingTarget { .. })
        ));
        assert_eq!(fs::read(&path).unwrap(), b"contender");
    }

    #[test]
    fn post_publication_directory_sync_failure_reports_uncertainty_and_keeps_bytes() {
        let dir = tempdir().unwrap();
        let path = dir.path().join("artifact.bin");
        FAIL_DIRECTORY_SYNC.with(|fault| fault.set(true));
        let result = publish_new(&path, |file| {
            file.write_all(b"published")?;
            Ok(())
        });
        assert!(matches!(
            result,
            Err(PublicationError::PublishedDurabilityUnconfirmed { .. })
        ));
        assert_eq!(fs::read(&path).unwrap(), b"published");
    }

    #[test]
    fn bare_relative_parent_normalizes_to_current_directory_without_chdir() {
        assert_eq!(
            parent_directory(Path::new("artifact.bin")).unwrap(),
            PathBuf::from(".")
        );
    }

    #[test]
    fn panic_in_writer_removes_staged_file_and_destination_stays_absent() {
        let dir = tempdir().unwrap();
        let path = dir.path().join("artifact.bin");
        let result = std::panic::catch_unwind(AssertUnwindSafe(|| {
            let _ = publish_new(&path, |file| {
                file.write_all(b"panic")?;
                panic!("injected writer panic");
                #[allow(unreachable_code)]
                Ok::<(), io::Error>(())
            });
        }));
        assert!(result.is_err());
        assert!(!path.exists());
        assert_eq!(fs::read_dir(dir.path()).unwrap().count(), 0);
    }

    #[test]
    fn writer_is_only_given_a_borrow_and_no_temp_is_left_on_failure() {
        let dir = tempdir().unwrap();
        let path = dir.path().join("artifact.bin");
        let called = AtomicBool::new(false);
        let result = publish_new(&path, |file| {
            called.store(true, Ordering::Relaxed);
            file.write_all(b"x")?;
            Err::<(), _>(io::Error::new(ErrorKind::Interrupted, "interrupted"))
        });
        assert!(called.load(Ordering::Relaxed));
        assert!(matches!(
            result,
            Err(PublicationError::BeforePublication { .. })
        ));
        assert!(!path.exists());
        assert_eq!(fs::read_dir(dir.path()).unwrap().count(), 0);
    }
}

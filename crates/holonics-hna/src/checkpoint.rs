//! Exterior HNA checkpoint envelope: a verified native rest plus its coefficient-base witness.

use std::{
    fs::File,
    io::{self, Read, Seek, SeekFrom, Write},
    path::{Path, PathBuf},
};

use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use thiserror::Error;

use holonic_engine::native_ecology::holonic_intelligence::{
    NativeFullSessionRest, NativeSessionRestError,
};

use crate::publication::{publish_new, PublicationError, PublicationReceipt};

const MAGIC: &[u8] = b"HNA-CHECKPOINT\x01";
const STREAM_MAGIC: &[u8] = b"HNA-CHECKPOINT\x02";
const MATERIAL_MAGIC: &[u8] = b"HNA-CHECKPOINT\x03";
const MATERIAL_STREAM_MAGIC: &[u8] = b"HNA-CHECKPOINT\x04";
const END: &[u8] = b"HNA-CHECKPOINT-END\x01";

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct HnaBaseDependency {
    pub path: PathBuf,
    pub octets: u64,
    pub sha256: String,
    pub class: Option<usize>,
    /// Explicit immutable input material in addition to the original restricted base.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub input_material: Vec<HnaInputMaterialDependency>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct HnaFileDependency {
    pub path: PathBuf,
    pub octets: u64,
    pub sha256: String,
}

/// Input material uses the same immutable wire reference as other exterior session artifacts.
pub type HnaInputMaterialDependency = HnaFileDependency;

impl HnaFileDependency {
    pub fn capture(path: impl AsRef<Path>) -> Result<Self, CheckpointError> {
        let pin = HnaBaseDependency::capture(path, None)?;
        Ok(Self {
            path: pin.path,
            octets: pin.octets,
            sha256: pin.sha256,
        })
    }
    pub fn open_verified(&self) -> Result<File, CheckpointError> {
        HnaBaseDependency {
            path: self.path.clone(),
            octets: self.octets,
            sha256: self.sha256.clone(),
            class: None,
            input_material: Vec::new(),
        }
        .open_verified(None)
    }
}

#[derive(Debug, Error)]
pub enum CheckpointError {
    #[error("checkpoint I/O: {0}")]
    Io(#[from] io::Error),
    #[error("checkpoint publication: {0}")]
    Publication(#[from] PublicationError),
    #[error("checkpoint base is missing: {path}")]
    MissingBase { path: PathBuf },
    #[error("checkpoint base is stale: {path}")]
    StaleBase { path: PathBuf },
    #[error("malformed checkpoint: {0}")]
    Malformed(String),
    #[error("checkpoint checksum mismatch")]
    Checksum,
    #[error("native session rest: {0}")]
    Rest(#[from] NativeSessionRestError),
    #[error("checkpoint JSON: {0}")]
    Json(#[from] serde_json::Error),
}

#[derive(Debug)]
pub struct HnaCheckpointReceipt {
    pub publication: PublicationReceipt<()>,
    pub dependency: HnaBaseDependency,
}

pub struct HnaSavedSession {
    pub dependency: HnaBaseDependency,
    pub state: NativeFullSessionRest,
    pub transport: Option<crate::HnaStreamState>,
}

#[derive(Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct TransportHeader {
    sequence: u64,
    input_complete: bool,
    output_accepted: usize,
    closed: bool,
    has_output: bool,
}

impl HnaBaseDependency {
    pub fn capture(path: impl AsRef<Path>, class: Option<usize>) -> Result<Self, CheckpointError> {
        Ok(Self::capture_with_open_handle(path, class)?.0)
    }

    /// Capture the immutable pin and return the same file handle, rewound to byte zero after its
    /// hash is complete. Fresh model construction consumes this handle directly, avoiding a
    /// second full hash; loading an existing dependency continues to use `open_verified` below.
    pub fn capture_with_open_handle(
        path: impl AsRef<Path>,
        class: Option<usize>,
    ) -> Result<(Self, File), CheckpointError> {
        let requested = path.as_ref();
        let path = requested.canonicalize().map_err(|error| {
            if error.kind() == io::ErrorKind::NotFound {
                CheckpointError::MissingBase {
                    path: requested.to_path_buf(),
                }
            } else {
                CheckpointError::Io(error)
            }
        })?;
        let mut file = File::open(&path).map_err(|error| {
            if error.kind() == io::ErrorKind::NotFound {
                CheckpointError::MissingBase { path: path.clone() }
            } else {
                CheckpointError::Io(error)
            }
        })?;
        let octets = file.metadata()?.len();
        let sha256 = hash_reader(&mut file)?;
        file.seek(SeekFrom::Start(0))?;
        Ok((
            Self {
                path,
                octets,
                sha256,
                class,
                input_material: Vec::new(),
            },
            file,
        ))
    }

    /// Opens the verified base once and rewinds that same handle for the consumer.
    pub fn open_verified(&self, override_path: Option<&Path>) -> Result<File, CheckpointError> {
        let path = override_path.unwrap_or(&self.path).to_path_buf();
        let mut file = File::open(&path).map_err(|error| {
            if error.kind() == io::ErrorKind::NotFound {
                CheckpointError::MissingBase { path: path.clone() }
            } else {
                CheckpointError::Io(error)
            }
        })?;
        if file.metadata()?.len() != self.octets || hash_reader(&mut file)? != self.sha256 {
            return Err(CheckpointError::StaleBase { path });
        }
        file.seek(SeekFrom::Start(0))?;
        Ok(file)
    }
}

pub fn save_checkpoint_new(
    path: impl AsRef<Path>,
    dependency: &HnaBaseDependency,
    state: &NativeFullSessionRest,
) -> Result<HnaCheckpointReceipt, CheckpointError> {
    save_checkpoint(path.as_ref(), dependency, state, None)
}

pub fn save_stream_checkpoint_new(
    path: impl AsRef<Path>,
    dependency: &HnaBaseDependency,
    state: &NativeFullSessionRest,
    transport: &crate::HnaStreamState,
) -> Result<HnaCheckpointReceipt, CheckpointError> {
    transport
        .validate()
        .map_err(|e| CheckpointError::Malformed(e.to_string()))?;
    save_checkpoint(path.as_ref(), dependency, state, Some(transport))
}

fn save_checkpoint(
    path: &Path,
    dependency: &HnaBaseDependency,
    state: &NativeFullSessionRest,
    transport: Option<&crate::HnaStreamState>,
) -> Result<HnaCheckpointReceipt, CheckpointError> {
    let metadata = serde_json::to_vec(dependency)?;
    state.validate()?;
    let publication = publish_new(path, |file| {
        file.write_all(
            match (dependency.input_material.is_empty(), transport.is_some()) {
                (true, false) => MAGIC,
                (true, true) => STREAM_MAGIC,
                (false, false) => MATERIAL_MAGIC,
                (false, true) => MATERIAL_STREAM_MAGIC,
            },
        )?;
        write_len(file, metadata.len())?;
        file.write_all(&metadata)?;
        if let Some(transport) = transport {
            let header = serde_json::to_vec(&TransportHeader {
                sequence: transport.sequence,
                input_complete: transport.input_complete,
                output_accepted: transport.output_accepted,
                closed: transport.closed,
                has_output: transport.output.is_some(),
            })
            .map_err(io::Error::other)?;
            for bytes in [
                header.as_slice(),
                transport.input.as_slice(),
                transport.output.as_deref().unwrap_or(&[]),
            ] {
                write_len(file, bytes.len())?;
                file.write_all(bytes)?;
            }
        }
        let extent_position = file.stream_position()?;
        file.write_all(&0u64.to_le_bytes())?;
        let start = file.stream_position()?;
        {
            let mut buffered = io::BufWriter::new(&mut *file);
            state.write_to(&mut buffered).map_err(io::Error::other)?;
            buffered.flush()?;
        }
        let end = file.stream_position()?;
        file.seek(SeekFrom::Start(extent_position))?;
        file.write_all(&(end - start).to_le_bytes())?;
        let digest = hash_prefix(file, end)?;
        file.seek(SeekFrom::Start(end))?;
        file.write_all(&digest)?;
        file.write_all(END)?;
        Ok(())
    })?;
    Ok(HnaCheckpointReceipt {
        publication,
        dependency: dependency.clone(),
    })
}

pub fn read_checkpoint(
    path: impl AsRef<Path>,
) -> Result<(HnaBaseDependency, NativeFullSessionRest), CheckpointError> {
    let saved = read_session_checkpoint(path)?;
    if saved.transport.is_some() {
        return Err(CheckpointError::Malformed(
            "checkpoint carries transport state; use read_session_checkpoint".into(),
        ));
    }
    Ok((saved.dependency, saved.state))
}

pub fn read_session_checkpoint(path: impl AsRef<Path>) -> Result<HnaSavedSession, CheckpointError> {
    read_session_checkpoint_file(File::open(path)?)
}

pub(crate) fn read_session_checkpoint_file(
    mut file: File,
) -> Result<HnaSavedSession, CheckpointError> {
    let length = file.metadata()?.len();
    if length < (MAGIC.len() + END.len() + 48) as u64 {
        return Err(CheckpointError::Malformed("magic or minimum frame".into()));
    }
    let footer_start = length - END.len() as u64 - 32;
    file.seek(SeekFrom::Start(footer_start))?;
    let mut expected = [0u8; 32];
    file.read_exact(&mut expected)?;
    let mut end = vec![0; END.len()];
    file.read_exact(&mut end)?;
    if end != END {
        return Err(CheckpointError::Malformed("end marker".into()));
    }
    if hash_prefix(&mut file, footer_start)? != expected {
        return Err(CheckpointError::Checksum);
    }
    file.seek(SeekFrom::Start(0))?;
    let mut magic = vec![0; MAGIC.len()];
    file.read_exact(&mut magic)?;
    if magic != MAGIC
        && magic != STREAM_MAGIC
        && magic != MATERIAL_MAGIC
        && magic != MATERIAL_STREAM_MAGIC
    {
        return Err(CheckpointError::Malformed("magic/version".into()));
    }
    let metadata = read_blob(&mut file, footer_start)?;
    let dependency: HnaBaseDependency = serde_json::from_slice(&metadata)?;
    if dependency.input_material.is_empty() != (magic == MAGIC || magic == STREAM_MAGIC) {
        return Err(CheckpointError::Malformed(
            "input material requires its distinct checkpoint version".into(),
        ));
    }
    let transport = if magic == STREAM_MAGIC || magic == MATERIAL_STREAM_MAGIC {
        let header: TransportHeader = serde_json::from_slice(&read_blob(&mut file, footer_start)?)?;
        let input = read_blob(&mut file, footer_start)?;
        let output = read_blob(&mut file, footer_start)?;
        if !header.has_output && !output.is_empty() {
            return Err(CheckpointError::Malformed(
                "unclaimed transport output".into(),
            ));
        }
        let transport = crate::HnaStreamState {
            sequence: header.sequence,
            input,
            input_complete: header.input_complete,
            output: header.has_output.then_some(output),
            output_accepted: header.output_accepted,
            closed: header.closed,
        };
        transport
            .validate()
            .map_err(|e| CheckpointError::Malformed(e.to_string()))?;
        Some(transport)
    } else {
        None
    };
    let mut extent = [0; 8];
    file.read_exact(&mut extent)?;
    let extent = u64::from_le_bytes(extent);
    let position = file.stream_position()?;
    if position.checked_add(extent) != Some(footer_start) {
        return Err(CheckpointError::Malformed("native state extent".into()));
    }
    let mut input = io::BufReader::new(file.take(extent));
    let state = NativeFullSessionRest::read_from(&mut input, extent)?;
    Ok(HnaSavedSession {
        dependency,
        state,
        transport,
    })
}

fn write_len(out: &mut impl Write, len: usize) -> io::Result<()> {
    out.write_all(
        &u64::try_from(len)
            .map_err(|_| io::Error::other("checkpoint extent"))?
            .to_le_bytes(),
    )
}

fn read_blob(input: &mut File, end: u64) -> Result<Vec<u8>, CheckpointError> {
    let mut length = [0; 8];
    input.read_exact(&mut length)?;
    let length = u64::from_le_bytes(length);
    if input
        .stream_position()?
        .checked_add(length)
        .is_none_or(|offset| offset > end)
    {
        return Err(CheckpointError::Malformed("metadata extent".into()));
    }
    let mut bytes = Vec::new();
    let copied = input.take(length).read_to_end(&mut bytes)?;
    if copied as u64 != length {
        return Err(CheckpointError::Malformed("truncated metadata".into()));
    }
    Ok(bytes)
}

fn hash_reader(file: &mut File) -> Result<String, CheckpointError> {
    file.seek(SeekFrom::Start(0))?;
    let mut digest = Sha256::new();
    let mut buffer = [0u8; 64 * 1024];
    loop {
        let count = file.read(&mut buffer)?;
        if count == 0 {
            break;
        }
        digest.update(&buffer[..count]);
    }
    Ok(format!("{:x}", digest.finalize()))
}

/// One integrity scheme for each serialized artifact, not a model-identity or theorem registry.
/// The source/artifact is required to remain immutable while its opened descriptor is consumed.
fn hash_prefix(file: &mut File, octets: u64) -> io::Result<[u8; 32]> {
    file.seek(SeekFrom::Start(0))?;
    let mut remaining = octets;
    let mut digest = Sha256::new();
    let mut bytes = [0; 64 * 1024];
    while remaining > 0 {
        let count = bytes
            .len()
            .min(usize::try_from(remaining).unwrap_or(usize::MAX));
        file.read_exact(&mut bytes[..count])?;
        digest.update(&bytes[..count]);
        remaining -= count as u64;
    }
    Ok(digest.finalize().into())
}

#[cfg(test)]
mod tests {
    use super::*;
    use tempfile::tempdir;

    #[test]
    fn base_pin_refuses_missing_or_changed_bytes_and_returns_the_verified_handle() {
        let directory = tempdir().unwrap();
        let path = directory.path().join("base.bin");
        std::fs::write(&path, b"abc").unwrap();
        let dependency = HnaBaseDependency::capture(&path, Some(2)).unwrap();
        assert!(dependency.path.is_absolute());
        let mut opened = dependency.open_verified(None).unwrap();
        let moved = directory.path().join("moved.bin");
        std::fs::rename(&path, &moved).unwrap();
        assert!(matches!(
            dependency.open_verified(None),
            Err(CheckpointError::MissingBase { .. })
        ));
        std::fs::write(&path, b"def").unwrap();
        assert!(matches!(
            dependency.open_verified(None),
            Err(CheckpointError::StaleBase { .. })
        ));
        let mut bytes = Vec::new();
        opened.read_to_end(&mut bytes).unwrap();
        assert_eq!(
            bytes, b"abc",
            "the consumer keeps the admitted descriptor, not a new path lookup"
        );
        assert!(dependency.open_verified(Some(&moved)).is_ok());
    }

    #[test]
    fn capture_with_open_handle_returns_the_pinned_file_at_zero() {
        let directory = tempdir().unwrap();
        let path = directory.path().join("base.bin");
        std::fs::write(&path, b"abc").unwrap();
        let (dependency, mut file) = HnaBaseDependency::capture_with_open_handle(&path, Some(7)).unwrap();
        assert_eq!(dependency.path, path.canonicalize().unwrap());
        assert_eq!(dependency.octets, 3);
        assert_eq!(dependency.sha256, "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad");
        assert_eq!(file.stream_position().unwrap(), 0);
        std::fs::rename(&path, directory.path().join("retained.bin")).unwrap();
        std::fs::write(&path, b"xyz").unwrap();
        let mut bytes = Vec::new();
        file.read_to_end(&mut bytes).unwrap();
        assert_eq!(bytes, b"abc");
        assert_eq!(file.stream_position().unwrap(), dependency.octets);
        assert!(dependency.open_verified(None).is_err(), "an existing pin must not trust the replacement path");
    }

    #[test]
    fn checksum_is_verified_before_native_state_decoding_and_truncation_refuses() {
        let directory = tempdir().unwrap();
        let path = directory.path().join("checkpoint.bin");
        let mut bytes = Vec::from(MAGIC);
        write_len(&mut bytes, 2).unwrap();
        bytes.extend_from_slice(b"{}");
        write_len(&mut bytes, 16).unwrap();
        bytes.extend_from_slice(&[255; 16]);
        bytes.extend_from_slice(&[0; 32]);
        bytes.extend_from_slice(END);
        std::fs::write(&path, &bytes).unwrap();
        assert!(
            matches!(read_checkpoint(&path), Err(CheckpointError::Checksum)),
            "malformed state must not be decoded first"
        );
        for length in 0..bytes.len() {
            std::fs::write(&path, &bytes[..length]).unwrap();
            assert!(read_checkpoint(&path).is_err());
        }
    }
}

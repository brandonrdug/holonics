use std::io::{Read, Write};
use std::path::{Path, PathBuf};

use sha2::{Digest, Sha256};

use super::manifest::{
    NativePayloadDescriptor, NativePopulationDescriptor, NativeRestWire, mount_external_evidence,
    validate_manifest_digest, validate_manifest_shape,
};
use super::types::*;
use super::{MANIFEST_DIGEST_OCTETS, NATIVE_REST_PREFIX};

/// File-backed remount. Only the manifest is retained; exact population bytes remain in the
/// sealed native rest file and are streamed when a named population is requested.
pub struct MountedNativeRest {
    path: PathBuf,
    wire: NativeRestWire,
    payload_offset: u64,
}

impl std::fmt::Debug for MountedNativeRest {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("MountedNativeRest")
            .field("path", &self.path)
            .field("payload_offset", &self.payload_offset)
            .finish()
    }
}

impl MountedNativeRest {
    pub fn open(path: impl AsRef<Path>) -> Result<Self, NativeRestRefusal> {
        use std::io::Seek;
        let path = path.as_ref().to_owned();
        let mut file =
            std::fs::File::open(&path).map_err(|e| NativeRestRefusal::WireDecode(e.to_string()))?;
        let mut prefix = vec![0u8; NATIVE_REST_PREFIX.len()];
        file.read_exact(&mut prefix)
            .map_err(|e| NativeRestRefusal::WireDecode(e.to_string()))?;
        if prefix != NATIVE_REST_PREFIX {
            return Err(NativeRestRefusal::WirePrefix { opened: prefix });
        }
        let mut len = [0u8; 8];
        file.read_exact(&mut len)
            .map_err(|e| NativeRestRefusal::WireDecode(e.to_string()))?;
        let manifest_len = usize::try_from(u64::from_le_bytes(len)).map_err(|_| {
            NativeRestRefusal::WireDecode("manifest extent exceeds process".to_owned())
        })?;
        let mut expected_digest = [0u8; MANIFEST_DIGEST_OCTETS];
        file.read_exact(&mut expected_digest)
            .map_err(|e| NativeRestRefusal::WireDecode(e.to_string()))?;
        let mut manifest = vec![0u8; manifest_len];
        file.read_exact(&mut manifest)
            .map_err(|e| NativeRestRefusal::WireDecode(e.to_string()))?;
        validate_manifest_digest(&expected_digest, &manifest)?;
        let wire: NativeRestWire = serde_json::from_slice(&manifest)
            .map_err(|e| NativeRestRefusal::WireDecode(e.to_string()))?;
        let wire = mount_external_evidence(wire)?;
        let payload_offset =
            (NATIVE_REST_PREFIX.len() + 8 + MANIFEST_DIGEST_OCTETS + manifest_len) as u64;
        let file_len = file
            .metadata()
            .map_err(|e| NativeRestRefusal::WireDecode(e.to_string()))?
            .len();
        let payload_len = file_len.saturating_sub(payload_offset);
        validate_manifest_shape(&wire, payload_len)?;
        file.seek(std::io::SeekFrom::Start(payload_offset))
            .map_err(|e| NativeRestRefusal::WireDecode(e.to_string()))?;
        let actual = digest_stream(&mut file, payload_len)?;
        if actual != wire.payload_sha256 {
            return Err(NativeRestRefusal::PayloadDigest {
                expected: wire.payload_sha256.clone(),
                actual,
            });
        }
        Ok(Self {
            path,
            wire,
            payload_offset,
        })
    }

    pub fn topology(&self) -> &NativeTopology {
        &self.wire.topology[0]
    }
    pub fn topologies(&self) -> &[NativeTopology] {
        &self.wire.topology
    }

    pub fn source(&self) -> &NativeSourceIdentity {
        &self.wire.source
    }

    pub fn populations(&self) -> &[NativePopulationDescriptor] {
        &self.wire.populations
    }

    pub fn laws(&self) -> &[NativeLawIdentity] {
        &self.wire.laws
    }

    /// Resolve a concrete graph through the correspondence registry; the mounted rest does not
    /// duplicate graph chronology/topology outside that registry.
    pub fn graph(&self, key: &str) -> Option<&NativeGraphIdentity> {
        self.wire
            .correspondence
            .graphs
            .iter()
            .find(|graph| graph.key == key)
    }

    pub fn graphs(&self) -> &[NativeGraphIdentity] {
        &self.wire.correspondence.graphs
    }

    pub fn tilings(&self) -> &[NativeOwnerIdentity] {
        &self.wire.tilings
    }

    pub fn reductions(&self) -> &[NativeOwnerIdentity] {
        &self.wire.reductions
    }
    pub fn correspondence(&self) -> &crate::operation_correspondence::OperationCorrespondenceSeal {
        &self.wire.correspondence
    }
    pub fn codebook(&self) -> &crate::foreign_codec_rest::ExteriorCodebookRest {
        &self.wire.codebook
    }

    /// Stream one exact population to a receiver. Open fibres return no bytes and are reported by
    /// the caller through the descriptor; this method never allocates the whole payload.
    pub fn read_population_to<W: Write>(
        &self,
        population: &str,
        output: &mut W,
    ) -> Result<(), NativeRestRefusal> {
        let descriptor = self
            .wire
            .populations
            .iter()
            .find(|p| p.source.population == population)
            .ok_or_else(|| NativeRestRefusal::ActivePopulationMissing {
                population: population.to_owned(),
            })?;
        let NativePayloadDescriptor::Exact { start, end } = &descriptor.payload else {
            return Ok(());
        };
        let (start, end) = (*start, *end);
        let mut file = std::fs::File::open(&self.path)
            .map_err(|e| NativeRestRefusal::WireDecode(e.to_string()))?;
        use std::io::Seek;
        file.seek(std::io::SeekFrom::Start(self.payload_offset + start))
            .map_err(|e| NativeRestRefusal::WireDecode(e.to_string()))?;
        let mut remaining = (end - start) as usize;
        let mut chunk = vec![0u8; 1 << 20];
        while remaining > 0 {
            let take = remaining.min(chunk.len());
            file.read_exact(&mut chunk[..take])
                .map_err(|e| NativeRestRefusal::WireDecode(e.to_string()))?;
            output
                .write_all(&chunk[..take])
                .map_err(|e| NativeRestRefusal::WireDecode(e.to_string()))?;
            remaining -= take;
        }
        Ok(())
    }
}

fn digest_stream(
    file: &mut std::fs::File,
    mut remaining: u64,
) -> Result<String, NativeRestRefusal> {
    let mut hasher = Sha256::new();
    let mut chunk = vec![0u8; 1 << 20];
    while remaining > 0 {
        let take = remaining.min(chunk.len() as u64) as usize;
        file.read_exact(&mut chunk[..take])
            .map_err(|e| NativeRestRefusal::WireDecode(e.to_string()))?;
        hasher.update(&chunk[..take]);
        remaining -= take as u64;
    }
    Ok(format!("{:x}", hasher.finalize()))
}

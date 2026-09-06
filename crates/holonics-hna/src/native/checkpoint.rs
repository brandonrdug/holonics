//! Dependency-free native-phase artifact, with the existing no-overwrite publication and
//! transport codec. One wire digest protects corruption, not semantic identity or provenance.
use super::*;
use crate::checkpoint::{hash_prefix, read_transport, write_transport};
use crate::publication::{publish_new, PublicationReceipt};
use crate::{HnaStream, HnaStreamState};
use holonic_engine::native_ecology::constitutive_fibre::NativeEcologyRest;
use std::{
    fs::File,
    io::{self, Read, Seek, SeekFrom, Write},
    path::Path,
};

const MAGIC: &[u8] = b"HNA-NATIVE-CHECKPOINT\x01";
const END: &[u8] = b"HNA-NATIVE-CHECKPOINT-END\x01";
fn malformed(detail: impl std::fmt::Display) -> NativeSessionError {
    NativeSessionError::Application(format!("native checkpoint: {detail}"))
}

/// Complete cold native state plus delivery state. No Clone or borrowed repeat-mount interface.
pub struct NativeSavedSession {
    ecology: NativeEcologyRest,
    transport: HnaStreamState,
}
impl NativeSavedSession {
    pub fn occurrences(&self) -> usize {
        self.ecology.occurrences()
    }
    pub fn source_slots(&self) -> &[Option<usize>] {
        self.ecology.source_slots()
    }
    pub fn transport(&self) -> &HnaStreamState {
        &self.transport
    }
    /// Like the standing checkpoint codec, this consumes one opened descriptor; its artifact
    /// must remain immutable while the integrity pass and bounded decoding complete.
    pub fn read(path: impl AsRef<Path>) -> Result<Self, NativeSessionError> {
        let mut file = File::open(path)?;
        let length = file.metadata()?.len();
        if length < (MAGIC.len() + END.len() + 32 + 8) as u64 {
            return Err(malformed("minimum frame"));
        }
        let footer = length - END.len() as u64 - 32;
        file.seek(SeekFrom::Start(footer))?;
        let mut expected = [0; 32];
        file.read_exact(&mut expected)?;
        let mut end = vec![0; END.len()];
        file.read_exact(&mut end)?;
        if end != END {
            return Err(malformed("end marker"));
        }
        if hash_prefix(&mut file, footer)? != expected {
            return Err(malformed("checksum mismatch"));
        }
        file.seek(SeekFrom::Start(0))?;
        let mut magic = vec![0; MAGIC.len()];
        file.read_exact(&mut magic)?;
        if magic != MAGIC {
            return Err(malformed("model kind/version"));
        }
        let transport = read_transport(&mut file, footer).map_err(malformed)?;
        let mut extent = [0; 8];
        file.read_exact(&mut extent)?;
        let extent = u64::from_le_bytes(extent);
        if file.stream_position()?.checked_add(extent) != Some(footer) {
            return Err(malformed("native extent"));
        }
        let ecology = NativeEcologyRest::read(&mut io::BufReader::new(file.take(extent)), extent)?;
        Ok(Self { ecology, transport })
    }
    /// Consume the saved representation into one live native owner and its matching delivery
    /// state. Connection replay is explicit via HnaStream::open_new_connection, not implicit here.
    pub fn with_session<R>(
        self,
        operation: impl FnOnce(&mut NativeSession<'_>, &mut HnaStream) -> Result<R, NativeSessionError>,
    ) -> Result<R, NativeSessionError> {
        let mut stream = HnaStream::from_state(self.transport).map_err(malformed)?;
        let readout = ResidentReadout::new().map_err(malformed)?;
        let surface = ResidentSurface::on(&readout).map_err(malformed)?;
        let confirmed_rank = self.ecology.rank();
        let (body, sources) = NativeConstitutiveEcology::remount(&surface, self.ecology)?;
        let mut session = NativeSession {
            body,
            sources,
            confirmed_rank,
        };
        let returned = operation(&mut session, &mut stream);
        drop(session);
        returned
    }
}

impl NativeSession<'_> {
    /// Save native state with a fresh exterior delivery chart. Existing streams must use
    /// checkpoint_stream, otherwise their pending output/input would be lost.
    pub fn checkpoint(
        &self,
        path: impl AsRef<Path>,
    ) -> Result<PublicationReceipt<()>, NativeSessionError> {
        self.checkpoint_stream(path, &HnaStreamState::default())
    }
    pub fn checkpoint_stream(
        &self,
        path: impl AsRef<Path>,
        transport: &HnaStreamState,
    ) -> Result<PublicationReceipt<()>, NativeSessionError> {
        transport.validate().map_err(malformed)?;
        if path.as_ref().exists() {
            return Err(crate::publication::PublicationError::ExistingTarget {
                path: path.as_ref().to_path_buf(),
            }
            .into());
        }
        let state = self
            .body
            .rest(&self.sources.iter().map(Option::as_ref).collect::<Vec<_>>())?;
        let receipt = publish_new(path, |file| {
            file.write_all(MAGIC)?;
            write_transport(file, transport)?;
            let extent_at = file.stream_position()?;
            file.write_all(&0u64.to_le_bytes())?;
            let start = file.stream_position()?;
            {
                let mut buffered = io::BufWriter::new(&mut *file);
                state.write(&mut buffered).map_err(io::Error::other)?;
                buffered.flush()?;
            }
            let end = file.stream_position()?;
            file.seek(SeekFrom::Start(extent_at))?;
            file.write_all(&(end - start).to_le_bytes())?;
            let digest = hash_prefix(file, end)?;
            file.seek(SeekFrom::Start(end))?;
            file.write_all(&digest)?;
            file.write_all(END)?;
            Ok(())
        })?;
        Ok(receipt)
    }
}

#[cfg(test)]
mod tests;

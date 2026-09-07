//! Durable native field, actual text capabilities and exterior application/delivery state.
//! A wire digest protects corruption; it does not define semantic identity.
use super::{
    material::AlphaMaterialError,
    text_codec::TextSymbol,
    text_session::{TextFieldSession, TextFieldSource},
};
use crate::checkpoint::{hash_prefix, read_blob, read_transport, write_len, write_transport};
use crate::publication::PublicationReceipt;
use crate::{publish_new, HnaStream, HnaStreamState};
use holonic_engine::{
    embedding_fiber::ResidentReadout,
    native_ecology::constitutive_fibre::{
        NativeConstitutiveField, NativeFieldOccurrence, NativeFieldRest, NativeFieldSourceAnchor,
    },
    resident_section::ResidentSurface,
};
use serde::{Deserialize, Serialize};
use std::{
    fs::File,
    io::{self, Read, Seek, SeekFrom, Write},
    path::Path,
};

const MAGIC: &[u8] = b"HNA-NATIVE-TEXT-FIELD\x01";
const END: &[u8] = b"HNA-NATIVE-TEXT-FIELD-END\x01";
fn error(value: impl std::fmt::Display) -> AlphaMaterialError {
    AlphaMaterialError::Apparatus(format!("text field checkpoint: {value}"))
}

#[derive(Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct SessionWire {
    schema: String,
    pending: Option<TextSymbol>,
    external_anchors: usize,
}

pub struct SavedTextField {
    field: NativeFieldRest,
    session: SessionWire,
    stream: HnaStreamState,
    application: Vec<u8>,
}
impl SavedTextField {
    pub fn occurrences(&self) -> usize {
        self.field.occurrences()
    }
    pub fn nodes(&self) -> usize {
        self.field.nodes()
    }
    pub fn application_state(&self) -> &[u8] {
        &self.application
    }
    pub fn external_anchor_occurrences(&self) -> &[Option<usize>] {
        &self.field.anchor_slots()[2..]
    }
    pub fn fractional_bits(&self) -> Result<u32, AlphaMaterialError> {
        match self.field.junction_representation() {
            Some(holonic_engine::native_ecology::constitutive_fibre::NativeFieldJunctionRepresentation::EnclosedDyadic{fractional_bits})=>Ok(fractional_bits),
            _=>Err(error("text checkpoint is not an enclosed field")),
        }
    }
    fn validate(&self) -> Result<(), AlphaMaterialError> {
        self.field.validate()?;
        self.stream.validate().map_err(error)?;
        let sources = self.field.source_slots();
        let anchors = self.field.anchor_slots();
        if self.field.nodes() != super::text_codec::TEXT_INPUT_CHANNELS
            || self.field.junction_representation().is_none()
            || self.session.schema != "holonics.native-text-session.v1"
            || sources.len() != 2
            || anchors.len()
                != self
                    .session
                    .external_anchors
                    .checked_add(2)
                    .ok_or_else(|| error("anchor extent"))?
            || anchors[2..].iter().any(Option::is_none)
            || (sources[0].is_some() && anchors[0].is_some())
            || (sources[1].is_some() && anchors[1].is_some())
            || (self.session.pending.is_none() && (sources[1].is_some() || anchors[1].is_some()))
            || (self.session.pending.is_some() && (sources[0].is_some() || anchors[0].is_some()))
        {
            return Err(error("session/capability correspondence"));
        }
        Ok(())
    }
    pub fn read(path: impl AsRef<Path>) -> Result<Self, AlphaMaterialError> {
        let mut file = File::open(path).map_err(error)?;
        let length = file.metadata().map_err(error)?.len();
        if length < (MAGIC.len() + END.len() + 32 + 8) as u64 {
            return Err(error("minimum frame"));
        }
        let footer = length - END.len() as u64 - 32;
        file.seek(SeekFrom::Start(footer)).map_err(error)?;
        let mut digest = [0; 32];
        file.read_exact(&mut digest).map_err(error)?;
        let mut end = vec![0; END.len()];
        file.read_exact(&mut end).map_err(error)?;
        if end != END || hash_prefix(&mut file, footer).map_err(error)? != digest {
            return Err(error("end marker or wire checksum"));
        }
        file.seek(SeekFrom::Start(0)).map_err(error)?;
        let mut magic = vec![0; MAGIC.len()];
        file.read_exact(&mut magic).map_err(error)?;
        if magic != MAGIC {
            return Err(error("native model kind/version"));
        }
        let stream = read_transport(&mut file, footer).map_err(error)?;
        let session =
            serde_json::from_slice(&read_blob(&mut file, footer).map_err(error)?).map_err(error)?;
        let application = read_blob(&mut file, footer).map_err(error)?;
        let mut extent = [0; 8];
        file.read_exact(&mut extent).map_err(error)?;
        let extent = u64::from_le_bytes(extent);
        if file.stream_position().map_err(error)?.checked_add(extent) != Some(footer) {
            return Err(error("native field extent"));
        }
        let field = NativeFieldRest::read(&mut io::BufReader::new(file.take(extent)), extent)?;
        let saved = Self {
            field,
            session,
            stream,
            application,
        };
        saved.validate()?;
        Ok(saved)
    }
    /// Consume the saved chart into one owner. Source material is not consulted, and no native
    /// occurrence or coefficient update is replayed. The caller receives its application bytes
    /// and all explicitly retained exterior anchors alongside the restored delivery state.
    pub fn with_session<R>(
        self,
        operation: impl FnOnce(
            &mut TextFieldSession<'_, '_>,
            &mut HnaStream,
            Vec<NativeFieldSourceAnchor>,
            Vec<u8>,
        ) -> Result<R, AlphaMaterialError>,
    ) -> Result<R, AlphaMaterialError> {
        self.validate()?;
        let latest = self.field.source_slots()[0];
        let readout = ResidentReadout::new().map_err(error)?;
        let surface = ResidentSurface::on(&readout).map_err(error)?;
        let (mut field, mut sources, mut anchors) =
            NativeConstitutiveField::remount(&surface, self.field)?;
        let mut session = TextFieldSession::on(&mut field)?;
        session.latest = latest.map(|occurrence| TextFieldSource {
            occurrence,
            source: sources[0].take().expect("validated latest source"),
        });
        session.next_anchor = anchors[0].take();
        if let Some(symbol) = self.session.pending {
            let occurrence = if let Some(source) = sources[1].take() {
                NativeFieldOccurrence::through(source, symbol.inputs())
            } else if let Some(anchor) = anchors[1].take() {
                NativeFieldOccurrence::through_anchor(&anchor, symbol.inputs())
            } else {
                NativeFieldOccurrence::entering(symbol.inputs())
            };
            session.pending = Some((symbol, occurrence));
        }
        let external = anchors
            .into_iter()
            .skip(2)
            .map(|a| a.expect("validated exterior anchor"))
            .collect();
        let mut stream = HnaStream::from_state(self.stream).map_err(error)?;
        operation(&mut session, &mut stream, external, self.application)
    }
}

impl TextFieldSession<'_, '_> {
    /// Batch consumers with no live delivery channel may use the empty stream state. A consumer
    /// that owns a live HnaStream must use checkpoint_stream with its actual state.
    pub fn checkpoint(
        &self,
        path: impl AsRef<Path>,
        anchors: &[&NativeFieldSourceAnchor],
        application: &[u8],
    ) -> Result<PublicationReceipt<()>, AlphaMaterialError> {
        self.checkpoint_stream(path, &HnaStreamState::default(), anchors, application)
    }
    pub fn checkpoint_stream(
        &self,
        path: impl AsRef<Path>,
        stream: &HnaStreamState,
        anchors: &[&NativeFieldSourceAnchor],
        application: &[u8],
    ) -> Result<PublicationReceipt<()>, AlphaMaterialError> {
        stream.validate().map_err(error)?;
        if path.as_ref().exists() {
            return Err(error("checkpoint target already exists"));
        }
        let sources = [
            self.latest.as_ref().map(|s| &s.source),
            self.pending.as_ref().and_then(|(_, p)| p.source_ref()),
        ];
        let mut kept = vec![
            self.next_anchor.as_ref(),
            self.pending.as_ref().and_then(|(_, p)| p.anchor_ref()),
        ];
        kept.extend(anchors.iter().map(|a| Some(*a)));
        let field = self.field.rest(&sources, &kept)?;
        let session = SessionWire {
            schema: "holonics.native-text-session.v1".into(),
            pending: self.pending_symbol(),
            external_anchors: anchors.len(),
        };
        let session = serde_json::to_vec(&session).map_err(error)?;
        publish_new(path, |file| {
            #[cfg(unix)]
            {
                use std::os::unix::fs::PermissionsExt;
                file.set_permissions(std::fs::Permissions::from_mode(0o600))?;
            }
            file.write_all(MAGIC)?;
            write_transport(file, stream)?;
            write_len(file, session.len())?;
            file.write_all(&session)?;
            write_len(file, application.len())?;
            file.write_all(application)?;
            let extent_at = file.stream_position()?;
            file.write_all(&0u64.to_le_bytes())?;
            let start = file.stream_position()?;
            {
                let mut out = io::BufWriter::new(&mut *file);
                field.write(&mut out).map_err(io::Error::other)?;
                out.flush()?;
            }
            let end = file.stream_position()?;
            file.seek(SeekFrom::Start(extent_at))?;
            file.write_all(&(end - start).to_le_bytes())?;
            let digest = hash_prefix(file, end)?;
            file.seek(SeekFrom::Start(end))?;
            file.write_all(&digest)?;
            file.write_all(END)?;
            Ok(())
        })
        .map_err(error)
    }
}

#[cfg(test)]
mod tests;

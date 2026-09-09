//! Durable native field, actual text capabilities and exterior application/delivery state.
//! A wire digest protects corruption; it does not define semantic identity.
use super::{
    material::AlphaMaterialError,
    text_codec::TextSymbol,
    text_session::{TextFieldSession, TextFieldSource},
};
use crate::checkpoint::{hash_prefix, read_blob, read_transport, write_len, write_transport};
use crate::publication::PublicationReceipt;
use crate::{HnaStream, HnaStreamState, publish_new};
use holonic_engine::{
    embedding_fiber::ResidentReadout,
    native_ecology::constitutive_fibre::{
        ConstitutiveReturnRest, NativeConstitutiveField, NativeFieldOccurrence, NativeFieldRest,
        NativeFieldSourceAnchor,
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

#[derive(Debug,Serialize,Deserialize)]
#[serde(deny_unknown_fields)]
struct PendingMaterialActuation {
    quadrature:holonic_engine::native_ecology::constitutive_fibre::NativePacketQuadrature,
    coordinate:usize,
    #[serde(default,skip_serializing_if="Option::is_none")]
    incoming:Option<Vec<holonic_engine::native_ecology::constitutive_fibre::NativePhaseCurrent>>,
}

#[derive(Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct SessionWire {
    #[serde(default,skip_serializing_if="Option::is_none")]
    pending_material_actuation:Option<PendingMaterialActuation>,
    #[serde(default,skip_serializing_if="std::ops::Not::not")]
    duplex:bool,
    #[serde(default,skip_serializing_if="super::text_codec::TextDirection::is_incoming")]
    pending_direction:super::text_codec::TextDirection,
    schema: String,
    pending: Option<TextSymbol>,
    external_anchors: usize,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pending_native: Option<ConstitutiveReturnRest>,
}

pub struct SavedTextField {
    field: NativeFieldRest,
    session: SessionWire,
    stream: HnaStreamState,
    application: Vec<u8>,
}
impl SavedTextField {
    pub fn duplex(&self)->bool{self.session.duplex}
    pub fn material_target(&self)->Option<holonic_engine::native_ecology::constitutive_fibre::NativeMaterialTarget>{
        self.field.material_target()
    }
    pub fn occurrences(&self) -> usize {
        self.field.occurrences()
    }
    pub fn nodes(&self) -> usize {
        self.field.nodes()
    }
    pub fn material_transport_source(
        &self,
    ) -> Option<holonic_engine::native_ecology::constitutive_fibre::NativeMaterialTransportSource>
    {
        self.field.material_transport_source()
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
        if matches!(self.field.material_target(),Some(holonic_engine::native_ecology::constitutive_fibre::NativeMaterialTarget::TensorProduct{factor_width}) if factor_width!=2){
            return Err(error("text checkpoint has an incompatible packet target"));
        }
        if self.session.duplex && (self.field.material_target()!=Some(holonic_engine::native_ecology::constitutive_fibre::NativeMaterialTarget::TensorProduct{factor_width:2}) || self.session.pending_native.is_some()){
            return Err(error("duplex checkpoint requires its joint packet chart"));
        }
        if self.session.pending.is_none() && !self.session.pending_direction.is_incoming(){return Err(error("direction without a pending occurrence"));}
        self.stream.validate().map_err(error)?;
        let sources = self.field.source_slots();
        let anchors = self.field.anchor_slots();
        if let Some(native) = &self.session.pending_native {
            if self.session.pending.is_none() {
                return Err(error("pending native current lacks its exterior symbol"));
            }
            native.validate()?;
            let (words, _) = native
                .unique_current_words()
                .ok_or_else(|| error("pending native return is not a point"))?;
            if words.len() != 2 * super::text_codec::TEXT_INPUT_CHANNELS {
                return Err(error("pending native receiving chart"));
            }
            let mut code = 0u16;
            for bit in 0..super::text_codec::TEXT_BIT_PAIRS {
                match words[4 * bit + 2].cmp(&words[4 * bit]) {
                    std::cmp::Ordering::Greater => code |= 1 << bit,
                    std::cmp::Ordering::Less => {}
                    std::cmp::Ordering::Equal => {
                        return Err(error("pending native codeword is unresolved"));
                    }
                }
            }
            if super::text_codec::TextSymbol::from_codeword(code) != self.session.pending {
                return Err(error(
                    "pending native codeword does not match its exterior symbol",
                ));
            }
        }
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
        if let Some(actuation)=&self.session.pending_material_actuation {
            if self.session.pending_native.is_some() || self.session.pending.map(|s|s.codeword() as usize)!=Some(actuation.coordinate)
                || sources[1].is_none() || anchors[1].is_some()
                || actuation.quadrature!=(if self.session.duplex{self.session.pending_direction}else{super::text_codec::TextDirection::Incoming}).quadrature(){
                return Err(error("incompatible pending material actuation"));
            }
            if let Some(input)=&actuation.incoming {
                if input.len()!=self.nodes(){return Err(error("pending actuation input extent"));}
                let amplitude=self.material_target().ok_or_else(||error("missing actuation target"))?
                    .tensor_basis_amplitude(actuation.coordinate,input)?;
                let coordinate=if actuation.quadrature==holonic_engine::native_ecology::constitutive_fibre::NativePacketQuadrature::Real {
                    amplitude.real
                }else{amplitude.imaginary};
                if coordinate<=num_rational::BigRational::from_integer(0.into()) {return Err(error("pending actuation phase"));}
            }
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
        self.with_session_placed(None, operation)
    }
    /// Restore the same session with older numerical carriers in a fresh history archive.
    /// The portable checkpoint includes their payload; no earlier archive path is required.
    pub fn with_session_archived<R>(
        self,
        archive_path: impl AsRef<Path>,
        operation: impl FnOnce(
            &mut TextFieldSession<'_, '_>,
            &mut HnaStream,
            Vec<NativeFieldSourceAnchor>,
            Vec<u8>,
        ) -> Result<R, AlphaMaterialError>,
    ) -> Result<R, AlphaMaterialError> {
        self.with_session_placed(Some(archive_path.as_ref()), operation)
    }
    fn with_session_placed<R>(
        self,
        archive_path: Option<&Path>,
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
        let (mut field, mut sources, mut anchors) = match archive_path {
            Some(path) => {
                NativeConstitutiveField::remount_with_history_archive(&surface, self.field, path)?
            }
            None => NativeConstitutiveField::remount(&surface, self.field)?,
        };
        let mut session = TextFieldSession::on(&mut field)?;
        session.duplex=self.session.duplex;
        session.pending_direction=self.session.pending_direction;
        session.latest = latest.map(|occurrence| TextFieldSource {
            occurrence,
            source: sources[0].take().expect("validated latest source"),
        });
        session.next_anchor = anchors[0].take();
        if let Some(symbol) = self.session.pending {
            let inputs = if let Some(input)=self.session.pending_material_actuation.as_ref().and_then(|a|a.incoming.as_ref()) {
                input.clone()
            } else if self.session.pending_native.is_some() {
                vec![]
            } else {
                symbol.inputs_on(if self.session.duplex{self.session.pending_direction}else{super::text_codec::TextDirection::Incoming})
            };
            let occurrence = if let Some(source) = sources[1].take() {
                if let Some(expected)=&self.session.pending_material_actuation {
                    let actuation=session.field().read_material_actuation(&source,expected.quadrature)?;
                    if actuation.reading().selected!=Some(expected.coordinate){return Err(error("pending actuation source face changed"));}
                    NativeFieldOccurrence::actuating(source,inputs,actuation)
                }else{NativeFieldOccurrence::through(source,inputs)}
            } else if let Some(anchor) = anchors[1].take() {
                NativeFieldOccurrence::through_anchor(&anchor, inputs)
            } else {
                NativeFieldOccurrence::entering(inputs)
            };
            session.pending = Some((symbol, occurrence));
            session.pending_native = self
                .session
                .pending_native
                .map(|v| v.remount(&surface))
                .transpose()?;
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
        let pending_material_actuation=self.pending.as_ref().and_then(|(symbol,p)|p.material_actuation().map(|a|(symbol,p,a))).map(|(symbol,p,a)|{
            Ok::<_,AlphaMaterialError>(PendingMaterialActuation{quadrature:a.reading().quadrature,
                coordinate:a.reading().selected.ok_or_else(||error("pending material face is not fixed"))?,
                incoming:(p.incoming()!=symbol.inputs_on(self.pending_direction).as_slice()).then(||p.incoming().to_vec())})
        }).transpose()?;
        let session = SessionWire {
            pending_material_actuation,
            duplex:self.duplex,
            pending_direction:self.pending_direction,
            schema: "holonics.native-text-session.v1".into(),
            pending: self.pending_symbol(),
            external_anchors: anchors.len(),
            pending_native: self.pending_native.as_ref().map(|v| v.rest()).transpose()?,
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

//! Exterior source, emission and delivery state over one move-owned applied normal wave.
//! Native current/learning/selection stay in their engine owners; the shared HnaStream owns I/O.
use super::{NativeSessionError, section_input::SymbolCurrentChart};
use crate::{HnaStream, HnaStreamState, PublicationReceipt, publish_new};
use holonic_engine::{
    codec_recovery::{Symbol, SymbolAlphabet},
    embedding_fiber::ResidentReadout,
    native_ecology::constitutive_fibre::{
        NormalBasisSelection, NormalWaveBasisChart, NormalWaveRest, NormalWaveTransport,
        ResidentConstitutiveSection, ResidentNormalWave,
    },
    resident_section::ResidentSurface,
};
use serde::{Deserialize, Serialize};
use serde_json::{Value, json};
use std::{
    fs::File,
    io::{self, Read, Write},
    path::Path,
};
const MAGIC: &[u8] = b"HNA-APPLIED-WAVE-SESSION\x01";
fn invalid(message: impl ToString) -> NativeSessionError {
    NativeSessionError::Application(message.to_string())
}

#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
struct EmittedSource {
    ordinal: u64,
    generation: u64,
    symbol: Symbol,
    prediction: Option<u64>,
}
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
enum Cursor {
    Ready,
    AwaitSelection {
        generation: u64,
        observations: u64,
        prediction: Option<u64>,
    },
    AwaitReentry {
        generation: u64,
        observations: u64,
        action: EmittedSource,
    },
}
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Header {
    alphabet: SymbolAlphabet,
    coordinates: Vec<usize>,
    cursor: Cursor,
    emission_ordinal: u64,
    last: Option<EmittedSource>,
    transport: HnaStreamState,
}

pub struct NativeWaveAttachRefusal<'c> {
    pub wave: ResidentNormalWave<'c>,
    pub reason: NativeSessionError,
}
impl std::fmt::Debug for NativeWaveAttachRefusal<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.reason.fmt(f)
    }
}
pub struct NativeWaveSession<'c> {
    surface: &'c ResidentSurface<'c>,
    wave: ResidentNormalWave<'c>,
    chart: SymbolCurrentChart,
    basis: NormalWaveBasisChart<'c>,
    cursor: Cursor,
    emission_ordinal: u64,
    last: Option<EmittedSource>,
}
impl<'c> NativeWaveSession<'c> {
    pub fn from_wave(
        surface: &'c ResidentSurface<'c>,
        wave: ResidentNormalWave<'c>,
        chart: SymbolCurrentChart,
    ) -> Result<Self, NativeWaveAttachRefusal<'c>> {
        if wave.transport() != NormalWaveTransport::Applied {
            return Err(NativeWaveAttachRefusal {
                wave,
                reason: invalid("wave session requires explicit Applied transport"),
            });
        }
        let basis = match chart.receiver(surface) {
            Ok(v) => v,
            Err(reason) => return Err(NativeWaveAttachRefusal { wave, reason }),
        };
        // A pure receiver verifies the actual surface and domain, not just matching dimensions.
        if let Err(error) = wave.read_basis_face(&basis) {
            return Err(NativeWaveAttachRefusal {
                wave,
                reason: error.into(),
            });
        }
        Ok(Self {
            surface,
            wave,
            chart,
            basis,
            cursor: Cursor::Ready,
            emission_ordinal: 0,
            last: None,
        })
    }
    pub fn wave(&self) -> &ResidentNormalWave<'c> {
        &self.wave
    }
    fn ready(&self) -> Result<(), NativeSessionError> {
        if !matches!(self.cursor, Cursor::Ready) {
            return Err(invalid(
                "finish or retry the pending emission before another source operation",
            ));
        }
        Ok(())
    }
    fn pending_cut(&self) -> Result<(u64, u64), NativeSessionError> {
        let (generation, observations) = match &self.cursor {
            Cursor::AwaitSelection {
                generation,
                observations,
                ..
            }
            | Cursor::AwaitReentry {
                generation,
                observations,
                ..
            } => (*generation, *observations),
            Cursor::Ready => return Err(invalid("no pending emission")),
        };
        if generation != self.wave.epoch()
            || observations != self.wave.fibre().material_observations
        {
            return Err(invalid(
                "pending emission does not describe the held native state",
            ));
        }
        Ok((generation, observations))
    }
    /// Each native cut publishes once. Selection or re-entry refusal leaves a retryable phase;
    /// it does not regenerate a current or train on a self-selected symbol.
    pub fn next_symbol(&mut self, full: bool) -> Result<Value, NativeSessionError> {
        self.emit_symbol(full, false)
    }
    pub fn predict_symbol(&mut self, full: bool) -> Result<Value, NativeSessionError> {
        self.emit_symbol(full, true)
    }
    fn emit_symbol(&mut self, full: bool, retain: bool) -> Result<Value, NativeSessionError> {
        let next = self
            .emission_ordinal
            .checked_add(1)
            .ok_or_else(|| invalid("emission ordinal overflow"))?;
        if matches!(self.cursor, Cursor::Ready) {
            let prediction = if retain {
                Some(self.wave.predict()?.handle.id())
            } else {
                self.wave.advance()?;
                None
            };
            self.cursor = Cursor::AwaitSelection {
                generation: self.wave.epoch(),
                observations: self.wave.fibre().material_observations,
                prediction,
            };
        }
        let (generation, observations) = self.pending_cut()?;
        let face = self.wave.read_basis_face(&self.basis)?;
        let emitted = self.chart.emit(face)?;
        let prediction = match &self.cursor {
            Cursor::AwaitSelection { prediction, .. } => *prediction,
            Cursor::AwaitReentry { action, .. } => action.prediction,
            Cursor::Ready => unreachable!(),
        };
        let action = EmittedSource {
            ordinal: next,
            generation,
            symbol: emitted.symbol(),
            prediction,
        };
        if let Cursor::AwaitReentry { action: prior, .. } = &self.cursor {
            if *prior != action {
                return Err(invalid(
                    "restored projected action disagrees with its retained source",
                ));
            }
        }
        self.cursor = Cursor::AwaitReentry {
            generation,
            observations,
            action: action.clone(),
        };
        // All optional readouts precede the final native mutation. Afterwards only already-owned
        // metadata is published, so a reader failure never loses a committed re-entry.
        let detail = if full {
            Some(json!({"receiver":emitted.source().inspect()?,
            "source_current":emitted.source().source().view().inspect()?}))
        } else {
            None
        };
        let octets = emitted.octets().to_vec();
        let selection: NormalBasisSelection = emitted.selection().clone();
        let prior = self.last.clone();
        let reentry = if let Some(previous) = &prior {
            let source = self
                .chart
                .mount(self.surface, &[previous.symbol, action.symbol])?;
            let returned = self
                .wave
                .actuate_section(ResidentConstitutiveSection::integers(&source)?)?;
            Some(json!({"first":previous,"second":action,
                "before_epoch":returned.predecessor_fibre().epoch,
                "after_epoch":returned.successor_fibre().epoch,
                "relation":"ordered actual emissions in one output part"}))
        } else {
            None
        };
        self.last = Some(action.clone());
        self.emission_ordinal = next;
        self.cursor = Cursor::Ready;
        Ok(
            json!({"action":action,"octets":octets,"text":std::str::from_utf8(&octets).ok(),
            "selection":selection,"detail":detail,"reentry":reentry,
            "successor_epoch":self.wave.epoch(),"observations":self.wave.fibre().material_observations}),
        )
    }
    pub fn actuate_text(&mut self, text: &str) -> Result<Value, NativeSessionError> {
        self.ready()?;
        let symbols = self.chart.decode_text(text)?;
        if symbols.len() < 2 {
            return Err(invalid(
                "this field chart requires two actual source symbols; none are padded",
            ));
        }
        let mounted = self.chart.mount(self.surface, &symbols)?;
        let returned = self
            .wave
            .actuate_section(ResidentConstitutiveSection::integers(&mounted)?)?;
        self.last = None; // an explicit new source opens a new exterior output part
        Ok(
            json!({"rows":symbols.len(),"before_epoch":returned.predecessor_fibre().epoch,
            "after_epoch":returned.successor_fibre().epoch}),
        )
    }
    pub fn receive_symbol(
        &mut self,
        prediction: u64,
        text: &str,
    ) -> Result<Value, NativeSessionError> {
        self.ready()?;
        let symbols = self.chart.decode_text(text)?;
        if symbols.len() != 1 {
            return Err(invalid(
                "the addressed observation chart requires one actual symbol",
            ));
        }
        let source = self.chart.mount(self.surface, &symbols)?;
        let handle = self.wave.pending_prediction(prediction)?;
        let result = self.wave.receive_prediction(
            &handle,
            ResidentConstitutiveSection::integers(&source)?.row(0)?,
        )?;
        Ok(json!({"prediction":prediction,"epoch":self.wave.epoch(),
            "observations":result.successor_fibre.material_observations}))
    }
    pub fn inspect(&self) -> Value {
        json!({"model_kind":"applied-normal-wave","transport":self.wave.transport(),
            "epoch":self.wave.epoch(),"steps":self.wave.steps(),"pending_predictions":self.wave.pending_predictions(),
            "observations":self.wave.fibre().material_observations,"cursor":self.cursor,
            "emission_ordinal":self.emission_ordinal,"last_source":self.last})
    }
    pub fn checkpoint_stream(
        &self,
        path: impl AsRef<Path>,
        transport: &HnaStreamState,
    ) -> Result<PublicationReceipt<()>, NativeSessionError> {
        transport.validate().map_err(invalid)?;
        let rest = self.wave.rest()?;
        let header = Header {
            alphabet: self.chart.alphabet().clone(),
            coordinates: self.chart.coordinates().to_vec(),
            cursor: self.cursor.clone(),
            emission_ordinal: self.emission_ordinal,
            last: self.last.clone(),
            transport: transport.clone(),
        };
        let bytes = serde_json::to_vec(&header)?;
        Ok(publish_new(path, |file| {
            file.write_all(MAGIC)?;
            file.write_all(&(bytes.len() as u64).to_le_bytes())?;
            file.write_all(&bytes)?;
            rest.write(file).map_err(io::Error::other)
        })?)
    }
}

pub struct NativeWaveSavedSession {
    header: Header,
    rest: NormalWaveRest,
}
impl NativeWaveSavedSession {
    fn validate(header: &Header, rest: &NormalWaveRest) -> Result<(), NativeSessionError> {
        header.transport.validate().map_err(invalid)?;
        if rest.transport() != NormalWaveTransport::Applied
            || rest.material().roots() != header.alphabet.len()
        {
            return Err(invalid("saved wave scope or alphabet extent"));
        }
        // Reconstitute through the actual alphabet constructor so malformed parallel lists and
        // repeated identities are not silently admitted by a derived JSON decoder.
        let entries = header
            .alphabet
            .symbols()
            .into_iter()
            .map(|symbol| {
                Ok((
                    header
                        .alphabet
                        .identity(symbol)
                        .ok_or_else(|| invalid("missing symbol identity"))?
                        .to_owned(),
                    header
                        .alphabet
                        .octets(symbol)
                        .ok_or_else(|| invalid("missing symbol octets"))?
                        .to_vec(),
                ))
            })
            .collect::<Result<Vec<_>, NativeSessionError>>()?;
        let alphabet =
            SymbolAlphabet::declared(entries).map_err(|e| invalid(format!("alphabet: {e:?}")))?;
        if alphabet != header.alphabet {
            return Err(invalid("inconsistent alphabet serialization"));
        }
        SymbolCurrentChart::recharted(alphabet, header.coordinates.clone())?;
        if let Some(last) = &header.last {
            if last.generation > rest.epoch()
                || last.ordinal == 0
                || last.ordinal != header.emission_ordinal
                || last.symbol.0 as usize >= header.alphabet.len()
            {
                return Err(invalid("saved emitted source"));
            }
        }
        match &header.cursor {
            Cursor::Ready => {}
            Cursor::AwaitSelection {
                generation,
                observations,
                ..
            }
            | Cursor::AwaitReentry {
                generation,
                observations,
                ..
            } => {
                if header
                    .last
                    .as_ref()
                    .is_some_and(|last| last.generation >= *generation)
                {
                    return Err(invalid(
                        "pending emission does not follow its preceding source",
                    ));
                }
                if *generation != rest.epoch() || *observations != rest.material().observations() {
                    return Err(invalid("saved pending emission cut"));
                }
            }
        }
        let prediction = match &header.cursor {
            Cursor::Ready => None,
            Cursor::AwaitSelection { prediction, .. } => *prediction,
            Cursor::AwaitReentry { action, .. } => action.prediction,
        };
        if let Some(id) = prediction {
            if id != rest.epoch() || !rest.has_pending_prediction(id) {
                return Err(invalid("pending emission prediction address"));
            }
        }
        if let Cursor::AwaitReentry {
            action, generation, ..
        } = &header.cursor
        {
            if action.generation != *generation
                || action.ordinal
                    != header
                        .emission_ordinal
                        .checked_add(1)
                        .ok_or_else(|| invalid("emission ordinal overflow"))?
                || action.symbol.0 as usize >= header.alphabet.len()
            {
                return Err(invalid("saved pending action"));
            }
        }
        Ok(())
    }
    pub fn read(path: impl AsRef<Path>) -> Result<Self, NativeSessionError> {
        let mut file = File::open(path)?;
        let length = file.metadata()?.len();
        let prefix = (MAGIC.len() + 8) as u64;
        if length < prefix {
            return Err(invalid("truncated wave session"));
        }
        let mut magic = vec![0; MAGIC.len()];
        file.read_exact(&mut magic)?;
        if magic != MAGIC {
            return Err(invalid("wave session magic"));
        }
        let mut count = [0; 8];
        file.read_exact(&mut count)?;
        let count = u64::from_le_bytes(count);
        let remaining = length
            .checked_sub(prefix)
            .and_then(|v| v.checked_sub(count))
            .ok_or_else(|| invalid("wave header extent"))?;
        let size = usize::try_from(count).map_err(invalid)?;
        let mut bytes = vec![0; size];
        file.read_exact(&mut bytes)?;
        let header: Header = serde_json::from_slice(&bytes)?;
        let rest = NormalWaveRest::read(&mut file, remaining)?;
        Self::validate(&header, &rest)?;
        Ok(Self { header, rest })
    }
    /// Start an emission session from a completed packet-1 directory. The model is moved into
    /// the session; this does not restart development or reinterpret a legacy reference scope.
    pub fn from_model_directory(path: impl AsRef<Path>) -> Result<Self, NativeSessionError> {
        let path = path.as_ref();
        let mut file = File::open(path.join("model.wave"))?;
        let size = file.metadata()?.len();
        let rest = NormalWaveRest::read(&mut file, size)?;
        let alphabet: SymbolAlphabet =
            serde_json::from_reader(File::open(path.join("exterior-chart.json"))?)?;
        let coordinates = (0..alphabet.len()).collect();
        let header = Header {
            alphabet,
            coordinates,
            cursor: Cursor::Ready,
            emission_ordinal: 0,
            last: None,
            transport: HnaStreamState::default(),
        };
        Self::validate(&header, &rest)?;
        Ok(Self { header, rest })
    }
    pub fn with_session<R>(
        self,
        operation: impl FnOnce(
            &mut NativeWaveSession<'_>,
            &mut HnaStream,
        ) -> Result<R, NativeSessionError>,
    ) -> Result<R, NativeSessionError> {
        let readout = ResidentReadout::new().map_err(invalid)?;
        let surface = ResidentSurface::on(&readout).map_err(invalid)?;
        let wave = self.rest.remount(&surface, |_| {})?;
        let chart = SymbolCurrentChart::recharted(self.header.alphabet, self.header.coordinates)?;
        let mut session =
            NativeWaveSession::from_wave(&surface, wave, chart).map_err(|r| r.reason)?;
        session.cursor = self.header.cursor;
        session.emission_ordinal = self.header.emission_ordinal;
        session.last = self.header.last;
        let mut stream = HnaStream::from_state(self.header.transport).map_err(invalid)?;
        operation(&mut session, &mut stream)
    }
}

#[cfg(test)]
mod tests;

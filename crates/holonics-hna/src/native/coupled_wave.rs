//! Exterior session over one move-owned coupled normal wave.
use super::section_input::SymbolCurrentChart;
use super::NativeSessionError;
use crate::{publish_new, HnaStream, HnaStreamState, PublicationReceipt};
use holonic_engine::{
    codec_recovery::{Symbol, SymbolAlphabet},
    embedding_fiber::ResidentReadout,
    native_ecology::constitutive_fibre::{
        NormalWaveBasisChart, NormalWaveCoupled, NormalWaveRest, ResidentConstitutiveSection,
        ResidentNormalWave, WaveSourceReceiver,
    },
    resident_section::ResidentSurface,
};
use serde::{Deserialize, Serialize};
use serde_json::{json, Value};
use std::{
    fs::File,
    io::{self, Read, Write},
    path::Path,
};

const MAGIC: &[u8] = b"HNA-COUPLED-WAVE-SESSION\x01";
fn invalid(message: impl ToString) -> NativeSessionError {
    NativeSessionError::Application(message.to_string())
}

#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
struct Action {
    ordinal: u64,
    generation: u64,
    symbol: Symbol,
}
#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
enum Cursor {
    Ready,
    AwaitSelection { generation: u64 },
    AwaitReentry { generation: u64, action: Action },
}
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Header {
    alphabet: SymbolAlphabet,
    coordinates: Vec<usize>,
    member: usize,
    receiver: WaveSourceReceiver,
    cursor: Cursor,
    emission_ordinal: u64,
    last: Option<Action>,
    transport: HnaStreamState,
}

pub struct AttachRefusal<'c> {
    pub wave: ResidentNormalWave<'c, NormalWaveCoupled<'c>>,
    pub reason: NativeSessionError,
}
/// Named alias for callers that keep the session family in their public API.
pub type NativeCoupledWaveAttachRefusal<'c> = AttachRefusal<'c>;
impl std::fmt::Debug for AttachRefusal<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.reason.fmt(f)
    }
}

pub struct NativeCoupledWaveSession<'c> {
    surface: &'c ResidentSurface<'c>,
    wave: ResidentNormalWave<'c, NormalWaveCoupled<'c>>,
    chart: SymbolCurrentChart,
    basis: NormalWaveBasisChart<'c>,
    member: usize,
    receiver: WaveSourceReceiver,
    cursor: Cursor,
    emission_ordinal: u64,
    last: Option<Action>,
}
impl<'c> NativeCoupledWaveSession<'c> {
    pub fn from_wave(
        surface: &'c ResidentSurface<'c>,
        wave: ResidentNormalWave<'c, NormalWaveCoupled<'c>>,
        chart: SymbolCurrentChart,
        member: usize,
        receiver: WaveSourceReceiver,
    ) -> Result<Self, AttachRefusal<'c>> {
        let basis = match chart.receiver(surface) {
            Ok(v) => v,
            Err(reason) => return Err(AttachRefusal { wave, reason }),
        };
        if let Err(reason) = wave.neighborhood().generator(member) {
            return Err(AttachRefusal {
                wave,
                reason: reason.into(),
            });
        }
        if let Err(reason) = wave.read_basis_face(&basis) {
            return Err(AttachRefusal {
                wave,
                reason: reason.into(),
            });
        }
        Ok(Self {
            surface,
            wave,
            chart,
            basis,
            member,
            receiver,
            cursor: Cursor::Ready,
            emission_ordinal: 0,
            last: None,
        })
    }
    pub fn wave(&self) -> &ResidentNormalWave<'c, NormalWaveCoupled<'c>> {
        &self.wave
    }
    fn ready(&self) -> Result<(), NativeSessionError> {
        if matches!(self.cursor, Cursor::Ready) {
            Ok(())
        } else {
            Err(invalid(
                "finish or retry the pending emission before another source operation",
            ))
        }
    }
    fn pending_generation(&self) -> Result<u64, NativeSessionError> {
        let g = match &self.cursor {
            Cursor::AwaitSelection { generation } | Cursor::AwaitReentry { generation, .. } => {
                *generation
            }
            Cursor::Ready => return Err(invalid("no pending emission")),
        };
        if g != self.wave.epoch() {
            return Err(invalid(
                "pending emission does not describe the held native state",
            ));
        }
        Ok(g)
    }
    fn contact(
        &mut self,
    ) -> Result<
        holonic_engine::native_ecology::constitutive_fibre::NormalCoupledContact<'c>,
        NativeSessionError,
    > {
        let existing = self.wave.contact_ids().find(|id| {
            self.wave.contact(*id).is_ok_and(|h| {
                h.member() == self.member && h.relation().source_receiver() == self.receiver
            })
        });
        Ok(if let Some(id) = existing {
            self.wave.contact(id)?
        } else {
            self.wave
                .admit_contact_in_chart(self.member, self.receiver)?
        })
    }
    /// Cold observation of an already admitted contact; this never publishes the candidate.
    pub fn inspect_relation(&self) -> Result<Value, NativeSessionError> {
        let id = self
            .wave
            .contact_ids()
            .find(|id| {
                self.wave.contact(*id).is_ok_and(|h| {
                    h.member() == self.member && h.relation().source_receiver() == self.receiver
                })
            })
            .ok_or_else(|| invalid("no live contact for this session member and receiver"))?;
        let contact = self.wave.contact(id)?;
        let candidate = self.wave.read_contact(&contact)?;
        let reading = candidate.read_receiver()?.inspect()?;
        Ok(
            json!({"scope":"unpublished-conditional-family","epoch":self.wave.epoch(),
            "contact":id,"member":self.member,"receiver":self.receiver,"reading":reading}),
        )
    }
    pub fn project_current(&self, full: bool) -> Result<Value, NativeSessionError> {
        let face = self.wave.read_basis_face(&self.basis)?;
        let emitted = self.chart.emit_family(face)?;
        let detail = if full {
            Some(emitted.source().inspect()?)
        } else {
            None
        };
        Ok(
            json!({"scope":"projected-family-joint","epoch":self.wave.epoch(),"selection":emitted.selection(),
            "symbol":emitted.symbol(),"octets":emitted.octets(),"text":std::str::from_utf8(emitted.octets()).ok(),"detail":detail}),
        )
    }
    pub fn next_symbol(&mut self, full: bool) -> Result<Value, NativeSessionError> {
        let ordinal = self
            .emission_ordinal
            .checked_add(1)
            .ok_or_else(|| invalid("emission ordinal overflow"))?;
        if matches!(self.cursor, Cursor::Ready) {
            let contact = self.contact()?;
            let step = self.wave.advance_contact(&contact)?;
            self.cursor = Cursor::AwaitSelection {
                generation: step.successor_epoch,
            };
        }
        let generation = self.pending_generation()?;
        let face = self.wave.read_basis_face(&self.basis)?;
        let emitted = self.chart.emit_family(face)?;
        let action = Action {
            ordinal,
            generation,
            symbol: emitted.symbol(),
        };
        if let Cursor::AwaitReentry { action: prior, .. } = &self.cursor {
            if *prior != action {
                return Err(invalid(
                    "restored projected action disagrees with retained source",
                ));
            }
        }
        self.cursor = Cursor::AwaitReentry {
            generation,
            action: action.clone(),
        };
        let octets = emitted.octets().to_vec();
        let detail = if full {
            Some(json!(emitted.source().inspect()?))
        } else {
            None
        };
        let previous = self.last.clone();
        let reentry = if let Some(previous) = &previous {
            let source = self
                .chart
                .mount(self.surface, &[previous.symbol, action.symbol])?;
            let contact = self.contact()?;
            let returned = self.wave.actuate_contact_section(
                &contact,
                ResidentConstitutiveSection::integers(&source)?,
            )?;
            Some(
                json!({"first":previous,"second":action,"before_epoch":returned.predecessor_epoch,"after_epoch":returned.successor_epoch,"relation":"ordered actual emissions in one output part"}),
            )
        } else {
            None
        };
        self.last = Some(action.clone());
        self.emission_ordinal = ordinal;
        self.cursor = Cursor::Ready;
        Ok(
            json!({"receiver_scope":"projected-family-joint","action":action,"octets":octets,"text":std::str::from_utf8(&octets).ok(),"selection":emitted.selection(),"detail":detail,"reentry":reentry,"successor_epoch":self.wave.epoch()}),
        )
    }
    /// An explicitly observed next current, not an unpaired message or an evaluation target.
    pub fn receive_next_symbol(&mut self, text: &str) -> Result<Value, NativeSessionError> {
        self.ready()?;
        let symbols = self.chart.decode_text(text)?;
        if symbols.len() != 1 {
            return Err(invalid(
                "next-symbol observation requires one actual symbol",
            ));
        }
        let source = self.chart.mount(self.surface, &symbols)?;
        let contact = self.contact()?;
        let returned = self.wave.receive_contact_next(&contact,
            holonic_engine::native_ecology::constitutive_fibre::ResidentConstitutiveCurrent::integers(&source)?)?;
        self.last = None;
        Ok(json!({"scope":"actual-next-current","symbol":symbols[0],
            "before_epoch":returned.predecessor_epoch,"after_epoch":returned.successor_epoch,
            "material_deposited":false}))
    }
    pub fn actuate_text(&mut self, text: &str) -> Result<Value, NativeSessionError> {
        self.ready()?;
        let symbols = self.chart.decode_text(text)?;
        if symbols.len() < 2 {
            return Err(invalid(
                "this field chart requires two actual source symbols; none are padded",
            ));
        }
        let source = self.chart.mount(self.surface, &symbols)?;
        let contact = self.contact()?;
        let returned = self
            .wave
            .actuate_contact_section(&contact, ResidentConstitutiveSection::integers(&source)?)?;
        self.last = None;
        Ok(
            json!({"rows":symbols.len(),"before_epoch":returned.predecessor_epoch,"after_epoch":returned.successor_epoch}),
        )
    }
    pub fn inspect(&self) -> Value {
        json!({"model_kind":"coupled-normal-wave","member":self.member,"receiver":self.receiver,"epoch":self.wave.epoch(),"passages":self.wave.current().passages(),"observations":self.wave.normal_material().observations(),"cursor":self.cursor,"emission_ordinal":self.emission_ordinal,"last_source":self.last})
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
            member: self.member,
            receiver: self.receiver,
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

pub struct NativeCoupledWaveSavedSession {
    header: Header,
    rest: NormalWaveRest,
}
impl NativeCoupledWaveSavedSession {
    fn validate(h: &Header, r: &NormalWaveRest) -> Result<(), NativeSessionError> {
        h.transport.validate().map_err(invalid)?;
        if !r.is_coupled()
            || r.material().roots() != h.alphabet.len()
            || r.coupled_members().is_none_or(|n| h.member >= n)
        {
            return Err(invalid("saved session requires complete coupled rest"));
        }
        let entries = h
            .alphabet
            .symbols()
            .into_iter()
            .map(|s| {
                Ok((
                    h.alphabet
                        .identity(s)
                        .ok_or_else(|| invalid("missing symbol identity"))?
                        .to_owned(),
                    h.alphabet
                        .octets(s)
                        .ok_or_else(|| invalid("missing symbol octets"))?
                        .to_vec(),
                ))
            })
            .collect::<Result<Vec<_>, NativeSessionError>>()?;
        if SymbolAlphabet::declared(entries).map_err(|e| invalid(format!("alphabet: {e:?}")))?
            != h.alphabet
        {
            return Err(invalid("inconsistent alphabet serialization"));
        }
        SymbolCurrentChart::recharted(h.alphabet.clone(), h.coordinates.clone())?;
        if h.emission_ordinal == 0 && h.last.is_some() {
            return Err(invalid("saved emitted source"));
        }
        if let Some(a) = &h.last {
            let age = r.epoch().checked_sub(a.generation);
            let admitted_age = match h.cursor {
                Cursor::Ready => matches!(age, Some(0 | 1)),
                Cursor::AwaitSelection { .. } | Cursor::AwaitReentry { .. } => {
                    matches!(age, Some(1 | 2))
                }
            };
            if a.ordinal != h.emission_ordinal
                || a.generation == 0
                || !admitted_age
                || a.symbol.0 as usize >= h.alphabet.len()
            {
                return Err(invalid("saved emitted source"));
            }
        }
        match &h.cursor {
            Cursor::AwaitSelection { generation } | Cursor::AwaitReentry { generation, .. }
                if h.last
                    .as_ref()
                    .is_some_and(|last| last.generation >= *generation) =>
            {
                return Err(invalid(
                    "pending emission does not follow its preceding source",
                ))
            }
            Cursor::Ready => {}
            Cursor::AwaitSelection { generation } => {
                if *generation == 0 || *generation != r.epoch() {
                    return Err(invalid("saved pending emission cut"));
                }
            }
            Cursor::AwaitReentry { generation, action } => {
                if *generation == 0
                    || *generation != r.epoch()
                    || action.generation != *generation
                    || action.ordinal
                        != h.emission_ordinal
                            .checked_add(1)
                            .ok_or_else(|| invalid("emission ordinal overflow"))?
                    || action.symbol.0 as usize >= h.alphabet.len()
                {
                    return Err(invalid("saved pending action"));
                }
            }
        }
        Ok(())
    }
    pub fn read(path: impl AsRef<Path>) -> Result<Self, NativeSessionError> {
        let mut f = File::open(path)?;
        let len = f.metadata()?.len();
        let prefix = (MAGIC.len() + 8) as u64;
        if len < prefix {
            return Err(invalid("truncated coupled session"));
        }
        let mut m = vec![0; MAGIC.len()];
        f.read_exact(&mut m)?;
        if m != MAGIC {
            return Err(invalid("coupled session magic"));
        }
        let mut n = [0; 8];
        f.read_exact(&mut n)?;
        let count = u64::from_le_bytes(n);
        let rem = len
            .checked_sub(prefix)
            .and_then(|v| v.checked_sub(count))
            .ok_or_else(|| invalid("coupled header extent"))?;
        let mut b = vec![0; usize::try_from(count).map_err(invalid)?];
        f.read_exact(&mut b)?;
        let h: Header = serde_json::from_slice(&b)?;
        let r = NormalWaveRest::read(&mut f, rem)?;
        Self::validate(&h, &r)?;
        Ok(Self { header: h, rest: r })
    }
    pub fn from_model_directory(
        path: impl AsRef<Path>,
        member: usize,
        receiver: WaveSourceReceiver,
    ) -> Result<Self, NativeSessionError> {
        let p = path.as_ref();
        let mut f = File::open(p.join("model.wave"))?;
        let size = f.metadata()?.len();
        let r = NormalWaveRest::read(&mut f, size)?;
        let a: SymbolAlphabet =
            serde_json::from_reader(File::open(p.join("exterior-chart.json"))?)?;
        let h = Header {
            alphabet: a,
            coordinates: (0..r.material().roots()).collect(),
            member,
            receiver,
            cursor: Cursor::Ready,
            emission_ordinal: 0,
            last: None,
            transport: HnaStreamState::default(),
        };
        Self::validate(&h, &r)?;
        Ok(Self { header: h, rest: r })
    }
    pub fn with_session<R>(
        self,
        operation: impl FnOnce(
            &mut NativeCoupledWaveSession<'_>,
            &mut HnaStream,
        ) -> Result<R, NativeSessionError>,
    ) -> Result<R, NativeSessionError> {
        let ro = ResidentReadout::new().map_err(invalid)?;
        let s = ResidentSurface::on(&ro).map_err(invalid)?;
        let w = self.rest.remount_coupled(&s, |_| {})?;
        let c = SymbolCurrentChart::recharted(self.header.alphabet, self.header.coordinates)?;
        let mut session =
            NativeCoupledWaveSession::from_wave(&s, w, c, self.header.member, self.header.receiver)
                .map_err(|r| r.reason)?;
        session.cursor = self.header.cursor;
        session.emission_ordinal = self.header.emission_ordinal;
        session.last = self.header.last;
        let mut stream = HnaStream::from_state(self.header.transport).map_err(invalid)?;
        operation(&mut session, &mut stream)
    }
}

#[cfg(test)]
mod tests;

//! Whole-section text reception over the existing constituted-field model.
//! Text segmentation and symbol exhibition are exterior codecs. The native model receives
//! complete unit-basis sections and an ordered context tensor, and learns its own D/M action.
use super::section_input::SymbolCurrentChart;
use super::{NativeCoupledBody, NativeFieldReactionPort, NativeSessionError, SavedCoupledBody};
use crate::{publish_new, HnaStream, HnaStreamState, PublicationReceipt};
use holonic_engine::{
    codec_recovery::{Symbol, SymbolAlphabet},
    embedding_fiber::ResidentReadout,
    native_ecology::constitutive_fibre::{
        ConditionContactMetric, NativeConstitutiveField, NativeFieldOccurrence, NativeJunctionSeed,
        NativePhaseCurrent, ResidentConstitutiveCurrent, ResidentConstitutiveFibre,
        ResidentConstitutiveSection, ResidentGeneratorNeighborhood, ResidentNormalMaterial,
    },
    resident_section::{ResidentGrain, ResidentSection, ResidentSectionRest, ResidentSurface},
};
use serde::{Deserialize, Serialize};
use serde_json::{json, Value};
use std::{
    fs::File,
    io::{Read, Write},
    path::Path,
    time::Instant,
};
type Result<T> = std::result::Result<T, NativeSessionError>;
fn invalid(s: impl ToString) -> NativeSessionError {
    NativeSessionError::Application(s.to_string())
}
fn grain() -> u32 {
    48
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum FieldTextCodec {
    #[default]
    UnicodeScalars,
    WhitespaceWords,
}
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct FieldSessionSpec {
    pub symbols: Vec<String>,
    pub section_symbols: usize,
    pub context_symbols: usize,
    #[serde(default)]
    pub codec: FieldTextCodec,
    #[serde(default = "grain")]
    pub fractional_bits: u32,
}
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct FieldSectionRequest {
    pub text: String,
    #[serde(default)]
    pub context: Vec<String>,
    #[serde(default)]
    pub commit: bool,
    #[serde(default)]
    pub retain_comparison: bool,
}
impl FieldSectionRequest {
    /// Exterior bridge from validated exposure families. Callers select the source aperture;
    /// each supplied preceding family must be the recorded prior parent of the next one.
    /// ExposureReader validates the records; their paths/IDs never become native amplitudes.
    pub fn from_exposures(
        request: &crate::alpha::exposure::ExposureOccurrence,
        context: &[&crate::alpha::exposure::ExposureOccurrence],
        commit: bool,
        retain_comparison: bool,
    ) -> Result<Self> {
        fn text(event: &crate::alpha::exposure::ExposureOccurrence) -> Result<String> {
            event
                .shared_visible_parts()
                .map_err(invalid)?
                .iter()
                .map(|p| {
                    p.text.as_deref().ok_or_else(|| {
                        invalid("this field text codec requires visible textual parts")
                    })
                })
                .collect::<Result<Vec<_>>>()
                .map(|p| p.concat())
        }
        let chain = context
            .iter()
            .copied()
            .chain(std::iter::once(request))
            .collect::<Vec<_>>();
        for pair in chain.windows(2) {
            if pair[0].sequence >= pair[1].sequence
                || pair[1].shared_prior_parent().map_err(invalid)?.as_ref() != Some(&pair[0].family)
            {
                return Err(invalid("context is not the recorded prior exposure chain"));
            }
        }
        Ok(Self {
            text: text(request)?,
            context: context
                .iter()
                .map(|event| text(event))
                .collect::<Result<Vec<_>>>()?,
            commit,
            retain_comparison,
        })
    }
}
impl FieldSessionSpec {
    fn chart(&self) -> Result<SymbolCurrentChart> {
        if self.section_symbols == 0 || !(1..=120).contains(&self.fractional_bits) {
            return Err(invalid("field section extent/grain"));
        }
        for symbol in &self.symbols {
            let valid = match self.codec {
                FieldTextCodec::UnicodeScalars => symbol.chars().count() == 1,
                FieldTextCodec::WhitespaceWords => {
                    !symbol.is_empty() && !symbol.chars().any(char::is_whitespace)
                }
            };
            if !valid {
                return Err(invalid("symbol does not fit the declared text codec"));
            }
        }
        let alphabet = SymbolAlphabet::declared(
            self.symbols
                .iter()
                .map(|s| (s.clone(), s.as_bytes().to_vec()))
                .collect(),
        )
        .map_err(invalid)?;
        Ok(SymbolCurrentChart::declared(alphabet))
    }
    fn extents(&self) -> Result<(usize, usize, usize)> {
        let complex = self
            .section_symbols
            .checked_mul(self.symbols.len())
            .ok_or_else(|| invalid("field section extent"))?;
        let nodes = complex
            .checked_add(2)
            .ok_or_else(|| invalid("field node extent"))?
            / 3;
        let context = self
            .symbols
            .len()
            .checked_pow(u32::try_from(self.context_symbols).map_err(invalid)?)
            .ok_or_else(|| invalid("context tensor extent"))?;
        let features = nodes
            .checked_mul(3)
            .and_then(|s| s.checked_mul(context)?.checked_add(s)?.checked_add(context))
            .ok_or_else(|| invalid("field reaction feature extent"))?;
        Ok((nodes, context, features))
    }
    fn symbols_of(&self, chart: &SymbolCurrentChart, text: &str) -> Result<Vec<Symbol>> {
        match self.codec {
            FieldTextCodec::UnicodeScalars => chart.decode_text(text),
            FieldTextCodec::WhitespaceWords => text
                .split_whitespace()
                .map(|s| {
                    chart.alphabet().symbol_of(s).ok_or_else(|| {
                        invalid(format!("symbol {s:?} is outside the declared codec"))
                    })
                })
                .collect(),
        }
    }
}

pub struct NativeFieldSession<'c> {
    surface: &'c ResidentSurface<'c>,
    spec: FieldSessionSpec,
    chart: SymbolCurrentChart,
    body: NativeCoupledBody<'c>,
}
impl<'c> NativeFieldSession<'c> {
    fn found(surface: &'c ResidentSurface<'c>, spec: &FieldSessionSpec) -> Result<Self> {
        let chart = spec.chart()?;
        let (nodes, context, features) = spec.extents()?;
        let seed = NativeJunctionSeed {
            incoming_admittance: 1,
            held_admittance: 1,
            incoming_transport: NativePhaseCurrent::unit(),
            initial_held: NativePhaseCurrent::zero(),
        };
        let mut field = NativeConstitutiveField::found_with_enclosed_junction(
            surface,
            vec![seed; nodes],
            ResidentGrain(spec.fractional_bits),
        )?;
        let first = field.advance_resident(&mut NativeFieldOccurrence::entering(
            vec![NativePhaseCurrent::unit(); nodes],
        ))?;
        field.advance_resident(&mut NativeFieldOccurrence::through(
            first.source,
            vec![NativePhaseCurrent::new(0, 1, 1)?; nodes],
        ))?;
        let initial = surface
            .mount_section_rest(
                &ResidentSectionRest::found(
                    1,
                    2 * context,
                    ResidentGrain(0),
                    64,
                    vec![(0, 0); 2 * context],
                )
                .map_err(invalid)?,
            )
            .map_err(invalid)?;
        let law = ResidentConstitutiveFibre::found_bilinear_contact(
            surface,
            3 * nodes,
            context,
            3 * nodes,
        )?;
        let material = ResidentNormalMaterial::found_features(
            surface,
            features,
            3 * nodes,
            ResidentGrain(spec.fractional_bits),
        )?;
        let mut reaction = ResidentGeneratorNeighborhood::with_shared_condition(
            vec![law],
            ResidentConstitutiveCurrent::integers(&initial)?,
            ConditionContactMetric::UnitAdmittanceRealification,
        )?;
        reaction
            .attach_normal_prediction(0, material)
            .map_err(|(_, e)| e)?;
        let body = NativeCoupledBody::from_field_with_reaction_port(
            field,
            reaction,
            0,
            NativeFieldReactionPort::IncomingBoundary,
        )
        .map_err(|r| r.reason)?;
        Ok(Self {
            surface,
            spec: spec.clone(),
            chart,
            body,
        })
    }
    fn mount_text(&self, text: &str) -> Result<ResidentSection<'c>> {
        let symbols = self.spec.symbols_of(&self.chart, text)?;
        if symbols.len() != self.spec.section_symbols {
            return Err(invalid(format!(
                "requested section has {} symbols; this declared boundary has {}",
                symbols.len(),
                self.spec.section_symbols
            )));
        }
        self.chart
            .mount_joint(self.surface, &symbols, 6 * self.spec.extents()?.0)
    }
    fn mount_context(&self, parts: &[String]) -> Result<ResidentSection<'c>> {
        let symbols = parts
            .iter()
            .map(|s| self.spec.symbols_of(&self.chart, s))
            .collect::<Result<Vec<_>>>()?
            .into_iter()
            .flatten()
            .collect::<Vec<_>>();
        if symbols.len() != self.spec.context_symbols {
            return Err(invalid(format!(
                "context has {} symbols; declared context section has {}",
                symbols.len(),
                self.spec.context_symbols
            )));
        }
        if symbols.is_empty() {
            return Ok(self
                .surface
                .mount_section_rest(
                    &ResidentSectionRest::found(
                        1,
                        3,
                        ResidentGrain(0),
                        64,
                        vec![(1, 1), (0, 0), (1, 1)],
                    )
                    .map_err(invalid)?,
                )
                .map_err(invalid)?);
        }
        let rows = self.chart.mount(self.surface, &symbols)?;
        let rows = ResidentConstitutiveSection::integers(&rows)?;
        let mut tensor = rows.row(0)?.to_owned(self.surface)?;
        for at in 1..symbols.len() {
            let next = rows.row(at)?.to_owned(self.surface)?;
            let a = ResidentConstitutiveSection::rationals(&tensor)?;
            let b = ResidentConstitutiveSection::rationals(&next)?;
            let joined = a.bilinear_features(self.surface, b)?;
            let features = joined.features();
            let start = a.components() + b.components();
            // Keep the tensor-product coordinates. Marginal inputs remain exterior operands;
            // the ordered context product is constructed on device, not an episode identifier.
            tensor = features
                .row(0)?
                .restrict_components(start..features.components())?
                .to_owned(self.surface)?;
        }
        Ok(tensor)
    }
    pub fn request(&mut self, request: &FieldSectionRequest) -> Result<Value> {
        if request.retain_comparison && !request.commit {
            return Err(invalid(
                "a retained target requires committed field generation",
            ));
        }
        let start = Instant::now();
        let input = self.mount_text(&request.text)?;
        let condition = self.mount_context(&request.context)?;
        let chart = self.chart.receiver(self.surface)?;
        let generation = Instant::now();
        let produced = if request.commit {
            self.body.generate_field(
                ResidentConstitutiveCurrent::integers(&input)?.into(),
                ResidentConstitutiveCurrent::rational(&condition)?,
                request.retain_comparison,
            )?
        } else {
            self.body.preview_field(
                ResidentConstitutiveCurrent::integers(&input)?.into(),
                ResidentConstitutiveCurrent::rational(&condition)?,
            )?
        };
        let generation_us = generation.elapsed().as_micros();
        let receive = || -> Result<_> {
            let selected = produced
                .output()
                .restrict(0..2 * self.spec.section_symbols * self.spec.symbols.len())?;
            let face = selected
                .view()
                .read_basis_sections(&chart, self.spec.section_symbols)?;
            Ok(face.selections()?)
        };
        let selections = match receive() {
            Ok(value) => value,
            Err(error) if request.commit => {
                return Ok(
                    json!({"schema":"org.holonics.hna.field-section.v1", "status":"committed-receiver-refused", "committed":true,
                "comparison":produced.comparison_id(),"producing_epoch":produced.producing_epoch(),"error":error.to_string(),"anatomy":self.inspect()}),
                )
            }
            Err(error) => return Err(error),
        };
        let pieces = selections
            .iter()
            .map(|v| {
                self.spec
                    .symbols
                    .get(v.selected)
                    .cloned()
                    .ok_or_else(|| invalid("selected symbol outside codec"))
            })
            .collect::<Result<Vec<_>>>()?;
        let text = pieces.join(match self.spec.codec {
            FieldTextCodec::UnicodeScalars => "",
            FieldTextCodec::WhitespaceWords => " ",
        });
        Ok(
            json!({"schema":"org.holonics.hna.field-section.v1","text":text,"symbols":pieces,
            "comparison":produced.comparison_id(),"producing_epoch":produced.producing_epoch(),"committed":request.commit,
            "selections":selections,"generated":produced.inspect()?,"generation_us":generation_us,"elapsed_us":start.elapsed().as_micros(),
            "scope":"joint complete section; native incoming reaction and constituted scattering; declared exterior symbol codec"}),
        )
    }
    pub fn observe(&mut self, source: u64, text: &str, step_bits: u32) -> Result<Value> {
        let start = Instant::now();
        let target = self.mount_text(text)?;
        let returned = self.body.observe_field(
            source,
            ResidentConstitutiveCurrent::integers(&target)?.into(),
            step_bits,
        )?;
        Ok(
            json!({"source":source,"target":text,"returned":returned,"elapsed_us":start.elapsed().as_micros(),"anatomy":self.inspect()}),
        )
    }
    pub fn release(&mut self, source: u64) -> Result<Value> {
        self.body.release(source)?;
        Ok(json!({"released":source,"anatomy":self.inspect()}))
    }
    pub fn inspect(&self) -> Value {
        json!({"kind":"constituted-field-session","epoch":self.body.epoch(),"pending":self.body.pending_coupled_predictions(),"pending_comparisons":self.body.pending_ids().ok(),"spec":self.spec,"census":self.surface.census()})
    }
    pub fn inspect_current(&mut self) -> Result<Value> {
        self.body.inspect_current()
    }
    pub fn checkpoint(
        &self,
        path: &Path,
        state: &HnaStreamState,
    ) -> Result<PublicationReceipt<()>> {
        let rest = self.body.rest()?;
        let saved = NativeFieldSavedSession {
            spec: self.spec.clone(),
            state: state.clone(),
            body: rest,
        };
        let mut bytes = Vec::new();
        saved.write(&mut bytes)?;
        Ok(publish_new(path, |out| out.write_all(&bytes))?)
    }
}
const MAGIC: &[u8] = b"HNA-FIELD-SESSION\x01";
pub struct NativeFieldSavedSession {
    spec: FieldSessionSpec,
    state: HnaStreamState,
    body: SavedCoupledBody,
}
impl NativeFieldSavedSession {
    fn write(&self, out: &mut impl Write) -> Result<()> {
        let header = serde_json::to_vec(&(self.spec.clone(), self.state.clone()))?;
        let mut body = Vec::new();
        self.body.write(&mut body)?;
        out.write_all(MAGIC)?;
        for bytes in [&header, &body] {
            out.write_all(&(bytes.len() as u64).to_le_bytes())?;
            out.write_all(bytes)?;
        }
        Ok(())
    }
    pub fn open(path: impl AsRef<Path>) -> Result<Self> {
        let file = File::open(path)?;
        let octets = file.metadata()?.len();
        Self::read(&mut file.take(octets), octets)
    }
    fn read(input: &mut impl Read, octets: u64) -> Result<Self> {
        let mut input = input.take(octets);
        let mut magic = vec![0; MAGIC.len()];
        input.read_exact(&mut magic)?;
        if magic != MAGIC {
            return Err(invalid("unsupported field-session rest"));
        }
        fn blob(input: &mut std::io::Take<impl Read>) -> Result<Vec<u8>> {
            let mut n = [0; 8];
            input.read_exact(&mut n)?;
            let n = u64::from_le_bytes(n);
            if n > input.limit() {
                return Err(invalid("truncated field-session rest"));
            }
            let mut bytes = Vec::new();
            bytes
                .try_reserve_exact(usize::try_from(n).map_err(invalid)?)
                .map_err(invalid)?;
            bytes.resize(n as usize, 0);
            input.read_exact(&mut bytes)?;
            Ok(bytes)
        }
        let (spec, state): (FieldSessionSpec, HnaStreamState) =
            serde_json::from_slice(&blob(&mut input)?)?;
        spec.chart()?;
        state.validate().map_err(invalid)?;
        let bytes = blob(&mut input)?;
        let body = SavedCoupledBody::read(&mut bytes.as_slice(), bytes.len() as u64)?;
        if !matches!(body, SavedCoupledBody::Field(_))
            || body.roots() != spec.extents()?.0
            || input.limit() != 0
        {
            return Err(invalid("field session body/configuration mismatch"));
        }
        Ok(Self { spec, state, body })
    }
    pub fn with_session<T>(
        self,
        f: impl FnOnce(&mut NativeFieldSession<'_>, &mut HnaStream) -> Result<T>,
    ) -> Result<T> {
        let readout = ResidentReadout::new().map_err(invalid)?;
        let surface = ResidentSurface::on(&readout).map_err(invalid)?;
        let chart = self.spec.chart()?;
        let mut session = NativeFieldSession {
            surface: &surface,
            spec: self.spec,
            chart,
            body: self.body.remount(&surface)?,
        };
        let (nodes, context, _) = session.spec.extents()?;
        if session.body.field_dimensions()?
            != (
                6 * nodes,
                2 * context,
                ResidentGrain(session.spec.fractional_bits),
                NativeFieldReactionPort::IncomingBoundary,
            )
        {
            return Err(invalid(
                "saved session model ports/grain do not match its declared codec",
            ));
        }
        let mut stream = HnaStream::from_state(self.state).map_err(invalid)?;
        f(&mut session, &mut stream)
    }
}
pub fn with_field_session<T>(
    spec: &FieldSessionSpec,
    f: impl FnOnce(&mut NativeFieldSession<'_>) -> Result<T>,
) -> Result<T> {
    let readout = ResidentReadout::new().map_err(invalid)?;
    let surface = ResidentSurface::on(&readout).map_err(invalid)?;
    let mut session = NativeFieldSession::found(&surface, spec)?;
    f(&mut session)
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    #[ignore = "requires CUDA; actual outstanding field comparison resumes with its producing D/M"]
    fn field_session_reopens_old_producing_material_and_returns_once() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("pending.rest");
        let spec = FieldSessionSpec {
            symbols: vec!["a".into(), "b".into(), "c".into()],
            section_symbols: 1,
            context_symbols: 0,
            codec: FieldTextCodec::UnicodeScalars,
            fractional_bits: 48,
        };
        let make = |text: &str| FieldSectionRequest {
            text: text.into(),
            context: vec![],
            commit: true,
            retain_comparison: true,
        };
        let (expected, current) = with_field_session(&spec, |s| {
            let a = s.request(&make("a"))?;
            let b = s.request(&make("b"))?;
            s.observe(a["comparison"].as_u64().unwrap(), "b", 3)?;
            // b still refers to material from BEFORE the update just performed.
            s.checkpoint(&path, &HnaStreamState::default())?;
            let returned = s.observe(b["comparison"].as_u64().unwrap(), "c", 3)?;
            assert!(s
                .observe(b["comparison"].as_u64().unwrap(), "c", 3)
                .is_err());
            Ok((returned["returned"].clone(), s.inspect_current()?))
        })
        .unwrap();
        NativeFieldSavedSession::open(&path)
            .unwrap()
            .with_session(|s, _| {
                assert_eq!(s.inspect()["pending"], 1);
                let got = s.observe(1, "c", 3)?;
                assert_eq!(got["returned"], expected);
                assert_eq!(s.inspect_current()?, current);
                assert!(s.observe(1, "c", 3).is_err());
                Ok(())
            })
            .unwrap();
    }
    #[test]
    fn text_codec_and_extents_are_declared() {
        let spec = FieldSessionSpec {
            symbols: vec!["red".into(), "blue".into(), "green".into()],
            section_symbols: 2,
            context_symbols: 2,
            codec: FieldTextCodec::WhitespaceWords,
            fractional_bits: 48,
        };
        let chart = spec.chart().unwrap();
        assert_eq!(spec.extents().unwrap(), (2, 9, 69));
        assert_eq!(
            spec.symbols_of(&chart, "red blue").unwrap(),
            [Symbol(0), Symbol(1)]
        );
        assert!(spec.symbols_of(&chart, "orange").is_err());
    }
}

#[cfg(test)]
mod delivery_tests {
    use super::*;
    struct Refuse;
    impl Write for Refuse {
        fn write(&mut self, _: &[u8]) -> std::io::Result<usize> {
            Err(std::io::Error::new(
                std::io::ErrorKind::BrokenPipe,
                "receiver disconnected",
            ))
        }
        fn flush(&mut self) -> std::io::Result<()> {
            Ok(())
        }
    }
    #[test]
    #[ignore = "requires CUDA; failed output drains after restart without regenerating the field"]
    fn field_stream_preserves_committed_response_across_write_failure() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("delivery.session");
        let spec = FieldSessionSpec {
            symbols: vec!["a".into(), "b".into(), "c".into()],
            section_symbols: 1,
            context_symbols: 0,
            codec: FieldTextCodec::UnicodeScalars,
            fractional_bits: 48,
        };
        let request = crate::HnaStreamRequest {
            schema: crate::HNA_STREAM_REQUEST_SCHEMA.into(),
            command: crate::HnaStreamCommand::FieldRequest {
                request: FieldSectionRequest {
                    text: "a".into(),
                    context: vec![],
                    commit: true,
                    retain_comparison: true,
                },
            },
        };
        let mut line = serde_json::to_vec(&request).unwrap();
        line.push(b'\n');
        let epoch = with_field_session(&spec, |s| {
            let mut stream = HnaStream::new();
            assert!(stream
                .pump_field(s, &mut std::io::Cursor::new(&line), &mut Refuse)
                .is_err());
            assert!(stream.state().output.is_some());
            assert_eq!(s.inspect()["pending"], 1);
            s.checkpoint(&path, stream.state())?;
            Ok(s.body.epoch())
        })
        .unwrap();
        NativeFieldSavedSession::open(&path)
            .unwrap()
            .with_session(|s, stream| {
                stream.open_new_connection();
                let mut output = Vec::new();
                stream
                    .pump_field(s, &mut std::io::Cursor::new(Vec::<u8>::new()), &mut output)
                    .map_err(invalid)?;
                assert_eq!(s.body.epoch(), epoch);
                assert_eq!(s.inspect()["pending"], 1);
                let event: Value = serde_json::from_slice(&output)?;
                assert_eq!(event["event"], "field-request");
                assert_eq!(event["value"]["comparison"], 0);
                s.observe(0, "b", 1)?;
                assert_eq!(s.inspect()["pending"], 0);
                Ok(())
            })
            .unwrap();
    }
}

#[cfg(test)]
mod exposure_tests {
    use super::*;
    use crate::alpha::exposure::ExposureOccurrence;
    fn event(sequence: u64, name: &str, parent: Option<&str>, text: &str) -> ExposureOccurrence {
        serde_json::from_value(json!({"schema":"org.holonics.conversation-exposure.v1","kind":"occurrence-family","sequence":sequence,
            "position":{"first_source":0,"first_record":sequence,"first_event":sequence},"family":{"provider":"codex","record_group":name},
            "partition":"development","partition_reasons":[],"conflicts":[],"views":[{"event":sequence,"source":0,"provider":"codex",
                "record":{"number":sequence,"byte_start":0,"byte_end":1},"author_class":"human","record_kind":"message","flags":[],"provider_metadata":{},
                "visible_parts":[{"ordinal":0,"pointer":"/text","kind":"text","text":text}],"nonvisible_part_references":[],
                "links":parent.map(|p|vec![json!({"kind":"provider-parent","evidence":"declared test source relationship","availability":"prior",
                    "target":{"event":sequence-1,"source":0,"provider":"codex","record_group":p}})]).unwrap_or_default()}]})).unwrap()
    }
    #[test]
    fn exposure_bridge_preserves_whole_parts_and_rejects_a_future_or_wrong_parent() {
        let before = event(0, "before", None, "red");
        let request = event(1, "request", Some("before"), "red blue");
        let prepared =
            FieldSectionRequest::from_exposures(&request, &[&before], false, false).unwrap();
        assert_eq!(prepared.text, "red blue");
        assert_eq!(prepared.context, ["red"]);
        let other = event(0, "unrelated", None, "red");
        assert!(FieldSectionRequest::from_exposures(&request, &[&other], false, false).is_err());
        let future = event(2, "before", None, "red");
        assert!(FieldSectionRequest::from_exposures(&request, &[&future], false, false).is_err());
    }
}

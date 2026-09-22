//! Source-qualified sessions over one constituted-field model.
//! Native incidence prepares resident currents directly; the retained text presentations
//! supply their explicitly declared symbol charts.
use super::section_input::SymbolCurrentChart;
mod boundary;
mod generator_application;
mod geometric;
mod incident_application;
mod incident_encoder;
mod incident_receiver;
pub use generator_application::GeneratorSessionOptions;
use generator_application::{GeneratorPresentation, GeneratorPresentationRest};
use incident_application::{IncidentPresentation, IncidentPresentationRest};
mod incidence;
mod incident_preparation;
mod mathematical_port;
mod native_source;
mod shared;
use super::mathematical::{MathematicalInputWire, MathematicalRequest, NativeMathematicalSession};
use super::{NativeCoupledBody, NativeFieldReactionPort, NativeSessionError, SavedCoupledBody};
use crate::{HnaStream, HnaStreamState, PublicationReceipt, publish_new};
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
pub use incidence::{
    NativeFieldIncidence, NativeFieldIncidenceDeclaration, NativeFieldIncomingArc,
    NativeFieldOmittedSelfComparison, PreparedFieldIncidence,
};
pub use incident_preparation::{
    IncidentContact, IncidentContactKind, IncidentPreparation, IncidentSourceCell,
    IncidentSourceOrigin, IncidentSourcePart, IncidentSourceRegion,
};
pub use mathematical_port::FieldMathematicalRequest;
pub use native_source::*;
use serde::{Deserialize, Serialize};
use serde_json::{Value, json};
use std::{
    collections::BTreeMap,
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
    Utf8Nibbles,
}
/// The legacy chart expands a categorical context tensor. Joint regions place the actual
/// context currents beside the requested region and use a bounded observation-mask port.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum FieldSourceChart {
    #[default]
    TensorCondition,
    JointRegions,
    SharedRegions,
    GeometricRegions,
    IncidentField,
    GeneratorMachine,
}
fn tensor_condition(chart: &FieldSourceChart) -> bool {
    *chart == FieldSourceChart::TensorCondition
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct FieldSessionSpec {
    pub symbols: Vec<String>,
    pub section_symbols: usize,
    pub context_symbols: usize,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub region_offsets: Vec<isize>,
    #[serde(default, skip_serializing_if = "tensor_condition")]
    pub source_chart: FieldSourceChart,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub geometry: Option<super::GeometricFieldSpec>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub incident: Option<IncidentFieldOptions>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub generator: Option<GeneratorSessionOptions>,
    #[serde(default)]
    pub codec: FieldTextCodec,
    #[serde(default = "grain")]
    pub fractional_bits: u32,
}
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct IncidentFieldOptions {
    #[serde(
        default,
        skip_serializing_if = "super::IncidentParticipationChart::is_bilinear"
    )]
    pub participation: super::IncidentParticipationChart,
    pub local_roots: usize,
    pub material_seed: u64,
    pub response_aperture: usize,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub response_port_start: Option<usize>,
    #[serde(default)]
    pub material_owners: Vec<usize>,
    #[serde(default = "incident_solve_steps")]
    pub solve_steps: usize,
    #[serde(
        default,
        skip_serializing_if = "super::IncidentFieldSolver::is_richardson"
    )]
    pub solver: super::IncidentFieldSolver,
}
fn incident_solve_steps() -> usize {
    256
}
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct FieldSectionRequest {
    #[serde(default)]
    pub text: String,
    /// Explicit unobserved regions. Null selects the declared zero latent seed, not observed zero.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub partial: Option<Vec<Option<String>>>,
    /// Requested receiving extent; the source can expose fewer positions than this.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub output_symbols: Option<usize>,
    #[serde(default)]
    pub context: Vec<String>,
    /// Complete ordered source/part/cell/contact packet for the incident-field boundary.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub incident_preparation: Option<IncidentPreparation>,
    #[serde(default)]
    pub commit: bool,
    #[serde(default)]
    pub retain_comparison: bool,
}
/// The caller's declared exposure aperture: how much recorded request material may be held at
/// the receiving face, how far the free response extent reaches past it, and how much preceding
/// material may accompany them. Byte caps are exterior presentation boundaries; they are refused
/// against, never silently trimmed, and the symbol counts they bound size the actual section.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ExposureAperture {
    pub request_bytes: usize,
    /// Free receiving positions in declared codec symbols, generated after the held request.
    pub response_symbols: usize,
    #[serde(default)]
    pub context_bytes: usize,
}
impl ExposureAperture {
    /// Bound the declared aperture against the session's own capacity before any recorded
    /// material is read. One presentation byte can supply at most `per_byte` codec symbols.
    fn bounded(&self, spec: &FieldSessionSpec) -> Result<(usize, usize)> {
        let per_byte = usize::from(spec.codec == FieldTextCodec::Utf8Nibbles) + 1;
        let held = self
            .request_bytes
            .checked_mul(per_byte)
            .ok_or_else(|| invalid("declared exposure request aperture"))?;
        let context = self
            .context_bytes
            .checked_mul(per_byte)
            .ok_or_else(|| invalid("declared exposure context aperture"))?;
        // A byte codec receives whole bytes: an extent that splits one can never be observed,
        // because every target text decodes to a multiple of `per_byte` symbols.
        if self.response_symbols % per_byte != 0 {
            return Err(invalid(
                "declared response aperture splits a codec byte; no target text can meet it",
            ));
        }
        if self.response_symbols == 0
            || held
                .checked_add(self.response_symbols)
                .is_none_or(|n| n > spec.section_symbols)
            || context > spec.context_symbols
        {
            return Err(invalid(
                "declared exposure aperture exceeds this session's section/context capacity",
            ));
        }
        Ok((held, context))
    }
}
impl FieldSectionRequest {
    /// Exterior bridge from validated exposure families to a held request with a free receiving
    /// extent. The source role is retained from the recorded occurrence; this bridge does not
    /// invent a universal author-role restriction. Each supplied preceding family must be the
    /// recorded prior parent of the next one. Every frame revalidates against its own manifest
    /// here, because a bridge is a wire.
    /// The records' paths, roles and IDs stay exterior; they never become native amplitudes.
    pub fn from_exposures(
        spec: &FieldSessionSpec,
        aperture: &ExposureAperture,
        manifest: &crate::alpha::exposure::ExposureManifest,
        request: &crate::alpha::exposure::ExposureOccurrence,
        context: &[&crate::alpha::exposure::ExposureOccurrence],
        commit: bool,
        retain_comparison: bool,
    ) -> Result<Self> {
        let (held_cap, context_cap) = aperture.bounded(spec)?;
        let chart = spec.chart()?;
        if !matches!(
            spec.source_chart,
            FieldSourceChart::IncidentField | FieldSourceChart::GeneratorMachine
        ) && request.shared_author_class().map_err(invalid)? != "human"
        {
            return Err(invalid(
                "legacy exposure request requires human-authored source material",
            ));
        }
        let incident_preparation = matches!(
            spec.source_chart,
            FieldSourceChart::IncidentField | FieldSourceChart::GeneratorMachine
        )
        .then(|| IncidentPreparation::from_exposures(spec, aperture, manifest, request, context))
        .transpose()?;
        let text =
            |event: &crate::alpha::exposure::ExposureOccurrence, cap: usize| -> Result<String> {
                event.validate(manifest).map_err(invalid)?;
                let text = event
                    .development_parts()
                    .map_err(invalid)?
                    .iter()
                    .map(|p| {
                        p.text.as_deref().ok_or_else(|| {
                            invalid("this field text codec requires visible textual parts")
                        })
                    })
                    .collect::<Result<Vec<_>>>()?
                    .concat();
                if text.len() > cap {
                    return Err(invalid(
                        "recorded material is longer than the declared exposure aperture",
                    ));
                }
                Ok(text)
            };
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
        let held = spec
            .symbols_of(&chart, &text(request, aperture.request_bytes)?)?
            .into_iter()
            .map(|symbol| Some(spec.symbols[symbol.0 as usize].clone()))
            .collect::<Vec<_>>();
        if held.len() > held_cap {
            return Err(invalid(
                "held request positions exceed the declared exposure aperture",
            ));
        }
        let mut partial = held;
        partial.resize(partial.len() + aperture.response_symbols, None);
        let context = context
            .iter()
            .map(|event| text(event, aperture.context_bytes))
            .collect::<Result<Vec<_>>>()?;
        let preceding = context
            .iter()
            .map(|part| Ok(spec.symbols_of(&chart, part)?.len()))
            .sum::<Result<usize>>()?;
        if preceding > context_cap {
            return Err(invalid(
                "preceding positions exceed the declared exposure aperture",
            ));
        }
        Ok(Self {
            text: String::new(),
            output_symbols: Some(partial.len()),
            partial: Some(partial),
            context,
            incident_preparation,
            commit,
            retain_comparison,
        })
    }
}
impl FieldSessionSpec {
    pub fn response_aperture(&self) -> Result<usize> {
        match self.source_chart {
            FieldSourceChart::IncidentField => self
                .incident
                .as_ref()
                .map(|options| options.response_aperture)
                .ok_or_else(|| invalid("incident material declaration")),
            FieldSourceChart::GeneratorMachine => self
                .generator
                .as_ref()
                .and_then(|options| options.receiver.aperture.checked_sub(1))
                .filter(|n| *n > 0)
                .ok_or_else(|| invalid("generator session declaration")),
            _ => Err(invalid(
                "response aperture requires an incident or generator chart",
            )),
        }
    }

    fn chart(&self) -> Result<SymbolCurrentChart> {
        if self.source_chart != FieldSourceChart::GeneratorMachine && self.generator.is_some() {
            return Err(invalid(
                "generator declaration requires its tagged source chart",
            ));
        }
        if !matches!(
            self.source_chart,
            FieldSourceChart::GeometricRegions | FieldSourceChart::IncidentField
        ) && self.geometry.is_some()
        {
            return Err(invalid(
                "geometric standing requires the geometric source chart",
            ));
        }
        if self.section_symbols == 0 || !(1..=120).contains(&self.fractional_bits) {
            return Err(invalid("field section extent/grain"));
        }
        if self.source_chart == FieldSourceChart::IncidentField {
            let options = self.incident.as_ref().ok_or_else(|| {
                invalid("incident source chart requires its local material declaration")
            })?;
            if self.codec != FieldTextCodec::UnicodeScalars
                || self.geometry.is_none()
                || options.local_roots == 0
                || options.response_aperture == 0
            {
                return Err(invalid(
                    "incident field geometry, Unicode codec, local roots and response aperture are required",
                ));
            }
            if let Some(start) = options.response_port_start {
                if start
                    .checked_add(options.response_aperture)
                    .is_none_or(|end| end > self.section_symbols)
                {
                    return Err(invalid("incident response port binding"));
                }
            }
        } else if self.source_chart == FieldSourceChart::GeneratorMachine {
            let options = self
                .generator
                .as_ref()
                .ok_or_else(|| invalid("generator source chart requires its declaration"))?;
            if self.codec != FieldTextCodec::UnicodeScalars
                || self.geometry.is_some()
                || self.incident.is_some()
                || options.receiver.aperture < 2
            {
                return Err(invalid(
                    "generator chart requires Unicode, no legacy geometry/incident chart, and aperture >= 2",
                ));
            }
            let machine = options.field.machine.compile().map_err(invalid)?;
            options.source.validate_scope(&machine, 0, 1)?;
            if options.field.source_condition_ports != options.source.contact_kinds.len()
                || options
                    .source
                    .contact_kinds
                    .iter()
                    .collect::<std::collections::BTreeSet<_>>()
                    .len()
                    != options.source.contact_kinds.len()
            {
                return Err(invalid("generator source condition declaration"));
            }
            if options.receiver.ports.is_empty()
                || options.receiver.receiver_id.is_empty()
                || options.receiver.termination_receiver_id.is_empty()
                || options.receiver.clock.duration
                    <= num_rational::BigRational::from_integer(0.into())
                || options.receiver.clock.lineage.is_empty()
                || options.receiver.clock.unit.is_empty()
                || options.receiver.ports.iter().any(|port| {
                    !machine
                        .sites()
                        .iter()
                        .any(|s| s.id() == port.site_id && s.is_receiver())
                })
            {
                return Err(invalid(
                    "generator receiver requires declared receiver ports and clock",
                ));
            }
        } else if self.incident.is_some() || self.generator.is_some() {
            return Err(invalid(
                "incident/generator material declaration requires its tagged source chart",
            ));
        }
        if self.codec == FieldTextCodec::Utf8Nibbles
            && (self.symbols.len() != 16
                || !matches!(
                    self.source_chart,
                    FieldSourceChart::SharedRegions | FieldSourceChart::GeometricRegions
                ))
        {
            return Err(invalid(
                "UTF-8 nibble codec requires sixteen declared symbols and shared-regions",
            ));
        }
        if self.source_chart == FieldSourceChart::GeometricRegions {
            self.geometric_extents()?;
        } else if self.source_chart == FieldSourceChart::SharedRegions {
            self.shared_extents()?;
        } else if !self.region_offsets.is_empty() {
            return Err(invalid(
                "region offsets require the shared-regions source chart",
            ));
        }
        for symbol in &self.symbols {
            let valid = match self.codec {
                FieldTextCodec::UnicodeScalars => symbol.chars().count() == 1,
                FieldTextCodec::Utf8Nibbles => !symbol.is_empty(),
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
        if matches!(
            self.source_chart,
            FieldSourceChart::IncidentField | FieldSourceChart::GeneratorMachine
        ) {
            return Err(invalid(
                "incident/generator charts use local machine width and not legacy tensor extents",
            ));
        }
        if self.source_chart == FieldSourceChart::GeometricRegions {
            return self.geometric_extents();
        }
        if self.source_chart == FieldSourceChart::SharedRegions {
            return self.shared_extents();
        }
        let regions = match self.source_chart {
            FieldSourceChart::SharedRegions
            | FieldSourceChart::GeometricRegions
            | FieldSourceChart::IncidentField
            | FieldSourceChart::GeneratorMachine => unreachable!(),
            FieldSourceChart::TensorCondition => self.section_symbols,
            FieldSourceChart::JointRegions => self
                .section_symbols
                .checked_add(self.context_symbols)
                .ok_or_else(|| invalid("joint region extent"))?,
        };
        let complex = regions
            .checked_mul(self.symbols.len())
            .ok_or_else(|| invalid("field section extent"))?;
        let nodes = complex
            .checked_add(2)
            .ok_or_else(|| invalid("field node extent"))?
            / 3;
        let context = match self.source_chart {
            FieldSourceChart::SharedRegions
            | FieldSourceChart::GeometricRegions
            | FieldSourceChart::IncidentField
            | FieldSourceChart::GeneratorMachine => unreachable!(),
            FieldSourceChart::TensorCondition => self
                .symbols
                .len()
                .checked_pow(u32::try_from(self.context_symbols).map_err(invalid)?)
                .ok_or_else(|| invalid("context tensor extent"))?,
            FieldSourceChart::JointRegions => regions
                .checked_mul(2)
                .and_then(|n| n.checked_add(1))
                .ok_or_else(|| invalid("observation port extent"))?,
        };
        let features = nodes
            .checked_mul(3)
            .and_then(|s| s.checked_mul(context)?.checked_add(s)?.checked_add(context))
            .ok_or_else(|| invalid("field reaction feature extent"))?;
        Ok((nodes, context, features))
    }
    fn symbols_of(&self, chart: &SymbolCurrentChart, text: &str) -> Result<Vec<Symbol>> {
        match self.codec {
            FieldTextCodec::Utf8Nibbles => text
                .as_bytes()
                .iter()
                .flat_map(|b| [b >> 4, b & 15])
                .map(|n| {
                    chart
                        .alphabet()
                        .symbol_of(&self.symbols[n as usize])
                        .ok_or_else(|| invalid("nibble outside codec"))
                })
                .collect(),
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

/// Exterior recorded-source aliases and receiver extent for one retained comparison.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct RetainedExposurePairing {
    pub family: crate::alpha::exposure::ExposureFamily,
    pub request_events: Vec<u64>,
    pub response_symbols: usize,
    pub request_text: String,
}

/// A recorded comparison retained at the cut that produced it on the shared-regions chart.
/// That chart's rows are a function of the declared source addresses alone, so these
/// request-level operands re-prepare exactly the producing rows without copying the row law
/// into this wire. The producing epoch travels with them and is reported beside the epoch that
/// actually applies them, because a shared-source update acts at the current material.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct RetainedSharedSource {
    pub request: FieldSectionRequest,
    pub held: Vec<bool>,
    pub output_symbols: usize,
    pub producing_epoch: u64,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub exposure_pairing: Option<RetainedExposurePairing>,
}
fn validate_exposure_pairing(
    pairing: &RetainedExposurePairing,
    retained: &RetainedSharedSource,
    spec: &FieldSessionSpec,
    chart: &SymbolCurrentChart,
) -> Result<()> {
    if pairing.family.provider.is_empty()
        || pairing.family.record_group.is_empty()
        || pairing.request_events.is_empty()
        || pairing.request_events.contains(&0)
        || pairing.request_events.windows(2).any(|p| p[0] >= p[1])
        || pairing.response_symbols == 0
    {
        return Err(invalid("retained exposure pairing coordinates"));
    }
    if matches!(
        spec.source_chart,
        FieldSourceChart::IncidentField | FieldSourceChart::GeneratorMachine
    ) {
        let prepared = IncidentPreparation::from_request(spec, &retained.request)?;
        let recorded = retained
            .request
            .partial
            .as_ref()
            .ok_or_else(|| invalid("incident exposure source parts"))?
            .iter()
            .take_while(|s| s.is_some())
            .map(|s| s.as_ref().unwrap().as_str())
            .collect::<String>();
        let response_aperture = spec.response_aperture()?;
        if spec.source_chart == FieldSourceChart::GeneratorMachine {
            if recorded != pairing.request_text
                || prepared.response_aperture != pairing.response_symbols
                || response_aperture != pairing.response_symbols
                || retained.output_symbols != prepared.request_extent + prepared.response_aperture
            {
                return Err(invalid(
                    "generator retained exposure source/receiver mismatch",
                ));
            }
            return Ok(());
        }
        let options = spec
            .incident
            .as_ref()
            .ok_or_else(|| invalid("incident exposure declaration"))?;
        let geometry = spec
            .geometry
            .as_ref()
            .ok_or_else(|| invalid("incident exposure geometry"))?
            .compile()?;
        let d = options
            .local_roots
            .checked_mul(3)
            .ok_or_else(|| invalid("incident local width"))?;
        let mut mask = vec![
            false;
            geometry
                .rows
                .checked_mul(d)
                .ok_or_else(|| invalid("incident field extent"))?
        ];
        if prepared.source_extent > geometry.slot_rows.len() {
            return Err(invalid("incident source slot extent"));
        }
        for &site in &geometry.slot_rows[..prepared.source_extent] {
            mask[site * d..(site + 1) * d].fill(true);
        }
        if recorded != pairing.request_text
            || prepared.response_aperture != pairing.response_symbols
            || response_aperture != pairing.response_symbols
            || retained.output_symbols != prepared.request_extent + prepared.response_aperture
            || retained.held != mask
        {
            return Err(invalid(
                "incident retained exposure source/receiver mismatch",
            ));
        }
        return Ok(());
    }
    let parts = retained
        .request
        .partial
        .as_ref()
        .ok_or_else(|| invalid("retained exposure request has no held partial"))?;
    let held = parts.iter().take_while(|p| p.is_some()).count();
    if parts.len() != retained.output_symbols
        || parts[held..].iter().any(Option::is_some)
        || retained.output_symbols.checked_sub(held) != Some(pairing.response_symbols)
    {
        return Err(invalid("retained exposure request/response extent"));
    }
    let expected = parts[..held]
        .iter()
        .map(|p| {
            chart
                .alphabet()
                .symbol_of(p.as_ref().unwrap())
                .ok_or_else(|| invalid("retained exposure held symbol is outside its chart"))
        })
        .collect::<Result<Vec<_>>>()?;
    if expected != spec.symbols_of(chart, &pairing.request_text)? {
        return Err(invalid(
            "retained exposure request text disagrees with held symbols",
        ));
    }
    if retained
        .held
        .iter()
        .enumerate()
        .any(|(i, fixed)| *fixed != (i / spec.symbols.len() < held))
    {
        return Err(invalid("retained exposure receiver mask"));
    }
    Ok(())
}

/// One body with a source presentation. Text remains the default API specialization.
pub struct NativeFieldSession<'c, P = FieldTextPresentation> {
    surface: &'c ResidentSurface<'c>,
    body: NativeCoupledBody<'c>,
    presentation: P,
    incident: Option<IncidentPresentation<'c>>,
    generator: Option<GeneratorPresentation<'c>>,
}
/// The existing text/control source and its receiving bookkeeping.
pub struct FieldTextPresentation {
    spec: FieldSessionSpec,
    chart: SymbolCurrentChart,
    compiled_geometry: Option<std::rc::Rc<super::field_geometry::CompiledFieldGeometry>>,
    pending_extents: BTreeMap<u64, usize>,
    retained_shared: BTreeMap<u64, RetainedSharedSource>,
    issued_shared: u64,
    exposure: Option<crate::alpha::exposure::ExposureCursor>,
}
struct PreparedFieldSection<'c> {
    input: ResidentSection<'c>,
    condition: ResidentSection<'c>,
    held: Option<Vec<bool>>,
    output_symbols: usize,
    observed: Option<Vec<bool>>,
}
impl<'c> NativeFieldSession<'c> {
    fn found(surface: &'c ResidentSurface<'c>, spec: &FieldSessionSpec) -> Result<Self> {
        if spec.source_chart == FieldSourceChart::GeneratorMachine {
            return Self::found_generator(surface, spec);
        }
        if spec.source_chart == FieldSourceChart::IncidentField {
            return Self::found_incident(surface, spec);
        }
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
            body,
            incident: None,
            generator: None,
            presentation: FieldTextPresentation {
                compiled_geometry: spec
                    .geometry
                    .as_ref()
                    .map(|g| g.compile().map(std::rc::Rc::new))
                    .transpose()?,
                spec: spec.clone(),
                chart,
                pending_extents: BTreeMap::new(),
                retained_shared: BTreeMap::new(),
                issued_shared: 0,
                exposure: None,
            },
        })
    }
    fn mount_text(&self, text: &str) -> Result<ResidentSection<'c>> {
        let symbols = self
            .presentation
            .spec
            .symbols_of(&self.presentation.chart, text)?;
        if symbols.len() != self.presentation.spec.section_symbols {
            return Err(invalid(format!(
                "requested section has {} symbols; this declared boundary has {}",
                symbols.len(),
                self.presentation.spec.section_symbols
            )));
        }
        self.presentation.chart.mount_joint(
            self.surface,
            &symbols,
            6 * self.presentation.spec.extents()?.0,
        )
    }
    fn mount_context(&self, parts: &[String]) -> Result<ResidentSection<'c>> {
        let symbols = parts
            .iter()
            .map(|s| {
                self.presentation
                    .spec
                    .symbols_of(&self.presentation.chart, s)
            })
            .collect::<Result<Vec<_>>>()?
            .into_iter()
            .flatten()
            .collect::<Vec<_>>();
        if symbols.len() != self.presentation.spec.context_symbols {
            return Err(invalid(format!(
                "context has {} symbols; declared context section has {}",
                symbols.len(),
                self.presentation.spec.context_symbols
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
        let rows = self.presentation.chart.mount(self.surface, &symbols)?;
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
    fn prepare_request(&self, request: &FieldSectionRequest) -> Result<PreparedFieldSection<'c>> {
        if self.presentation.spec.source_chart == FieldSourceChart::TensorCondition {
            if request.partial.is_some()
                || request
                    .output_symbols
                    .is_some_and(|n| n != self.presentation.spec.section_symbols)
            {
                return Err(invalid(
                    "partial/variable regions require the joint-regions source chart",
                ));
            }
            return Ok(PreparedFieldSection {
                input: self.mount_text(&request.text)?,
                condition: self.mount_context(&request.context)?,
                held: None,
                output_symbols: self.presentation.spec.section_symbols,
                observed: None,
            });
        }
        if request.partial.is_some() && !request.text.is_empty() {
            return Err(invalid("supply text or partial regions, not both"));
        }
        let partial = match &request.partial {
            Some(parts) => parts
                .iter()
                .map(|p| match p {
                    None => Ok(None),
                    Some(text) => {
                        let symbols = self
                            .presentation
                            .spec
                            .symbols_of(&self.presentation.chart, text)?;
                        if symbols.len() != 1 {
                            return Err(invalid(
                                "one partial region must name exactly one codec symbol",
                            ));
                        }
                        Ok(Some(symbols[0]))
                    }
                })
                .collect::<Result<Vec<_>>>()?,
            None => self
                .presentation
                .spec
                .symbols_of(&self.presentation.chart, &request.text)?
                .into_iter()
                .map(Some)
                .collect(),
        };
        let output_symbols = request.output_symbols.unwrap_or(partial.len());
        if output_symbols == 0
            || output_symbols > self.presentation.spec.section_symbols
            || partial.len() > self.presentation.spec.section_symbols
        {
            return Err(invalid(
                "request or receiving region exceeds the declared field capacity",
            ));
        }
        let context = request
            .context
            .iter()
            .map(|s| {
                self.presentation
                    .spec
                    .symbols_of(&self.presentation.chart, s)
            })
            .collect::<Result<Vec<_>>>()?
            .into_iter()
            .flatten()
            .collect::<Vec<_>>();
        if context.len() > self.presentation.spec.context_symbols {
            return Err(invalid(
                "context exceeds the declared observed-region capacity",
            ));
        }
        let (nodes, condition_complex, _) = self.presentation.spec.extents()?;
        let width = 6 * nodes;
        let a = self.presentation.spec.symbols.len();
        let regions =
            self.presentation.spec.section_symbols + self.presentation.spec.context_symbols;
        let mut current = vec![(0i64, 0i64); width];
        let mut held = vec![true; width / 2];
        // Presence and observation are separate source maps. An inactive region, an
        // unobserved active region, and an observed numerical zero are distinct charts.
        let mut active = vec![false; regions];
        let mut observed = vec![false; regions];
        for i in 0..self.presentation.spec.section_symbols {
            let value = partial.get(i).copied().flatten();
            if let Some(symbol) = value {
                current[2 * (i * a + self.presentation.chart.coordinates()[symbol.0 as usize])] =
                    (1, 1);
            }
            active[i] = i < output_symbols || i < partial.len();
            observed[i] = value.is_some();
            if i < output_symbols {
                let fixed = request.partial.is_some() && value.is_some();
                held[i * a..(i + 1) * a].fill(fixed);
            }
        }
        for (j, symbol) in context.iter().enumerate() {
            let i = self.presentation.spec.section_symbols + j;
            current[2 * (i * a + self.presentation.chart.coordinates()[symbol.0 as usize])] =
                (1, 1);
            active[i] = true;
            observed[i] = true;
        }
        let mut condition = vec![(0i64, 0i64); 2 * condition_complex + 1];
        condition[0] = (1, 1);
        for i in 0..regions {
            let a = i64::from(active[i]);
            let k = i64::from(observed[i]);
            condition[2 * (i + 1)] = (a, a);
            condition[2 * (regions + i + 1)] = (k, k);
        }
        *condition.last_mut().unwrap() = (1, 1);
        let input = self
            .surface
            .mount_section_rest(
                &ResidentSectionRest::found(1, width, ResidentGrain(0), 64, current)
                    .map_err(invalid)?,
            )
            .map_err(invalid)?;
        let condition = self
            .surface
            .mount_section_rest(
                &ResidentSectionRest::found(1, condition.len(), ResidentGrain(0), 64, condition)
                    .map_err(invalid)?,
            )
            .map_err(invalid)?;
        Ok(PreparedFieldSection {
            input,
            condition,
            held: Some(held),
            output_symbols,
            observed: Some(observed),
        })
    }
    pub fn request(&mut self, request: &FieldSectionRequest) -> Result<Value> {
        if self.presentation.spec.source_chart == FieldSourceChart::GeneratorMachine {
            return self.generator_request(request);
        }
        if self.presentation.spec.source_chart == FieldSourceChart::IncidentField {
            return self.incident_request(request);
        }
        if self.presentation.spec.source_chart == FieldSourceChart::GeometricRegions {
            return self.geometric_request(request);
        }
        if self.presentation.spec.source_chart == FieldSourceChart::SharedRegions {
            return self.shared_request(request);
        }
        if request.retain_comparison && !request.commit {
            return Err(invalid(
                "a retained target requires committed field generation",
            ));
        }
        let start = Instant::now();
        let prepared = self.prepare_request(request)?;
        let chart = self.presentation.chart.receiver(self.surface)?;
        let generation = Instant::now();
        let input = ResidentConstitutiveCurrent::integers(&prepared.input)?;
        let condition = ResidentConstitutiveCurrent::rational(&prepared.condition)?;
        let produced = if let Some(held) = &prepared.held {
            self.body.generate_received_field(
                input.into(),
                condition,
                held,
                request.commit,
                request.retain_comparison,
            )?
        } else if request.commit {
            self.body
                .generate_field(input.into(), condition, request.retain_comparison)?
        } else {
            self.body.preview_field(input.into(), condition)?
        };
        if let Some(id) = produced.comparison_id() {
            self.presentation
                .pending_extents
                .insert(id, prepared.output_symbols);
        }
        let generation_us = generation.elapsed().as_micros();
        let receive = || -> Result<_> {
            let selected = produced
                .received_output()
                .restrict(0..2 * prepared.output_symbols * self.presentation.spec.symbols.len())?;
            let face = selected
                .view()
                .read_basis_sections(&chart, prepared.output_symbols)?;
            Ok(face.selections()?)
        };
        let selections = match receive() {
            Ok(value) => value,
            Err(error) if request.commit => {
                return Ok(
                    json!({"schema":"org.holonics.hna.field-section.v1", "status":"committed-receiver-refused", "committed":true,
                "comparison":produced.comparison_id(),"producing_epoch":produced.producing_epoch(),"error":error.to_string(),"anatomy":self.inspect()}),
                );
            }
            Err(error) => return Err(error),
        };
        let pieces = selections
            .iter()
            .map(|v| {
                self.presentation
                    .spec
                    .symbols
                    .get(v.selected)
                    .cloned()
                    .ok_or_else(|| invalid("selected symbol outside codec"))
            })
            .collect::<Result<Vec<_>>>()?;
        let text = pieces.join(match self.presentation.spec.codec {
            FieldTextCodec::Utf8Nibbles => unreachable!(),
            FieldTextCodec::UnicodeScalars => "",
            FieldTextCodec::WhitespaceWords => " ",
        });
        Ok(
            json!({"schema":"org.holonics.hna.field-section.v1","text":text,"symbols":pieces,
            "comparison":produced.comparison_id(),"producing_epoch":produced.producing_epoch(),"committed":request.commit,
            "selections":selections,"output_symbols":prepared.output_symbols,"observed_regions":prepared.observed,
            "latent_seed":"zero on explicitly unobserved regions","generated":produced.inspect()?,"generation_us":generation_us,"elapsed_us":start.elapsed().as_micros(),
            "scope":"joint complete section; native incoming reaction and constituted scattering; declared exterior symbol codec"}),
        )
    }
    pub fn observe(&mut self, source: u64, text: &str, step_bits: u32) -> Result<Value> {
        if self.presentation.spec.source_chart == FieldSourceChart::GeneratorMachine {
            return self.generator_observe(source, text, step_bits);
        }
        if self.presentation.spec.source_chart == FieldSourceChart::IncidentField {
            return self.incident_observe(source, text, step_bits);
        }
        if self.presentation.spec.source_chart == FieldSourceChart::GeometricRegions {
            return self.observe_retained_geometric(source, text, step_bits);
        }
        if self.presentation.spec.source_chart == FieldSourceChart::SharedRegions {
            return self.observe_retained_source(source, text, step_bits);
        }
        let start = Instant::now();
        let target = if self.presentation.spec.source_chart == FieldSourceChart::JointRegions {
            let expected = *self
                .presentation
                .pending_extents
                .get(&source)
                .ok_or_else(|| invalid("unknown field response extent"))?;
            let symbols = self
                .presentation
                .spec
                .symbols_of(&self.presentation.chart, text)?;
            if symbols.len() != expected {
                return Err(invalid(
                    "target does not match its producing response extent",
                ));
            }
            self.presentation.chart.mount_joint(
                self.surface,
                &symbols,
                2 * self.presentation.spec.symbols.len() * expected,
            )?
        } else {
            self.mount_text(text)?
        };
        let returned = self.body.observe_field(
            source,
            ResidentConstitutiveCurrent::integers(&target)?.into(),
            step_bits,
        )?;
        self.presentation.pending_extents.remove(&source);
        Ok(
            json!({"source":source,"target":text,"returned":returned,"elapsed_us":start.elapsed().as_micros(),"anatomy":self.inspect()}),
        )
    }
    pub fn release(&mut self, source: u64) -> Result<Value> {
        if let Some(generator) = &mut self.generator {
            if !generator.pending.contains_key(&source) {
                return Err(invalid("unknown generator comparison"));
            }
            self.body.release(source)?;
            generator.pending.remove(&source);
            self.presentation.retained_shared.remove(&source);
            return Ok(json!({"released":source,"anatomy":self.inspect()}));
        }
        if let Some(incident) = &mut self.incident {
            if !incident.pending.contains_key(&source) {
                return Err(invalid("unknown incident comparison"));
            }
            self.body.release(source)?;
            incident.pending.remove(&source);
            self.presentation.retained_shared.remove(&source);
            return Ok(json!({"released":source,"anatomy":self.inspect()}));
        }
        if matches!(
            self.presentation.spec.source_chart,
            FieldSourceChart::SharedRegions | FieldSourceChart::GeometricRegions
        ) {
            self.presentation
                .retained_shared
                .remove(&source)
                .ok_or_else(|| invalid("unknown retained shared-source comparison"))?;
            return Ok(json!({"released":source,"anatomy":self.inspect()}));
        }
        self.body.release(source)?;
        self.presentation.pending_extents.remove(&source);
        Ok(json!({"released":source,"anatomy":self.inspect()}))
    }
    pub fn inspect(&self) -> Value {
        json!({"kind":"constituted-field-session","epoch":self.body.epoch(),"pending":self.body.pending_coupled_predictions(),"pending_comparisons":self.body.pending_ids().ok(),
        "retained_shared":self.presentation.retained_shared.keys().collect::<Vec<_>>(),"spec":self.presentation.spec,"census":self.surface.census()})
    }
    /// The cold exposure position this session's trained state has actually consumed. AC3: it
    /// is published inside the same atomic checkpoint file as the model, never beside it. The
    /// cursor still names a frame the reader has not acknowledged; that is the resumable case.
    pub fn attach_exposure_cursor(&mut self, cursor: crate::alpha::exposure::ExposureCursor) {
        self.presentation.exposure = Some(cursor);
    }
    pub fn exposure_cursor(&self) -> Option<&crate::alpha::exposure::ExposureCursor> {
        self.presentation.exposure.as_ref()
    }
    pub fn retained_shared_comparisons(&self) -> Vec<u64> {
        self.presentation.retained_shared.keys().copied().collect()
    }
    pub fn attach_exposure_pairing(
        &mut self,
        comparison: u64,
        family: crate::alpha::exposure::ExposureFamily,
        mut request_events: Vec<u64>,
        request_text: String,
    ) -> Result<()> {
        request_events.sort_unstable();
        request_events.dedup();
        let retained = self
            .presentation
            .retained_shared
            .get(&comparison)
            .ok_or_else(|| invalid("unknown retained shared-source comparison"))?;
        if retained.exposure_pairing.is_some() {
            return Err(invalid("retained exposure pairing is already attached"));
        }
        let held = retained
            .request
            .partial
            .as_ref()
            .ok_or_else(|| invalid("retained exposure request has no held partial"))?
            .iter()
            .take_while(|part| part.is_some())
            .count();
        let pairing = RetainedExposurePairing {
            family,
            request_events,
            request_text,
            response_symbols: retained
                .output_symbols
                .checked_sub(held)
                .ok_or_else(|| invalid("retained exposure response extent"))?,
        };
        validate_exposure_pairing(
            &pairing,
            retained,
            &self.presentation.spec,
            &self.presentation.chart,
        )?;
        self.presentation
            .retained_shared
            .get_mut(&comparison)
            .unwrap()
            .exposure_pairing = Some(pairing);
        Ok(())
    }
    pub fn retained_exposure_pairings(&self) -> Vec<(u64, RetainedExposurePairing)> {
        self.presentation
            .retained_shared
            .iter()
            .filter_map(|(id, retained)| {
                retained
                    .exposure_pairing
                    .clone()
                    .map(|pairing| (*id, pairing))
            })
            .collect()
    }
    pub fn spec(&self) -> &FieldSessionSpec {
        &self.presentation.spec
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
            spec: self.presentation.spec.clone(),
            state: state.clone(),
            body: rest,
            pending_extents: self.presentation.pending_extents.clone(),
            retained_shared: self.presentation.retained_shared.clone(),
            issued_shared: self.presentation.issued_shared,
            exposure: self.presentation.exposure.clone(),
            incident: self.incident.as_ref().map(|i| i.rest()).transpose()?,
            generator: self.generator.as_ref().map(|g| g.rest()).transpose()?,
        };
        let mut bytes = Vec::new();
        saved.write(&mut bytes)?;
        Ok(publish_new(path, |out| out.write_all(&bytes))?)
    }
}
const MAGIC: &[u8] = b"HNA-FIELD-SESSION\x01";
const REGIONS_MAGIC: &[u8] = b"HNA-FIELD-SESSION\x02";
/// Version 3 adds the retained shared-source comparisons and the exposure cursor. Versions 1
/// and 2 stay readable: their tuple headers simply carry neither.
const SOURCE_MAGIC: &[u8] = b"HNA-FIELD-SESSION\x03";
const INCIDENT_MAGIC: &[u8] = b"HNA-FIELD-SESSION\x04";
const GENERATOR_MAGIC: &[u8] = b"HNA-FIELD-SESSION\x05";
#[derive(Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct FieldSessionHeader {
    spec: FieldSessionSpec,
    state: HnaStreamState,
    pending_extents: BTreeMap<u64, usize>,
    #[serde(default, skip_serializing_if = "BTreeMap::is_empty")]
    retained_shared: BTreeMap<u64, RetainedSharedSource>,
    #[serde(default)]
    issued_shared: u64,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    exposure: Option<crate::alpha::exposure::ExposureCursor>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    incident: Option<IncidentPresentationRest>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    generator: Option<GeneratorPresentationRest>,
}
pub struct NativeFieldSavedSession {
    spec: FieldSessionSpec,
    state: HnaStreamState,
    body: SavedCoupledBody,
    pending_extents: BTreeMap<u64, usize>,
    retained_shared: BTreeMap<u64, RetainedSharedSource>,
    issued_shared: u64,
    exposure: Option<crate::alpha::exposure::ExposureCursor>,
    incident: Option<IncidentPresentationRest>,
    generator: Option<GeneratorPresentationRest>,
}
impl NativeFieldSavedSession {
    fn write(&self, out: &mut impl Write) -> Result<()> {
        let header = serde_json::to_vec(&FieldSessionHeader {
            spec: self.spec.clone(),
            state: self.state.clone(),
            pending_extents: self.pending_extents.clone(),
            retained_shared: self.retained_shared.clone(),
            issued_shared: self.issued_shared,
            exposure: self.exposure.clone(),
            incident: self.incident.clone(),
            generator: self.generator.clone(),
        })?;
        let mut body = Vec::new();
        self.body.write(&mut body)?;
        out.write_all(if self.generator.is_some() {
            GENERATOR_MAGIC
        } else if self.incident.is_some() {
            INCIDENT_MAGIC
        } else {
            SOURCE_MAGIC
        })?;
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
        let incident_wire = magic == INCIDENT_MAGIC;
        let generator_wire = magic == GENERATOR_MAGIC;
        let sources = magic == SOURCE_MAGIC || incident_wire || generator_wire;
        let regions = magic == REGIONS_MAGIC;
        if magic != MAGIC && !regions && !sources {
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
        let header = blob(&mut input)?;
        let header: FieldSessionHeader = if sources {
            serde_json::from_slice(&header)?
        } else {
            let (spec, state, pending_extents) = if regions {
                serde_json::from_slice(&header)?
            } else {
                let (spec, state): (FieldSessionSpec, HnaStreamState) =
                    serde_json::from_slice(&header)?;
                (spec, state, BTreeMap::new())
            };
            FieldSessionHeader {
                spec,
                state,
                pending_extents,
                retained_shared: BTreeMap::new(),
                issued_shared: 0,
                exposure: None,
                incident: None,
                generator: None,
            }
        };
        let FieldSessionHeader {
            spec,
            state,
            pending_extents,
            retained_shared,
            issued_shared,
            exposure,
            incident,
            generator,
        } = header;
        let incident_mode = spec.source_chart == FieldSourceChart::IncidentField;
        let generator_mode = spec.source_chart == FieldSourceChart::GeneratorMachine;
        if incident_mode != incident_wire
            || incident_mode != incident.is_some()
            || generator_mode != generator_wire
            || generator_mode != generator.is_some()
        {
            return Err(invalid("incident session wire chart"));
        }
        let chart = spec.chart()?;
        state.validate().map_err(invalid)?;
        // A remounted wire re-checks its own operands. The rows themselves are rebuilt from the
        // retained request at application; only its declared extents can be checked here.
        if !incident_mode
            && !generator_mode
            && (retained_shared.iter().any(|(id, retained)| {
                *id >= issued_shared
                    || retained.request.commit
                    || !retained.request.retain_comparison
                    || retained.output_symbols == 0
                    || retained.output_symbols > spec.section_symbols
                    || Some(retained.held.len())
                        != retained.output_symbols.checked_mul(spec.symbols.len())
                    || retained.held.iter().all(|fixed| *fixed)
            }) || (!retained_shared.is_empty()
                && !matches!(
                    spec.source_chart,
                    FieldSourceChart::SharedRegions | FieldSourceChart::GeometricRegions
                )))
        {
            return Err(invalid("retained shared-source comparison operands"));
        }
        for retained in retained_shared.values() {
            if let Some(pairing) = &retained.exposure_pairing {
                validate_exposure_pairing(pairing, retained, &spec, &chart)?;
            }
        }
        if exposure
            .as_ref()
            .is_some_and(|cursor| cursor.byte_offset > cursor.source.octets)
        {
            return Err(invalid(
                "saved exposure cursor is outside its pinned source",
            ));
        }
        let bytes = blob(&mut input)?;
        let body = SavedCoupledBody::read(&mut bytes.as_slice(), bytes.len() as u64)?;
        let body_matches = if generator_mode {
            matches!(body, SavedCoupledBody::Incident(_))
                && Some(body.roots())
                    == spec
                        .generator
                        .as_ref()
                        .unwrap()
                        .field
                        .machine
                        .sites()
                        .len()
                        .checked_mul(2)
        } else if incident_mode {
            let geometry = spec
                .geometry
                .as_ref()
                .ok_or_else(|| invalid("incident rest geometry"))?
                .compile()?;
            matches!(body, SavedCoupledBody::Incident(_))
                && Some(body.roots())
                    == geometry
                        .rows
                        .checked_mul(spec.incident.as_ref().unwrap().local_roots)
        } else {
            matches!(body, SavedCoupledBody::Field(_)) && body.roots() == spec.extents()?.0
        };
        if !body_matches || input.limit() != 0 {
            return Err(invalid("field session body/configuration mismatch"));
        }
        if pending_extents
            .iter()
            .any(|(id, n)| *n == 0 || *n > spec.section_symbols || !body.has_prediction(*id))
        {
            return Err(invalid("field session pending receiver extent"));
        }
        Ok(Self {
            spec,
            state,
            body,
            pending_extents,
            retained_shared,
            issued_shared,
            exposure,
            incident,
            generator,
        })
    }
    pub fn exposure_cursor(&self) -> Option<&crate::alpha::exposure::ExposureCursor> {
        self.exposure.as_ref()
    }
    pub fn with_session<T>(
        self,
        f: impl FnOnce(&mut NativeFieldSession<'_>, &mut HnaStream) -> Result<T>,
    ) -> Result<T> {
        let readout = ResidentReadout::new().map_err(invalid)?;
        let surface = ResidentSurface::on(&readout).map_err(invalid)?;
        let chart = self.spec.chart()?;
        let body = self.body.remount(&surface)?;
        let incident = self
            .incident
            .map(|i| i.remount(&surface, &self.spec, &body))
            .transpose()?;
        let generator = self
            .generator
            .map(|g| g.remount(&surface, &self.spec, &body))
            .transpose()?;
        let mut session = NativeFieldSession {
            surface: &surface,
            body,
            incident,
            generator,
            presentation: FieldTextPresentation {
                compiled_geometry: self
                    .spec
                    .geometry
                    .as_ref()
                    .map(|g| g.compile().map(std::rc::Rc::new))
                    .transpose()?,
                spec: self.spec,
                chart,
                pending_extents: self.pending_extents,
                retained_shared: self.retained_shared,
                issued_shared: self.issued_shared,
                exposure: self.exposure,
            },
        };
        if !matches!(
            session.presentation.spec.source_chart,
            FieldSourceChart::IncidentField | FieldSourceChart::GeneratorMachine
        ) {
            let (nodes, context, _) = session.presentation.spec.extents()?;
            if session.body.field_dimensions()?
                != (
                    6 * nodes,
                    2 * context,
                    ResidentGrain(session.presentation.spec.fractional_bits),
                    NativeFieldReactionPort::IncomingBoundary,
                )
            {
                return Err(invalid(
                    "saved session model ports/grain do not match its declared codec",
                ));
            }
            for id in session.body.pending_ids()? {
                // Only the legacy tensor-condition chart receives its whole declared section, so
                // only it can back-fill a missing extent. A variable-extent chart must refuse;
                // the shared chart's section capacity is a source aperture, not a response length.
                if !session.presentation.pending_extents.contains_key(&id) {
                    if session.presentation.spec.source_chart != FieldSourceChart::TensorCondition {
                        return Err(invalid("missing pending field receiving extent"));
                    }
                    session
                        .presentation
                        .pending_extents
                        .insert(id, session.presentation.spec.section_symbols);
                }
            }
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
            region_offsets: vec![],
            source_chart: FieldSourceChart::TensorCondition,
            geometry: None,
            incident: None,
            generator: None,
            codec: FieldTextCodec::UnicodeScalars,
            fractional_bits: 48,
        };
        let make = |text: &str| FieldSectionRequest {
            text: text.into(),
            partial: None,
            output_symbols: None,
            context: vec![],
            incident_preparation: None,
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
            assert!(
                s.observe(b["comparison"].as_u64().unwrap(), "c", 3)
                    .is_err()
            );
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
            region_offsets: vec![],
            source_chart: FieldSourceChart::TensorCondition,
            geometry: None,
            incident: None,
            generator: None,
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
            region_offsets: vec![],
            source_chart: FieldSourceChart::TensorCondition,
            geometry: None,
            incident: None,
            generator: None,
            codec: FieldTextCodec::UnicodeScalars,
            fractional_bits: 48,
        };
        let request = crate::HnaStreamRequest {
            schema: crate::HNA_STREAM_REQUEST_SCHEMA.into(),
            command: crate::HnaStreamCommand::FieldRequest {
                request: FieldSectionRequest {
                    text: "a".into(),
                    partial: None,
                    output_symbols: None,
                    context: vec![],
                    incident_preparation: None,
                    commit: true,
                    retain_comparison: true,
                },
            },
        };
        let mut line = serde_json::to_vec(&request).unwrap();
        line.push(b'\n');
        let epoch = with_field_session(&spec, |s| {
            let mut stream = HnaStream::new();
            assert!(
                stream
                    .pump_field(s, &mut std::io::Cursor::new(&line), &mut Refuse)
                    .is_err()
            );
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
    use crate::alpha::exposure::{EXPOSURE_SCHEMA, ExposureManifest, ExposureOccurrence};
    fn manifest() -> ExposureManifest {
        serde_json::from_value(json!({"schema":EXPOSURE_SCHEMA,"kind":"manifest",
            "temporal_cut":"2026-09-04T00:00:00Z","temporal_cut_normalized":"2026-09-04T00:00:00.000000+00:00",
            "private_sources":[{"source":1,"provider":"codex","private_path":"private/source.jsonl","captured_octets":10000,"records":100}],
            "visible_parts":{},"boundary":{}}))
        .unwrap()
    }
    fn event(
        sequence: u64,
        name: &str,
        role: &str,
        parent: Option<&str>,
        text: &str,
    ) -> ExposureOccurrence {
        let kind = if role == "human" {
            "human-text"
        } else {
            "agent-text"
        };
        serde_json::from_value(json!({"schema":EXPOSURE_SCHEMA,"kind":"occurrence-family","sequence":sequence,
            "position":{"first_source":1,"first_record":sequence+1,"first_event":sequence+1},
            "family":{"provider":"codex","record_group":format!("declared:{name}")},
            "partition":"development","partition_reasons":[],"conflicts":[],"views":[{"event":sequence+1,"source":1,"provider":"codex",
                "record":{"number":sequence+1,"byte_start":sequence*100,"byte_end":(sequence+1)*100},
                "normalized_timestamp":format!("2026-09-0{}T00:00:00.000000+00:00",sequence+1),
                "native_id":name,"author_class":role,"record_kind":"message","flags":[],"provider_metadata":{},
                "visible_parts":[{"ordinal":0,"pointer":"/text","kind":kind,"text":text}],"nonvisible_part_references":[],
                "links":parent.map(|p|vec![json!({"kind":"provider-parent","evidence":"declared test source relationship","availability":"prior","target_event":sequence,
                    "target":{"event":sequence,"source":1,"provider":"codex","record_group":format!("declared:{p}"),
                        "normalized_timestamp":format!("2026-09-0{sequence}T00:00:00.000000+00:00")}})]).unwrap_or_default()}]})).unwrap()
    }
    fn spec() -> FieldSessionSpec {
        FieldSessionSpec {
            symbols: (0..16).map(|n| format!("{n:x}")).collect(),
            section_symbols: 64,
            context_symbols: 16,
            region_offsets: vec![-2, -1, 0, 1, 2],
            source_chart: FieldSourceChart::SharedRegions,
            geometry: None,
            incident: None,
            generator: None,
            codec: FieldTextCodec::Utf8Nibbles,
            fractional_bits: 48,
        }
    }

    #[test]
    fn retained_exposure_pairing_roundtrips_and_legacy_payload_defaults() {
        let request = FieldSectionRequest {
            text: String::new(),
            partial: Some(vec![Some("0".into()), None]),
            output_symbols: Some(2),
            context: Vec::new(),
            incident_preparation: None,
            commit: false,
            retain_comparison: true,
        };
        let retained = RetainedSharedSource {
            request,
            held: vec![true, false],
            output_symbols: 2,
            producing_epoch: 7,
            exposure_pairing: Some(RetainedExposurePairing {
                family: crate::alpha::exposure::ExposureFamily {
                    provider: "codex".into(),
                    record_group: "declared:request".into(),
                },
                request_events: vec![11, 12],
                response_symbols: 1,
                request_text: "source".into(),
            }),
        };
        let wire = serde_json::to_value(&retained).unwrap();
        let roundtrip: RetainedSharedSource = serde_json::from_value(wire.clone()).unwrap();
        assert_eq!(roundtrip, retained);
        let mut legacy = wire.as_object().unwrap().clone();
        legacy.remove("exposure_pairing");
        let restored: RetainedSharedSource = serde_json::from_value(Value::Object(legacy)).unwrap();
        assert!(restored.exposure_pairing.is_none());
    }
    #[test]
    fn saved_pairing_validates_its_original_receiver_and_source_text() {
        let spec = spec();
        let chart = spec.chart().unwrap();
        let retained = RetainedSharedSource {
            request: FieldSectionRequest {
                text: String::new(),
                partial: Some(vec![Some("6".into()), Some("1".into()), None, None]),
                output_symbols: Some(4),
                context: vec![],
                incident_preparation: None,
                commit: false,
                retain_comparison: true,
            },
            held: (0..64).map(|i| i < 32).collect(),
            output_symbols: 4,
            producing_epoch: 0,
            exposure_pairing: None,
        };
        let pairing = RetainedExposurePairing {
            family: crate::alpha::exposure::ExposureFamily {
                provider: "codex".into(),
                record_group: "request".into(),
            },
            request_events: vec![1, 3],
            response_symbols: 2,
            request_text: "a".into(),
        };
        assert!(validate_exposure_pairing(&pairing, &retained, &spec, &chart).is_ok());
        let mut changed = pairing.clone();
        changed.request_text = "b".into();
        assert!(validate_exposure_pairing(&changed, &retained, &spec, &chart).is_err());
        changed = pairing.clone();
        changed.response_symbols = 4;
        assert!(validate_exposure_pairing(&changed, &retained, &spec, &chart).is_err());
        changed = pairing.clone();
        changed.request_events = vec![1, 1];
        assert!(validate_exposure_pairing(&changed, &retained, &spec, &chart).is_err());
        let mut changed = retained.clone();
        changed.request.partial.as_mut().unwrap().swap(1, 2);
        assert!(validate_exposure_pairing(&pairing, &changed, &spec, &chart).is_err());
        let mut changed = retained;
        changed.held[0] = false;
        assert!(validate_exposure_pairing(&pairing, &changed, &spec, &chart).is_err());
    }

    fn aperture() -> ExposureAperture {
        ExposureAperture {
            request_bytes: 8,
            response_symbols: 6,
            context_bytes: 4,
        }
    }
    #[test]
    fn a_response_aperture_that_splits_a_codec_byte_is_refused_before_any_material() {
        // Two nibbles per byte: no target text has an odd symbol count, so an odd free extent
        // could be retained and never observed.
        let odd = ExposureAperture {
            response_symbols: 5,
            ..aperture()
        };
        assert!(odd.bounded(&spec()).is_err());
        assert!(aperture().bounded(&spec()).is_ok());
    }
    #[test]
    fn exposure_bridge_holds_the_request_and_leaves_its_response_extent_free() {
        let before = event(0, "before", "human", None, "ab");
        let request = event(1, "request", "human", Some("before"), "cd");
        let prepared = FieldSectionRequest::from_exposures(
            &spec(),
            &aperture(),
            &manifest(),
            &request,
            &[&before],
            false,
            true,
        )
        .unwrap();
        // Four held request nibbles, then exactly the declared free receiving extent.
        assert_eq!(prepared.text, "");
        assert_eq!(prepared.output_symbols, Some(10));
        assert_eq!(
            prepared.partial.unwrap(),
            [
                Some("6".into()),
                Some("3".into()),
                Some("6".into()),
                Some("4".into()),
                None,
                None,
                None,
                None,
                None,
                None
            ]
        );
        assert_eq!(prepared.context, ["ab"]);
        let bridge = |request: &ExposureOccurrence, context: &[&ExposureOccurrence]| {
            FieldSectionRequest::from_exposures(
                &spec(),
                &aperture(),
                &manifest(),
                request,
                context,
                false,
                true,
            )
        };
        let other = event(0, "unrelated", "human", None, "ab");
        assert!(bridge(&request, &[&other]).is_err());
        let future = event(2, "before", "human", None, "ab");
        assert!(bridge(&request, &[&future]).is_err());
        assert!(bridge(&event(1, "long", "human", None, "123456789"), &[]).is_err());
        assert!(bridge(&event(1, "agent", "agent-visible", None, "cd"), &[]).is_err());
        let mut evaluation = event(1, "later", "human", None, "cd");
        evaluation.partition = crate::alpha::exposure::ExposurePartition::Evaluation;
        assert!(bridge(&evaluation, &[]).is_err());
        let mut deferred = event(1, "held", "human", None, "cd");
        deferred.partition = crate::alpha::exposure::ExposurePartition::Deferred;
        deferred.partition_reasons = vec!["conflicting captured times".into()];
        assert!(bridge(&deferred, &[]).is_err());
        let mut unvalidated = event(1, "request", "human", None, "cd");
        unvalidated.views[0].record.byte_end = 0;
        assert!(bridge(&unvalidated, &[]).is_err());
    }
    #[test]
    #[ignore = "requires CUDA; the cold exposure position and the state that consumed it are published in one file"]
    fn exposure_cursor_and_trained_state_reopen_together() {
        let dir = tempfile::tempdir().unwrap();
        let wire = dir.path().join("exposure.jsonl");
        let mut bytes = serde_json::to_vec(&manifest()).unwrap();
        bytes.push(b'\n');
        for frame in [
            event(0, "request", "human", None, "cd"),
            event(1, "reply", "agent-visible", None, "ef"),
        ] {
            bytes.extend(serde_json::to_vec(&frame).unwrap());
            bytes.push(b'\n');
        }
        std::fs::write(&wire, bytes).unwrap();
        let pending = dir.path().join("pending.session");
        let mut reader = crate::alpha::exposure::ExposureReader::open(&wire).unwrap();
        let frame = reader.peek().unwrap().unwrap().clone();
        let request = FieldSectionRequest::from_exposures(
            &spec(),
            &aperture(),
            reader.manifest(),
            &frame,
            &[],
            false,
            true,
        )
        .unwrap();
        with_field_session(&spec(), |s| {
            assert_eq!(s.request(&request)?["comparison"], 0);
            // The frame is not acknowledged, so the published cursor still names it.
            s.attach_exposure_cursor(reader.cursor());
            s.checkpoint(&pending, &HnaStreamState::default())?;
            Ok(())
        })
        .unwrap();
        let saved = NativeFieldSavedSession::open(&pending).unwrap();
        let cursor = saved.exposure_cursor().cloned().unwrap();
        assert_eq!(cursor.next_sequence, 0);
        let continued = dir.path().join("continued.session");
        saved
            .with_session(|s, _| {
                assert_eq!(s.exposure_cursor(), Some(&cursor));
                let mut resumed =
                    crate::alpha::exposure::ExposureReader::resume(cursor).map_err(invalid)?;
                assert_eq!(resumed.peek().map_err(invalid)?.unwrap().sequence, 0);
                s.observe(0, "cdefg", 1)?;
                resumed.acknowledge(0).map_err(invalid)?;
                s.attach_exposure_cursor(resumed.cursor());
                s.checkpoint(&continued, &HnaStreamState::default())
            })
            .unwrap();
        let saved = NativeFieldSavedSession::open(&continued).unwrap();
        let cursor = saved.exposure_cursor().cloned().unwrap();
        assert_eq!(cursor.next_sequence, 1);
        saved
            .with_session(|s, _| {
                assert!(s.retained_shared_comparisons().is_empty());
                assert_eq!(
                    crate::alpha::exposure::ExposureReader::resume(cursor)
                        .map_err(invalid)?
                        .peek()
                        .map_err(invalid)?
                        .unwrap()
                        .sequence,
                    1
                );
                Ok(())
            })
            .unwrap();
    }
    #[test]
    fn declared_exposure_aperture_is_bounded_before_it_sizes_a_section() {
        let spec = spec();
        assert_eq!(aperture().bounded(&spec).unwrap(), (16, 8));
        for refused in [
            ExposureAperture {
                response_symbols: 0,
                ..aperture()
            },
            ExposureAperture {
                request_bytes: 32,
                ..aperture()
            },
            ExposureAperture {
                context_bytes: 9,
                ..aperture()
            },
            ExposureAperture {
                request_bytes: usize::MAX,
                ..aperture()
            },
        ] {
            assert!(refused.bounded(&spec).is_err());
        }
    }
}

#[cfg(test)]
mod joint_region_tests {
    use super::*;
    fn spec() -> FieldSessionSpec {
        FieldSessionSpec {
            symbols: vec!["a".into(), "b".into(), "c".into()],
            section_symbols: 2,
            context_symbols: 1,
            region_offsets: vec![],
            source_chart: FieldSourceChart::JointRegions,
            geometry: None,
            incident: None,
            generator: None,
            codec: FieldTextCodec::UnicodeScalars,
            fractional_bits: 48,
        }
    }
    fn request(parts: Vec<Option<&str>>, context: &str) -> FieldSectionRequest {
        FieldSectionRequest {
            text: String::new(),
            partial: Some(parts.into_iter().map(|s| s.map(str::to_owned)).collect()),
            output_symbols: None,
            context: vec![context.into()],
            incident_preparation: None,
            commit: true,
            retain_comparison: true,
        }
    }
    #[test]
    fn region_extents_grow_with_regions_and_retain_legacy_chart() {
        let mut spec = spec();
        assert_eq!(spec.extents().unwrap(), (3, 7, 79));
        spec.context_symbols = 10;
        assert_eq!(spec.extents().unwrap(), (12, 25, 961));
    }
    #[test]
    #[ignore = "requires CUDA; active, observed and held are distinct region maps"]
    fn joint_source_distinguishes_unknown_from_inactive_and_context() {
        with_field_session(&spec(), |s| {
            let p = s.prepare_request(&request(vec![None], "b"))?;
            let h = s.surface.read_out(&p.condition).map_err(invalid)?;
            // bias; active(query0,query1,context0); observed(query0,query1,context0); denominator
            assert_eq!(
                h.iter().map(|v| v.0).collect::<Vec<_>>(),
                [1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1]
            );
            assert_eq!(
                p.held.unwrap(),
                [false, false, false, true, true, true, true, true, true]
            );
            let x = s.surface.read_out(&p.input).map_err(invalid)?;
            assert_eq!(x[14], (1, 1)); // b in the context region, not a context identifier.
            assert_eq!(p.output_symbols, 1);
            Ok(())
        })
        .unwrap();
    }
    #[test]
    #[ignore = "requires CUDA; receiver mask and variable target extent survive a delayed comparison"]
    fn partial_receiver_reopens_after_intervening_material_update() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("partial.session");
        let expected = with_field_session(&spec(), |s| {
            let a = s.request(&request(vec![Some("a"), None], "b"))?;
            assert!(a["text"].as_str().unwrap().starts_with('a'));
            let b = s.request(&request(vec![None], "c"))?;
            s.observe(a["comparison"].as_u64().unwrap(), "ab", 1)?;
            s.checkpoint(&path, &HnaStreamState::default())?;
            assert!(
                s.observe(b["comparison"].as_u64().unwrap(), "cc", 1)
                    .is_err()
            );
            let returned = s.observe(b["comparison"].as_u64().unwrap(), "c", 1)?;
            Ok((returned["returned"].clone(), s.inspect_current()?))
        })
        .unwrap();
        NativeFieldSavedSession::open(&path)
            .unwrap()
            .with_session(|s, _| {
                assert!(s.observe(1, "cc", 1).is_err());
                let returned = s.observe(1, "c", 1)?;
                assert_eq!(returned["returned"], expected.0);
                assert_eq!(s.inspect_current()?, expected.1);
                assert!(s.observe(1, "c", 1).is_err());
                Ok(())
            })
            .unwrap();
    }
    #[test]
    #[ignore = "requires CUDA; a fully held face has no parameter derivative and exposes contradictory data"]
    fn fully_held_receiver_does_not_deposit_its_own_output() {
        with_field_session(&spec(), |s| {
            let p = s.request(&request(vec![Some("a")], "b"))?;
            assert_eq!(p["text"], "a");
            let before = s.inspect_current()?;
            let comparison = s.observe(p["comparison"].as_u64().unwrap(), "c", 1)?;
            let after = s.inspect_current()?;
            assert_eq!(before["material"], after["material"]);
            assert_eq!(before["reaction"], after["reaction"]);
            assert!(
                comparison["returned"]["parameter_update"]
                    .as_str()
                    .unwrap()
                    .starts_with("zero")
            );
            assert_ne!(
                comparison["returned"]["held_difference"]["coordinates"][0]["difference"]["real"],
                json!([[0, []], [1, [1]]])
            );
            Ok(())
        })
        .unwrap();
    }
}

//! Mandatory resident CUDA founding of the recurrent-section morphology.
//!
//! Exterior tokenization and dense chart naming remain at the process membrane. The device forms
//! the five generalized suffix ecologies and the boundary-anchored question-prefix incidence.
//! The host decodes those returned relations into their existing owners; it does not replay the
//! conditioning algorithm. There is no host fallback.

use core::ffi::c_void;
use std::collections::{BTreeMap, BTreeSet};

use body::num::COG_WORDS;
use mount::{DeviceBuffer, Dim3, Stream};
use soma_abi::morphological_condition_cuda as wire;
use soma_membrane::ReceiverFiberIdentity;

use crate::{
    live_current_cuda::CudaLiveCurrentExecutor,
    resonance_ecology::ResonanceGerm,
    suffix_ecology::{
        DeviceConditionedSuffixState, DeviceConditionedSuffixTransition, ExactLabeledSuffixEcology,
        ExactSuffixEcologyError,
    },
};

#[derive(Clone, Debug)]
pub enum MorphologicalConditionCudaError {
    Driver(mount::CudaError),
    Suffix(ExactSuffixEcologyError),
    EmptyChart,
    Extent,
    DeviceRefused(&'static str),
    InvalidDeviceReturn(&'static str),
}

impl PartialEq for MorphologicalConditionCudaError {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Driver(left), Self::Driver(right)) => {
                left.code == right.code
                    && left.name == right.name
                    && left.message == right.message
                    && left.context == right.context
            }
            (Self::Suffix(left), Self::Suffix(right)) => left == right,
            (Self::EmptyChart, Self::EmptyChart) | (Self::Extent, Self::Extent) => true,
            (Self::DeviceRefused(left), Self::DeviceRefused(right))
            | (Self::InvalidDeviceReturn(left), Self::InvalidDeviceReturn(right)) => left == right,
            _ => false,
        }
    }
}

impl Eq for MorphologicalConditionCudaError {}

impl std::fmt::Display for MorphologicalConditionCudaError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Driver(error) => write!(formatter, "{error}"),
            Self::Suffix(error) => write!(formatter, "suffix ecology refused: {error:?}"),
            Self::EmptyChart => write!(formatter, "a resident conditioning chart is empty"),
            Self::Extent => write!(
                formatter,
                "a resident conditioning extent exceeded its wire"
            ),
            Self::DeviceRefused(chart) => {
                write!(formatter, "the card refused {chart} conditioning")
            }
            Self::InvalidDeviceReturn(at) => {
                write!(formatter, "malformed conditioning return at {at}")
            }
        }
    }
}

impl std::error::Error for MorphologicalConditionCudaError {}

impl From<mount::CudaError> for MorphologicalConditionCudaError {
    fn from(value: mount::CudaError) -> Self {
        Self::Driver(value)
    }
}

impl From<ExactSuffixEcologyError> for MorphologicalConditionCudaError {
    fn from(value: ExactSuffixEcologyError) -> Self {
        Self::Suffix(value)
    }
}

/// One exact run of a receiver-shadow distribution. Adjacent coordinates with the same
/// population share a stratum; gaps and population changes remain explicit. This is a lossless
/// presentation rebase, not a histogram or sampled summary.
#[derive(Clone, Debug, Default, PartialEq, Eq, serde::Serialize)]
pub struct ExactPhaseStratum {
    pub coordinate_start: u64,
    pub coordinate_end_inclusive: u64,
    pub population_at_each_coordinate: u64,
}

/// One receiver-shadow field of a resident suffix chart. Fronts are maximum-length strata;
/// source-fiber widths are the exact reconstruction populations behind those states; outgoing
/// degrees are interaction-vertex arities. Clone states are the chart's exact context-splitting
/// caustics. The automaton's length orientation makes directed holonomy absent, stated rather than
/// inferred from a scalar count.
#[derive(Clone, Debug, Default, PartialEq, Eq, serde::Serialize)]
pub struct MorphologicalSuffixShadowReceipt {
    pub chart: String,
    pub states: u64,
    pub transitions: u64,
    pub material_transitions: u64,
    pub causal_front_distribution: Vec<ExactPhaseStratum>,
    pub reconstruction_fiber_width_distribution: Vec<ExactPhaseStratum>,
    pub interaction_arity_distribution: Vec<ExactPhaseStratum>,
    pub clone_caustics: u64,
    pub material_transition_holonomy_loops: u64,
}

#[derive(Clone, Debug, Default, PartialEq, Eq, serde::Serialize)]
pub struct MorphologicalPrefixShadowReceipt {
    pub nodes: u64,
    pub causal_depth_distribution: Vec<ExactPhaseStratum>,
    pub interaction_arity_distribution: Vec<ExactPhaseStratum>,
    pub active_caustics: u64,
    pub prefix_edge_holonomy_loops: u64,
}

#[derive(Clone, Debug, Default, PartialEq, Eq, serde::Serialize)]
pub struct MorphologicalConditionSemanticReceipt {
    pub suffix_extensions: u64,
    pub suffix_clones: u64,
    pub suffix_crosses: u64,
    pub suffix_transition_reads: u64,
    pub prefix_crossings: u64,
    pub prefix_edge_reads: u64,
    pub prefix_returned_tokens: u64,
    pub suffix_shadows: Vec<MorphologicalSuffixShadowReceipt>,
    pub prefix_shadow: MorphologicalPrefixShadowReceipt,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MorphologicalConditionApparatusReceipt {
    pub device_name: String,
    pub suffix_launches: u64,
    pub prefix_launches: u64,
    pub resident_words: u64,
    pub route_launches: u64,
    pub route_contact_launches: u64,
}

#[derive(Debug)]
pub(crate) struct DeviceConditionedCharts {
    pub lexical: ExactLabeledSuffixEcology,
    pub clause_lexical: ExactLabeledSuffixEcology,
    pub ordered_region: ExactLabeledSuffixEcology,
    pub forward_mark: ExactLabeledSuffixEcology,
    pub reverse_mark: ExactLabeledSuffixEcology,
    pub question_prefixes: BTreeMap<Vec<String>, BTreeSet<ReceiverFiberIdentity>>,
    pub question_prefix_crossings: u64,
    pub question_prefix_nodes: u64,
    pub question_prefix_legacy_cloned_tokens: u64,
    pub question_prefix_returned_tokens: u64,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct GermKey {
    identity: ReceiverFiberIdentity,
    phase: [u32; COG_WORDS],
}

impl GermKey {
    fn from_germ(germ: &ResonanceGerm) -> Self {
        Self {
            identity: germ.identity().clone(),
            phase: germ.phase().words(),
        }
    }
}

struct StagedSuffix {
    name: &'static str,
    material_symbols: Vec<ResonanceGerm>,
    source_catalogue: Vec<ReceiverFiberIdentity>,
    boundary_count: usize,
    control: DeviceBuffer<u32>,
    input: DeviceBuffer<u32>,
    states: DeviceBuffer<u32>,
    transitions: DeviceBuffer<u32>,
    occurrence_sources: DeviceBuffer<u32>,
    scratch: DeviceBuffer<u32>,
    output: DeviceBuffer<u32>,
    stream: Stream,
}

impl StagedSuffix {
    fn resident_words(&self) -> usize {
        self.control.len()
            + self.input.len()
            + self.states.len()
            + self.transitions.len()
            + self.occurrence_sources.len()
            + self.scratch.len()
            + self.output.len()
    }
}

struct StagedPrefix {
    tokens: Vec<String>,
    sources: Vec<ReceiverFiberIdentity>,
    control: DeviceBuffer<u32>,
    paths: DeviceBuffer<u32>,
    token_rows: DeviceBuffer<u32>,
    nodes: DeviceBuffer<u32>,
    supports: DeviceBuffer<u32>,
    output: DeviceBuffer<u32>,
    stream: Stream,
}

impl StagedPrefix {
    fn resident_words(&self) -> usize {
        self.control.len()
            + self.paths.len()
            + self.token_rows.len()
            + self.nodes.len()
            + self.supports.len()
            + self.output.len()
    }
}

/// One resident apparatus owner for the complete conditioning deed.
pub struct CudaMorphologicalConditioner {
    route: CudaLiveCurrentExecutor,
    suffix_resident: Vec<StagedSuffix>,
    prefix_resident: Option<StagedPrefix>,
    suffix_launches: u64,
    prefix_launches: u64,
    last_semantic: Option<MorphologicalConditionSemanticReceipt>,
    last_apparatus: Option<MorphologicalConditionApparatusReceipt>,
}

impl CudaMorphologicalConditioner {
    pub fn new(device_ordinal: i32) -> Result<Self, MorphologicalConditionCudaError> {
        let route = CudaLiveCurrentExecutor::new(device_ordinal)?;
        Ok(Self {
            route,
            suffix_resident: Vec::new(),
            prefix_resident: None,
            suffix_launches: 0,
            prefix_launches: 0,
            last_semantic: None,
            last_apparatus: None,
        })
    }

    pub fn device_name(&self) -> &str {
        self.route.device_name()
    }

    pub fn last_semantic_receipt(&self) -> Option<MorphologicalConditionSemanticReceipt> {
        self.last_semantic.clone()
    }

    pub fn last_apparatus_receipt(&self) -> Option<&MorphologicalConditionApparatusReceipt> {
        self.last_apparatus.as_ref()
    }

    pub(crate) fn condition_charts(
        &mut self,
        suffixes: [(
            &'static str,
            &[Vec<ResonanceGerm>],
            &[ReceiverFiberIdentity],
        ); 5],
        question_paths: &[(Vec<String>, ReceiverFiberIdentity)],
    ) -> Result<DeviceConditionedCharts, MorphologicalConditionCudaError> {
        self.route.context.make_current()?;
        let mut staged = Vec::with_capacity(suffixes.len());
        for (name, paths, labels) in suffixes {
            staged.push(stage_suffix(name, paths, labels)?);
        }
        let prefix = stage_prefix(question_paths)?;
        // All initial zeroing uses the context's default stream. The six deed streams are
        // non-blocking, so this explicit barrier closes ingress before any chart begins.
        self.route.context.synchronize()?;

        let suffix_function = self.route.module.function(wire::SUFFIX_ENTRY_SYMBOL)?;
        for chart in &staged {
            launch_suffix(&suffix_function, chart)?;
        }
        let prefix_function = self.route.module.function(wire::PREFIX_ENTRY_SYMBOL)?;
        launch_prefix(&prefix_function, &prefix)?;
        for chart in &staged {
            chart.stream.synchronize()?;
        }
        prefix.stream.synchronize()?;

        let route_launches = self.route.launches();
        let route_contact_launches = self.route.contact_launches();
        let mut semantic = MorphologicalConditionSemanticReceipt::default();
        let mut decoded = Vec::with_capacity(5);
        for chart in &staged {
            let (ecology, receipt, shadow) = decode_suffix(chart)?;
            semantic.suffix_extensions += receipt.suffix_extensions;
            semantic.suffix_clones += receipt.suffix_clones;
            semantic.suffix_crosses += receipt.suffix_crosses;
            semantic.suffix_transition_reads += receipt.suffix_transition_reads;
            semantic.suffix_shadows.push(shadow);
            decoded.push(ecology);
        }
        let (question_prefixes, prefix_receipt, prefix_nodes, legacy_clones) =
            decode_prefix(&prefix)?;
        semantic.prefix_crossings = prefix_receipt.prefix_crossings;
        semantic.prefix_edge_reads = prefix_receipt.prefix_edge_reads;
        semantic.prefix_returned_tokens = prefix_receipt.prefix_returned_tokens;
        semantic.prefix_shadow = prefix_receipt.prefix_shadow.clone();

        self.suffix_launches += 5;
        self.prefix_launches += 1;
        let resident_words = staged
            .iter()
            .map(StagedSuffix::resident_words)
            .sum::<usize>()
            .checked_add(prefix.resident_words())
            .ok_or(MorphologicalConditionCudaError::Extent)?;
        let apparatus = MorphologicalConditionApparatusReceipt {
            device_name: self.route.device_name().to_owned(),
            suffix_launches: 5,
            prefix_launches: 1,
            resident_words: u64::try_from(resident_words)
                .map_err(|_| MorphologicalConditionCudaError::Extent)?,
            route_launches,
            route_contact_launches,
        };
        self.last_semantic = Some(semantic.clone());
        self.last_apparatus = Some(apparatus.clone());
        self.suffix_resident = staged;
        self.prefix_resident = Some(prefix);
        let mut ecologies = decoded.into_iter();
        Ok(DeviceConditionedCharts {
            lexical: ecologies
                .next()
                .ok_or(MorphologicalConditionCudaError::Extent)?,
            clause_lexical: ecologies
                .next()
                .ok_or(MorphologicalConditionCudaError::Extent)?,
            ordered_region: ecologies
                .next()
                .ok_or(MorphologicalConditionCudaError::Extent)?,
            forward_mark: ecologies
                .next()
                .ok_or(MorphologicalConditionCudaError::Extent)?,
            reverse_mark: ecologies
                .next()
                .ok_or(MorphologicalConditionCudaError::Extent)?,
            question_prefixes,
            question_prefix_crossings: prefix_receipt.prefix_crossings,
            question_prefix_nodes: prefix_nodes,
            question_prefix_legacy_cloned_tokens: legacy_clones,
            question_prefix_returned_tokens: prefix_receipt.prefix_returned_tokens,
        })
    }
}

fn checked_u32(value: usize) -> Result<u32, MorphologicalConditionCudaError> {
    u32::try_from(value).map_err(|_| MorphologicalConditionCudaError::Extent)
}

fn exact_phase_strata(distribution: BTreeMap<u64, u64>) -> Vec<ExactPhaseStratum> {
    let mut strata = Vec::<ExactPhaseStratum>::new();
    for (coordinate, population) in distribution {
        if let Some(last) = strata.last_mut() {
            if last.population_at_each_coordinate == population
                && last.coordinate_end_inclusive.checked_add(1) == Some(coordinate)
            {
                last.coordinate_end_inclusive = coordinate;
                continue;
            }
        }
        strata.push(ExactPhaseStratum {
            coordinate_start: coordinate,
            coordinate_end_inclusive: coordinate,
            population_at_each_coordinate: population,
        });
    }
    strata
}

fn stage_suffix(
    name: &'static str,
    paths: &[Vec<ResonanceGerm>],
    labels: &[ReceiverFiberIdentity],
) -> Result<StagedSuffix, MorphologicalConditionCudaError> {
    if paths.is_empty() || paths.len() != labels.len() || paths.iter().any(Vec::is_empty) {
        return Err(MorphologicalConditionCudaError::EmptyChart);
    }
    let source_catalogue = labels
        .iter()
        .cloned()
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect::<Vec<_>>();
    let source_indices = source_catalogue
        .iter()
        .cloned()
        .enumerate()
        .map(|(at, source)| Ok((source, checked_u32(at)?)))
        .collect::<Result<BTreeMap<_, _>, MorphologicalConditionCudaError>>()?;
    let key_population = paths
        .iter()
        .flat_map(|path| path.iter().map(GermKey::from_germ))
        .collect::<BTreeSet<_>>();
    let material_symbols = key_population
        .iter()
        .map(|key| {
            let phase = soma_abi::active::RelationAtom::from_words(key.phase)
                .ok_or(MorphologicalConditionCudaError::Extent)?;
            Ok(ResonanceGerm::new(key.identity.clone(), phase))
        })
        .collect::<Result<Vec<_>, MorphologicalConditionCudaError>>()?;
    let symbol_indices = key_population
        .into_iter()
        .enumerate()
        .map(|(at, key)| Ok((key, checked_u32(at)?)))
        .collect::<Result<BTreeMap<_, _>, MorphologicalConditionCudaError>>()?;
    let mut canonical = paths
        .iter()
        .zip(labels)
        .map(|(path, label)| {
            Ok((
                path.iter()
                    .map(|germ| {
                        symbol_indices
                            .get(&GermKey::from_germ(germ))
                            .copied()
                            .ok_or(MorphologicalConditionCudaError::Extent)
                    })
                    .collect::<Result<Vec<_>, _>>()?,
                *source_indices
                    .get(label)
                    .ok_or(MorphologicalConditionCudaError::Extent)?,
            ))
        })
        .collect::<Result<Vec<_>, MorphologicalConditionCudaError>>()?;
    canonical.sort();
    let material_count = checked_u32(material_symbols.len())?;
    let material_occurrences = canonical.iter().map(|(path, _)| path.len()).sum::<usize>();
    let inputs = material_occurrences
        .checked_add(canonical.len())
        .ok_or(MorphologicalConditionCudaError::Extent)?;
    let mut input_words = Vec::with_capacity(
        inputs
            .checked_mul(wire::SUFFIX_INPUT_WORDS)
            .ok_or(MorphologicalConditionCudaError::Extent)?,
    );
    for (path_at, (path, source)) in canonical.iter().enumerate() {
        for symbol in path {
            input_words.extend([*symbol, *source, 1]);
        }
        input_words.extend([
            material_count
                .checked_add(checked_u32(path_at)?)
                .ok_or(MorphologicalConditionCudaError::Extent)?,
            wire::OPEN,
            0,
        ]);
    }
    let state_capacity = inputs
        .checked_mul(2)
        .ok_or(MorphologicalConditionCudaError::Extent)?;
    // A suffix automaton of a string of length n has at most 2n states and fewer than 3n
    // transitions. The unique path boundaries make the generalized ecology one such string.
    let transition_capacity = inputs
        .checked_mul(3)
        .and_then(|value| value.checked_add(1))
        .ok_or(MorphologicalConditionCudaError::Extent)?;
    let scratch_words = inputs
        .checked_add(1)
        .and_then(|value| {
            state_capacity
                .checked_mul(6)
                .and_then(|states| value.checked_add(states))
        })
        .ok_or(MorphologicalConditionCudaError::Extent)?;
    let control_words = [
        wire::LAYOUT_VERSION,
        checked_u32(inputs)?,
        material_count,
        checked_u32(state_capacity)?,
        checked_u32(transition_capacity)?,
        checked_u32(material_occurrences)?,
        checked_u32(scratch_words)?,
    ];
    let control = DeviceBuffer::alloc(control_words.len())?;
    control.copy_from_slice(&control_words)?;
    let input = DeviceBuffer::alloc(input_words.len())?;
    input.copy_from_slice(&input_words)?;
    Ok(StagedSuffix {
        name,
        material_symbols,
        source_catalogue,
        boundary_count: canonical.len(),
        control,
        input,
        states: DeviceBuffer::alloc_zeroed(state_capacity * wire::SUFFIX_STATE_WORDS)?,
        transitions: DeviceBuffer::alloc_zeroed(
            transition_capacity * wire::SUFFIX_TRANSITION_WORDS,
        )?,
        occurrence_sources: DeviceBuffer::alloc_zeroed(material_occurrences)?,
        scratch: DeviceBuffer::alloc_zeroed(scratch_words)?,
        output: DeviceBuffer::alloc_zeroed(wire::SUFFIX_OUTPUT_WORDS)?,
        stream: Stream::create()?,
    })
}

fn launch_suffix(
    function: &mount::Function<'_>,
    chart: &StagedSuffix,
) -> Result<(), MorphologicalConditionCudaError> {
    let mut control_pointer = chart.control.device_ptr();
    let mut control_len = chart.control.len();
    let mut input_pointer = chart.input.device_ptr();
    let mut input_len = chart.input.len();
    let mut state_pointer = chart.states.device_ptr();
    let mut state_len = chart.states.len();
    let mut transition_pointer = chart.transitions.device_ptr();
    let mut transition_len = chart.transitions.len();
    let mut occurrence_pointer = chart.occurrence_sources.device_ptr();
    let mut occurrence_len = chart.occurrence_sources.len();
    let mut scratch_pointer = chart.scratch.device_ptr();
    let mut scratch_len = chart.scratch.len();
    let mut output_pointer = chart.output.device_ptr();
    let mut output_len = chart.output.len();
    let mut parameters = [
        &mut control_pointer as *mut u64 as *mut c_void,
        &mut control_len as *mut usize as *mut c_void,
        &mut input_pointer as *mut u64 as *mut c_void,
        &mut input_len as *mut usize as *mut c_void,
        &mut state_pointer as *mut u64 as *mut c_void,
        &mut state_len as *mut usize as *mut c_void,
        &mut transition_pointer as *mut u64 as *mut c_void,
        &mut transition_len as *mut usize as *mut c_void,
        &mut occurrence_pointer as *mut u64 as *mut c_void,
        &mut occurrence_len as *mut usize as *mut c_void,
        &mut scratch_pointer as *mut u64 as *mut c_void,
        &mut scratch_len as *mut usize as *mut c_void,
        &mut output_pointer as *mut u64 as *mut c_void,
        &mut output_len as *mut usize as *mut c_void,
    ];
    function.launch_on(&chart.stream, Dim3::x(1), Dim3::x(1), &mut parameters)?;
    Ok(())
}

fn decode_suffix(
    chart: &StagedSuffix,
) -> Result<
    (
        ExactLabeledSuffixEcology,
        MorphologicalConditionSemanticReceipt,
        MorphologicalSuffixShadowReceipt,
    ),
    MorphologicalConditionCudaError,
> {
    let mut output = vec![0u32; chart.output.len()];
    chart.output.copy_to_slice(&mut output)?;
    match output[wire::SUFFIX_OUTPUT_STATUS] {
        wire::STATUS_COMPLETE => {}
        wire::STATUS_INVALID => {
            return Err(MorphologicalConditionCudaError::DeviceRefused(chart.name))
        }
        _ => {
            return Err(MorphologicalConditionCudaError::InvalidDeviceReturn(
                "suffix status",
            ))
        }
    }
    if output[wire::SUFFIX_OUTPUT_VERSION] != wire::LAYOUT_VERSION {
        return Err(MorphologicalConditionCudaError::InvalidDeviceReturn(
            "suffix version",
        ));
    }
    let state_count = output[wire::SUFFIX_OUTPUT_STATE_COUNT] as usize;
    let transition_count = output[wire::SUFFIX_OUTPUT_TRANSITION_COUNT] as usize;
    let occurrence_count = output[wire::SUFFIX_OUTPUT_OCCURRENCE_COUNT] as usize;
    if state_count == 0
        || state_count * wire::SUFFIX_STATE_WORDS > chart.states.len()
        || transition_count * wire::SUFFIX_TRANSITION_WORDS > chart.transitions.len()
        || occurrence_count > chart.occurrence_sources.len()
    {
        return Err(MorphologicalConditionCudaError::InvalidDeviceReturn(
            "suffix extents",
        ));
    }
    let mut state_words = vec![0u32; state_count * wire::SUFFIX_STATE_WORDS];
    chart.states.copy_range_to_slice(0, &mut state_words)?;
    let states = state_words
        .chunks_exact(wire::SUFFIX_STATE_WORDS)
        .map(|row| DeviceConditionedSuffixState {
            maximum_length: row[wire::SUFFIX_STATE_MAXIMUM_LENGTH] as usize,
            suffix: (row[wire::SUFFIX_STATE_SUFFIX] != wire::OPEN)
                .then_some(row[wire::SUFFIX_STATE_SUFFIX] as usize),
            material_end_multiplicity: row[wire::SUFFIX_STATE_MULTIPLICITY_LO] as u64
                | ((row[wire::SUFFIX_STATE_MULTIPLICITY_HI] as u64) << 32),
            source_span_start: row[wire::SUFFIX_STATE_SPAN_START] as u64,
            source_span_len: row[wire::SUFFIX_STATE_SPAN_LEN] as u64,
        })
        .collect::<Vec<_>>();
    let mut transition_words = vec![0u32; transition_count * wire::SUFFIX_TRANSITION_WORDS];
    chart
        .transitions
        .copy_range_to_slice(0, &mut transition_words)?;
    let transitions = transition_words
        .chunks_exact(wire::SUFFIX_TRANSITION_WORDS)
        .map(|row| DeviceConditionedSuffixTransition {
            state: row[wire::SUFFIX_TRANSITION_STATE] as usize,
            symbol: row[wire::SUFFIX_TRANSITION_SYMBOL],
            target: row[wire::SUFFIX_TRANSITION_TARGET] as usize,
        })
        .collect::<Vec<_>>();
    let mut causal_front_distribution = BTreeMap::new();
    let mut reconstruction_fiber_width_distribution = BTreeMap::new();
    let mut arities = vec![0u64; states.len()];
    for state in &states {
        *causal_front_distribution
            .entry(state.maximum_length as u64)
            .or_insert(0) += 1;
        *reconstruction_fiber_width_distribution
            .entry(state.source_span_len)
            .or_insert(0) += 1;
    }
    for transition in &transitions {
        let arity = arities.get_mut(transition.state).ok_or(
            MorphologicalConditionCudaError::InvalidDeviceReturn("transition source"),
        )?;
        *arity += 1;
    }
    let mut interaction_arity_distribution = BTreeMap::new();
    for arity in arities {
        *interaction_arity_distribution.entry(arity).or_insert(0) += 1;
    }
    let mut occurrences = vec![0u32; occurrence_count];
    chart
        .occurrence_sources
        .copy_range_to_slice(0, &mut occurrences)?;
    let ecology = ExactLabeledSuffixEcology::from_device_conditioned(
        &chart.material_symbols,
        chart.boundary_count,
        &states,
        &transitions,
        chart.source_catalogue.clone(),
        occurrences,
        output[wire::SUFFIX_OUTPUT_MATERIAL_TRANSITIONS] as usize,
    )?;
    let shadow = MorphologicalSuffixShadowReceipt {
        chart: chart.name.to_owned(),
        states: state_count as u64,
        transitions: transition_count as u64,
        material_transitions: output[wire::SUFFIX_OUTPUT_MATERIAL_TRANSITIONS] as u64,
        causal_front_distribution: exact_phase_strata(causal_front_distribution),
        reconstruction_fiber_width_distribution: exact_phase_strata(
            reconstruction_fiber_width_distribution,
        ),
        interaction_arity_distribution: exact_phase_strata(interaction_arity_distribution),
        clone_caustics: output[wire::SUFFIX_OUTPUT_CLONES] as u64,
        material_transition_holonomy_loops: 0,
    };
    Ok((
        ecology,
        MorphologicalConditionSemanticReceipt {
            suffix_extensions: output[wire::SUFFIX_OUTPUT_EXTENSIONS] as u64,
            suffix_clones: output[wire::SUFFIX_OUTPUT_CLONES] as u64,
            suffix_crosses: output[wire::SUFFIX_OUTPUT_SUFFIX_CROSSES_LO] as u64
                | ((output[wire::SUFFIX_OUTPUT_SUFFIX_CROSSES_HI] as u64) << 32),
            suffix_transition_reads: output[wire::SUFFIX_OUTPUT_TRANSITION_READS_LO] as u64
                | ((output[wire::SUFFIX_OUTPUT_TRANSITION_READS_HI] as u64) << 32),
            ..MorphologicalConditionSemanticReceipt::default()
        },
        shadow,
    ))
}

fn stage_prefix(
    question_paths: &[(Vec<String>, ReceiverFiberIdentity)],
) -> Result<StagedPrefix, MorphologicalConditionCudaError> {
    let token_catalogue = question_paths
        .iter()
        .flat_map(|(path, _)| path.iter().cloned())
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect::<Vec<_>>();
    let token_indices = token_catalogue
        .iter()
        .cloned()
        .enumerate()
        .map(|(at, token)| Ok((token, checked_u32(at)?)))
        .collect::<Result<BTreeMap<_, _>, MorphologicalConditionCudaError>>()?;
    let sources = question_paths
        .iter()
        .map(|(_, source)| source.clone())
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect::<Vec<_>>();
    let source_indices = sources
        .iter()
        .cloned()
        .enumerate()
        .map(|(at, source)| Ok((source, checked_u32(at)?)))
        .collect::<Result<BTreeMap<_, _>, MorphologicalConditionCudaError>>()?;
    let token_count = question_paths
        .iter()
        .map(|(path, _)| path.len())
        .sum::<usize>();
    let crossings = question_paths
        .iter()
        .map(|(path, _)| path.len().saturating_sub(1))
        .sum::<usize>();
    let mut token_rows = Vec::with_capacity(token_count);
    let mut path_words = Vec::with_capacity(question_paths.len() * wire::PREFIX_PATH_WORDS);
    for (path, source) in question_paths {
        if path.len() < 2 {
            return Err(MorphologicalConditionCudaError::EmptyChart);
        }
        let start = token_rows.len();
        for token in path {
            token_rows.push(
                *token_indices
                    .get(token)
                    .ok_or(MorphologicalConditionCudaError::Extent)?,
            );
        }
        path_words.extend([
            checked_u32(start)?,
            checked_u32(path.len())?,
            *source_indices
                .get(source)
                .ok_or(MorphologicalConditionCudaError::Extent)?,
        ]);
    }
    let node_capacity = crossings
        .checked_add(1)
        .ok_or(MorphologicalConditionCudaError::Extent)?;
    let control_words = [
        wire::LAYOUT_VERSION,
        checked_u32(question_paths.len())?,
        checked_u32(token_count)?,
        checked_u32(node_capacity)?,
        checked_u32(crossings)?,
    ];
    let control = DeviceBuffer::alloc(control_words.len())?;
    control.copy_from_slice(&control_words)?;
    let paths = DeviceBuffer::alloc(path_words.len().max(1))?;
    if !path_words.is_empty() {
        paths.copy_range_from_slice(0, &path_words)?;
    }
    let token_buffer = DeviceBuffer::alloc(token_rows.len().max(1))?;
    if !token_rows.is_empty() {
        token_buffer.copy_range_from_slice(0, &token_rows)?;
    }
    Ok(StagedPrefix {
        tokens: token_catalogue,
        sources,
        control,
        paths,
        token_rows: token_buffer,
        nodes: DeviceBuffer::alloc_zeroed(node_capacity * wire::PREFIX_NODE_WORDS)?,
        supports: DeviceBuffer::alloc_zeroed((crossings * wire::PREFIX_SUPPORT_WORDS).max(1))?,
        output: DeviceBuffer::alloc_zeroed(wire::PREFIX_OUTPUT_WORDS)?,
        stream: Stream::create()?,
    })
}

fn launch_prefix(
    function: &mount::Function<'_>,
    prefix: &StagedPrefix,
) -> Result<(), MorphologicalConditionCudaError> {
    let mut control_pointer = prefix.control.device_ptr();
    let mut control_len = prefix.control.len();
    let mut path_pointer = prefix.paths.device_ptr();
    let mut path_len = if prefix.paths.len() == 1 && prefix.sources.is_empty() {
        0
    } else {
        prefix.paths.len()
    };
    let mut token_pointer = prefix.token_rows.device_ptr();
    let mut token_len = if prefix.token_rows.len() == 1 && prefix.tokens.is_empty() {
        0
    } else {
        prefix.token_rows.len()
    };
    let mut node_pointer = prefix.nodes.device_ptr();
    let mut node_len = prefix.nodes.len();
    let mut support_pointer = prefix.supports.device_ptr();
    let mut support_len = if prefix.supports.len() == 1 && prefix.sources.is_empty() {
        0
    } else {
        prefix.supports.len()
    };
    let mut output_pointer = prefix.output.device_ptr();
    let mut output_len = prefix.output.len();
    let mut parameters = [
        &mut control_pointer as *mut u64 as *mut c_void,
        &mut control_len as *mut usize as *mut c_void,
        &mut path_pointer as *mut u64 as *mut c_void,
        &mut path_len as *mut usize as *mut c_void,
        &mut token_pointer as *mut u64 as *mut c_void,
        &mut token_len as *mut usize as *mut c_void,
        &mut node_pointer as *mut u64 as *mut c_void,
        &mut node_len as *mut usize as *mut c_void,
        &mut support_pointer as *mut u64 as *mut c_void,
        &mut support_len as *mut usize as *mut c_void,
        &mut output_pointer as *mut u64 as *mut c_void,
        &mut output_len as *mut usize as *mut c_void,
    ];
    function.launch_on(&prefix.stream, Dim3::x(1), Dim3::x(1), &mut parameters)?;
    Ok(())
}

fn decode_prefix(
    prefix: &StagedPrefix,
) -> Result<
    (
        BTreeMap<Vec<String>, BTreeSet<ReceiverFiberIdentity>>,
        MorphologicalConditionSemanticReceipt,
        u64,
        u64,
    ),
    MorphologicalConditionCudaError,
> {
    let mut output = vec![0u32; prefix.output.len()];
    prefix.output.copy_to_slice(&mut output)?;
    match output[wire::PREFIX_OUTPUT_STATUS] {
        wire::STATUS_COMPLETE => {}
        wire::STATUS_INVALID => {
            return Err(MorphologicalConditionCudaError::DeviceRefused(
                "question-prefix",
            ))
        }
        _ => {
            return Err(MorphologicalConditionCudaError::InvalidDeviceReturn(
                "prefix status",
            ))
        }
    }
    let node_count = output[wire::PREFIX_OUTPUT_NODE_COUNT] as usize;
    let support_count = output[wire::PREFIX_OUTPUT_SUPPORT_COUNT] as usize;
    if node_count == 0
        || node_count * wire::PREFIX_NODE_WORDS > prefix.nodes.len()
        || support_count * wire::PREFIX_SUPPORT_WORDS > prefix.supports.len()
    {
        return Err(MorphologicalConditionCudaError::InvalidDeviceReturn(
            "prefix extents",
        ));
    }
    let mut node_words = vec![0u32; node_count * wire::PREFIX_NODE_WORDS];
    prefix.nodes.copy_range_to_slice(0, &mut node_words)?;
    let mut support_words = vec![0u32; support_count * wire::PREFIX_SUPPORT_WORDS];
    if !support_words.is_empty() {
        prefix.supports.copy_range_to_slice(0, &mut support_words)?;
    }
    let mut sources_by_node = BTreeMap::<usize, BTreeSet<ReceiverFiberIdentity>>::new();
    for support in support_words.chunks_exact(wire::PREFIX_SUPPORT_WORDS) {
        let node = support[wire::PREFIX_SUPPORT_NODE] as usize;
        let source = prefix
            .sources
            .get(support[wire::PREFIX_SUPPORT_SOURCE] as usize)
            .ok_or(MorphologicalConditionCudaError::InvalidDeviceReturn(
                "prefix source",
            ))?;
        sources_by_node
            .entry(node)
            .or_default()
            .insert(source.clone());
    }
    let mut returned = BTreeMap::new();
    let mut causal_depth_distribution = BTreeMap::new();
    let mut interaction_arity_distribution = BTreeMap::new();
    let mut active_caustics = 0u64;
    for node in 1..node_count {
        let row = &node_words[node * wire::PREFIX_NODE_WORDS..][..wire::PREFIX_NODE_WORDS];
        let mut depth = 0u64;
        let mut depth_cursor = node;
        while depth_cursor != 0 {
            depth += 1;
            depth_cursor = node_words
                [depth_cursor * wire::PREFIX_NODE_WORDS + wire::PREFIX_NODE_PARENT]
                as usize;
            if depth_cursor >= node_count {
                return Err(MorphologicalConditionCudaError::InvalidDeviceReturn(
                    "prefix depth",
                ));
            }
        }
        *causal_depth_distribution.entry(depth).or_insert(0) += 1;
        let mut arity = 0u64;
        let mut child = row[wire::PREFIX_NODE_FIRST_CHILD];
        while child != wire::OPEN {
            arity += 1;
            let child_at = child as usize;
            if child_at >= node_count {
                return Err(MorphologicalConditionCudaError::InvalidDeviceReturn(
                    "prefix child",
                ));
            }
            child = node_words[child_at * wire::PREFIX_NODE_WORDS + wire::PREFIX_NODE_NEXT_SIBLING];
        }
        *interaction_arity_distribution.entry(arity).or_insert(0) += 1;
        if row[wire::PREFIX_NODE_ACTIVE] != 1 {
            continue;
        }
        active_caustics += 1;
        let mut reverse = Vec::new();
        let mut cursor = node;
        while cursor != 0 {
            let here = &node_words[cursor * wire::PREFIX_NODE_WORDS..][..wire::PREFIX_NODE_WORDS];
            reverse.push(
                prefix
                    .tokens
                    .get(here[wire::PREFIX_NODE_TOKEN] as usize)
                    .ok_or(MorphologicalConditionCudaError::InvalidDeviceReturn(
                        "prefix token",
                    ))?
                    .clone(),
            );
            cursor = here[wire::PREFIX_NODE_PARENT] as usize;
            if cursor >= node_count {
                return Err(MorphologicalConditionCudaError::InvalidDeviceReturn(
                    "prefix parent",
                ));
            }
        }
        reverse.reverse();
        returned.insert(reverse, sources_by_node.remove(&node).unwrap_or_default());
    }
    let join = |low: usize| output[low] as u64 | ((output[low + 1] as u64) << 32);
    let prefix_shadow = MorphologicalPrefixShadowReceipt {
        nodes: (node_count - 1) as u64,
        causal_depth_distribution: exact_phase_strata(causal_depth_distribution),
        interaction_arity_distribution: exact_phase_strata(interaction_arity_distribution),
        active_caustics,
        prefix_edge_holonomy_loops: 0,
    };
    Ok((
        returned,
        MorphologicalConditionSemanticReceipt {
            prefix_crossings: join(wire::PREFIX_OUTPUT_CROSSINGS_LO),
            prefix_edge_reads: join(wire::PREFIX_OUTPUT_EDGE_READS_LO),
            prefix_returned_tokens: join(wire::PREFIX_OUTPUT_RETURNED_TOKENS_LO),
            prefix_shadow,
            ..MorphologicalConditionSemanticReceipt::default()
        },
        u64::try_from(node_count - 1).map_err(|_| MorphologicalConditionCudaError::Extent)?,
        join(wire::PREFIX_OUTPUT_LEGACY_CLONES_LO),
    ))
}

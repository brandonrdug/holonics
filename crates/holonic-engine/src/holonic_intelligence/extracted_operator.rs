//! **The extracted operator as one Holon: its occurrence, advance, emission, trace and refusal.**
//!
//! [definition] Equation extraction reads a foreign model's computational graph as native
//! equations on the Holon `H = (K, ∂_A; Π; 𝒟; 𝓔; G; π)`
//! ([object](../../../../docs/ELEMENTARY_OBJECTS.md#the-holon-as-one-object)): the operator graph's
//! carrier incidence is the interconnection 𝒟 (`NativeFullOperatorEcology::{carriers, operations}`,
//! each `NativeOperatorNode` a bond between its input and output carriers), its coefficient
//! populations are the element relations 𝓔 (`NativeCoefficientPopulation`, resident as
//! `ResidentNativeOperatorPopulation` in `NativeOperatorResidence`), and the operation word is the
//! transport law advanced one occurrence at a time. An occurrence enters at the source port Π —
//! as addresses into a resident population (a lookup) or as host-entered carrier words (an
//! occurrence-entered product) — and every operation returns one emission at its receiver face
//! and one trace of its passage. The deposited overlay is the only change of the constitution
//! (`NativeMorphologyDeposit`, core `deposition`), and the return through the body is its one-cut
//! pullback.
//!
//! [definition] Two executors realize the same advance and share this one ladder: the graph
//! session (`ExtractedOperatorSession`, the complete operation word by fused segments with its
//! tiled terminal receiver) and the branch session (`ExtractedBranchSession`, the six-node
//! per-layer interaction branch executed operation by operation on host-entered carriers). The
//! branch's morphology charts onto the same constitution type
//! (`NativeOperatorMorphology::constitution_chart`) and rests in the same rest
//! (`ExtractedOperatorRest`). Plan: `docs/plans/THE_HOLON_CORE_FOUNDS_THE_NATIVE_MACHINERY.md`,
//! "Phase 15 disposition".
//!
//! ```text
//! ExtractedOperatorOccurrence   one occurrence at the source port (addressed rows | entered words)
//! ExtractedOperatorAdvance      the advance facet: occurrence → step, move-owned successor
//! ExtractedOperatorEmission<O>  the successor carrier read at the receiver face (O labels the operation)
//! ExtractedOperatorTrace<C>     the passage's testimony; C is the executor's chart of it
//! ExtractedOperatorStep / Branch  one operation / one whole word, with the successor
//! ExtractedOperatorRefusal      the one refusal family of advance, pullback and rest
//! ```

use serde::Serialize;
use thiserror::Error;

use crate::resident_section::{ResidentRefusal, TransferCensus};

use super::{
    NativeCarrierOrdinal, NativeEmissionProjection, NativeFullOperatorError,
    NativeMorphologyTransition, NativeNumericalOrigin, NativeOperatorKind,
    NativeOperatorMorphologyError, NativeOperatorNode, NativeOperatorResidenceError,
    NativeSuccessorProjection,
};

/// [definition] **One occurrence at the source port.** `ordinal` is the generation it joins. A
/// lookup consumes `row_addresses` (addresses into a resident coefficient population); an
/// occurrence-entered product consumes `interaction_words` (host-entered bfloat16 carrier words).
/// Every other operation receives neither, and an executor refuses the port it does not have.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct ExtractedOperatorOccurrence {
    pub ordinal: u64,
    pub row_addresses: Vec<u32>,
    pub interaction_words: Vec<u16>,
}

impl ExtractedOperatorOccurrence {
    /// An occurrence addressed into resident rows.
    pub fn addressed(ordinal: u64, row_addresses: Vec<u32>) -> Self {
        Self {
            ordinal,
            row_addresses,
            interaction_words: Vec::new(),
        }
    }

    /// An occurrence entered as host carrier words.
    pub fn entered(ordinal: u64, interaction_words: Vec<u16>) -> Self {
        Self {
            ordinal,
            row_addresses: Vec::new(),
            interaction_words,
        }
    }

    /// An internal operation's occurrence: it consumes nothing at the port.
    pub fn internal(ordinal: u64) -> Self {
        Self {
            ordinal,
            ..Self::default()
        }
    }

    /// Whether nothing enters at the port.
    pub fn is_internal(&self) -> bool {
        self.row_addresses.is_empty() && self.interaction_words.is_empty()
    }
}

/// [definition] **The receiver face of one operation**: the successor carrier's shape and grain,
/// and its enclosures when it crosses to the host. `operation` labels the operation in its
/// executor's chart (`u32`: the graph ordinal; `NativeOperatorKind`: the branch's kind). The graph
/// session's intermediate emissions carry no words (no section crosses between two operations);
/// its terminal face carries them, read once at the declared receiver (`projection` names an exact
/// receiver restriction of the complete face).
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct ExtractedOperatorEmission<O = u32> {
    pub generation: u64,
    pub operation: O,
    /// The operation's output carrier in the constitution chart.
    pub carrier: NativeCarrierOrdinal,
    pub rows: usize,
    pub width: usize,
    pub grain: u32,
    pub intervals: Vec<(i64, i64)>,
    /// Exact receiver projection; the complete source section stays with the native successor.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub projection: Option<NativeEmissionProjection>,
}

/// [definition] **The testimony of one passage**: which generation it joined and produced, the
/// measured octave bound of the successor carrier, the resident constitution's size and the
/// surface's transfer census around it. `chart` is the executor's own reading (the operation
/// node, projection, morphology transition and numerical origin of the graph session; the
/// chronology, widths and passage slots of the branch session), flattened into the same record.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct ExtractedOperatorTrace<C> {
    pub schema: String,
    pub predecessor_generation: u64,
    pub successor_generation: u64,
    pub occurrence: u64,
    /// The measured octave bound of the successor carrier.
    pub successor_bound_octaves: u32,
    pub resident_coefficient_octets: u64,
    pub census_before: TransferCensus,
    pub census_after: TransferCensus,
    #[serde(flatten)]
    pub chart: C,
}

/// The graph session's chart of one passage.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct GraphTraceChart {
    pub row_addresses: Vec<u32>,
    pub operation: NativeOperatorNode,
    pub successor_projection: NativeSuccessorProjection,
    pub morphology_transition: NativeMorphologyTransition,
    /// The total rank of the factorized overlay the constitution carries at this operation.
    pub morphology_overlay_rank: usize,
    /// The a-priori octave bound the operation was admitted under.
    pub admitted_octaves: u32,
    /// None is a freshly enacted numerical passage; Some retains its exact prior computation
    /// while this trace's native occurrence, chronology and local return are new.
    pub numerical_origin: Option<NativeNumericalOrigin>,
}

/// The branch session's chart of one passage.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct BranchTraceChart {
    pub chronology: Vec<u64>,
    pub operation: NativeOperatorKind,
    pub predecessor_width: usize,
    pub successor_width: usize,
    pub passage_slot_population: usize,
    pub refusal_population: usize,
}

/// [definition] **The advance facet of the extracted operator.** One occurrence at the source
/// port advances the move-owned session by one operation and returns its emission, its trace and
/// the successor; the operation word, not the caller, decides which operation enacts.
pub trait ExtractedOperatorAdvance: Sized {
    /// How the executor labels an operation at its receiver face.
    type Operation;
    /// The executor's chart of a passage.
    type TraceChart;

    fn generation(&self) -> u64;
    fn operation_at(&self) -> usize;
    fn chronology(&self) -> &[u64];
    fn advance_occurrence(
        self,
        occurrence: ExtractedOperatorOccurrence,
    ) -> Result<ExtractedOperatorStep<Self>, ExtractedOperatorRefusal>;
}

/// One operation: its emission, its trace and the move-owned successor.
pub struct ExtractedOperatorStep<S: ExtractedOperatorAdvance> {
    pub emission: ExtractedOperatorEmission<S::Operation>,
    pub trace: ExtractedOperatorTrace<S::TraceChart>,
    pub successor: S,
}

/// A whole run of the operation word (the branch's six operations, the graph's terminal
/// boundary): every emission and trace in order, and the successor.
pub struct ExtractedOperatorBranch<S: ExtractedOperatorAdvance> {
    pub emissions: Vec<ExtractedOperatorEmission<S::Operation>>,
    pub traces: Vec<ExtractedOperatorTrace<S::TraceChart>>,
    pub successor: S,
}

/// [definition] **The one refusal family** of the extracted operator: advance, the return
/// through the body, residence and rest. Constitution refusals (the chart, the branch morphology,
/// the residence, the resident apparatus) enter as their own sources.
#[derive(Debug, Error)]
pub enum ExtractedOperatorRefusal {
    #[error("the native session is interrupted; its held state must not be silently replayed")]
    Interrupted,
    #[error("native contact: {0}")]
    Contact(&'static str),
    #[error("operator ecology: {0}")]
    Ecology(#[from] NativeFullOperatorError),
    #[error(transparent)]
    BranchMorphology(#[from] NativeOperatorMorphologyError),
    #[error("operator residence: {0}")]
    Residence(#[from] NativeOperatorResidenceError),
    #[error("resident apparatus: {0}")]
    Resident(#[from] ResidentRefusal),
    #[error("the carrier occurrence has the wrong extent")]
    CarrierExtent,
    #[error("the interaction occurrence has the wrong extent for this operation")]
    InteractionExtent,
    #[error("the occurrence does not join the contemporary ecology")]
    Occurrence,
    #[error("the current operation disagrees with the complete ecology")]
    Operation,
    #[error("operation {operation} is not yet enacted by the full-session owner")]
    PrimitiveOpen { operation: u32 },
    #[error("the lookup's exact common grain is outside the resident carrier")]
    Grain,
    #[error("no exact resident grain admits the initial carrier")]
    NoAdmittedGrain,
    #[error("resident operation {operation} returned obstruction flags {flags:#x}")]
    ResidentObstruction { operation: u32, flags: u32 },
    #[error("the residual re-entry standing is absent")]
    MissingReentry,
    #[error("the ecology generation overflowed")]
    Generation,
    #[error("the requested contemporary carrier is absent")]
    Carrier,
    #[error("the declared successor projection did not return a point carrier")]
    Projection,
    #[error("the local morphology current is malformed or does not enter this operation")]
    Morphology,
    #[error("the return through the body refused: {0}")]
    Adjoint(String),
    #[error("the differential does not match the cross-section: {0}")]
    AdjointShape(String),
    #[error("resident adjoint returned obstruction flags {flags:#x}")]
    AdjointObstruction { flags: u32 },
    #[error("native session rest: {0}")]
    Rest(String),
    #[error("this session rest boundary is not supported: {0}")]
    Unsupported(&'static str),
    #[error("rest I/O: {0}")]
    Io(#[from] std::io::Error),
    #[error("rest header: {0}")]
    Json(#[from] serde_json::Error),
}

impl From<crate::embedding_fiber::FiberError> for ExtractedOperatorRefusal {
    fn from(error: crate::embedding_fiber::FiberError) -> Self {
        Self::Resident(ResidentRefusal::Declaration {
            operation: "operator-mount",
            what: error.to_string(),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn one_occurrence_carries_either_port() {
        let addressed = ExtractedOperatorOccurrence::addressed(3, vec![1, 2]);
        let entered = ExtractedOperatorOccurrence::entered(4, vec![0x3f80]);
        assert!(!addressed.is_internal() && !entered.is_internal());
        assert!(ExtractedOperatorOccurrence::internal(5).is_internal());
        assert_eq!(entered.row_addresses, Vec::<u32>::new());
        assert_eq!(addressed.interaction_words, Vec::<u16>::new());
    }

    #[test]
    fn a_trace_flattens_its_chart_into_one_record() {
        let census = TransferCensus::default();
        let trace = ExtractedOperatorTrace {
            schema: "s".into(),
            predecessor_generation: 0,
            successor_generation: 1,
            occurrence: 0,
            successor_bound_octaves: 9,
            resident_coefficient_octets: 12,
            census_before: census.clone(),
            census_after: census,
            chart: BranchTraceChart {
                chronology: vec![0],
                operation: NativeOperatorKind::GeluTanh,
                predecessor_width: 2,
                successor_width: 2,
                passage_slot_population: 1,
                refusal_population: 0,
            },
        };
        let value = serde_json::to_value(&trace).unwrap();
        let keys: Vec<_> = value.as_object().unwrap().keys().cloned().collect();
        for key in [
            "schema",
            "predecessor_generation",
            "successor_generation",
            "occurrence",
            "chronology",
            "operation",
            "predecessor_width",
            "successor_width",
            "resident_coefficient_octets",
            "passage_slot_population",
            "refusal_population",
            "successor_bound_octaves",
            "census_before",
            "census_after",
        ] {
            assert!(keys.contains(&key.to_owned()), "{key}");
        }
        assert_eq!(
            keys.len(),
            14,
            "the chart adds no key the record did not carry"
        );
        assert_eq!(value["operation"], "gelu-tanh");
    }
}

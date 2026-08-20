//! **The front passage: a bound operation diagram compiled into one resident graph, admitted whole
//! before any allocation, launched once, read once.**
//!
//! Contract:
//! [`research/records/2026-08-18_THE_SECTION_MUST_STAY_ON_THE_CARD_THE_CONTRACT_BEFORE_THE_RESIDENT_LAYER.md`]
//! §4–5. Audit that occasioned this form:
//! `research/records/2026-08-18_THE_SECTION_STAYED_BUT_THE_HOST_STILL_OWNED_THE_PASSAGE_AND_NO_PHOENIX_STATION_PASSED.md`.
//! The lineage-local refusal transport and the typed admission below answer the resident-gate
//! directive of 2026-08-19.
//!
//! ```text
//!   ported_operation::Front           co-presence, read off CausalDiagram::layers
//!     -> source_occurrence            every binding's testimony resolved against authenticated content
//!     -> the a-priori octave law      what each port is bounded at, before anything launches
//!     -> exact_work + apparatus       the WHOLE deed priced: every front, staging, sections, census,
//!                                     lineage, ingress, egress, allocations, launches, synchronizations
//!     -> DeedReceiver + the card      admitted coordinate by coordinate in the product order — every
//!                                     coordinate bounded or exhibited as unbounded with what still
//!                                     constrains it — or a typed refusal with zero launches and zero
//!                                     allocations
//!     -> hardware_cover               partition integrity per front, cells placed on the surface's cover
//!     -> interchange::certify_footprints   independence derived from footprints — sections, maps, the
//!                                     occurrence's own census slot written, its predecessors' slots and
//!                                     its lineage list read — before launch
//!     -> resident_section             the graph: bonds as edges, refusals travelling along the lineage
//!     -> one launch, one census read  the deed
//!     -> FrontReceipt                 predicted against measured, port by port; the complete
//!                                     obstruction lineage beside it
//! ```
//!
//! # The laws are owner-local, not a cabinet
//!
//! An occurrence is bound to a [`ResidentLaw`] ([`crate::resident_law`]): one object that carries
//! its own species and arity, names the material it reads, derives its a-priori octave bound and
//! its shape and price, states the resident ranges its kernel reads, and records its one kernel
//! into a lane. The first form of this owner held an eleven-variant `enum ResidentBinding` matched
//! at six sites — the shape, the bound, the material check, the footprint, the recording and the
//! naming each re-dispatched over the same variants — which is a central semantic cabinet consumed
//! at graph construction, and one every future architecture would extend. A law is now added by
//! writing one type and one kernel; nothing in this file is touched. The realization table
//! ([`ResidentRealization`]) binds occurrences to laws and is consumed once, at compile. Nothing
//! here is consulted while the deed runs: [`crate::resident_section::TransferCensus`] measures
//! that.
//!
//! # The a-priori octave law is a hypothesis, admitted and then refuted or confirmed on the card
//!
//! Every occurrence is admitted under a bound on the octaves its output can occupy, derived from
//! the bounds on its inputs and the material's extents. The card's census compares the measured
//! octave to that bound after every occurrence; a refuted bound is a refusal that travels along the
//! lineage, so no successor computes on words wider than it was admitted for. The receipt reports
//! bound and measured per port, so the law is refutable rather than trusted.
//!
//! # Admission is typed and product-ordered; nothing is `None`
//!
//! [`DeedAdmission`] carries every semantic coordinate of the deed's [`ExactWork`] and every
//! apparatus coordinate of its [`ApparatusPrediction`], each as a [`CoordinateAdmission`]: the
//! required value, its [`Ceiling`] — bounded by the receiver's declaration or by the mounted
//! apparatus, or **unbounded with the reason and with the apparatus limits that still constrain
//! it** — and whether it is admitted. The deed is admitted exactly when every bounded coordinate
//! is inside its ceiling. No magic scalar stands for an undeclared ceiling, and source-map mounting
//! is its own preceding admission ([`MaterialAdmission`]) which the deed cites.
//!
//! # The five obstruction species, kept apart
//!
//! [`FrontPassageObstruction`] carries a cover barrier, an interchange refusal, a resource
//! obstruction and a compile refusal as four variants with four payloads because each is answered
//! differently; and a fifth, [`FrontPassageObstruction::Refused`], for a refusal the card raised
//! during the deed, named for its occurrence and carrying the complete obstruction lineage. None is
//! answered by running anything on the CPU.

use std::collections::{BTreeMap, BTreeSet};

use holonic_structure::LocalSet;
use num_bigint::BigUint;
use num_traits::{ToPrimitive, Zero};
use relational_geometry::Rat;

use crate::causal::EventId;
use crate::exact_work::{ExactWork, WorkBudget};
use crate::hardware_cover::{ChartId, CoverBarrier, CoverDecomposition, FrontCell, ModeIdentity};
use crate::interaction::OccurrencePort;
use crate::interchange::{certify_footprints, DistinguishingWord, FrontCertificate, MemberFootprint};
use crate::ported_operation::{DiagramClosure, Front, OperationSpecies, PortedOperationComplex};
use crate::receiver_current::{ExactReceiverCurrentLaw, ExactReceiverCurrentPassage, ReceiverCurrentPassageId, ReceiverCurrentSiteId};
use crate::approach_front::ApproachFront;
use crate::resident_section::{
    CouplingPlan, LawShape, ObstructionLineage, ResidentGrain, ResidentPassage, ResidentRefusal, ResidentSection, ResidentSurface, Schedule,
    SlotReading, StagedWords, TransferCensus, SLOT_WORDS, WORD_OCTAVES,
};
use crate::source_occurrence::{BindingValidation, OccurrenceWitness, SourceRefusal};
use crate::traversible_chain::{found, Admittance, Crossing, Standing as ChainStanding};
use mount::{GraphCensus, Stream};

pub use crate::resident_law::{
    Chronology, CollapseControl, Contact, Contract, Enter, EnteringRows, EntailmentRefusal, GeluTanh, Hadamard, LawEntailment,
    MidpointQuotient, MountedPopulation, PermuteColumns, ReEntry, ResidentLaw, ResidentMaterial, RmsRebase, Scale, SealedMidpointQuotient,
    Standing, WithdrawColumns, WithdrawRows,
};

/// The binding of every occurrence in one complex to its law. **Binds; does not schedule.**
#[derive(Debug, Default)]
pub struct ResidentRealization {
    pub bindings: BTreeMap<EventId, Box<dyn ResidentLaw>>,
}

impl ResidentRealization {
    /// Bind an occurrence to a law; returns the law it displaced, if any.
    pub fn bind(&mut self, occurrence: EventId, law: impl ResidentLaw + 'static) -> Option<Box<dyn ResidentLaw>> {
        self.bindings.insert(occurrence, Box::new(law))
    }

    /// Every occurrence bound, every law's arity and species the diagram's, every input carried by
    /// a bond. The same checks `realization::ReceiverProgram` makes, at this seam.
    pub fn validate(&self, complex: &PortedOperationComplex) -> Result<(), CompileRefusal> {
        complex.shape.validate().map_err(|error| CompileRefusal::Shape(error.to_string()))?;
        for event in complex.shape.occurrences.keys() {
            if !self.bindings.contains_key(event) {
                return Err(CompileRefusal::OccurrenceUnbound { occurrence: *event });
            }
        }
        for event in self.bindings.keys() {
            if !complex.shape.occurrences.contains_key(event) {
                return Err(CompileRefusal::ForeignOccurrence { occurrence: *event });
            }
        }
        let targets: BTreeSet<OccurrencePort> = complex
            .shape
            .interactions
            .values()
            .flat_map(|interaction| &interaction.bonds)
            .map(|bond| bond.target)
            .collect();
        for (event, binding) in &self.bindings {
            let occurrence = &complex.shape.occurrences[event];
            let law = &complex.shape.laws[&occurrence.law];
            let (inputs, outputs) = binding.arity();
            if law.inputs.len() != inputs || law.outputs.len() != outputs {
                return Err(CompileRefusal::ArityDisagrees {
                    occurrence: *event,
                    law_inputs: law.inputs.len(),
                    law_outputs: law.outputs.len(),
                    binding_inputs: inputs,
                    binding_outputs: outputs,
                });
            }
            let declared = complex
                .operations
                .get(&occurrence.law)
                .map(|bound| bound.species)
                .ok_or(CompileRefusal::OccurrenceUnbound { occurrence: *event })?;
            if declared != binding.species() {
                return Err(CompileRefusal::SpeciesDisagrees { occurrence: *event, declared, binding: binding.species() });
            }
            for input in 0..inputs {
                if !targets.contains(&OccurrencePort::input(*event, input)) {
                    return Err(CompileRefusal::InputUncarried { occurrence: *event, input });
                }
            }
        }
        Ok(())
    }
}

/// Why a diagram and realization could not be compiled into a deed. Typed, before any launch.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CompileRefusal {
    Shape(String),
    OccurrenceUnbound { occurrence: EventId },
    ForeignOccurrence { occurrence: EventId },
    ArityDisagrees { occurrence: EventId, law_inputs: usize, law_outputs: usize, binding_inputs: usize, binding_outputs: usize },
    SpeciesDisagrees { occurrence: EventId, declared: OperationSpecies, binding: OperationSpecies },
    InputUncarried { occurrence: EventId, input: usize },
    /// **An unresolved candidate diagram cannot compile.** The closure names the open questions.
    DiagramOpen(DiagramClosure),
    /// The source occurrence refused a binding's testimony — a fabricated symbol, a drifted field,
    /// a wrong shape, a foreign locator, an intervention on a law.
    Source(SourceRefusal),
    /// A law names material the caller did not mount or read.
    MaterialAbsent { occurrence: EventId, name: String },
    /// The validated testimony of an occurrence does not entail the law bound to it — a valid but
    /// unrelated slice, or a parameter no field, shape or slice accounts for.
    Entailment { occurrence: EventId, operation: String, refusal: EntailmentRefusal },
    /// **A declared fusion whose predecessor's face does not factor through it.** A sealing law
    /// rewrites its predecessor's section in place, so the predecessor's own face is gone; §4.6
    /// admits that only when every declared future receiver reads through the fused output.
    /// `because` names which of the three conditions failed and `reopening` names the law to bind
    /// instead, so the refusal carries its own route out.
    FusionUnfactored { quotient: EventId, predecessor: EventId, because: String, reopening: &'static str },
}

impl From<SourceRefusal> for CompileRefusal {
    fn from(refusal: SourceRefusal) -> Self {
        Self::Source(refusal)
    }
}

impl std::fmt::Display for CompileRefusal {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(formatter, "{self:?}")
    }
}

// ---------------------------------------------------------------------------------------------
// obstruction species
// ---------------------------------------------------------------------------------------------

/// Why the deed could not be placed or priced onto the surface. Answered by changing partition,
/// factorization, residency or aperture — never by a magic number and never by a CPU branch.
#[derive(Debug)]
pub enum ResourceObstruction {
    /// A semantic coordinate of the deed exceeds the ceiling the receiver declared for it. Zero
    /// launches and zero allocations were made; the coordinate is named with its ceiling.
    Semantic { coordinate: CoordinateAdmission },
    /// An apparatus coordinate of the deed exceeds what the mounted apparatus admits. Named.
    Apparatus { coordinate: CoordinateAdmission },
    /// The material to be mounted exceeds what the apparatus admits, before any map is allocated.
    Material { coordinate: CoordinateAdmission },
    /// The exact carrier cannot hold what an operation would need, or a launch aperture refused.
    Carrier(ResidentRefusal),
    /// A cell of the front was placed on a chart that carries no semantics here.
    Placement { front: usize, cell: usize, chart: ChartId },
    /// The surface refused: no device, a driver error.
    Surface(ResidentRefusal),
}

/// **The obstruction species the correction directive names, plus the compile refusals that
/// precede them and the on-card refusal that follows.** Nothing here is answered by sequential
/// CPU execution.
#[derive(Debug)]
pub enum FrontPassageObstruction {
    Cover { front: usize, barriers: Vec<CoverBarrier> },
    Interchange { front: usize, because: DistinguishingWord, certificate: Box<FrontCertificate> },
    Resource(ResourceObstruction),
    Compile(CompileRefusal),
    /// The card refused at the named occurrence during the deed — the first refusal in front
    /// order that stands between the entering material and the terminal — with the slot it saw
    /// and the **complete** obstruction lineage of the deed beside it.
    Refused { occurrence: EventId, operation: String, refusal: ResidentRefusal, slot: SlotReading, lineage: ObstructionLineage },
    /// **A face a declared fusion sealed away.** The occurrence's section carries the quotient's
    /// midpoints now; its own pre-quotient enclosure was the apparatus compression the caller
    /// declared. `reopening` names the route back, and it is a recompile rather than a read.
    Sealed { occurrence: EventId, quotient: EventId, reopening: &'static str },
}

impl From<CompileRefusal> for FrontPassageObstruction {
    fn from(refusal: CompileRefusal) -> Self {
        Self::Compile(refusal)
    }
}

impl From<SourceRefusal> for FrontPassageObstruction {
    fn from(refusal: SourceRefusal) -> Self {
        Self::Compile(CompileRefusal::Source(refusal))
    }
}

fn surface_refusal(refusal: ResidentRefusal) -> FrontPassageObstruction {
    FrontPassageObstruction::Resource(ResourceObstruction::Surface(refusal))
}

// ---------------------------------------------------------------------------------------------
// admission — typed, product-ordered, every coordinate bounded or exhibited as unbounded
// ---------------------------------------------------------------------------------------------

/// **What a coordinate is admitted against.** Bounded by a receiver's declaration or by the
/// mounted apparatus; or unbounded, with the reason stated and the apparatus limits that still
/// constrain it named. `None` is not a value of this type.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Ceiling {
    /// A finite ceiling, and who declared it.
    Bounded { ceiling: BigUint, declared_by: &'static str },
    /// No finite ceiling exists for this coordinate at this receiver: why, and what still bounds
    /// it in practice (a device limit, the word, the bus).
    Unbounded { because: &'static str, constrained_by: Vec<&'static str> },
}

/// **One coordinate of the deed, admitted or not.** Required against its ceiling; an unbounded
/// coordinate is admitted by exhibition — it is carried, named and reported, never hidden.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CoordinateAdmission {
    pub name: &'static str,
    pub required: BigUint,
    pub ceiling: Ceiling,
    pub admitted: bool,
}

impl CoordinateAdmission {
    fn bounded(name: &'static str, required: BigUint, ceiling: BigUint, declared_by: &'static str) -> Self {
        let admitted = required <= ceiling;
        Self { name, required, ceiling: Ceiling::Bounded { ceiling, declared_by }, admitted }
    }
    fn unbounded(name: &'static str, required: BigUint, because: &'static str, constrained_by: &[&'static str]) -> Self {
        Self { name, required, ceiling: Ceiling::Unbounded { because, constrained_by: constrained_by.to_vec() }, admitted: true }
    }
    pub fn is_bounded(&self) -> bool {
        matches!(self.ceiling, Ceiling::Bounded { .. })
    }
}

/// **The receiver's declaration over the deed's semantic coordinates**: a finite ceiling per
/// coordinate it chooses to bound, by the names [`ExactWork::coordinates`] returns; every other
/// coordinate is admitted unbounded and the receipt says so. An optional scalar budget
/// ([`WorkBudget`]) prices one more declared coordinate under its metric.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct DeedReceiver {
    pub ceilings: BTreeMap<String, u64>,
    pub scalar: Option<WorkBudget>,
    /// Apertures the receiver declares on apparatus coordinates, by the names the apparatus
    /// admission uses. An aperture can only NARROW what the mounted card admits — the ceiling is
    /// the lesser of the two and the receipt says which it was — so a receiver may bound its own
    /// residency or launches below the device's, never above.
    pub apparatus_apertures: BTreeMap<String, u64>,
}

impl DeedReceiver {
    /// A receiver declaring no ceiling on any semantic coordinate. Lawful: every coordinate is then
    /// exhibited as unbounded with what constrains it, which is what the receipt will say.
    pub fn unbounded() -> Self {
        Self::default()
    }
    pub fn with_ceiling(mut self, coordinate: &str, ceiling: u64) -> Self {
        self.ceilings.insert(coordinate.to_owned(), ceiling);
        self
    }
    pub fn with_scalar(mut self, budget: WorkBudget) -> Self {
        self.scalar = Some(budget);
        self
    }
    pub fn with_apparatus_aperture(mut self, coordinate: &str, aperture: u64) -> Self {
        self.apparatus_apertures.insert(coordinate.to_owned(), aperture);
        self
    }
}

/// What constrains a semantic coordinate when the receiver declares no ceiling on it — the
/// apparatus limit that still bounds it in practice, named so the receipt carries it.
fn semantic_constraints(coordinate: &str) -> &'static [&'static str] {
    match coordinate {
        "additions" | "multiplications" | "divisions" => &["the launch aperture: grid extent × block", "the lanes resident on the device chart"],
        "entries-written" | "resident-entries" => &["the device's free memory (sections are two words per entry)"],
        "cumulative-bits" => &["the device's free memory", "the word: 63 octaves per coordinate"],
        "peak-bits" => &["the word: 63 octaves; admitted per occurrence by the a-priori octave law and refuted on the card by its census"],
        "dependency-span" => &["nothing finite: a longer chain is a longer deed; the graph's depth is its own"],
        "width-weighted-operations" => &["the product of the launch aperture and the word"],
        _ => &["none named"],
    }
}

/// **The apparatus prediction of one deed, before any allocation.** The same coordinates the
/// census measures, so predicted and happened are compared coordinate by coordinate.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct ApparatusPrediction {
    /// Mounted maps, bands and positions the deed reads — resident already, required by the deed.
    pub source_map_octets: u64,
    /// Standings carried in from earlier passages — resident already, released by them.
    pub carried_standing_octets: u64,
    /// Entering codewords staged on the card.
    pub staged_octets: u64,
    /// Every section written: two words per coordinate.
    pub section_octets: u64,
    /// The census array: one slot per occurrence.
    pub census_octets: u64,
    /// The lineage array: every occurrence's predecessor indices.
    pub lineage_octets: u64,
    /// The whole resident requirement of the deed beyond the source maps, as the words sum.
    pub deed_octets: u64,
    /// The same requirement as the card will CHARGE it: every allocation rounded up to the
    /// measured allocation grain.
    pub charged_octets: u64,
    /// The measured allocation grain the charge was rounded to.
    pub allocation_grain: u64,
    /// Every allocation the deed will make, in octets as the words sum — so the charge can be
    /// re-taken under another grain ([`ApparatusPrediction::charged_under`]).
    pub allocation_octets: Vec<u64>,
    pub allocations: u64,
    /// Dynamic shared octets the widest block reduction uses — the deed's scratch.
    pub scratch_octets: u64,
    /// The widest flat launch extent (rows × width) any occurrence issues.
    pub grid_extent: u64,
    /// The widest a-priori octave bound any occurrence is admitted under (capped at the word).
    pub carrier_peak_octaves: u64,
    /// The widest a-priori bound BEFORE the cap, and how many occurrences stood above the word and
    /// were admitted at it — those the census alone decides on the card.
    pub a_priori_peak_octaves_uncapped: u64,
    pub occurrences_admitted_at_the_word: u64,
    /// Kernel launches captured into the graph: semantic and census.
    pub captured_launches: u64,
    /// Within-section reductions realized as named barriers.
    pub reductions: u64,
    pub deed_launches: u64,
    pub synchronizations: u64,
    /// Streams, events, graphs and graph executables the passage holds.
    pub streams: u64,
    pub events: u64,
    pub graphs: u64,
    pub graph_execs: u64,
    pub ingress_octets: u64,
    pub egress_receipt_octets: u64,
    /// The declared terminal's egress: two words per coordinate.
    pub egress_section_octets: u64,
    pub graph_nodes: u64,
    pub graph_edges: u64,
    /// The dependency span of the graph: fronts.
    pub dependency_span: u64,
    /// The grain `2^-F` the remainder is retained at — the retained reconstruction remainder's
    /// finest coordinate.
    pub remainder_grain: u64,
}

fn rounded_to(octets: u64, grain: u64) -> u64 {
    if grain == 0 {
        octets
    } else {
        octets.div_ceil(grain) * grain
    }
}

impl ApparatusPrediction {
    /// **The charge law, re-taken under a declared grain**: every allocation rounded up to it and
    /// summed. Under grain `1` this is the words' own sum; under the measured grain it is
    /// `charged_octets`; under a coarser grain it can only rise. Exhibited so the requirement's
    /// dependence on the grain is a law a caller can check, not a number it must trust.
    pub fn charged_under(&self, grain: u64) -> u64 {
        self.allocation_octets.iter().map(|octets| rounded_to(*octets, grain)).sum()
    }
}

/// **The admission of the whole deed, coordinate by coordinate, taken before any launch or
/// allocation.** Semantic coordinates against the receiver's declaration; apparatus coordinates
/// against the mounted card; the source standing against the cited [`MaterialAdmission`]. The
/// deed is admitted exactly when every bounded coordinate is inside its ceiling — the product
/// order, with nothing summed and no clock.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DeedAdmission {
    pub semantic: Vec<CoordinateAdmission>,
    pub apparatus: Vec<CoordinateAdmission>,
    /// The material admission this deed cites for its source standing, by its resident octets and
    /// the free memory it was admitted against.
    pub cited_material: Option<MaterialAdmission>,
    /// The device's free octets at the instant of admission — the frame the apparatus ceilings
    /// were read in.
    pub free_octets_at_admission: u64,
}

impl DeedAdmission {
    pub fn is_admitted(&self) -> bool {
        self.semantic.iter().chain(self.apparatus.iter()).all(|c| c.admitted)
    }
    /// The first coordinate that refused, semantic before apparatus.
    pub fn refusing(&self) -> Option<(&'static str, &CoordinateAdmission)> {
        self.semantic.iter().find(|c| !c.admitted).map(|c| ("semantic", c)).or_else(|| self.apparatus.iter().find(|c| !c.admitted).map(|c| ("apparatus", c)))
    }
    pub fn bounded(&self) -> impl Iterator<Item = &CoordinateAdmission> {
        self.semantic.iter().chain(self.apparatus.iter()).filter(|c| c.is_bounded())
    }
    pub fn unbounded(&self) -> impl Iterator<Item = &CoordinateAdmission> {
        self.semantic.iter().chain(self.apparatus.iter()).filter(|c| !c.is_bounded())
    }
}

/// **What the caller intends to mount**: every stored map by name, rows and width, plus the band
/// elements and positions — declared from the container's header before any octet is read.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct MaterialPlan {
    /// `(name, rows, width)` of each map to be mounted through the BF16 mouth.
    pub maps: Vec<(String, usize, usize)>,
    pub band_elements: usize,
    pub positions: usize,
}

/// The prediction of the material deed: what mounting the plan will occupy and move.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct MaterialPrediction {
    /// Per map: name, resident octets (the aligned i64 form), stored octets crossing the bus.
    pub maps: Vec<(String, u64, u64)>,
    pub resident_octets: u64,
    /// Stored octets crossing the bus: two per entry.
    pub ingress_octets: u64,
    /// The transient peak beyond the resident: the largest map's stored staging while it aligns.
    pub transient_peak_octets: u64,
    pub allocations: u64,
    pub charged_octets: u64,
    pub allocation_grain: u64,
}

/// **The admission of the material deed**, before any map is allocated. The active deed cites it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MaterialAdmission {
    pub prediction: MaterialPrediction,
    pub coordinates: Vec<CoordinateAdmission>,
    pub free_octets_at_admission: u64,
}

impl MaterialAdmission {
    pub fn is_admitted(&self) -> bool {
        self.coordinates.iter().all(|c| c.admitted)
    }
    /// The admitted resident standing the deed may cite.
    pub fn resident_octets(&self) -> u64 {
        self.prediction.resident_octets
    }
    /// **Reconcile** the prediction with what was mounted: per map, predicted against measured
    /// resident octets. A mismatch is a refuted prediction and is returned, never hidden.
    pub fn reconcile(&self, material: &ResidentMaterial<'_>) -> Vec<(String, u64, u64)> {
        self.prediction
            .maps
            .iter()
            .map(|(name, predicted, _)| (name.clone(), *predicted, material.populations.get(name).map(|p| p.readout.resident_octets() as u64).unwrap_or(0)))
            .collect()
    }
}

// ---------------------------------------------------------------------------------------------
// receipts
// ---------------------------------------------------------------------------------------------

/// The cover's reading of one front: which charts received cells and what stood idle.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CoverReading {
    pub occupied: BTreeSet<ChartId>,
    pub device_cells: usize,
    pub cpu_cells: usize,
    pub idle_lanes: BigUint,
    pub members: BigUint,
    pub occupied_lanes: BigUint,
}

/// **A named within-section coupling, typed and completed by the deed**: the plan (kernel, extent,
/// block, predicted work) and the census that proves the reduction ran and what it wrote.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CouplingReceipt {
    pub plan: CouplingPlan,
    pub occurrence: EventId,
    pub output: OccurrencePort,
    pub inputs: Vec<OccurrencePort>,
    /// The census kernel's marker: the occurrence's kernels ran and were measured.
    pub written: bool,
    pub measured_octave: u32,
    pub measured_width: u64,
    pub refused: u32,
    /// The contact's greatest reach, where the coupling is a contact reduction.
    pub reach: u32,
}

/// The measured against the predicted, per occurrence.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MemberReading {
    pub occurrence: EventId,
    pub operation: &'static str,
    /// The a-priori octave bound the occurrence was admitted under.
    pub bound: u32,
    pub needed: u32,
    pub measured: SlotReading,
}

/// **The bound receipt of one front**: certificate, cover, couplings named, prediction — taken
/// before any launch. The deed completes it with [`FrontDeedReading`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FrontReceipt {
    pub depth: usize,
    pub members: Vec<(EventId, &'static str)>,
    pub certificate: FrontCertificate,
    /// Every member's footprint as the certificate was derived from it: the sections and material
    /// it reads, the predecessor slots and lineage list it reads, its own section and slot it
    /// writes. Retained so the certificate's premise is inspectable, not trusted.
    pub footprints: Vec<MemberFootprint>,
    /// Per member, in `members` order: the predecessor slot ranges its kernel reads and the slot
    /// range it writes — the census-slot part of the footprint, named.
    pub slot_footprints: Vec<(Vec<(u64, u64)>, (u64, u64))>,
    pub cover: CoverReading,
    pub couplings: Vec<CouplingReceipt>,
    pub predicted: ExactWork,
}

/// One front-to-front junction read as a crossing: the arriving lanes meet the next front's lanes.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct JunctionReading {
    pub from_depth: usize,
    pub to_depth: usize,
    pub incident_lanes: u64,
    pub transmitted_lanes: u64,
    pub transmission: Rat,
    pub reflection: Rat,
    pub power_transmission: Rat,
}

/// **The traffic reading of the passage** — composed from the standing owners and reported beside
/// the deed. It reports; it never routes.
///
/// * `hardware_cover`: the lanes each front occupies on the device chart and the lanes left idle.
/// * `receiver_current`: the diagram itself as a passage ecology — sites are occurrences, passages
///   are the diagram's bonds with characteristic delay one, one deed current radiated from the
///   entering occurrences within the diagram's own span. Its law is the EARLIEST section: the first
///   arrival at a site is caused and every later arrival is retained as deferred testimony. On the
///   layer that reads: the residual stream reaches the terminal in four hops, and the transforming
///   chains — attention, gated passage, per-layer input — arrive later and stand as the deferred
///   population, which is `approach_front`'s object. The graph itself waits for all of them.
/// * `traversible_chain`: each front-to-front junction as an admittance crossing — the lanes the
///   current arrives carrying meet the lanes the next front admits — with the transfer matrix
///   composed along the chain, so the whole passage's transmission, reflection and power share are
///   returned as ratios: the traffic system's refraction at the neck, read at every boundary.
/// * the device's own rounds: `⌈lanes / resident lanes⌉` per front, the one-sided service law.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TrafficReading {
    pub resident_lanes: u64,
    /// Per front: depth, occupied lanes, idle lanes, service rounds against the device.
    pub fronts: Vec<(usize, u64, u64, u64)>,
    /// The chronology of the earliest section reaching the terminal.
    pub earliest_arrival: u64,
    /// The exact population of routes arriving with that earliest section.
    pub earliest_routes: BigUint,
    /// Later arrivals retained past the earliest section: their count and their summed
    /// population — the approach front.
    pub deferred_arrivals: usize,
    pub deferred_population: BigUint,
    /// Occurrences with two or more distinct producers: where the diagram reconverges.
    pub reconvergent_sites: usize,
    pub junctions: Vec<JunctionReading>,
    /// The composed chain's transmission, reflection and power share, when every junction crossed.
    pub composite: Option<(Rat, Rat, Rat)>,
}

/// **What one deed returned** — the measured half. What was bound (predictions, admission, mode,
/// certificates, cover, traffic, source bindings) stands on the [`CompiledPassage`] and is not
/// copied per deed. The deed is returned whole even when the card refused somewhere: the complete
/// obstruction lineage is the return, and [`CompiledPassage::read_terminal`] refuses to read a
/// section that did not stand.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PassageReturn {
    /// Per front, in the diagram's order: every member's reading and every coupling completed.
    pub fronts: Vec<FrontDeedReading>,
    pub census_before: TransferCensus,
    pub census_after: TransferCensus,
    /// What each port measured after it was written; beside the bound passage's a-priori field so
    /// the law is refutable port by port.
    pub measured_octaves: BTreeMap<OccurrencePort, u32>,
    /// **The complete obstruction lineage of the deed**, by occurrence: every refusal, whether it
    /// originated there or was carried, and from which predecessor.
    pub obstruction: ObstructionLineage,
    /// Every refusal typed and named for its occurrence, in front order.
    pub refusals: Vec<(EventId, &'static str, SlotReading)>,
}

impl PassageReturn {
    /// Whether every occurrence stood.
    pub fn stands(&self) -> bool {
        self.obstruction.is_empty()
    }
}

/// One front's measured half after a deed.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FrontDeedReading {
    pub depth: usize,
    pub readings: Vec<MemberReading>,
    pub couplings: Vec<CouplingReceipt>,
}

// ---------------------------------------------------------------------------------------------
// the plan
// ---------------------------------------------------------------------------------------------

/// One occurrence, resolved: its law, its inputs' producers, its shape and price, and the a-priori
/// bound on its output.
struct Plan<'a> {
    index: usize,
    occurrence: EventId,
    depth: usize,
    law: &'a dyn ResidentLaw,
    inputs: Vec<OccurrencePort>,
    producers: Vec<usize>,
    shape: LawShape,
    bound: u32,
}

/// The whole passage, compiled: everything the deed needs, priced; nothing allocated on the card.
pub struct CompiledPlan<'a> {
    plans: Vec<Plan<'a>>,
    fronts: Vec<Front>,
    pub deed_prediction: ExactWork,
    pub apparatus_prediction: ApparatusPrediction,
    pub octave_field: BTreeMap<OccurrencePort, u32>,
    pub source_bindings: Vec<BindingValidation>,
    /// Per occurrence: how its law's parameters are entailed by the validated testimony.
    pub entailments: Vec<(EventId, LawEntailment)>,
    pub closure: DiagramClosure,
    terminal: EventId,
    grain: ResidentGrain,
}

impl CompiledPlan<'_> {
    pub fn occurrences(&self) -> usize {
        self.plans.len()
    }
    pub fn fronts(&self) -> &[Front] {
        &self.fronts
    }
    /// **The exact work of one occurrence, borrowed from the shape it was priced under.**
    ///
    /// Read-only, and it changes nothing: `LawShape::predicted` was already computed by the law and
    /// already summed into `deed_prediction` and into each front's `FrontReceipt::predicted`. What
    /// was missing was any way to *read* it per occurrence — H0's exact-work artifact records the
    /// absence in its own text, and had to report per-front and per-coupling instead. The plan owns
    /// the shapes, so the accessor belongs here; the passage consumes the plan and never held them.
    ///
    /// It returns an iterator rather than a population, so reading the work materializes nothing:
    /// the caller decides whether it wants a body, exactly as `receiver_current::sites` does.
    pub fn occurrence_work(&self) -> impl Iterator<Item = (EventId, &ExactWork)> {
        self.plans
            .iter()
            .map(|plan| (plan.occurrence, &plan.shape.predicted))
    }
}

/// The passage over one surface at one grain, under one schedule.
pub struct FrontPassage<'chart> {
    pub surface: &'chart ResidentSurface<'chart>,
    pub grain: ResidentGrain,
    /// How the kernels are ordered beyond the diagram's bonds. [`Schedule::Serialized`] is the
    /// control: a total order over the same kernels must return the same complete receipt.
    pub schedule: Schedule,
    /// Open each front's members in reverse order — another legal completion order of the same
    /// diagram, meaningful under the serialized schedule.
    pub reverse_fronts: bool,
    /// **The faces the receiver declared it will read**, beside the terminal. A declared face is a
    /// future receiver, so an occurrence in this set may not have its section fused away by a
    /// sealing successor: [`FrontPassage::compile`] refuses the fusion by name and the reopening
    /// route is the unfused law. Empty by default, which is the strictest reading of "no receiver
    /// declared anything but the terminal" — a caller that will read further faces must say so.
    pub declared_faces: BTreeSet<EventId>,
}

impl<'chart> FrontPassage<'chart> {
    pub fn new(surface: &'chart ResidentSurface<'chart>, grain: ResidentGrain) -> Self {
        Self { surface, grain, schedule: Schedule::CoPresent, reverse_fronts: false, declared_faces: BTreeSet::new() }
    }

    /// The serialized-realization control over the same diagram.
    pub fn serialized(surface: &'chart ResidentSurface<'chart>, grain: ResidentGrain) -> Self {
        Self { surface, grain, schedule: Schedule::Serialized, reverse_fronts: false, declared_faces: BTreeSet::new() }
    }

    /// The serialized control with every front opened in reverse member order.
    pub fn serialized_reversed(surface: &'chart ResidentSurface<'chart>, grain: ResidentGrain) -> Self {
        Self { surface, grain, schedule: Schedule::Serialized, reverse_fronts: true, declared_faces: BTreeSet::new() }
    }

    /// **Declare the faces this receiver will read**, beside the terminal. Every occurrence named
    /// here keeps its own section: a sealing successor over one of them refuses at compile.
    pub fn reading(mut self, faces: impl IntoIterator<Item = EventId>) -> Self {
        self.declared_faces.extend(faces);
        self
    }

    /// The dataflow: every bond indexed by the port it carries to.
    fn arriving(complex: &PortedOperationComplex) -> BTreeMap<OccurrencePort, OccurrencePort> {
        let mut arriving = BTreeMap::new();
        for interaction in complex.shape.interactions.values() {
            for bond in &interaction.bonds {
                arriving.insert(bond.target, bond.source);
            }
        }
        arriving
    }

    /// **Who reads each occurrence**, read off the same bonds `arriving` reads: every bond's source
    /// occurrence to the occurrences its output carries into. This is how a declared fusion's
    /// condition — *the predecessor's only consumer is the quotient* — is decided from the diagram
    /// at compile rather than hoped for at run time.
    fn consumers(complex: &PortedOperationComplex) -> BTreeMap<EventId, BTreeSet<EventId>> {
        let mut consumers: BTreeMap<EventId, BTreeSet<EventId>> = BTreeMap::new();
        for interaction in complex.shape.interactions.values() {
            for bond in &interaction.bonds {
                consumers.entry(bond.source.event).or_default().insert(bond.target.event);
            }
        }
        consumers
    }

    /// The members of each front in the order this passage opens them.
    fn ordered<'p, 'a>(&self, members: &'p [&'p Plan<'a>]) -> Vec<&'p Plan<'a>> {
        let mut ordered: Vec<&Plan<'a>> = members.to_vec();
        if self.reverse_fronts {
            ordered.reverse();
        }
        ordered
    }

    /// The bound a law puts on the octaves of its output words, clamped to the word, with the
    /// uncapped bound beside it.
    fn bound_octaves(&self, law: &dyn ResidentLaw, input_octaves: &[u32], material: &ResidentMaterial<'chart>) -> (u32, u32) {
        let bound = law.bound_octaves(self.grain, input_octaves, material);
        let uncapped = u32::try_from(bound.max(1)).unwrap_or(u32::MAX);
        // A written word occupies at most the signed word: a bound past it is a bound on nothing,
        // and a value past it is refused on the card by name. The occurrence is admitted AT the
        // word, and the receipt exhibits that its a-priori bound stood above it, so the admission
        // says which occurrences the census alone decides.
        (uncapped.min(WORD_OCTAVES), uncapped)
    }

    // -----------------------------------------------------------------------------------------
    // the material deed: predicted and admitted before any map is allocated
    // -----------------------------------------------------------------------------------------

    /// **Predict the material deed** from the container's declared shapes, before any octet is
    /// read: the aligned residency of every map (`rows × width × 8`), the stored octets that will
    /// cross (`× 2`), the transient staging peak, the allocations, and the charge at the measured
    /// grain.
    pub fn predict_material(&self, plan: &MaterialPlan) -> MaterialPrediction {
        let grain = self.surface.allocation_grain();
        let mut prediction = MaterialPrediction { allocation_grain: grain, ..Default::default() };
        for (name, rows, width) in &plan.maps {
            let entries = (*rows as u64) * (*width as u64);
            let resident = entries * 8;
            let stored = entries * 2;
            prediction.maps.push((name.clone(), resident, stored));
            prediction.resident_octets += resident;
            prediction.ingress_octets += stored;
            prediction.transient_peak_octets = prediction.transient_peak_octets.max(stored + 16 + 2 * rows.max(&1).to_owned() as u64 * 16);
            prediction.allocations += 1;
            prediction.charged_octets += rounded_to(resident, grain);
        }
        if plan.band_elements > 0 {
            let octets = (plan.band_elements * 4 * 8) as u64;
            prediction.resident_octets += octets;
            prediction.ingress_octets += octets;
            prediction.allocations += 4;
            prediction.charged_octets += 4 * rounded_to(octets / 4, grain);
        }
        if plan.positions > 0 {
            let octets = (plan.positions * 4) as u64;
            prediction.resident_octets += octets;
            prediction.ingress_octets += octets;
            prediction.allocations += 1;
            prediction.charged_octets += rounded_to(octets, grain);
        }
        prediction
    }

    /// **Predict a POOLED material deed**: standing slots admitted once and rewritten between
    /// deeds, rather than one mount allocated and released per deed.
    ///
    /// The difference from [`FrontPassage::predict_material`] is exactly where the stored
    /// codewords sit. In the per-deed path they are a **transient** staging that exists only while
    /// one map aligns, so the prediction carries the largest of them as a peak beyond the resident
    /// standing. In the pooled path the stored region is part of the slot and stays for the life
    /// of the circulation, so it is **resident** and the transient peak is zero — there is no
    /// moment at which the pool holds more than it was admitted for.
    ///
    /// `ingress_octets` is the whole tower's crossing, not one slot's: a slot is refilled once per
    /// segment and the caller declares how many segments each slot carries.
    pub fn predict_pooled_material(&self, slots: &[crate::streamed_standing::SlotShape], refills: &[u64], band_elements: usize, positions: usize) -> MaterialPrediction {
        let grain = self.surface.allocation_grain();
        let mut prediction = MaterialPrediction { allocation_grain: grain, ..Default::default() };
        for (which, slot) in slots.iter().enumerate() {
            let octets = slot.octets() as u64;
            prediction.maps.push((slot.name.clone(), octets, slot.stored_octets as u64));
            prediction.resident_octets += octets;
            prediction.ingress_octets += slot.stored_octets as u64 * refills.get(which).copied().unwrap_or(1);
            prediction.allocations += 1;
            prediction.charged_octets += rounded_to(octets, grain);
        }
        if band_elements > 0 {
            let octets = (band_elements * 4 * 8) as u64;
            prediction.resident_octets += octets;
            prediction.ingress_octets += octets;
            prediction.allocations += 4;
            prediction.charged_octets += 4 * rounded_to(octets / 4, grain);
        }
        if positions > 0 {
            let octets = (positions * 4) as u64;
            prediction.resident_octets += octets;
            prediction.ingress_octets += octets;
            prediction.allocations += 1;
            prediction.charged_octets += rounded_to(octets, grain);
        }
        prediction
    }

    /// **Admit the material deed** against the device's free memory now, before any map is
    /// allocated: the charged residency plus the transient peak must fit. A refusal names the
    /// coordinate; nothing was allocated.
    pub fn admit_material(&self, prediction: &MaterialPrediction) -> Result<MaterialAdmission, FrontPassageObstruction> {
        let free = self.surface.memory().map_err(surface_refusal)?.free_bytes as u64;
        let coordinates = vec![
            CoordinateAdmission::bounded("material-charged-octets", BigUint::from(prediction.charged_octets), BigUint::from(free), "the device's free memory at admission"),
            CoordinateAdmission::bounded("material-peak-octets", BigUint::from(prediction.charged_octets + prediction.transient_peak_octets), BigUint::from(free), "the device's free memory at admission"),
            CoordinateAdmission::unbounded("material-ingress-octets", BigUint::from(prediction.ingress_octets), "stored octets crossing the bus once; no finite ceiling is declared", &["the bus"]),
            CoordinateAdmission::unbounded("material-allocations", BigUint::from(prediction.allocations), "the driver publishes no finite allocation count", &["the device's free memory"]),
            CoordinateAdmission::unbounded("material-allocation-grain", BigUint::from(prediction.allocation_grain), "a measured apparatus constant, exhibited", &["the card's own charge law"]),
        ];
        let admission = MaterialAdmission { prediction: prediction.clone(), coordinates, free_octets_at_admission: free };
        if let Some(coordinate) = admission.coordinates.iter().find(|c| !c.admitted) {
            return Err(FrontPassageObstruction::Resource(ResourceObstruction::Material { coordinate: coordinate.clone() }));
        }
        Ok(admission)
    }

    // -----------------------------------------------------------------------------------------
    // compile, admit, realize
    // -----------------------------------------------------------------------------------------

    /// **Compile**: validate the realization, close the diagram, validate every binding's testimony
    /// against the source occurrence, check the material, and derive every occurrence's shape,
    /// price and a-priori bound — then price the WHOLE deed, semantic and apparatus. No launch, no
    /// allocation on the card.
    pub fn compile<'a>(
        &self,
        complex: &PortedOperationComplex,
        realization: &'a ResidentRealization,
        material: &ResidentMaterial<'chart>,
        source: &dyn OccurrenceWitness,
        terminal: EventId,
    ) -> Result<CompiledPlan<'a>, FrontPassageObstruction> {
        realization.validate(complex)?;
        let closure = complex.closure().map_err(|error| CompileRefusal::Shape(error.to_string()))?;
        if !closure.is_closed() {
            return Err(CompileRefusal::DiagramOpen(closure).into());
        }
        let source_bindings = source.validate(complex)?;
        // Every occurrence's law must be ENTAILED by the validated testimony of its operation: a
        // resolved slice names the operation and every parameter is accounted for by a field, a
        // shape or a slice. Validation says the testimony is real; entailment says it is THIS law's.
        let mut entailments: Vec<(EventId, LawEntailment)> = Vec::with_capacity(realization.bindings.len());
        for (occurrence, law) in &realization.bindings {
            if let Err(name) = law.material(material) {
                return Err(CompileRefusal::MaterialAbsent { occurrence: *occurrence, name }.into());
            }
            let operation = complex
                .shape
                .occurrences
                .get(occurrence)
                .and_then(|o| complex.shape.laws.get(&o.law))
                .map(|l| l.name.clone())
                .ok_or(CompileRefusal::OccurrenceUnbound { occurrence: *occurrence })?;
            let validation = source_bindings.iter().find(|v| v.operation == operation).ok_or(CompileRefusal::OccurrenceUnbound { occurrence: *occurrence })?;
            // An occurrence that is WHOLLY the caller's intervention — intervention testimony and
            // nothing exterior — is entailed by its declaration whatever its law: the matched
            // sibling's rebase, permutation or replacement is the caller's and says so.
            let wholly_intervention = !validation.interventions.is_empty() && validation.symbols.is_empty() && validation.fields.is_empty() && validation.shapes.is_empty();
            if wholly_intervention {
                entailments.push((*occurrence, LawEntailment { law: law.name(), parameters: vec![("intervention".to_owned(), law.name().to_owned(), format!("the caller's typed intervention: {}", validation.interventions.join(" | ")))], naming_slices: Vec::new() }));
                continue;
            }
            match law.entailment(validation) {
                Ok(entailment) => entailments.push((*occurrence, entailment)),
                Err(refusal) => return Err(CompileRefusal::Entailment { occurrence: *occurrence, operation, refusal }.into()),
            }
        }
        if !complex.shape.occurrences.contains_key(&terminal) {
            return Err(CompileRefusal::ForeignOccurrence { occurrence: terminal }.into());
        }
        let fronts = complex.fronts().map_err(|error| CompileRefusal::Shape(error.to_string()))?;
        let arriving = Self::arriving(complex);
        let consumers = Self::consumers(complex);

        // Every occurrence, in front order: shape, price, bound.
        let mut plans: Vec<Plan<'a>> = Vec::with_capacity(complex.shape.occurrences.len());
        let mut index_of: BTreeMap<EventId, usize> = BTreeMap::new();
        let mut field: BTreeMap<OccurrencePort, (usize, usize, u32)> = BTreeMap::new();
        let mut deed = ExactWork::nothing();
        let mut apparatus = ApparatusPrediction::default();
        let mut section_octets = 0u64;
        let grain = self.surface.allocation_grain();
        let mut charged = 0u64;
        let mut allocation_octets: Vec<u64> = Vec::new();
        for front in &fronts {
            let mut front_work = ExactWork::nothing();
            for occurrence in &front.occurrences {
                let law: &'a dyn ResidentLaw = realization.bindings.get(occurrence).ok_or(CompileRefusal::OccurrenceUnbound { occurrence: *occurrence })?.as_ref();
                let (inputs_count, _) = law.arity();
                let mut inputs = Vec::with_capacity(inputs_count);
                let mut producers = Vec::with_capacity(inputs_count);
                for input in 0..inputs_count {
                    let port = OccurrencePort::input(*occurrence, input);
                    let source_port = arriving.get(&port).copied().ok_or(CompileRefusal::InputUncarried { occurrence: *occurrence, input })?;
                    let producer = index_of.get(&source_port.event).copied().ok_or(CompileRefusal::InputUncarried { occurrence: *occurrence, input })?;
                    inputs.push(source_port);
                    producers.push(producer);
                }
                // **The fusion's condition, decided from the diagram.** A sealing law rewrites its
                // predecessor's section in place, so that section's face is gone after the deed.
                // §4.6 admits the fusion only when every declared future receiver factors through
                // the fused output, and that is exactly three readings of the diagram: the
                // predecessor is read by this occurrence and by nothing else; it is not the declared
                // terminal; and the receiver did not declare its face. The refusal names which one
                // failed and the law to bind instead.
                if law.seals_predecessor() {
                    let predecessor = inputs[0].event;
                    let because = seal_unfactored(
                        &consumers,
                        *occurrence,
                        predecessor,
                        terminal,
                        &self.declared_faces,
                        realization.bindings.get(&predecessor).map(|l| l.seals_predecessor()).unwrap_or(false),
                    );
                    if let Some(because) = because {
                        return Err(CompileRefusal::FusionUnfactored {
                            quotient: *occurrence,
                            predecessor,
                            because,
                            reopening: "bind MidpointQuotient instead: the pair runs as two nodes, the predecessor keeps its own section, and its enclosure is censused and readable",
                        }
                        .into());
                    }
                }
                let shapes: Vec<(usize, usize, u32)> = inputs.iter().map(|port| field.get(port).copied().unwrap_or((0, 0, 0))).collect();
                let octaves: Vec<u32> = shapes.iter().map(|(_, _, o)| *o).collect();
                let (bound, uncapped) = self.bound_octaves(law, &octaves, material);
                if uncapped > WORD_OCTAVES {
                    apparatus.occurrences_admitted_at_the_word += 1;
                }
                apparatus.a_priori_peak_octaves_uncapped = apparatus.a_priori_peak_octaves_uncapped.max(u64::from(uncapped));
                let shape = law.shape(self.surface, self.grain, &shapes, material).map_err(|refusal| FrontPassageObstruction::Resource(ResourceObstruction::Carrier(refusal)))?;
                field.insert(OccurrencePort::output(*occurrence, 0), (shape.rows, shape.width, bound));
                front_work = co_present(&front_work, &shape.predicted);
                // A sealing occurrence carries no section of its own: its words ARE its
                // predecessor's, rewritten in place. Nothing is allocated and nothing is charged for
                // it, which is the second half of the apparatus compression and is predicted here.
                if !law.seals_predecessor() {
                    let section = (shape.rows * shape.width * 8) as u64;
                    section_octets += 2 * section;
                    charged += 2 * rounded_to(section.max(8), grain);
                    allocation_octets.push(section.max(8));
                    allocation_octets.push(section.max(8));
                    apparatus.allocations += 2;
                }
                apparatus.captured_launches += u64::from(shape.launches);
                apparatus.reductions += shape.couplings.len() as u64;
                apparatus.scratch_octets = apparatus.scratch_octets.max(u64::from(shape.shared_octets));
                apparatus.grid_extent = apparatus.grid_extent.max((shape.rows * shape.width) as u64);
                apparatus.carrier_peak_octaves = apparatus.carrier_peak_octaves.max(u64::from(bound));
                let index = plans.len();
                index_of.insert(*occurrence, index);
                plans.push(Plan { index, occurrence: *occurrence, depth: front.depth, law, inputs, producers, shape, bound });
            }
            deed = deed.then(&front_work);
        }
        deed.dependency_span = BigUint::from(fronts.len() as u64);

        // The apparatus prediction: what the deed will occupy, move and issue.
        let mut staged_octets = 0u64;
        let mut staged_names: BTreeSet<&str> = BTreeSet::new();
        for plan in &plans {
            if let Some(population) = plan.law.stages() {
                if staged_names.insert(population) {
                    if let Some(entering) = material.entering.get(population) {
                        let octets = (entering.words.len() * 2) as u64;
                        staged_octets += octets;
                        charged += rounded_to(octets.max(2), grain);
                        allocation_octets.push(octets.max(2));
                    }
                }
            }
        }
        let entering_count = staged_names.len() as u64;
        let census_octets = (SLOT_WORDS * plans.len().max(1) * 4) as u64;
        let lineage_words: usize = plans
            .iter()
            .map(|plan| {
                let mut distinct: Vec<usize> = plan.producers.clone();
                distinct.sort_unstable();
                distinct.dedup();
                distinct.len()
            })
            .sum();
        let lineage_octets = (lineage_words.max(1) * 4) as u64;
        charged += rounded_to(census_octets, grain) + rounded_to(lineage_octets, grain);
        allocation_octets.push(census_octets);
        allocation_octets.push(lineage_octets);
        let terminal_plan = plans.iter().find(|plan| plan.occurrence == terminal).ok_or(CompileRefusal::ForeignOccurrence { occurrence: terminal })?;
        apparatus.source_map_octets = material.resident_octets();
        apparatus.carried_standing_octets = material.standings_octets();
        apparatus.staged_octets = staged_octets;
        apparatus.section_octets = section_octets;
        apparatus.census_octets = census_octets;
        apparatus.lineage_octets = lineage_octets;
        apparatus.deed_octets = staged_octets + section_octets + census_octets + lineage_octets;
        apparatus.charged_octets = charged;
        apparatus.allocation_grain = grain;
        apparatus.allocation_octets = allocation_octets;
        apparatus.allocations += entering_count + 2;
        apparatus.deed_launches = 1;
        apparatus.synchronizations = 1;
        apparatus.streams = plans.len() as u64 + 1;
        apparatus.events = plans.len() as u64 + 1;
        apparatus.graphs = 1;
        apparatus.graph_execs = 1;
        apparatus.ingress_octets = staged_octets + (lineage_words * 4) as u64;
        apparatus.egress_receipt_octets = census_octets;
        apparatus.egress_section_octets = 2 * (terminal_plan.shape.rows * terminal_plan.shape.width * 8) as u64;
        // One node per launch plus the memset: an occurrence whose kernel wrote its own census
        // records one node and no census edge, so both counts move with the declared fusion.
        apparatus.graph_nodes = 1 + plans.iter().map(|plan| u64::from(plan.shape.launches)).sum::<u64>();
        apparatus.graph_edges = plans
            .iter()
            .map(|plan| {
                let mut distinct: Vec<usize> = plan.producers.clone();
                distinct.sort_unstable();
                distinct.dedup();
                (if distinct.is_empty() { 1 } else { distinct.len() as u64 }) + u64::from(!plan.law.fuses_census())
            })
            .sum();
        if self.schedule == Schedule::Serialized {
            // The serialized control orders every occurrence after the one opened before it, in
            // the order this passage opens them.
            let by_depth: BTreeMap<usize, Vec<&Plan<'a>>> = plans.iter().fold(BTreeMap::new(), |mut map, p| {
                map.entry(p.depth).or_default().push(p);
                map
            });
            let mut previous: Option<usize> = None;
            let mut extra = 0u64;
            for front in &fronts {
                let members: Vec<&Plan<'a>> = by_depth.get(&front.depth).cloned().unwrap_or_default();
                for p in self.ordered(&members) {
                    if let Some(prev) = previous {
                        if !p.producers.contains(&prev) {
                            extra += 1;
                        }
                    }
                    previous = Some(p.index);
                }
            }
            apparatus.graph_edges += extra;
        }
        apparatus.dependency_span = fronts.len() as u64;
        apparatus.remainder_grain = u64::from(self.grain.0);
        let octave_field = field.into_iter().map(|(port, (_, _, o))| (port, o)).collect();
        Ok(CompiledPlan {
            plans,
            fronts,
            deed_prediction: deed,
            apparatus_prediction: apparatus,
            octave_field,
            source_bindings,
            entailments,
            closure,
            terminal,
            grain: self.grain,
        })
    }

    /// **Admit the whole deed, coordinate by coordinate**: every semantic coordinate against the
    /// receiver's declaration — bounded where declared, exhibited as unbounded with what still
    /// constrains it where not — and every apparatus coordinate against the mounted card, with the
    /// source standing cited from the material admission. Taken before any allocation. The deed is
    /// admitted exactly when every bounded coordinate is inside its ceiling; the first refusing
    /// coordinate is returned typed and named.
    pub fn admit(&self, plan: &CompiledPlan<'_>, receiver: &DeedReceiver, material: Option<&MaterialAdmission>) -> Result<DeedAdmission, FrontPassageObstruction> {
        let free = self.surface.memory().map_err(surface_refusal)?.free_bytes as u64;
        let declaration = self.surface.declaration();
        let (_, max_grid, _) = self.surface.derived_launch();
        // semantic
        let mut semantic = Vec::new();
        for (name, required) in plan.deed_prediction.coordinates() {
            match receiver.ceilings.get(name) {
                Some(ceiling) => semantic.push(CoordinateAdmission::bounded(name, required, BigUint::from(*ceiling), "the receiver's declared ceiling")),
                None => semantic.push(CoordinateAdmission::unbounded(name, required, "the receiver declared no ceiling on this coordinate", semantic_constraints(name))),
            }
        }
        if let Some(budget) = &receiver.scalar {
            let priced = budget.metric.price(&plan.deed_prediction);
            semantic.push(CoordinateAdmission::bounded("scalar-price-under-declared-metric", priced, budget.ceiling.clone(), "the receiver's declared scalar budget"));
        }
        // apparatus
        let a = &plan.apparatus_prediction;
        let mut apparatus = vec![
            CoordinateAdmission::bounded("carrier-peak-octaves", BigUint::from(a.carrier_peak_octaves), BigUint::from(u64::from(WORD_OCTAVES)), "the signed word the section is stored in (the a-priori bound is capped here; see the two coordinates below)"),
            CoordinateAdmission::unbounded("a-priori-peak-octaves-uncapped", BigUint::from(a.a_priori_peak_octaves_uncapped), "the widest a-priori bound before the cap at the word; where it exceeds the word the occurrence is admitted at the word and its census refuses on the card", &["the word: 63 octaves, enforced by the census and by CarrierLeft on the card"]),
            CoordinateAdmission::unbounded("occurrences-admitted-at-the-word", BigUint::from(a.occurrences_admitted_at_the_word), "occurrences whose a-priori bound stood above the word; the census alone decides them", &["the word"]),
            CoordinateAdmission::bounded("charged-resident-octets", BigUint::from(a.charged_octets), BigUint::from(free), "the device's free memory at admission"),
            CoordinateAdmission::bounded("scratch-octets", BigUint::from(a.scratch_octets), BigUint::from(u64::from(declaration.max_sectiond_bytes)), "the device's shared memory per block"),
            CoordinateAdmission::bounded("grid-extent", BigUint::from(a.grid_extent), BigUint::from(u64::from(max_grid)) * BigUint::from(u64::from(self.surface.derived_launch().0)), "the launch aperture: grid ceiling × block"),
            CoordinateAdmission::unbounded("resident-octets-as-words-sum", BigUint::from(a.deed_octets), "the words' own sum, beside the charge the card levies", &["the charged residency above"]),
            CoordinateAdmission::unbounded("staged-octets", BigUint::from(a.staged_octets), "entering material crossing once; inside the charged residency", &["the charged residency above"]),
            CoordinateAdmission::unbounded("census-octets", BigUint::from(a.census_octets), "one slot per occurrence; inside the charged residency", &["the charged residency above"]),
            CoordinateAdmission::unbounded("lineage-octets", BigUint::from(a.lineage_octets), "the diagram's bond structure; inside the charged residency", &["the charged residency above"]),
            CoordinateAdmission::unbounded("allocation-grain-octets", BigUint::from(a.allocation_grain), "a measured apparatus constant, exhibited", &["the card's own charge law"]),
            CoordinateAdmission::unbounded("allocations", BigUint::from(a.allocations), "the driver publishes no finite allocation count", &["the device's free memory"]),
            CoordinateAdmission::unbounded("captured-launches", BigUint::from(a.captured_launches), "the driver publishes no finite graph-node count", &["the device's free memory for the graph executable"]),
            CoordinateAdmission::unbounded("reductions", BigUint::from(a.reductions), "within-section barriers, one kernel each; no finite ceiling", &["the launch aperture"]),
            CoordinateAdmission::unbounded("streams", BigUint::from(a.streams), "one lane per occurrence; the driver publishes no finite stream count", &["the device's free memory"]),
            CoordinateAdmission::unbounded("events", BigUint::from(a.events), "one per occurrence; the driver publishes no finite event count", &["the device's free memory"]),
            CoordinateAdmission::unbounded("graphs", BigUint::from(a.graphs), "one per passage", &["the device's free memory"]),
            CoordinateAdmission::unbounded("graph-execs", BigUint::from(a.graph_execs), "one per passage", &["the device's free memory"]),
            CoordinateAdmission::unbounded("graph-nodes", BigUint::from(a.graph_nodes), "one per launch plus the memset; no finite ceiling is published", &["the device's free memory"]),
            CoordinateAdmission::unbounded("graph-edges", BigUint::from(a.graph_edges), "the diagram's bonds; no finite ceiling is published", &["the device's free memory"]),
            CoordinateAdmission::unbounded("dependency-span", BigUint::from(a.dependency_span), "the diagram's depth; nothing finite", &["none"]),
            CoordinateAdmission::unbounded("ingress-octets", BigUint::from(a.ingress_octets), "entering material and the lineage, crossing once", &["the bus"]),
            CoordinateAdmission::unbounded("egress-receipt-octets", BigUint::from(a.egress_receipt_octets), "the census array, read once", &["the bus"]),
            CoordinateAdmission::unbounded("egress-section-octets", BigUint::from(a.egress_section_octets), "the terminal face, read once by the receiver", &["the bus"]),
            CoordinateAdmission::unbounded("retained-remainder-grain", BigUint::from(a.remainder_grain), "the remainder is retained whole at this grain; no ceiling on its width is declared", &["the word: 63 octaves"]),
        ];
        apparatus.push(CoordinateAdmission::unbounded("carried-standing-octets", BigUint::from(a.carried_standing_octets), "standings released by earlier passages, resident already; no ceiling is declared", &["the device's memory"]));
        // the source standing: cited from the material admission, or exhibited as already resident
        match material {
            Some(admitted) => apparatus.push(CoordinateAdmission::bounded("source-standing-octets", BigUint::from(a.source_map_octets), BigUint::from(admitted.resident_octets()), "the cited material admission's admitted resident standing")),
            None => apparatus.push(CoordinateAdmission::unbounded("source-standing-octets", BigUint::from(a.source_map_octets), "no material admission was cited; the standing is already resident and counted", &["the device's memory"])),
        }
        // the receiver's apertures narrow, never widen
        for coordinate in &mut apparatus {
            if let Some(aperture) = receiver.apparatus_apertures.get(coordinate.name) {
                let aperture = BigUint::from(*aperture);
                let (ceiling, declared_by) = match &coordinate.ceiling {
                    Ceiling::Bounded { ceiling, .. } if *ceiling <= aperture => (ceiling.clone(), "the mounted apparatus (the receiver's aperture is wider)"),
                    _ => (aperture, "the receiver's declared apparatus aperture, narrower than the apparatus"),
                };
                coordinate.admitted = coordinate.required <= ceiling;
                coordinate.ceiling = Ceiling::Bounded { ceiling, declared_by };
            }
        }
        let admission = DeedAdmission { semantic, apparatus, cited_material: material.cloned(), free_octets_at_admission: free };
        if let Some((kind, coordinate)) = admission.refusing() {
            return Err(FrontPassageObstruction::Resource(if kind == "semantic" {
                ResourceObstruction::Semantic { coordinate: coordinate.clone() }
            } else {
                ResourceObstruction::Apparatus { coordinate: coordinate.clone() }
            }));
        }
        Ok(admission)
    }

    /// **Realize**: allocate every section and staging buffer, place every front on the surface's
    /// cover, derive every front's certificate from footprints — sections, maps, the occurrence's
    /// own slot written, its predecessors' slots and its lineage list read — name every coupling,
    /// and bind the graph. Nothing launches. Refuses on a cover barrier, an ordered front, or a
    /// placement on the CPU chart, releasing what it allocated.
    pub fn realize<'a>(
        &self,
        plan: CompiledPlan<'a>,
        material: &ResidentMaterial<'chart>,
        admission: DeedAdmission,
    ) -> Result<CompiledPassage<'chart>, FrontPassageObstruction> {
        let surface = self.surface;
        // 1. Sections and staging. A sealing occurrence allocates nothing: its section IS its
        //    predecessor's, and the alias is recorded so every later lookup resolves to one buffer.
        let mut sections: BTreeMap<EventId, ResidentSection<'chart>> = BTreeMap::new();
        let mut sealed: BTreeMap<EventId, EventId> = BTreeMap::new();
        let mut staged: BTreeMap<String, StagedWords<'chart>> = BTreeMap::new();
        for p in &plan.plans {
            if p.law.seals_predecessor() {
                sealed.insert(p.occurrence, p.inputs[0].event);
            } else {
                sections.insert(p.occurrence, surface.fresh_section(p.shape.rows, p.shape.width, plan.grain).map_err(surface_refusal)?);
            }
            if let Some(population) = p.law.stages() {
                if !staged.contains_key(population) {
                    let entering = &material.entering[population];
                    staged.insert(population.to_owned(), surface.stage_words(&entering.words, entering.rows, entering.width).map_err(surface_refusal)?);
                }
            }
        }
        // 2. The capture, opened over the declared lineage; per front: cover, footprints,
        //    certificate, couplings, recording.
        let lineage: Vec<Vec<usize>> = plan.plans.iter().map(|p| p.producers.clone()).collect();
        let mut builder = surface.begin_passage_scheduled(&lineage, self.schedule).map_err(surface_refusal)?;
        let cover = surface.cover();
        let mut receipts: Vec<FrontReceipt> = Vec::with_capacity(plan.fronts.len());
        let mut lane_demand: Vec<(usize, u64, u64)> = Vec::with_capacity(plan.fronts.len());
        let by_depth: BTreeMap<usize, Vec<&Plan<'a>>> = plan.plans.iter().fold(BTreeMap::new(), |mut map, p| {
            map.entry(p.depth).or_default().push(p);
            map
        });
        for (at, front) in plan.fronts.iter().enumerate() {
            let members: Vec<&Plan<'a>> = by_depth.get(&front.depth).cloned().unwrap_or_default();
            // The cover: every member is a cell of its output extent, placed against the device
            // chart's own grain. Semantics live on the device chart only.
            let cells: Vec<FrontCell> = members.iter().enumerate().map(|(index, p)| FrontCell { index, extent: (p.shape.rows * p.shape.width) as u64 }).collect();
            let decomposition = CoverDecomposition::of(cover, &cells, "exact_resident_section");
            if let Err(barriers) = decomposition.independence(&cells) {
                return Err(FrontPassageObstruction::Cover { front: at, barriers });
            }
            let mut device_cells = 0usize;
            let mut cpu_cells = 0usize;
            for section in &decomposition.sections {
                match section.chart {
                    ChartId::Device(_) => device_cells += section.cells.len(),
                    ChartId::Cpu => {
                        cpu_cells += section.cells.len();
                        if let Some(cell) = section.cells.first() {
                            return Err(FrontPassageObstruction::Resource(ResourceObstruction::Placement { front: at, cell: cell.index, chart: ChartId::Cpu }));
                        }
                    }
                }
            }
            let works = decomposition.work(cover);
            let occupied_lanes: BigUint = works.iter().map(|w| w.occupied_lanes.clone()).sum();
            let cover_reading = CoverReading {
                occupied: decomposition.occupied_charts(),
                device_cells,
                cpu_cells,
                idle_lanes: works.iter().map(|w| w.idle_lanes.clone()).sum(),
                members: works.iter().map(|w| w.members.clone()).sum(),
                occupied_lanes: occupied_lanes.clone(),
            };
            let idle: u64 = cover_reading.idle_lanes.to_u64().unwrap_or(u64::MAX);
            lane_demand.push((front.depth, occupied_lanes.to_u64().unwrap_or(u64::MAX), idle));
            // The certificate, from footprints: what each member reads and writes — its inputs'
            // sections, the material its law names, its predecessors' census slots and its own
            // lineage list (read); its own section and its own slot (written).
            let footprints: Vec<MemberFootprint> = members
                .iter()
                .map(|p| {
                    let mut reads: Vec<(u64, u64)> = Vec::new();
                    for input in &p.inputs {
                        reads.extend(sections[&owner_of(&sealed, input.event)].ranges());
                    }
                    reads.extend(p.law.reads(material, &staged));
                    for predecessor in builder.declared_lineage(p.index) {
                        reads.push(builder.slot_range(*predecessor));
                    }
                    reads.push(builder.lineage_range(p.index));
                    // A sealing occurrence's write footprint IS its predecessor's section — the same
                    // range it reads. Self-overlap is not a barrier: each thread touches only its own
                    // coordinate, and the compile refused the fusion unless this occurrence is the
                    // section's only other reader.
                    let mut writes: Vec<(u64, u64)> = sections[&owner_of(&sealed, p.occurrence)].ranges().to_vec();
                    writes.push(builder.slot_range(p.index));
                    MemberFootprint { reads, writes }
                })
                .collect();
            let slot_footprints: Vec<(Vec<(u64, u64)>, (u64, u64))> = members
                .iter()
                .map(|p| (builder.declared_lineage(p.index).iter().map(|pr| builder.slot_range(*pr)).collect(), builder.slot_range(p.index)))
                .collect();
            let certificate = certify_footprints(&footprints);
            if let Some(because) = certificate.because() {
                return Err(FrontPassageObstruction::Interchange { front: at, because: because.clone(), certificate: Box::new(certificate) });
            }
            // The recording: every member's semantic kernel after its producers, then its census.
            let mut predicted = ExactWork::nothing();
            let mut couplings = Vec::new();
            for p in self.ordered(&members) {
                let out = &sections[&owner_of(&sealed, p.occurrence)];
                let lane = builder.open(p.index, &p.producers).map_err(surface_refusal)?;
                let inputs: Vec<&ResidentSection<'chart>> = p.inputs.iter().map(|port| &sections[&owner_of(&sealed, port.event)]).collect();
                if p.law.seals_predecessor() {
                    // The passage records the fused kernel: the fusion is its compression and the
                    // a-priori bound the fused census compares against is its reading. One node, no
                    // census node, no edge between them.
                    surface.record_midpoint_seal(&lane, inputs[0], p.bound).map_err(surface_refusal)?;
                    builder.close_fused(p.index).map_err(surface_refusal)?;
                } else {
                    p.law.record(surface, &lane, &inputs, material, &staged, &p.shape, out).map_err(surface_refusal)?;
                    builder.close(p.index, out, p.bound).map_err(surface_refusal)?;
                }
                predicted = co_present(&predicted, &p.shape.predicted);
                for coupling in &p.shape.couplings {
                    couplings.push(CouplingReceipt {
                        plan: coupling.clone(),
                        occurrence: p.occurrence,
                        output: OccurrencePort::output(p.occurrence, 0),
                        inputs: p.inputs.clone(),
                        written: false,
                        measured_octave: 0,
                        measured_width: 0,
                        refused: 0,
                        reach: 0,
                    });
                }
            }
            receipts.push(FrontReceipt {
                depth: front.depth,
                members: members.iter().map(|p| (p.occurrence, p.law.name())).collect(),
                certificate,
                footprints,
                slot_footprints,
                cover: cover_reading,
                couplings,
                predicted,
            });
        }
        let passage = builder.finish().map_err(surface_refusal)?;
        let ecology: Vec<(EventId, usize, Vec<usize>)> = plan.plans.iter().map(|p| (p.occurrence, p.depth, p.producers.clone())).collect();
        let terminal_index = plan.plans.iter().position(|p| p.occurrence == plan.terminal).unwrap_or(0);
        let traffic = traffic_reading(surface.declaration().resident_lanes(), &lane_demand, &ecology, terminal_index);
        let index_of: BTreeMap<EventId, usize> = plan.plans.iter().map(|p| (p.occurrence, p.index)).collect();
        let bounds: BTreeMap<EventId, (u32, u32, &'static str)> = plan.plans.iter().map(|p| (p.occurrence, (p.bound, p.shape.needed, p.shape.operation))).collect();
        let ancestry: BTreeMap<EventId, Vec<usize>> = plan.plans.iter().map(|p| (p.occurrence, p.producers.clone())).collect();
        Ok(CompiledPassage {
            surface,
            passage,
            sections,
            sealed,
            staged,
            receipts,
            index_of,
            bounds,
            ancestry,
            order: plan.plans.iter().map(|p| p.occurrence).collect(),
            deed_prediction: plan.deed_prediction,
            apparatus_prediction: plan.apparatus_prediction,
            octave_field: plan.octave_field,
            source_bindings: plan.source_bindings,
            entailments: plan.entailments,
            admission,
            mode: surface.mode(),
            traffic,
            terminal: plan.terminal,
            released: false,
        })
    }

    /// Compile, admit and realize in one call. The admission precedes every allocation.
    pub fn bind(
        &self,
        complex: &PortedOperationComplex,
        realization: &ResidentRealization,
        material: &ResidentMaterial<'chart>,
        source: &dyn OccurrenceWitness,
        receiver: &DeedReceiver,
        material_admission: Option<&MaterialAdmission>,
        terminal: EventId,
    ) -> Result<CompiledPassage<'chart>, FrontPassageObstruction> {
        let plan = self.compile(complex, realization, material, source, terminal)?;
        let admission = self.admit(&plan, receiver, material_admission)?;
        self.realize(plan, material, admission)
    }
}

/// **The §4.6 fusion condition, decided from the diagram alone.** `None` when the seal is
/// factored — every declared future receiver reads through the fused output — and otherwise the
/// sentence naming which of the four readings failed.
///
/// It lives as one function because two callers need the same verdict: [`FrontPassage::compile`],
/// which ENFORCES it and refuses the deed, and [`factored_seals`], which a caller uses to decide
/// which quotients to bind fused **before** compiling. Two spellings of one condition is how a
/// pre-check and a guard drift apart.
fn seal_unfactored(
    consumers: &BTreeMap<EventId, BTreeSet<EventId>>,
    quotient: EventId,
    predecessor: EventId,
    terminal: EventId,
    declared: &BTreeSet<EventId>,
    predecessor_is_itself_a_seal: bool,
) -> Option<String> {
    let reading = consumers.get(&predecessor).cloned().unwrap_or_default();
    if reading.len() != 1 || !reading.contains(&quotient) {
        return Some(format!(
            "the predecessor's section is read by {} occurrences ({:?}) and the fusion rewrites it in place; only the quotient may read it",
            reading.len(),
            reading.iter().map(|e| e.0).collect::<Vec<_>>()
        ));
    }
    if predecessor == terminal {
        return Some("the predecessor is the declared terminal, so the receiver reads its pre-quotient enclosure".to_owned());
    }
    if declared.contains(&predecessor) {
        return Some("the receiver declared the predecessor's pre-quotient enclosure as a face it reads".to_owned());
    }
    if predecessor_is_itself_a_seal {
        return Some("the predecessor is itself a fused seal, so its section is already another occurrence's".to_owned());
    }
    None
}

/// **Which of a founded diagram's midpoint quotients may be bound as FUSED seals**, and why each
/// of the rest may not.
///
/// A caller that founded a diagram with the unfused [`MidpointQuotient`] everywhere — because the
/// site that founds it does not know which faces this receiver will read — asks this, rebinds the
/// returned occurrences to [`SealedMidpointQuotient`], and compiles. The refused list is the
/// receipt of what the receiver's own declarations cost: each entry is an occurrence whose
/// pre-quotient enclosure something reads.
///
/// **This decides nothing semantic.** Fusion moves no returned word; it is the apparatus
/// compression of two nodes into one, and the reopening route is to bind the unfused law.
pub fn factored_seals(
    complex: &PortedOperationComplex,
    realization: &ResidentRealization,
    terminal: EventId,
    declared: &BTreeSet<EventId>,
) -> (Vec<EventId>, Vec<(EventId, String)>) {
    let consumers = FrontPassage::consumers(complex);
    let arriving = FrontPassage::arriving(complex);
    let quotients: BTreeSet<EventId> = realization
        .bindings
        .iter()
        .filter(|(_, law)| law.name().starts_with("midpoint-quotient"))
        .map(|(occurrence, _)| *occurrence)
        .collect();
    let mut fusable = Vec::new();
    let mut refused = Vec::new();
    for quotient in &quotients {
        let Some(source) = arriving.get(&OccurrencePort::input(*quotient, 0)) else {
            refused.push((*quotient, "the quotient's input carries no bond".to_owned()));
            continue;
        };
        let predecessor = source.event;
        match seal_unfactored(&consumers, *quotient, predecessor, terminal, declared, quotients.contains(&predecessor)) {
            None => fusable.push(*quotient),
            Some(because) => refused.push((*quotient, because)),
        }
    }
    (fusable, refused)
}

/// **Which occurrence owns the buffer an occurrence's words live in.** A sealing occurrence's
/// section is its predecessor's, rewritten in place; every lookup resolves through this. Chained
/// seals are refused at compile, so the walk takes at most one step, and the loop is written anyway
/// because a resolver that assumes its own precondition is not a resolver.
fn owner_of(sealed: &BTreeMap<EventId, EventId>, occurrence: EventId) -> EventId {
    let mut at = occurrence;
    let mut steps = 0usize;
    while let Some(next) = sealed.get(&at) {
        at = *next;
        steps += 1;
        if steps > sealed.len() {
            break;
        }
    }
    at
}

/// Two co-present deeds compose co-presently: counts add, peaks and spans take the maximum,
/// resident populations add. The serial law is `ExactWork::then`.
pub fn co_present(left: &ExactWork, right: &ExactWork) -> ExactWork {
    ExactWork {
        additions: &left.additions + &right.additions,
        multiplications: &left.multiplications + &right.multiplications,
        divisions: &left.divisions + &right.divisions,
        entries_written: &left.entries_written + &right.entries_written,
        cumulative_bits: &left.cumulative_bits + &right.cumulative_bits,
        peak_bits: left.peak_bits.clone().max(right.peak_bits.clone()),
        resident_entries: &left.resident_entries + &right.resident_entries,
        dependency_span: left.dependency_span.clone().max(right.dependency_span.clone()),
    }
}

/// The traffic reading composed from `receiver_current`, `traversible_chain` and the cover's own
/// lanes. Reports; never routes. `ecology` is every occurrence with its depth and the indices of
/// its producers; `terminal` is the index of the declared terminal.
fn traffic_reading(resident_lanes: u64, lane_demand: &[(usize, u64, u64)], ecology: &[(EventId, usize, Vec<usize>)], terminal: usize) -> TrafficReading {
    let mut fronts = Vec::with_capacity(lane_demand.len());
    for (depth, occupied, idle) in lane_demand {
        let rounds = if resident_lanes == 0 { 0 } else { occupied.div_ceil(resident_lanes) };
        fronts.push((*depth, *occupied, *idle, rounds));
    }
    // receiver_current: sites are occurrences, passages are the bonds, one deed current radiated
    // from the entering occurrences to the terminal within the diagram's own span.
    let mut law = ExactReceiverCurrentLaw::new();
    let capacity = BigUint::from(resident_lanes.max(1));
    for (index, _) in ecology.iter().enumerate() {
        let _ = law.found_site(ReceiverCurrentSiteId(index as u64), capacity.clone());
    }
    let mut passage_id = 0u64;
    let mut sources: Vec<ReceiverCurrentSiteId> = Vec::new();
    for (index, (_, _, producers)) in ecology.iter().enumerate() {
        let mut distinct = producers.clone();
        distinct.sort_unstable();
        distinct.dedup();
        if distinct.is_empty() {
            sources.push(ReceiverCurrentSiteId(index as u64));
        }
        for producer in distinct {
            let _ = law.found_passage(ExactReceiverCurrentPassage {
                id: ReceiverCurrentPassageId(passage_id),
                from: ReceiverCurrentSiteId(producer as u64),
                to: ReceiverCurrentSiteId(index as u64),
                characteristic_delay: 1,
            });
            passage_id += 1;
        }
    }
    let horizon = ecology.iter().map(|(_, depth, _)| *depth as u64).max().unwrap_or(0);
    let reconvergent_sites = ecology
        .iter()
        .filter(|(_, _, producers)| {
            let mut distinct = producers.clone();
            distinct.sort_unstable();
            distinct.dedup();
            distinct.len() >= 2
        })
        .count();
    let (earliest_arrival, earliest_routes, deferred_arrivals, deferred_population) = if !sources.is_empty() && !ecology.is_empty() {
        let terminal_site = ReceiverCurrentSiteId(terminal as u64);
        match law.radiate_to_horizon(sources.into_iter().collect::<LocalSet<_>>(), horizon) {
            Ok(radiation) => {
                let arrival = radiation.arrivals.get(&terminal_site).map(|a| a.chronology).unwrap_or(0);
                let routes = radiation.exact_path_population(terminal_site);
                let approaching = ApproachFront::of(&radiation);
                (arrival, routes, radiation.deferred_arrivals.len(), approaching.population())
            }
            Err(_) => (0, BigUint::zero(), 0, BigUint::zero()),
        }
    } else {
        (0, BigUint::zero(), 0, BigUint::zero())
    };
    // traversible_chain: each front-to-front junction as an admittance crossing.
    let mut junctions = Vec::new();
    let mut composite = None;
    if let Some(first) = lane_demand.first() {
        if let Ok(admittance) = Admittance::from_shared(first.1.max(1), 1) {
            let mut chain = found(first.0, &admittance, ChainStanding::Carrying(admittance.value().clone()));
            let mut carrying = admittance;
            let mut whole = true;
            for window in lane_demand.windows(2) {
                let (from, incident_lanes, _) = window[0];
                let (to, transmitted_lanes, _) = window[1];
                let Ok(transmitted) = Admittance::from_shared(transmitted_lanes.max(1), 1) else { whole = false; break };
                let Ok(crossing) = Crossing::meet(&carrying, &transmitted) else { whole = false; break };
                junctions.push(JunctionReading {
                    from_depth: from,
                    to_depth: to,
                    incident_lanes,
                    transmitted_lanes,
                    transmission: crossing.transmission(),
                    reflection: crossing.reflection(),
                    power_transmission: crossing.power_transmission(),
                });
                chain.carry(crossing, to, ChainStanding::Carrying(transmitted.value().clone()));
                carrying = transmitted;
            }
            if whole && chain.hops() > 0 {
                let matrix = chain.compose();
                composite = match (matrix.transmission(), matrix.reflection(), matrix.power_transmission()) {
                    (Some(t), Some(r), Some(p)) => Some((t, r, p)),
                    _ => None,
                };
            }
        }
    }
    TrafficReading { resident_lanes, fronts, earliest_arrival, earliest_routes, deferred_arrivals, deferred_population, reconvergent_sites, junctions, composite }
}


// ---------------------------------------------------------------------------------------------
// the bound passage
// ---------------------------------------------------------------------------------------------

/// **The passage, bound and admitted**: every section allocated, the graph instantiated, every
/// front's certificate and cover taken. `launch` is the deed; the terminal is read from the
/// section the receiver names, and only against a reading in which it stood.
pub struct CompiledPassage<'chart> {
    surface: &'chart ResidentSurface<'chart>,
    passage: ResidentPassage<'chart>,
    sections: BTreeMap<EventId, ResidentSection<'chart>>,
    /// A sealing occurrence to the predecessor whose buffer it rewrote in place. The key's words
    /// live in the value's section; the value's own pre-quotient face no longer exists, and
    /// [`CompiledPassage::read_section`] refuses it by name.
    sealed: BTreeMap<EventId, EventId>,
    staged: BTreeMap<String, StagedWords<'chart>>,
    receipts: Vec<FrontReceipt>,
    index_of: BTreeMap<EventId, usize>,
    bounds: BTreeMap<EventId, (u32, u32, &'static str)>,
    ancestry: BTreeMap<EventId, Vec<usize>>,
    order: Vec<EventId>,
    pub deed_prediction: ExactWork,
    pub apparatus_prediction: ApparatusPrediction,
    pub octave_field: BTreeMap<OccurrencePort, u32>,
    pub source_bindings: Vec<BindingValidation>,
    /// Per occurrence: the entailment of its law by the validated testimony.
    pub entailments: Vec<(EventId, LawEntailment)>,
    pub admission: DeedAdmission,
    pub mode: ModeIdentity,
    pub traffic: TrafficReading,
    terminal: EventId,
    /// A section has been released to a later passage; this passage may not launch again.
    released: bool,
}

impl<'chart> CompiledPassage<'chart> {
    /// The section written at an occurrence's output, for the receiver to copy out. A sealing
    /// occurrence resolves to the buffer it rewrote; a sealed predecessor resolves to nothing,
    /// because after the deed those words are the quotient's.
    pub fn section(&self, occurrence: EventId) -> Option<&ResidentSection<'chart>> {
        if self.sealed_by(occurrence).is_some() {
            return None;
        }
        self.sections.get(&owner_of(&self.sealed, occurrence))
    }

    /// The occurrence that sealed this one, if any: the quotient whose fused kernel rewrote this
    /// occurrence's section in place. Its face is the one the receiver reads.
    pub fn sealed_by(&self, occurrence: EventId) -> Option<EventId> {
        self.sealed.iter().find(|(_, predecessor)| **predecessor == occurrence).map(|(quotient, _)| *quotient)
    }
    pub fn terminal(&self) -> EventId {
        self.terminal
    }
    /// **Release a section to a later passage**, with the a-priori bound it was admitted under:
    /// the residual stream or a shared standing leaves this passage's ownership and enters the next
    /// passage's material as a [`Standing`]. This passage may not be launched again afterwards;
    /// the section it wrote has moved.
    pub fn release_section(&mut self, occurrence: EventId) -> Option<(ResidentSection<'chart>, u32)> {
        if self.sealed_by(occurrence).is_some() {
            return None;
        }
        let bound = self.bounds.get(&occurrence).map(|(b, _, _)| *b)?;
        self.released = true;
        let owner = owner_of(&self.sealed, occurrence);
        self.sections.remove(&owner).map(|section| (section, bound))
    }
    /// The passage index of an occurrence, as the lineage names it.
    pub fn index_of(&self, occurrence: EventId) -> Option<usize> {
        self.index_of.get(&occurrence).copied()
    }
    /// The occurrence at a passage index.
    pub fn occurrence_at(&self, index: usize) -> Option<EventId> {
        self.order.get(index).copied()
    }
    /// The declared producers of an occurrence, by passage index.
    pub fn producers_of(&self, occurrence: EventId) -> Option<&[usize]> {
        self.ancestry.get(&occurrence).map(Vec::as_slice)
    }
    /// The schedule this passage was bound under.
    pub fn schedule(&self) -> Schedule {
        self.passage.schedule()
    }

    /// **The terminal face**: the one section this passage's receiver declared, copied out once —
    /// only when the reading says it stood. A terminal whose lineage carries a refusal is refused
    /// by name with the complete obstruction lineage; its words are never returned as a standing.
    pub fn read_terminal(&self, returned: &PassageReturn) -> Result<Vec<(i64, i64)>, FrontPassageObstruction> {
        self.read_section(returned, self.terminal)
    }

    /// A section at any occurrence, read only against a reading in which that occurrence stood.
    ///
    /// **A face a declared fusion sealed away is refused by name.** The compile admitted the fusion
    /// because no consumer read this occurrence's section and no receiver declared it; a receiver
    /// asking for it afterwards is asking for words that are now the quotient's midpoints, and it is
    /// given the refusal and the reopening route instead of the collapsed words. Readability at read
    /// time is not knowable at compile — `read_section` takes any occurrence — so the guard lives at
    /// both ends and neither is decorative.
    pub fn read_section(&self, returned: &PassageReturn, occurrence: EventId) -> Result<Vec<(i64, i64)>, FrontPassageObstruction> {
        if let Some(quotient) = self.sealed_by(occurrence) {
            return Err(FrontPassageObstruction::Sealed {
                occurrence,
                quotient,
                reopening: "bind MidpointQuotient at the quotient instead of SealedMidpointQuotient, or declare this occurrence through FrontPassage::reading before compiling: the unfused pair keeps this section and censuses its enclosure",
            });
        }
        let index = self.index_of.get(&occurrence).copied().ok_or(FrontPassageObstruction::Compile(CompileRefusal::ForeignOccurrence { occurrence }))?;
        if !returned.obstruction.stands(index) {
            let (bound, _, operation) = self.bounds[&occurrence];
            let slot = returned.fronts.iter().flat_map(|f| f.readings.iter()).find(|r| r.occurrence == occurrence).map(|r| r.measured).unwrap_or_default();
            let refusal = slot.refusal(operation, bound).unwrap_or(ResidentRefusal::Upstream { operation: operation.to_owned() });
            return Err(FrontPassageObstruction::Refused { occurrence, operation: operation.to_owned(), refusal, slot, lineage: returned.obstruction.clone() });
        }
        // A FUSED occurrence's words are its predecessor's buffer, rewritten in place, so the
        // lookup resolves through the seal exactly as [`CompiledPassage::section`] does. Reading a
        // fused quotient's OWN face is lawful and is what a receiver declaring the quotient asks
        // for; it was a panic until 2026-08-19, when the streamed circulation read the final
        // normed standing — a quotient — through a fused seal for the first time.
        self.surface.read_out(&self.sections[&owner_of(&self.sealed, occurrence)]).map_err(surface_refusal)
    }

    /// The graph as the apparatus bound it, and what the builder intended.
    pub fn graph(&self) -> (&GraphCensus, (usize, usize)) {
        (self.passage.graph_census(), self.passage.intended())
    }
    /// The certificates and cover readings taken before any launch, front by front.
    pub fn fronts(&self) -> &[FrontReceipt] {
        &self.receipts
    }

    /// New entering material of the same extents, crossing once, for a later deed of this bound
    /// passage. Nothing else changes: the graph is invariant under the material.
    pub fn refill(&self, material: &ResidentMaterial<'chart>) -> Result<(), FrontPassageObstruction> {
        for (name, staged) in &self.staged {
            let entering = material.entering.get(name).ok_or_else(|| FrontPassageObstruction::Compile(CompileRefusal::MaterialAbsent { occurrence: EventId(0), name: name.clone() }))?;
            self.surface.refill(staged, &entering.words).map_err(surface_refusal)?;
        }
        Ok(())
    }

    /// **The deed.** The caller declares the mode it expects; a mode that is not the surface's
    /// refuses without launching. One graph launch, one synchronize, one census read; the census
    /// completes every receipt, and the complete obstruction lineage is returned beside it — the
    /// deed is returned whole whether or not the card refused somewhere, and what did not stand
    /// cannot be read as standing.
    pub fn launch(&self, expected: &ModeIdentity) -> Result<PassageReturn, FrontPassageObstruction> {
        if self.released {
            return Err(surface_refusal(ResidentRefusal::Declaration { operation: "passage", what: "a section was released to a later passage; this passage may not launch again".to_owned() }));
        }
        let actual = self.surface.mode();
        if *expected != actual {
            return Err(surface_refusal(ResidentRefusal::ModeMismatch { expected: Box::new(expected.clone()), actual: Box::new(actual) }));
        }
        let reading = self.passage.launch().map_err(surface_refusal)?;
        Ok(self.compose(reading))
    }

    /// **Launch this deed onto a caller's stream, and return nothing yet.**
    ///
    /// The same mode guard, the same graph, the same deed. What is deferred is the terminal
    /// synchronization: a caller conducting a succession of passages whose standings cross on the
    /// card orders every graph on one stream, so the apparatus never waits between them, and then
    /// synchronizes once and asks each passage for its return through
    /// [`CompiledPassage::returned`]. Returns the census reading taken **before** the launch,
    /// which the return needs and which cannot be re-taken later.
    ///
    /// A caller that reads a section before synchronizing reads a deed that has not finished; the
    /// two calls are separate exactly so that the synchronization is a declared act rather than a
    /// side effect of asking a question.
    pub fn launch_on(&self, expected: &ModeIdentity, stream: &Stream) -> Result<TransferCensus, FrontPassageObstruction> {
        if self.released {
            return Err(surface_refusal(ResidentRefusal::Declaration { operation: "passage", what: "a section was released to a later passage; this passage may not launch again".to_owned() }));
        }
        let actual = self.surface.mode();
        if *expected != actual {
            return Err(surface_refusal(ResidentRefusal::ModeMismatch { expected: Box::new(expected.clone()), actual: Box::new(actual) }));
        }
        self.passage.launch_on(stream).map_err(surface_refusal)
    }

    /// **The return of a deed launched with [`CompiledPassage::launch_on`]**, read after the
    /// caller's terminal synchronization. Identical in every field to what `launch` returns.
    pub fn returned(&self, census_before: TransferCensus) -> Result<PassageReturn, FrontPassageObstruction> {
        let reading = self.passage.census(census_before).map_err(surface_refusal)?;
        Ok(self.compose(reading))
    }

    fn compose(&self, reading: crate::resident_section::PassageReading) -> PassageReturn {
        let mut fronts = Vec::with_capacity(self.receipts.len());
        let mut measured_octaves = BTreeMap::new();
        let mut refusals = Vec::new();
        for front in &self.receipts {
            let mut readings = Vec::with_capacity(front.members.len());
            for (occurrence, operation) in &front.members {
                let index = self.index_of[occurrence];
                let slot = reading.slots[index];
                let (bound, needed, _) = self.bounds[occurrence];
                if slot.refusal(operation, bound).is_some() {
                    refusals.push((*occurrence, *operation, slot));
                }
                measured_octaves.insert(OccurrencePort::output(*occurrence, 0), slot.max_octave);
                readings.push(MemberReading { occurrence: *occurrence, operation, bound, needed, measured: slot });
            }
            let couplings = front
                .couplings
                .iter()
                .map(|coupling| {
                    let slot = reading.slots[self.index_of[&coupling.occurrence]];
                    CouplingReceipt {
                        written: slot.written,
                        measured_octave: slot.max_octave,
                        measured_width: slot.max_width,
                        refused: slot.refused,
                        reach: slot.reach,
                        ..coupling.clone()
                    }
                })
                .collect();
            fronts.push(FrontDeedReading { depth: front.depth, readings, couplings });
        }
        PassageReturn { fronts, census_before: reading.census_before, census_after: reading.census_after, measured_octaves, obstruction: reading.obstruction, refusals }
    }

    /// The first refusal in front order as a typed obstruction, or `Ok` when every occurrence
    /// stood. For a caller that needs a verdict beside the lineage.
    pub fn standing(&self, returned: &PassageReturn) -> Result<(), FrontPassageObstruction> {
        match returned.refusals.first() {
            None => Ok(()),
            Some((occurrence, operation, slot)) => {
                let (bound, _, _) = self.bounds[occurrence];
                let refusal = slot.refusal(operation, bound).unwrap_or(ResidentRefusal::Upstream { operation: (*operation).to_owned() });
                Err(FrontPassageObstruction::Refused { occurrence: *occurrence, operation: (*operation).to_owned(), refusal, slot: *slot, lineage: returned.obstruction.clone() })
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::embedding_fiber::ResidentReadout;
    use crate::exact_work::WorkMetric;
    use crate::resident_section::{Dyadic, DyadicEnclosure, REFUSED_MALFORMED, REFUSED_UPSTREAM};
    use crate::ported_operation::SourceTestimony;
    use crate::source_occurrence::{AuthenticatedContainer, AuthenticatedText};

    const ONE: u16 = 0x3F80;
    const TWO: u16 = 0x4000;
    const HALF: u16 = 0x3F00;
    const MINUS_ONE_AND_HALF: u16 = 0xBFC0;

    fn surface() -> Option<(&'static ResidentReadout, &'static ResidentSurface<'static>)> {
        let readout = match ResidentReadout::new() {
            Ok(readout) => Box::leak(Box::new(readout)),
            Err(_) => {
                eprintln!("no resident chart answered; the front-passage tests did not run");
                return None;
            }
        };
        let surface = Box::leak(Box::new(ResidentSurface::on(readout).ok()?));
        Some((readout, surface))
    }

    const IMPLEMENTATION: &str = "class Site:\n    def enter(self):\n        x = embed(words) * scale\n    def scale(self):\n        y = x * 2\n    def hadamard(self):\n        z = x * x\n";

    fn occurrence() -> crate::source_occurrence::SourceOccurrence {
        crate::source_occurrence::SourceOccurrence {
            implementation: AuthenticatedText::of_text("/site.py", IMPLEMENTATION, None),
            configuration: AuthenticatedText::of_text("/config.json", r#"{"text_config": {"grain": 20, "width": 1}}"#, None),
            configuration_scope: vec!["text_config".to_owned()],
            container: AuthenticatedContainer { locator: "/none".to_owned(), octets: 0, header_octets: 0, header_sha256: String::new(), content_sha256: None, regions: BTreeMap::new(), identity: None },
            assets: Vec::new(),
        }
    }

    /// A two-front diagram: `enter x` then co-present `{scale x by 2, hadamard x·x}`.
    fn small_diagram() -> (PortedOperationComplex, ResidentRealization, EventId, EventId, EventId) {
        let mut complex = PortedOperationComplex::new("small");
        let standing = complex.port("standing");
        let testimony = |symbol: &str| vec![SourceTestimony::Implementation { locator: "/site.py".to_owned(), symbol: symbol.to_owned() }, SourceTestimony::Configuration { field: "grain".to_owned(), value: "20".to_owned() }, SourceTestimony::Configuration { field: "width".to_owned(), value: "1".to_owned() }];
        let enter = complex.bind_operation("enter", OperationSpecies::Construction, vec![], vec![standing], None, testimony("Site.enter (x = embed(words) * scale)")).expect("law");
        let scale = complex.bind_operation("scale", OperationSpecies::Transport, vec![standing], vec![standing], None, testimony("Site.scale (y = x * 2)")).expect("law");
        let hadamard = complex.bind_operation("hadamard", OperationSpecies::Construction, vec![standing, standing], vec![standing], None, testimony("Site.hadamard (z = x * x)")).expect("law");
        let e = complex.occur(enter).expect("occur");
        let s = complex.occur(scale).expect("occur");
        let h = complex.occur(hadamard).expect("occur");
        complex.carries_precedence("x scales", standing, OccurrencePort::output(e, 0), OccurrencePort::input(s, 0)).expect("bond");
        complex.carries_precedence("x squares left", standing, OccurrencePort::output(e, 0), OccurrencePort::input(h, 0)).expect("bond");
        complex.carries_precedence("x squares right", standing, OccurrencePort::output(e, 0), OccurrencePort::input(h, 1)).expect("bond");
        let mut realization = ResidentRealization::default();
        realization.bind(e, Enter { population: "x".to_owned(), scale: Dyadic::ONE });
        realization.bind(s, Scale { by: DyadicEnclosure { lo: 2, hi: 2, grain: 0 } });
        realization.bind(h, Hadamard);
        (complex, realization, e, s, h)
    }

    /// One warp of entering words, so the cover places the cell on the device chart.
    fn material() -> ResidentMaterial<'static> {
        let mut words = vec![ONE, TWO, HALF, MINUS_ONE_AND_HALF];
        words.resize(32, ONE);
        let mut material = ResidentMaterial::empty();
        material.entering.insert("x".to_owned(), EnteringRows { words, rows: 1, width: 32 });
        material
    }

    /// `enter x` → `scale x by 2` → a midpoint quotient sealing the scale. The quotient's law is the
    /// caller's to choose: `MidpointQuotient` is the unfused pair, `SealedMidpointQuotient` the
    /// declared fusion. `extra_consumer` bonds a second reader onto the scale, which is exactly the
    /// receiver the fusion may not fuse away.
    fn sealed_diagram(fused: bool, extra_consumer: bool) -> (PortedOperationComplex, ResidentRealization, EventId, EventId, EventId) {
        let mut complex = PortedOperationComplex::new("sealed");
        let standing = complex.port("standing");
        let testimony = |symbol: &str| vec![SourceTestimony::Implementation { locator: "/site.py".to_owned(), symbol: symbol.to_owned() }, SourceTestimony::Configuration { field: "grain".to_owned(), value: "20".to_owned() }, SourceTestimony::Configuration { field: "width".to_owned(), value: "1".to_owned() }];
        let enter = complex.bind_operation("enter", OperationSpecies::Construction, vec![], vec![standing], None, testimony("Site.enter (x = embed(words) * scale)")).expect("law");
        let scale = complex.bind_operation("scale", OperationSpecies::Transport, vec![standing], vec![standing], None, testimony("Site.scale (y = x * 2)")).expect("law");
        let quotient = complex
            .bind_operation("scale · midpoint quotient", OperationSpecies::Quotient, vec![standing], vec![standing], None, vec![SourceTestimony::Intervention { statement: "declared quotient chart: the certified enclosure is collapsed to its midpoint for the successors".to_owned() }])
            .expect("law");
        let e = complex.occur(enter).expect("occur");
        let s = complex.occur(scale).expect("occur");
        let q = complex.occur(quotient).expect("occur");
        complex.carries_precedence("x scales", standing, OccurrencePort::output(e, 0), OccurrencePort::input(s, 0)).expect("bond");
        complex.carries_precedence("scale sealed", standing, OccurrencePort::output(s, 0), OccurrencePort::input(q, 0)).expect("bond");
        let mut realization = ResidentRealization::default();
        realization.bind(e, Enter { population: "x".to_owned(), scale: Dyadic::ONE });
        realization.bind(s, Scale { by: DyadicEnclosure { lo: 2, hi: 2, grain: 0 } });
        if fused {
            realization.bind(q, SealedMidpointQuotient);
        } else {
            realization.bind(q, MidpointQuotient);
        }
        if extra_consumer {
            let second = complex.bind_operation("second reader", OperationSpecies::Quotient, vec![standing], vec![standing], None, vec![SourceTestimony::Intervention { statement: "the receiver reads the pre-quotient enclosure through a second consumer".to_owned() }]).expect("law");
            let r = complex.occur(second).expect("occur");
            complex.carries_precedence("scale read again", standing, OccurrencePort::output(s, 0), OccurrencePort::input(r, 0)).expect("bond");
            realization.bind(r, WithdrawColumns { from: 0, span: 1 });
        }
        (complex, realization, e, s, q)
    }

    /// **`factored_seals` answers, from the diagram alone, exactly what the compile enforces.**
    ///
    /// A caller founding a diagram with the unfused quotient everywhere — which is what
    /// `phoenix/tower.rs` does, because a site does not know which faces a receiver will read —
    /// asks this before compiling and rebinds what it returns. The falsifier is that the two must
    /// never disagree: an occurrence `factored_seals` names must bind fused, and one it refuses
    /// must refuse at compile with the same sentence.
    #[test]
    fn factored_seals_and_the_compile_agree_on_which_quotients_may_fuse_in_this_circulation() {
        // (i) the legal shape: the quotient's predecessor has exactly one consumer.
        let (complex, realization, _, scale, q) = sealed_diagram(false, false);
        let (fusable, refused) = factored_seals(&complex, &realization, q, &BTreeSet::new());
        assert_eq!(fusable, vec![q], "the one quotient is factored");
        assert!(refused.is_empty(), "{refused:?}");

        // (ii) the receiver declares the predecessor's pre-quotient face: the seal is unfactored,
        //      and the sentence is the compile's own.
        let declared: BTreeSet<EventId> = [scale].into_iter().collect();
        let (fusable, refused) = factored_seals(&complex, &realization, q, &declared);
        assert!(fusable.is_empty());
        assert_eq!(refused.len(), 1);
        assert!(refused[0].1.contains("declared"), "{:?}", refused[0]);

        // (iii) the terminal is the predecessor itself.
        let (fusable, refused) = factored_seals(&complex, &realization, scale, &BTreeSet::new());
        assert!(fusable.is_empty());
        assert!(refused[0].1.contains("terminal"), "{:?}", refused[0]);

        // (iv) a second consumer reads the predecessor.
        let (complex, realization, _, _, q) = sealed_diagram(false, true);
        let (fusable, refused) = factored_seals(&complex, &realization, q, &BTreeSet::new());
        assert!(fusable.is_empty(), "a second reader is exactly what the fusion may not fuse away");
        assert!(refused[0].1.contains("read by 2"), "{:?}", refused[0]);
    }

    /// **A fused quotient's OWN face is readable, and it is the collapsed one.**
    ///
    /// The seal rewrites its predecessor's buffer in place, so the quotient carries no section of
    /// its own and the lookup must resolve through the seal. Reading it was a panic until the
    /// streamed circulation asked for the final normed standing — which is a quotient — through a
    /// fused seal. The falsifier is that the fused and unfused readings of the same occurrence are
    /// the same words.
    #[test]
    fn a_fused_quotients_own_face_is_readable_and_equals_the_unfused_pairs() {
        let Some((_, surface)) = surface() else { return };
        let material = material();
        let receiver = DeedReceiver::unbounded();
        let (complex, realization, _, _, q) = sealed_diagram(true, false);
        let fused = FrontPassage::new(surface, ResidentGrain(20)).bind(&complex, &realization, &material, &occurrence(), &receiver, None, q).expect("the fusion binds");
        let returned = fused.launch(&surface.mode()).expect("the fused deed");
        let fused_face = fused.read_section(&returned, q).expect("the fused quotient's own face is readable");

        let (uc, ur, _, _, uq) = sealed_diagram(false, false);
        let unfused = FrontPassage::new(surface, ResidentGrain(20)).bind(&uc, &ur, &material, &occurrence(), &receiver, None, uq).expect("the unfused pair binds");
        let unreturned = unfused.launch(&surface.mode()).expect("the unfused deed");
        let unfused_face = unfused.read_section(&unreturned, uq).expect("the unfused quotient's face");
        assert_eq!(fused_face, unfused_face, "the fusion moved a returned word");
    }

    /// **The deferred launch returns the same deed as the immediate one.** `launch_on` records the
    /// graph onto a caller's stream and waits for nothing; `returned` reads the same census words
    /// after the caller's own terminal synchronization. The falsifier is that the two readings must
    /// agree in every field — one synchronization for a whole circulation is only lawful if what
    /// comes back is what `launch` would have returned.
    #[test]
    fn a_deferred_launch_onto_a_callers_stream_returns_the_same_deed_as_an_immediate_one() {
        let Some((_, surface)) = surface() else { return };
        let material = material();
        let (complex, realization, _, _, h) = small_diagram();
        let passage = FrontPassage::new(surface, ResidentGrain(20));
        let bound = passage.bind(&complex, &realization, &material, &occurrence(), &DeedReceiver::unbounded(), None, h).expect("binds");
        let immediate = bound.launch(&surface.mode()).expect("the immediate deed");
        let immediate_face = bound.read_terminal(&immediate).expect("the immediate terminal");

        let stream = Stream::create().expect("a conducting stream");
        let before = bound.launch_on(&surface.mode(), &stream).expect("the deferred deed");
        surface.synchronize_counted(&stream).expect("the terminal synchronization");
        let deferred = bound.returned(before).expect("the deferred return");
        let deferred_face = bound.read_terminal(&deferred).expect("the deferred terminal");

        assert_eq!(immediate_face, deferred_face, "the deed does not move with where its terminal synchronization sits");
        assert_eq!(immediate.obstruction, deferred.obstruction);
        assert_eq!(immediate.measured_octaves, deferred.measured_octaves);
        for (a, b) in immediate.fronts.iter().zip(&deferred.fronts) {
            assert_eq!(a.depth, b.depth);
            for (x, y) in a.readings.iter().zip(&b.readings) {
                assert_eq!(x.measured, y.measured, "occurrence {:?} censused differently", x.occurrence);
            }
        }
    }

    /// **Part C's fusion condition, decided at compile from the diagram.** The legal case binds and
    /// predicts one node fewer and one section fewer; each of the three illegal cases refuses by
    /// name and the refusal carries the reopening route.
    #[test]
    fn a_declared_fusion_binds_only_when_every_declared_receiver_factors_through_it() {
        let Some((_, surface)) = surface() else { return };
        let material = material();
        let receiver = DeedReceiver::unbounded();
        // (i) legal: the scale's only consumer is the quotient, the quotient is the terminal, and
        //     the receiver declared no other face.
        let (complex, realization, _, _, q) = sealed_diagram(true, false);
        let passage = FrontPassage::new(surface, ResidentGrain(20));
        let fused = passage.bind(&complex, &realization, &material, &occurrence(), &receiver, None, q).expect("the fusion binds");
        // (ii) the same diagram unfused, for the counts to be read against.
        let (uc, ur, _, us, uq) = sealed_diagram(false, false);
        let unfused_passage = FrontPassage::new(surface, ResidentGrain(20));
        let unfused = unfused_passage.bind(&uc, &ur, &material, &occurrence(), &receiver, None, uq).expect("the unfused pair binds");
        let (fused_graph, _) = fused.graph();
        let (unfused_graph, _) = unfused.graph();
        assert_eq!(fused_graph.nodes + 1, unfused_graph.nodes, "the fusion is exactly one node fewer");
        assert_eq!(fused.apparatus_prediction.graph_nodes as usize, fused_graph.nodes, "and the prediction moved with it");
        assert_eq!(unfused.apparatus_prediction.graph_nodes as usize, unfused_graph.nodes);
        assert_eq!(fused.apparatus_prediction.captured_launches + 1, unfused.apparatus_prediction.captured_launches);
        assert_eq!(fused.apparatus_prediction.allocations + 2, unfused.apparatus_prediction.allocations, "and two allocations fewer: the quotient carries no section");
        assert!(fused.apparatus_prediction.section_octets < unfused.apparatus_prediction.section_octets);
        // the sealed predecessor's face is refused by name, with the reopening route, and the
        // unfused pair returns it.
        let returned = fused.launch(&surface.mode()).expect("launches");
        let sealed_read = fused.read_section(&returned, fused.occurrence_at(1).expect("the scale"));
        match sealed_read {
            Err(FrontPassageObstruction::Sealed { reopening, .. }) => assert!(reopening.contains("MidpointQuotient")),
            other => panic!("a sealed face must refuse by name, not return words: {other:?}"),
        }
        let unfused_returned = unfused.launch(&surface.mode()).expect("launches");
        assert!(unfused.read_section(&unfused_returned, us).is_ok(), "the reopening route returns the pre-quotient enclosure");
        // and the terminals are bit-equal: the fusion moved apparatus, not words.
        assert_eq!(fused.read_terminal(&returned).expect("fused terminal"), unfused.read_terminal(&unfused_returned).expect("unfused terminal"));
        // (iii) the pre-seal section declared as a return: the terminal itself.
        let (c2, r2, _, s2, _) = sealed_diagram(true, false);
        let refused = FrontPassage::new(surface, ResidentGrain(20)).bind(&c2, &r2, &material, &occurrence(), &receiver, None, s2);
        assert!(matches!(refused.as_ref().err(), Some(FrontPassageObstruction::Compile(CompileRefusal::FusionUnfactored { because, .. })) if because.contains("terminal")), "{:?}", refused.err());
        // (iv) the pre-seal section declared as a face the receiver reads.
        let (c3, r3, _, s3, q3) = sealed_diagram(true, false);
        let declared = FrontPassage::new(surface, ResidentGrain(20)).reading([s3]).bind(&c3, &r3, &material, &occurrence(), &receiver, None, q3);
        assert!(matches!(declared.as_ref().err(), Some(FrontPassageObstruction::Compile(CompileRefusal::FusionUnfactored { because, .. })) if because.contains("declared")), "{:?}", declared.err());
        // (v) a second consumer reads the pre-seal section.
        let (c4, r4, _, _, q4) = sealed_diagram(true, true);
        let shared = FrontPassage::new(surface, ResidentGrain(20)).bind(&c4, &r4, &material, &occurrence(), &receiver, None, q4);
        assert!(matches!(shared.as_ref().err(), Some(FrontPassageObstruction::Compile(CompileRefusal::FusionUnfactored { because, .. })) if because.contains("read by 2")), "{:?}", shared.err());
    }

    /// **The fused quotient's census is the unfused pair's, word for word** — including the collapsed
    /// population the predecessor's own census carries, which the fusion does not touch.
    #[test]
    fn the_fused_seal_returns_the_same_census_as_the_unfused_pair_including_the_collapsed_population() {
        let Some((_, surface)) = surface() else { return };
        let material = material();
        let receiver = DeedReceiver::unbounded();
        let (fc, fr, _, _, fq) = sealed_diagram(true, false);
        let fused = FrontPassage::new(surface, ResidentGrain(20)).bind(&fc, &fr, &material, &occurrence(), &receiver, None, fq).expect("binds");
        let (uc, ur, _, us, uq) = sealed_diagram(false, false);
        let unfused = FrontPassage::new(surface, ResidentGrain(20)).bind(&uc, &ur, &material, &occurrence(), &receiver, None, uq).expect("binds");
        let fused_returned = fused.launch(&surface.mode()).expect("launches");
        let unfused_returned = unfused.launch(&surface.mode()).expect("launches");
        let slot_of = |ret: &PassageReturn, at: EventId| ret.fronts.iter().flat_map(|f| f.readings.iter()).find(|r| r.occurrence == at).expect("reading").measured;
        // the predecessor's census — the PRE-quotient widest, summed and nonzero widths
        let fused_pre = slot_of(&fused_returned, fused.occurrence_at(1).expect("the scale"));
        let unfused_pre = slot_of(&unfused_returned, us);
        assert_eq!(fused_pre, unfused_pre, "the collapsed population the chart retains is unchanged by the fusion");
        // the quotient's own census
        let fused_q = slot_of(&fused_returned, fq);
        let unfused_q = slot_of(&unfused_returned, uq);
        assert_eq!(fused_q, unfused_q, "the quotient's census is the unfused pair's, word for word");
        assert_eq!(fused_q.max_width, 0, "a collapsed section has no width");
        assert_eq!(fused_q.width_sum, 0);
        assert_eq!(fused_q.nonzero_widths, 0);
        assert!(fused_q.written && unfused_q.written);
        assert_eq!(fused_q.lineage_inspected, 1);
    }

    /// **The fusion is the unfused pair on the REFUSING path too**, and that is the load-bearing
    /// half: a fused quotient's only possible flag is UPSTREAM, its upstream decision is
    /// thread-uniform and final at entry because the fused node sits after its predecessor's census
    /// on the graph's own edge, and a refused occurrence's census measures nothing. Poison the
    /// entering material and require the two deeds' slots to agree word for word.
    #[test]
    fn a_poisoned_lineage_refuses_identically_through_the_fused_seal_and_the_unfused_pair() {
        let Some((_, surface)) = surface() else { return };
        // 0x7F80 is +inf in bfloat16: a non-finite stored codeword the mouth refuses as malformed.
        let mut words = vec![ONE, TWO, 0x7F80, MINUS_ONE_AND_HALF];
        words.resize(32, ONE);
        let mut material = ResidentMaterial::empty();
        material.entering.insert("x".to_owned(), EnteringRows { words, rows: 1, width: 32 });
        let receiver = DeedReceiver::unbounded();
        let (fc, fr, fe, fs, fq) = sealed_diagram(true, false);
        let fused = FrontPassage::new(surface, ResidentGrain(20)).bind(&fc, &fr, &material, &occurrence(), &receiver, None, fq).expect("binds");
        let (uc, ur, ue, us, uq) = sealed_diagram(false, false);
        let unfused = FrontPassage::new(surface, ResidentGrain(20)).bind(&uc, &ur, &material, &occurrence(), &receiver, None, uq).expect("binds");
        let fused_returned = fused.launch(&surface.mode()).expect("launches");
        let unfused_returned = unfused.launch(&surface.mode()).expect("launches");
        let slot_of = |ret: &PassageReturn, at: EventId| ret.fronts.iter().flat_map(|f| f.readings.iter()).find(|r| r.occurrence == at).expect("reading").measured;
        for (f, u, what) in [(fe, ue, "the mouth"), (fs, us, "the scale"), (fq, uq, "the quotient")] {
            assert_eq!(slot_of(&fused_returned, f), slot_of(&unfused_returned, u), "{what}'s slot moved with the fusion");
        }
        let quotient = slot_of(&fused_returned, fq);
        assert_eq!(quotient.refused, REFUSED_UPSTREAM, "a fused quotient's only possible flag is UPSTREAM");
        assert_eq!(quotient.upstream_count, 1);
        assert_eq!(quotient.upstream_first, Some(1), "the least refusing predecessor is the scale, at passage index 1");
        // the lineage join is of the PREDECESSOR's own refusal word, so the quotient reads the
        // scale's UPSTREAM and the scale reads the mouth's MALFORMED — the flag travels a hop at a
        // time and is never flattened, and the fused seal reads exactly what the unfused collapse did
        assert_eq!(quotient.upstream_flags, REFUSED_UPSTREAM);
        let scale = slot_of(&fused_returned, fs);
        assert_eq!(scale.upstream_flags & REFUSED_MALFORMED, REFUSED_MALFORMED, "the malformed codeword's flag reached the scale");
        assert!(quotient.written, "the census still marks that it ran");
        assert_eq!((quotient.max_octave, quotient.max_width, quotient.width_sum, quotient.nonzero_widths), (0, 0, 0, 0), "and it measures nothing");
        // and neither deed will hand back a face that did not stand
        assert!(fused.read_terminal(&fused_returned).is_err() && unfused.read_terminal(&unfused_returned).is_err());
    }

    #[test]
    fn a_sub_warp_cell_is_a_placement_obstruction_not_a_fallback() {
        let Some((_, surface)) = surface() else { return };
        let (complex, realization, _, s, _) = small_diagram();
        let mut material = ResidentMaterial::empty();
        material.entering.insert("x".to_owned(), EnteringRows { words: vec![ONE, TWO, HALF, MINUS_ONE_AND_HALF], rows: 1, width: 4 });
        let passage = FrontPassage::new(surface, ResidentGrain(20));
        let before = surface.census();
        let outcome = passage.bind(&complex, &realization, &material, &occurrence(), &DeedReceiver::unbounded(), None, s);
        assert!(matches!(outcome, Err(FrontPassageObstruction::Resource(ResourceObstruction::Placement { chart: ChartId::Cpu, .. }))));
        assert_eq!(surface.census().deed_launches, before.deed_launches, "no deed, no CPU computation");
    }

    #[test]
    fn a_two_front_diagram_binds_launches_once_and_the_section_never_crosses_until_the_terminal_read() {
        let Some((_, surface)) = surface() else { return };
        let (complex, realization, _, s, h) = small_diagram();
        let material = material();
        let passage = FrontPassage::new(surface, ResidentGrain(20));
        let bound = passage.bind(&complex, &realization, &material, &occurrence(), &DeedReceiver::unbounded(), None, s).expect("binds");
        assert!(bound.admission.is_admitted());
        assert!(bound.admission.semantic.iter().all(|c| !c.is_bounded() && c.admitted), "no ceiling was declared: every semantic coordinate is exhibited as unbounded, none is invented");
        assert!(bound.admission.semantic.iter().all(|c| matches!(&c.ceiling, Ceiling::Unbounded { constrained_by, .. } if !constrained_by.is_empty())), "every unbounded coordinate names what still constrains it");
        assert!(bound.admission.apparatus.iter().any(|c| c.name == "charged-resident-octets" && c.is_bounded() && c.admitted));
        assert!(bound.admission.apparatus.iter().any(|c| c.name == "carrier-peak-octaves" && c.is_bounded() && c.admitted));
        assert!(bound.admission.apparatus.iter().any(|c| c.name == "scratch-octets" && c.is_bounded()));
        assert!(bound.admission.apparatus.iter().any(|c| c.name == "grid-extent" && c.is_bounded()));
        assert_eq!(bound.fronts().len(), 2);
        assert!(bound.fronts()[1].certificate.is_interchangeable());
        assert_eq!(bound.fronts()[1].members.len(), 2);
        assert!(bound.fronts().iter().all(|f| f.cover.cpu_cells == 0 && f.cover.device_cells > 0));
        let (graph, intended) = bound.graph();
        assert_eq!((graph.nodes, graph.edges), intended);
        assert_eq!(bound.apparatus_prediction.graph_nodes as usize, graph.nodes);
        assert_eq!(bound.apparatus_prediction.graph_edges as usize, graph.edges);
        let before = surface.census();
        let returned = bound.launch(&surface.mode()).expect("launches");
        let after = surface.census();
        assert_eq!(after.deed_launches, before.deed_launches + 1);
        assert_eq!(after.synchronizations, before.synchronizations + 1);
        assert_eq!(after.captured_launches, before.captured_launches, "nothing launched between the graph and the terminal");
        assert_eq!(after.section_read_outs, before.section_read_outs, "no section crossed during the deed");
        assert_eq!(after.egress_receipt_octets - before.egress_receipt_octets, bound.apparatus_prediction.egress_receipt_octets);
        assert!(returned.fronts.iter().all(|f| f.readings.iter().all(|r| r.measured.written && r.measured.max_octave <= r.bound)));
        assert!(returned.stands());
        assert!(returned.measured_octaves.values().all(|o| *o > 0));
        let unit = 1i64 << 20;
        let scaled = bound.read_terminal(&returned).expect("read");
        assert_eq!(&scaled[..4], &[(2 * unit, 2 * unit), (4 * unit, 4 * unit), (unit, unit), (-3 * unit, -3 * unit)]);
        let squared = surface.read_out(bound.section(h).expect("squared")).expect("read");
        assert_eq!(squared[3], (9 * unit / 4, 9 * unit / 4));
        assert!(bound.admission.is_admitted());
        assert!(bound.traffic.fronts.len() == 2 && bound.traffic.junctions.len() == 1);
        assert_eq!(bound.traffic.deferred_population, BigUint::zero());
        assert_eq!(bound.source_bindings.len(), 3);
        // Refilled material, same bound passage: a second deed with a different terminal face.
        let mut second = ResidentMaterial::empty();
        let mut words = vec![TWO, TWO, HALF, MINUS_ONE_AND_HALF];
        words.resize(32, ONE);
        second.entering.insert("x".to_owned(), EnteringRows { words, rows: 1, width: 32 });
        bound.refill(&second).expect("refill");
        let second_return = bound.launch(&surface.mode()).expect("second deed");
        assert_eq!(bound.read_terminal(&second_return).expect("read")[0], (4 * unit, 4 * unit));
    }

    #[test]
    fn a_budget_below_the_prediction_makes_zero_launches_and_zero_allocations() {
        let Some((_, surface)) = surface() else { return };
        let (complex, realization, _, s, _) = small_diagram();
        let material = material();
        let passage = FrontPassage::new(surface, ResidentGrain(20));
        let plan = passage.compile(&complex, &realization, &material, &occurrence(), s).expect("compiles");
        let metric = WorkMetric::width_weighted();
        let price = metric.price(&plan.deed_prediction);
        let ceiling = u64::try_from(&price).expect("fits") - 1;
        let receiver = DeedReceiver::unbounded().with_scalar(WorkBudget::declared(metric, ceiling));
        let before = surface.census();
        let outcome = passage.bind(&complex, &realization, &material, &occurrence(), &receiver, None, s);
        assert!(matches!(outcome, Err(FrontPassageObstruction::Resource(ResourceObstruction::Semantic { .. }))));
        // and a per-coordinate ceiling one below the requirement refuses naming that coordinate
        let written = u64::try_from(&plan.deed_prediction.entries_written).expect("fits");
        assert!(written > 0);
        let starved = DeedReceiver::unbounded().with_ceiling("entries-written", written - 1);
        match passage.bind(&complex, &realization, &material, &occurrence(), &starved, None, s) {
            Err(FrontPassageObstruction::Resource(ResourceObstruction::Semantic { coordinate })) => {
                assert_eq!(coordinate.name, "entries-written");
                assert!(matches!(coordinate.ceiling, Ceiling::Bounded { .. }));
            }
            other => panic!("expected a semantic refusal naming entries-written, got {:?}", other.map(|_| ())),
        }
        assert_eq!(surface.census().allocations, before.allocations, "the per-coordinate refusal allocates nothing");
        let after = surface.census();
        assert_eq!(after.deed_launches, before.deed_launches, "a refusal launches nothing");
        assert_eq!(after.captured_launches, before.captured_launches, "a refusal captures nothing");
        assert_eq!(after.allocations, before.allocations, "a refusal allocates nothing");
        assert_eq!(after.resident_octets_now, before.resident_octets_now);
    }

    #[test]
    fn a_fabricated_symbol_a_drifted_field_and_an_open_fibre_do_not_compile() {
        let Some((_, surface)) = surface() else { return };
        let (mut complex, realization, _, s, _) = small_diagram();
        let material = material();
        let passage = FrontPassage::new(surface, ResidentGrain(20));
        let mut fabricated = occurrence();
        fabricated.implementation = AuthenticatedText::of_text("/site.py", "class Site:\n    def enter(self):\n        x = embed(words) * scale\n", None);
        assert!(matches!(passage.compile(&complex, &realization, &material, &fabricated, s), Err(FrontPassageObstruction::Compile(CompileRefusal::Source(SourceRefusal::SymbolUnresolved { .. })))));
        let mut drifted = occurrence();
        drifted.configuration = AuthenticatedText::of_text("/config.json", r#"{"text_config": {"grain": 21, "width": 1}}"#, None);
        assert!(matches!(passage.compile(&complex, &realization, &material, &drifted, s), Err(FrontPassageObstruction::Compile(CompileRefusal::Source(SourceRefusal::ConfigurationValueDiffers { .. })))));
        complex.retain_undecided(crate::ported_operation::CandidateDiagrams {
            question: "which pairing?".to_owned(),
            candidates: vec!["halves".to_owned(), "adjacent".to_owned()],
            would_be_decided_by: vec!["the implementation".to_owned()],
        });
        assert!(matches!(passage.compile(&complex, &realization, &material, &occurrence(), s), Err(FrontPassageObstruction::Compile(CompileRefusal::DiagramOpen(_)))));
    }

    #[test]
    fn a_mode_that_is_not_the_surfaces_refuses_the_launch_without_a_deed() {
        let Some((_, surface)) = surface() else { return };
        let (complex, realization, _, s, _) = small_diagram();
        let material = material();
        let passage = FrontPassage::new(surface, ResidentGrain(20));
        let bound = passage.bind(&complex, &realization, &material, &occurrence(), &DeedReceiver::unbounded(), None, s).expect("binds");
        let mut foreign = surface.mode();
        foreign.device = Some("a card that is not mounted".to_owned());
        let before = surface.census();
        assert!(matches!(bound.launch(&foreign), Err(FrontPassageObstruction::Resource(ResourceObstruction::Surface(ResidentRefusal::ModeMismatch { .. })))));
        assert_eq!(surface.census().deed_launches, before.deed_launches);
        let mut other_kernel = surface.mode();
        other_kernel.kernel_content = Some("00".repeat(32));
        assert!(matches!(bound.launch(&other_kernel), Err(FrontPassageObstruction::Resource(ResourceObstruction::Surface(ResidentRefusal::ModeMismatch { .. })))));
    }


    /// Two entering branches A and B, each scaled, then joined: B's entering words carry a
    /// non-finite codeword at a NONZERO coordinate, so B refuses `MALFORMED` on the card at runtime.
    fn two_branch_diagram() -> (PortedOperationComplex, ResidentRealization, EventId, EventId, EventId, EventId, EventId) {
        let mut complex = PortedOperationComplex::new("two branches");
        let standing = complex.port("standing");
        let testimony = |symbol: &str| vec![SourceTestimony::Implementation { locator: "/site.py".to_owned(), symbol: symbol.to_owned() }, SourceTestimony::Configuration { field: "grain".to_owned(), value: "20".to_owned() }, SourceTestimony::Configuration { field: "width".to_owned(), value: "1".to_owned() }];
        let enter = complex.bind_operation("enter", OperationSpecies::Construction, vec![], vec![standing], None, testimony("Site.enter (x = embed(words) * scale)")).expect("law");
        let scale = complex.bind_operation("scale", OperationSpecies::Transport, vec![standing], vec![standing], None, testimony("Site.scale (y = x * 2)")).expect("law");
        let join = complex.bind_operation("hadamard", OperationSpecies::Construction, vec![standing, standing], vec![standing], None, testimony("Site.hadamard (z = x * x)")).expect("law");
        let ea = complex.occur(enter).expect("occur");
        let eb = complex.occur(enter).expect("occur");
        let sa = complex.occur(scale).expect("occur");
        let sb = complex.occur(scale).expect("occur");
        let j = complex.occur(join).expect("occur");
        complex.carries_precedence("a scales", standing, OccurrencePort::output(ea, 0), OccurrencePort::input(sa, 0)).expect("bond");
        complex.carries_precedence("b scales", standing, OccurrencePort::output(eb, 0), OccurrencePort::input(sb, 0)).expect("bond");
        complex.carries_precedence("a joins", standing, OccurrencePort::output(sa, 0), OccurrencePort::input(j, 0)).expect("bond");
        complex.carries_precedence("b joins", standing, OccurrencePort::output(sb, 0), OccurrencePort::input(j, 1)).expect("bond");
        let mut realization = ResidentRealization::default();
        realization.bind(ea, Enter { population: "a".to_owned(), scale: Dyadic::ONE });
        realization.bind(eb, Enter { population: "b".to_owned(), scale: Dyadic::ONE });
        realization.bind(sa, Scale { by: DyadicEnclosure { lo: 2, hi: 2, grain: 0 } });
        realization.bind(sb, Scale { by: DyadicEnclosure { lo: 2, hi: 2, grain: 0 } });
        realization.bind(j, Hadamard);
        (complex, realization, ea, eb, sa, sb, j)
    }

    fn two_branch_material(poison: bool) -> ResidentMaterial<'static> {
        let mut a = vec![ONE, TWO, HALF, MINUS_ONE_AND_HALF];
        a.resize(32, ONE);
        let mut b = vec![ONE, TWO, if poison { 0x7F80 } else { HALF }, MINUS_ONE_AND_HALF];
        b.resize(32, TWO);
        let mut material = ResidentMaterial::empty();
        material.entering.insert("a".to_owned(), EnteringRows { words: a, rows: 1, width: 32 });
        material.entering.insert("b".to_owned(), EnteringRows { words: b, rows: 1, width: 32 });
        material
    }

    #[test]
    fn a_runtime_refusal_in_one_branch_returns_the_complete_lineage_and_the_terminal_cannot_be_read_as_standing() {
        let Some((_, surface)) = surface() else { return };
        let (complex, realization, ea, eb, sa, sb, j) = two_branch_diagram();
        let passage = FrontPassage::new(surface, ResidentGrain(20));
        let clean = two_branch_material(false);
        let bound_clean = passage.bind(&complex, &realization, &clean, &occurrence(), &DeedReceiver::unbounded(), None, j).expect("binds");
        let clean_return = bound_clean.launch(&surface.mode()).expect("deed");
        assert!(clean_return.stands());
        let clean_a = bound_clean.read_section(&clean_return, sa).expect("a stood");
        let clean_terminal = bound_clean.read_terminal(&clean_return).expect("terminal stood");
        let poisoned = two_branch_material(true);
        let bound = passage.bind(&complex, &realization, &poisoned, &occurrence(), &DeedReceiver::unbounded(), None, j).expect("binds");
        // every front certified from footprints that now include the predecessor slots read
        assert!(bound.fronts().iter().all(|f| f.certificate.is_interchangeable()));
        let returned = bound.launch(&surface.mode()).expect("the deed returns whole even when the card refused");
        assert!(!returned.stands());
        // the complete lineage: B originated (malformed), B's scale carried it, the join carried it
        let ib = bound.index_of(eb).expect("index");
        let isb = bound.index_of(sb).expect("index");
        let ij = bound.index_of(j).expect("index");
        let ia = bound.index_of(ea).expect("index");
        let isa = bound.index_of(sa).expect("index");
        let lineage = &returned.obstruction;
        assert_eq!(lineage.refusals.iter().map(|r| r.index).collect::<Vec<_>>(), { let mut v = vec![ib, isb, ij]; v.sort_unstable(); v });
        assert!(lineage.refusals.iter().find(|r| r.index == ib).expect("B").origin);
        let carried_sb = lineage.refusals.iter().find(|r| r.index == isb).expect("sB");
        assert!(!carried_sb.origin && carried_sb.upstream_first == Some(ib) && carried_sb.upstream_flags == REFUSED_MALFORMED);
        let carried_j = lineage.refusals.iter().find(|r| r.index == ij).expect("join");
        assert!(!carried_j.origin && carried_j.upstream_first == Some(isb) && carried_j.upstream_count == 1 && carried_j.upstream_flags & REFUSED_UPSTREAM != 0);
        assert!(lineage.stands(ia) && lineage.stands(isa));
        // the unrelated sibling is bit-identical to the clean run
        assert_eq!(bound.read_section(&returned, sa).expect("A stood"), clean_a);
        // the terminal cannot be read as standing: refused by name with the lineage
        match bound.read_terminal(&returned) {
            Err(FrontPassageObstruction::Refused { occurrence, lineage: l, .. }) => {
                assert_eq!(occurrence, j);
                assert_eq!(&l, lineage);
            }
            other => panic!("the terminal must refuse: {:?}", other.map(|_| ())),
        }
        assert!(matches!(bound.standing(&returned), Err(FrontPassageObstruction::Refused { .. })));
        let _ = clean_terminal;
        // the same diagram under the serialized and the reversed-serialized schedules: one lineage
        for control in [FrontPassage::serialized(surface, ResidentGrain(20)), FrontPassage::serialized_reversed(surface, ResidentGrain(20))] {
            let bound_control = control.bind(&complex, &realization, &poisoned, &occurrence(), &DeedReceiver::unbounded(), None, j).expect("binds");
            let (graph, intended) = bound_control.graph();
            assert_eq!((graph.nodes, graph.edges), intended);
            assert_eq!(bound_control.apparatus_prediction.graph_edges as usize, graph.edges, "the serialized control's edges were predicted");
            let control_return = bound_control.launch(&surface.mode()).expect("deed");
            assert_eq!(control_return.obstruction, returned.obstruction);
            assert_eq!(control_return.refusals.iter().map(|(e, _, s)| (*e, *s)).collect::<Vec<_>>(), returned.refusals.iter().map(|(e, _, s)| (*e, *s)).collect::<Vec<_>>());
            assert_eq!(bound_control.read_section(&control_return, sa).expect("A stood"), clean_a);
        }
        // and the co-present deed launched again: the same lineage
        let again = bound.launch(&surface.mode()).expect("deed");
        assert_eq!(again.obstruction, returned.obstruction);
    }

    #[test]
    fn the_material_deed_is_predicted_admitted_and_cited_and_the_grain_moves_the_charge_lawfully() {
        let Some((readout, surface)) = surface() else { return };
        let passage = FrontPassage::new(surface, ResidentGrain(20));
        let plan = MaterialPlan { maps: vec![("m".to_owned(), 2, 2)], band_elements: 0, positions: 0 };
        let prediction = passage.predict_material(&plan);
        assert_eq!(prediction.resident_octets, 2 * 2 * 8);
        assert_eq!(prediction.ingress_octets, 2 * 2 * 2);
        assert_eq!(prediction.allocation_grain, surface.allocation_grain());
        assert!(prediction.charged_octets >= prediction.resident_octets && prediction.charged_octets % surface.allocation_grain() == 0);
        let admitted = passage.admit_material(&prediction).expect("admits");
        assert!(admitted.is_admitted());
        // mount as predicted and reconcile
        let map = readout.mount_bfloat16(&[ONE, TWO, MINUS_ONE_AND_HALF, HALF], 2).expect("map");
        let mut mounted = ResidentMaterial::empty();
        mounted.populations.insert("m".to_owned(), MountedPopulation { readout: map, mass_value_octaves: 3 });
        let reconciled = admitted.reconcile(&mounted);
        assert_eq!(reconciled, vec![("m".to_owned(), 32, 32)]);
        // an impossible material refuses before any map is allocated, naming the coordinate
        let huge = MaterialPlan { maps: vec![("too big".to_owned(), 1 << 40, 1 << 20)], band_elements: 0, positions: 0 };
        let before = surface.census();
        match passage.admit_material(&passage.predict_material(&huge)) {
            Err(FrontPassageObstruction::Resource(ResourceObstruction::Material { coordinate })) => assert_eq!(coordinate.name, "material-charged-octets"),
            other => panic!("expected a material refusal, got {:?}", other.map(|_| ())),
        }
        assert_eq!(surface.census().allocations, before.allocations);
        // the deed cites the material admission: its source standing is bounded by it
        let (complex, realization, _, s, _) = small_diagram();
        let entering = material();
        let bound = passage.bind(&complex, &realization, &entering, &occurrence(), &DeedReceiver::unbounded(), Some(&admitted), s).expect("binds");
        let cited = bound.admission.apparatus.iter().find(|c| c.name == "source-standing-octets").expect("cited");
        assert!(cited.is_bounded() && cited.admitted);
        assert_eq!(bound.admission.cited_material.as_ref().map(|m| m.resident_octets()), Some(32));
        // the charge is the grain-rounded sum, and a coarser grain raises it lawfully
        let a = &bound.apparatus_prediction;
        assert!(a.charged_octets >= a.deed_octets);
        assert_eq!(a.charged_octets % a.allocation_grain, 0);
        assert_eq!(a.charged_under(a.allocation_grain), a.charged_octets);
        assert_eq!(a.charged_under(1), a.deed_octets, "under grain one the charge is the words' own sum");
        assert!(a.charged_under(2 * a.allocation_grain) >= a.charged_octets);
        assert_eq!(a.charged_under(2 * a.allocation_grain) % (2 * a.allocation_grain), 0);
        // a receiver aperture below the requirement on an apparatus coordinate refuses before
        // allocation, naming the coordinate and the aperture
        let narrow = DeedReceiver::unbounded().with_apparatus_aperture("charged-resident-octets", a.charged_octets - 1);
        let before = surface.census();
        match passage.bind(&complex, &realization, &entering, &occurrence(), &narrow, Some(&admitted), s) {
            Err(FrontPassageObstruction::Resource(ResourceObstruction::Apparatus { coordinate })) => {
                assert_eq!(coordinate.name, "charged-resident-octets");
                assert!(matches!(&coordinate.ceiling, Ceiling::Bounded { declared_by, .. } if declared_by.contains("aperture")));
            }
            other => panic!("expected an apparatus refusal, got {:?}", other.map(|_| ())),
        }
        assert_eq!(surface.census().allocations, before.allocations, "the apparatus refusal allocates nothing");
        // every member's footprint carries its predecessors' slots as reads and its own as a write
        for front in bound.fronts() {
            for (footprint, (reads, own)) in front.footprints.iter().zip(&front.slot_footprints) {
                assert!(footprint.writes.contains(own));
                assert!(reads.iter().all(|r| footprint.reads.contains(r)));
            }
        }
    }

    /// A standing released from one passage enters the next as a `Standing` construction: the carry
    /// is bit-exact, no octet crosses the apparatus boundary, and the released passage may not
    /// launch again.
    #[test]
    fn a_released_standing_enters_the_next_passage_bit_exactly_and_the_releasing_passage_cannot_relaunch() {
        let Some((_, surface)) = surface() else { return };
        let (complex, realization, _, s, _) = small_diagram();
        let material = material();
        let passage = FrontPassage::new(surface, ResidentGrain(20));
        let mut first = passage.bind(&complex, &realization, &material, &occurrence(), &DeedReceiver::unbounded(), None, s).expect("binds");
        let returned = first.launch(&surface.mode()).expect("deed");
        let face = first.read_terminal(&returned).expect("read");
        let ingress_before = surface.census().ingress_octets;
        let (section, bound) = first.release_section(s).expect("released");
        assert!(matches!(first.launch(&surface.mode()), Err(FrontPassageObstruction::Resource(ResourceObstruction::Surface(ResidentRefusal::Declaration { .. })))));
        // the next passage: standing → scale by 2, the carry entailed by the slice that names the standing
        let mut occ = occurrence();
        occ.implementation = AuthenticatedText::of_text("/site.py", "class Site:\n    def enter(self):\n        x = embed(words) * scale\n        hidden_states = x\n    def scale(self):\n        y = x * 2\n    def hadamard(self):\n        z = x * x\n", None);
        let testimony = |symbol: &str| vec![SourceTestimony::Implementation { locator: "/site.py".to_owned(), symbol: symbol.to_owned() }, SourceTestimony::Configuration { field: "grain".to_owned(), value: "20".to_owned() }];
        let mut next = PortedOperationComplex::new("next");
        let standing = next.port("standing");
        let carry = next.bind_operation("carry", OperationSpecies::Construction, vec![], vec![standing], None, vec![SourceTestimony::Implementation { locator: "/site.py".to_owned(), symbol: "Site.enter (hidden_states = x)".to_owned() }]).expect("law");
        let scale = next.bind_operation("scale", OperationSpecies::Transport, vec![standing], vec![standing], None, testimony("Site.scale (y = x * 2)")).expect("law");
        let c = next.occur(carry).expect("occur");
        let sc = next.occur(scale).expect("occur");
        next.carries_precedence("carried scales", standing, OccurrencePort::output(c, 0), OccurrencePort::input(sc, 0)).expect("bond");
        let mut next_realization = ResidentRealization::default();
        next_realization.bind(c, Standing { name: "x".to_owned() });
        next_realization.bind(sc, Scale { by: DyadicEnclosure { lo: 2, hi: 2, grain: 0 } });
        let mut next_material = ResidentMaterial::empty();
        next_material.standings.insert("x".to_owned(), (std::rc::Rc::new(section), bound));
        let second = passage.bind(&next, &next_realization, &next_material, &occ, &DeedReceiver::unbounded(), None, sc).expect("binds");
        let returned2 = second.launch(&surface.mode()).expect("deed");
        let doubled = second.read_terminal(&returned2).expect("read");
        assert_eq!(doubled.len(), face.len());
        assert!(doubled.iter().zip(&face).all(|((l2, h2), (l, h))| *l2 == 2 * l && *h2 == 2 * h));
        assert_eq!(surface.census().ingress_octets - ingress_before, 4, "only the one lineage word crossed; the standing did not");
    }

    #[test]
    fn co_present_composition_adds_counts_and_maxes_the_span() {
        let mut a = ExactWork::nothing();
        a.added(3);
        a.stepped();
        a.stepped();
        a.resident(10);
        let mut b = ExactWork::nothing();
        b.added(4);
        b.stepped();
        b.resident(7);
        let both = co_present(&a, &b);
        assert_eq!(both.additions, BigUint::from(7u32));
        assert_eq!(both.dependency_span, BigUint::from(2u32));
        assert_eq!(both.resident_entries, BigUint::from(17u32));
        let serial = a.then(&b);
        assert_eq!(serial.dependency_span, BigUint::from(3u32));
        assert_eq!(serial.resident_entries, BigUint::from(10u32));
    }

    #[test]
    fn the_traffic_reading_reports_rounds_junctions_routes_and_no_deferral() {
        // enter x (0); scale x (1) and hadamard x·x (2) co-present at depth 1; re-entry of both (3).
        let ecology = vec![
            (EventId(10), 0usize, vec![]),
            (EventId(11), 1, vec![0]),
            (EventId(12), 1, vec![0, 0]),
            (EventId(13), 2, vec![1, 2]),
        ];
        let reading = traffic_reading(1000, &[(0, 32, 0), (1, 2500, 0), (2, 64, 0)], &ecology, 3);
        assert_eq!(reading.fronts[1].3, 3, "2500 lanes over 1000 resident lanes take three rounds");
        assert_eq!(reading.junctions.len(), 2);
        assert!(reading.junctions[0].reflection < Rat::zero(), "a widening channel returns an inverted half");
        assert!(reading.junctions[1].reflection > Rat::zero(), "a narrowing channel returns a cohering half");
        assert_eq!(reading.earliest_arrival, 2);
        assert_eq!(reading.earliest_routes, BigUint::from(2u32), "two equal-arrival routes superpose at the re-entry");
        assert_eq!(reading.reconvergent_sites, 1);
        assert_eq!(reading.deferred_arrivals, 0);
        assert_eq!(reading.deferred_population, BigUint::zero());
        assert!(reading.composite.is_some());
        // A residual skip makes the earliest section arrive early and defers the longer chain.
        let skipped = vec![
            (EventId(10), 0usize, vec![]),
            (EventId(11), 1, vec![0]),
            (EventId(12), 2, vec![1]),
            (EventId(13), 3, vec![0, 2]),
        ];
        let reading = traffic_reading(1000, &[(0, 32, 0), (1, 32, 0), (2, 32, 0), (3, 32, 0)], &skipped, 3);
        assert_eq!(reading.earliest_arrival, 1, "the skip reaches the terminal in one hop");
        assert_eq!(reading.deferred_arrivals, 1, "the chain's arrival is retained as deferred");
    }

    /// **A released standing is shared READ-ONLY between sibling passages** — the relation Deed
    /// H5's cohort rests on, measured rather than promised.
    ///
    /// One deed releases its terminal as a standing. Two siblings then enter on that same standing
    /// through [`Standing`], whose realization is `section_carry`: it names the standing as an
    /// input address and writes only its own fresh output section. Each sibling then withdraws a
    /// DIFFERENT span of its own copy. The falsifier is direct: after both have conducted, the
    /// released standing's words are bit-identical to what they were before either ran, and the two
    /// siblings' returns differ from each other — so both really did read it and neither wrote it.
    #[test]
    fn the_cohort_shares_a_released_standing_read_only_between_sibling_passages() {
        let Some((_, surface)) = surface() else { return };
        let grain = ResidentGrain(20);
        let source = occurrence();
        let receiver = DeedReceiver::unbounded();

        // the base deed: enter x, scale it, seal it, and RELEASE the seal as a standing
        let (complex, realization, _, _, quotient) = sealed_diagram(false, false);
        let material = material();
        let passage = FrontPassage::new(surface, grain);
        let mut bound = passage.bind(&complex, &realization, &material, &source, &receiver, None, quotient).expect("the base deed binds");
        let returned = bound.launch(&surface.mode()).expect("the base deed launches");
        bound.standing(&returned).expect("the base deed stands");
        let (section, octaves) = bound.release_section(quotient).expect("the terminal releases as a standing");
        let standing = std::rc::Rc::new(section);
        let before = surface.read_out(&standing).expect("the standing reads out");
        drop(bound);

        // two siblings, each entering on the SAME standing and withdrawing a different span
        let sibling = |from: usize, span: usize| -> Vec<(i64, i64)> {
            let mut complex = PortedOperationComplex::new("sibling");
            let port = complex.port("standing");
            let declared = |what: &str| vec![SourceTestimony::Intervention { statement: what.to_owned() }];
            let carry = complex
                .bind_operation("carried standing", OperationSpecies::Construction, vec![], vec![port], None, declared("the sibling enters on the base's released standing"))
                .expect("law");
            let withdraw = complex
                .bind_operation("span withdrawn (intervention)", OperationSpecies::Quotient, vec![port], vec![port], None, declared("the caller's intervention on its OWN copy of the shared standing"))
                .expect("law");
            let c = complex.occur(carry).expect("occur");
            let w = complex.occur(withdraw).expect("occur");
            complex.carries_precedence("the carried standing is withdrawn from", port, OccurrencePort::output(c, 0), OccurrencePort::input(w, 0)).expect("bond");
            let mut realization = ResidentRealization::default();
            realization.bind(c, Standing { name: "shared".to_owned() });
            realization.bind(w, WithdrawColumns { from, span });
            let mut material = ResidentMaterial::empty();
            material.standings.insert("shared".to_owned(), (std::rc::Rc::clone(&standing), octaves));
            let passage = FrontPassage::new(surface, grain);
            let bound = passage.bind(&complex, &realization, &material, &source, &receiver, None, w).expect("the sibling binds");
            let returned = bound.launch(&surface.mode()).expect("the sibling launches");
            bound.standing(&returned).expect("the sibling stands");
            bound.read_terminal(&returned).expect("the sibling returns its terminal")
        };
        let left = sibling(0, 16);
        let right = sibling(16, 16);

        let after = surface.read_out(&standing).expect("the standing reads out again");
        assert_eq!(before, after, "the shared standing was written by a sibling: the read-only share is broken");
        assert_ne!(left, right, "the two siblings withdrew different spans, so their returns must differ");
        // and each sibling really read the shared standing: outside its withdrawn span it carries
        // exactly the standing's own words
        assert_eq!(left[16..], before[16..], "the left sibling's untouched half is the standing's");
        assert_eq!(right[..16], before[..16], "the right sibling's untouched half is the standing's");
        assert!(left[..16].iter().all(|(lo, hi)| *lo == 0 && *hi == 0), "the withdrawn span is withdrawn");
    }
}

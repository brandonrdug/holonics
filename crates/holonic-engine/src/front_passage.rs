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
use crate::source_occurrence::{BindingValidation, SourceOccurrence, SourceRefusal};
use crate::traversible_chain::{found, Admittance, Crossing, Standing};
use mount::GraphCensus;

pub use crate::resident_law::{
    Chronology, CollapseControl, Contact, Contract, Enter, EnteringRows, GeluTanh, Hadamard, MountedPopulation, ReEntry, ResidentLaw,
    ResidentMaterial, RmsRebase, Scale, WithdrawColumns,
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
    /// The widest a-priori octave bound any occurrence is admitted under.
    pub carrier_peak_octaves: u64,
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
}

impl<'chart> FrontPassage<'chart> {
    pub fn new(surface: &'chart ResidentSurface<'chart>, grain: ResidentGrain) -> Self {
        Self { surface, grain, schedule: Schedule::CoPresent, reverse_fronts: false }
    }

    /// The serialized-realization control over the same diagram.
    pub fn serialized(surface: &'chart ResidentSurface<'chart>, grain: ResidentGrain) -> Self {
        Self { surface, grain, schedule: Schedule::Serialized, reverse_fronts: false }
    }

    /// The serialized control with every front opened in reverse member order.
    pub fn serialized_reversed(surface: &'chart ResidentSurface<'chart>, grain: ResidentGrain) -> Self {
        Self { surface, grain, schedule: Schedule::Serialized, reverse_fronts: true }
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

    /// The members of each front in the order this passage opens them.
    fn ordered<'p, 'a>(&self, members: &'p [&'p Plan<'a>]) -> Vec<&'p Plan<'a>> {
        let mut ordered: Vec<&Plan<'a>> = members.to_vec();
        if self.reverse_fronts {
            ordered.reverse();
        }
        ordered
    }

    /// The bound a law puts on the octaves of its output words, clamped to the word.
    fn bound_octaves(&self, law: &dyn ResidentLaw, input_octaves: &[u32], material: &ResidentMaterial<'chart>) -> u32 {
        let bound = law.bound_octaves(self.grain, input_octaves, material);
        // A written word occupies at most the signed word: a bound past it is a bound on nothing,
        // and a value past it is refused on the card by name.
        u32::try_from(bound.max(1)).unwrap_or(u32::MAX).min(WORD_OCTAVES)
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
        source: &SourceOccurrence,
        terminal: EventId,
    ) -> Result<CompiledPlan<'a>, FrontPassageObstruction> {
        realization.validate(complex)?;
        let closure = complex.closure().map_err(|error| CompileRefusal::Shape(error.to_string()))?;
        if !closure.is_closed() {
            return Err(CompileRefusal::DiagramOpen(closure).into());
        }
        let source_bindings = source.validate(complex)?;
        for (occurrence, law) in &realization.bindings {
            if let Err(name) = law.material(material) {
                return Err(CompileRefusal::MaterialAbsent { occurrence: *occurrence, name }.into());
            }
        }
        if !complex.shape.occurrences.contains_key(&terminal) {
            return Err(CompileRefusal::ForeignOccurrence { occurrence: terminal }.into());
        }
        let fronts = complex.fronts().map_err(|error| CompileRefusal::Shape(error.to_string()))?;
        let arriving = Self::arriving(complex);

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
                let shapes: Vec<(usize, usize, u32)> = inputs.iter().map(|port| field.get(port).copied().unwrap_or((0, 0, 0))).collect();
                let octaves: Vec<u32> = shapes.iter().map(|(_, _, o)| *o).collect();
                let bound = self.bound_octaves(law, &octaves, material);
                let shape = law.shape(self.surface, self.grain, &shapes, material).map_err(|refusal| FrontPassageObstruction::Resource(ResourceObstruction::Carrier(refusal)))?;
                field.insert(OccurrencePort::output(*occurrence, 0), (shape.rows, shape.width, bound));
                front_work = co_present(&front_work, &shape.predicted);
                let section = (shape.rows * shape.width * 8) as u64;
                section_octets += 2 * section;
                charged += 2 * rounded_to(section.max(8), grain);
                allocation_octets.push(section.max(8));
                allocation_octets.push(section.max(8));
                apparatus.captured_launches += u64::from(shape.launches);
                apparatus.reductions += shape.couplings.len() as u64;
                apparatus.scratch_octets = apparatus.scratch_octets.max(u64::from(shape.shared_octets));
                apparatus.grid_extent = apparatus.grid_extent.max((shape.rows * shape.width) as u64);
                apparatus.carrier_peak_octaves = apparatus.carrier_peak_octaves.max(u64::from(bound));
                apparatus.allocations += 2;
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
        apparatus.graph_nodes = 1 + 2 * plans.len() as u64;
        apparatus.graph_edges = plans
            .iter()
            .map(|plan| {
                let mut distinct: Vec<usize> = plan.producers.clone();
                distinct.sort_unstable();
                distinct.dedup();
                (if distinct.is_empty() { 1 } else { distinct.len() as u64 }) + 1
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
            CoordinateAdmission::bounded("carrier-peak-octaves", BigUint::from(a.carrier_peak_octaves), BigUint::from(u64::from(WORD_OCTAVES)), "the signed word the section is stored in"),
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
        // 1. Sections and staging.
        let mut sections: BTreeMap<EventId, ResidentSection<'chart>> = BTreeMap::new();
        let mut staged: BTreeMap<String, StagedWords<'chart>> = BTreeMap::new();
        for p in &plan.plans {
            sections.insert(p.occurrence, surface.fresh_section(p.shape.rows, p.shape.width, plan.grain).map_err(surface_refusal)?);
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
                        reads.extend(sections[&input.event].ranges());
                    }
                    reads.extend(p.law.reads(material, &staged));
                    for predecessor in builder.declared_lineage(p.index) {
                        reads.push(builder.slot_range(*predecessor));
                    }
                    reads.push(builder.lineage_range(p.index));
                    let mut writes: Vec<(u64, u64)> = sections[&p.occurrence].ranges().to_vec();
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
                let out = &sections[&p.occurrence];
                let lane = builder.open(p.index, &p.producers).map_err(surface_refusal)?;
                let inputs: Vec<&ResidentSection<'chart>> = p.inputs.iter().map(|port| &sections[&port.event]).collect();
                p.law.record(surface, &lane, &inputs, material, &staged, &p.shape, out).map_err(surface_refusal)?;
                builder.close(p.index, out, p.bound).map_err(surface_refusal)?;
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
            admission,
            mode: surface.mode(),
            traffic,
            terminal: plan.terminal,
        })
    }

    /// Compile, admit and realize in one call. The admission precedes every allocation.
    pub fn bind(
        &self,
        complex: &PortedOperationComplex,
        realization: &ResidentRealization,
        material: &ResidentMaterial<'chart>,
        source: &SourceOccurrence,
        receiver: &DeedReceiver,
        material_admission: Option<&MaterialAdmission>,
        terminal: EventId,
    ) -> Result<CompiledPassage<'chart>, FrontPassageObstruction> {
        let plan = self.compile(complex, realization, material, source, terminal)?;
        let admission = self.admit(&plan, receiver, material_admission)?;
        self.realize(plan, material, admission)
    }
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
            let mut chain = found(first.0, &admittance, Standing::Carrying(admittance.value().clone()));
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
                chain.carry(crossing, to, Standing::Carrying(transmitted.value().clone()));
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
    pub admission: DeedAdmission,
    pub mode: ModeIdentity,
    pub traffic: TrafficReading,
    terminal: EventId,
}

impl<'chart> CompiledPassage<'chart> {
    /// The section written at an occurrence's output, for the receiver to copy out.
    pub fn section(&self, occurrence: EventId) -> Option<&ResidentSection<'chart>> {
        self.sections.get(&occurrence)
    }
    pub fn terminal(&self) -> EventId {
        self.terminal
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
    pub fn read_section(&self, returned: &PassageReturn, occurrence: EventId) -> Result<Vec<(i64, i64)>, FrontPassageObstruction> {
        let index = self.index_of.get(&occurrence).copied().ok_or(FrontPassageObstruction::Compile(CompileRefusal::ForeignOccurrence { occurrence }))?;
        if !returned.obstruction.stands(index) {
            let (bound, _, operation) = self.bounds[&occurrence];
            let slot = returned.fronts.iter().flat_map(|f| f.readings.iter()).find(|r| r.occurrence == occurrence).map(|r| r.measured).unwrap_or_default();
            let refusal = slot.refusal(operation, bound).unwrap_or(ResidentRefusal::Upstream { operation: operation.to_owned() });
            return Err(FrontPassageObstruction::Refused { occurrence, operation: operation.to_owned(), refusal, slot, lineage: returned.obstruction.clone() });
        }
        self.surface.read_out(&self.sections[&occurrence]).map_err(surface_refusal)
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
        let actual = self.surface.mode();
        if *expected != actual {
            return Err(surface_refusal(ResidentRefusal::ModeMismatch { expected: Box::new(expected.clone()), actual: Box::new(actual) }));
        }
        let reading = self.passage.launch().map_err(surface_refusal)?;
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
        Ok(PassageReturn { fronts, census_before: reading.census_before, census_after: reading.census_after, measured_octaves, obstruction: reading.obstruction, refusals })
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

    const IMPLEMENTATION: &str = "class Site:\n    def enter(self):\n        x = words * scale\n    def scale(self):\n        y = x * 2\n    def hadamard(self):\n        z = x * x\n";

    fn occurrence() -> SourceOccurrence {
        SourceOccurrence {
            implementation: AuthenticatedText::of_text("/site.py", IMPLEMENTATION, None),
            configuration: AuthenticatedText::of_text("/config.json", r#"{"text_config": {"grain": 20}}"#, None),
            configuration_scope: vec!["text_config".to_owned()],
            container: AuthenticatedContainer { locator: "/none".to_owned(), octets: 0, header_octets: 0, header_sha256: String::new(), content_sha256: None, regions: BTreeMap::new() },
            assets: Vec::new(),
        }
    }

    /// A two-front diagram: `enter x` then co-present `{scale x by 2, hadamard x·x}`.
    fn small_diagram() -> (PortedOperationComplex, ResidentRealization, EventId, EventId, EventId) {
        let mut complex = PortedOperationComplex::new("small");
        let standing = complex.port("standing");
        let testimony = |symbol: &str| vec![SourceTestimony::Implementation { locator: "/site.py".to_owned(), symbol: symbol.to_owned() }, SourceTestimony::Configuration { field: "grain".to_owned(), value: "20".to_owned() }];
        let enter = complex.bind_operation("enter", OperationSpecies::Construction, vec![], vec![standing], None, testimony("Site.enter (x = words * scale)")).expect("law");
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
        fabricated.implementation = AuthenticatedText::of_text("/site.py", "class Site:\n    def enter(self):\n        x = words * scale\n", None);
        assert!(matches!(passage.compile(&complex, &realization, &material, &fabricated, s), Err(FrontPassageObstruction::Compile(CompileRefusal::Source(SourceRefusal::SymbolUnresolved { .. })))));
        let mut drifted = occurrence();
        drifted.configuration = AuthenticatedText::of_text("/config.json", r#"{"text_config": {"grain": 21}}"#, None);
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
        let testimony = |symbol: &str| vec![SourceTestimony::Implementation { locator: "/site.py".to_owned(), symbol: symbol.to_owned() }, SourceTestimony::Configuration { field: "grain".to_owned(), value: "20".to_owned() }];
        let enter = complex.bind_operation("enter", OperationSpecies::Construction, vec![], vec![standing], None, testimony("Site.enter (x = words * scale)")).expect("law");
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
}

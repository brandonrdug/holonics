use super::*;

pub(super) type ExactSet<T> = BTreeSet<T>;

pub(super) fn relational_cpu_error(
    error: CpuExecutionError<RelationalLanguageError>,
) -> RelationalLanguageError {
    match error {
        CpuExecutionError::Operation(error) => error,
        CpuExecutionError::WorkerPanicked => RelationalLanguageError::CarrierExtent,
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RelationalLanguageError {
    EmptyEcology,
    CarrierExtent,
    OpenCausalConflict(usize),
    MalformedClause,
    /// The continuing relation body still owns a caused passage whose complete return has not
    /// reached standing. A question may not observe its partially founded internal morphology.
    OpenPassage,
    Association(ResonanceEcologyError),
    Current(ExactReceiverCurrentError),
}

impl From<ResonanceEcologyError> for RelationalLanguageError {
    fn from(error: ResonanceEcologyError) -> Self {
        Self::Association(error)
    }
}

impl From<ExactReceiverCurrentError> for RelationalLanguageError {
    fn from(error: ExactReceiverCurrentError) -> Self {
        Self::Current(error)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum RelationalClauseVoice {
    Active,
    Passive,
    Copular,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RelationalEntity {
    pub surface: Vec<String>,
    pub identity: BTreeSet<String>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RelationalClause {
    pub identity: String,
    pub passage: String,
    pub source: String,
    pub receiver: u64,
    /// The source occurrence and its own serial clause strand remain separate coordinates.
    /// Neither caller slice position nor canonical identity becomes causal order.
    pub source_order: u128,
    pub source_order_declared: bool,
    pub source_local_step: u64,
    /// Semantic orientation. A witnessed passive clause is reversed here so incidence, not
    /// English word order, owns the carried relation.
    pub subject: RelationalEntity,
    pub relation: String,
    /// A witnessed modal remains part of the relation phase. Dropping `could` while realizing a
    /// clause would promote a proposed capacity into an asserted present fact.
    pub modality: Option<String>,
    pub object: RelationalEntity,
    pub witnessed_voice: RelationalClauseVoice,
    pub witnessed_surface: String,
}

/// The mutually alternative clause incidences admitted for one caused sentence occurrence.
///
/// The first member is the inherited transducer's present traversal, not an assertion that every
/// other member is false. Alternatives remain attached to the same occurrence rather than being
/// flattened into co-present facts.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RelationalParseFiber {
    pub identity: String,
    pub selected_clause: String,
    pub alternatives: Vec<RelationalClause>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RelationalJoin {
    pub from_clause: String,
    pub to_clause: String,
    pub shared_entity_faces: BTreeSet<String>,
    /// Clauses may also touch because one caused passage delivered them together, even when no
    /// nominal surface is repeated across the clause boundary.
    pub shared_passage: Option<String>,
    pub conduct: RelationalChannelConduct,
    pub recurrence_population: BigUint,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RelationalRealizationClause {
    pub relation_clause: String,
    pub text: String,
    pub sources: BTreeSet<String>,
    pub passages: BTreeSet<String>,
    pub inherited_contiguous: bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RelationalRealization {
    pub text: String,
    pub clauses: Vec<RelationalRealizationClause>,
    /// True when every clause was cast through the orientation opposed to its source witness.
    pub voice_dual: bool,
    pub inherited_contiguous: bool,
}

/// One caused relation passage in a receiver-local transport current.
///
/// `delay` and `arrival_chronology` are exact discrete causal-order coordinates. They are not
/// wall-clock time and do not pretend that linguistic transport has a physical speed measured in
/// metres per second. The passage identity is an operator letter; composing the retained letters
/// in order is the exact noncommutative transport product.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RelationalTransportPassage {
    pub identity: String,
    pub from_clause: String,
    pub to_clause: String,
    pub delay: u64,
    pub arrival_chronology: u64,
    pub shared_entity_faces: BTreeSet<String>,
    pub shared_passage: Option<String>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum RelationalTransportHand {
    Forward,
    Reverse,
}

/// The receiver-local state of one structurally possible clause contact.
///
/// A contact is not automatically a conducting edge. Co-present/source-continuous material and
/// an explicit caused output-to-input seam conduct from their inherited morphology. A separated
/// coincident face conducts only after the same complete junction phase has returned through two
/// distinct source pairs. Until then it remains an inspectable OPEN boundary.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum RelationalChannelConduct {
    Copresent,
    SourceContinuous,
    Caused,
    Ride,
    Open,
}

/// Exact testimony for one local channel reached by a causal relation front.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RelationalCausalChannel {
    pub from_clause: String,
    pub to_clause: String,
    pub shared_entity_faces: BTreeSet<String>,
    pub conduct: RelationalChannelConduct,
    /// Population of distinct source-pair occurrences carrying the complete junction phase.
    /// This is capacitance testimony, not a normalized score or probability.
    pub recurrence_population: BigUint,
}

/// One step in a fundamental return word. A reverse hand is retained rather than silently
/// commuting the relation past its opposed traversal.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RelationalHolonomyStep {
    pub passage: String,
    pub hand: RelationalTransportHand,
}

/// A chord and the exact ordered return word which it closes in the current relation body.
///
/// This is symbolic holonomy: it records the noncommuting operator itinerary without inventing a
/// numeric connection coefficient which the language ecology has not conditioned.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RelationalHolonomyGenerator {
    pub chord: String,
    pub ordered_return: Vec<RelationalHolonomyStep>,
}

/// One outward receiver chart over the same carried relation body.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RelationalReceiverQuotient {
    pub realization: usize,
    pub voice_dual: bool,
    pub inherited_contiguous: bool,
    pub surface: String,
}

/// The receiver-relative transport retained by one complete or open thought current.
///
/// The topology, chronology, branch capacity, stored open boundary, and outward charts remain
/// distinct. `ordered_transport_product` is a word in the current's caused passage operators;
/// it is deliberately not collapsed to a scalar score or a commutative bag of contacts.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RelationalCurrentTransport {
    pub components: Vec<BTreeSet<String>>,
    pub clause_arrivals: BTreeMap<String, u64>,
    pub passages: Vec<RelationalTransportPassage>,
    pub ordered_transport_product: Vec<String>,
    pub receiver_horizon: u64,
    pub local_branch_capacities: BTreeMap<String, BigUint>,
    pub boundary_storage: BTreeSet<usize>,
    pub holonomy_generators: Vec<RelationalHolonomyGenerator>,
    pub receiver_quotients: Vec<RelationalReceiverQuotient>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RelationalThoughtCurrent {
    pub question: String,
    pub clauses: Vec<RelationalClause>,
    pub joins: Vec<RelationalJoin>,
    pub required_entity_regions: Vec<BTreeSet<String>>,
    pub returned_entity_regions: BTreeSet<usize>,
    pub open_entity_regions: BTreeSet<usize>,
    pub source_witnesses: BTreeSet<String>,
    pub passage_witnesses: BTreeSet<String>,
    pub parse_fibers: Vec<RelationalParseFiber>,
    /// Exact population of transport alternatives retained by this complete current. The
    /// current is caused by the whole predecessor body; no receiver section is promoted into
    /// standing merely because an observer can un-rank it.
    pub factorized_transport_population: BigUint,
    /// Exact population of the parse-alternative product, retained as a factorized receipt.
    /// `realizations` exposes the selected path and each one-fiber receiver variation; it never
    /// materializes this Cartesian product merely to prove that the product exists.
    pub factorized_parse_population: BigUint,
    pub realizations: Vec<RelationalRealization>,
    pub selected_realization: usize,
    pub transport: RelationalCurrentTransport,
}

/// Every inclusion-minimal causal traversal presently admitted by one question.
///
/// A receiver may eventually expose one realization, but the other closed or still-open
/// traversals remain part of the contemporary thought morphology.  This is deliberately not a
/// ranked list of candidate strings: each current names the clauses, joins, parse fibers, and
/// unresolved entity regions which physically distinguish that traversal.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RelationalThoughtFiber {
    pub question: String,
    pub currents: Vec<RelationalThoughtCurrent>,
    /// Question regions which have not returned through one complete connected question current.
    ///
    /// A deliberative fiber may contain many locally closed currents without pretending that
    /// their coproduct already supplies the relation among them. A locally witnessed region may
    /// therefore remain here when it has not yet glued to the other question regions. Ordinary
    /// connected thought has this field empty exactly when one complete current has returned.
    pub unreturned_question_regions: Vec<BTreeSet<String>>,
    /// Factorized causal fronts which actually advanced the current. Every equal-arrival
    /// predecessor and its complete support remain present; no representative path is promoted
    /// into standing.
    pub causal_front_fibers: Vec<RelationalCausalFrontFiber>,
    /// Structurally possible contacts reached by the current which had not yet returned as a
    /// conducting local phase.
    pub open_channel_boundaries: Vec<RelationalCausalChannel>,
}

/// One receiver-local thought result together with separate apparatus testimony.
///
/// The physical receipt is deliberately not embedded in [`RelationalThoughtFiber`]: worker
/// placement cannot enter deterministic semantic equality. Each worker task reads the same
/// immutable relational predecessor and returns a detached traversal/current result; ordered
/// Swing conditioning remains outside this aperture.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RelationalThoughtExecution {
    pub fiber: Option<RelationalThoughtFiber>,
    pub cpu: Option<CpuExecutionReceipt>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RelationalCausalFrontFiber {
    pub source_clauses: LocalSequence<String>,
    /// Co-present target sections returned at this one receiver horizon.
    pub target_clauses: LocalSequence<String>,
    pub arrival_wave: u64,
    /// One shared predecessor incidence for the complete returned wave. It is not copied once per
    /// target, and its union is never asserted to be one enacted semantic path.
    pub predecessor_incidence: LocalRelations<String, LocalSet<String>>,
    /// Exact factorized path population at each returned target.
    pub exact_path_populations: LocalRelations<String, BigUint>,
    /// Union of every clause in the equal-arrival predecessor body. This is a factorized
    /// support chart over the retained predecessor incidence, not one claimed linear path.
    pub complete_support: LocalSet<String>,
    pub channels: LocalSequence<RelationalCausalChannel>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(super) enum RelationalJunctionRole {
    Subject,
    Object,
    CausedOutput,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(super) struct RelationalJunctionEndpoint {
    pub(super) relation: String,
    pub(super) modality: Option<String>,
    pub(super) roles: BTreeSet<RelationalJunctionRole>,
}

/// Delivery-gauge identity of a complete local junction phase. Clause and source identities are
/// deliberately absent: distinct occurrences must be able to recur through the same phase.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(super) struct RelationalJunctionPhase {
    pub(super) shared_entity_faces: BTreeSet<String>,
    pub(super) endpoints: [RelationalJunctionEndpoint; 2],
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(super) struct RelationalClauseMorphology {
    pub(super) subject: BTreeSet<String>,
    pub(super) relation: String,
    pub(super) modality: Option<String>,
    pub(super) object: BTreeSet<String>,
    pub(super) voice: RelationalClauseVoice,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct RelationalJunctionCandidate {
    pub(super) left: usize,
    pub(super) right: usize,
    pub(super) phase: RelationalJunctionPhase,
}

#[derive(Debug, PartialEq, Eq)]
pub(super) struct PendingRelationalJunction {
    pub(super) candidate: RelationalJunctionCandidate,
    pub(super) direct_contact_returned: bool,
    pub(super) swing_returned: Option<ResonanceOccurrenceRead>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) struct RelationalPassageStanding {
    pub(super) delivery_order: u64,
    pub(super) complete: bool,
    pub(super) acknowledged: bool,
}

pub(super) struct RelationalPassageProposal {
    pub(super) surfaces: LocalSequence<Vec<String>>,
    pub(super) clauses: LocalSequence<RelationalClause>,
    pub(super) parse_fibers: LocalSequence<RelationalParseFiber>,
    pub(super) predicates: LocalSet<String>,
}

/// One caused language occurrence while its morphology is crossing into the continuing body.
///
/// Every cursor names a completed causal stage. Recoverable refusal returns this owner intact;
/// retry resumes the first unreturned stage and never rolls the ecology back or replays a stage
/// which has already changed standing.
pub(super) struct OpenRelationalPassage {
    pub(super) identity: Option<String>,
    pub(super) delivery_order: u64,
    pub(super) proposal: Option<RelationalPassageProposal>,
    pub(super) first_new_clause: Option<usize>,
    pub(super) next_current_site: usize,
    pub(super) candidates: Option<LocalSequence<RelationalJunctionCandidate>>,
    pub(super) junctions_queued: bool,
    /// Co-present fronts defer their shared Swing mouth until every member has completed its
    /// structural ingress. Ordered passage reception leaves this false.
    pub(super) defer_junctions: bool,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) struct PendingReceiverCurrentPair {
    pub(super) passages: [ReceiverCurrentPassageId; 2],
}

/// Apparatus testimony for the one continuing relation body.
///
/// The requested aperture is reported separately from the admitted Swing lane. Until a complete
/// successor-commutation receipt exists, junction events remain one ordered current even when
/// independent morphology construction is physically concurrent elsewhere.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RelationalExecutionReceipt {
    pub requested_worker_threads: usize,
    pub clauses: usize,
    pub structural_junctions: usize,
    pub conducting_channels: usize,
    pub junction_phase_population: usize,
    pub pending_junctions: usize,
    pub open_passages: usize,
    pub pending_current_pairs: usize,
    pub received_passages: usize,
    pub association_memory: LiveMemory,
}

#[derive(Debug, PartialEq, Eq)]
pub(super) struct RelationalRadiatedSection {
    pub(super) selected: BTreeSet<usize>,
    pub(super) enacted_pairs: BTreeSet<(usize, usize)>,
    pub(super) clause_arrivals: BTreeMap<usize, u64>,
    pub(super) passages: Vec<RelationalTransportPassage>,
    pub(super) receiver_horizon: u64,
    pub(super) factorized_path_population: BigUint,
}

/// Plural receiver scales emitted by one visible question before any exterior material returns.
///
/// `leader_regions` retains the complete nominal faces as contextual contacts while
/// `required_regions` exposes their local constituents as simultaneous obligations.  A broad
/// phrase can therefore be transported across several connected clauses without pretending that
/// one source entity already contained the whole phrase.  The complete face is not discarded: it
/// remains the higher-grain leader which recruits passages where several constituents are
/// genuinely co-present.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RelationalQuestionFrontier {
    pub leader_regions: Vec<BTreeSet<String>>,
    pub required_regions: Vec<BTreeSet<String>>,
}

impl RelationalThoughtFiber {
    pub fn closed(&self) -> impl Iterator<Item = &RelationalThoughtCurrent> {
        self.currents.iter().filter(|current| current.is_closed())
    }

    pub fn open(&self) -> impl Iterator<Item = &RelationalThoughtCurrent> {
        self.currents.iter().filter(|current| !current.is_closed())
    }

    pub fn is_closed(&self) -> bool {
        self.unreturned_question_regions.is_empty() && self.closed().next().is_some()
    }
}

impl RelationalThoughtCurrent {
    pub fn selected(&self) -> Option<&RelationalRealization> {
        self.realizations.get(self.selected_realization)
    }

    pub fn is_closed(&self) -> bool {
        !self.required_entity_regions.is_empty() && self.open_entity_regions.is_empty()
    }
}

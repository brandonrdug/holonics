//! Exact repository receivers and a recurrent laboratory-research current.
//!
//! The repository is not flattened into one prompt or copied into an answer context.  Theory
//! sentences and source-native Rust passages remain separate receiver sections.  A question
//! emits one leader for every entity region admitted by the inherited relational transducer;
//! every returned section conditions the same mounted [`ExactRelationalLanguageEcology`].  The
//! current may rest only after all emitted leaders have returned and at least one joined thought
//! traversal closes.  Plural minimal traversals remain inspectable after the outward receiver
//! exposes one generated realization.

use std::collections::{BTreeMap, BTreeSet};

use holonic_engine::CpuExecutionReceipt;
use holonic_engine::traversible_chain::CountedCrossing;

/// The in-flight reading. **A phase that has not finished still has something to say.**
///
/// Every counter this emits was already computed and every one was trapped in a local until the
/// loop containing it returned — so a run that did not return reported nothing at all, which is why
/// three days of one-core hangs were diagnosed by guessing. `LaboratoryThoughtStep` is built per
/// wave and handed to the caller only on completion; these lines are the same quantities, radiated
/// as they are produced.
///
/// Enabled by `EROS_TRACE`, resolved once. It writes to stderr so a driver's own return stays clean.
pub(crate) fn eros_trace(phase: &str, detail: &std::fmt::Arguments<'_>) {
    use std::sync::OnceLock;
    static ENABLED: OnceLock<bool> = OnceLock::new();
    if *ENABLED.get_or_init(|| std::env::var_os("EROS_TRACE").is_some()) {
        eprintln!("eros-trace {phase:<28} {detail}");
    }
}

macro_rules! trace_phase {
    ($phase:expr, $($argument:tt)*) => {
        crate::laboratory_language::eros_trace($phase, &format_args!($($argument)*))
    };
}
use holonic_structure::{LocalRelations, LocalSequence, LocalSet};
use serde::{Deserialize, Serialize};

use crate::{
    causal_language::lexical_tokens,
    morphological_language::MorphologicalLanguagePassage,
    relational_language::{
        relational_deliberation_frontier, ExactRelationalLanguageEcology, RelationalCausalChannel,
        RelationalChannelConduct, RelationalLanguageError, RelationalThoughtCurrent,
        RelationalThoughtExecution, RelationalThoughtFiber, RelationalTransportHand,
    },
};

mod repository;

pub use repository::{
    LaboratoryAtlasReceipt, LaboratorySourceAtlas, LaboratorySourceReading, LaboratorySourceRoots,
};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LaboratoryLanguageError {
    Io(String),
    World(String),
    EmptyQuestion,
    NoQuestionRegions,
    CarrierExtent,
    /// A declared root resolves to nothing beneath the mounted repository.
    ///
    /// **This refusal exists because its absence made the whole agentic loop return nothing and say
    /// nothing.** `receive_paths` returns `Ok(())` for a root that does not exist, so a mount whose
    /// roots miss the material by one path component indexes zero sections, zero features, and the
    /// first question fails with `NoClosedCurrent` — a diagnosis about the *question* for a defect
    /// in the *mount*. A world that was handed a root and found nothing there must say so.
    DeclaredRootIsAbsent {
        root: String,
        beneath: String,
    },
    Relational(RelationalLanguageError),
}

impl From<RelationalLanguageError> for LaboratoryLanguageError {
    fn from(value: RelationalLanguageError) -> Self {
        Self::Relational(value)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize)]
#[serde(rename_all = "kebab-case")]
pub enum LaboratorySourceKind {
    MathematicsReturn,
    CodeReturn,
    DialogueUser,
    DialogueAssistant,
    Theory,
    RustSource,
    EmanatedAnswer,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct LaboratoryResearchLeader {
    pub identity: String,
    pub question: String,
    pub region: BTreeSet<String>,
    /// The chronology this leader's traversal is admitted through — **not a count of sections.**
    ///
    /// A site's cost is its own: a junction between what the leader carries and what the site
    /// shares needs `⌈(R+M)²/(4RM)⌉` service rounds, one when they match and more as they separate.
    /// A site whose rounds exceed this horizon **defers** — retained by name with its exact
    /// reflection — rather than being refused.
    ///
    /// This replaced `aperture: usize` on 2026-08-15. The count had exactly two settings and both
    /// were wrong: every finite value refused at `aperture + 1` on every material measured, and
    /// `usize::MAX` never refused, which made `omitted_population = complete − selected` **zero by
    /// construction**. A count is not a viscosity; a chronology with a congestion dilation is.
    pub horizon: u64,
    /// Zero denotes a region emitted directly by the question.  Later generations are emitted by
    /// still-open thought currents after earlier world returns changed the body.
    pub generation: usize,
    pub caused_by_clauses: BTreeSet<String>,
}

/// What a junction between a leader and a site returned. **The one place the admission law is
/// spelled**, so the three world ports cannot drift apart on it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LeaderAdmission {
    /// The junction dilates within the leader's horizon; the current crosses.
    Crosses { service_rounds: u128 },
    /// The junction dilates past it. Retained, never refused.
    Defers {
        service_rounds: u128,
        reflection: (i128, u128),
    },
    /// The site shares nothing. There is no traveling section to fabricate, and this is a terminus
    /// by type rather than a comparison against a small number.
    NoTravelingSection,
}

impl LaboratoryResearchLeader {
    /// Cross a site that shares `shared` of this leader's region.
    ///
    /// The incident admittance is what the leader carries (`|region|`), the transmitted admittance
    /// is what the site shares, and the cost is
    /// `⌈(R + M)² / (4RM)⌉` — one round at a match, more as they separate. Both admittances are
    /// populations of the material; the horizon is the caller's declared chronology.
    ///
    /// **Why one leader-level method rather than a filter in each port.** Before 2026-08-15 three
    /// ports each spelled their own count truncation — `selected.len() > leader.aperture` returning
    /// an error in the repository port, `sections.len() >= leader.aperture` silently `continue`ing
    /// in the dialogue port, and an aperture clamp sizing device buffers in the card port. Two of
    /// the three **dropped** what they excluded. A law that three callers spell three ways is three
    /// laws.
    pub fn admits(&self, shared: usize) -> LeaderAdmission {
        let carried = self.region.len() as u64;
        let Ok(shared) = u64::try_from(shared) else {
            return LeaderAdmission::NoTravelingSection;
        };
        let Some(crossing) = CountedCrossing::meet(carried, shared) else {
            return LeaderAdmission::NoTravelingSection;
        };
        let service_rounds = crossing.service_rounds();
        if service_rounds > u128::from(self.horizon) {
            return LeaderAdmission::Defers {
                service_rounds,
                reflection: crossing.reflection_pair(),
            };
        }
        LeaderAdmission::Crosses { service_rounds }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct LaboratoryReturnedSection {
    pub identity: String,
    /// Stable identity of the inherited source occurrence.  Different leaders may encounter the
    /// same occurrence, but doing so does not manufacture another training event.
    pub source_identity: String,
    pub source: String,
    pub receiver: u64,
    pub line: usize,
    pub kind: LaboratorySourceKind,
    pub text: String,
    pub matched_features: BTreeSet<String>,
}

impl LaboratoryReturnedSection {
    /// Cast this exact world occurrence through the generic language membrane without changing
    /// its stable source identity.  The richer section remains the lineage receipt; the passage
    /// is the receiver face admitted by language owners.
    pub fn passage(&self) -> MorphologicalLanguagePassage {
        MorphologicalLanguagePassage::new(
            self.source_identity.clone(),
            self.source.clone(),
            self.receiver,
            self.text.clone(),
        )
        // Line is chronology only inside this exact source. Receiver numbering addresses a chart
        // and must never turn lexically sorted repository paths into one global causal clock.
        .with_source_order(self.line as u128)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct LaboratoryWorldReturn {
    pub leader: String,
    pub sections: Vec<LaboratoryReturnedSection>,
    pub complete_population: usize,
    pub omitted_population: usize,
    /// What the traversal met and did not cross, **retained with its exact reflection**.
    ///
    /// Reflection is not loss; it is the retained fiber of a junction that did not match. A rank is
    /// only meaningful against the population that did not connect, so dropping these would delete
    /// the null every reading here is taken against.
    pub deferred: Vec<LaboratoryDeferredSection>,
}

/// A site the leader met whose junction dilated past its horizon. Kept, not discarded.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct LaboratoryDeferredSection {
    pub source_identity: String,
    pub source: String,
    pub matched_features: Vec<String>,
    /// What the junction cost: `⌈(R+M)²/(4RM)⌉`, from the two populations and nothing else.
    pub service_rounds: u128,
    /// `Γ = (R − M) : (R + M)`, carried as a pair and never divided — the exact share that turned
    /// back at this junction.
    pub reflection: (i128, u128),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum LaboratoryInformantPort {
    RepositorySource,
    ResidentTextCard,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LaboratoryWorldContactRequest {
    pub identity: String,
    pub leader: LaboratoryResearchLeader,
    pub port: LaboratoryInformantPort,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LaboratoryWorldContactReturn {
    pub identity: String,
    pub leader: String,
    pub port: LaboratoryInformantPort,
    pub returned: LaboratoryWorldReturn,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LaboratoryWorldContactOutcome {
    Returned(LaboratoryWorldContactReturn),
    Obstructed {
        identity: String,
        obstruction: String,
    },
}

/// One typed attempt over exactly the unresolved members exposed by the research owner.
/// Apparatus testimony is separate and cannot become event chronology. A member obstruction is
/// returned in-band so successful siblings remain available to the continuing frontier.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LaboratoryWorldContactAttempt {
    pub outcomes: LocalSequence<LaboratoryWorldContactOutcome>,
    pub execution: Option<CpuExecutionReceipt>,
}

impl LaboratoryWorldContactAttempt {
    /// Glue independently enacted informant-port attempts back into the exact unresolved address
    /// order emitted by the research owner. No application may author a joined world return or
    /// silently omit, duplicate, or substitute a semantic member.
    pub fn compose(
        requested: &[LaboratoryWorldContactRequest],
        attempts: impl IntoIterator<Item = Self>,
    ) -> Result<Self, LaboratoryLanguageError> {
        let mut received = LocalRelations::<String, LaboratoryWorldContactOutcome>::new();
        let mut executions = LocalSequence::new();
        for attempt in attempts {
            if let Some(execution) = attempt.execution {
                executions.push(execution);
            }
            for outcome in attempt.outcomes {
                let identity = match &outcome {
                    LaboratoryWorldContactOutcome::Returned(returned) => &returned.identity,
                    LaboratoryWorldContactOutcome::Obstructed { identity, .. } => identity,
                };
                if !requested
                    .iter()
                    .any(|request| request.identity == *identity)
                    || received.contains(identity)
                {
                    return Err(LaboratoryLanguageError::World(format!(
                        "a composed contact attempt duplicated or substituted {identity}"
                    )));
                }
                received
                    .try_insert(identity.clone(), outcome)
                    .map_err(|_| LaboratoryLanguageError::CarrierExtent)?;
            }
        }
        let mut outcomes = LocalSequence::with_capacity(requested.len());
        for request in requested {
            outcomes.push(received.remove(&request.identity).ok_or_else(|| {
                LaboratoryLanguageError::World(format!(
                    "a composed contact attempt omitted {}",
                    request.identity
                ))
            })?);
        }
        if !received.is_empty() {
            return Err(LaboratoryLanguageError::World(
                "a composed contact attempt retained a foreign member".to_owned(),
            ));
        }
        Ok(Self {
            outcomes,
            execution: (!executions.is_empty())
                .then(|| CpuExecutionReceipt::sequential_components(&executions)),
        })
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct LaboratoryThoughtStep {
    /// Every leader in one co-present causal antichain. Their exterior returns are all obtained
    /// before any of them conditions the language body.
    pub leaders: Vec<String>,
    pub arrival_chronology: u64,
    pub generation: usize,
    pub returned_sections: usize,
    pub complete_return_population: usize,
    pub omitted_return_population: usize,
    pub newly_conditioned_passages: usize,
    pub conditioned_passages_before: usize,
    pub conditioned_passages: usize,
    pub relational_clauses_before: usize,
    pub relational_clauses_after: usize,
    pub current_population: usize,
    pub closed_current_population: usize,
    pub phase_passage_population: usize,
    pub returned_entity_region_population: usize,
    pub world_execution: Option<CpuExecutionReceipt>,
    /// Physical realization of the read-only seed/current antichains. It is separate from the
    /// semantic fiber and therefore cannot change deterministic answer equality.
    pub traversal_execution: Option<CpuExecutionReceipt>,
    pub open_front_population_before: usize,
    pub open_fronts: Vec<Vec<Vec<String>>>,
    pub sources: BTreeSet<String>,
}

/// An exact discrete quotient formed by one receiver over a caused chronology interval.
/// Distances retain their units. These quotients are not silently interpreted as physical metres
/// per second, probabilities, or scalar quality scores.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct LaboratoryTransportPassageReceipt {
    pub identity: String,
    pub from_clause: String,
    pub to_clause: String,
    pub delay: u64,
    pub arrival_chronology: u64,
    pub shared_entity_faces: BTreeSet<String>,
    pub shared_passage: Option<String>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct LaboratoryHolonomyStepReceipt {
    pub passage: String,
    pub hand: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct LaboratoryHolonomyGeneratorReceipt {
    pub chord: String,
    pub ordered_return: Vec<LaboratoryHolonomyStepReceipt>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct LaboratoryReceiverQuotientReceipt {
    pub realization: usize,
    pub voice_dual: bool,
    pub inherited_contiguous: bool,
    pub surface: String,
}

/// The exact path product and receiver faces retained by one relational current.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct LaboratoryRelationalTransportReceipt {
    pub components: Vec<BTreeSet<String>>,
    pub clause_arrivals: BTreeMap<String, u64>,
    pub passages: Vec<LaboratoryTransportPassageReceipt>,
    pub ordered_transport_product: Vec<String>,
    pub receiver_horizon: u64,
    pub local_branch_capacities: BTreeMap<String, String>,
    pub boundary_storage: Vec<Vec<String>>,
    pub holonomy_generators: Vec<LaboratoryHolonomyGeneratorReceipt>,
    pub receiver_quotients: Vec<LaboratoryReceiverQuotientReceipt>,
}

/// Whether a caused passage founded, extended, or left unchanged the continuing morphology.
///
/// This is deliberately independent from the shape of a particular question's continuation
/// fiber. Extending the carrier can narrow one query, enlarge another, and leave a third equal.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
#[serde(rename_all = "kebab-case")]
pub enum LaboratoryMorphologyChange {
    Founded,
    Extended,
    Unchanged,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct LaboratoryContinuationJoinReceipt {
    pub from_clause: String,
    pub to_clause: String,
    pub conduct: String,
    pub recurrence_population: String,
}

/// One structurally exact continuation current exposed by a receiver query.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct LaboratoryContinuationCurrentReceipt {
    pub closed: bool,
    pub clause_identities: Vec<String>,
    pub joins: Vec<LaboratoryContinuationJoinReceipt>,
    pub required_entity_regions: Vec<Vec<String>>,
    pub returned_entity_regions: Vec<usize>,
    pub open_entity_regions: Vec<Vec<String>>,
    pub source_witnesses: BTreeSet<String>,
    pub passage_witnesses: BTreeSet<String>,
    /// Decimal exact population of transport witnesses retained behind this receiver section.
    pub factorized_transport_population: String,
    /// Decimal rendering of the exact arbitrary-precision parse-product population.
    pub factorized_parse_population: String,
    pub exposed_realization_population: usize,
    pub transport: LaboratoryRelationalTransportReceipt,
}

/// A receiver's complete retained continuation fiber at one caused boundary.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct LaboratoryContinuationFiberReceipt {
    pub current_population: usize,
    pub closed_current_population: usize,
    pub open_current_population: usize,
    /// Outer question regions not returned by any local current. Locally closed currents do not
    /// erase this boundary.
    pub unreturned_question_regions: Vec<Vec<String>>,
    pub currents: Vec<LaboratoryContinuationCurrentReceipt>,
    /// Inclusion-minimal passage families among the closed currents. Equal generated surfaces do
    /// not collapse distinct witness families.
    pub minimal_closed_witness_families: Vec<BTreeSet<String>>,
    /// Factorized equal-arrival causal fronts encountered while forming the currents. Every
    /// predecessor and the full support which advanced remain visible without enumerating paths.
    pub causal_front_fibers: LocalSequence<LaboratoryCausalFrontFiberReceipt>,
    /// Reached structural contacts whose local junction phase had not yet returned as conduct.
    pub open_channel_boundaries: Vec<LaboratoryCausalChannelReceipt>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct LaboratoryCausalFrontFiberReceipt {
    pub source_clauses: LocalSequence<String>,
    pub target_clauses: LocalSequence<String>,
    pub arrival_wave: u64,
    pub predecessor_incidence: LocalRelations<String, LocalSet<String>>,
    pub exact_path_populations: LocalRelations<String, String>,
    pub complete_support: LocalSet<String>,
    pub channels: LocalSequence<LaboratoryCausalChannelReceipt>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct LaboratoryCausalChannelReceipt {
    pub from_clause: String,
    pub to_clause: String,
    pub shared_entity_faces: BTreeSet<String>,
    pub conduct: String,
    pub recurrence_population: String,
}

/// Deterministic logical work caused while the question recruited its local world.
///
/// Physical elapsed time, bytes, device work, and energy belong to the exterior experiment
/// receipt because they vary between realizations and must not alter answer equality.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct LaboratoryLogicalWorkReceipt {
    pub leader_population: usize,
    pub causal_wave_population: usize,
    pub returned_section_population: usize,
    /// Population presented by each world return before the outer leader aperture. Individual
    /// source membranes may retain larger candidate stars in their own resource receipts.
    pub world_return_pre_aperture_population: usize,
    pub world_return_omitted_population: usize,
    pub newly_conditioned_passage_population: usize,
    pub thought_current_visits: usize,
    pub peak_current_population: usize,
    pub peak_open_front_population: usize,
}

/// Causal-information receipt when a separate continuing intelligence, rather than this
/// research organ's terminal projector, emits the answer which returns as conditioning.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct LaboratoryEmanatedCausalInformationReceipt {
    pub schema: String,
    pub world_conditioning: LaboratoryMorphologyChange,
    pub emanated_answer_conditioning: LaboratoryMorphologyChange,
    pub conditioned_passages_before: usize,
    pub conditioned_passages_after_world: usize,
    pub conditioned_passages_after_emanated_answer: usize,
    pub relational_clauses_before: usize,
    pub relational_clauses_after_world: usize,
    pub relational_clauses_after_emanated_answer: usize,
    pub continuation_before_contact: Option<LaboratoryContinuationFiberReceipt>,
    pub continuation_after_world: Option<LaboratoryContinuationFiberReceipt>,
    pub continuation_after_emanated_answer_return: Option<LaboratoryContinuationFiberReceipt>,
    pub selected_witness_family: BTreeSet<String>,
    pub answer_passage_identities: Vec<String>,
    pub logical_work: LaboratoryLogicalWorkReceipt,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct LaboratoryResearchSpec {
    /// The chronology each leader's traversal is admitted through. **Declared by the caller,
    /// reported in the receipt, and never authored inside an organ.**
    ///
    /// What would derive it rather than declare it: the material's own service-round distribution,
    /// which this spec does not yet consult. Until then it is an `APERTURE` in the sense of
    /// `canon/THE_AUTHORED_LEVEL.md` — a declared receiver coordinate whose orbit must be exhibited
    /// before any reading taken through it is evidence.
    pub leader_horizon: u64,
    /// Apparatus aperture for independent receiver-local thought currents. Ordered Swing
    /// conditioning remains one lineage even when this aperture is plural.
    pub worker_threads: usize,
    /// Exact receiver chronology admitted for each relational source section. This is distinct
    /// from the world-return aperture and from the number of exterior thought waves.
    pub thought_receiver_horizon: u64,
}

impl Default for LaboratoryResearchSpec {
    fn default() -> Self {
        Self {
            leader_horizon: 8,
            worker_threads: 1,
            thought_receiver_horizon: 16,
        }
    }
}

impl LaboratoryResearchSpec {
    /// Traverse at a declared chronology horizon.
    ///
    /// **This replaced `complete_local_star()` on 2026-08-15 and the replacement is the point.**
    /// That constructor set `leader_aperture: usize::MAX` because every finite count refused — a
    /// leader's caused region reaches more of a repository of this size than any authored count
    /// admits, so a finite aperture there was a guaranteed refusal rather than a bound. The
    /// unbounded form was the only remaining setting, and it made the omitted population zero by
    /// construction: nothing was ever omitted, so nothing was ever retained or reported, and the
    /// atlas's own promise to keep the alternatives could not be kept.
    ///
    /// A horizon is not that. A site's cost comes out of its own junction, congestion dilates it,
    /// and what dilates past the horizon **defers rather than refusing.** As a leader's region grows
    /// the same weak match becomes expensive on its own, which is the negative feedback a count
    /// could not supply.
    pub const fn at_horizon(leader_horizon: u64) -> Self {
        Self {
            leader_horizon,
            worker_threads: 1,
            thought_receiver_horizon: 16,
        }
    }
}

/// Complete internal testimony from a question even when no outward answer has yet closed.
///
/// The outward answer mouth still refuses to project an open current as a settled answer. An
/// autonomous ecology can instead receive this body, let its open currents cause further
/// questions, and return only the consequences which later close.
#[derive(Clone, Debug)]
pub struct LaboratoryResearchDeliberation {
    pub deed: String,
    pub question_identity: String,
    pub question: String,
    pub leaders: Vec<LaboratoryResearchLeader>,
    pub returns: Vec<LaboratoryWorldReturn>,
    pub thought_steps: Vec<LaboratoryThoughtStep>,
    pub fiber: Option<RelationalThoughtFiber>,
    pub conditioned_passages_before: usize,
    pub conditioned_passages_after: usize,
    pub relational_clauses_before: usize,
    pub relational_clauses_after: usize,
    pub continuation_before_contact: Option<LaboratoryContinuationFiberReceipt>,
}

#[derive(Debug)]
struct OpenLaboratoryWorldContactMember {
    request: LaboratoryWorldContactRequest,
    returned: Option<LaboratoryWorldContactReturn>,
    obstructions: LocalSequence<String>,
}

#[derive(Debug)]
struct OpenLaboratoryWorldContactFront {
    identity: String,
    wave: LocalSequence<LaboratoryResearchLeader>,
    members: LocalSequence<OpenLaboratoryWorldContactMember>,
    executions: LocalSequence<CpuExecutionReceipt>,
    conditioned_before_wave: usize,
    clauses_before_wave: usize,
    open_before_wave: usize,
    wave_returns: Option<LocalSequence<LaboratoryWorldReturn>>,
    newly_conditioned: Option<usize>,
}

impl OpenLaboratoryWorldContactFront {
    fn new(
        passage: &str,
        receiver_horizon: u64,
        wave: LocalSequence<LaboratoryResearchLeader>,
        conditioned_before_wave: usize,
        clauses_before_wave: usize,
        open_before_wave: usize,
    ) -> Self {
        let requests = open_world_contact_front(&wave);
        let members = requests
            .into_iter()
            .map(|request| OpenLaboratoryWorldContactMember {
                request,
                returned: None,
                obstructions: LocalSequence::new(),
            })
            .collect();
        Self {
            identity: format!("{passage}/world-front/{receiver_horizon}"),
            wave,
            members,
            executions: LocalSequence::new(),
            conditioned_before_wave,
            clauses_before_wave,
            open_before_wave,
            wave_returns: None,
            newly_conditioned: None,
        }
    }

    fn unresolved(&self) -> LocalSequence<LaboratoryWorldContactRequest> {
        self.members
            .iter()
            .filter(|member| member.returned.is_none())
            .map(|member| member.request.to_owned())
            .collect()
    }

    fn receive_attempt(
        &mut self,
        requested: &[LaboratoryWorldContactRequest],
        attempt: LaboratoryWorldContactAttempt,
    ) -> Result<(), LaboratoryLanguageError> {
        if attempt.outcomes.len() != requested.len() {
            return Err(LaboratoryLanguageError::World(format!(
                "{} returned an incomplete contact attempt",
                self.identity
            )));
        }
        let mut addressed = LocalSet::new();
        for outcome in &attempt.outcomes {
            let (identity, valid) = match outcome {
                LaboratoryWorldContactOutcome::Returned(returned) => {
                    let member = self
                        .members
                        .iter()
                        .find(|member| member.request.identity == returned.identity);
                    (
                        returned.identity.as_str(),
                        member.is_some_and(|member| {
                            member.returned.is_none()
                                && returned.leader == member.request.leader.identity
                                && returned.port == member.request.port
                                && returned.returned.leader == member.request.leader.identity
                        }),
                    )
                }
                LaboratoryWorldContactOutcome::Obstructed {
                    identity,
                    obstruction,
                } => {
                    let member = self
                        .members
                        .iter()
                        .find(|member| member.request.identity == *identity);
                    (
                        identity.as_str(),
                        member.is_some_and(|member| {
                            member.returned.is_none() && !obstruction.trim().is_empty()
                        }),
                    )
                }
            };
            if !valid
                || !addressed.insert(identity.to_owned())
                || !requested.iter().any(|request| request.identity == identity)
            {
                return Err(LaboratoryLanguageError::World(format!(
                    "{} returned a malformed, duplicate, or foreign contact {identity}",
                    self.identity
                )));
            }
        }
        for request in requested {
            if !addressed.contains(&request.identity) {
                return Err(LaboratoryLanguageError::World(format!(
                    "{} omitted contact {}",
                    self.identity, request.identity
                )));
            }
        }
        for outcome in attempt.outcomes {
            match outcome {
                LaboratoryWorldContactOutcome::Returned(returned) => {
                    let member = self
                        .members
                        .iter_mut()
                        .find(|member| member.request.identity == returned.identity)
                        .expect("the complete contact attempt was prevalidated");
                    member.returned = Some(returned);
                }
                LaboratoryWorldContactOutcome::Obstructed {
                    identity,
                    obstruction,
                } => {
                    let member = self
                        .members
                        .iter_mut()
                        .find(|member| member.request.identity == identity)
                        .expect("the complete obstruction attempt was prevalidated");
                    member.obstructions.push(obstruction);
                }
            }
        }
        if let Some(execution) = attempt.execution {
            self.executions.push(execution);
        }
        Ok(())
    }

    fn first_obstruction(&self) -> Option<String> {
        self.members.iter().find_map(|member| {
            (member.returned.is_none()).then(|| {
                member
                    .obstructions
                    .last()
                    .map_or_else(|| "contact remains open".to_owned(), ToOwned::to_owned)
            })
        })
    }

    fn execution(&self) -> Option<CpuExecutionReceipt> {
        (!self.executions.is_empty())
            .then(|| CpuExecutionReceipt::ordered_antichains(&self.executions))
    }
}

#[derive(Debug)]
struct OpenLaboratoryResearchPassage {
    deed: String,
    question_identity: String,
    question: String,
    required_regions: LocalSequence<BTreeSet<String>>,
    leaders: LocalSequence<LaboratoryResearchLeader>,
    pending: LocalSequence<LaboratoryResearchLeader>,
    visited_regions: LocalSet<BTreeSet<String>>,
    returns: LocalSequence<LaboratoryWorldReturn>,
    thought_steps: LocalSequence<LaboratoryThoughtStep>,
    last_fiber: Option<RelationalThoughtFiber>,
    receiver_horizon: u64,
    conditioned_passages_before: usize,
    relational_clauses_before: usize,
    continuation_before_contact: Option<LaboratoryContinuationFiberReceipt>,
    contact: Option<OpenLaboratoryWorldContactFront>,
}

impl OpenLaboratoryResearchPassage {
    fn into_deliberation(
        self,
        conditioned_passages_after: usize,
        relational_clauses_after: usize,
    ) -> LaboratoryResearchDeliberation {
        LaboratoryResearchDeliberation {
            deed: self.deed,
            question_identity: self.question_identity,
            question: self.question,
            leaders: self.leaders.into_inner(),
            returns: self.returns.into_inner(),
            thought_steps: self.thought_steps.into_inner(),
            fiber: self.last_fiber,
            conditioned_passages_before: self.conditioned_passages_before,
            conditioned_passages_after,
            relational_clauses_before: self.relational_clauses_before,
            relational_clauses_after,
            continuation_before_contact: self.continuation_before_contact,
        }
    }
}

/// One continuing research body. Source returns and self-emanated answers enter the same
/// relational ecology; no per-question `condition(passages)` reconstruction occurs here.
#[derive(Debug)]
pub struct LaboratoryResearchEcology {
    spec: LaboratoryResearchSpec,
    relation: Option<ExactRelationalLanguageEcology>,
    received_passages: LocalRelations<String, MorphologicalLanguagePassage>,
    received_order: LocalSequence<String>,
    conditioned_passages: usize,
    next_question: u64,
    next_leader: u64,
    open_passage: Option<OpenLaboratoryResearchPassage>,
    #[cfg(test)]
    refuse_next_emanated_return: bool,
}

impl LaboratoryResearchEcology {
    pub const fn new(spec: LaboratoryResearchSpec) -> Self {
        Self {
            spec,
            relation: None,
            received_passages: LocalRelations::new(),
            received_order: LocalSequence::new(),
            conditioned_passages: 0,
            next_question: 0,
            next_leader: 0,
            open_passage: None,
            #[cfg(test)]
            refuse_next_emanated_return: false,
        }
    }

    pub const fn conditioned_passages(&self) -> usize {
        self.conditioned_passages
    }

    pub fn relational_clauses(&self) -> usize {
        self.relation
            .as_ref()
            .map_or(0, |relation| relation.clauses().len())
    }

    /// Exterior deed currently carried by the research owner, if a returned world front has not
    /// yet completed its causal passage. This is an identity aperture only; frontier standing
    /// remains private to this body.
    pub fn open_deed_identity(&self) -> Option<&str> {
        self.open_passage.as_ref().map(|open| open.deed.as_str())
    }

    /// Inspect the contemporary plural continuation of a broad question without causing another
    /// exterior contact or changing standing.
    pub fn inspect_deliberative_continuation(
        &self,
        text: &str,
    ) -> Result<Option<LaboratoryContinuationFiberReceipt>, LaboratoryLanguageError> {
        let frontier = relational_deliberation_frontier(text);
        if frontier.required_regions.is_empty() {
            return Ok(None);
        }
        Ok(self
            .relation
            .as_ref()
            .map(|relation| {
                relation.think_deliberative_fiber_over_regions(
                    text,
                    &frontier.required_regions,
                    self.spec.thought_receiver_horizon,
                )
            })
            .transpose()?
            .flatten()
            .as_ref()
            .map(continuation_fiber_receipt))
    }

    /// Inspect the same contemporary relation body through the ordinary connected-question
    /// receiver without another exterior contact or standing change.
    ///
    /// This fiber is intentionally carried beside, rather than substituted for, the broader
    /// deliberative fiber. A local connected current may close at this scale while the larger
    /// constituent frontier still retains open alternatives.
    pub fn inspect_connected_question_fiber(
        &self,
        text: &str,
    ) -> Result<Option<RelationalThoughtFiber>, LaboratoryLanguageError> {
        if lexical_tokens(text).is_empty() {
            return Err(LaboratoryLanguageError::EmptyQuestion);
        }
        self.relation
            .as_ref()
            .map(|relation| relation.think_fiber(text, self.spec.thought_receiver_horizon))
            .transpose()
            .map(Option::flatten)
            .map_err(Into::into)
    }

    /// Condition the continuing research body with complete caused occurrences before or between
    /// questions. Stable passage identity makes an already received occurrence an exact no-op;
    /// a later message with equal visible text remains a distinct recurrence.
    pub fn condition_passages(
        &mut self,
        passages: &[MorphologicalLanguagePassage],
    ) -> Result<usize, LaboratoryLanguageError> {
        self.receive(passages)
    }

    /// Return passages emitted by a separate continuing intelligence and retain the complete
    /// before/world/answer continuation receipt around that conditioning event.
    pub fn receive_emanated_answer_passages(
        &mut self,
        deliberation: &LaboratoryResearchDeliberation,
        passages: &[MorphologicalLanguagePassage],
        selected_witness_family: BTreeSet<String>,
    ) -> Result<LaboratoryEmanatedCausalInformationReceipt, LaboratoryLanguageError> {
        #[cfg(test)]
        if std::mem::take(&mut self.refuse_next_emanated_return) {
            return Err(LaboratoryLanguageError::CarrierExtent);
        }
        let exact_return_already_standing = !passages.is_empty()
            && passages
                .iter()
                .all(|passage| self.received_passages.get(&passage.identity) == Some(passage));
        if (!exact_return_already_standing
            && self.conditioned_passages != deliberation.conditioned_passages_after)
            || (exact_return_already_standing
                && self.conditioned_passages <= deliberation.conditioned_passages_after)
        {
            return Err(LaboratoryLanguageError::CarrierExtent);
        }
        let conditioned_passages_after_world = deliberation.conditioned_passages_after;
        let relational_clauses_after_world = deliberation.relational_clauses_after;
        let continuation_after_world = deliberation.fiber.as_ref().map(continuation_fiber_receipt);
        let answer_passage_identities = passages
            .iter()
            .map(|passage| passage.identity.clone())
            .collect();
        let logical_work = logical_work_receipt(
            &deliberation.leaders,
            &deliberation.returns,
            &deliberation.thought_steps,
        )?;
        if !exact_return_already_standing {
            self.receive(passages)?;
        }
        let continuation_after_emanated_answer_return =
            self.inspect_deliberative_continuation(&deliberation.question)?;
        Ok(LaboratoryEmanatedCausalInformationReceipt {
            schema: "life.laboratory-emanated-causal-information.v1".to_owned(),
            world_conditioning: morphology_change(
                deliberation.conditioned_passages_before,
                conditioned_passages_after_world,
            ),
            emanated_answer_conditioning: morphology_change(
                conditioned_passages_after_world,
                self.conditioned_passages,
            ),
            conditioned_passages_before: deliberation.conditioned_passages_before,
            conditioned_passages_after_world,
            conditioned_passages_after_emanated_answer: self.conditioned_passages,
            relational_clauses_before: deliberation.relational_clauses_before,
            relational_clauses_after_world,
            relational_clauses_after_emanated_answer: self.relational_clauses(),
            continuation_before_contact: deliberation.continuation_before_contact.clone(),
            continuation_after_world,
            continuation_after_emanated_answer_return,
            selected_witness_family,
            answer_passage_identities,
            logical_work,
        })
    }

    /// Advance caused open fronts until one complete connected current can return. Other open
    /// currents remain in the same fiber as future alternatives; they are not exhausted through
    /// additional exterior deeds before the receiver may speak.
    pub fn deliberate_until_return_with_world_front(
        &mut self,
        deed: &str,
        text: &str,
        mut enact: impl FnMut(&[LaboratoryWorldContactRequest]) -> LaboratoryWorldContactAttempt,
    ) -> Result<LaboratoryResearchDeliberation, LaboratoryLanguageError> {
        self.conduct_through(deed, text, &mut enact)
    }

    fn conduct_through(
        &mut self,
        deed: &str,
        text: &str,
        enact: &mut impl FnMut(&[LaboratoryWorldContactRequest]) -> LaboratoryWorldContactAttempt,
    ) -> Result<LaboratoryResearchDeliberation, LaboratoryLanguageError> {
        if deed.trim().is_empty() || lexical_tokens(text).is_empty() {
            return Err(LaboratoryLanguageError::EmptyQuestion);
        }
        let mut open = match self.open_passage.take() {
            Some(open) => open,
            None => self.open_research_passage(deed, text)?,
        };
        if open.deed != deed || open.question != text {
            self.open_passage = Some(open);
            return Err(LaboratoryLanguageError::World(
                "another research passage owns the open world frontier".to_owned(),
            ));
        }
        match self.advance_open_research_passage(&mut open, enact) {
            Ok(()) => {
                Ok(open.into_deliberation(self.conditioned_passages, self.relational_clauses()))
            }
            Err(error) => {
                self.open_passage = Some(open);
                Err(error)
            }
        }
    }

    fn open_research_passage(
        &mut self,
        deed: &str,
        text: &str,
    ) -> Result<OpenLaboratoryResearchPassage, LaboratoryLanguageError> {
        let frontier = relational_deliberation_frontier(text);
        let (leader_regions, required_regions) =
            (frontier.leader_regions, frontier.required_regions);
        if leader_regions.is_empty() || required_regions.is_empty() {
            return Err(LaboratoryLanguageError::NoQuestionRegions);
        }
        let question_identity = format!("laboratory-question-{}", self.next_question);
        self.next_question = self
            .next_question
            .checked_add(1)
            .ok_or(LaboratoryLanguageError::CarrierExtent)?;
        let conditioned_passages_before = self.conditioned_passages;
        let relational_clauses_before = self.relational_clauses();
        let continuation_before_contact = self
            .relation
            .as_ref()
            .map(|relation| {
                think_relation_fiber(
                    relation,
                    text,
                    &required_regions,
                    self.spec.thought_receiver_horizon,
                )
            })
            .transpose()?
            .flatten()
            .as_ref()
            .map(continuation_fiber_receipt);
        let mut leaders = LocalSequence::with_capacity(leader_regions.len());
        for region in leader_regions {
            leaders.push(self.form_leader(&question_identity, text, region, 0, BTreeSet::new())?);
        }
        let visited_regions = leaders
            .iter()
            .map(|leader| leader.region.to_owned())
            .collect();
        Ok(OpenLaboratoryResearchPassage {
            deed: deed.to_owned(),
            question_identity,
            question: text.to_owned(),
            required_regions: LocalSequence::from_iter(required_regions),
            pending: leaders.to_owned(),
            leaders,
            visited_regions,
            returns: LocalSequence::new(),
            thought_steps: LocalSequence::new(),
            last_fiber: None,
            receiver_horizon: 0,
            conditioned_passages_before,
            relational_clauses_before,
            continuation_before_contact,
            contact: None,
        })
    }

    fn advance_open_research_passage(
        &mut self,
        open: &mut OpenLaboratoryResearchPassage,
        enact: &mut impl FnMut(&[LaboratoryWorldContactRequest]) -> LaboratoryWorldContactAttempt,
    ) -> Result<(), LaboratoryLanguageError> {
        loop {
            if open.contact.is_none() {
                if open.pending.is_empty() {
                    return Ok(());
                }
                let wave = std::mem::take(&mut open.pending);
                trace_phase!(
                    "wave.open",
                    "leaders {} visited_regions {} clauses {} passages {} region_extents {:?}",
                    wave.len(),
                    open.visited_regions.len(),
                    self.relational_clauses(),
                    self.conditioned_passages,
                    wave.iter().map(|l| l.region.len()).collect::<Vec<_>>()
                );
                let open_before_wave = open
                    .last_fiber
                    .as_ref()
                    .map(boundary_storage_population)
                    .transpose()?
                    .unwrap_or(0);
                open.contact = Some(OpenLaboratoryWorldContactFront::new(
                    &open.deed,
                    open.receiver_horizon,
                    wave,
                    self.conditioned_passages,
                    self.relational_clauses(),
                    open_before_wave,
                ));
            }

            let unresolved = open
                .contact
                .as_ref()
                .ok_or(LaboratoryLanguageError::CarrierExtent)?
                .unresolved();
            if !unresolved.is_empty() {
                trace_phase!("wave.enact.begin", "requests {}", unresolved.len());
                let began = std::time::Instant::now();
                let attempt = enact(&unresolved);
                trace_phase!(
                    "wave.enact.end",
                    "requests {} in {} ms",
                    unresolved.len(),
                    began.elapsed().as_millis()
                );
                open.contact
                    .as_mut()
                    .ok_or(LaboratoryLanguageError::CarrierExtent)?
                    .receive_attempt(&unresolved, attempt)?;
                if let Some(obstruction) = open
                    .contact
                    .as_ref()
                    .and_then(OpenLaboratoryWorldContactFront::first_obstruction)
                {
                    return Err(LaboratoryLanguageError::World(format!(
                        "{} remains open: {obstruction}",
                        open.contact
                            .as_ref()
                            .ok_or(LaboratoryLanguageError::CarrierExtent)?
                            .identity
                    )));
                }
            }

            if open
                .contact
                .as_ref()
                .is_some_and(|contact| contact.wave_returns.is_none())
            {
                let wave_returns = receive_world_contact_front(
                    open.contact
                        .as_ref()
                        .ok_or(LaboratoryLanguageError::CarrierExtent)?,
                )?;
                open.contact
                    .as_mut()
                    .ok_or(LaboratoryLanguageError::CarrierExtent)?
                    .wave_returns = Some(wave_returns);
            }

            if open
                .contact
                .as_ref()
                .is_some_and(|contact| contact.newly_conditioned.is_none())
            {
                let wave_passages = open
                    .contact
                    .as_ref()
                    .and_then(|contact| contact.wave_returns.as_ref())
                    .ok_or(LaboratoryLanguageError::CarrierExtent)?
                    .iter()
                    .flat_map(|returned| returned.sections.iter())
                    .map(LaboratoryReturnedSection::passage)
                    .collect::<LocalSequence<_>>();
                trace_phase!(
                    "wave.condition.begin",
                    "passages {} clauses_standing {}",
                    wave_passages.len(),
                    self.relational_clauses()
                );
                let began = std::time::Instant::now();
                let newly_conditioned = if wave_passages.is_empty() {
                    0
                } else {
                    self.receive_copresent(&wave_passages)?
                };
                trace_phase!(
                    "wave.condition.end",
                    "new {} clauses_standing {} in {} ms",
                    newly_conditioned,
                    self.relational_clauses(),
                    began.elapsed().as_millis()
                );
                open.contact
                    .as_mut()
                    .ok_or(LaboratoryLanguageError::CarrierExtent)?
                    .newly_conditioned = Some(newly_conditioned);
            }

            trace_phase!(
                "wave.radiate.begin",
                "clauses {} horizon {}",
                self.relational_clauses(),
                self.spec.thought_receiver_horizon
            );
            let radiate_began = std::time::Instant::now();
            let thought_execution = self
                .relation
                .as_ref()
                .map(|relation| {
                    think_relation_fiber_with_execution(
                        relation,
                        &open.question,
                        &open.required_regions,
                        self.spec.thought_receiver_horizon,
                    )
                })
                .transpose()?
                .unwrap_or(RelationalThoughtExecution {
                    fiber: None,
                    cpu: None,
                });
            trace_phase!(
                "wave.radiate.end",
                "currents {} in {} ms",
                thought_execution
                    .fiber
                    .as_ref()
                    .map_or(0, |fiber| fiber.currents.len()),
                radiate_began.elapsed().as_millis()
            );
            let fiber = thought_execution.fiber;
            let next_receiver_horizon = open
                .receiver_horizon
                .checked_add(1)
                .ok_or(LaboratoryLanguageError::CarrierExtent)?;
            let thought_step = {
                let contact = open
                    .contact
                    .as_ref()
                    .ok_or(LaboratoryLanguageError::CarrierExtent)?;
                let wave_returns = contact
                    .wave_returns
                    .as_ref()
                    .ok_or(LaboratoryLanguageError::CarrierExtent)?;
                thought_wave(
                    &contact.wave,
                    wave_returns,
                    next_receiver_horizon,
                    contact
                        .newly_conditioned
                        .ok_or(LaboratoryLanguageError::CarrierExtent)?,
                    contact.conditioned_before_wave,
                    self.conditioned_passages,
                    contact.clauses_before_wave,
                    self.relational_clauses(),
                    contact.open_before_wave,
                    fiber.as_ref(),
                    contact.execution(),
                    thought_execution.cpu,
                )?
            };
            let contact = open
                .contact
                .as_ref()
                .ok_or(LaboratoryLanguageError::CarrierExtent)?;
            let newly_conditioned = contact
                .newly_conditioned
                .ok_or(LaboratoryLanguageError::CarrierExtent)?;

            // Found the complete successor front before retiring the returned contact. Every
            // fallible extent check therefore occurs while the exact world-return frontier is
            // still retained by this owner. Once the contact is taken, the remainder is an
            // infallible ownership commit and cannot invite replay of the exterior event.
            let mut staged_continuations = LocalSequence::new();
            let mut staged_regions = LocalSet::new();
            let next_generation = if newly_conditioned > 0
                && fiber.as_ref().is_some_and(|fiber| !fiber.is_closed())
            {
                let generation = contact
                    .wave
                    .iter()
                    .map(|leader| leader.generation)
                    .max()
                    .unwrap_or(0)
                    .checked_add(1)
                    .ok_or(LaboratoryLanguageError::CarrierExtent)?;
                let active_fiber = fiber
                    .as_ref()
                    .ok_or(LaboratoryLanguageError::CarrierExtent)?;
                for (region, caused_by_clauses) in continuation_regions(active_fiber) {
                    let expanded = expand_features(region);
                    if expanded.is_empty()
                        || open.visited_regions.contains(&expanded)
                        || !staged_regions.insert(expanded.clone())
                    {
                        continue;
                    }
                    staged_continuations.push((expanded, caused_by_clauses));
                }
                Some(generation)
            } else {
                None
            };
            let staged_population = u64::try_from(staged_continuations.len())
                .map_err(|_| LaboratoryLanguageError::CarrierExtent)?;
            let next_leader_after_commit = self
                .next_leader
                .checked_add(staged_population)
                .ok_or(LaboratoryLanguageError::CarrierExtent)?;
            let first_staged_leader = self.next_leader;

            let contact = open.contact.take().expect(
                "the contact front was retained through complete successor-front preflight",
            );
            let wave_returns = contact
                .wave_returns
                .expect("complete contact preflight requires the owner-validated returned wave");
            open.receiver_horizon = next_receiver_horizon;
            open.thought_steps.push(thought_step);
            open.returns.extend(wave_returns);
            if fiber.is_some() {
                open.last_fiber = fiber;
            }

            let Some(next_generation) = next_generation else {
                return Ok(());
            };
            for (offset, (expanded, caused_by_clauses)) in
                staged_continuations.into_iter().enumerate()
            {
                let offset = u64::try_from(offset).expect("staged population already fit in u64");
                let identity_ordinal = first_staged_leader
                    .checked_add(offset)
                    .expect("the complete successor identity interval was preflighted");
                let leader = LaboratoryResearchLeader {
                    identity: format!("laboratory-leader-{identity_ordinal}"),
                    question: format!("{}: {}", open.question_identity, open.question),
                    region: expanded.clone(),
                    horizon: self.spec.leader_horizon.max(1),
                    generation: next_generation,
                    caused_by_clauses,
                };
                open.visited_regions.insert(expanded);
                open.leaders.push(leader.to_owned());
                open.pending.push(leader);
            }
            self.next_leader = next_leader_after_commit;
        }
    }

    fn form_leader(
        &mut self,
        question: &str,
        text: &str,
        region: BTreeSet<String>,
        generation: usize,
        caused_by_clauses: BTreeSet<String>,
    ) -> Result<LaboratoryResearchLeader, LaboratoryLanguageError> {
        let identity = format!("laboratory-leader-{}", self.next_leader);
        self.next_leader = self
            .next_leader
            .checked_add(1)
            .ok_or(LaboratoryLanguageError::CarrierExtent)?;
        Ok(LaboratoryResearchLeader {
            identity,
            question: format!("{question}: {text}"),
            region: expand_features(region),
            horizon: self.spec.leader_horizon.max(1),
            generation,
            caused_by_clauses,
        })
    }

    fn receive(
        &mut self,
        passages: &[MorphologicalLanguagePassage],
    ) -> Result<usize, LaboratoryLanguageError> {
        self.receive_mode(passages, false)
    }

    #[cfg(test)]
    pub(crate) fn receive_test_passages(
        &mut self,
        passages: &[MorphologicalLanguagePassage],
    ) -> Result<usize, LaboratoryLanguageError> {
        self.receive(passages)
    }

    #[cfg(test)]
    pub(crate) fn refuse_next_emanated_return_for_test(&mut self) {
        self.refuse_next_emanated_return = true;
    }

    fn receive_copresent(
        &mut self,
        passages: &[MorphologicalLanguagePassage],
    ) -> Result<usize, LaboratoryLanguageError> {
        self.receive_mode(passages, true)
    }

    fn receive_mode(
        &mut self,
        passages: &[MorphologicalLanguagePassage],
        copresent: bool,
    ) -> Result<usize, LaboratoryLanguageError> {
        for passage in passages {
            if self
                .received_passages
                .get(&passage.identity)
                .is_some_and(|standing| standing != passage)
            {
                return Err(LaboratoryLanguageError::CarrierExtent);
            }
        }
        let mut unseen_identities = LocalSet::new();
        let unseen = passages
            .iter()
            .filter(|passage| {
                !self.received_passages.contains(&passage.identity)
                    && unseen_identities.insert(passage.identity.to_owned())
            })
            .cloned()
            .collect::<Vec<_>>();
        if unseen.is_empty() {
            return Ok(0);
        }
        let conditioned_passages = self
            .conditioned_passages
            .checked_add(unseen.len())
            .ok_or(LaboratoryLanguageError::CarrierExtent)?;
        let received = if let Some(relation) = self.relation.as_mut() {
            if copresent {
                relation.receive_copresent_with_workers(&unseen, self.spec.worker_threads.max(1))?
            } else {
                relation.receive_with_workers(&unseen, self.spec.worker_threads.max(1))?
            }
        } else {
            self.relation = Some(if copresent {
                ExactRelationalLanguageEcology::condition_copresent_with_workers(
                    &unseen,
                    self.spec.worker_threads.max(1),
                )?
            } else {
                ExactRelationalLanguageEcology::condition_with_workers(
                    &unseen,
                    self.spec.worker_threads.max(1),
                )?
            });
            unseen.len()
        };
        if received != unseen.len() {
            return Err(LaboratoryLanguageError::CarrierExtent);
        }
        for passage in unseen {
            self.received_order.push(passage.identity.to_owned());
            self.received_passages
                .insert(passage.identity.clone(), passage);
        }
        self.conditioned_passages = conditioned_passages;
        Ok(received)
    }
}

const fn morphology_change(before: usize, after: usize) -> LaboratoryMorphologyChange {
    if after == before {
        LaboratoryMorphologyChange::Unchanged
    } else if before == 0 {
        LaboratoryMorphologyChange::Founded
    } else {
        LaboratoryMorphologyChange::Extended
    }
}

fn open_world_contact_front(
    leaders: &[LaboratoryResearchLeader],
) -> LocalSequence<LaboratoryWorldContactRequest> {
    let mut requests = LocalSequence::with_capacity(leaders.len().saturating_mul(2));
    for leader in leaders {
        for port in [
            LaboratoryInformantPort::RepositorySource,
            LaboratoryInformantPort::ResidentTextCard,
        ] {
            requests.push(LaboratoryWorldContactRequest {
                identity: format!("{}/{}", leader.identity, informant_port_name(port)),
                leader: leader.clone(),
                port,
            });
        }
    }
    requests
}

fn receive_world_contact_front(
    front: &OpenLaboratoryWorldContactFront,
) -> Result<LocalSequence<LaboratoryWorldReturn>, LaboratoryLanguageError> {
    if front.members.iter().any(|member| member.returned.is_none()) {
        return Err(LaboratoryLanguageError::World(
            "incomplete world-contact population".to_owned(),
        ));
    }
    let mut wave_returns = LocalSequence::with_capacity(front.wave.len());
    for leader in &front.wave {
        let mut sections = Vec::new();
        let mut complete_population = 0usize;
        let mut omitted_population = 0usize;
        // The deferred populations of both ports join here rather than being summed into a count.
        // Merging them as a number would be the collapse this whole carrier exists to refuse.
        let mut deferred = Vec::new();
        for port in [
            LaboratoryInformantPort::RepositorySource,
            LaboratoryInformantPort::ResidentTextCard,
        ] {
            let returned = front
                .members
                .iter()
                .find(|member| {
                    member.request.leader.identity == leader.identity && member.request.port == port
                })
                .and_then(|member| member.returned.as_ref())
                .ok_or(LaboratoryLanguageError::CarrierExtent)?;
            sections.extend(returned.returned.sections.iter().cloned());
            complete_population = complete_population
                .checked_add(returned.returned.complete_population)
                .ok_or(LaboratoryLanguageError::CarrierExtent)?;
            omitted_population = omitted_population
                .checked_add(returned.returned.omitted_population)
                .ok_or(LaboratoryLanguageError::CarrierExtent)?;
            deferred.extend(returned.returned.deferred.iter().cloned());
        }
        wave_returns.push(LaboratoryWorldReturn {
            leader: leader.identity.clone(),
            sections,
            complete_population,
            omitted_population,
            deferred,
        });
    }
    Ok(wave_returns)
}

const fn informant_port_name(port: LaboratoryInformantPort) -> &'static str {
    match port {
        LaboratoryInformantPort::RepositorySource => "repository-source",
        LaboratoryInformantPort::ResidentTextCard => "resident-text-card",
    }
}

fn think_relation_fiber(
    relation: &ExactRelationalLanguageEcology,
    text: &str,
    required_regions: &[BTreeSet<String>],
    receiver_horizon: u64,
) -> Result<Option<RelationalThoughtFiber>, RelationalLanguageError> {
    relation.think_deliberative_fiber_over_regions(text, required_regions, receiver_horizon)
}

fn think_relation_fiber_with_execution(
    relation: &ExactRelationalLanguageEcology,
    text: &str,
    required_regions: &[BTreeSet<String>],
    receiver_horizon: u64,
) -> Result<RelationalThoughtExecution, RelationalLanguageError> {
    relation.think_deliberative_fiber_over_regions_with_execution(
        text,
        required_regions,
        receiver_horizon,
    )
}

pub(crate) fn continuation_fiber_receipt(
    fiber: &RelationalThoughtFiber,
) -> LaboratoryContinuationFiberReceipt {
    let currents = fiber
        .currents
        .iter()
        .map(|current| LaboratoryContinuationCurrentReceipt {
            closed: current.is_closed(),
            clause_identities: current
                .clauses
                .iter()
                .map(|clause| clause.identity.clone())
                .collect(),
            joins: current
                .joins
                .iter()
                .map(|join| LaboratoryContinuationJoinReceipt {
                    from_clause: join.from_clause.clone(),
                    to_clause: join.to_clause.clone(),
                    conduct: match join.conduct {
                        RelationalChannelConduct::Copresent => "copresent",
                        RelationalChannelConduct::SourceContinuous => "source-continuous",
                        RelationalChannelConduct::Caused => "caused",
                        RelationalChannelConduct::Ride => "ride",
                        RelationalChannelConduct::Open => "open",
                    }
                    .to_owned(),
                    recurrence_population: join.recurrence_population.to_string(),
                })
                .collect(),
            required_entity_regions: current
                .required_entity_regions
                .iter()
                .map(|region| region.iter().cloned().collect())
                .collect(),
            returned_entity_regions: current.returned_entity_regions.iter().copied().collect(),
            open_entity_regions: current
                .open_entity_regions
                .iter()
                .filter_map(|at| current.required_entity_regions.get(*at))
                .map(|region| region.iter().cloned().collect())
                .collect(),
            source_witnesses: current.source_witnesses.clone(),
            passage_witnesses: current.passage_witnesses.clone(),
            factorized_transport_population: current.factorized_transport_population.to_string(),
            factorized_parse_population: current.factorized_parse_population.to_string(),
            exposed_realization_population: current.realizations.len(),
            transport: relational_transport_receipt(current),
        })
        .collect::<Vec<_>>();
    let closed_current_population = fiber.closed().count();
    let mut causal_front_fibers = LocalSequence::with_capacity(fiber.causal_front_fibers.len());
    for front in &fiber.causal_front_fibers {
        let mut source_clauses = LocalSequence::with_capacity(front.source_clauses.len());
        for source in &front.source_clauses {
            source_clauses.push(source.to_owned());
        }
        let mut target_clauses = LocalSequence::with_capacity(front.target_clauses.len());
        for target in &front.target_clauses {
            target_clauses.push(target.to_owned());
        }
        let mut predecessor_incidence = LocalRelations::new();
        for (target, incoming) in front.predecessor_incidence.iter() {
            let mut copied = LocalSet::new();
            for predecessor in incoming {
                copied.insert(predecessor.to_owned());
            }
            predecessor_incidence
                .try_insert(target.to_owned(), copied)
                .expect("causal-front receipt has the same bounded extent as its standing");
        }
        let mut exact_path_populations = LocalRelations::new();
        for (target, population) in front.exact_path_populations.iter() {
            exact_path_populations
                .try_insert(target.to_owned(), population.to_string())
                .expect("causal-front receipt has the same bounded extent as its standing");
        }
        let mut complete_support = LocalSet::new();
        for clause in &front.complete_support {
            complete_support.insert(clause.to_owned());
        }
        let mut channels = LocalSequence::with_capacity(front.channels.len());
        for channel in &front.channels {
            channels.push(causal_channel_receipt(channel));
        }
        causal_front_fibers.push(LaboratoryCausalFrontFiberReceipt {
            source_clauses,
            target_clauses,
            arrival_wave: front.arrival_wave,
            predecessor_incidence,
            exact_path_populations,
            complete_support,
            channels,
        });
    }
    LaboratoryContinuationFiberReceipt {
        current_population: currents.len(),
        closed_current_population,
        open_current_population: currents.len().saturating_sub(closed_current_population),
        unreturned_question_regions: fiber
            .unreturned_question_regions
            .iter()
            .map(|region| region.iter().cloned().collect())
            .collect(),
        minimal_closed_witness_families: minimal_closed_witness_families(fiber),
        causal_front_fibers,
        open_channel_boundaries: fiber
            .open_channel_boundaries
            .iter()
            .map(causal_channel_receipt)
            .collect(),
        currents,
    }
}

fn causal_channel_receipt(channel: &RelationalCausalChannel) -> LaboratoryCausalChannelReceipt {
    let conduct = match channel.conduct {
        RelationalChannelConduct::Copresent => "copresent",
        RelationalChannelConduct::SourceContinuous => "source-continuous",
        RelationalChannelConduct::Caused => "caused",
        RelationalChannelConduct::Ride => "ride",
        RelationalChannelConduct::Open => "open",
    };
    LaboratoryCausalChannelReceipt {
        from_clause: channel.from_clause.clone(),
        to_clause: channel.to_clause.clone(),
        shared_entity_faces: channel.shared_entity_faces.clone(),
        conduct: conduct.to_owned(),
        recurrence_population: channel.recurrence_population.to_string(),
    }
}

fn relational_transport_receipt(
    current: &RelationalThoughtCurrent,
) -> LaboratoryRelationalTransportReceipt {
    LaboratoryRelationalTransportReceipt {
        components: current.transport.components.clone(),
        clause_arrivals: current.transport.clause_arrivals.clone(),
        passages: current
            .transport
            .passages
            .iter()
            .map(|passage| LaboratoryTransportPassageReceipt {
                identity: passage.identity.clone(),
                from_clause: passage.from_clause.clone(),
                to_clause: passage.to_clause.clone(),
                delay: passage.delay,
                arrival_chronology: passage.arrival_chronology,
                shared_entity_faces: passage.shared_entity_faces.clone(),
                shared_passage: passage.shared_passage.clone(),
            })
            .collect(),
        ordered_transport_product: current.transport.ordered_transport_product.clone(),
        receiver_horizon: current.transport.receiver_horizon,
        local_branch_capacities: current
            .transport
            .local_branch_capacities
            .iter()
            .map(|(clause, population)| (clause.clone(), population.to_string()))
            .collect(),
        boundary_storage: current
            .transport
            .boundary_storage
            .iter()
            .filter_map(|at| current.required_entity_regions.get(*at))
            .map(|region| region.iter().cloned().collect())
            .collect(),
        holonomy_generators: current
            .transport
            .holonomy_generators
            .iter()
            .map(|generator| LaboratoryHolonomyGeneratorReceipt {
                chord: generator.chord.clone(),
                ordered_return: generator
                    .ordered_return
                    .iter()
                    .map(|step| LaboratoryHolonomyStepReceipt {
                        passage: step.passage.clone(),
                        hand: match step.hand {
                            RelationalTransportHand::Forward => "forward",
                            RelationalTransportHand::Reverse => "reverse",
                        }
                        .to_owned(),
                    })
                    .collect(),
            })
            .collect(),
        receiver_quotients: current
            .transport
            .receiver_quotients
            .iter()
            .map(|quotient| LaboratoryReceiverQuotientReceipt {
                realization: quotient.realization,
                voice_dual: quotient.voice_dual,
                inherited_contiguous: quotient.inherited_contiguous,
                surface: quotient.surface.clone(),
            })
            .collect(),
    }
}

fn minimal_closed_witness_families(fiber: &RelationalThoughtFiber) -> Vec<BTreeSet<String>> {
    let mut candidates = fiber
        .closed()
        .map(|current| current.passage_witnesses.clone())
        .collect::<Vec<_>>();
    candidates.sort_by(|left, right| left.len().cmp(&right.len()).then_with(|| left.cmp(right)));
    candidates.dedup();
    let mut minimal = Vec::<BTreeSet<String>>::new();
    for candidate in candidates {
        if minimal
            .iter()
            .any(|existing| existing.is_subset(&candidate))
        {
            continue;
        }
        minimal.push(candidate);
    }
    minimal
}

fn logical_work_receipt(
    leaders: &[LaboratoryResearchLeader],
    returns: &[LaboratoryWorldReturn],
    thought_steps: &[LaboratoryThoughtStep],
) -> Result<LaboratoryLogicalWorkReceipt, LaboratoryLanguageError> {
    let checked_sum = |values: Vec<usize>| {
        values.into_iter().try_fold(0usize, |sum, value| {
            sum.checked_add(value)
                .ok_or(LaboratoryLanguageError::CarrierExtent)
        })
    };
    Ok(LaboratoryLogicalWorkReceipt {
        leader_population: leaders.len(),
        causal_wave_population: leaders
            .iter()
            .map(|leader| leader.generation)
            .collect::<BTreeSet<_>>()
            .len(),
        returned_section_population: checked_sum(
            returns
                .iter()
                .map(|returned| returned.sections.len())
                .collect(),
        )?,
        world_return_pre_aperture_population: checked_sum(
            returns
                .iter()
                .map(|returned| returned.complete_population)
                .collect(),
        )?,
        world_return_omitted_population: checked_sum(
            returns
                .iter()
                .map(|returned| returned.omitted_population)
                .collect(),
        )?,
        newly_conditioned_passage_population: checked_sum(
            thought_steps
                .iter()
                .map(|step| step.newly_conditioned_passages)
                .collect(),
        )?,
        thought_current_visits: checked_sum(
            thought_steps
                .iter()
                .map(|step| step.current_population)
                .collect(),
        )?,
        peak_current_population: thought_steps
            .iter()
            .map(|step| step.current_population)
            .max()
            .unwrap_or(0),
        peak_open_front_population: thought_steps
            .iter()
            .map(|step| step.open_fronts.len())
            .max()
            .unwrap_or(0),
    })
}

#[allow(clippy::too_many_arguments)]
fn thought_wave(
    leaders: &[LaboratoryResearchLeader],
    returned: &[LaboratoryWorldReturn],
    arrival_chronology: u64,
    newly_conditioned_passages: usize,
    conditioned_passages_before: usize,
    conditioned_passages: usize,
    relational_clauses_before: usize,
    relational_clauses_after: usize,
    open_front_population_before: usize,
    fiber: Option<&RelationalThoughtFiber>,
    world_execution: Option<CpuExecutionReceipt>,
    traversal_execution: Option<CpuExecutionReceipt>,
) -> Result<LaboratoryThoughtStep, LaboratoryLanguageError> {
    let checked_sum = |values: Vec<usize>| {
        values.into_iter().try_fold(0usize, |sum, value| {
            sum.checked_add(value)
                .ok_or(LaboratoryLanguageError::CarrierExtent)
        })
    };
    let current_population = fiber.map_or(0, |fiber| fiber.currents.len());
    let closed_current_population = fiber.map_or(0, |fiber| fiber.closed().count());
    let phase_passage_population = fiber
        .map(|fiber| {
            checked_sum(
                fiber
                    .currents
                    .iter()
                    .map(|current| current.transport.passages.len())
                    .collect(),
            )
        })
        .transpose()?
        .unwrap_or(0);
    let returned_entity_region_population = fiber
        .map(|fiber| {
            checked_sum(
                fiber
                    .currents
                    .iter()
                    .map(|current| current.returned_entity_regions.len())
                    .collect(),
            )
        })
        .transpose()?
        .unwrap_or(0);
    let mut open_fronts = fiber
        .into_iter()
        .flat_map(RelationalThoughtFiber::open)
        .map(open_regions)
        .collect::<Vec<_>>();
    if let Some(fiber) = fiber {
        open_fronts.extend(
            fiber
                .unreturned_question_regions
                .iter()
                .map(|region| vec![region.iter().cloned().collect()]),
        );
    }
    let generation = leaders.first().map_or(0, |leader| leader.generation);
    if leaders.iter().any(|leader| leader.generation != generation) {
        return Err(LaboratoryLanguageError::CarrierExtent);
    }
    Ok(LaboratoryThoughtStep {
        leaders: leaders
            .iter()
            .map(|leader| leader.identity.clone())
            .collect(),
        arrival_chronology,
        generation,
        returned_sections: checked_sum(
            returned
                .iter()
                .map(|world_return| world_return.sections.len())
                .collect(),
        )?,
        complete_return_population: checked_sum(
            returned
                .iter()
                .map(|world_return| world_return.complete_population)
                .collect(),
        )?,
        omitted_return_population: checked_sum(
            returned
                .iter()
                .map(|world_return| world_return.omitted_population)
                .collect(),
        )?,
        newly_conditioned_passages,
        conditioned_passages_before,
        conditioned_passages,
        relational_clauses_before,
        relational_clauses_after,
        current_population,
        closed_current_population,
        phase_passage_population,
        returned_entity_region_population,
        world_execution,
        traversal_execution,
        open_front_population_before,
        open_fronts,
        sources: returned
            .iter()
            .flat_map(|world_return| world_return.sections.iter())
            .map(|section| section.source.clone())
            .collect(),
    })
}

/// Emit bridge leaders from every still-open causal current. The unresolved requested region is
/// paired with each subject/object face already reached by that current. These pairings are the
/// body's own next questions, so distinct currents can continue along distinct later pathways.
fn continuation_regions(
    fiber: &RelationalThoughtFiber,
) -> BTreeMap<BTreeSet<String>, BTreeSet<String>> {
    let mut regions = BTreeMap::<BTreeSet<String>, BTreeSet<String>>::new();
    for current in fiber.open() {
        let caused_by = current
            .clauses
            .iter()
            .map(|clause| clause.identity.clone())
            .collect::<BTreeSet<_>>();
        let Some(boundary_face) = current_boundary_region(current) else {
            continue;
        };
        for open_at in &current.open_entity_regions {
            let Some(open) = current.required_entity_regions.get(*open_at) else {
                continue;
            };
            let mut bridge = open.clone();
            bridge.extend(boundary_face.iter().cloned());
            if bridge != *open {
                regions
                    .entry(bridge)
                    .or_default()
                    .extend(caused_by.iter().cloned());
            }
        }
    }
    regions
}

/// The current's active exterior face is a returned question region incident to its terminal
/// clause. Full clause lineage remains in `caused_by`; it is not copied into the next receiver
/// address as one enormous nominal region.
fn current_boundary_region(current: &RelationalThoughtCurrent) -> Option<BTreeSet<String>> {
    let terminal = current.clauses.last()?;
    let head = terminal
        .object
        .surface
        .iter()
        .rev()
        .find_map(|word| {
            let normalized = word.to_lowercase();
            terminal
                .object
                .identity
                .iter()
                .find(|identity| normalized == **identity || normalized.starts_with(*identity))
                .cloned()
        })
        .or_else(|| terminal.object.identity.iter().next_back().cloned())?;
    Some(BTreeSet::from([head]))
}

fn open_regions(current: &RelationalThoughtCurrent) -> Vec<Vec<String>> {
    current
        .open_entity_regions
        .iter()
        .filter_map(|at| current.required_entity_regions.get(*at))
        .map(|region| region.iter().cloned().collect())
        .collect()
}

fn boundary_storage_population(
    fiber: &RelationalThoughtFiber,
) -> Result<usize, LaboratoryLanguageError> {
    let local = fiber.open().try_fold(0usize, |sum, current| {
        sum.checked_add(current.open_entity_regions.len())
            .ok_or(LaboratoryLanguageError::CarrierExtent)
    })?;
    local
        .checked_add(fiber.unreturned_question_regions.len())
        .ok_or(LaboratoryLanguageError::CarrierExtent)
}

fn identifier_words(identifier: &str) -> Vec<String> {
    let mut words = Vec::new();
    let mut current = String::new();
    let characters = identifier.chars().collect::<Vec<_>>();
    for (at, character) in characters.iter().copied().enumerate() {
        if character == '_' || character == '-' || character == '/' || character == '.' {
            if !current.is_empty() {
                words.push(std::mem::take(&mut current));
            }
            continue;
        }
        let boundary = !current.is_empty()
            && character.is_uppercase()
            && characters
                .get(at.saturating_sub(1))
                .is_some_and(|prior| prior.is_lowercase() || prior.is_ascii_digit());
        if boundary {
            words.push(std::mem::take(&mut current));
        }
        current.extend(character.to_lowercase());
    }
    if !current.is_empty() {
        words.push(current);
    }
    words
}

pub fn text_features(text: &str) -> BTreeSet<String> {
    lexical_tokens(text)
        .into_iter()
        .filter(|token| token.chars().any(char::is_alphanumeric))
        .flat_map(|token| {
            let mut words = identifier_words(&token);
            words.push(token.to_lowercase());
            words
        })
        .filter(|feature| !is_feature_operator(feature))
        .collect()
}

fn expand_features(features: BTreeSet<String>) -> BTreeSet<String> {
    features
        .into_iter()
        .flat_map(|feature| {
            let mut words = identifier_words(&feature);
            words.push(feature.to_lowercase());
            words
        })
        .filter(|feature| !is_feature_operator(feature))
        .collect()
}

fn is_feature_operator(feature: &str) -> bool {
    matches!(
        feature,
        "a" | "an"
            | "and"
            | "are"
            | "as"
            | "at"
            | "be"
            | "because"
            | "by"
            | "does"
            | "for"
            | "from"
            | "how"
            | "in"
            | "is"
            | "it"
            | "no"
            | "of"
            | "on"
            | "or"
            | "that"
            | "the"
            | "this"
            | "through"
            | "to"
            | "what"
            | "when"
            | "where"
            | "which"
            | "while"
            | "who"
            | "why"
            | "with"
    )
}

#[cfg(test)]
mod tests;

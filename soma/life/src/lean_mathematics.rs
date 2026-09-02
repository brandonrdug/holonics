//! Exact conditioning and kernel-return ecology for formal Lean mathematics.
//!
//! Lean source crosses as developmental material. The retained body is an incidence atlas of
//! declaration organs, binder charts, referenced declarations, and proof-motion species. Inherited
//! developmental sources depart; a kernel-admitted self-emanated declaration remains mounted as
//! the exact environment face needed by later kernel passages. A new theorem recruits its local declaration
//! star, composes plural proof paths from the conditioned organs, and sends every complete path to
//! Lean's kernel. Compiler acceptance or obstruction returns as typed testimony. No diagnostic,
//! tactic frequency, candidate ordinal, wall time, or source order becomes a proof score.

use std::{
    collections::BTreeSet,
    fs,
    path::{Path, PathBuf},
    process::Command,
    sync::Arc,
    time::Instant,
};

use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

use holonic_structure::{LocalRelations, LocalSequence, LocalSet};

mod candidates; mod ecology; mod lattice_mouth;
pub mod kernel_returns;
mod syntax;
#[cfg(test)] mod tests;

pub use lattice_mouth::*; pub use syntax::collect_lean_documents;

use kernel_returns::{LeanKernelOutcome, LeanKernelReturn, LeanKernelReturnFamily};

const REST_SCHEMA: &str = "life.lean-mathematics-ecology.v4";

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LeanMathematicsError {
    Io(String),
    Parse(String),
    InvalidRest,
    EmptyProblem,
    NoLocalDeclarations,
    NoProofCandidates,
    NoKernelAdmittedProof,
    KernelDeedAlreadyOpen,
    TargetSelectionAlreadyOpen,
    WrongKernelDeed,
    IncompleteKernelReturn,
    CarrierExtent,
}

impl std::fmt::Display for LeanMathematicsError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Io(error) => write!(formatter, "Lean world I/O obstruction: {error}"),
            Self::Parse(error) => write!(formatter, "Lean codec obstruction: {error}"),
            Self::InvalidRest => formatter.write_str("the Lean mathematics rest is invalid"),
            Self::EmptyProblem => formatter.write_str("the Lean theorem face is empty"),
            Self::NoLocalDeclarations => {
                formatter.write_str("the theorem reached no conditioned declaration organ")
            }
            Self::NoProofCandidates => {
                formatter.write_str("the local declaration star emitted no complete proof path")
            }
            Self::NoKernelAdmittedProof => {
                formatter.write_str("every generated proof path was obstructed by Lean")
            }
            Self::KernelDeedAlreadyOpen => {
                formatter.write_str("a Lean kernel deed is already open")
            }
            Self::TargetSelectionAlreadyOpen => {
                formatter.write_str("a Lean target-selection obstruction is already open")
            }
            Self::WrongKernelDeed => formatter.write_str("the Lean return names another deed"),
            Self::IncompleteKernelReturn => {
                formatter.write_str("the Lean kernel return population is incomplete")
            }
            Self::CarrierExtent => formatter.write_str("the Lean mathematics carrier overflowed"),
        }
    }
}

impl std::error::Error for LeanMathematicsError {}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LeanSourceDocument {
    pub path: String,
    pub text: String,
}

impl LeanSourceDocument {
    pub fn new(path: impl Into<String>, text: impl Into<String>) -> Self {
        Self {
            path: path.into(),
            text: text.into(),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct LeanBinderChart {
    pub name: String,
    pub explicit: bool,
    /// How the source wrote this binder. `explicit` is the coarse face of it and is retained so
    /// every existing reading still holds.
    #[serde(default)]
    pub kind: LeanBinderKind,
    /// The binder's **type, as the source wrote it**, normalised to single spaces.
    ///
    /// This is `H.0362`'s `D` — the parameter domain — and it was discarded at the destructuring
    /// `content.split_once(':')`, which bound the type to `_`. Without it an application cannot be
    /// typed at all, and the emission filled argument positions by matching binder **names** across
    /// two different declarations' frames.
    ///
    /// Empty when the source gave none: an instance binder is commonly written `[Fintype α]`, whose
    /// whole content is the type and whose name Lean synthesises.
    #[serde(default)]
    pub type_text: String,
}

/// Whether an emission is typed by the node it recruits, or offers every family to every organ.
///
/// `Inherited` is what every caller got before 2026-08-14 and remains the default, so nothing that
/// stands moves. `Typed` consults `H.0362`'s `(D, v)` before offering an edge:
///
/// - `rw [d]` is offered only where `d` concludes in an equality or an iff — that is
///   [`LeanDeclarationOrgan::rewritable`], and the untyped emission offered it to every organ,
///   producing exactly the 105 structural refusals a seven-declaration corpus returned;
/// - an application is built **in the recruited declaration's own frame**, position by position,
///   with `_` where the goal supplies no binder of that name — rather than by intersecting two
///   frames' binder names and silently dropping the rest.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum EmissionGrain {
    /// Every family offered to every organ, arguments by name intersection.
    #[default]
    Inherited,
    /// Families gated by `v`, arguments positional in the organ's own domain.
    Typed,
}

/// How a binder is written, which decides whether it occupies a positional argument slot.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum LeanBinderKind {
    /// `(x : T)` — supplied positionally.
    #[default]
    Explicit,
    /// `{x : T}` — inferred from later arguments.
    Implicit,
    /// `[Inst T]` — resolved by instance search, and commonly anonymous.
    Instance,
    /// `⦃x : T⦄` — strict implicit.
    StrictImplicit,
}

impl LeanBinderKind {
    /// Whether a binder of this kind is supplied in a positional application.
    pub const fn is_positional(self) -> bool {
        matches!(self, LeanBinderKind::Explicit)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct LeanDeclarationOrgan {
    pub source: String,
    pub name: String,
    pub binders: Vec<LeanBinderChart>,
    pub statement_identifiers: BTreeSet<String>,
    pub tactic_species: BTreeSet<String>,
    pub referenced_declarations: BTreeSet<String>,
    /// Algebraic constructors exposed by the declaration's outer result face. The source
    /// statement itself departs; this exact structural chart is sufficient to induce lawful
    /// eliminations such as conjunction projection without mounting a target-specific proof.
    pub result_constructors: BTreeSet<LeanResultConstructor>,
    /// The **principal relation** of this declaration's conclusion, when the material exposes
    /// exactly one at depth zero after the last top-level arrow.
    ///
    /// `None` is a real return and not a missing measurement: the conclusion carried no depth-zero
    /// relation, or it carried several and the reader will not guess which binds loosest. It is the
    /// component `H.0362` calls `v`, and it is what decides whether a declaration can carry a
    /// rewrite at all — [`LeanDeclarationOrgan::rewritable`].
    #[serde(default)]
    pub conclusion_relation: Option<String>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum LeanResultConstructor {
    Conjunction,
}

impl LeanDeclarationOrgan {
    /// Whether this declaration can carry a **rewrite** at all.
    ///
    /// `rw [d]` demands that `d` conclude in an equality or an iff — Lean says so in as many words
    /// when it refuses: *"Invalid rewrite argument: Expected an equality or iff proof."* It is
    /// `H.0362`'s `v` deciding an edge species before any kernel runs, and it is the whole content
    /// of the largest structural refusal this body has produced: on a seven-declaration corpus, five
    /// of the seven conclude in something else and the emission offered each of them twenty-one
    /// rewrites, for exactly the 105 refusals the kernel returned.
    ///
    /// `None` — the conclusion exposed no single depth-zero relation — is **not rewritable**. A
    /// reader that cannot see what a declaration concludes may not license a transport by it.
    pub fn rewritable(&self) -> bool {
        matches!(self.conclusion_relation.as_deref(), Some("=") | Some("↔"))
    }

    /// The conclusion's principal relation, or `"?"` when the material exposed none the reader could
    /// resolve. The placeholder is a **display** convenience and never enters a decision.
    pub fn relation_label(&self) -> &str {
        self.conclusion_relation.as_deref().unwrap_or("?")
    }
}

#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct LeanConditioningReceipt {
    pub source_documents_exposed: u64,
    pub source_bytes_exposed: u64,
    pub retained_source_surfaces: u64,
    pub declaration_organs: u64,
    pub binder_charts: u64,
    pub declaration_relations: u64,
    /// Inherited Lean proof-motion codecs supplied to the conditioned body. Their availability is
    /// not relabelled as learned from the corpus.
    pub mounted_codecs: BTreeSet<String>,
    pub tactic_species: BTreeSet<String>,
    pub result_constructors: BTreeSet<LeanResultConstructor>,
    /// The **principal relation** of this declaration's conclusion, when the material exposes
    /// exactly one at depth zero after the last top-level arrow.
    ///
    /// `None` is a real return and not a missing measurement: the conclusion carried no depth-zero
    /// relation, or it carried several and the reader will not guess which binds loosest. It is the
    /// component `H.0362` calls `v`, and it is what decides whether a declaration can carry a
    /// rewrite at all — [`LeanDeclarationOrgan::rewritable`].
    #[serde(default)]
    pub conclusion_relation: Option<String>,
    /// Complete kernel-return events which changed the continuing proof morphology.
    pub kernel_return_events: u64,
    /// Crossed proof paths admitted by the exterior Lean kernel.
    pub kernel_admitted_paths: u64,
    /// Crossed proof paths retained as exact kernel obstructions.
    pub kernel_obstructed_paths: u64,
    /// Kernel-admitted theorem organs caused by Eros' own proof passages.
    pub self_emanated_declarations: u64,
}

#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct LeanMathematicsEcology {
    schema: String,
    generation: u64,
    declarations: LocalRelations<String, LeanDeclarationOrgan>,
    identifier_incidence: LocalRelations<String, LocalSet<String>>,
    receipt: LeanConditioningReceipt,
    /// Returned proof morphology, not source or proof text. Every admitted and obstructed path
    /// remains distinguishable after the developmental candidate files depart.
    returned_theorems: LocalSequence<LeanReturnedTheoremFiber>,
    /// Kernel-admitted declarations emitted by this continuing body. These are mounted operative
    /// environment faces, not a retained developmental corpus or an application-side registry.
    returned_declaration_sources: LocalSequence<LeanReturnedDeclarationSource>,
    /// Complete kernel-observed sources for every admitted proof path. A plural admitted family
    /// remains plural even when no one path can lawfully become the mounted declaration.
    returned_generated_sources: LocalSequence<LeanGeneratedTheoremSourceFace>,
    /// Exact theorem-family crossings and their selected/open conduct. The Lean owner retains
    /// these faces; an application cannot become the hidden owner of selection history.
    target_selections: LocalSequence<LeanTargetSelectionStanding>,
    open_kernel_deed: Option<LeanKernelDeed>,
}

/// Source-detached ownership suspension of one continuing mathematical body. The live ecology is
/// consumed before this native standing can remount; no caller receives a second mutable owner.
#[derive(Debug)]
pub struct LeanMathematicsNativeRest {
    bytes: Box<[u8]>,
}

#[derive(Debug)]
pub struct LeanMathematicsNativeRestRefusal {
    pub error: LeanMathematicsError,
    body: Option<LeanMathematicsEcology>,
    rest: Option<LeanMathematicsNativeRest>,
}

impl LeanMathematicsNativeRestRefusal {
    pub fn recover_body(self) -> Option<LeanMathematicsEcology> {
        self.body
    }

    pub fn recover_rest(self) -> Option<LeanMathematicsNativeRest> {
        self.rest
    }
}

impl LeanMathematicsNativeRest {
    pub fn remount(self) -> Result<LeanMathematicsEcology, LeanMathematicsNativeRestRefusal> {
        match LeanMathematicsEcology::from_native_bytes(&self.bytes) {
            Ok(body) => Ok(body),
            Err(error) => Err(LeanMathematicsNativeRestRefusal {
                error,
                body: None,
                rest: Some(self),
            }),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct LeanProofProblem {
    pub identity: String,
    pub source_scope: BTreeSet<String>,
    /// Complete imports, namespaces, section variables, and notation needed before the theorem.
    pub prefix: String,
    /// A complete `theorem ... : ...` header without `:=` or a proof.
    pub theorem_header: String,
    pub suffix: String,
}

impl LeanProofProblem {
    pub fn validate(&self) -> Result<(), LeanMathematicsError> {
        if self.identity.trim().is_empty()
            || self.prefix.trim().is_empty()
            || self.theorem_header.trim().is_empty()
            || !self.theorem_header.trim_start().starts_with("theorem ")
            || self.theorem_header.contains(":=")
        {
            return Err(LeanMathematicsError::EmptyProblem);
        }
        Ok(())
    }

    pub fn render(&self, proof: &str) -> Result<String, LeanMathematicsError> {
        self.validate()?;
        if proof.trim().is_empty() || proof.contains("sorry") || proof.contains("admit") {
            return Err(LeanMathematicsError::NoKernelAdmittedProof);
        }
        Ok(format!(
            "{}\n{} := {}\n{}\n",
            self.prefix, self.theorem_header, proof, self.suffix
        ))
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum LeanDiagnosisRequirement {
    ClosedRemovalMinimalCurrent,
}

/// Research-owner-issued current face which can cause theorem selection. Clause/current
/// morphology and removal-minimal testimony remain distinct from receiver lineage strings.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct LeanDiagnosisCurrentFace {
    target_episode: String,
    question: String,
    clause_identities: LocalSequence<String>,
    source_witnesses: LocalSet<String>,
    passage_witnesses: LocalSet<String>,
    required_entity_regions: LocalSequence<LocalSet<String>>,
    returned_entity_regions: LocalSet<LocalSet<String>>,
    minimal_closed_witness_family: LocalSet<String>,
    target_lineage: LocalSet<String>,
}

impl LeanDiagnosisCurrentFace {
    pub fn target_episode(&self) -> &str {
        self.target_episode.as_str()
    }

    pub const fn target_lineage(&self) -> &LocalSet<String> {
        &self.target_lineage
    }

    pub const fn passage_witnesses(&self) -> &LocalSet<String> {
        &self.passage_witnesses
    }

    fn conducts(&self, requirement: LeanDiagnosisRequirement) -> bool {
        match requirement {
            LeanDiagnosisRequirement::ClosedRemovalMinimalCurrent => {
                !self.target_episode.trim().is_empty()
                    && !self.question.trim().is_empty()
                    && !self.clause_identities.is_empty()
                    && !self.passage_witnesses.is_empty()
                    && self.passage_witnesses == self.minimal_closed_witness_family
                    && !self.required_entity_regions.is_empty()
                    && self
                        .required_entity_regions
                        .iter()
                        .all(|required| self.returned_entity_regions.contains(required))
                    && self
                        .returned_entity_regions
                        .iter()
                        .all(|returned| self.required_entity_regions.contains(returned))
                    && !self.target_lineage.is_empty()
            }
        }
    }

    /// **Made `pub` 2026-08-14**, for the same reason as
    /// `select_and_open_kernel_deed`: a diagnosis current is a required part of
    /// a target request, so a deed could not be opened from outside the crate
    /// without it.
    pub fn from_closed_current(
        target_episode: String,
        question: String,
        clause_identities: LocalSequence<String>,
        source_witnesses: LocalSet<String>,
        passage_witnesses: LocalSet<String>,
        required_entity_regions: LocalSequence<LocalSet<String>>,
        returned_entity_regions: LocalSet<LocalSet<String>>,
        minimal_closed_witness_family: LocalSet<String>,
        target_lineage: LocalSet<String>,
    ) -> Option<Self> {
        let face = Self {
            target_episode,
            question,
            clause_identities,
            source_witnesses,
            passage_witnesses,
            required_entity_regions,
            returned_entity_regions,
            minimal_closed_witness_family,
            target_lineage,
        };
        face.conducts(LeanDiagnosisRequirement::ClosedRemovalMinimalCurrent)
            .then_some(face)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct LeanTheoremTargetRequest {
    pub identity: String,
    pub target_episode: String,
    /// Exact theorem identities declared by the application theorem specification. Selection can
    /// close only when the received faces equal this family; omission cannot masquerade as a
    /// uniquely viable population.
    pub declared_theorem_faces: LocalSet<String>,
    pub alternatives: LocalSequence<LeanTheoremTargetFace>,
    pub diagnosis: LeanDiagnosisCurrentFace,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct LeanTheoremTargetFace {
    pub problem: LeanProofProblem,
    pub diagnosis_requirement: LeanDiagnosisRequirement,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct LeanTargetAlternativeReceipt {
    pub theorem: String,
    pub face_received: bool,
    pub diagnosis_reached: bool,
    pub already_returned: bool,
    pub reached_declarations: usize,
    pub candidate_population: usize,
    pub obstruction: Option<String>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct LeanKernelDeedFace {
    pub deed: String,
    pub theorem: String,
    pub target_episode: String,
    pub diagnosis: LeanDiagnosisCurrentFace,
    pub reached_declarations: LeanDeclarationNames,
    pub candidate_ordinals: LocalSequence<u64>,
    pub alternatives: LocalSequence<LeanTargetAlternativeReceipt>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct OpenTargetSelection {
    pub request: String,
    pub target_episode: String,
    pub declared_theorem_faces: LocalSet<String>,
    pub received_theorem_faces: LocalSet<String>,
    pub alternatives: LocalSequence<LeanTargetAlternativeReceipt>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "conduct", rename_all = "kebab-case")]
#[serde(deny_unknown_fields)]
pub enum LeanTargetSelectionReceipt {
    Selected(LeanKernelDeedFace),
    Open(OpenTargetSelection),
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct LeanTargetSelectionStanding {
    generation: u64,
    request: LeanTheoremTargetRequest,
    receipt: LeanTargetSelectionReceipt,
}

struct LeanViableTarget {
    problem: LeanProofProblem,
    kernel_problem: LeanProofProblem,
    reached_declarations: LeanDeclarationNames,
    candidates: LocalSequence<LeanProofCandidate>,
    diagnosis: LeanDiagnosisCurrentFace,
}

/// Exact conduct of the target-selection owner. A second caused face changes the state to an
/// open noncommuting family; uniqueness is not inferred from a population scalar.
enum LeanTargetSelectionConduct {
    NoCausedFace,
    OneCausedFace(LeanViableTarget),
    NoncommutingFaces,
}

impl LeanTargetSelectionConduct {
    fn receive(&mut self, target: LeanViableTarget) {
        *self = match std::mem::replace(self, Self::NoncommutingFaces) {
            Self::NoCausedFace => Self::OneCausedFace(target),
            Self::OneCausedFace(_) | Self::NoncommutingFaces => Self::NoncommutingFaces,
        };
    }

    fn close(self, complete_face_family: bool) -> Option<LeanViableTarget> {
        if !complete_face_family {
            return None;
        }
        match self {
            Self::OneCausedFace(target) => Some(target),
            Self::NoCausedFace | Self::NoncommutingFaces => None,
        }
    }
}

/// One Lean-owned immutable candidate frontier. External worlds may grade its members, but only
/// this owner can validate the complete returned population and cultivate the successor.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct LeanKernelDeed {
    identity: String,
    target_request: String,
    target_episode: String,
    diagnosis: LeanDiagnosisCurrentFace,
    problem: LeanProofProblem,
    kernel_problem: LeanProofProblem,
    reached_declarations: LeanDeclarationNames,
    candidates: LocalSequence<LeanProofCandidate>,
}

impl LeanKernelDeed {
    pub fn identity(&self) -> &str {
        self.identity.as_str()
    }

    pub const fn problem(&self) -> &LeanProofProblem {
        &self.kernel_problem
    }

    pub fn candidates(&self) -> &[LeanProofCandidate] {
        &self.candidates
    }

    pub fn target_episode(&self) -> &str {
        self.target_episode.as_str()
    }

    pub const fn diagnosis(&self) -> &LeanDiagnosisCurrentFace {
        &self.diagnosis
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct LeanKernelDeedCompletion {
    deed: String,
    target_episode: String,
    diagnosis: LeanDiagnosisCurrentFace,
    returned: LeanReturnedTheoremFiber,
    cultivation: LeanKernelCultivationReceipt,
    kernel_admitted_sources: LocalSequence<LeanGeneratedTheoremSourceFace>,
}

impl LeanKernelDeedCompletion {
    pub fn deed(&self) -> &str {
        self.deed.as_str()
    }

    pub fn target_episode(&self) -> &str {
        self.target_episode.as_str()
    }

    pub const fn diagnosis(&self) -> &LeanDiagnosisCurrentFace {
        &self.diagnosis
    }

    pub const fn returned(&self) -> &LeanReturnedTheoremFiber {
        &self.returned
    }

    pub const fn cultivation(&self) -> &LeanKernelCultivationReceipt {
        &self.cultivation
    }

    pub const fn kernel_admitted_sources(&self) -> &LocalSequence<LeanGeneratedTheoremSourceFace> {
        &self.kernel_admitted_sources
    }

    /// Revalidate the complete owner-issued face before it crosses another body's mouth. The
    /// typed declaration selection is the admission cause; population scalars are checked only
    /// as receipts of the already-formed plural fiber.
    pub fn validates_formal_return_face(&self) -> bool {
        let fiber = &self.returned;
        let cultivation = &self.cultivation;
        let declaration_conduct_matches = match &cultivation.declaration_conduct {
            LeanDeclarationConduct::NoKernelAdmittedProof => {
                fiber.kernel_admitted.is_empty() && !fiber.declaration_admitted
            }
            LeanDeclarationConduct::KernelAdmittedFamily { proofs } => {
                fiber.declaration_admitted
                    && !fiber.kernel_admitted.is_empty()
                    && syntax::proof_family_matches_paths(proofs, &fiber.kernel_admitted)
            }
        };
        let admitted_sources_match = fiber.kernel_admitted.iter().all(|path| {
            self.kernel_admitted_sources.iter().any(|source| {
                source.theorem == fiber.theorem
                    && source.candidate_ordinal == path.candidate_ordinal
                    && source.source_sha256 == path.source_sha256
                    && source.proof_sha256 == path.proof_sha256
                    && syntax::sha256(source.source.as_bytes()) == source.source_sha256
            })
        }) && self.kernel_admitted_sources.iter().all(|source| {
            fiber.kernel_admitted.iter().any(|path| {
                source.theorem == fiber.theorem
                    && source.candidate_ordinal == path.candidate_ordinal
                    && source.source_sha256 == path.source_sha256
                    && source.proof_sha256 == path.proof_sha256
            })
        });
        declaration_conduct_matches
            && admitted_sources_match
            && !self.deed.trim().is_empty()
            && !self.target_episode.trim().is_empty()
            && self
                .diagnosis
                .conducts(LeanDiagnosisRequirement::ClosedRemovalMinimalCurrent)
            && !fiber.theorem.trim().is_empty()
            && !fiber.theorem_face_sha256.trim().is_empty()
            && !fiber.generated_source_identity.trim().is_empty()
            && fiber.generation > 0
            && (!fiber.kernel_admitted.is_empty() || !fiber.obstructed.is_empty())
            && cultivation.theorem == fiber.theorem
            && cultivation.generated_source_identity == fiber.generated_source_identity
            && cultivation.generation_before.checked_add(1) == Some(cultivation.generation_after)
            && cultivation.generation_after == fiber.generation
            && cultivation
                .kernel_admitted_path_population
                .checked_add(cultivation.obstructed_path_population)
                == Some(cultivation.crossed_candidate_population)
            && cultivation
                .crossed_candidate_population
                .checked_add(cultivation.unmaterialized_path_population)
                == Some(cultivation.complete_candidate_population)
            && cultivation.kernel_admitted_path_population
                == u64::try_from(fiber.kernel_admitted.len())
                    .ok()
                    .unwrap_or(u64::MAX)
            && cultivation.obstructed_path_population
                == u64::try_from(fiber.obstructed.len())
                    .ok()
                    .unwrap_or(u64::MAX)
            && cultivation.declaration_admitted == fiber.declaration_admitted
            && cultivation
                .declaration_organs_before
                .checked_add(u64::from(fiber.declaration_admitted))
                == Some(cultivation.declaration_organs_after)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "kebab-case")]
#[serde(deny_unknown_fields)]
pub enum LeanProofMotion {
    Close {
        tactic: Arc<str>,
    },
    Direct {
        declaration: Arc<str>,
    },
    Rewrite {
        declaration: Arc<str>,
    },
    IntroduceFact {
        declaration: Arc<str>,
    },
    /// Apply one reached declaration recurrently through a bounded serial strand before closing
    /// the remaining local face. Every unfolded application is checked by the kernel.
    RecurApply {
        declaration: Arc<str>,
        depth: u8,
    },
    Contrapose {
        hypothesis: Arc<str>,
        declaration: Arc<str>,
    },
    Project {
        declaration: Arc<str>,
        projection: u8,
    },
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct LeanProofCandidate {
    pub ordinal: u64,
    pub proof: String,
    pub motions: Vec<LeanProofMotion>,
    pub declaration_lineage: LocalSet<Arc<str>>,
}

pub type LeanDeclarationNames = LocalSet<String>;

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct LeanProofRun {
    problem: String,
    kernel_problem: LeanProofProblem,
    reached_declarations: LeanDeclarationNames,
    candidates: LocalSequence<LeanProofCandidate>,
    returns: LeanKernelReturnFamily,
    rounds: LocalSequence<LeanProofRoundReceipt>,
}

impl LeanProofRun {
    pub fn problem(&self) -> &str {
        self.problem.as_str()
    }

    pub const fn reached_declarations(&self) -> &LeanDeclarationNames {
        &self.reached_declarations
    }

    pub fn candidates(&self) -> &[LeanProofCandidate] {
        &self.candidates
    }

    pub const fn returns(&self) -> &LeanKernelReturnFamily {
        &self.returns
    }

    pub fn kernel_admitted(&self) -> impl Iterator<Item = &LeanKernelReturn> {
        self.returns.kernel_admitted()
    }

    pub fn rounds(&self) -> &[LeanProofRoundReceipt] {
        &self.rounds
    }

    /// Complete independently compilable sources exactly as they crossed the kernel environment.
    pub fn kernel_admitted_sources(&self) -> Result<LocalSequence<String>, LeanMathematicsError> {
        let mut sources = LocalSequence::new();
        for returned in self.returns.kernel_admitted() {
            sources.push(self.kernel_problem.render(&returned.candidate.proof)?);
        }
        Ok(sources)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct LeanProofRoundReceipt {
    pub ordinal: u64,
    pub cause: String,
    pub candidate_ordinals: Vec<u64>,
    pub kernel_admitted: u64,
    pub obstructed: u64,
}

/// One kernel-crossed proof path retained without copying its generated source surface.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct LeanReturnedProofPath {
    pub candidate_ordinal: u64,
    pub proof_sha256: String,
    pub source_sha256: String,
    pub diagnostic_sha256: String,
    pub motions: LocalSequence<LeanProofMotion>,
    pub declaration_lineage: LocalSequence<Arc<str>>,
}

/// The exact plural proof fiber caused by one theorem request and its kernel returns.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct LeanReturnedTheoremFiber {
    pub theorem: String,
    pub theorem_face_sha256: String,
    pub generated_source_identity: String,
    pub generation: u64,
    pub declaration_admitted: bool,
    pub kernel_admitted: LocalSequence<LeanReturnedProofPath>,
    pub obstructed: LocalSequence<LeanReturnedProofPath>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct LeanReturnedDeclarationSource {
    pub generated_source_identity: String,
    pub theorem: String,
    /// Every proof which founded this theorem organ, in the deed's exact candidate chronology.
    pub proof_family: LocalSequence<LeanDeclarationProofFace>,
    /// One family-composite declaration, without imports or enclosing namespace faces. A later
    /// problem mounts it inside its own declared prefix. Its proof body contains every admitted
    /// path and therefore cannot silently substitute a ranked application-owned representative.
    pub declaration: String,
}

/// One complete self-emanated source exactly as it crossed and was admitted by Lean's kernel.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct LeanGeneratedTheoremSourceFace {
    pub identity: String,
    pub theorem: String,
    pub candidate_ordinal: u64,
    pub source: String,
    pub source_sha256: String,
    pub proof_sha256: String,
}

/// Observer receipt for one returned proof event changing the continuing mathematical body.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct LeanKernelCultivationReceipt {
    pub theorem: String,
    pub generated_source_identity: String,
    pub generation_before: u64,
    pub generation_after: u64,
    pub declaration_organs_before: u64,
    pub declaration_organs_after: u64,
    pub complete_candidate_population: u64,
    pub crossed_candidate_population: u64,
    pub kernel_admitted_path_population: u64,
    pub obstructed_path_population: u64,
    pub unmaterialized_path_population: u64,
    pub declaration_admitted: bool,
    pub declaration_conduct: LeanDeclarationConduct,
    pub retained_source_surfaces: u64,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct LeanDeclarationProofFace {
    pub proof_sha256: String,
    pub source_sha256: String,
    pub motions: LocalSequence<LeanProofMotion>,
    pub declaration_lineage: LocalSequence<Arc<str>>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "conduct", rename_all = "kebab-case")]
#[serde(deny_unknown_fields)]
pub enum LeanDeclarationConduct {
    NoKernelAdmittedProof,
    KernelAdmittedFamily {
        proofs: LocalSequence<LeanDeclarationProofFace>,
    },
}

#[derive(Clone, Debug)]
pub struct LeanKernelWorld {
    project_root: PathBuf,
    scratch_root: PathBuf,
    worker_aperture: usize,
}

impl LeanKernelWorld {
    pub fn new(
        project_root: impl Into<PathBuf>,
        scratch_root: impl Into<PathBuf>,
        worker_aperture: usize,
    ) -> Result<Self, LeanMathematicsError> {
        if worker_aperture == 0 {
            return Err(LeanMathematicsError::CarrierExtent);
        }
        Ok(Self {
            project_root: project_root.into(),
            scratch_root: scratch_root.into(),
            worker_aperture,
        })
    }

    fn grade(
        &self,
        problem: &LeanProofProblem,
        candidate: &LeanProofCandidate,
    ) -> Result<LeanKernelReturn, LeanMathematicsError> {
        fs::create_dir_all(&self.scratch_root).map_err(syntax::io_error)?;
        let source = problem.render(&candidate.proof)?;
        let source_sha256 = syntax::sha256(source.as_bytes());
        let path = self.scratch_root.join(format!(
            "{}-{:05}.lean",
            syntax::safe_identity(&problem.identity),
            candidate.ordinal
        ));
        fs::write(&path, source.as_bytes()).map_err(syntax::io_error)?;
        let relative = path
            .strip_prefix(&self.project_root)
            .unwrap_or(path.as_path());
        let began = Instant::now();
        let output = Command::new("lake")
            .arg("env")
            .arg("lean")
            .arg(relative)
            .current_dir(&self.project_root)
            .output()
            .map_err(syntax::io_error)?;
        let observed_millis = u64::try_from(began.elapsed().as_millis())
            .map_err(|_| LeanMathematicsError::CarrierExtent)?;
        let mut diagnostic = String::from_utf8_lossy(&output.stdout).into_owned();
        diagnostic.push_str(&String::from_utf8_lossy(&output.stderr));
        let outcome = if output.status.success()
            && !candidate.proof.contains("sorry")
            && !candidate.proof.contains("admit")
        {
            LeanKernelOutcome::KernelAdmitted
        } else {
            LeanKernelOutcome::Obstructed
        };
        Ok(LeanKernelReturn {
            candidate: candidate.clone(),
            outcome,
            source_sha256,
            diagnostic_sha256: syntax::sha256(diagnostic.as_bytes()),
            diagnostic,
            observed_millis,
        })
    }

    pub fn grade_all(
        &self,
        problem: &LeanProofProblem,
        candidates: &[LeanProofCandidate],
    ) -> Result<LeanKernelReturnFamily, LeanMathematicsError> {
        if candidates.is_empty() {
            return Err(LeanMathematicsError::NoProofCandidates);
        }
        let threads = self.worker_aperture.min(candidates.len()).max(1);
        let mut returned = vec![None; candidates.len()];
        let base = candidates.len() / threads;
        let remainder = candidates.len() % threads;
        std::thread::scope(|scope| {
            let mut output_tail = returned.as_mut_slice();
            let mut input_start = 0usize;
            for worker in 0..threads {
                let extent = base + usize::from(worker < remainder);
                let (output, tail) = output_tail.split_at_mut(extent);
                let input = &candidates[input_start..input_start + extent];
                scope.spawn(move || {
                    for (slot, candidate) in output.iter_mut().zip(input) {
                        *slot = Some(self.grade(problem, candidate));
                    }
                });
                output_tail = tail;
                input_start += extent;
            }
        });
        let members = returned
            .into_iter()
            .map(|returned| {
                returned
                    .ok_or(LeanMathematicsError::CarrierExtent)?
                    .map_err(|error| error)
            })
            .collect::<Result<LocalSequence<_>, _>>()?;
        LeanKernelReturnFamily::from_members(members)
    }
}

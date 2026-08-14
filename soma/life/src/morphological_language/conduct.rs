//! Exact deposited conduct for morphological continuation transports.
//!
//! A visible continuation does not conduct because it is common or co-present. One exact
//! query-independent suffix transport conducts only when its own target occurrences project to
//! at least two distinct exterior sources. Context incidence, match horizon, and recurrence
//! multiplicity remain testimony; none of them can manufacture the contact or enter its address.

use body::num::COG_WORDS;
use holonic_structure::{LocalRelations, LocalSequence, LocalSet};
use soma_membrane::ReceiverFiberIdentity;

use crate::suffix_ecology::{
    ExactLabeledSuffixBranch, ExactLabeledSuffixMaterialEdge, SuffixBranchSupport,
};

use super::{
    CudaMorphologicalConductExecutor, MorphologicalConductCudaReceipt, MorphologicalGenerationSpec,
    MorphologicalLanguageCurrentGeneration, MorphologicalLanguageEcology,
    MorphologicalLanguageError,
};

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum MorphologicalConductChart {
    ClauseLexical,
    PassageLexical,
}

/// Stable address of one material suffix transport. Query horizon and recurrence are deliberately
/// absent: changing either observation must not mint another deposited pathway.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct MorphologicalConductEdgeAddress {
    chart: MorphologicalConductChart,
    context_state: u32,
    germ_identity: ReceiverFiberIdentity,
    germ_phase: [u32; COG_WORDS],
    target_state: u32,
}

impl MorphologicalConductEdgeAddress {
    pub fn new(
        chart: MorphologicalConductChart,
        context_state: u32,
        germ_identity: ReceiverFiberIdentity,
        germ_phase: [u32; COG_WORDS],
        target_state: u32,
    ) -> Self {
        Self {
            chart,
            context_state,
            germ_identity,
            germ_phase,
            target_state,
        }
    }

    pub fn from_material_edge(
        chart: MorphologicalConductChart,
        edge: &ExactLabeledSuffixMaterialEdge,
    ) -> Self {
        Self::new(
            chart,
            edge.context_state(),
            edge.germ_identity().clone(),
            edge.germ_phase(),
            edge.target_state(),
        )
    }

    pub fn from_branch_support(
        chart: MorphologicalConductChart,
        branch: &ExactLabeledSuffixBranch,
        support: &SuffixBranchSupport,
    ) -> Result<Self, MorphologicalConductRefusal> {
        if branch.sources_for_support(support).is_none()
            || branch.context_sources_for_support(support).is_none()
        {
            return Err(MorphologicalConductRefusal::SupportNotOnBranch);
        }
        Ok(Self::new(
            chart,
            support.state(),
            branch.branch().germ().identity().clone(),
            branch.branch().germ().phase().words(),
            support.target_state(),
        ))
    }

    pub const fn chart(&self) -> MorphologicalConductChart {
        self.chart
    }

    pub const fn context_state(&self) -> u32 {
        self.context_state
    }

    pub const fn germ_identity(&self) -> &ReceiverFiberIdentity {
        &self.germ_identity
    }

    pub const fn germ_phase(&self) -> [u32; COG_WORDS] {
        self.germ_phase
    }

    pub const fn target_state(&self) -> u32 {
        self.target_state
    }

    /// **The exact word key the card matches on, at a width the front declares.**
    ///
    /// **Germ identities are NOT of uniform width and assuming they were is a defect this driver
    /// found by running.** `token_germs` founds an identity from the token's own surface, so a
    /// front mixes identities of several word counts, and the first version of this encoding
    /// refused every real front with `NonuniformKeyWidth`. The fix is to declare one identity width
    /// per launch — `identity_words`, read off the front as the maximum over the deposits and the
    /// candidates present — and pad the shorter identities to it.
    ///
    /// **The padding is injective because the word COUNT is written before the words.** Identity
    /// `[5]` and identity `[5, 0]` pad to the same trailing words and are separated by the count
    /// field, so no two addresses share a key. And the count precedes the words, so the order of
    /// two keys does not depend on the declared width: widening a front cannot reorder its sheets.
    ///
    /// **This order is NOT the type's derived `Ord`, and the difference is real.** `Ord` compares
    /// identities as slices — elementwise, a prefix sorting first — so `[5, 9] < [6]`. This key
    /// compares the count first, so `[6]` precedes `[5, 9]`. The card searches on the key, so the
    /// sheets it receives must be sorted by `card_key_cmp` and not by address; the atlas keeps
    /// address order for its own canonicity, and the two are separately correct.
    pub fn identity_word_extent(&self) -> usize {
        self.germ_identity.words().len()
    }

    pub const fn key_word_extent(identity_words: usize) -> usize {
        5 + identity_words + COG_WORDS + 1
    }

    pub fn key_words(&self, identity_words: usize) -> Option<LocalSequence<u32>> {
        let carried = self.germ_identity.words();
        if carried.len() > identity_words {
            return None;
        }
        let mut key = LocalSequence::with_capacity(Self::key_word_extent(identity_words));
        key.push(match self.chart {
            MorphologicalConductChart::ClauseLexical => 0,
            MorphologicalConductChart::PassageLexical => 1,
        });
        key.push(self.context_state);
        let schema = self.germ_identity.schema();
        key.push((schema >> 32) as u32);
        key.push(schema as u32);
        key.push(carried.len() as u32);
        for word in carried {
            key.push(*word);
        }
        for _ in carried.len()..identity_words {
            key.push(0);
        }
        for word in self.germ_phase {
            key.push(word);
        }
        key.push(self.target_state);
        Some(key)
    }

    /// The total order the card's sheets must be in. Equal to the lexicographic order of
    /// `key_words` at any declared width, and computable without materializing a key.
    pub fn card_key_cmp(&self, other: &Self) -> core::cmp::Ordering {
        self.chart
            .cmp(&other.chart)
            .then_with(|| self.context_state.cmp(&other.context_state))
            .then_with(|| {
                self.germ_identity
                    .schema()
                    .cmp(&other.germ_identity.schema())
            })
            .then_with(|| {
                self.germ_identity
                    .words()
                    .len()
                    .cmp(&other.germ_identity.words().len())
            })
            .then_with(|| self.germ_identity.words().cmp(other.germ_identity.words()))
            .then_with(|| self.germ_phase.cmp(&other.germ_phase))
            .then_with(|| self.target_state.cmp(&other.target_state))
    }
}

/// **Encode one transport key at a declared identity width, refusing rather than truncating.**
///
/// This is the single site where a declared width meets an address, so it is the single site the
/// refusal can come from, and a caller cannot silently drop the high words of an identity that is
/// wider than the width it declared. `MorphologicalConductEdgeAddress::key_words` returns `None`
/// for exactly that case; this names it.
pub fn card_key(
    edge: &MorphologicalConductEdgeAddress,
    identity_words: usize,
) -> Result<LocalSequence<u32>, MorphologicalConductRefusal> {
    edge.key_words(identity_words)
        .ok_or(MorphologicalConductRefusal::NonuniformKeyWidth)
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct MorphologicalConductSourceAddress {
    fiber: ReceiverFiberIdentity,
    identity: String,
    receiver: u64,
}

impl MorphologicalConductSourceAddress {
    pub fn new(
        fiber: ReceiverFiberIdentity,
        identity: impl Into<String>,
        receiver: u64,
    ) -> Result<Self, MorphologicalConductRefusal> {
        let identity = identity.into();
        if identity.is_empty() {
            return Err(MorphologicalConductRefusal::EmptySourceIdentity);
        }
        Ok(Self {
            fiber,
            identity,
            receiver,
        })
    }

    pub const fn fiber(&self) -> &ReceiverFiberIdentity {
        &self.fiber
    }

    pub fn identity(&self) -> &str {
        &self.identity
    }

    pub const fn receiver(&self) -> u64 {
        self.receiver
    }
}

/// Wide validation row for one material transport. The target relation decides conduct. The
/// context relation is retained only so a sealed atlas can prove which receiver seam was present.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MorphologicalConductSupportRow {
    edge: MorphologicalConductEdgeAddress,
    recurrence_multiplicity: u64,
    target_sources: LocalRelations<ReceiverFiberIdentity, MorphologicalConductSourceAddress>,
    context_sources: LocalRelations<ReceiverFiberIdentity, MorphologicalConductSourceAddress>,
}

impl MorphologicalConductSupportRow {
    pub fn from_material_edge<F>(
        chart: MorphologicalConductChart,
        edge: &ExactLabeledSuffixMaterialEdge,
        mut exterior_source_of: F,
    ) -> Result<Self, MorphologicalConductRefusal>
    where
        F: FnMut(
            &ReceiverFiberIdentity,
        ) -> Result<MorphologicalConductSourceAddress, MorphologicalConductRefusal>,
    {
        let mut target_sources = LocalRelations::new();
        for occurrence in edge.sources() {
            let source = exterior_source_of(occurrence)?;
            if target_sources
                .try_insert(occurrence.clone(), source)
                .map_err(|_| MorphologicalConductRefusal::CarrierExtent)?
                .is_some()
            {
                return Err(MorphologicalConductRefusal::DuplicateOccurrence);
            }
        }
        let mut context_sources = LocalRelations::new();
        for occurrence in edge.context_sources() {
            let source = exterior_source_of(occurrence)?;
            if context_sources
                .try_insert(occurrence.clone(), source)
                .map_err(|_| MorphologicalConductRefusal::CarrierExtent)?
                .is_some()
            {
                return Err(MorphologicalConductRefusal::DuplicateOccurrence);
            }
        }
        Self::new(
            MorphologicalConductEdgeAddress::from_material_edge(chart, edge),
            edge.recurrence_multiplicity(),
            target_sources,
            context_sources,
        )
    }

    pub fn new(
        edge: MorphologicalConductEdgeAddress,
        recurrence_multiplicity: u64,
        target_sources: LocalRelations<ReceiverFiberIdentity, MorphologicalConductSourceAddress>,
        context_sources: LocalRelations<ReceiverFiberIdentity, MorphologicalConductSourceAddress>,
    ) -> Result<Self, MorphologicalConductRefusal> {
        if recurrence_multiplicity == 0 {
            return Err(MorphologicalConductRefusal::ZeroRecurrence);
        }
        if target_sources.is_empty() {
            return Err(MorphologicalConductRefusal::EmptyTargetIncidence);
        }
        Ok(Self {
            edge,
            recurrence_multiplicity,
            target_sources,
            context_sources,
        })
    }

    pub const fn edge(&self) -> &MorphologicalConductEdgeAddress {
        &self.edge
    }

    pub const fn recurrence_multiplicity(&self) -> u64 {
        self.recurrence_multiplicity
    }

    pub const fn target_sources(
        &self,
    ) -> &LocalRelations<ReceiverFiberIdentity, MorphologicalConductSourceAddress> {
        &self.target_sources
    }

    pub const fn context_sources(
        &self,
    ) -> &LocalRelations<ReceiverFiberIdentity, MorphologicalConductSourceAddress> {
        &self.context_sources
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DepositedMorphologicalConduct {
    edge: MorphologicalConductEdgeAddress,
    occurrences: LocalSet<ReceiverFiberIdentity>,
    exterior_sources: LocalSet<MorphologicalConductSourceAddress>,
}

impl DepositedMorphologicalConduct {
    pub const fn edge(&self) -> &MorphologicalConductEdgeAddress {
        &self.edge
    }

    pub const fn occurrences(&self) -> &LocalSet<ReceiverFiberIdentity> {
        &self.occurrences
    }

    pub const fn exterior_sources(&self) -> &LocalSet<MorphologicalConductSourceAddress> {
        &self.exterior_sources
    }
}

/// **The plurality a caller declares, and the reason it declares it.**
///
/// The condition that separates a deposit from a coincidence is *how many distinct exterior
/// sources one exact material transport returned through*. That number is **not** this module's to
/// author — `canon/THE_AUTHORED_LEVEL.md` and `canon/TABLET_THE_RESONANCE.md` §11 forbid a
/// threshold the material did not supply or a caller did not declare with its reason — and it
/// stood here as a bare `< 2` in `into_state` that no caller could vary. Carrying the reason with
/// the number is what makes the declaration checkable: a receipt can print who declared it and
/// why, and a driver can vary it and exhibit the orbit.
///
/// Zero is refused: *at least zero distinct sources* is not a condition, and
/// `MorphologicalConductSupportRow::new` already refuses an empty target incidence. One is lawful
/// and is the useful negative control — it declares that every material transport conducts, which
/// is the arm a driver runs to show that the plurality is doing the separating.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MorphologicalConductPlurality {
    minimum_distinct_sources: usize,
    declared_by: String,
}

impl MorphologicalConductPlurality {
    pub fn declared(
        minimum_distinct_sources: usize,
        declared_by: impl Into<String>,
    ) -> Result<Self, MorphologicalConductRefusal> {
        let declared_by = declared_by.into();
        if minimum_distinct_sources == 0 {
            return Err(MorphologicalConductRefusal::VacuousPlurality);
        }
        if declared_by.is_empty() {
            return Err(MorphologicalConductRefusal::UndeclaredPlurality);
        }
        Ok(Self {
            minimum_distinct_sources,
            declared_by,
        })
    }

    /// **The body's own conducting condition: recurrence across two distinct wholes.**
    ///
    /// `relational_language::RelationalChannelConduct` states it — *"A separated coincident face
    /// conducts only after the same complete junction phase has returned through two distinct
    /// source pairs"* — and `soma/life/src/agentic_language`'s `CODEC_MINIMUM_RECURRENCE = 2` says
    /// the same thing on the codec side: a route is retained but inactive until it recurs across
    /// **distinct** occurrences. This constructor is a citation, not an authorship.
    pub fn recurrence_across_two_distinct_wholes() -> Self {
        Self {
            minimum_distinct_sources: 2,
            declared_by: "relational_language::RelationalChannelConduct / \
                          agentic_language::CODEC_MINIMUM_RECURRENCE: a contact conducts only \
                          after the same transport returned through two distinct wholes"
                .to_owned(),
        }
    }

    pub const fn minimum_distinct_sources(&self) -> usize {
        self.minimum_distinct_sources
    }

    pub fn declared_by(&self) -> &str {
        &self.declared_by
    }
}

/// The exact wide atlas before its conducting subpopulation is condensed. Rows must already be in
/// canonical edge order; duplicate or order-dependent testimony is refused rather than hidden.
#[derive(Debug, PartialEq, Eq)]
pub struct MorphologicalConductAtlas {
    rows: LocalSequence<MorphologicalConductSupportRow>,
}

impl MorphologicalConductAtlas {
    pub fn found(
        rows: LocalSequence<MorphologicalConductSupportRow>,
    ) -> Result<Self, MorphologicalConductRefusal> {
        if rows.windows(2).any(|pair| pair[0].edge() >= pair[1].edge()) {
            return Err(MorphologicalConductRefusal::NoncanonicalAtlas);
        }
        Ok(Self { rows })
    }

    pub const fn rows(&self) -> &LocalSequence<MorphologicalConductSupportRow> {
        &self.rows
    }

    /// Condense the wide atlas into the deposits that satisfy the **caller's declared** plurality.
    ///
    /// This consumes the atlas, so a receiver that wants both the complete population and the
    /// condensed one founds the atlas twice — `conduct_atlas` is a pure function of the conditioned
    /// material and returns the same rows every time. The plurality is carried on the returned
    /// morphology so a receipt can state which condition separated the deposits from the
    /// coincidences rather than leaving the reader to guess at a bare number.
    pub fn into_state(
        self,
        plurality: &MorphologicalConductPlurality,
    ) -> Result<MorphologicalConductState, MorphologicalConductRefusal> {
        let mut deposits = LocalRelations::new();
        for row in self.rows {
            let exterior_sources = row
                .target_sources
                .iter()
                .map(|(_, source)| source.clone())
                .collect::<LocalSet<_>>();
            if exterior_sources.len() < plurality.minimum_distinct_sources() {
                continue;
            }
            let deposit = DepositedMorphologicalConduct {
                edge: row.edge.clone(),
                occurrences: row
                    .target_sources
                    .iter()
                    .map(|(occurrence, _)| occurrence.clone())
                    .collect(),
                exterior_sources,
            };
            if deposits
                .try_insert(row.edge, deposit)
                .map_err(|_| MorphologicalConductRefusal::CarrierExtent)?
                .is_some()
            {
                return Err(MorphologicalConductRefusal::DuplicateDeposit);
            }
        }
        if deposits.is_empty() {
            Ok(MorphologicalConductState::Unconditioned(
                UnconditionedMorphologicalConduct,
            ))
        } else {
            Ok(MorphologicalConductState::Conducting(
                MorphologicalConductMorphology {
                    deposits,
                    plurality: plurality.clone(),
                },
            ))
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
pub struct UnconditionedMorphologicalConduct;

#[derive(Debug, PartialEq, Eq)]
pub enum MorphologicalConductState {
    Unconditioned(UnconditionedMorphologicalConduct),
    Conducting(MorphologicalConductMorphology),
}

/// One candidate transition as presented to and returned from the resident attachment deed.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MorphologicalConductTransitionDisposition {
    pub chronology: u64,
    pub candidate: u64,
    pub surface: String,
    pub witness_population: usize,
    pub candidate_edges: LocalSequence<MorphologicalConductEdgeAddress>,
    pub attached_deposits: LocalSequence<MorphologicalConductEdgeAddress>,
}

/// **One branch that reached the attachment deed and found nothing conducting.**
///
/// `canon/TABLET_THE_RESONANCE.md` §11: *"Where nothing conducts, the return is the obstruction
/// with its address — not silence and not a fabrication."* The owner silently `continue`d such a
/// branch, which dropped the whole current: it entered neither the pending front nor the rested
/// population, so a receiver could not tell a branch that never existed from one the deposits
/// refused. The branch now comes to rest as `MorphologicalResponseRest::Obstructed` and is returned
/// among the outputs, and this row is its address.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MorphologicalConductObstruction {
    /// The chronology the branch had reached when nothing conducted.
    pub chronology: u64,
    /// The clause-lexical receiver state the branch sat at — the generation site.
    pub site: u32,
    /// How many exact witness paths came to rest with it.
    pub witness_population: usize,
    /// The candidate ordinals this branch withheld. Each resolves in `dispositions` to its surface
    /// and its complete candidate-edge population, so what was refused is inspectable by name.
    pub withheld_candidates: LocalSequence<u64>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MorphologicalConductGenerationReceipt {
    pub schema: String,
    pub evaluated_transitions: usize,
    pub attached_transitions: usize,
    pub withheld_transitions: usize,
    /// The plurality the caller declared, and the reason it gave. A receipt that cannot state which
    /// condition separated its deposits from its coincidences has not stated its own aperture.
    pub declared_minimum_distinct_sources: usize,
    pub plurality_declared_by: String,
    pub dispositions: LocalSequence<MorphologicalConductTransitionDisposition>,
    pub obstructions: LocalSequence<MorphologicalConductObstruction>,
}

pub struct MorphologicalConductedGeneration {
    pub generation: MorphologicalLanguageCurrentGeneration,
    pub semantic: MorphologicalConductGenerationReceipt,
    pub apparatus: LocalSequence<MorphologicalConductCudaReceipt>,
}

/// One continuing morphology owner. The base ecology is moved into this wrapper exactly once;
/// sparse generation branches continue to borrow it and own only their local current differences.
#[derive(Debug)]
pub struct ConductingMorphologicalLanguageEcology {
    ecology: MorphologicalLanguageEcology,
    conduct: MorphologicalConductMorphology,
}

#[derive(Debug)]
pub enum MorphologicalLanguageConductState {
    Unconditioned(MorphologicalLanguageEcology),
    Conducting(ConductingMorphologicalLanguageEcology),
}

impl MorphologicalLanguageEcology {
    pub fn receive_conduct(
        self,
        conduct: MorphologicalConductState,
    ) -> MorphologicalLanguageConductState {
        match conduct {
            MorphologicalConductState::Unconditioned(_) => {
                MorphologicalLanguageConductState::Unconditioned(self)
            }
            MorphologicalConductState::Conducting(conduct) => {
                MorphologicalLanguageConductState::Conducting(
                    ConductingMorphologicalLanguageEcology {
                        ecology: self,
                        conduct,
                    },
                )
            }
        }
    }
}

impl ConductingMorphologicalLanguageEcology {
    pub const fn ecology(&self) -> &MorphologicalLanguageEcology {
        &self.ecology
    }

    pub const fn conduct(&self) -> &MorphologicalConductMorphology {
        &self.conduct
    }

    pub fn generate_currents_over(
        &self,
        prompt: &str,
        spec: MorphologicalGenerationSpec,
        cover: &holonic_engine::hardware_cover::HardwareCover,
        executor: &mut CudaMorphologicalConductExecutor,
    ) -> Result<MorphologicalConductedGeneration, MorphologicalLanguageError> {
        self.ecology
            .generate_currents_over_conducted(prompt, spec, cover, &self.conduct, executor)
    }

    pub fn ablate_target(
        self,
        target: &MorphologicalConductEdgeAddress,
    ) -> Result<MorphologicalLanguageTargetConductAblation, MorphologicalConductRefusal> {
        let ConductingMorphologicalLanguageEcology { ecology, conduct } = self;
        let ablated = conduct.ablate_target(target)?;
        let state = match ablated.state {
            MorphologicalConductState::Unconditioned(_) => {
                MorphologicalLanguageConductState::Unconditioned(ecology)
            }
            MorphologicalConductState::Conducting(conduct) => {
                MorphologicalLanguageConductState::Conducting(Self { ecology, conduct })
            }
        };
        Ok(MorphologicalLanguageTargetConductAblation {
            state,
            removed: ablated.removed,
        })
    }

    pub fn ablate_all(self) -> MorphologicalLanguageAllConductAblation {
        let ConductingMorphologicalLanguageEcology { ecology, conduct } = self;
        let ablated = conduct.ablate_all();
        MorphologicalLanguageAllConductAblation {
            ecology,
            removed: ablated.removed,
        }
    }
}

pub struct MorphologicalLanguageTargetConductAblation {
    pub state: MorphologicalLanguageConductState,
    pub removed: DepositedMorphologicalConduct,
}

pub struct MorphologicalLanguageAllConductAblation {
    pub ecology: MorphologicalLanguageEcology,
    pub removed: LocalSequence<DepositedMorphologicalConduct>,
}

#[derive(Debug, PartialEq, Eq)]
pub struct MorphologicalConductMorphology {
    deposits: LocalRelations<MorphologicalConductEdgeAddress, DepositedMorphologicalConduct>,
    plurality: MorphologicalConductPlurality,
}

impl MorphologicalConductMorphology {
    pub const fn deposit_count(&self) -> usize {
        self.deposits.len()
    }

    pub const fn plurality(&self) -> &MorphologicalConductPlurality {
        &self.plurality
    }

    /// The widest germ identity this morphology carries. A front declares its key width as the
    /// maximum of this and of the candidates present, and pads to it.
    pub fn identity_word_extent(&self) -> usize {
        self.deposits
            .iter()
            .map(|(edge, _)| edge.identity_word_extent())
            .max()
            .unwrap_or(0)
    }

    /// This morphology's deposits in the order the card's sheet must be in, each with the exterior
    /// source lineage it carries. The ordinals the card returns index into exactly this sequence.
    pub fn card_ordered_deposits(&self) -> LocalSequence<&DepositedMorphologicalConduct> {
        let mut ordered = self
            .deposits
            .iter()
            .map(|(_, deposit)| deposit)
            .collect::<LocalSequence<_>>();
        ordered.sort_by(|left, right| left.edge().card_key_cmp(right.edge()));
        ordered
    }

    pub fn deposits(&self) -> impl ExactSizeIterator<Item = &DepositedMorphologicalConduct> {
        self.deposits.iter().map(|(_, deposit)| deposit)
    }

    pub fn deposit(
        &self,
        edge: &MorphologicalConductEdgeAddress,
    ) -> Option<&DepositedMorphologicalConduct> {
        self.deposits.get(edge)
    }

    pub fn deposits_for(
        &self,
        edges: &LocalSet<MorphologicalConductEdgeAddress>,
    ) -> LocalSequence<&DepositedMorphologicalConduct> {
        edges
            .iter()
            .filter_map(|edge| self.deposits.get(edge))
            .collect()
    }

    pub fn ablate_target(
        mut self,
        target: &MorphologicalConductEdgeAddress,
    ) -> Result<MorphologicalConductTargetAblation, MorphologicalConductRefusal> {
        let removed = self
            .deposits
            .remove(target)
            .ok_or(MorphologicalConductRefusal::UnknownDeposit)?;
        let state = if self.deposits.is_empty() {
            MorphologicalConductState::Unconditioned(UnconditionedMorphologicalConduct)
        } else {
            MorphologicalConductState::Conducting(self)
        };
        Ok(MorphologicalConductTargetAblation { state, removed })
    }

    /// **Ablate every deposit, one named target at a time.**
    ///
    /// The audit's finding stands and is not repaired by renaming: consuming the morphology and
    /// returning `Unconditioned` is true *by type-state* and could not have come out otherwise, so
    /// it is no evidence about the material. What it does establish is narrower and worth keeping:
    /// removing all of them by the same targeted path that removes one leaves nothing behind, so a
    /// later complete enumeration is running on an ecology the conducted pass did not mutate. The
    /// non-tautological ablation is `ablate_target`, and it is the one a falsifier must fire.
    pub fn ablate_all(self) -> MorphologicalConductAllAblation {
        MorphologicalConductAllAblation {
            unconditioned: UnconditionedMorphologicalConduct,
            removed: self
                .deposits
                .into_iter()
                .map(|(_, deposit)| deposit)
                .collect(),
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
pub struct MorphologicalConductTargetAblation {
    pub state: MorphologicalConductState,
    pub removed: DepositedMorphologicalConduct,
}

#[derive(Debug, PartialEq, Eq)]
pub struct MorphologicalConductAllAblation {
    pub unconditioned: UnconditionedMorphologicalConduct,
    pub removed: LocalSequence<DepositedMorphologicalConduct>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MorphologicalConductRefusal {
    EmptySourceIdentity,
    UnknownOccurrenceSource,
    DuplicateOccurrence,
    EmptyTargetIncidence,
    ZeroRecurrence,
    SupportNotOnBranch,
    NoncanonicalAtlas,
    DuplicateDeposit,
    UnknownDeposit,
    VacuousPlurality,
    UndeclaredPlurality,
    NonuniformKeyWidth,
    CarrierExtent,
}

impl core::fmt::Display for MorphologicalConductRefusal {
    fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        formatter.write_str(match self {
            Self::EmptySourceIdentity => "morphological conduct source identity is empty",
            Self::UnknownOccurrenceSource => {
                "a morphological occurrence has no authoritative exterior source"
            }
            Self::DuplicateOccurrence => "a morphological occurrence is duplicated",
            Self::EmptyTargetIncidence => "a conduct support has no target occurrence",
            Self::ZeroRecurrence => "a conduct support has zero recurrence testimony",
            Self::SupportNotOnBranch => "suffix support is not carried by the labeled branch",
            Self::NoncanonicalAtlas => "the conduct atlas is duplicated or out of order",
            Self::DuplicateDeposit => "a morphological conduct deposit is duplicated",
            Self::UnknownDeposit => "morphological conduct deposit is absent",
            Self::VacuousPlurality => {
                "a conduct plurality of zero distinct sources is not a condition"
            }
            Self::UndeclaredPlurality => "a conduct plurality was declared with no stated reason",
            Self::NonuniformKeyWidth => {
                "the conduct deposits do not share one exact transport key width"
            }
            Self::CarrierExtent => "morphological conduct carrier extent is invalid",
        })
    }
}

impl std::error::Error for MorphologicalConductRefusal {}

#[cfg(test)]
mod tests {
    use body::num::Cog;
    use soma_abi::active::RelationAtom;

    use crate::{resonance_ecology::ResonanceGerm, suffix_ecology::ExactLabeledSuffixEcology};

    use super::*;

    const GERM_SCHEMA: u64 = 0x504c_414e_335f_474d;
    const SOURCE_SCHEMA: u64 = 0x504c_414e_335f_5352;
    const OCCURRENCE_SCHEMA: u64 = 0x504c_414e_335f_4f43;

    fn fiber(schema: u64, value: u32) -> ReceiverFiberIdentity {
        ReceiverFiberIdentity::new(schema, [value])
    }

    fn germ(value: u32) -> ResonanceGerm {
        ResonanceGerm::new(
            fiber(GERM_SCHEMA, value),
            RelationAtom::new(Cog::lit(i64::from(value) + 1)).unwrap(),
        )
    }

    fn source(value: u32) -> MorphologicalConductSourceAddress {
        MorphologicalConductSourceAddress::new(
            fiber(SOURCE_SCHEMA, value),
            format!("source-{value}"),
            SOURCE_SCHEMA,
        )
        .unwrap()
    }

    fn edge(value: u32, phase: i64) -> MorphologicalConductEdgeAddress {
        MorphologicalConductEdgeAddress::new(
            MorphologicalConductChart::ClauseLexical,
            value,
            fiber(GERM_SCHEMA, 99),
            RelationAtom::new(Cog::lit(phase)).unwrap().words(),
            value + 10,
        )
    }

    fn row(
        edge: MorphologicalConductEdgeAddress,
        target: &[(u32, u32)],
        context: &[(u32, u32)],
    ) -> MorphologicalConductSupportRow {
        let mut target_sources = LocalRelations::new();
        for (occurrence, source_at) in target {
            target_sources.insert(fiber(OCCURRENCE_SCHEMA, *occurrence), source(*source_at));
        }
        let mut context_sources = LocalRelations::new();
        for (occurrence, source_at) in context {
            context_sources.insert(fiber(OCCURRENCE_SCHEMA, *occurrence), source(*source_at));
        }
        MorphologicalConductSupportRow::new(edge, 1, target_sources, context_sources).unwrap()
    }

    fn state(rows: LocalSequence<MorphologicalConductSupportRow>) -> MorphologicalConductState {
        state_under(
            rows,
            &MorphologicalConductPlurality::recurrence_across_two_distinct_wholes(),
        )
    }

    fn state_under(
        rows: LocalSequence<MorphologicalConductSupportRow>,
        plurality: &MorphologicalConductPlurality,
    ) -> MorphologicalConductState {
        MorphologicalConductAtlas::found(rows)
            .unwrap()
            .into_state(plurality)
            .unwrap()
    }

    #[test]
    fn target_contact_not_context_copresence_decides_conduct() {
        let state = state(LocalSequence::from([row(
            edge(1, 7),
            &[(10, 1), (11, 1)],
            &[(20, 1), (21, 2)],
        )]));
        assert!(matches!(state, MorphologicalConductState::Unconditioned(_)));
    }

    #[test]
    fn one_exact_edge_across_two_exterior_sources_deposits() {
        let state = state(LocalSequence::from([row(
            edge(2, 7),
            &[(10, 1), (11, 2)],
            &[(20, 1), (21, 2)],
        )]));
        let MorphologicalConductState::Conducting(morphology) = state else {
            panic!("plural exact target contact must conduct");
        };
        let deposit = morphology.deposits().next().unwrap();
        assert_eq!(deposit.occurrences().len(), 2);
        assert_eq!(deposit.exterior_sources().len(), 2);
    }

    #[test]
    fn complete_germ_phase_and_receiver_state_separate_edges() {
        let left = edge(3, 7);
        let right_phase = edge(3, 11);
        let right_state = edge(4, 7);
        assert_ne!(left, right_phase);
        assert_ne!(left, right_state);
    }

    #[test]
    fn material_edge_projection_uses_exact_occurrence_to_source_map() {
        let occurrence_1 = fiber(OCCURRENCE_SCHEMA, 1);
        let occurrence_2 = fiber(OCCURRENCE_SCHEMA, 2);
        let ecology = ExactLabeledSuffixEcology::condition(
            &[vec![germ(1), germ(2)], vec![germ(1), germ(2)]],
            &[occurrence_1.clone(), occurrence_2.clone()],
        )
        .unwrap();
        let edge = ecology
            .material_edges()
            .unwrap()
            .into_iter()
            .find(|edge| edge.sources().len() == 2)
            .unwrap();
        let row = MorphologicalConductSupportRow::from_material_edge(
            MorphologicalConductChart::PassageLexical,
            &edge,
            |occurrence| {
                if occurrence == &occurrence_1 {
                    Ok(source(1))
                } else if occurrence == &occurrence_2 {
                    Ok(source(2))
                } else {
                    Err(MorphologicalConductRefusal::UnknownOccurrenceSource)
                }
            },
        )
        .unwrap();
        assert_eq!(row.target_sources().len(), 2);
        assert!(matches!(
            state(LocalSequence::from([row])),
            MorphologicalConductState::Conducting(_)
        ));
    }

    #[test]
    fn target_and_all_ablation_recover_typed_unconditioned_state() {
        let first = edge(5, 7);
        let second = edge(6, 7);
        let state = state(LocalSequence::from([
            row(first.clone(), &[(10, 1), (11, 2)], &[(20, 1)]),
            row(second.clone(), &[(12, 3), (13, 4)], &[(21, 3)]),
        ]));
        let MorphologicalConductState::Conducting(morphology) = state else {
            panic!("two plural contacts must conduct");
        };
        let target = morphology.ablate_target(&first).unwrap();
        let MorphologicalConductState::Conducting(remaining) = target.state else {
            panic!("the unrelated deposit must remain");
        };
        assert!(remaining.deposit(&first).is_none());
        assert!(remaining.deposit(&second).is_some());
        let all = remaining.ablate_all();
        assert_eq!(all.removed.len(), 1);
        assert_eq!(all.unconditioned, UnconditionedMorphologicalConduct);
    }

    #[test]
    fn the_plurality_is_the_callers_declaration_and_it_moves_the_deposited_population() {
        let single = row(edge(8, 7), &[(10, 1), (11, 1)], &[(20, 1)]);
        let plural = row(edge(9, 7), &[(12, 2), (13, 3)], &[(21, 2)]);
        let rows = LocalSequence::from([single, plural]);

        // THE ORBIT. The same atlas under two declared pluralities must not return the same
        // deposited population, or the parameter is present in the code and absent from the
        // evidence.
        let two = MorphologicalConductPlurality::recurrence_across_two_distinct_wholes();
        let MorphologicalConductState::Conducting(under_two) = state_under(rows.clone(), &two)
        else {
            panic!("one plural contact must conduct at two");
        };
        assert_eq!(under_two.deposit_count(), 1);
        assert_eq!(under_two.plurality().minimum_distinct_sources(), 2);
        assert!(!under_two.plurality().declared_by().is_empty());

        let one = MorphologicalConductPlurality::declared(
            1,
            "negative control: every material transport conducts, so the separation is the \
             plurality and nothing else",
        )
        .unwrap();
        let MorphologicalConductState::Conducting(under_one) = state_under(rows, &one) else {
            panic!("every contact conducts at one");
        };
        assert_eq!(under_one.deposit_count(), 2);

        assert_eq!(
            MorphologicalConductPlurality::declared(0, "vacuous"),
            Err(MorphologicalConductRefusal::VacuousPlurality)
        );
        assert_eq!(
            MorphologicalConductPlurality::declared(2, ""),
            Err(MorphologicalConductRefusal::UndeclaredPlurality)
        );
    }

    #[test]
    fn the_word_key_orders_as_the_card_order_at_every_declared_width() {
        let wide = ReceiverFiberIdentity::new(GERM_SCHEMA, [1u32, 0]);
        let ordered = [
            MorphologicalConductEdgeAddress::new(
                MorphologicalConductChart::ClauseLexical,
                1,
                fiber(GERM_SCHEMA, 1),
                RelationAtom::new(Cog::lit(1)).unwrap().words(),
                1,
            ),
            MorphologicalConductEdgeAddress::new(
                MorphologicalConductChart::ClauseLexical,
                1,
                fiber(GERM_SCHEMA, 1),
                RelationAtom::new(Cog::lit(1)).unwrap().words(),
                2,
            ),
            MorphologicalConductEdgeAddress::new(
                MorphologicalConductChart::ClauseLexical,
                1,
                fiber(GERM_SCHEMA, 1),
                RelationAtom::new(Cog::lit(2)).unwrap().words(),
                1,
            ),
            MorphologicalConductEdgeAddress::new(
                MorphologicalConductChart::ClauseLexical,
                1,
                fiber(GERM_SCHEMA, 2),
                RelationAtom::new(Cog::lit(1)).unwrap().words(),
                1,
            ),
            // A WIDER identity sorts after every narrower one, because the count is written before
            // the words. That is what makes the padded key injective and its order width-invariant.
            MorphologicalConductEdgeAddress::new(
                MorphologicalConductChart::ClauseLexical,
                1,
                wide.clone(),
                RelationAtom::new(Cog::lit(1)).unwrap().words(),
                1,
            ),
            MorphologicalConductEdgeAddress::new(
                MorphologicalConductChart::ClauseLexical,
                2,
                fiber(GERM_SCHEMA, 1),
                RelationAtom::new(Cog::lit(1)).unwrap().words(),
                1,
            ),
            MorphologicalConductEdgeAddress::new(
                MorphologicalConductChart::PassageLexical,
                1,
                fiber(GERM_SCHEMA, 1),
                RelationAtom::new(Cog::lit(1)).unwrap().words(),
                1,
            ),
        ];
        // THE ORBIT ON THE DECLARED WIDTH. If the order moved with the width, a front that widened
        // between launches would silently unsort the sheet the card binary-searches.
        for identity_words in [2usize, 5] {
            for pair in ordered.windows(2) {
                assert_eq!(
                    pair[0].card_key_cmp(&pair[1]),
                    core::cmp::Ordering::Less,
                    "the declared sequence is card-key order"
                );
                assert!(
                    soma_abi::morphological_conduct_cuda::key_precedes(
                        pair[0].key_words(identity_words).unwrap().as_ref(),
                        pair[1].key_words(identity_words).unwrap().as_ref()
                    ),
                    "the card searches on the key, so key order must be card-key order at width \
                     {identity_words}"
                );
            }
            for address in &ordered {
                assert_eq!(
                    address.key_words(identity_words).unwrap().len(),
                    MorphologicalConductEdgeAddress::key_word_extent(identity_words)
                );
            }
        }

        // Padding is injective: `[1]` and `[1, 0]` pad to the same trailing words and are separated
        // by the count field alone.
        let narrow = &ordered[0];
        let widened = &ordered[4];
        assert_eq!(narrow.germ_identity().words(), &[1]);
        assert_eq!(widened.germ_identity().words(), &[1, 0]);
        assert_ne!(
            narrow.key_words(2).unwrap(),
            widened.key_words(2).unwrap(),
            "the word count is what separates a padded identity from a genuinely wider one"
        );
        // And a width narrower than the material is refused rather than truncated.
        assert!(widened.key_words(1).is_none());
    }

    #[test]
    fn a_key_narrower_than_its_identity_refuses_by_name_rather_than_truncating() {
        // THE CONTROL FOR THE GUARD. Once the front computes its width off the same population it
        // encodes, the real path stops reaching this refusal — and a refusal nothing can reach is a
        // check that cannot fail. This constructs the condition directly.
        let wide = MorphologicalConductEdgeAddress::new(
            MorphologicalConductChart::ClauseLexical,
            1,
            ReceiverFiberIdentity::new(GERM_SCHEMA, [7u32, 8, 9]),
            RelationAtom::new(Cog::lit(1)).unwrap().words(),
            2,
        );
        assert_eq!(
            card_key(&wide, 2),
            Err(MorphologicalConductRefusal::NonuniformKeyWidth)
        );
        let admitted = card_key(&wide, 3).unwrap();
        assert_eq!(
            admitted.len(),
            MorphologicalConductEdgeAddress::key_word_extent(3)
        );
        // Widening past the material pads and never truncates: the identity's own words survive
        // unchanged and the extra words are the declared padding.
        let padded = card_key(&wide, 5).unwrap();
        assert_eq!(&padded.as_ref()[5..8], &[7, 8, 9]);
        assert_eq!(&padded.as_ref()[8..10], &[0, 0]);
    }

    #[test]
    fn duplicate_or_order_only_atlas_is_refused() {
        let first = row(edge(7, 7), &[(10, 1)], &[(20, 1)]);
        let duplicate = first.clone();
        assert_eq!(
            MorphologicalConductAtlas::found(LocalSequence::from([first, duplicate])),
            Err(MorphologicalConductRefusal::NoncanonicalAtlas)
        );
    }
}

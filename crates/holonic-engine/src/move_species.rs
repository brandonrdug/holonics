//! The species of a proof move, returned as a fiber rather than a label.
//!
//! **Record:** `research/records/2026-08-14_THE_MOVE_SPECIES_IS_A_FIBER_AND_THE_ISOLATED_POPULATION_IS_ITS_OWN_ROW.md`.
//!
//! This is the second instance of a shape the tree already owns. `soma/life/src/reconstruction_fiber.rs`
//! presents a token occurrence together with a declared candidate population, gives every candidate
//! **one common exposed face**, lets conduct reach their actual contexts, and returns the stable
//! block of [`crate::receiver_exact_compression`] as the fiber. Nothing chooses a surface. The
//! driver `the_token_reconstruction_remains_a_fiber` returns `["vectro","vector","tensor","matrix"]`
//! at `{kind}` and `["vectro","vector"]` at `{kind,weight}`, with `[tensor, matrix]` departing and
//! carrying their separating witnesses.
//!
//! **Here the occurrence is a proof move and the conduct is causal rather than positional.** A
//! token's neighbours are its stream predecessor and successor. A move's neighbours are the moves it
//! **feeds** and the moves it **arrives from** — [`crate::lean_development::DeclaredForm::internal_arrivals`],
//! which is a step recruiting a name an earlier step founded, with simultaneous foundings excluded
//! and sibling goal-scopes excluded because Lean's scopes are disjoint.
//!
//! So the atlas row is the fiber, and the *"phases between each other, causally linked"* are the
//! refinement lattice: which axis splits which class, and the shortest word that separates the
//! members it departed. (Formally the blocks are the Nerode congruence of the declared receiver
//! family over this transition system; `receiver_exact_compression` computes it and returns the
//! collapsed pairs with their witnesses.)
//!
//! # What this module does not do
//!
//! It assigns no method name, ranks nothing, and selects no canonical representative. A species is
//! **the block**, and its identity is the population plus the family that could not separate it. A
//! reading that returned one label per move would have deleted exactly the object.
//!
//! # The axis panels, and why the split is nameable
//!
//! [`MoveAxis::Former`] reads the founding tactic's **identity** — `have`, `obtain`, `set`. The
//! other five read the move's causal situation. Both panels are nameable so every reading can be
//! taken at both on one material, which is the discipline
//! [`crate::token_invariance::ReceiverAxis::ORTHOGRAPHIC`] already established for tokens.
//!
//! **The check that can fail is the spelling comparison.** If the causal panel's fiber coincides
//! with the former-only fiber on a declared population, the causal axes added nothing and the
//! reading is the tactic name wearing a different coat. That is the convicted centrifuge defect —
//! `2+2` separating from `2*2` by the operator's glyph — asked of this reading before it is
//! believed.
//!
//! **A relabelling control cannot fail here, and the reason is worth stating rather than
//! discovering.** Every observation enters `compress` through equality alone, and `Former` is
//! interned by identity, so renaming every tactic by a bijection moves no block. The centrifuge's
//! transport failed the same control at 11 of 13 boundaries because `contact_winding` was
//! `popcount(tail xor head)` — a function of the bytes rather than of the identity. Running the
//! control is still worth its cost: it is what distinguishes a reading that consumes identity from
//! one that consumes spelling, and only one of those is a transport invariant.

use std::collections::{BTreeMap, BTreeSet};

use serde::{Deserialize, Serialize};

use crate::lean_development::DeclaredForm;
use crate::receiver_exact_compression::{
    CollapsedPair, InputId, ItemId, Observation, ObservedSystem, Partition, ReceiverId, compress,
};

/// One situated proof move: the declaration it was written in and its step index inside that body.
///
/// The step **index** is the identity, never the binder name, because Lean shadows and
/// `· rintro ⟨b', hab', rfl⟩` beside `· intro hab` founds two different objects in one body.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct MoveOccurrence {
    pub declaration: u32,
    pub step: u32,
}

/// One receiver axis over a move. Each returns an exact `u64` that enters the quotient by equality
/// only — no axis is an ordering and none is a magnitude.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum MoveAxis {
    /// The founding tactic's identity, interned. **The spelling panel.**
    Former,
    /// Whether the step carries its own statement between the binder and `:=`.
    Ascribed,
    /// How many binders the founding act produced at once. `rintro ⟨c, ⟨b, hab, hbc⟩, hcd⟩` founds
    /// five in one act, and reading their token order as a chain would promote source layout into
    /// an invariant.
    Cohort,
    /// The depth of the `·` goal-scope stack the step was founded inside.
    FocusDepth,
    /// How many later steps arrive **from** this one.
    ArrivalsOut,
    /// How many earlier steps this one arrives **from**.
    ArrivalsIn,
}

impl MoveAxis {
    pub const DECLARED: [MoveAxis; 6] = [
        MoveAxis::Former,
        MoveAxis::Ascribed,
        MoveAxis::Cohort,
        MoveAxis::FocusDepth,
        MoveAxis::ArrivalsOut,
        MoveAxis::ArrivalsIn,
    ];

    /// The single axis that reads the tactic's identity rather than its situation.
    pub const SPELLING: [MoveAxis; 1] = [MoveAxis::Former];

    /// The five axes that read where the move sits in the body's own causal order.
    pub const CAUSAL: [MoveAxis; 5] = [
        MoveAxis::Ascribed,
        MoveAxis::Cohort,
        MoveAxis::FocusDepth,
        MoveAxis::ArrivalsOut,
        MoveAxis::ArrivalsIn,
    ];

    pub const fn index(self) -> usize {
        match self {
            MoveAxis::Former => 0,
            MoveAxis::Ascribed => 1,
            MoveAxis::Cohort => 2,
            MoveAxis::FocusDepth => 3,
            MoveAxis::ArrivalsOut => 4,
            MoveAxis::ArrivalsIn => 5,
        }
    }

    pub const fn id(self) -> ReceiverId {
        ReceiverId(self.index() as u64)
    }

    pub fn from_id(id: ReceiverId) -> Option<Self> {
        Self::DECLARED.get(id.0 as usize).copied()
    }

    pub const fn label(self) -> &'static str {
        match self {
            MoveAxis::Former => "former",
            MoveAxis::Ascribed => "ascribed",
            MoveAxis::Cohort => "cohort",
            MoveAxis::FocusDepth => "focus-depth",
            MoveAxis::ArrivalsOut => "arrivals-out",
            MoveAxis::ArrivalsIn => "arrivals-in",
        }
    }

    fn read(self, record: &MoveRecord) -> u64 {
        match self {
            MoveAxis::Former => record.former,
            MoveAxis::Ascribed => u64::from(record.ascribed),
            MoveAxis::Cohort => record.cohort,
            MoveAxis::FocusDepth => record.focus_depth,
            MoveAxis::ArrivalsOut => record.downstream.len() as u64,
            MoveAxis::ArrivalsIn => record.upstream.len() as u64,
        }
    }
}

/// A declared receiver family over moves. The empty family is refused rather than silently
/// returning one block, because a verdict at it could not have come out otherwise.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct MoveFamily(pub u8);

impl MoveFamily {
    pub const EMPTY: MoveFamily = MoveFamily(0);
    pub const FULL: MoveFamily = MoveFamily(0b111111);
    /// The tactic's identity alone.
    pub const SPELLING: MoveFamily = MoveFamily(0b000001);
    /// The move's causal situation, with no tactic identity at all.
    pub const CAUSAL: MoveFamily = MoveFamily(0b111110);

    pub fn of(axes: impl IntoIterator<Item = MoveAxis>) -> Self {
        MoveFamily(
            axes.into_iter()
                .fold(0u8, |bits, axis| bits | (1 << axis.index())),
        )
    }

    pub fn contains(self, axis: MoveAxis) -> bool {
        self.0 & (1 << axis.index()) != 0
    }

    pub fn with(self, axis: MoveAxis) -> Self {
        MoveFamily(self.0 | (1 << axis.index()))
    }

    pub fn without(self, axis: MoveAxis) -> Self {
        MoveFamily(self.0 & !(1 << axis.index()))
    }

    pub fn is_empty(self) -> bool {
        self.0 == 0
    }

    /// Whether every axis of `self` is also in `other`. A refinement must be a superset, and a
    /// reading that changed the family sideways is not a refinement of anything.
    pub fn refines(self, coarser: MoveFamily) -> bool {
        coarser.0 & !self.0 == 0
    }

    pub fn axes(self) -> Vec<MoveAxis> {
        MoveAxis::DECLARED
            .into_iter()
            .filter(|axis| self.contains(*axis))
            .collect()
    }

    pub fn label(self) -> String {
        let axes = self.axes();
        if axes.is_empty() {
            return "{}".to_owned();
        }
        format!(
            "{{{}}}",
            axes.iter()
                .map(|axis| axis.label())
                .collect::<Vec<_>>()
                .join(",")
        )
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct MoveRecord {
    occurrence: MoveOccurrence,
    former: u64,
    ascribed: bool,
    cohort: u64,
    focus_depth: u64,
    /// Later steps that arrive from this one, in canonical step order.
    downstream: Vec<usize>,
    /// Earlier steps this one arrives from, in canonical step order.
    upstream: Vec<usize>,
    /// Something in the declaration consumes this binder that is **not a later step** — in practice
    /// the closing term. See [`MoveComplex::terminally_consumed`].
    terminal: bool,
}

/// The founded move material: every step of every admitted declaration, with the intra-declaration
/// arrival graph and an interning of the founding tactics.
///
/// The branch aperture is **read off the material** — it is the largest downstream or upstream
/// degree present — so no number here is authored. A caller may not raise it; a material with a
/// wider branch simply returns a wider aperture.
#[derive(Clone, Debug)]
pub struct MoveComplex {
    records: Vec<MoveRecord>,
    index: BTreeMap<MoveOccurrence, usize>,
    formers: Vec<String>,
    branch_aperture: usize,
}

impl MoveComplex {
    /// Found the complex over a declared population of read declarations.
    ///
    /// `declarations` is indexed positionally and that index becomes [`MoveOccurrence::declaration`],
    /// so a caller joining back to source keeps its own ordering.
    pub fn found(declarations: &[DeclaredForm]) -> Self {
        let mut records = Vec::new();
        let mut index = BTreeMap::new();
        let mut formers: Vec<String> = Vec::new();
        let mut former_ids: BTreeMap<String, u64> = BTreeMap::new();
        let mut base_of_declaration = Vec::with_capacity(declarations.len());

        for (declaration, form) in declarations.iter().enumerate() {
            base_of_declaration.push(records.len());
            for (step_index, step) in form.steps.iter().enumerate() {
                let former = *former_ids.entry(step.former.clone()).or_insert_with(|| {
                    formers.push(step.former.clone());
                    (formers.len() - 1) as u64
                });
                let occurrence = MoveOccurrence {
                    declaration: declaration as u32,
                    step: step_index as u32,
                };
                index.insert(occurrence, records.len());
                records.push(MoveRecord {
                    occurrence,
                    former,
                    ascribed: !step.statement.trim().is_empty(),
                    cohort: form
                        .steps
                        .iter()
                        .filter(|other| other.cohort == step.cohort)
                        .count() as u64,
                    focus_depth: step.focus.len() as u64,
                    downstream: Vec::new(),
                    upstream: Vec::new(),
                    terminal: false,
                });
            }
        }

        for (declaration, form) in declarations.iter().enumerate() {
            let base = base_of_declaration[declaration];
            for (from, to) in form.internal_arrivals() {
                let from = base + from;
                let to = base + to;
                if from >= records.len() || to >= records.len() {
                    continue;
                }
                records[from].downstream.push(to);
                records[to].upstream.push(from);
            }
        }
        for record in &mut records {
            record.downstream.sort_unstable();
            record.downstream.dedup();
            record.upstream.sort_unstable();
            record.upstream.dedup();
        }

        // A binder consumed by something that is not a later step. `local_bindings` counts every
        // occurrence of a founded name in the body, its own founding line included, so subtracting
        // that founding and the step-to-step arrivals leaves exactly the uses no step accounts for.
        //
        // **This exists because an independent instrument found the gap.**
        // `the_kernel_decides_which_moves_are_load_bearing` deleted each move of a real development
        // and asked Lean: 5 of 10 moves this reading called isolated had their binder named again
        // later in the same body, and the kernel refused every one of them. A declaration's closing
        // term is not a step, so a `have` the final tactic consumes has no outgoing arrival.
        // `isolated` therefore means *no later STEP arrives here* and never *nothing uses this*.
        for (declaration, form) in declarations.iter().enumerate() {
            let base = base_of_declaration[declaration];
            for (step_index, step) in form.steps.iter().enumerate() {
                let index = base + step_index;
                let Some(record) = records.get_mut(index) else {
                    continue;
                };
                let named = form
                    .local_bindings
                    .get(&step.binder)
                    .copied()
                    .unwrap_or(0) as usize;
                record.terminal = named.saturating_sub(1) > record.downstream.len();
            }
        }

        let branch_aperture = records
            .iter()
            .map(|record| record.downstream.len().max(record.upstream.len()))
            .max()
            .unwrap_or(0);

        Self {
            records,
            index,
            formers,
            branch_aperture,
        }
    }

    pub fn moves(&self) -> usize {
        self.records.len()
    }

    pub fn arrivals(&self) -> usize {
        self.records
            .iter()
            .map(|record| record.downstream.len())
            .sum()
    }

    /// The widest downstream or upstream degree in this material. Zero means every move is isolated
    /// and conduct can reach nothing, which is a property of the material and not a refusal.
    pub fn branch_aperture(&self) -> usize {
        self.branch_aperture
    }

    /// How many distinct founding tactics the material exposed.
    pub fn formers(&self) -> usize {
        self.formers.len()
    }

    pub fn former_label(&self, occurrence: MoveOccurrence) -> Option<&str> {
        let record = self.records.get(*self.index.get(&occurrence)?)?;
        self.formers.get(record.former as usize).map(String::as_str)
    }

    pub fn occurrences(&self) -> impl Iterator<Item = MoveOccurrence> + '_ {
        self.records.iter().map(|record| record.occurrence)
    }

    /// How many later moves arrive from this one, and how many earlier ones it arrives from.
    pub fn reach(&self, occurrence: MoveOccurrence) -> Option<(usize, usize)> {
        let record = self.records.get(*self.index.get(&occurrence)?)?;
        Some((record.downstream.len(), record.upstream.len()))
    }

    /// Moves conduct can reach something from, in canonical order.
    ///
    /// **A focus outside this population makes every family return the same block**, and that is
    /// not a defect in the family — an isolated move presents only its common exposed face, so
    /// there is nothing for any receiver to read. Measured on
    /// `Mathlib/Geometry/Euclidean/Triangle.lean`: 78 moves, 25 arrivals, and a focus taken as
    /// "first in canonical order" landed on an isolated one, where the causal panel and the
    /// spelling panel returned an identical species of 45. The reading was right and the focus was
    /// uninformative.
    pub fn connected(&self) -> Vec<MoveOccurrence> {
        self.records
            .iter()
            .filter(|record| !record.downstream.is_empty() || !record.upstream.is_empty())
            .map(|record| record.occurrence)
            .collect()
    }

    /// Whether something that is **not a later step** consumes this move's binder — in practice the
    /// declaration's closing term.
    ///
    /// A move can be [`MoveComplex::isolated`] and still terminally consumed, and on real material
    /// half of them are. Reading `isolated` as *unused* is the error this accessor exists to make
    /// impossible.
    pub fn terminally_consumed(&self, occurrence: MoveOccurrence) -> Option<bool> {
        Some(self.records.get(*self.index.get(&occurrence)?)?.terminal)
    }

    /// Moves nothing consumes at all: no later step arrives, and the closing term does not name
    /// them either. **This is the population `isolated` was mistaken for.**
    pub fn unconsumed(&self) -> Vec<MoveOccurrence> {
        self.records
            .iter()
            .filter(|record| {
                record.downstream.is_empty() && record.upstream.is_empty() && !record.terminal
            })
            .map(|record| record.occurrence)
            .collect()
    }

    /// Moves conduct reaches nothing from, in the strict step-to-step sense.
    ///
    /// **This is not the unused population.** A `have` the closing term consumes lands here, because
    /// the closing term is not a step — see [`MoveComplex::unconsumed`] for the population that is
    /// genuinely unused, and [`MoveComplex::terminally_consumed`] for the difference.
    pub fn isolated(&self) -> Vec<MoveOccurrence> {
        self.records
            .iter()
            .filter(|record| record.downstream.is_empty() && record.upstream.is_empty())
            .map(|record| record.occurrence)
            .collect()
    }

    /// Every move whose founding tactic is one of the named ones, in canonical order.
    pub fn founded_by(&self, formers: &BTreeSet<String>) -> Vec<MoveOccurrence> {
        self.records
            .iter()
            .filter(|record| {
                self.formers
                    .get(record.former as usize)
                    .is_some_and(|former| formers.contains(former))
            })
            .map(|record| record.occurrence)
            .collect()
    }

    /// Rename every founding tactic by a declared bijection, leaving all else untouched.
    ///
    /// The control this exists for cannot fail, and that is the point: observations enter the
    /// quotient by equality, so a relabelling is invisible to every block. A reading that moved
    /// under this would be consuming bytes rather than identity.
    pub fn with_renamed_formers(&self, rename: impl Fn(&str) -> String) -> Self {
        let mut renamed = self.clone();
        renamed.formers = self.formers.iter().map(|former| rename(former)).collect();
        renamed
    }
}

/// What a fiber will cost before it is computed. A caller holds this against its own cover.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct MoveWorkDemand {
    pub roots: usize,
    pub slots: usize,
    pub items: usize,
    pub pair_chart: usize,
}

/// What a caller can hold. Work never participates in the quotient; it decides only whether the
/// whole requested chart can be presented.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct MoveWorkCover {
    pub items: usize,
    pub pair_chart: usize,
}

impl MoveWorkCover {
    pub fn exactly(demand: &MoveWorkDemand) -> Self {
        Self {
            items: demand.items,
            pair_chart: demand.pair_chart,
        }
    }

    pub fn holds(&self, demand: &MoveWorkDemand) -> bool {
        self.items >= demand.items && self.pair_chart >= demand.pair_chart
    }
}

/// The declaration a caller makes before a fiber is returned.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MoveDeclaration {
    /// The complete finite candidate population. Never inferred.
    pub candidates: Vec<MoveOccurrence>,
    pub family: MoveFamily,
    /// How far conduct reaches through the arrival graph.
    pub horizon: usize,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum MoveSpeciesError {
    /// The declared family is empty; every move would land in one block whatever the material did.
    EmptyFamily,
    /// The focus is not in the declared candidate population. A fiber is always *of* a focus.
    FocusNotDeclared,
    /// A declared occurrence is not in this complex.
    OccurrenceAbsent(MoveOccurrence),
    /// Fewer than two candidates. A fiber of one is a restatement of the declaration.
    CandidatesTooFew(usize),
    /// The caller's cover cannot hold the chart. Refused **before** execution.
    WorkCoverInsufficient {
        demand: MoveWorkDemand,
        cover: MoveWorkCover,
    },
}

/// The returned fiber: what the declared family could not separate, and what it could.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct MoveSpeciesFiber {
    pub family: MoveFamily,
    pub horizon: usize,
    pub focus: MoveOccurrence,
    /// Every candidate the family leaves indistinguishable from the focus, focus included. **This
    /// is the species.**
    pub fiber: Vec<MoveOccurrence>,
    /// The one-shot blocks over the candidate roots — the reading before conduct refines it.
    pub one_shot_blocks: usize,
    /// The stable blocks over the candidate roots — the reading after conduct refines it.
    pub conduct_blocks: usize,
    /// Refinement rounds to stability, which is also the longest shortest-distinguishing-word
    /// length: **how far back the reading had to look.**
    pub memory_order: usize,
    /// Pairs the one-shot reading identified that conduct separates, each carrying its witness.
    pub collapsed: Vec<CollapsedPair>,
    pub demand: MoveWorkDemand,
}

impl MoveSpeciesFiber {
    /// The fiber is a species only if it holds more than the focus. A singleton says the family
    /// separated everything, which is a real return and a different one.
    pub fn is_plural(&self) -> bool {
        self.fiber.len() > 1
    }
}

/// A coarse fiber refined by a richer family: what stayed, what departed, and the witness.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct MoveSpeciesRefinement {
    pub coarse: MoveSpeciesFiber,
    pub richer: MoveSpeciesFiber,
    pub retained: Vec<MoveOccurrence>,
    /// Members the richer family removed from the focus's species.
    pub departed: Vec<MoveOccurrence>,
    /// Shortest separating witnesses the richer reading exhibited.
    pub witnesses: usize,
}

impl MoveSpeciesRefinement {
    /// A refinement that departs nothing has declared an axis this material cannot see. It is not
    /// an error and it is not evidence; it is a measurement of the axis.
    pub fn moved(&self) -> bool {
        !self.departed.is_empty()
    }
}

/// The cost of the requested chart, without computing it.
pub fn move_demand(complex: &MoveComplex, declaration: &MoveDeclaration) -> MoveWorkDemand {
    let roots = declaration.candidates.len();
    let slots = slot_extent(complex.branch_aperture, declaration.horizon);
    let items = roots.saturating_mul(slots);
    MoveWorkDemand {
        roots,
        slots,
        items,
        pair_chart: items.saturating_mul(items.saturating_sub(1)) / 2,
    }
}

/// Return the focus's complete species under the declared family, or refuse before execution.
pub fn species_fiber(
    complex: &MoveComplex,
    focus: MoveOccurrence,
    declaration: &MoveDeclaration,
    cover: &MoveWorkCover,
) -> Result<MoveSpeciesFiber, MoveSpeciesError> {
    if declaration.family.is_empty() {
        return Err(MoveSpeciesError::EmptyFamily);
    }
    if declaration.candidates.len() < 2 {
        return Err(MoveSpeciesError::CandidatesTooFew(
            declaration.candidates.len(),
        ));
    }
    if !declaration.candidates.contains(&focus) {
        return Err(MoveSpeciesError::FocusNotDeclared);
    }
    let mut roots = Vec::with_capacity(declaration.candidates.len());
    for candidate in &declaration.candidates {
        let record = *complex
            .index
            .get(candidate)
            .ok_or(MoveSpeciesError::OccurrenceAbsent(*candidate))?;
        roots.push(record);
    }
    let demand = move_demand(complex, declaration);
    if !cover.holds(&demand) {
        return Err(MoveSpeciesError::WorkCoverInsufficient {
            demand,
            cover: *cover,
        });
    }

    let system = MoveSystem {
        complex,
        roots: roots.clone(),
        horizon: declaration.horizon,
        axes: declaration.family.axes(),
    };
    let compression = compress(&system);
    let focus_root = declaration
        .candidates
        .iter()
        .position(|candidate| *candidate == focus)
        .expect("the focus was checked to be declared");
    let focus_item = system.root_item(focus_root);
    let block = compression
        .conduct
        .block_of(focus_item)
        .expect("a presented root belongs to the compression");

    let fiber = compression.conduct.blocks[block]
        .iter()
        .filter_map(|item| system.root_index(*item))
        .map(|root| declaration.candidates[root])
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect();

    Ok(MoveSpeciesFiber {
        family: declaration.family,
        horizon: declaration.horizon,
        focus,
        fiber,
        one_shot_blocks: root_blocks(&system, &compression.one_shot),
        conduct_blocks: root_blocks(&system, &compression.conduct),
        memory_order: compression.rounds,
        collapsed: compression.collapsed,
        demand,
    })
}

/// Take the same population at a coarse family and then at a richer one, and deposit what departed.
///
/// The richer family must **refine** the coarse one — a superset of axes — because a reading taken
/// at a sideways family is not a refinement of anything and its departures would mean nothing.
pub fn refine_species(
    complex: &MoveComplex,
    focus: MoveOccurrence,
    coarse: &MoveDeclaration,
    richer: &MoveDeclaration,
    cover: &MoveWorkCover,
) -> Result<MoveSpeciesRefinement, MoveSpeciesError> {
    debug_assert!(
        richer.family.refines(coarse.family),
        "the richer family must contain every axis of the coarse one"
    );
    let coarse_fiber = species_fiber(complex, focus, coarse, cover)?;
    let richer_fiber = species_fiber(complex, focus, richer, cover)?;
    let retained_set: BTreeSet<MoveOccurrence> = richer_fiber.fiber.iter().copied().collect();
    let departed = coarse_fiber
        .fiber
        .iter()
        .copied()
        .filter(|member| !retained_set.contains(member))
        .collect();
    Ok(MoveSpeciesRefinement {
        retained: richer_fiber.fiber.clone(),
        departed,
        witnesses: richer_fiber.collapsed.len(),
        coarse: coarse_fiber,
        richer: richer_fiber,
    })
}

/// Paths of length at most `horizon` over an alphabet of `2 * aperture` letters, the empty path
/// included. With no branch at all the only slot is the root itself.
fn slot_extent(aperture: usize, horizon: usize) -> usize {
    let letters = aperture.saturating_mul(2);
    if letters == 0 {
        return 1;
    }
    let mut total = 1usize;
    let mut level = 1usize;
    for _ in 0..horizon {
        level = level.saturating_mul(letters);
        total = total.saturating_add(level);
    }
    total
}

fn root_blocks(system: &MoveSystem<'_>, partition: &Partition) -> usize {
    partition
        .blocks
        .iter()
        .filter(|block| block.iter().any(|item| system.root_index(*item).is_some()))
        .count()
}

/// The candidate-root system over moves.
///
/// Slot zero is the root's **common exposed face**: every candidate observes the same value there,
/// so nothing about a candidate's own move can separate it and only its causal situation can. That
/// is the same construction `reconstruction_fiber` uses to keep a token's own spelling out of its
/// fiber, and it is what makes the return a species rather than a lookup.
struct MoveSystem<'a> {
    complex: &'a MoveComplex,
    roots: Vec<usize>,
    horizon: usize,
    axes: Vec<MoveAxis>,
}

impl MoveSystem<'_> {
    fn letters(&self) -> usize {
        self.complex.branch_aperture * 2
    }

    fn stride(&self) -> u64 {
        slot_extent(self.complex.branch_aperture, self.horizon) as u64
    }

    fn root_item(&self, root: usize) -> ItemId {
        ItemId(root as u64 * self.stride())
    }

    fn root_index(&self, item: ItemId) -> Option<usize> {
        let stride = self.stride();
        ((item.0 % stride) == 0)
            .then_some((item.0 / stride) as usize)
            .filter(|root| *root < self.roots.len())
    }

    /// Resolve a slot to the word of letters that reaches it. Slot 0 is the empty word; slots then
    /// enumerate length 1, then length 2, in letter order.
    fn word(&self, slot: u64) -> Option<Vec<usize>> {
        let letters = self.letters() as u64;
        if slot == 0 {
            return Some(Vec::new());
        }
        if letters == 0 {
            return None;
        }
        let mut remaining = slot;
        let mut length = 1usize;
        let mut level = letters;
        while remaining > level {
            remaining -= level;
            level = level.checked_mul(letters)?;
            length += 1;
            if length > self.horizon {
                return None;
            }
        }
        if length > self.horizon {
            return None;
        }
        let mut ordinal = remaining - 1;
        let mut word = vec![0usize; length];
        for position in (0..length).rev() {
            word[position] = (ordinal % letters) as usize;
            ordinal /= letters;
        }
        Some(word)
    }

    /// Follow a word from a root through the arrival graph. A letter below the aperture is a
    /// downstream arrival; a letter at or above it is an upstream one.
    fn site(&self, item: ItemId) -> Option<usize> {
        let stride = self.stride();
        let root = (item.0 / stride) as usize;
        let mut here = *self.roots.get(root)?;
        for letter in self.word(item.0 % stride)? {
            let record = self.complex.records.get(here)?;
            let aperture = self.complex.branch_aperture;
            let next = if letter < aperture {
                record.downstream.get(letter)
            } else {
                record.upstream.get(letter - aperture)
            }?;
            here = *next;
        }
        Some(here)
    }
}

impl ObservedSystem for MoveSystem<'_> {
    fn items(&self) -> Vec<ItemId> {
        let stride = self.stride();
        (0..self.roots.len())
            .flat_map(|root| {
                (0..stride).filter_map(move |slot| {
                    let item = ItemId(root as u64 * stride + slot);
                    self.site(item).map(|_| item)
                })
            })
            .collect()
    }

    fn receivers(&self) -> Vec<ReceiverId> {
        self.axes.iter().map(|axis| axis.id()).collect()
    }

    fn inputs(&self) -> Vec<InputId> {
        (0..self.letters() as u64).map(InputId).collect()
    }

    fn observation(&self, item: ItemId, receiver: ReceiverId) -> Observation {
        if self.root_index(item).is_some() {
            return Observation(0);
        }
        let Some(site) = self.site(item) else {
            return Observation(u64::MAX);
        };
        let record = &self.complex.records[site];
        Observation(
            MoveAxis::from_id(receiver)
                .map(|axis| axis.read(record))
                .unwrap_or(u64::MAX),
        )
    }

    fn successor(&self, item: ItemId, input: InputId) -> Option<ItemId> {
        let letters = self.letters() as u64;
        if input.0 >= letters {
            return None;
        }
        let stride = self.stride();
        let root = item.0 / stride;
        let slot = item.0 % stride;
        let mut word = self.word(slot)?;
        if word.len() >= self.horizon {
            return None;
        }
        word.push(input.0 as usize);
        let next_slot = self.slot_of(&word)?;
        let next = ItemId(root * stride + next_slot);
        self.site(next).map(|_| next)
    }
}

impl MoveSystem<'_> {
    fn slot_of(&self, word: &[usize]) -> Option<u64> {
        let letters = self.letters() as u64;
        if word.is_empty() {
            return Some(0);
        }
        if letters == 0 {
            return None;
        }
        let mut base = 1u64;
        let mut level = letters;
        for _ in 1..word.len() {
            base = base.checked_add(level)?;
            level = level.checked_mul(letters)?;
        }
        let mut ordinal = 0u64;
        for letter in word {
            ordinal = ordinal.checked_mul(letters)?.checked_add(*letter as u64)?;
        }
        base.checked_add(ordinal)
    }
}

#[cfg(test)]
mod tests;

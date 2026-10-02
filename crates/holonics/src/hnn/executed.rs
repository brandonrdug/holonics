//! **The release's own comparison: its declared compositions and readings, their exact pullback, a
//! carried update and the release's full receipt** (THE_REBUILD U6; the
//! [diagnosis record](../../../../research/records/2026-09-30_THE_LEARNING_FAILURE_DIAGNOSED_THE_TRAINED_COMPARISON_IS_NOT_THE_ONE_THE_RELEASE_EXECUTES.md)
//! §5; step 1b's
//! [pin](../../../../research/records/2026-09-30_STEP_1B_THE_CANDIDATE_COMPARISON_PINNED_BEFORE_ITS_RUNS.md)
//! §2 as amended by its §13; #73, #148, #63).
//!
//! [definition; agent-inferred, September 30] The receiving bank's release (`hnn::prediction`,
//! [`bank_release`], one owner of the lock iteration) decides every station by the largest member's
//! executed growth from its actual storage. The learning path trained a different quantity (the
//! bank's second-order face) in different contexts (the readout's partitions); its descent
//! direction met the executed decision's at cosine `39/512`. This owner compares exactly what the
//! release executes, in the contexts it executes, and joins that comparison to its pullback and to a
//! carried update of `E` and the source navigator's transport modulus `ρ` (the pumps, the other
//! families and the fold held).
//!
//! **The station's readings.** For a request of `n` cells with locked partial section `S`, every
//! open station `j` and class `x`, the actual storage is the passage's read from `j`
//! (`hnn::prediction`, "The section continues the request's passage" and "A candidate reads the span
//! from its own station"):
//! `z_(S,j,x) = z_pairs + Σ_c w_j(c) P^(λ−c) E M[c] + Σ_(k∈S) w_j(k) P^(r_k) E e_(S_k) + w_j(j) P^(r_j) E e_x`,
//! `w_j(k) = ρ^|τ_j − τ_k| / Σ_l ρ^|τ_j − τ_l|` (`BankPlacement::storage`), and the reading is
//! `a_(j,x) = max_m ρ(M_m(z))` with exact enclosure `[L, U]` (`ReceivingBank::read_turn`): one
//! turn's cell holonomy, the joint over the bank's members. Against the target `t` of station `j`
//! ([`StationComparison`], every one read exactly):
//! - **class**: `L_(j,t) > U_(j,x)` for every `x ≠ t` ([`Predicate`]: holds, fails when some
//!   rival's `L` reaches the target's `U`, else undecided);
//! - **threshold**: `L_(j,t) > 1`;
//! - **the lock's flip** (the solved level): `1 + Σ_(x≠t) U_(j,x) < L_(j,t)`, one exact rational
//!   comparison and the authoritative solved predicate (holds; fails when `1 + Σ_(x≠t) L_x ≥ U_t`;
//!   else undecided); it implies class and threshold (Lean
//!   `HNN/ExecutedComparison.lockFace_enclosure_sublevel`) and is strictly stronger than the
//!   release's per-rival predicate; read per station, never as an aggregate;
//! - **order** (the machine's own refinements): the eligible stations and gaps the release read,
//!   the stations of the strictly largest gap locking together; the lock is safe when every station
//!   it locks is correct ([`OrderReading`]);
//! - **section**: the complete release, its termination and any refusal (`BankGeneration`).
//!
//! **The two compositions** ([`Composition`]) [definition; agent-inferred]:
//! - **the hinge** (1a's): `f_j = max(max_(x≠t) ln(a_x/a_t), −ln a_t)`, `F = Σ (f_j)_+`. Its zero
//!   set is the closed predicate set, every candidate tie above threshold included, where the class
//!   fails and the release holds (Lean `hinge_zero_iff`, `hinge_zero_at_tie`), and a right decision
//!   leaves `F` with no covector (`hinge_right_leaves`); its solved level is zero;
//! - **the lock face** (step 1b's candidate, the pin §2): each station's lock read whole, its
//!   candidates biased sheets of weights `a_x` and its resting sheet the lossless ring's weight one
//!   (the release's own threshold normalization), `Π = 1 + Σ_x a_x`, `θ_x = a_x/Π`,
//!   `ℓ_j = log(Π/a_t) = −log θ_t` enclosed on
//!   `[ln(1 + (1 + Σ_(x≠t) L_x)/U_t), ln(1 + (1 + Σ_(x≠t) U_x)/L_t)]` (`ln_enclosure`), `L = Σ ℓ_j`;
//!   its covector on the log-readings is `θ − q` (`lockFace_covector`), its solved level the lock's
//!   flip `ℓ < log 2` (`lockFace_lt_log_two_iff`), read by the rational test above. "No zero and no
//!   minimizer" (`lockFace_pos`, `lockFace_strictAnti`) is a statement in unconstrained growth
//!   coordinates, not a fact about the bounded constitution (the pin §13.2).
//!
//! Each composition's **excess over its solved level** is `X = Σ_j (term_j − level)_+`: for the
//! hinge `X = F`, for the lock face `X = Σ (ℓ_j − ln 2)_+`, a term's share exactly zero where the
//! rational solved test holds (it is authoritative over the logarithm's enclosure). A term is
//! [`Excess::Solved`], [`Excess::Above`] (certainly past its level: `f⁻ > 0`, or
//! `1 + Σ_(x≠t) L_x > U_t`), or [`Excess::Boundary`] (neither is certain, `ℓ = ln 2` exactly
//! included, which the strict test never counts solved).
//!
//! **The readings** ([`Reading`]; the pin §2.4, §13.1): on an open context the release runs its
//! refinements from the open section; a composition reads its terms at
//! - **every refinement** (1a's reading): every open station of every refinement;
//! - **the decisions**: each station once, at `d(j)`, the refinement locking `j` when that is before
//!   `r*`, else `r*`, with `r*` the last refinement whose placed cells all equal their targets. At
//!   `r*` every station still open is read, the first wrong lock and the held stations included, so
//!   a request keeps exactly `m` obligations on a release, a hold and a refused certificate alike;
//! - **the teacher-forced left-to-right diagnostic**: station `j` at the section holding every
//!   earlier station at its target and the rest open (a section the release need not execute).
//!
//! On a partition context the partition's one refinement is read. The targets are the terrain's
//! declared input, read only by the comparison (validated: one per station, each a class of the
//! chart); the release never reads one. Zero denominators keep their fibre: a reading whose lower end
//! is not positive refuses the comparison ([`HnnError::NonpositiveDeclaration`]), nothing is added
//! to a reading, and a candidate the crossing's signed form refuses refuses the comparison.
//!
//! **The covector** (`hnn::ring`, "The executed growth's covector"). Each candidate's active members
//! (those whose enclosure reaches the joint's lower end) return the simple-root eigen-derivative of
//! their executed monodromy through the executed tick and its solve, or a typed refusal
//! (`CovectorRefusal`: collision, tie, defective). The proposal is carried from each candidate's
//! storage to `E` through the request's phases and the section's placements
//! (`SourceMoment::encoder_covector`'s law, per phase), as the source port's returns ([`returns`]):
//! - **the hinge** descends each positive term along its leading branch (its rivals and threshold
//!   whose enclosure reaches the term's lower end, the largest midpoint, its leading members), the
//!   rival at weight `+1` and the target at `−1`;
//! - **the lock face** descends every term along every candidate's leading member, at the weights
//!   `c_x = θ_x` (`x ≠ t`) and `c_t = θ_t − 1`, each at the dyadic face of its enclosure's midpoint
//!   (`θ_x ∈ [L_x/(1 + L_x + Σ_(y≠x) U_y), U_x/(1 + U_x + Σ_(y≠x) L_y)]`).
//!
//! **The first-order certificate** on a move's exact storage moves `Δz` (Lean `sum_max_descends`,
//! `lockFace_first_order`, `sum_upper_dini_descends`): the hinge's term bound is
//! `sup_(α active) Df_α[Δz]` (a straddling term's hinged at zero); the lock face's is
//! `Σ_(x≠t) sup(θ_x · D_x) + sup((θ_t − 1) · D_t)` in interval arithmetic,
//! `D_x = [min_(m∈A_x) ⟨ĝ_(x,m), Δz_x⟩⁻, max_(m∈A_x) ⟨ĝ_(x,m), Δz_x⟩⁺]` over the candidate's
//! enclosure-active members. The composition's bound is the sum over its terms; the excess's
//! **piecewise directional derivative** (the pin §13.5) sums the bounds of the terms above their
//! level and `max(bound, 0)` over the boundary terms (solved terms add nothing).
//!
//! **The committed move** ([`executed_move`], its conditions of adoption the same for every
//! composition and reading, the pin §13.4). The source port's normal law prepares the unit step on
//! the returns (`Constitution::stepped_source`); the modulus's unit move is its least-squares step
//! `Δρ = −γ_ρ/G_ρ` with `γ_ρ = Σ_c c ⟨ĝ_c, ∂z_c/∂ρ⟩` and `G_ρ = Σ_c |∂z_c/∂ρ|²` over the proposal's
//! contributions (`BankPlacement::modulus_derivative`; Lean `modulus_least_squares`); none upward
//! from `ρ = 1`. Then:
//! - **an unresolved active member refuses the move** ([`MoveRefusal::Unresolved`]): a term the
//!   certificate reads with any active member unresolved is never bounded by its resolved members
//!   alone (1a's hinge let it through);
//! - **the slope is read on the joint unit direction** `(ΔE, Δρ)`, each storage move the exact
//!   `E`-part plus `(∂z/∂ρ)Δρ`, before any refusal (the old early test on `E`'s unit alone could
//!   refuse before the modulus joined); the move is refused, typed, when the composition's joint
//!   bound is not negative;
//! - **the first trial step** is `η₀ = 2^⌊log₂ min(X⁻/(−s_X⁺), ½/u)⌋`, `s_X` the excess's piecewise
//!   derivative on the joint unit move and `u` its largest entry change ([`ladder_start`]); with
//!   `X⁻ = 0`, or `s_X⁺ ≥ 0`, the entry scale `½/u` alone: no division by a zero excess or a
//!   nonnegative slope, and nothing becomes solved by it;
//! - each carried successor `(E + ηD, ρ + ηΔρ)` (`ρ` held on the port's lattice within
//!   `[ρ/2, max(ρ₀, ρ)]` under every metric, `ρ₀` the founding's one-turn alias bound) is adopted
//!   only when all of these hold on it: the entry bound `2^ENTRY_BOUND = 8` ([`entry_bound`]); the
//!   first-order certificate negative on the carried move; every crossing of its own release
//!   admissible and every lock's Floquet certificate certified; every reading supported; the
//!   constitution's own conditions on a deposit (its bit budget and certified storage growth);
//!   **the fixed incumbent mask's composition strictly lower by disjoint enclosures**,
//!   `C_mask(Θ′)⁺ < C(Θ)⁻`; and **the composition the successor's own release executes strictly
//!   lower too**, `C_own(Θ′)⁺ < C(Θ)⁻` (October 1, the
//!   [native direction record](../../../../research/records/2026-10-01_THE_NATIVE_DIRECTION_MEASURED_THE_STEP_DESCENDS_THE_EXECUTED_RELEASE_WITHIN_ITS_CELL_AND_GATE_A_ADOPTED_SIXTEEN_TIMES_BEYOND_IT.md):
//!   the mask's first order holds only within the trajectory cell where the mask and the own
//!   release coincide, and gate A's first move certified the mask's decrease sixteen times past
//!   that cell while the executed release rose). Within the cell the second condition is the first;
//!   past it, a step is adopted only while the executed comparison still descends, so over moves on
//!   fixed requests the executed composition falls strictly at every adopted move;
//! - otherwise the step is halved and tried again until the carried move falls below the lattice's
//!   resolution (`η · 2u < λ`, `λ` the source port's lattice unit), and the move is refused, typed,
//!   when no trial is adopted. The lattice alone ends the halvings: with `η₀ · 2u ≤ 1` a halving `k`
//!   is tried only when `2^k ≤ 1/λ` (Lean `HNN/ReleaseRun.attempted_halvings_le_lattice`; the
//!   [run-end record](../../../../research/records/2026-10-02_A_RUN_CLOSES_ON_A_CONDITION_NOT_A_LENGTH_AND_THE_HALVINGS_END_AT_THE_LATTICE.md) §3).
//!
//! **The two readings, kept apart** (the pin §13.1). The descent account is read on one fixed
//! conditional-context mask, the incumbent's own terms' sections: the proposal, its first order and
//! the successor's re-read compare like with like. The mask is transient within the move: it is
//! formed from the incumbent's release, read once at each trial and discarded with the move; no
//! event, no replay history is retained. The successor's **own release** is read beside it for
//! behaviour and for its own certificates (admissible crossings, certified locks, supported
//! readings); its recomputed composition is a condition of adoption (it must fall) and is never
//! read as decision progress, with the context change (own less mask) beside it. Every count is kept ([`TermCounts`]): attempted, unresolved, absent, post-error, held,
//! support, coverage. The persistence reads (the pin §13.7, [`Persistence`]) re-read each decision
//! solved at its refinement after the later locks of its section.
//!
//! The operands are transient; nothing of the comparison is retained: the successor's `E`, `ρ` and
//! the source port's normal law are the only change (their complete continuing state is
//! `Constitution::continuing_state`).
//!
//! **Every modality reads it the same way**: the comparison reads the receiving ring's storage,
//! which holds any chart's classes through `E` at their residues; nothing here reads a byte, a
//! pixel or an alphabet's meaning.
//!
//! | Law | Lean | Rust |
//! |---|---|---|
//! | the simple root's eigen-derivative, `D log|μ|[ΔM] = Re(ℓᵀΔMr/(μℓᵀr))` | `HNN/ExecutedComparison.{simple_root_deriv, log_modulus_deriv}` | `hnn::ring::ReceivingBank::read_turn_covector` |
//! | the monodromy's variation, `ΔM = Σ_t T_(>t) ΔT_t T_(<t)` | `HNN/ExecutedComparison.product_deriv` | `hnn::ring::ReceivingBank::turn_variation` |
//! | a max comparison descends where every active branch descends, and a sum of maxes where its active slopes sum below zero | `HNN/ExecutedComparison.{max_descends, sum_max_descends}` | [`executed_move`]'s first-order certificate (the hinge) |
//! | a strict decrease certified by disjoint enclosures | `HNN/ExecutedComparison.disjoint_enclosures_decrease` | [`executed_move`]'s condition of adoption |
//! | the release's predicates, class and threshold, sufficient for order and section | `HNN/ExecutedComparison.predicates_release_the_section` | [`BatchComparison`] |
//! | the hinge's zero set is the closed predicate set | `HNN/ExecutedComparison.{hinge_zero_iff, hinge_zero_at_tie, hinge_right_leaves}` | [`Composition::Hinge`] |
//! | the lock face, its solved level and the rational test | `HNN/ExecutedComparison.{lockFace_pos, lockFace_lt_log_two_iff, lockFace_enclosure_sublevel, class_top_is_target}` | [`lock_face`] |
//! | its covector `θ − q` and its first-order certificate over the members | `HNN/ExecutedComparison.{lockFace_covector, lockFace_first_order, sum_upper_dini_descends}` | [`executed_move`]'s proposal and certificate (the lock face) |
//! | decisions read along the key-consistent prefix release the section | `HNN/ExecutedComparison.decisions_release_the_section` | [`Reading::Decisions`] |
//! | the modulus's least-squares step | `HNN/ExecutedComparison.modulus_least_squares` | [`executed_move`]'s modulus |
//! | the excess's piecewise directional derivative; the chord against the line | owed (#62) | [`ladder_start`], [`FirstOrderReading::excess`] |
//! | loop 1c's representation readings: each decision term's lock face pulled back to `E` and `ρ`, and the comparison re-read on frozen sites (a search's readings, never a move) | `HNN/ExecutedComparison.lockFace_covector`; the pullback's joined statement owed (#62) | [`site_gradients`], [`frozen_reread`] |
//! | the restore law as a standing law (the continuing state's consumer) | `HNN/ExecutedComparison.{restoreStanding, restored_continuation_agrees, equal_states_agree}` | `hnn::constitution::{ContinuingState, Constitution::continued}` |

use std::collections::BTreeMap;
use std::sync::OnceLock;

use num_bigint::BigInt;
use num_traits::{One, Signed, Zero};

use crate::hnn::HnnError;
use crate::hnn::constitution::{Constitution, Sample, SourceStep};
use crate::hnn::field::{ConstitutionRead, Current, Field};
use crate::hnn::moment::SourceMoment;
use crate::hnn::prediction::{
    BankGeneration, BankPlacement, BankRefinement, JointGrowth, Refinement, bank_release,
};
use crate::hnn::ring::{
    CovectorRefusal, Growth, MemberCovector, ReceivingBank, TurnCovector, TurnReading, turn,
};
use crate::holon::deposition::significant;
use crate::ratio::GaussianRat;
use crate::ratio::Rat;
use crate::ratio::algebraic::{ExactInterval, ln_enclosure};
use crate::ratio::linear::ExactRatMatrix;
use crate::ratio::linear::inertia::{SymmetricForm, inertia};

/// [definition; agent-inferred, September 30] **The entry bound** `2³`: every entry of `E` at most
/// three binary orders above the founding's unit scale (the certified step's pins, acceptance 1;
/// every development read stayed below 2, the divergence it excludes passed 316). A condition of
/// adoption here, never a tally.
pub fn entry_bound() -> Rat {
    Rat::from_integer(BigInt::from(8))
}

/// The entry bound's binary exponent (the bound is `2^ENTRY_BOUND`).
pub const ENTRY_BOUND: u32 = 3;

/// [definition; agent-inferred] **The covector's dyadic face**: each proposal covector entry at
/// 64 significant bits toward zero, so the returns' denominators stay powers of two. The proposal
/// is certified on the successor, so its rounding needs no charge.
const FACE_BITS: u32 = 64;

/// [definition; agent-inferred, September 30] **A predicate's exact reading** on enclosures.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Predicate {
    Holds,
    Fails,
    Undecided,
}

/// [definition; agent-inferred, September 30] **A request's context of comparison**: the machine's
/// own open-section trajectory (its refinements read by the declared [`Reading`]), or a partition
/// of its stations with the locked stations' targets placed (the readout's `mask`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Context {
    Open,
    Partition(Vec<bool>),
}

/// [definition; agent-inferred, September 30] **One request**: its ingested current and moment, its
/// targets (the terrain's truth; only the comparison reads them), and its context. A comparison
/// reads several requests together, as co-present regions of one constitution.
#[derive(Clone, Debug)]
pub struct Request {
    pub current: Current,
    pub moment: SourceMoment,
    pub targets: Vec<usize>,
    pub context: Context,
}

/// [definition; agent-inferred, September 30; step 1b's pin §2] **The declared composition**
/// (module header, "The two compositions").
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Composition {
    /// 1a's hinge `F = Σ (f)_+`; its solved level is zero.
    Hinge,
    /// Step 1b's lock face `L = Σ ℓ`, `ℓ = log(Π/a_t)`; its solved level `log 2`.
    LockFace,
    /// The lock face joined by each request's order term at its decision refinement ([`OrderTerm`];
    /// the [order's pin](../../../../research/records/2026-10-01_THE_ORDER_AS_A_TERM_OF_THE_COMPARISON_PINNED_BEFORE_ITS_RUN.md)):
    /// the release's first lock read as a lock over the stations. Its solved level `log 2`.
    LockOrder,
}

/// [definition; agent-inferred, September 30; step 1b's pin §2.4, §13.1] **Where a composition
/// reads its terms** on an open context (module header, "The readings").
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Reading {
    /// Every open station of every refinement the release executes (1a's reading).
    Every,
    /// Each station once, at its decision `d(j)` along the key-consistent prefix.
    Decisions,
    /// Each station once, at the section with every earlier station at its target (a diagnostic).
    TeacherForced,
    /// Every open station of every refinement of the forced release (`prediction::bank_release_forced`:
    /// the release's own lock order, each lock placed at its target): every decision the release
    /// faces along the right trajectory, each in its own context (the
    /// [forced release's record](../../../../research/records/2026-10-01_THE_FORCED_RELEASE.md)).
    Forced,
    /// Each station once, at the forced release's refinement that locks it (every earlier lock at
    /// its target), the order read at the first refinement: the forced release's decisions at the
    /// decisions' cost (its every-refinement covectors exceeded a move's measured bound).
    ForcedDecisions,
}

/// [definition; agent-inferred, September 30] **A declared comparison**: its composition and its
/// reading. Every arm of step 1b's gate B is one: the lock face at the decisions (the candidate),
/// the lock face at every refinement, the hinge at the decisions, the hinge at every refinement (1a's
/// law), and the lock face teacher-forced left to right (the diagnostic).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Comparison {
    pub composition: Composition,
    pub reading: Reading,
}

impl Comparison {
    /// 1a's law: the hinge at every refinement.
    pub const HINGE_EVERY: Self = Self {
        composition: Composition::Hinge,
        reading: Reading::Every,
    };
    /// Step 1b's candidate: the lock face at the decisions.
    pub const LOCK_DECISIONS: Self = Self {
        composition: Composition::LockFace,
        reading: Reading::Decisions,
    };
}

/// [definition; agent-inferred, September 30] **One open station's comparison in one section**: the
/// refinement of the machine's own trajectory it was read in (`None` for a section the release did
/// not execute: a partition, a teacher-forced section), its station, target and top class; the class
/// and threshold predicates and the hinge's term `f` enclosed; the lock face `ℓ` enclosed, its
/// rational solved predicate and the target's share `θ_t` enclosed; the target's rank among every
/// candidate by lower end (0 the top), its rank among the candidates other than the termination
/// (`None` when the target is the termination) and the termination's rank; and the target's and
/// the leading rival's joint enclosures.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StationComparison {
    pub context: Option<usize>,
    pub station: usize,
    pub target: usize,
    pub top: usize,
    pub class: Predicate,
    pub threshold: Predicate,
    pub value: ExactInterval,
    pub lock: ExactInterval,
    pub solved: Predicate,
    pub share: ExactInterval,
    pub rank: usize,
    pub symbol_rank: Option<usize>,
    pub termination_rank: usize,
    pub target_growth: Growth,
    pub rival_growth: Growth,
}

/// [definition; agent-inferred, September 30] **One refinement's order** (the machine's own
/// trajectory): each eligible station with its top class, gap and whether its top is its target;
/// the stations it locked; and whether that lock was safe (`None` when nothing was eligible: the
/// release held).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OrderReading {
    pub context: usize,
    pub eligible: Vec<(usize, usize, Rat, bool)>,
    pub locked: Vec<usize>,
    pub safe: Option<bool>,
}

/// [definition; agent-inferred, September 30] **Where a term lies against its solved level**
/// (module header, "The two compositions").
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Excess {
    /// Certainly in the solved level (the hinge `f⁺ < 0`; the lock face's rational test).
    Solved,
    /// Neither certainly solved nor certainly past the level (`ℓ = ln 2` exactly included).
    Boundary,
    /// Certainly past the level (`f⁻ > 0`; `1 + Σ_(x≠t) L_x > U_t`).
    Above,
}

/// [definition; agent-inferred, September 30] **A term's site**: the request, the station, the
/// section it is read at (the station open; the fixed mask's entry), the refinement of the machine's
/// own trajectory that section is (`None` when the release did not execute it), whether the section
/// holds a cell that is not its target (post-error), and whether the station was read at a
/// refinement that did not lock it (held).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TermSite {
    pub request: usize,
    pub station: usize,
    pub cells: Vec<Option<usize>>,
    pub context: Option<usize>,
    pub post_error: bool,
    pub held: bool,
}

/// [definition; agent-inferred, September 30] **One term of the declared reading**: its site, the
/// station's comparison there, the composition's term enclosed (the hinge's `(f)_+`, the lock face's
/// `ℓ`), its excess over the solved level enclosed and where it lies against the level.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TermReading {
    pub site: TermSite,
    pub comparison: StationComparison,
    pub value: ExactInterval,
    pub excess: ExactInterval,
    pub kind: Excess,
}

/// [definition; agent-inferred, September 30] **A request's comparison**: its release from the open
/// section (on an open context), every open station's comparison at every refinement it executed
/// (receipts), every refinement's order, the declared reading's terms, `r*` (the last refinement
/// whose placed cells equal their targets, on an open context), and the composition and its excess
/// summed over the terms, enclosed.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RequestComparison {
    pub generation: Option<BankGeneration>,
    pub stations: Vec<StationComparison>,
    pub orders: Vec<OrderReading>,
    pub terms: Vec<TermReading>,
    /// The order terms ([`Composition::LockOrder`] only): at the decisions, one at the decision
    /// refinement; at every refinement, one at each refinement the release executed. A refinement
    /// where no eligible station's top is its target has none.
    pub order_terms: Vec<OrderTerm>,
    pub consistent: Option<usize>,
    pub value: ExactInterval,
    pub excess: ExactInterval,
    pub readings: usize,
}

/// [definition; agent-inferred, September 30; the pin §13.1] **The counts of a reading's terms**:
/// the station obligations (`m` a request), the terms attempted, the obligations covered by a term
/// and those absent, the terms read after an error in their section, the terms held (read at a
/// refinement that did not lock their station), the terms in the composition's support (the hinge's
/// terms not certainly solved; every lock-face term), the terms solved, at the boundary and above
/// their level.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct TermCounts {
    pub obligations: usize,
    pub attempted: usize,
    pub coverage: usize,
    pub absent: usize,
    pub post_error: usize,
    pub held: usize,
    pub support: usize,
    pub solved: usize,
    pub boundary: usize,
    pub above: usize,
}

/// [definition; agent-inferred, September 30] **The comparison of requests read together** at one
/// constitution: its declared comparison, each request's, and the composition and its excess
/// enclosed.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BatchComparison {
    pub comparison: Comparison,
    pub requests: Vec<RequestComparison>,
    pub value: ExactInterval,
    pub excess: ExactInterval,
    pub readings: usize,
}

impl BatchComparison {
    /// The stations whose class and threshold both hold, of those compared at every refinement.
    pub fn holding(&self) -> (usize, usize) {
        let stations = self.requests.iter().flat_map(|r| &r.stations);
        let (mut holds, mut all) = (0, 0);
        for station in stations {
            all += 1;
            holds += usize::from(
                station.class == Predicate::Holds && station.threshold == Predicate::Holds,
            );
        }
        (holds, all)
    }

    /// Whole sections released equal to their targets, of the open contexts, and the stations
    /// right of their released classes.
    pub fn sections(&self, targets: &[Vec<usize>]) -> (usize, usize, usize) {
        let (mut whole, mut right, mut released) = (0, 0, 0);
        for (request, target) in self.requests.iter().zip(targets) {
            let Some(generation) = &request.generation else {
                continue;
            };
            if generation.release.released() {
                released += 1;
                let hits = generation
                    .release
                    .classes
                    .iter()
                    .zip(target)
                    .filter(|(a, b)| a == b)
                    .count();
                right += hits;
                whole += usize::from(hits == target.len());
            }
        }
        (whole, right, released)
    }

    /// **The counts of the declared reading's terms** ([`TermCounts`]) over `stations` obligations
    /// a request.
    pub fn counts(&self, stations: usize) -> TermCounts {
        let mut counts = TermCounts {
            obligations: stations * self.requests.len(),
            ..TermCounts::default()
        };
        for request in &self.requests {
            let mut covered = vec![false; stations];
            for term in &request.terms {
                counts.attempted += 1;
                if let Some(slot) = covered.get_mut(term.site.station) {
                    *slot = true;
                }
                counts.post_error += usize::from(term.site.post_error);
                counts.held += usize::from(term.site.held);
                counts.support += usize::from(in_support(self.comparison.composition, term.kind));
                match term.kind {
                    Excess::Solved => counts.solved += 1,
                    Excess::Boundary => counts.boundary += 1,
                    Excess::Above => counts.above += 1,
                }
            }
            let covering = covered.iter().filter(|c| **c).count();
            counts.coverage += covering;
            counts.absent += stations - covering;
        }
        counts
    }
}

/// Whether a term is in its composition's support (it moves the composition): every lock-face term
/// (the face has no zero), the hinge's terms not certainly solved.
fn in_support(composition: Composition, kind: Excess) -> bool {
    match composition {
        Composition::LockFace | Composition::LockOrder => true,
        Composition::Hinge => kind != Excess::Solved,
    }
}

// -------------------------------------------------------------------------------------------
// enclosures

fn nought() -> ExactInterval {
    ExactInterval::point(Rat::zero())
}

fn plus(a: &ExactInterval, b: &ExactInterval) -> ExactInterval {
    ExactInterval {
        lower: &a.lower + &b.lower,
        upper: &a.upper + &b.upper,
    }
}

/// The product of two enclosures: its four corners' least and largest.
fn product(a: &ExactInterval, b: &ExactInterval) -> ExactInterval {
    let corners = [
        &a.lower * &b.lower,
        &a.lower * &b.upper,
        &a.upper * &b.lower,
        &a.upper * &b.upper,
    ];
    ExactInterval {
        lower: corners.iter().min().expect("a corner").clone(),
        upper: corners.iter().max().expect("a corner").clone(),
    }
}

/// The positive part of an enclosure.
fn positive_part(value: &ExactInterval) -> ExactInterval {
    ExactInterval {
        lower: value.lower.clone().max(Rat::zero()),
        upper: value.upper.clone().max(Rat::zero()),
    }
}

/// `ln 2` enclosed on the declared grid, formed once.
pub(crate) fn ln_two() -> Result<ExactInterval, HnnError> {
    static LN_TWO: OnceLock<ExactInterval> = OnceLock::new();
    if let Some(value) = LN_TWO.get() {
        return Ok(value.clone());
    }
    let value = ln_enclosure(&Rat::from_integer(BigInt::from(2)))?;
    Ok(LN_TWO.get_or_init(|| value).clone())
}

fn ln_of(growth: &Growth) -> Result<ExactInterval, HnnError> {
    if !growth.lower.is_positive() {
        // A zero lower end keeps its fibre: the reading is below every positive value.
        return Err(HnnError::NonpositiveDeclaration);
    }
    let lower = ln_enclosure(&growth.lower)?;
    let upper = ln_enclosure(&growth.upper)?;
    Ok(ExactInterval {
        lower: lower.lower,
        upper: upper.upper,
    })
}

// -------------------------------------------------------------------------------------------
// the station's comparisons

/// [definition; agent-inferred, September 30] **A branch of the hinge's max comparison** (module
/// header): a rival class `x` against the target (`Some(x)`), or the threshold (`None`).
pub type Branch = Option<usize>;

/// One station's hinge term read on enclosures: its value, predicates, top and the branches that
/// may attain it.
struct Term {
    value: ExactInterval,
    class: Predicate,
    threshold: Predicate,
    top: usize,
    branches: Vec<Branch>,
    leading: Branch,
    /// The class branch of the largest midpoint (the rival the class comparison reads first).
    rival: usize,
}

/// A station's hinge term from its candidates' joint enclosures (module header, "The two
/// compositions").
fn station_term(joints: &[&Growth], target: usize) -> Result<Term, HnnError> {
    let logs: Vec<ExactInterval> = joints
        .iter()
        .map(|growth| ln_of(growth))
        .collect::<Result<_, _>>()?;
    let t = &logs[target];
    let mut parts: Vec<(Branch, ExactInterval)> = Vec::new();
    for (x, log) in logs.iter().enumerate() {
        if x != target {
            parts.push((
                Some(x),
                ExactInterval {
                    lower: &log.lower - &t.upper,
                    upper: &log.upper - &t.lower,
                },
            ));
        }
    }
    parts.push((
        None,
        ExactInterval {
            lower: -t.upper.clone(),
            upper: -t.lower.clone(),
        },
    ));
    let lower = parts
        .iter()
        .map(|(_, part)| part.lower.clone())
        .max()
        .expect("a part");
    let upper = parts
        .iter()
        .map(|(_, part)| part.upper.clone())
        .max()
        .expect("a part");
    let branches: Vec<Branch> = parts
        .iter()
        .filter(|(_, part)| part.upper >= lower)
        .map(|(branch, _)| *branch)
        .collect();
    let leading = parts
        .iter()
        .max_by(|a, b| (&a.1.lower + &a.1.upper).cmp(&(&b.1.lower + &b.1.upper)))
        .map(|(branch, _)| *branch)
        .expect("a part");
    let rival = parts
        .iter()
        .filter_map(|(branch, part)| branch.map(|x| (x, part)))
        .max_by(|a, b| (&a.1.lower + &a.1.upper).cmp(&(&b.1.lower + &b.1.upper)))
        .map(|(x, _)| x)
        .expect("a rival");
    let target_growth = joints[target];
    let class = if (0..joints.len())
        .filter(|&x| x != target)
        .all(|x| target_growth.exceeds(joints[x]))
    {
        Predicate::Holds
    } else if (0..joints.len())
        .filter(|&x| x != target)
        .any(|x| joints[x].lower >= target_growth.upper)
    {
        Predicate::Fails
    } else {
        Predicate::Undecided
    };
    let threshold = if target_growth.is_locked() {
        Predicate::Holds
    } else if target_growth.upper <= Rat::one() {
        Predicate::Fails
    } else {
        Predicate::Undecided
    };
    let top = (0..joints.len())
        .max_by(|&a, &b| joints[a].lower.cmp(&joints[b].lower).then(b.cmp(&a)))
        .expect("a class");
    Ok(Term {
        value: ExactInterval { lower, upper },
        class,
        threshold,
        top,
        branches,
        leading,
        rival,
    })
}

/// **A station's comparison from its candidates' joint enclosures** (the owner's predicate test):
/// the term `f` enclosed, the class predicate and the threshold predicate.
#[cfg(test)]
pub(crate) fn station_predicates(
    joints: &[Growth],
    target: usize,
) -> Result<(ExactInterval, Predicate, Predicate), HnnError> {
    let joints: Vec<&Growth> = joints.iter().collect();
    let term = station_term(&joints, target)?;
    Ok((term.value, term.class, term.threshold))
}

/// [definition; agent-inferred, September 30; step 1b's pin §2.2–§2.5, §13.2, §13.5] **A station's
/// lock face on its candidates' exact enclosures** ([`lock_face`]): `ℓ = log(Π/a_t)` enclosed; the
/// rational solved predicate (`1 + Σ_(x≠t) U_x < L_t` holds; `1 + Σ_(x≠t) L_x ≥ U_t` fails;
/// else undecided); whether `ℓ > ln 2` is certain (`1 + Σ_(x≠t) L_x > U_t`); every sheet's share
/// `θ_x` enclosed; the excess `(ℓ − ln 2)_+` enclosed, exactly zero where the solved test holds; and
/// **the lock's one normalized reading** (`sheets`, October 1; Astra's review): the resting sheet and
/// every candidate at one common representative of the readings, each joint enclosure's dyadic face,
/// `(1, a_0, …)/Π` with `Π = 1 + Σ a_x` ([`lock_sheets`]). The enclosures stay enclosures (the
/// certificate's bounds read them); every consumer of a categorical state (the descent covector's
/// weights `θ_x − [x = t]`, the witness's form) reads `sheets`, so they describe one receiver.
/// Each common share lies in its enclosure, which holds every representative ([`LockFace::within`]).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LockFace {
    pub value: ExactInterval,
    pub solved: Predicate,
    pub above: bool,
    pub shares: Vec<ExactInterval>,
    pub excess: ExactInterval,
    pub sheets: Vec<Rat>,
}

impl LockFace {
    /// The explicit residual of the common representative: every candidate's common share
    /// `sheets[x + 1]` lies in its share's enclosure.
    pub fn within(&self) -> bool {
        self.shares
            .iter()
            .zip(&self.sheets[1..])
            .all(|(share, theta)| share.lower <= *theta && *theta <= share.upper)
    }

    /// The descent covector's weight on candidate `x` of a term with target `t`, `θ_x − [x = t]`, at
    /// the lock's one normalized reading.
    pub fn weight(&self, x: usize, target: usize) -> Rat {
        let theta = self.sheets[x + 1].clone();
        if x == target { theta - Rat::one() } else { theta }
    }

    /// Where the term lies against the solved level: the rational test is authoritative.
    pub fn kind(&self) -> Excess {
        if self.solved == Predicate::Holds {
            Excess::Solved
        } else if self.above {
            Excess::Above
        } else {
            Excess::Boundary
        }
    }
}

/// **A station's lock face** ([`LockFace`]) on its candidates' joint enclosures and its target.
/// Refused, typed, for a target outside the candidates (`HnnError::Shape`), for an enclosure with a
/// negative or reversed end, and for a target whose lower end is not positive
/// (`HnnError::NonpositiveDeclaration`: `ℓ` has no finite upper end there; the station is never
/// solved by it, and no step divides by it).
pub fn lock_face(joints: &[Growth], target: usize) -> Result<LockFace, HnnError> {
    let joints: Vec<&Growth> = joints.iter().collect();
    lock_face_of(&joints, target)
}

fn lock_face_of(joints: &[&Growth], target: usize) -> Result<LockFace, HnnError> {
    if target >= joints.len() {
        return Err(HnnError::Shape {
            what: "a lock face's target among its candidates",
            expected: joints.len(),
            found: target,
        });
    }
    if joints
        .iter()
        .any(|g| g.lower.is_negative() || g.lower > g.upper)
    {
        return Err(HnnError::NonpositiveDeclaration);
    }
    let t = joints[target];
    if !t.lower.is_positive() {
        return Err(HnnError::NonpositiveDeclaration);
    }
    let one = Rat::one();
    let (mut rest_low, mut rest_high) = (one.clone(), one.clone());
    let (mut all_low, mut all_high) = (Rat::zero(), Rat::zero());
    for (x, g) in joints.iter().enumerate() {
        all_low += &g.lower;
        all_high += &g.upper;
        if x != target {
            rest_low += &g.lower;
            rest_high += &g.upper;
        }
    }
    let value = ExactInterval {
        lower: ln_enclosure(&(&one + &rest_low / &t.upper))?.lower,
        upper: ln_enclosure(&(&one + &rest_high / &t.lower))?.upper,
    };
    let solved = if rest_high < t.lower {
        Predicate::Holds
    } else if rest_low >= t.upper {
        Predicate::Fails
    } else {
        Predicate::Undecided
    };
    let above = rest_low > t.upper;
    let shares = joints
        .iter()
        .map(|g| ExactInterval {
            lower: &g.lower / (&one + &all_high - &g.upper + &g.lower),
            upper: &g.upper / (&one + &all_low - &g.lower + &g.upper),
        })
        .collect();
    let ln2 = ln_two()?;
    let excess = if solved == Predicate::Holds {
        nought()
    } else if above {
        ExactInterval {
            lower: (&value.lower - &ln2.upper).max(Rat::zero()),
            upper: &value.upper - &ln2.lower,
        }
    } else {
        ExactInterval {
            lower: Rat::zero(),
            upper: (&value.upper - &ln2.lower).max(Rat::zero()),
        }
    };
    let readings: Vec<Rat> = joints
        .iter()
        .map(|g| {
            face(&ExactInterval {
                lower: g.lower.clone(),
                upper: g.upper.clone(),
            })
        })
        .collect();
    let sheets = lock_sheets(&readings).ok_or(HnnError::NonpositiveDeclaration)?;
    Ok(LockFace {
        value,
        solved,
        above,
        shares,
        excess,
        sheets,
    })
}

/// One station's comparison ([`StationComparison`]) with its hinge term and its lock face.
fn station_comparison(
    joints: &[&Growth],
    target: usize,
    station: usize,
    context: Option<usize>,
    termination: usize,
) -> Result<(StationComparison, Term, LockFace), HnnError> {
    let term = station_term(joints, target)?;
    let lock = lock_face_of(joints, target)?;
    let rival = (0..joints.len())
        .filter(|&x| x != target)
        .max_by(|&a, &b| joints[a].upper.cmp(&joints[b].upper))
        .expect("a rival");
    let rank_of = |class: usize, among: &dyn Fn(usize) -> bool| {
        (0..joints.len())
            .filter(|&x| among(x) && joints[x].lower > joints[class].lower)
            .count()
    };
    let every = |_: usize| true;
    let symbols = |x: usize| x != termination;
    let comparison = StationComparison {
        context,
        station,
        target,
        top: term.top,
        class: term.class,
        threshold: term.threshold,
        value: term.value.clone(),
        lock: lock.value.clone(),
        solved: lock.solved,
        share: lock.shares[target].clone(),
        rank: rank_of(target, &every),
        symbol_rank: (target != termination).then(|| rank_of(target, &symbols)),
        termination_rank: if termination < joints.len() {
            rank_of(termination, &every)
        } else {
            joints.len()
        },
        target_growth: joints[target].clone(),
        rival_growth: joints[rival].clone(),
    };
    Ok((comparison, term, lock))
}

/// A term of the declared composition from its station's comparison and lock face.
fn term_reading(
    composition: Composition,
    site: TermSite,
    comparison: StationComparison,
    lock: &LockFace,
) -> TermReading {
    let (value, excess, kind) = match composition {
        Composition::Hinge => {
            let part = positive_part(&comparison.value);
            let kind = if comparison.value.lower.is_positive() {
                Excess::Above
            } else if comparison.value.upper.is_negative() {
                Excess::Solved
            } else {
                Excess::Boundary
            };
            (part.clone(), part, kind)
        }
        Composition::LockFace | Composition::LockOrder => {
            (lock.value.clone(), lock.excess.clone(), lock.kind())
        }
    };
    TermReading {
        site,
        comparison,
        value,
        excess,
        kind,
    }
}

// -------------------------------------------------------------------------------------------
// the readings

/// Validate a request's declared input: one target per station, each a class of the chart; a
/// partition's mask one flag per station.
fn validate(requests: &[Request], stations: usize, alphabet: usize) -> Result<(), HnnError> {
    for request in requests {
        if request.targets.len() != stations {
            return Err(HnnError::Shape {
                what: "a request's targets (one per station)",
                expected: stations,
                found: request.targets.len(),
            });
        }
        if let Some(&code) = request.targets.iter().find(|&&t| t >= alphabet) {
            return Err(HnnError::CellOutside { code, alphabet });
        }
        if let Context::Partition(locked) = &request.context
            && locked.len() != stations
        {
            return Err(HnnError::Shape {
                what: "a partition's mask (one flag per station)",
                expected: stations,
                found: locked.len(),
            });
        }
    }
    Ok(())
}

/// A request's release from the open section (every refinement kept), or its partition's one
/// refinement, each candidate read by `read`.
/// The refinements a declared reading's sites are read on: the forced release's
/// (`prediction::bank_release_forced`, with its readings made) for [`Reading::Forced`] on an open
/// context, else the release's own.
#[allow(clippy::too_many_arguments)]
fn sites_refinements<R: JointGrowth + Send + Sync>(
    placement: &BankPlacement,
    request: &Request,
    declared: &Refinement,
    alphabet: usize,
    bank: &ReceivingBank,
    grain: u32,
    read: &(impl Fn(&[GaussianRat]) -> Result<R, HnnError> + Sync),
    reading: Reading,
    refinements: Vec<BankRefinement<R>>,
) -> Result<(Vec<BankRefinement<R>>, usize), HnnError> {
    if !matches!(reading, Reading::Forced | Reading::ForcedDecisions)
        || !matches!(request.context, Context::Open)
    {
        return Ok((refinements, 0));
    }
    let (_, forced) = crate::hnn::prediction::bank_release_forced(
        placement,
        declared,
        alphabet,
        bank,
        grain,
        read,
        &request.targets,
    )?;
    let made = forced.iter().map(|r| r.read.len()).sum();
    Ok((forced, made))
}

fn release_of<R: JointGrowth + Send + Sync>(
    placement: &BankPlacement,
    request: &Request,
    declared: &Refinement,
    alphabet: usize,
    bank: &ReceivingBank,
    grain: u32,
    read: &(impl Fn(&[GaussianRat]) -> Result<R, HnnError> + Sync),
) -> Result<(Option<BankGeneration>, Vec<BankRefinement<R>>), HnnError> {
    use rayon::prelude::*;
    match &request.context {
        Context::Open => {
            let (generation, refinements) =
                bank_release(placement, declared, alphabet, bank, grain, read, true)?;
            Ok((Some(generation), refinements))
        }
        Context::Partition(locked) => {
            let stations = declared.stations();
            let placed: Vec<Option<usize>> = (0..stations)
                .map(|j| locked[j].then_some(request.targets[j]))
                .collect();
            let open: Vec<(usize, usize)> = (0..stations)
                .filter(|&j| !locked[j])
                .flat_map(|j| (0..alphabet).map(move |x| (j, x)))
                .collect();
            let reads: Vec<R> = open
                .par_iter()
                .map(|&(station, class)| {
                    let mut cells = placed.clone();
                    cells[station] = Some(class);
                    read(&turn(&placement.storage(station, &cells)))
                })
                .collect::<Result<_, HnnError>>()?;
            Ok((
                None,
                vec![BankRefinement {
                    placed,
                    open,
                    read: reads,
                    tops: Vec::new(),
                    eligible: Vec::new(),
                    locked: Vec::new(),
                }],
            ))
        }
    }
}

/// The release's receipts: every open station's comparison at every refinement (with its lock face),
/// and every refinement's order on an open context.
#[allow(clippy::type_complexity)]
fn receipts<R: JointGrowth>(
    request: &Request,
    refinements: &[BankRefinement<R>],
    alphabet: usize,
    termination: usize,
) -> Result<(Vec<StationComparison>, Vec<OrderReading>), HnnError> {
    let open_context = matches!(request.context, Context::Open);
    let mut stations = Vec::new();
    let mut orders = Vec::new();
    for (index, refinement) in refinements.iter().enumerate() {
        let context = open_context.then_some(index);
        for (chunk_index, chunk) in refinement.read.chunks(alphabet).enumerate() {
            let station = refinement.open[chunk_index * alphabet].0;
            let joints: Vec<&Growth> = chunk.iter().map(JointGrowth::joint).collect();
            let (comparison, _, _) = station_comparison(
                &joints,
                request.targets[station],
                station,
                context,
                termination,
            )?;
            stations.push(comparison);
        }
        if open_context {
            let eligible = refinement
                .eligible
                .iter()
                .map(|(station, top, gap)| {
                    (*station, *top, gap.clone(), *top == request.targets[*station])
                })
                .collect();
            let safe = (!refinement.locked.is_empty()).then(|| {
                refinement.locked.iter().all(|&station| {
                    refinement
                        .tops
                        .iter()
                        .any(|&(s, top)| s == station && top == request.targets[station])
                })
            });
            orders.push(OrderReading {
                context: index,
                eligible,
                locked: refinement.locked.clone(),
                safe,
            });
        }
    }
    Ok((stations, orders))
}

/// Whether a section's placed cells all equal their targets.
fn consistent_section(placed: &[Option<usize>], targets: &[usize]) -> bool {
    placed
        .iter()
        .zip(targets)
        .all(|(cell, target)| cell.is_none_or(|c| c == *target))
}

/// [definition; agent-inferred, September 30; step 1b's pin §2.4, §13.1] **The declared reading's
/// sites of one request** from its refinements (module header, "The readings"), with `r*` on an open
/// context. A pure function of the refinements' sections, locks and open stations: a release, a
/// hold and a refused certificate are read by one rule, and on an open context every station has
/// exactly one site under the decisions and the teacher-forced readings. Public for loop 1c's
/// readings of a release under a declared order (`prediction::bank_release_ordered`), which read
/// their decision sites by this one rule.
pub fn sites_of<R>(
    index: usize,
    request: &Request,
    refinements: &[BankRefinement<R>],
    reading: Reading,
    stations: usize,
    alphabet: usize,
) -> (Vec<TermSite>, Option<usize>) {
    let open_stations = |refinement: &BankRefinement<R>| -> Vec<usize> {
        refinement
            .open
            .chunks(alphabet)
            .map(|chunk| chunk[0].0)
            .collect()
    };
    let site = |k: Option<usize>, station: usize, cells: Vec<Option<usize>>| {
        let post_error = !consistent_section(&cells, &request.targets);
        let held = k.is_none_or(|k| !refinements[k].locked.contains(&station));
        TermSite {
            request: index,
            station,
            cells,
            context: k,
            post_error,
            held,
        }
    };
    if !matches!(request.context, Context::Open) {
        let sites = refinements
            .first()
            .map(|refinement| {
                open_stations(refinement)
                    .into_iter()
                    .map(|station| {
                        let mut s = site(None, station, refinement.placed.clone());
                        s.held = false;
                        s
                    })
                    .collect()
            })
            .unwrap_or_default();
        return (sites, None);
    }
    // `r*`: the placed sections only grow, so the consistent refinements are a prefix.
    let consistent = refinements
        .iter()
        .rposition(|refinement| consistent_section(&refinement.placed, &request.targets));
    let sites = match reading {
        Reading::Every | Reading::Forced => refinements
            .iter()
            .enumerate()
            .flat_map(|(k, refinement)| {
                open_stations(refinement)
                    .into_iter()
                    .map(move |station| (k, station, refinement.placed.clone()))
            })
            .map(|(k, station, cells)| site(Some(k), station, cells))
            .collect(),
        Reading::Decisions => {
            let Some(last) = consistent else {
                return (Vec::new(), None);
            };
            (0..stations)
                .map(|station| {
                    let locked_at = refinements
                        .iter()
                        .position(|refinement| refinement.locked.contains(&station));
                    let k = match locked_at {
                        Some(k) if k < last => k,
                        _ => last,
                    };
                    site(Some(k), station, refinements[k].placed.clone())
                })
                .collect()
        }
        Reading::ForcedDecisions if refinements.is_empty() => Vec::new(),
        Reading::ForcedDecisions => (0..stations)
            .map(|station| {
                let k = refinements
                    .iter()
                    .position(|refinement| refinement.locked.contains(&station))
                    .unwrap_or(refinements.len().saturating_sub(1));
                site(Some(k), station, refinements[k].placed.clone())
            })
            .collect(),
        Reading::TeacherForced => (0..stations)
            .map(|station| {
                let cells: Vec<Option<usize>> = (0..stations)
                    .map(|i| (i < station).then_some(request.targets[i]))
                    .collect();
                let k = refinements
                    .iter()
                    .position(|refinement| refinement.placed == cells);
                site(k, station, cells)
            })
            .collect(),
    };
    (sites, consistent)
}

/// Every site's candidates' readings: from the refinement that executed its section, else read at
/// the site's section (the station's candidates placed in turn); with the readings made afresh.
fn site_reads<R: JointGrowth + Clone + Send + Sync>(
    sites: &[TermSite],
    refinements: &[BankRefinement<R>],
    placement: &BankPlacement,
    alphabet: usize,
    read: &(impl Fn(&[GaussianRat]) -> Result<R, HnnError> + Sync),
) -> Result<(Vec<Vec<R>>, usize), HnnError> {
    use rayon::prelude::*;
    let found = |site: &TermSite| -> Option<Vec<R>> {
        let refinement = refinements.iter().find(|r| r.placed == site.cells)?;
        let at = refinement
            .open
            .iter()
            .position(|&(station, class)| station == site.station && class == 0)?;
        Some(refinement.read[at..at + alphabet].to_vec())
    };
    let known: Vec<Option<Vec<R>>> = sites.iter().map(found).collect();
    let fresh: Vec<(usize, usize)> = known
        .iter()
        .enumerate()
        .filter(|(_, k)| k.is_none())
        .flat_map(|(s, _)| (0..alphabet).map(move |x| (s, x)))
        .collect();
    let reads: Vec<R> = fresh
        .par_iter()
        .map(|&(s, class)| {
            let mut cells = sites[s].cells.clone();
            cells[sites[s].station] = Some(class);
            read(&turn(&placement.storage(sites[s].station, &cells)))
        })
        .collect::<Result<_, HnnError>>()?;
    let made = reads.len();
    let mut reads = reads.into_iter();
    Ok((
        known
            .into_iter()
            .map(|k| match k {
                Some(read) => read,
                None => reads.by_ref().take(alphabet).collect(),
            })
            .collect(),
        made,
    ))
}

/// The declared composition's terms at their sites, and their sums.
/// [definition; agent-inferred, October 1; the
/// [order's pin](../../../../research/records/2026-10-01_THE_ORDER_AS_A_TERM_OF_THE_COMPARISON_PINNED_BEFORE_ITS_RUN.md)]
/// **One sheet of the order's lock**: a station eligible at the decision refinement (its top flips
/// past every other candidate and locks), its term's index among the sites, its top and runner
/// classes, its release gap `g` (the top's `lower` less the runner's `upper`, exactly the quantity
/// the release compares), its share `θ = g/Σ_S g` and its covector weight `θ − [x = r]`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OrderSheet {
    pub site: usize,
    pub station: usize,
    pub top: usize,
    pub runner: usize,
    pub gap: Rat,
    pub share: Rat,
    pub weight: Rat,
}

/// [definition; agent-inferred, October 1] **The order term** (the pin above): at a request's
/// decision refinement `r*` (the latest refinement its decision terms are read at), the eligible
/// stations `E` with their release gaps, the right ones `R` (top = target), `r = argmax_R g` (the
/// least station among ties) and the sheets `S = {r} ∪ (E ∖ R)`, `r` first:
/// `ℓ_o = log(Σ_S g / g_r)`, enclosed; solved exactly when `g_r > Σ_(E∖R) g`, which makes the
/// release lock a right station first; its excess `(ℓ_o − ln 2)_+`, zero where solved.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OrderTerm {
    pub context: usize,
    pub sheets: Vec<OrderSheet>,
    pub value: ExactInterval,
    pub excess: ExactInterval,
    pub solved: Predicate,
    pub kind: Excess,
}

/// The order term of a request's decision terms ([`OrderTerm`]), from the candidates read at their
/// sites; `None` when no site carries a refinement or no eligible station's top is its target.
fn order_terms<R: JointGrowth>(
    sites: &[TermSite],
    reads: &[Vec<R>],
    targets: &[usize],
    reading: Reading,
) -> Result<Vec<OrderTerm>, HnnError> {
    let contexts: Vec<usize> = match reading {
        // At the decisions: the decision refinement, the latest the terms are read at.
        Reading::Decisions => sites.iter().filter_map(|s| s.context).max().into_iter().collect(),
        // The forced release's first lock: every station open.
        Reading::ForcedDecisions => sites.iter().filter_map(|s| s.context).min().into_iter().collect(),
        // At every refinement: each refinement the release executed (its open stations' sites).
        _ => sites
            .iter()
            .filter_map(|s| s.context)
            .collect::<std::collections::BTreeSet<_>>()
            .into_iter()
            .collect(),
    };
    let mut out = Vec::new();
    for context in contexts {
        if let Some(order) = order_at(context, sites, reads, targets)? {
            out.push(order);
        }
    }
    Ok(out)
}

/// The order term at one refinement `context` ([`OrderTerm`]) from the stations read there.
fn order_at<R: JointGrowth>(
    context: usize,
    sites: &[TermSite],
    reads: &[Vec<R>],
    targets: &[usize],
) -> Result<Option<OrderTerm>, HnnError> {
    let one = Rat::one();
    let mut eligible: Vec<(usize, usize, usize, usize, Rat, bool)> = Vec::new();
    for (index, (site, read)) in sites.iter().zip(reads).enumerate() {
        if site.context != Some(context) {
            continue;
        }
        let joints: Vec<&Growth> = read.iter().map(JointGrowth::joint).collect();
        let top = (0..joints.len())
            .max_by(|&a, &b| joints[a].lower.cmp(&joints[b].lower).then(b.cmp(&a)))
            .expect("a class");
        let Some(runner) = (0..joints.len())
            .filter(|&x| x != top)
            .max_by(|&a, &b| joints[a].upper.cmp(&joints[b].upper).then(b.cmp(&a)))
        else {
            continue;
        };
        let flips = (0..joints.len()).filter(|&x| x != top).all(|x| joints[top].exceeds(joints[x]));
        if flips && joints[top].is_locked() {
            let gap = &joints[top].lower - &joints[runner].upper;
            eligible.push((index, site.station, top, runner, gap, top == targets[site.station]));
        }
    }
    let Some(best) = eligible
        .iter()
        .filter(|e| e.5)
        .max_by(|a, b| a.4.cmp(&b.4).then(b.1.cmp(&a.1)))
        .cloned()
    else {
        return Ok(None);
    };
    let members: Vec<(usize, usize, usize, usize, Rat, bool)> = std::iter::once(best.clone())
        .chain(eligible.into_iter().filter(|e| !e.5))
        .collect();
    let total: Rat = members.iter().map(|e| e.4.clone()).sum();
    let wrong = &total - &best.4;
    let sheets = members
        .iter()
        .enumerate()
        .map(|(x, (site, station, top, runner, gap, _))| {
            let share = gap / &total;
            OrderSheet {
                site: *site,
                station: *station,
                top: *top,
                runner: *runner,
                gap: gap.clone(),
                weight: if x == 0 { &share - &one } else { share.clone() },
                share,
            }
        })
        .collect();
    let value = ln_enclosure(&(&total / &best.4))?;
    let (solved, kind) = if best.4 > wrong {
        (Predicate::Holds, Excess::Solved)
    } else if best.4 == wrong {
        (Predicate::Fails, Excess::Boundary)
    } else {
        (Predicate::Fails, Excess::Above)
    };
    let ln2 = ln_two()?;
    let excess = match kind {
        Excess::Solved => nought(),
        Excess::Above => ExactInterval {
            lower: (&value.lower - &ln2.upper).max(Rat::zero()),
            upper: &value.upper - &ln2.lower,
        },
        Excess::Boundary => ExactInterval {
            lower: Rat::zero(),
            upper: (&value.upper - &ln2.lower).max(Rat::zero()),
        },
    };
    Ok(Some(OrderTerm {
        context,
        sheets,
        value,
        excess,
        solved,
        kind,
    }))
}

fn terms_of<R: JointGrowth>(
    composition: Composition,
    targets: &[usize],
    sites: Vec<TermSite>,
    reads: &[Vec<R>],
    termination: usize,
) -> Result<(Vec<TermReading>, ExactInterval, ExactInterval), HnnError> {
    let mut terms = Vec::with_capacity(sites.len());
    let (mut value, mut excess) = (nought(), nought());
    for (site, read) in sites.into_iter().zip(reads) {
        let joints: Vec<&Growth> = read.iter().map(JointGrowth::joint).collect();
        let (comparison, _, lock) = station_comparison(
            &joints,
            targets[site.station],
            site.station,
            site.context,
            termination,
        )?;
        let term = term_reading(composition, site, comparison, &lock);
        value = plus(&value, &term.value);
        excess = plus(&excess, &term.excess);
        terms.push(term);
    }
    Ok((terms, value, excess))
}

/// A request's comparison under the declared comparison, every candidate read by the bank's joint
/// growth alone: its release (receipts and orders), its terms and their sums; with the release's
/// refinements kept (the fixed mask's lookup at a successor).
#[allow(clippy::too_many_arguments)]
fn compare_request(
    field: &Field,
    constitution: &impl ConstitutionRead,
    index: usize,
    request: &Request,
    declared: &Refinement,
    bank: &ReceivingBank,
    grain: u32,
    comparison: Comparison,
) -> Result<(RequestComparison, Vec<BankRefinement<TurnReading>>, BankPlacement), HnnError> {
    let alphabet = field.alphabet();
    let termination = declared.termination();
    let read = |amplitudes: &[GaussianRat]| bank.read_turn(amplitudes, grain);
    let placement = BankPlacement::of(field, constitution, &request.current, &request.moment, declared)?;
    let (generation, refinements) =
        release_of(&placement, request, declared, alphabet, bank, grain, &read)?;
    let (stations, orders) = receipts(request, &refinements, alphabet, termination)?;
    let (refinements, forced) = sites_refinements(
        &placement, request, declared, alphabet, bank, grain, &read, comparison.reading, refinements,
    )?;
    let (sites, consistent) = sites_of(
        index,
        request,
        &refinements,
        comparison.reading,
        declared.stations(),
        alphabet,
    );
    let (reads, made) = site_reads(&sites, &refinements, &placement, alphabet, &read)?;
    let made = made + forced;
    let order_terms = match comparison.composition {
        Composition::LockOrder => {
            order_terms(&sites, &reads, &request.targets, comparison.reading)?
        }
        _ => Vec::new(),
    };
    let (terms, mut value, mut excess) =
        terms_of(comparison.composition, &request.targets, sites, &reads, termination)?;
    for order in &order_terms {
        value = plus(&value, &order.value);
        excess = plus(&excess, &order.excess);
    }
    let readings = refinements.iter().map(|r| r.read.len()).sum::<usize>() + made;
    Ok((
        RequestComparison {
            generation,
            stations,
            orders,
            terms,
            order_terms,
            consistent,
            value,
            excess,
            readings,
        },
        refinements,
        placement,
    ))
}

/// Join the requests' comparisons into their joint one.
fn batch_of(comparison: Comparison, requests: Vec<RequestComparison>) -> BatchComparison {
    let (mut value, mut excess, mut readings) = (nought(), nought(), 0);
    for request in &requests {
        value = plus(&value, &request.value);
        excess = plus(&excess, &request.excess);
        readings += request.readings;
    }
    BatchComparison {
        comparison,
        requests,
        value,
        excess,
        readings,
    }
}

/// **The declared comparison of requests read together** (module header): every request's release
/// read by the bank's joint growth alone, its predicates, orders and releases, its terms under the
/// declared reading, and the composition and its excess enclosed. The targets are validated; an
/// inadmissible crossing refuses it (`HnnError::UncertifiedResonator`), and a reading whose lower
/// end is not positive (`HnnError::NonpositiveDeclaration`).
pub fn compare(
    field: &Field,
    constitution: &impl ConstitutionRead,
    requests: &[Request],
    declared: &Refinement,
    bank: &ReceivingBank,
    grain: u32,
    comparison: Comparison,
) -> Result<BatchComparison, HnnError> {
    use rayon::prelude::*;
    validate(requests, declared.stations(), field.alphabet())?;
    // The requests are co-present regions: the shared constitution read at its cut, one
    // comparison each, joined in request order.
    let compared: Vec<RequestComparison> = requests
        .par_iter()
        .enumerate()
        .map(|(index, request)| {
            Ok(compare_request(
                field,
                constitution,
                index,
                request,
                declared,
                bank,
                grain,
                comparison,
            )?
            .0)
        })
        .collect::<Result<_, HnnError>>()?;
    Ok(batch_of(comparison, compared))
}

/// The incumbent's request: its comparison and every term's candidates read with their covectors.
/// Under the every-refinement reading (and on a partition) the release reads every candidate's
/// covector; otherwise the release reads the joint growths alone and each term's candidates are read
/// with their covectors at its section.
#[allow(clippy::too_many_arguments)]
fn incumbent_request(
    field: &Field,
    constitution: &impl ConstitutionRead,
    index: usize,
    request: &Request,
    declared: &Refinement,
    bank: &ReceivingBank,
    grain: u32,
    comparison: Comparison,
) -> Result<(RequestComparison, Vec<Vec<TurnCovector>>), HnnError> {
    let alphabet = field.alphabet();
    let termination = declared.termination();
    let covector = |amplitudes: &[GaussianRat]| bank.read_turn_covector(amplitudes, grain);
    let every = matches!(comparison.reading, Reading::Every | Reading::Forced)
        || !matches!(request.context, Context::Open);
    if !every {
        let (compared, _, placement) = compare_request(
            field,
            constitution,
            index,
            request,
            declared,
            bank,
            grain,
            comparison,
        )?;
        let sites: Vec<TermSite> = compared.terms.iter().map(|t| t.site.clone()).collect();
        let none: Vec<BankRefinement<TurnCovector>> = Vec::new();
        let (reads, made) = site_reads(&sites, &none, &placement, alphabet, &covector)?;
        let readings = compared.readings + made;
        return Ok((
            RequestComparison {
                readings,
                ..compared
            },
            reads,
        ));
    }
    let placement = BankPlacement::of(field, constitution, &request.current, &request.moment, declared)?;
    // Under a forced reading the release's own refinements carry only its receipts: they are read
    // by value, and only the forced release's candidates carry covectors (its terms' sections).
    let forced_reading = matches!(comparison.reading, Reading::Forced | Reading::ForcedDecisions)
        && matches!(request.context, Context::Open);
    let (generation, stations, orders, refinements, forced) = if forced_reading {
        let value = |amplitudes: &[GaussianRat]| bank.read_turn(amplitudes, grain);
        let (generation, own) =
            release_of(&placement, request, declared, alphabet, bank, grain, &value)?;
        let (stations, orders) = receipts(request, &own, alphabet, termination)?;
        let own_reads: usize = own.iter().map(|r| r.read.len()).sum();
        // The forced refinements' reads are counted with the sites below; the release's own here.
        let (refinements, _) = sites_refinements(
            &placement, request, declared, alphabet, bank, grain, &covector, comparison.reading, Vec::new(),
        )?;
        (generation, stations, orders, refinements, own_reads)
    } else {
        let (generation, refinements) =
            release_of(&placement, request, declared, alphabet, bank, grain, &covector)?;
        let (stations, orders) = receipts(request, &refinements, alphabet, termination)?;
        let (refinements, forced) = sites_refinements(
            &placement, request, declared, alphabet, bank, grain, &covector, comparison.reading, refinements,
        )?;
        (generation, stations, orders, refinements, forced)
    };
    let (sites, consistent) = sites_of(
        index,
        request,
        &refinements,
        comparison.reading,
        declared.stations(),
        alphabet,
    );
    let (reads, made) = site_reads(&sites, &refinements, &placement, alphabet, &covector)?;
    let made = made + forced;
    let order_terms = match comparison.composition {
        Composition::LockOrder => {
            order_terms(&sites, &reads, &request.targets, comparison.reading)?
        }
        _ => Vec::new(),
    };
    let (terms, mut value, mut excess) =
        terms_of(comparison.composition, &request.targets, sites, &reads, termination)?;
    for order in &order_terms {
        value = plus(&value, &order.value);
        excess = plus(&excess, &order.excess);
    }
    let readings = refinements.iter().map(|r| r.read.len()).sum::<usize>() + made;
    Ok((
        RequestComparison {
            generation,
            stations,
            orders,
            terms,
            order_terms,
            consistent,
            value,
            excess,
            readings,
        },
        reads,
    ))
}

// -------------------------------------------------------------------------------------------
// the proposal

/// An enclosure's dyadic face: its midpoint at [`FACE_BITS`] significant bits toward zero.
fn face(interval: &ExactInterval) -> Rat {
    let middle = (&interval.lower + &interval.upper) / Rat::from_integer(BigInt::from(2));
    if middle.is_negative() {
        -significant(&-middle, FACE_BITS, false)
    } else {
        significant(&middle, FACE_BITS, false)
    }
}

/// `⟨covector, move⟩` of an enclosed covector with an enclosed move (an exact move is its point
/// enclosure).
fn paired(covector: &[ExactInterval], moved: &[ExactInterval]) -> ExactInterval {
    let mut sum = nought();
    for (entry, delta) in covector.iter().zip(moved) {
        if delta.lower.is_zero() && delta.upper.is_zero() {
            continue;
        }
        let part = if delta.lower == delta.upper {
            let (a, b) = (&entry.lower * &delta.lower, &entry.upper * &delta.lower);
            ExactInterval {
                lower: a.clone().min(b.clone()),
                upper: a.max(b),
            }
        } else {
            product(entry, delta)
        };
        sum = plus(&sum, &part);
    }
    sum
}

/// Exact moves as their point enclosures.
#[cfg(test)]
fn points(moved: &[Rat]) -> Vec<ExactInterval> {
    moved.iter().cloned().map(ExactInterval::point).collect()
}

/// [definition; agent-inferred, September 30] **The joint direction's modulus part, enclosed**:
/// each entry of `(∂z/∂ρ)Δρ` is enclosed outward on dyadics of [`JOINT_BITS`] significant bits (the
/// derivative's entry and the modulus's unit move each enclosed, their product's corners taken), so
/// the certificate on the joint direction is an enclosure of its exact value with its rounding
/// charged. The exact product of the transported weights' derivatives (powers of the founded
/// modulus over the passage's mass) with the least-squares move carries thousands of bits a
/// coordinate and made the joint certificate cost minutes for each set of requests; the enclosure
/// keeps it at the port's cost. 128 bits lie far below the readings' grain (`2^(−16)` relative).
const JOINT_BITS: u32 = 128;

/// A rational's outward dyadic enclosure at `bits` significant bits.
fn dyadic_enclosure(x: &Rat, bits: u32) -> ExactInterval {
    if x.is_zero() {
        nought()
    } else if x.is_positive() {
        ExactInterval {
            lower: significant(x, bits, false),
            upper: significant(x, bits, true),
        }
    } else {
        let magnitude = -x.clone();
        ExactInterval {
            lower: -significant(&magnitude, bits, true),
            upper: -significant(&magnitude, bits, false),
        }
    }
}

/// The leading active member of a candidate: the resolved active member of the largest midpoint
/// growth, or the refusal of the leading one.
fn leading_member(candidate: &TurnCovector) -> Result<&MemberCovector, CovectorRefusal> {
    let member = candidate
        .active
        .iter()
        .max_by(|a, b| {
            let (ga, gb) = (
                &candidate.reading.members[a.member()],
                &candidate.reading.members[b.member()],
            );
            (&ga.lower + &ga.upper).cmp(&(&gb.lower + &gb.upper))
        })
        .expect("an active member");
    match member {
        MemberCovector::Resolved { .. } => Ok(member),
        MemberCovector::Unresolved { refusal, .. } => Err(*refusal),
    }
}

/// The first unresolved active member of a candidate, if any.
fn unresolved_member(candidate: &TurnCovector) -> Option<CovectorRefusal> {
    candidate.active.iter().find_map(|member| match member {
        MemberCovector::Unresolved { refusal, .. } => Some(*refusal),
        MemberCovector::Resolved { .. } => None,
    })
}

/// [definition; agent-inferred, September 30] **One storage contribution to the proposal**: the
/// station the candidate's storage was read from and the section it was read at (its index among
/// the proposal's sections), its member's storage covector (enclosed) and its weight in the term's
/// covector (the hinge's `+1` a rival and `−1` the target; the lock face's `θ_x` and `θ_t − 1`).
#[derive(Clone, Debug)]
struct Contribution {
    request: usize,
    station: usize,
    cells: Vec<Option<usize>>,
    section: usize,
    covector: Vec<ExactInterval>,
    weight: Rat,
    /// The kind of the branch that leads its term.
    kind: TermKind,
}

/// [definition; agent-inferred, September 30] **The kind of a term's leading branch** (module
/// header, "The two compositions"): the hinge's threshold (the target against the unit, `−ln a_t`)
/// or a class rival (`ln(a_x/a_t)`); every lock-face term reads every sheet (`Lock`). No composition
/// has an order term: the order is read beside it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TermKind {
    Threshold,
    Class,
    Lock,
}

/// [measured-diagnostic; agent-inferred, September 30] **The modulus's slope split by term kind**
/// (the station-framed placement's record §7: which terms carry `γ_ρ < 0`): over the proposal's
/// terms,
/// - the terms led by the threshold and by a class rival (every lock-face term is counted with the
///   class-led), their counts and their composition's sum by kind;
/// - `γ_ρ` of the leading contributions, by the leading kind (their sum is `γ_ρ`);
/// - every term's target part and its rival part read alone (the hinge: the target's
///   `−⟨ĝ_t, ∂z_t/∂ρ⟩` and its class rival's `+⟨ĝ_x, ∂z_x/∂ρ⟩`; the lock face: the target's
///   `(θ_t − 1)⟨ĝ_t, ∂z_t/∂ρ⟩` and the rivals' `Σ θ_x ⟨ĝ_x, ∂z_x/∂ρ⟩`);
/// - the storage curvature `G_ρ = Σ_c |∂z_c/∂ρ|²` over the leading contributions, so the committed
///   move's least-squares unit move `−γ_ρ/G_ρ` is read beside its slope (the segment probe's record
///   §4, October 1).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SlopeSplit {
    pub threshold_led: usize,
    pub class_led: usize,
    pub threshold_value: ExactInterval,
    pub class_value: ExactInterval,
    pub led_threshold: Rat,
    pub led_class: Rat,
    pub target: Rat,
    pub rival: Rat,
    pub curvature: Rat,
}

/// A term's first-order certificate (module header, "The first-order certificate").
#[derive(Clone, Debug)]
enum Certificate {
    /// The hinge: every active branch, each its contributions (rival at `+1`, target at `−1`).
    Hinge(Vec<Vec<Contribution>>),
    /// The lock face: every candidate's section, its active resolved members' covectors and its
    /// share `θ_x` enclosed; and the lock's one normalized reading ([`LockFace`]'s `sheets`).
    Lock {
        target: usize,
        candidates: Vec<(usize, Vec<Vec<ExactInterval>>, ExactInterval)>,
        sheets: Vec<Rat>,
    },
    /// The order term ([`OrderTerm`]): every sheet's covector weight over its gap `(θ − [x = r])/g`,
    /// its share `θ`, and its top's and runner's sections, active resolved members' covectors,
    /// leading covectors and joint enclosures. `dg = a_top du_top − a_runner du_runner`.
    Order(Vec<OrderPiece>),
}

/// One sheet of an order term's certificate ([`Certificate::Order`]).
#[derive(Clone, Debug)]
struct OrderPiece {
    ratio: Rat,
    share: Rat,
    gap: Rat,
    top: OrderEnd,
    runner: OrderEnd,
}

/// The top or the runner of an order sheet: its section, its active resolved members' covectors,
/// its leading member's covector and its joint enclosure.
#[derive(Clone, Debug)]
struct OrderEnd {
    section: usize,
    members: Vec<Vec<ExactInterval>>,
    leading: Vec<ExactInterval>,
    growth: ExactInterval,
}

/// One term of the certificate's support: its site, where it lies against its level, its
/// certificate, the first unresolved active member it reads (if any), and its leading contributions
/// (receipts).
#[derive(Clone, Debug)]
struct TermCertificate {
    site: TermSite,
    kind: Excess,
    certificate: Certificate,
    unresolved: Option<CovectorRefusal>,
    leading: Vec<Contribution>,
}

/// The proposal: its contributions (the direction), every term of the certificate's support, the
/// sections they read, the unresolved leading members, and the slope split's parts.
struct Proposal {
    contributions: Vec<Contribution>,
    terms: Vec<TermCertificate>,
    sections: Vec<(usize, usize, Vec<Option<usize>>)>,
    unresolved: Vec<CovectorRefusal>,
    targets: Vec<Contribution>,
    rivals: Vec<Contribution>,
    led: [(usize, ExactInterval); 2],
    /// Every section's storage derivative in `ρ` at the incumbent, read once ([`section_derivatives`]).
    derivatives: std::sync::OnceLock<Vec<Vec<Rat>>>,
}

impl Proposal {
    /// The terms whose certificate reads an unresolved active member.
    fn unresolved_terms(&self) -> usize {
        self.terms.iter().filter(|t| t.unresolved.is_some()).count()
    }
}

/// The proposal's sections, each once.
#[derive(Default)]
struct Sections {
    index: BTreeMap<(usize, usize, Vec<Option<usize>>), usize>,
    list: Vec<(usize, usize, Vec<Option<usize>>)>,
}

impl Sections {
    fn at(&mut self, request: usize, station: usize, cells: &[Option<usize>]) -> usize {
        let key = (request, station, cells.to_vec());
        if let Some(&at) = self.index.get(&key) {
            return at;
        }
        let at = self.list.len();
        self.list.push(key.clone());
        self.index.insert(key, at);
        at
    }
}

/// One contribution at a term's site with its candidate's class placed, its section indexed once.
fn contribute(
    sections: &mut Sections,
    request: usize,
    site: &TermSite,
    class: usize,
    covector: Vec<ExactInterval>,
    weight: Rat,
    kind: TermKind,
) -> Contribution {
    let mut cells = site.cells.clone();
    cells[site.station] = Some(class);
    let section = sections.at(request, site.station, &cells);
    Contribution {
        request,
        station: site.station,
        cells,
        section,
        covector,
        weight,
        kind,
    }
}

/// [definition; agent-inferred, September 30] **The proposal and its certificate's terms** (module
/// header, "The covector" and "The first-order certificate") from the incumbent's terms and their
/// candidates' covectors: a pure function of the readings.
fn propose(
    composition: Composition,
    before: &BatchComparison,
    reads: &[Vec<Vec<TurnCovector>>],
) -> Proposal {
    let mut sections = Sections::default();
    let mut contributions = Vec::new();
    let mut terms_out = Vec::new();
    let mut unresolved = Vec::new();
    let (mut targets_alone, mut rivals_alone) = (Vec::new(), Vec::new());
    let mut led = [(0, nought()), (0, nought())];
    let one = Rat::one();
    for (request, (compared, request_reads)) in before.requests.iter().zip(reads).enumerate() {
        for (term, chunk) in compared.terms.iter().zip(request_reads) {
            if !in_support(composition, term.kind) {
                continue;
            }
            let site = &term.site;
            let target = term.comparison.target;
            let mut contribution =
                |class: usize, covector: Vec<ExactInterval>, weight: Rat, kind: TermKind| {
                    contribute(&mut sections, request, site, class, covector, weight, kind)
                };
            match composition {
                Composition::Hinge => {
                    let joints: Vec<&Growth> = chunk.iter().map(JointGrowth::joint).collect();
                    let hinge = station_term(&joints, target).expect("a term already read");
                    let kind = match hinge.leading {
                        None => TermKind::Threshold,
                        Some(_) => TermKind::Class,
                    };
                    let mut leading = Vec::new();
                    if hinge.value.upper.is_positive() {
                        // The term's two parts read alone (the slope's split).
                        if let (Ok(t), Ok(x)) =
                            (leading_member(&chunk[target]), leading_member(&chunk[hinge.rival]))
                        {
                            targets_alone.push(contribution(
                                target,
                                t.storage().expect("resolved"),
                                -one.clone(),
                                kind,
                            ));
                            rivals_alone.push(contribution(
                                hinge.rival,
                                x.storage().expect("resolved"),
                                one.clone(),
                                kind,
                            ));
                        }
                        let slot = &mut led[usize::from(kind == TermKind::Class)];
                        slot.0 += 1;
                        slot.1 = plus(&slot.1, &positive_part(&hinge.value));
                        let target_member = leading_member(&chunk[target]);
                        let formed = match (hinge.leading, &target_member) {
                            (_, Err(refusal)) => Err(*refusal),
                            (None, Ok(t)) => Ok(vec![contribution(
                                target,
                                t.storage().expect("resolved"),
                                -one.clone(),
                                kind,
                            )]),
                            (Some(x), Ok(t)) => leading_member(&chunk[x]).map(|m| {
                                vec![
                                    contribution(x, m.storage().expect("resolved"), one.clone(), kind),
                                    contribution(
                                        target,
                                        t.storage().expect("resolved"),
                                        -one.clone(),
                                        kind,
                                    ),
                                ]
                            }),
                        };
                        match formed {
                            Ok(formed) => {
                                contributions.extend(formed.iter().cloned());
                                leading = formed;
                            }
                            Err(refusal) => unresolved.push(refusal),
                        }
                    }
                    // Every active branch, for the first-order certificate.
                    let mut branches = Vec::new();
                    let mut refused = unresolved_member(&chunk[target]);
                    for branch in &hinge.branches {
                        if let Some(x) = branch {
                            refused = refused.or(unresolved_member(&chunk[*x]));
                        }
                        for t in &chunk[target].active {
                            let Some(tc) = t.storage() else { continue };
                            match branch {
                                None => branches.push(vec![contribution(target, tc, -one.clone(), kind)]),
                                Some(x) => {
                                    for m in &chunk[*x].active {
                                        let Some(mc) = m.storage() else { continue };
                                        branches.push(vec![
                                            contribution(*x, mc, one.clone(), kind),
                                            contribution(target, tc.clone(), -one.clone(), kind),
                                        ]);
                                    }
                                }
                            }
                        }
                    }
                    terms_out.push(TermCertificate {
                        site: site.clone(),
                        kind: term.kind,
                        certificate: Certificate::Hinge(branches),
                        unresolved: refused,
                        leading,
                    });
                }
                Composition::LockFace | Composition::LockOrder => {
                    let joints: Vec<&Growth> = chunk.iter().map(JointGrowth::joint).collect();
                    let lock = lock_face_of(&joints, target).expect("a term already read");
                    let slot = &mut led[1];
                    slot.0 += 1;
                    slot.1 = plus(&slot.1, &lock.value);
                    let mut leading = Vec::new();
                    let mut refused = None;
                    let mut candidates = Vec::with_capacity(chunk.len());
                    for (x, candidate) in chunk.iter().enumerate() {
                        let weight = lock.weight(x, target);
                        match leading_member(candidate) {
                            Ok(member) => {
                                let c = contribution(
                                    x,
                                    member.storage().expect("resolved"),
                                    weight,
                                    TermKind::Lock,
                                );
                                if x == target {
                                    targets_alone.push(c.clone());
                                } else {
                                    rivals_alone.push(c.clone());
                                }
                                leading.push(c);
                            }
                            Err(refusal) => unresolved.push(refusal),
                        }
                        refused = refused.or(unresolved_member(candidate));
                        let section =
                            contribution(x, Vec::new(), Rat::zero(), TermKind::Lock).section;
                        let members: Vec<Vec<ExactInterval>> = candidate
                            .active
                            .iter()
                            .filter_map(MemberCovector::storage)
                            .collect();
                        candidates.push((section, members, lock.shares[x].clone()));
                    }
                    contributions.extend(leading.iter().cloned());
                    terms_out.push(TermCertificate {
                        site: site.clone(),
                        kind: term.kind,
                        certificate: Certificate::Lock {
                            target,
                            candidates,
                            sheets: lock.sheets.clone(),
                        },
                        unresolved: refused,
                        leading,
                    });
                }
            }
        }
        for order in &compared.order_terms {
            let mut pieces = Vec::with_capacity(order.sheets.len());
            let mut leading = Vec::new();
            let mut refused = None;
            for sheet in &order.sheets {
                let site = &compared.terms[sheet.site].site;
                let chunk = &request_reads[sheet.site];
                let ratio = &sheet.weight / &sheet.gap;
                let mut end = |class: usize, sign: Rat| -> Option<OrderEnd> {
                    let candidate = &chunk[class];
                    refused = refused.or(unresolved_member(candidate));
                    let member = match leading_member(candidate) {
                        Ok(member) => member,
                        Err(refusal) => {
                            unresolved.push(refusal);
                            return None;
                        }
                    };
                    let growth = candidate.joint();
                    let growth = ExactInterval {
                        lower: growth.lower.clone(),
                        upper: growth.upper.clone(),
                    };
                    let covector = member.storage().expect("resolved");
                    let weight = &ratio * &face(&growth) * &sign;
                    let c = contribute(
                        &mut sections,
                        request,
                        site,
                        class,
                        covector.clone(),
                        weight,
                        TermKind::Lock,
                    );
                    let section = c.section;
                    leading.push(c);
                    Some(OrderEnd {
                        section,
                        members: candidate
                            .active
                            .iter()
                            .filter_map(MemberCovector::storage)
                            .collect(),
                        leading: covector,
                        growth,
                    })
                };
                let top = end(sheet.top, Rat::one());
                let runner = end(sheet.runner, -Rat::one());
                if let (Some(top), Some(runner)) = (top, runner) {
                    pieces.push(OrderPiece {
                        ratio,
                        share: sheet.share.clone(),
                        gap: sheet.gap.clone(),
                        top,
                        runner,
                    });
                }
            }
            contributions.extend(leading.iter().cloned());
            terms_out.push(TermCertificate {
                site: compared.terms[order.sheets[0].site].site.clone(),
                kind: order.kind,
                certificate: Certificate::Order(pieces),
                unresolved: refused,
                leading,
            });
        }
    }
    Proposal {
        contributions,
        terms: terms_out,
        sections: sections.list,
        unresolved,
        targets: targets_alone,
        rivals: rivals_alone,
        led,
        derivatives: std::sync::OnceLock::new(),
    }
}

/// [definition; agent-inferred, September 30] **The proposal's returns at the source port**
/// (module header, "The covector"). Every contribution's storage is its passage's read from its
/// station `j` (`BankPlacement::storage`): each datum, the request's phase counts and the section's
/// cells, at its transported weight `w_S` from `j` over the span its section `S` closes (the
/// storage stays linear in `E` at fixed weights, so the form of the returns is unchanged; only the
/// weights are read from the contribution's station). Every datum returns in one form, one return a
/// placement aggregated by its feature: one per phase of each request (feature the phase's counts
/// `M[c]` at the weight `Σ w_S(c)²` over the contributions, covector their `w_S(c)`-weighted sum
/// carried back through the phase's rotation `P^(c − λ)`, over that weight), and one per class over
/// all the requests for the sections' placements (feature `e_x` at the weight `Σ w_S(j)²`, covector
/// their `w_S(j)`-weighted sum over it): the same gradient, unit step, alignment and metric as one
/// return a placement; each the descent covector, every contribution at its weight in its term's
/// covector.
fn returns(
    field: &Field,
    constitution: &Constitution,
    declared: &Refinement,
    requests: &[Request],
    contributions: &[Contribution],
) -> Result<Vec<Sample>, HnnError> {
    returns_coupled(field, constitution, declared, requests, contributions, None)
}

/// [definition; agent-inferred, October 2] **The returns carrying the modulus's coupling**
/// ([`ModulusCoupling`]): [`returns`], with `x = Δρ` the joined solve's modulus part, each return of
/// feature `f` and weight `W = Σ w²` carrying beside its covector `−x (S/W) E f`, `S = Σ w² s` over
/// the same data (`s` each datum's reach slope). The normal law's step with these returns is the
/// solve's `E` part, `M⁻¹Aᵀμ`'s `YH′⁻¹ − x bH′⁻¹` with `b` read on the data the returns reach: the
/// storage change of the modulus's move returned to the port through the data that carry it.
fn returns_coupled(
    field: &Field,
    constitution: &Constitution,
    declared: &Refinement,
    requests: &[Request],
    contributions: &[Contribution],
    coupling: Option<(&Rat, &ExactRatMatrix)>,
) -> Result<Vec<Sample>, HnnError> {
    let ring = declared.ring();
    // `−x E f` in `E`'s frame, for a feature `f`.
    let coupled = |feature: &[Rat]| -> Option<Vec<Rat>> {
        let (x, port) = coupling?;
        Some(
            (0..port.rows())
                .map(|r| {
                    let row = port.row(r).expect("a row of the port");
                    -(x * row.iter().zip(feature).map(|(e, f)| e * f).sum::<Rat>())
                })
                .collect(),
        )
    };
    let geometry = field.ring(ring);
    let period = geometry.period() as usize;
    let width = geometry.width();
    let alphabet = field.alphabet();
    let mut samples = Vec::new();
    let mut section_sums = vec![vec![Rat::zero(); width]; alphabet];
    let mut section_weights = vec![Rat::zero(); alphabet];
    let mut section_reach = vec![Rat::zero(); alphabet];
    let placements = placements_of(field, constitution, requests, declared)?;
    for (index, (request, placement)) in requests.iter().zip(&placements).enumerate() {
        let mine: Vec<&Contribution> = contributions.iter().filter(|c| c.request == index).collect();
        if mine.is_empty() {
            continue;
        }
        let lift = request.current.lift()[ring].clone();
        let phase = request.current.phase(field, ring)? as usize;
        let phases: Vec<usize> = (0..period)
            .filter(|&c| {
                request
                    .moment
                    .phase_counts(ring, c)
                    .is_ok_and(|counts| counts.iter().any(|&n| n != 0))
            })
            .collect();
        let mut phase_sums = vec![vec![Rat::zero(); width]; phases.len()];
        let mut phase_weights = vec![Rat::zero(); phases.len()];
        let mut phase_reach = vec![Rat::zero(); phases.len()];
        for contribution in mine {
            let covector: Vec<Rat> = contribution.covector.iter().map(face).collect();
            let (request_weights, station_weights) =
                placement.weights(contribution.station, &contribution.cells);
            if coupling.is_some() {
                let (request_slopes, station_slopes) =
                    placement.reach_slopes(contribution.station, &contribution.cells);
                for ((reach, weight), slope) in
                    phase_reach.iter_mut().zip(&request_weights).zip(&request_slopes)
                {
                    *reach += weight * weight * slope;
                }
                for ((cell, weight), slope) in
                    contribution.cells.iter().zip(&station_weights).zip(&station_slopes)
                {
                    if let (Some(class), Some(weight), Some(slope)) = (cell, weight, slope) {
                        section_reach[*class] += weight * weight * slope;
                    }
                }
            }
            for ((sum, total), weight) in phase_sums
                .iter_mut()
                .zip(phase_weights.iter_mut())
                .zip(&request_weights)
            {
                let scale = weight * &contribution.weight;
                for (value, add) in sum.iter_mut().zip(&covector) {
                    *value += add * &scale;
                }
                *total += weight * weight;
            }
            // The section's placements: each placed station's class at its phase and weight.
            for (station, (cell, weight)) in
                contribution.cells.iter().zip(&station_weights).enumerate()
            {
                let (Some(class), Some(weight)) = (cell, weight) else { continue };
                let at = (phase + 1 + station) % period;
                let rotated = geometry.rotate(&covector, &(BigInt::from(at) - &lift));
                for (sum, value) in section_sums[*class].iter_mut().zip(&rotated) {
                    *sum += value * weight * &contribution.weight;
                }
                section_weights[*class] += weight * weight;
            }
        }
        for (((c, sum), weight), reach) in phases.iter().zip(phase_sums).zip(phase_weights).zip(phase_reach) {
            let carried = coupling.is_some() && !reach.is_zero();
            if !weight.is_positive() || (sum.iter().all(Zero::is_zero) && !carried) {
                continue;
            }
            let feature: Vec<Rat> = request
                .moment
                .phase_counts(ring, *c)?
                .iter()
                .map(|&count| Rat::from_integer(BigInt::from(count)))
                .collect();
            let rotated = geometry.rotate(&sum, &(BigInt::from(*c as u64) - &lift));
            let mut covector: Vec<Rat> = rotated.into_iter().map(|x| -(x / &weight)).collect();
            if carried && let Some(term) = coupled(&feature) {
                let share = &reach / &weight;
                for (value, add) in covector.iter_mut().zip(term) {
                    *value += add * &share;
                }
            }
            samples.push(Sample { covector, weight, feature });
        }
    }
    for class in 0..alphabet {
        if !section_weights[class].is_positive() {
            continue;
        }
        let weight = section_weights[class].clone();
        let mut feature = vec![Rat::zero(); alphabet];
        feature[class] = Rat::one();
        let mut covector: Vec<Rat> = section_sums[class].iter().map(|x| -(x / &weight)).collect();
        if !section_reach[class].is_zero()
            && let Some(term) = coupled(&feature)
        {
            let share = &section_reach[class] / &weight;
            for (value, add) in covector.iter_mut().zip(term) {
                *value += add * &share;
            }
        }
        samples.push(Sample { covector, weight, feature });
    }
    Ok(samples)
}

/// Every request's placement at a constitution: co-present regions (the shared constitution at
/// its cut, one placement each), formed on the host's cores in request order.
fn placements_of(
    field: &Field,
    constitution: &impl ConstitutionRead,
    requests: &[Request],
    declared: &Refinement,
) -> Result<Vec<BankPlacement>, HnnError> {
    use rayon::prelude::*;
    requests
        .par_iter()
        .map(|r| BankPlacement::of(field, constitution, &r.current, &r.moment, declared))
        .collect()
}

/// [agent-inferred, October 1] **Every section's storage derivative in `ρ`, read once a proposal**
/// (`BankPlacement::modulus_derivative`, exact): the modulus's normal reading, its split and the
/// witness's plane all read the same sections at the same incumbent. Each had read them anew, the
/// split three times over; under the forced reading that cost 603,039 ms of a 635,681 ms read at
/// the opening, the incumbent's covectors 28,739 ms (the forced release's record).
fn section_derivatives<'a>(
    field: &Field,
    constitution: &impl ConstitutionRead,
    declared: &Refinement,
    requests: &[Request],
    proposal: &'a Proposal,
) -> Result<&'a [Vec<Rat>], HnnError> {
    use rayon::prelude::*;
    if let Some(derivatives) = proposal.derivatives.get() {
        return Ok(derivatives);
    }
    let placements = placements_of(field, constitution, requests, declared)?;
    let derivatives: Vec<Vec<Rat>> = proposal
        .sections
        .par_iter()
        .map(|(request, station, cells)| placements[*request].modulus_derivative(*station, cells))
        .collect();
    Ok(proposal.derivatives.get_or_init(|| derivatives))
}

/// Each contribution's `c ⟨ĝ, ∂z/∂ρ⟩` and `|∂z/∂ρ|²` (the modulus's normal reading, term by term),
/// every contribution a section of `proposal`.
fn modulus_pairings(
    field: &Field,
    constitution: &impl ConstitutionRead,
    declared: &Refinement,
    requests: &[Request],
    proposal: &Proposal,
    contributions: &[Contribution],
) -> Result<Vec<(Rat, Rat)>, HnnError> {
    use rayon::prelude::*;
    let derivatives = section_derivatives(field, constitution, declared, requests, proposal)?;
    Ok(contributions
        .par_iter()
        .map(|c| {
            let derivative = &derivatives[c.section];
            let paired: Rat = c
                .covector
                .iter()
                .map(face)
                .zip(derivative)
                .map(|(g, d)| g * d)
                .sum();
            let energy: Rat = derivative.iter().map(|d| d * d).sum();
            (paired * &c.weight, energy)
        })
        .collect())
}

/// [definition; agent-inferred, September 30] **The modulus's normal reading** (module header,
/// "The committed move"): the proposal's slope in the transport modulus
/// `γ_ρ = Σ_c c ⟨ĝ_c, ∂z_c/∂ρ⟩` (each contribution's storage covector at its dyadic face paired with
/// its storage's exact derivative, `BankPlacement::modulus_derivative`) and its storage curvature
/// `G_ρ = Σ_c |∂z_c/∂ρ|²`, each storage read from its contribution's station; the least-squares unit
/// move is `−γ_ρ/G_ρ` (Lean `HNN/ExecutedComparison.modulus_least_squares`).
fn modulus_normal(
    field: &Field,
    constitution: &Constitution,
    declared: &Refinement,
    requests: &[Request],
    proposal: &Proposal,
) -> Result<(Rat, Rat), HnnError> {
    Ok(
        modulus_pairings(field, constitution, declared, requests, proposal, &proposal.contributions)?
            .into_iter()
            .fold((Rat::zero(), Rat::zero()), |(a, b), (c, d)| (a + c, b + d)),
    )
}

/// [measured-diagnostic; agent-inferred, September 30] **The proposal's modulus slope split by
/// term kind** ([`SlopeSplit`]).
fn slope_split(
    field: &Field,
    constitution: &impl ConstitutionRead,
    declared: &Refinement,
    requests: &[Request],
    proposal: &Proposal,
) -> Result<SlopeSplit, HnnError> {
    let led =
        modulus_pairings(field, constitution, declared, requests, proposal, &proposal.contributions)?;
    let (mut led_threshold, mut led_class, mut curvature) = (Rat::zero(), Rat::zero(), Rat::zero());
    for (c, (value, energy)) in proposal.contributions.iter().zip(led) {
        curvature += energy;
        match c.kind {
            TermKind::Threshold => led_threshold += value,
            TermKind::Class | TermKind::Lock => led_class += value,
        }
    }
    let sum = |list: &[Contribution]| -> Result<Rat, HnnError> {
        Ok(modulus_pairings(field, constitution, declared, requests, proposal, list)?
            .into_iter()
            .map(|(value, _)| value)
            .sum())
    };
    Ok(SlopeSplit {
        threshold_led: proposal.led[0].0,
        class_led: proposal.led[1].0,
        threshold_value: proposal.led[0].1.clone(),
        class_value: proposal.led[1].1.clone(),
        led_threshold,
        led_class,
        target: sum(&proposal.targets)?,
        rival: sum(&proposal.rivals)?,
        curvature,
    })
}

/// The incumbent read of the requests: their comparison and every term's candidates' covectors.
#[allow(clippy::type_complexity)]
fn incumbent(
    field: &Field,
    constitution: &impl ConstitutionRead,
    requests: &[Request],
    declared: &Refinement,
    bank: &ReceivingBank,
    grain: u32,
    comparison: Comparison,
) -> Result<(BatchComparison, Vec<Vec<Vec<TurnCovector>>>), HnnError> {
    use rayon::prelude::*;
    validate(requests, declared.stations(), field.alphabet())?;
    // The requests are co-present regions (the shared constitution at its cut, one reading each).
    let joined: Vec<(RequestComparison, Vec<Vec<TurnCovector>>)> = requests
        .par_iter()
        .enumerate()
        .map(|(index, request)| {
            incumbent_request(
                field,
                constitution,
                index,
                request,
                declared,
                bank,
                grain,
                comparison,
            )
        })
        .collect::<Result<_, HnnError>>()?;
    let (compared, reads): (Vec<RequestComparison>, Vec<Vec<Vec<TurnCovector>>>) =
        joined.into_iter().unzip();
    Ok((batch_of(comparison, compared), reads))
}

/// [measured-diagnostic; agent-inferred, September 30] **The modulus's slope split by term kind at
/// a constitution** ([`SlopeSplit`]; the station-framed placement's record §7), with the requests'
/// comparison: the requests read with every term's candidates' covectors, the proposal formed as
/// [`executed_move`] forms it, and no move made.
pub fn modulus_slopes(
    field: &Field,
    constitution: &impl ConstitutionRead,
    requests: &[Request],
    declared: &Refinement,
    bank: &ReceivingBank,
    grain: u32,
    comparison: Comparison,
) -> Result<(BatchComparison, SlopeSplit), HnnError> {
    let (before, reads) = incumbent(field, constitution, requests, declared, bank, grain, comparison)?;
    let proposal = propose(comparison.composition, &before, &reads);
    let split = slope_split(field, constitution, declared, requests, &proposal)?;
    Ok((before, split))
}

// -------------------------------------------------------------------------------------------
// loop 1c's representation readings (a search's readings, never a move)

/// [measured-diagnostic; agent-inferred, loop 1c's
/// [pin](../../../../research/records/2026-10-01_LOOP_1C_PERSISTENCE_REPRESENTATION_AND_REACH_PINNED_BEFORE_ITS_RUNS.md)
/// §3] **A decision term's lock face and its gradient at the constitution**: its site, target,
/// `ℓ` enclosed and where it lies against `ln 2`, and, where every candidate's leading member is
/// resolved, `∂ℓ/∂E` (the port's rows by the chart's classes) and `∂ℓ/∂ρ`, each the lock face's
/// covector `θ − q` at the shares' dyadic faces paired through the candidates' leading members'
/// storage covectors at their dyadic faces (the proposal's own contributions, [`executed_move`]'s
/// law), pulled back to `E` at the placement's fixed weights (the storage is linear in `E` there)
/// and to `ρ` through `BankPlacement::modulus_derivative`. A reading for an exterior search: no
/// move is made, and nothing is retained.
#[derive(Clone, Debug)]
pub struct SiteGradient {
    pub site: TermSite,
    pub target: usize,
    pub lock: ExactInterval,
    pub kind: Excess,
    pub gradient: Option<(ExactRatMatrix, Rat)>,
}

/// One contribution's pullback to the source port at its placement's fixed weights:
/// `∂⟨ĝ, z⟩/∂E`, the covector at its dyadic face carried back through each request phase's rotation
/// against the phase's counts and through each placed station's rotation against its class
/// ([`returns`]' law for one contribution, unaggregated), times the contribution's weight.
fn pullback(
    field: &Field,
    declared: &Refinement,
    request: &Request,
    placement: &BankPlacement,
    contribution: &Contribution,
) -> Result<Vec<Vec<Rat>>, HnnError> {
    let ring = declared.ring();
    let geometry = field.ring(ring);
    let period = geometry.period() as usize;
    let width = geometry.width();
    let alphabet = field.alphabet();
    let lift = request.current.lift()[ring].clone();
    let phase = request.current.phase(field, ring)? as usize;
    let phases: Vec<usize> = (0..period)
        .filter(|&c| {
            request
                .moment
                .phase_counts(ring, c)
                .is_ok_and(|counts| counts.iter().any(|&n| n != 0))
        })
        .collect();
    let covector: Vec<Rat> = contribution.covector.iter().map(face).collect();
    let (request_weights, station_weights) =
        placement.weights(contribution.station, &contribution.cells);
    let mut gradient = vec![vec![Rat::zero(); alphabet]; width];
    for (c, weight) in phases.iter().zip(&request_weights) {
        let scale = weight * &contribution.weight;
        if scale.is_zero() {
            continue;
        }
        let rotated = geometry.rotate(&covector, &(BigInt::from(*c as u64) - &lift));
        let counts = request.moment.phase_counts(ring, *c)?;
        for (row, value) in gradient.iter_mut().zip(&rotated) {
            let value = value * &scale;
            for (entry, &count) in row.iter_mut().zip(counts) {
                if count != 0 {
                    *entry += &value * Rat::from_integer(BigInt::from(count));
                }
            }
        }
    }
    for (station, (cell, weight)) in contribution.cells.iter().zip(&station_weights).enumerate() {
        let (Some(class), Some(weight)) = (cell, weight) else { continue };
        let at = (phase + 1 + station) % period;
        let rotated = geometry.rotate(&covector, &(BigInt::from(at) - &lift));
        let scale = weight * &contribution.weight;
        for (row, value) in gradient.iter_mut().zip(&rotated) {
            row[*class] += value * &scale;
        }
    }
    Ok(gradient)
}

/// [measured-diagnostic; agent-inferred, loop 1c's pin §3] **Every decision term's lock face and
/// gradient at a constitution** ([`SiteGradient`]), with the requests' comparison (the lock face at
/// the decisions, [`Comparison::LOCK_DECISIONS`], read as [`executed_move`] reads its incumbent):
/// the exterior fit's linearization at the release's actual decision contexts. No move is made.
pub fn site_gradients(
    field: &Field,
    constitution: &Constitution,
    requests: &[Request],
    declared: &Refinement,
    bank: &ReceivingBank,
    grain: u32,
) -> Result<(BatchComparison, Vec<SiteGradient>), HnnError> {
    use rayon::prelude::*;
    let comparison = Comparison::LOCK_DECISIONS;
    let (before, reads) = incumbent(field, constitution, requests, declared, bank, grain, comparison)?;
    let proposal = propose(comparison.composition, &before, &reads);
    drop(reads);
    let placements = placements_of(field, constitution, requests, declared)?;
    let alphabet = field.alphabet();
    let rows = constitution
        .source_port(declared.ring())
        .ok_or(HnnError::MissingSourcePort {
            ring: declared.ring(),
        })?
        .rows();
    let terms: Vec<&TermReading> = before.requests.iter().flat_map(|r| &r.terms).collect();
    let gradients: Vec<SiteGradient> = proposal
        .terms
        .par_iter()
        .zip(terms.par_iter())
        .map(|(certificate, term)| -> Result<SiteGradient, HnnError> {
            let gradient = if certificate.leading.len() == alphabet {
                let mut port = vec![vec![Rat::zero(); alphabet]; rows];
                let mut modulus = Rat::zero();
                for c in &certificate.leading {
                    let request = &requests[c.request];
                    let placement = &placements[c.request];
                    for (row, add) in port
                        .iter_mut()
                        .zip(pullback(field, declared, request, placement, c)?)
                    {
                        for (entry, add) in row.iter_mut().zip(add) {
                            *entry += add;
                        }
                    }
                    let derivative = placement.modulus_derivative(c.station, &c.cells);
                    let paired: Rat = c
                        .covector
                        .iter()
                        .map(face)
                        .zip(&derivative)
                        .map(|(g, d)| g * d)
                        .sum();
                    modulus += paired * &c.weight;
                }
                Some((ExactRatMatrix::new(port)?, modulus))
            } else {
                None
            };
            Ok(SiteGradient {
                site: certificate.site.clone(),
                target: term.comparison.target,
                lock: term.comparison.lock.clone(),
                kind: term.kind,
                gradient,
            })
        })
        .collect::<Result<_, HnnError>>()?;
    Ok((before, gradients))
}

/// [measured-diagnostic; agent-inferred, loop 1c's pin §3] **A declared comparison read at a
/// constitution on its own release and on frozen sites**: the own release's comparison (every
/// request's release and its declared terms), and the terms re-read at the given sites (each a
/// request's station at a section, read from the own release's refinement where it executed the
/// same section, else read there), as [`executed_move`]'s fixed mask is read, with the readings
/// made. The representation search's frozen contexts: a constitution that solves the frozen sites
/// but not its own release's is a frozen-context witness only. Errors are the comparison's (an
/// inadmissible crossing, an unsupported reading).
pub fn frozen_reread(
    field: &Field,
    constitution: &impl ConstitutionRead,
    requests: &[Request],
    declared: &Refinement,
    bank: &ReceivingBank,
    grain: u32,
    comparison: Comparison,
    sites: &[Vec<TermSite>],
) -> Result<(BatchComparison, Vec<Vec<TermReading>>, usize), HnnError> {
    use rayon::prelude::*;
    validate(requests, declared.stations(), field.alphabet())?;
    let alphabet = field.alphabet();
    let termination = declared.termination();
    let read = |amplitudes: &[GaussianRat]| bank.read_turn(amplitudes, grain);
    #[allow(clippy::type_complexity)]
    let joined: Vec<(RequestComparison, Vec<TermReading>, usize)> = requests
        .par_iter()
        .enumerate()
        .map(|(index, request)| {
            let (own, refinements, placement) = compare_request(
                field,
                constitution,
                index,
                request,
                declared,
                bank,
                grain,
                comparison,
            )?;
            let frozen = sites[index].clone();
            let (reads, made) = site_reads(&frozen, &refinements, &placement, alphabet, &read)?;
            let (terms, _, _) =
                terms_of(comparison.composition, &request.targets, frozen, &reads, termination)?;
            Ok((own, terms, made))
        })
        .collect::<Result<_, HnnError>>()?;
    let mut own = Vec::with_capacity(joined.len());
    let mut frozen = Vec::with_capacity(joined.len());
    let mut made = 0;
    for (o, f, m) in joined {
        own.push(o);
        frozen.push(f);
        made += m;
    }
    Ok((batch_of(comparison, own), frozen, made))
}

/// **The proposal's contributions and returns at `E`** (the owner's pullback test): each
/// contribution's request, section, dyadic face of its storage covector and weight, and the returns
/// [`returns`] carries to the source port.
#[cfg(test)]
#[allow(clippy::type_complexity)]
pub(crate) fn proposal_returns(
    field: &Field,
    constitution: &Constitution,
    requests: &[Request],
    declared: &Refinement,
    bank: &ReceivingBank,
    grain: u32,
    comparison: Comparison,
) -> Result<(Vec<Sample>, Vec<(usize, usize, Vec<Option<usize>>, Vec<Rat>, Rat)>), HnnError> {
    let (before, reads) = incumbent(field, constitution, requests, declared, bank, grain, comparison)?;
    let proposal = propose(comparison.composition, &before, &reads);
    let samples = returns(field, constitution, declared, requests, &proposal.contributions)?;
    Ok((
        samples,
        proposal
            .contributions
            .iter()
            .map(|c| {
                (
                    c.request,
                    c.station,
                    c.cells.clone(),
                    c.covector.iter().map(face).collect(),
                    c.weight.clone(),
                )
            })
            .collect(),
    ))
}

// -------------------------------------------------------------------------------------------
// the first-order certificate

/// The storage moves of every section from a constitution to a carried successor, each read from
/// its station: the successor's storage less the constitution's, exactly (the storage is linear in
/// `E` at fixed weights, so at a fixed modulus this is the move `ΔE`'s placement; a move of the
/// modulus moves every weight). With `modulus = Some(Δρ)` each move adds the modulus's first-order
/// storage move `(∂z/∂ρ)Δρ` read at the constitution, enclosed outward at [`JOINT_BITS`]: the joint
/// unit direction's storage move. Each move is an enclosure (a point where exact).
fn section_moves(
    field: &Field,
    constitution: &Constitution,
    successor: &Constitution,
    declared: &Refinement,
    requests: &[Request],
    sections: &[(usize, usize, Vec<Option<usize>>)],
    modulus: Option<&Rat>,
) -> Result<Vec<Vec<ExactInterval>>, HnnError> {
    use rayon::prelude::*;
    let (before, after) = (
        placements_of(field, constitution, requests, declared)?,
        placements_of(field, successor, requests, declared)?,
    );
    Ok(sections
        .par_iter()
        .map(|(request, station, cells)| {
            let (old, new) = (
                before[*request].storage(*station, cells),
                after[*request].storage(*station, cells),
            );
            let mut moved: Vec<ExactInterval> = new
                .iter()
                .zip(&old)
                .map(|(n, o)| ExactInterval::point(n - o))
                .collect();
            if let Some(delta) = modulus.filter(|d| !d.is_zero()) {
                let delta = dyadic_enclosure(delta, JOINT_BITS);
                let derivative = before[*request].modulus_derivative(*station, cells);
                for (value, d) in moved.iter_mut().zip(derivative) {
                    if d.is_zero() {
                        continue;
                    }
                    *value = plus(value, &product(&dyadic_enclosure(&d, JOINT_BITS), &delta));
                }
            }
            moved
        })
        .collect())
}

/// [definition; agent-inferred, September 30] **A move's first-order reading** (module header, "The
/// first-order certificate"): the composition's bound `Σ_terms` enclosed (adoption needs its upper
/// end negative), the excess's piecewise bound (the terms above their level and `max(·, 0)` over
/// the boundary terms; its upper end sets the first trial step), the terms reading an unresolved
/// active member; and, as receipts only, each term's bound in the proposal's order (`None` for a
/// term with no resolved branch), aligned with [`ExecutedMove::sites`], and the leading
/// contributions' pairing `Σ c ⟨ĝ, Δz⟩`, the proposal's own gradient on the move.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FirstOrderReading {
    pub bound: ExactInterval,
    pub excess: ExactInterval,
    pub unresolved: usize,
    pub terms: Vec<Option<ExactInterval>>,
    pub leading: Option<ExactInterval>,
}

/// A contribution's weighted pairing `c ⟨ĝ, Δz⟩`, enclosed, with its storage move.
fn weighted_pairing(c: &Contribution, moved: &[ExactInterval]) -> ExactInterval {
    let d = paired(&c.covector, moved);
    product(&d, &ExactInterval::point(c.weight.clone()))
}

/// One lock-face term's bound on the moves: `Σ_(x≠t) θ_x · D_x⁺ + (θ_t − 1) · D_t⁻` enclosed over
/// the shares' enclosures (its upper end is `Σ sup(θ_x · D_x) + sup((θ_t − 1) · D_t)`); `None` when
/// some candidate has no resolved active member.
fn lock_term_bound(
    target: usize,
    candidates: &[(usize, Vec<Vec<ExactInterval>>, ExactInterval)],
    moves: &[Vec<ExactInterval>],
) -> Option<ExactInterval> {
    let one = Rat::one();
    let mut bound = nought();
    for (x, (section, members, share)) in candidates.iter().enumerate() {
        let pairings: Vec<ExactInterval> =
            members.iter().map(|m| paired(m, &moves[*section])).collect();
        let lower = pairings.iter().map(|p| p.lower.clone()).min()?;
        let upper = pairings.iter().map(|p| p.upper.clone()).max()?;
        let part = if x == target {
            product(
                &ExactInterval {
                    lower: &share.lower - &one,
                    upper: &share.upper - &one,
                },
                &ExactInterval::point(lower),
            )
        } else {
            product(share, &ExactInterval::point(upper))
        };
        bound = plus(&bound, &part);
    }
    Some(bound)
}

/// One order term's bound on the moves: `Σ_x ((θ_x − [x = r])/g_x)(a_top D_top − a_runner D_runner)`
/// enclosed, each `a` its joint enclosure and each `D` the hull of its active members' pairings with
/// its section's move; `None` when a sheet has no resolved active member.
fn order_term_bound(pieces: &[OrderPiece], moves: &[Vec<ExactInterval>]) -> Option<ExactInterval> {
    let hull = |end: &OrderEnd| -> Option<ExactInterval> {
        let pairings: Vec<ExactInterval> =
            end.members.iter().map(|m| paired(m, &moves[end.section])).collect();
        Some(ExactInterval {
            lower: pairings.iter().map(|p| p.lower.clone()).min()?,
            upper: pairings.iter().map(|p| p.upper.clone()).max()?,
        })
    };
    let minus = ExactInterval::point(-Rat::one());
    let mut bound = nought();
    for piece in pieces {
        let top = product(&piece.top.growth, &hull(&piece.top)?);
        let runner = product(&minus, &product(&piece.runner.growth, &hull(&piece.runner)?));
        bound = plus(&bound, &product(&ExactInterval::point(piece.ratio.clone()), &plus(&top, &runner)));
    }
    Some(bound)
}

/// [definition; agent-inferred, September 30] **The first-order reading of a proposal on the given
/// storage moves** (module header, "The first-order certificate"), a pure function of the moves:
/// each term's bound (the hinge's max over its active branches, a boundary term's hinged at zero;
/// the lock face's [`lock_term_bound`]); their sum; the excess's piecewise bound; the unresolved
/// terms; the leading contributions' pairing. The terms' bounds are co-present readings of one set
/// of moves (shared immutable input, one output each): they run on the host's cores and are summed
/// in the proposal's order.
fn first_order_on(proposal: &Proposal, moves: &[Vec<ExactInterval>]) -> FirstOrderReading {
    use rayon::prelude::*;
    let mut total = nought();
    let mut excess = nought();
    let mut terms = Vec::with_capacity(proposal.terms.len());
    let bounds: Vec<Option<ExactInterval>> = proposal
        .terms
        .par_iter()
        .map(|term| term_bound(term, moves))
        .collect();
    for (term, bound) in proposal.terms.iter().zip(bounds) {
        let Some(bound) = bound else {
            terms.push(None);
            continue;
        };
        total = plus(&total, &bound);
        let share = match term.kind {
            Excess::Solved => nought(),
            Excess::Above => bound.clone(),
            Excess::Boundary => positive_part(&bound),
        };
        excess = plus(&excess, &share);
        terms.push(Some(bound));
    }
    let mut leading = nought();
    for term in &proposal.terms {
        for c in &term.leading {
            leading = plus(&leading, &weighted_pairing(c, &moves[c.section]));
        }
    }
    FirstOrderReading {
        bound: total,
        excess,
        unresolved: proposal.unresolved_terms(),
        terms,
        leading: Some(leading),
    }
}

/// One term's bound on the moves: the hinge's max over its active branches (a term not certainly
/// above its level hinged at zero), the lock face's [`lock_term_bound`].
fn term_bound(term: &TermCertificate, moves: &[Vec<ExactInterval>]) -> Option<ExactInterval> {
    match &term.certificate {
        Certificate::Hinge(branches) => {
            let mut bound: Option<ExactInterval> = None;
            for branch in branches {
                let mut derivative = nought();
                for c in branch {
                    derivative = plus(&derivative, &weighted_pairing(c, &moves[c.section]));
                }
                bound = Some(match bound {
                    None => derivative,
                    Some(b) => ExactInterval {
                        lower: b.lower.max(derivative.lower),
                        upper: b.upper.max(derivative.upper),
                    },
                });
            }
            bound.map(|b| {
                if term.kind == Excess::Above {
                    b
                } else {
                    positive_part(&b)
                }
            })
        }
        Certificate::Lock {
            target, candidates, ..
        } => lock_term_bound(*target, candidates, moves),
        Certificate::Order(pieces) => order_term_bound(pieces, moves),
    }
}

/// The first-order reading of a proposal on the storage moves from a constitution to a successor
/// (with the modulus's first-order move when `modulus` is given: the joint unit direction).
#[allow(clippy::too_many_arguments)]
fn first_order(
    field: &Field,
    constitution: &Constitution,
    declared: &Refinement,
    requests: &[Request],
    proposal: &Proposal,
    successor: &Constitution,
    modulus: Option<&Rat>,
) -> Result<FirstOrderReading, HnnError> {
    let moves = section_moves(
        field,
        constitution,
        successor,
        declared,
        requests,
        &proposal.sections,
        modulus,
    )?;
    Ok(first_order_on(proposal, &moves))
}

// -------------------------------------------------------------------------------------------
// the committed move

/// [definition; agent-inferred, September 30] **Why a trial step is not adopted** (module header,
/// "The committed move"): each a condition of adoption that failed.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TrialRefusal {
    /// An entry of `E` past [`entry_bound`].
    EntryBound(Rat),
    /// A candidate crossing past its signed form (the re-read refused).
    Admission,
    /// A lock's Floquet certificate refused (the successor's own release refused).
    Floquet,
    /// A reading whose lower end is not positive (the comparison cannot be enclosed).
    Unsupported,
    /// The first-order descent not certified on the carried move.
    FirstOrder(ExactInterval),
    /// The fixed mask's composition not strictly lower by disjoint enclosures.
    NotBelow(ExactInterval),
    /// The fixed mask's composition lower, the successor's released code length not strictly below
    /// its opening state's plus the excursion ([`ReleaseExcursion`]; under strict descent, not
    /// strictly lower by disjoint enclosures): the step's jump took the released code length past
    /// what the interval admits.
    OwnNotBelow(ExactInterval),
    /// The constitution refused the deposit: its bit budget exceeded, or its storage growth not
    /// certified.
    Constitution(String),
}

/// [definition; agent-inferred, September 30] **One trial of the committed move**: its step, the
/// carried modulus, the carried move's largest entry change and the successor's largest entry, the
/// first-order bound on the carried move, the fixed mask's composition and excess at the successor,
/// the successor's own release comparison, the context change (the own reading less the mask's,
/// enclosed) where they were read, and its refusal, if any.
///
/// Receipts only (the move never reads them; the two counts' pin §5): `terms`, each term's
/// first-order bound on the carried move aligned with [`ExecutedMove::sites`], `leading`, the
/// leading contributions' pairing on it, `excess_bound`, the excess's piecewise bound, and `source`,
/// the carried source step's reading ([`SourceStep`]), where the trial reached them.
#[derive(Clone, Debug)]
pub struct Trial {
    pub step: Rat,
    pub modulus: Option<Rat>,
    pub moved: Rat,
    pub largest: Rat,
    pub first_order: Option<ExactInterval>,
    pub excess_bound: Option<ExactInterval>,
    pub value: Option<ExactInterval>,
    pub excess: Option<ExactInterval>,
    pub after: Option<BatchComparison>,
    pub change: Option<ExactInterval>,
    /// The readings the trial's re-read made (the own release and the mask), where it was read.
    pub readings: usize,
    pub refusal: Option<TrialRefusal>,
    pub terms: Option<Vec<Option<ExactInterval>>>,
    pub leading: Option<ExactInterval>,
    pub source: Option<SourceStep>,
}

/// [definition; agent-inferred, September 30] **Why the move was refused as a whole**.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MoveRefusal {
    /// No term moves the composition: nothing to descend.
    Nothing,
    /// The proposal's returns reached nothing.
    Unreached,
    /// This many terms of the certificate's support read an unresolved active member: the
    /// first-order certificate is not formed, and no trial can be adopted (the pin §13.4).
    Unresolved(usize),
    /// The joint unit move's first-order bound of the composition is not certified negative.
    NoDescent(ExactInterval),
    /// Every trial step failed a condition of adoption, halving down to a move below the lattice's
    /// resolution.
    Guards,
    /// The witness's metric ([`MoveMetric::Witness`]): no lock-face term reads the plane (the hinge
    /// has no lock), or some plane direction lies in the witness's kernel (`G` not positive
    /// definite): no lock reads it, so the witness defines no step.
    Invisible,
    /// The witness's metric: its step reverses the port's own unit move (`α ≤ 0`), which the
    /// source port's normal law does not define. The step `(α, β)` is returned.
    Reversed([Rat; 2]),
}

/// [definition; agent-inferred, September 30; the pin §2.6, §13.5] **Which bound set the first
/// trial step** ([`ladder_start`]).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LadderStart {
    /// The excess's first-order zero `X⁻/(−s_X⁺)`, at most the entry scale.
    FirstOrderZero,
    /// The entry scale `½/u`, below the excess's first-order zero.
    EntryScale,
    /// `X⁻ = 0`: no division by a zero excess; the entry scale alone. Nothing is solved by it.
    ExcessZero,
    /// `s_X⁺ ≥ 0`: the excess's linearization reaches no zero; the entry scale alone.
    ExcessRising,
    /// The witness's step `α` along the port's unit move ([`MoveMetric::Witness`]), at most the
    /// entry scale.
    Witness,
    /// The entry scale `½/u`, below the witness's step.
    WitnessEntryScale,
    /// The receiver's Gauss–Newton step (`η = 1`, [`MoveMetric::Kinetic`]), at most the entry scale.
    Kinetic,
    /// The entry scale `½/u`, below the Gauss–Newton step.
    KineticEntryScale,
}

/// [definition; agent-inferred, October 1; the
/// [witness's metric record](../../../../research/records/2026-10-01_THE_MOVES_METRIC_IS_ITS_WITNESSS_THE_LOCKS_FISHER_FORM_ON_THE_MOVES_PLANE.md)]
/// **Whose measurement sizes the joint move of `E` and `ρ`** ([`executed_move_in`]). The move
/// adjusts the source representation `E` (how incoming structure enters the receiving state) and
/// the memory transport `ρ` (how much of each earlier contribution a crossing carries) together;
/// the metric decides their relative sizes and how their interaction is counted.
/// - `Coordinate`: `E` by the source port's normal law, `ρ` by `−γ_ρ/Σ|∂z/∂ρ|²` in the storage
///   coordinates, no cross term (the move's law until October 1, kept as the control).
/// - `Witness`: both by the lock's own normalized reading pulled back onto the plane of the port's
///   unit move and `ρ`, its cross term counted ([`WitnessForm`]): the plane step `(α, β) = −G⁻¹g`,
///   the first trial step `α` (at most the entry scale) with `ρ` moving `β/α` per unit of `E`'s
///   step. The conditions of adoption are the same; only the direction and the first step differ. A
///   step's size is a constitutive change, not a velocity or an elapsed time.
/// - `Kinetic`: `E` alone, by the receiver's minimum-energy Gauss–Newton move over all of `E`
///   ([`KineticSolve`]), deposited by the normal law from the returns at the solve's reading weights;
///   `ρ` held. The first trial step is the Gauss–Newton step (`η = 1`), at most the entry scale.
/// - `KineticModulus`: `E` and `ρ` together, by the receiver's minimum-energy Gauss–Newton move over
///   both ([`KineticSolve`] with the modulus joined, [`ModulusCoupling`]): the readings' change is
///   the same Gauss–Newton change, and the storage-change mass splits it between `E` and `ρ`. `E`'s
///   part is deposited by the normal law from the returns at the solve's reading weights, each return
///   carrying the coupling's covector; `ρ` moves by the solve's `Δρ` per unit step, held at or below
///   the founding `ρ₀` (the one-turn alias bound, [`Constitution::founding_transport`]), or at the
///   incumbent's `ρ` where that already stands above it. Where `ρ` is at that bound and the solve
///   would raise it, the bound holds `ρ` and the move is `Kinetic`'s.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MoveMetric {
    Coordinate,
    Witness,
    Kinetic,
    KineticModulus,
}

/// [definition; agent-inferred, September 30; the pin §2.6, §13.5] **The first trial step**: from
/// the excess's lower end `X⁻`, the upper end `s_X⁺` of its piecewise directional derivative on the
/// joint unit move and the unit move's largest entry change `u`,
/// `η₀ = 2^⌊log₂ min(X⁻/(−s_X⁺), ½/u)⌋` when `X⁻ > 0` and `s_X⁺ < 0`; the entry scale `½/u` alone
/// otherwise (`1` when `u = 0`). A zero excess or a nonnegative slope never enters a division.
pub fn ladder_start(excess: &Rat, slope: &Rat, unit_largest: &Rat) -> (Rat, LadderStart) {
    let scale = if unit_largest.is_positive() {
        Rat::new(BigInt::one(), BigInt::from(2)) / unit_largest
    } else {
        Rat::one()
    };
    if !excess.is_positive() {
        return (power_below(&scale), LadderStart::ExcessZero);
    }
    if !slope.is_negative() {
        return (power_below(&scale), LadderStart::ExcessRising);
    }
    let zero = excess / -slope.clone();
    if zero <= scale {
        (power_below(&zero), LadderStart::FirstOrderZero)
    } else {
        (power_below(&scale), LadderStart::EntryScale)
    }
}

/// [definition; agent-inferred, September 30; the pin §13.4] **The certificate's refusal before
/// any step**: no term moves the composition ([`MoveRefusal::Nothing`]), or some term of the
/// certificate's support reads an unresolved active member ([`MoveRefusal::Unresolved`]): its
/// bound is never formed from its resolved members alone, for every composition and reading.
fn certificate_refusal(proposal: &Proposal) -> Option<MoveRefusal> {
    let unresolved = proposal.unresolved_terms();
    if unresolved > 0 {
        Some(MoveRefusal::Unresolved(unresolved))
    } else if proposal.contributions.is_empty() {
        Some(MoveRefusal::Nothing)
    } else {
        None
    }
}

/// [definition; agent-inferred, September 30; the pin §13.4] **The slope's refusal**, read on the
/// joint unit direction (the port's unit move with the modulus's least-squares move joined): the
/// move is refused, typed, only when the composition's joint first-order bound is not negative.
fn slope_refusal(joint: &FirstOrderReading) -> Option<MoveRefusal> {
    (!joint.bound.upper.is_negative()).then(|| MoveRefusal::NoDescent(joint.bound.clone()))
}

/// [measured-diagnostic; agent-inferred, September 30; the pin §13.7] **The persistence reads**:
/// the locks of the incumbent's releases, those whose lock face was solved at their refinement
/// (the rational test), those of them with a later lock in their section, and of those, re-read with
/// every later lock placed (the station open), the ones that stay solved and the ones that do not.
/// Those that do not are split (Astra's review, October 1): `reversed`, the strict test proved to
/// fail (a proved loss), and `uncertified`, the test undecided on the enclosures (lost
/// certification, not a proved reversal). `fall` is their sum, kept as gate A printed it.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Persistence {
    pub locks: usize,
    pub solved: usize,
    pub reread: usize,
    pub stay: usize,
    pub fall: usize,
    pub reversed: usize,
    pub uncertified: usize,
}

/// [definition; agent-inferred, September 30] **The committed move's receipt**: the declared
/// comparison; the incumbent's reading (the fixed mask's), the proposal's size (contributions,
/// returns, terms of the certificate's support, unresolved leading members, terms reading an
/// unresolved active member); the joint unit move's first-order bound of the composition and of its
/// excess; the first trial step; the modulus's reading; every trial; the adopted successor with its
/// carried step's reading, or the move's refusal; and the receipts: every term's site in the order of
/// every trial's `terms`, the unit move's largest entry change, the terms' counts and the
/// persistence reads.
#[derive(Clone, Debug)]
pub struct ExecutedMove {
    pub comparison: Comparison,
    /// Whose measurement sized the move ([`MoveMetric`]) and, under the witness, its form.
    pub metric: MoveMetric,
    pub witness: Option<WitnessForm>,
    /// Under the kinetic metric, the receiver's solve.
    pub kinetic: Option<KineticSolve>,
    pub before: BatchComparison,
    pub contributions: usize,
    pub returns: usize,
    pub terms: usize,
    pub unresolved: Vec<CovectorRefusal>,
    pub unresolved_branches: usize,
    pub slope: Option<ExactInterval>,
    /// The port's part of the unit move alone (`Δρ = 0`), a receipt: the slope's refusal reads
    /// `slope`.
    pub port_slope: Option<ExactInterval>,
    pub excess_slope: Option<ExactInterval>,
    pub start: Option<(Rat, LadderStart)>,
    pub modulus_slope: Option<Rat>,
    /// The modulus's storage curvature `G_ρ = Σ_c |∂z_c/∂ρ|²` and its least-squares unit move
    /// `−γ_ρ/G_ρ` (zero upward at `ρ = 1`), where the modulus was read.
    pub modulus_curvature: Option<Rat>,
    pub modulus_unit: Option<Rat>,
    /// `KineticModulus` at its bound: the joined solve whose upward `Δρ` the bound held (the move
    /// then is `E`'s alone, [`MoveMetric::KineticModulus`]); `None` where nothing was held.
    pub modulus_held: Option<KineticSolve>,
    /// The modulus's slope split by term kind ([`SlopeSplit`]), where the modulus was read.
    pub split: Option<SlopeSplit>,
    pub trials: Vec<Trial>,
    pub adopted: Option<(Constitution, SourceStep)>,
    pub refusal: Option<MoveRefusal>,
    pub sites: Vec<TermSite>,
    pub unit_largest: Option<Rat>,
    pub counts: TermCounts,
    pub persistence: Persistence,
}

/// The source port's largest absolute entry.
fn largest_entry(matrix: &ExactRatMatrix) -> Rat {
    matrix
        .entries()
        .iter()
        .map(|x| x.abs())
        .max()
        .unwrap_or_else(Rat::zero)
}

/// [definition; agent-inferred, September 30] **What a declared comparison reads at a carried
/// successor**: the fixed mask's composition and excess enclosed, the successor's own release
/// comparison where it was read, and the certificate that refused it (admission, Floquet, support),
/// if one did.
pub struct Reread {
    pub value: ExactInterval,
    pub excess: ExactInterval,
    pub comparison: Option<BatchComparison>,
    /// The readings made: the own release's and its terms', and the mask's sections it did not
    /// execute.
    pub readings: usize,
    pub refusal: Option<TrialRefusal>,
}

/// [definition; proved-derived, October 2] **The released code length compared between two
/// endpoint states** (`HNN/ExecutedComparison` §12; the record states each step). A step (one
/// deposition) changes the released code length by its change with the incumbent's commitments
/// held, continuous and certified at first order, plus the **jump** where a ring's all-or-nothing
/// commitment switches (`own_telescopes`; a trial's `change`, the released reading less the held
/// one, encloses it). Every admitted step certifies the held code length's fall (`NotBelow`,
/// unchanged). The jump is set by placement, not by the step's length, and only a later step can
/// repay it, so the released code length is compared between the two endpoint states of an
/// interval of the path: each successor's released code length strictly below the opening state's
/// lower end plus `height` ([`ReleaseExcursion::admits`], `excursion_enclosure`), and the closing
/// state, at most `W` admitted steps on, strictly below the opening's lower end less a certified
/// decrease `σ ≥ 0` ([`ReleaseExcursion::closes`]). An interval closes exactly when its held
/// decreases exceed its jumps by `σ` (`window_closes_iff`). The chain holds the opening state, the
/// interval's length and `σ`. [`ReleaseExcursion::monotone`] (the incumbent as opening state, no
/// excursion) is strict descent by disjoint enclosures, the former rule (`checkpoint_one_iff`).
///
/// The parameters, from the chain's laws:
/// - `height`: `None` inside an interval. The code length's range over the admitted states bounds
///   every excursion (`excursion_of_bounded`), so no per-step comparison of the released code length
///   is owed inside an interval; `Some(0)` with the incumbent as opening state is strict descent.
/// - `σ`: one receiver grain over the requests' decisions ([`ReleaseExcursion::grain`]). A decrease
///   below it is not a reading, and with it at most `(f 0 − m)/σ` intervals close
///   (`grain_windows_bounded`): the path releases at the grain.
/// - `W`: at least two steps, since a jump is read only by the step after it
///   (`one_move_closes_iff`), and at least `(F + σ)/d` for jumps `F` against a per-step certified
///   decrease of at most `d` (`window_length_lower`). No law fixes an upper end: a close is admitted
///   at any length (`HNN/ReleaseRun.close_at_any_length`), so [`release_run`] ends an interval only
///   at its close or a refusal, and a declared bound on work ends it incomplete.
///
/// A negative excursion states no condition (the opening state would breach its own) and a
/// negative decrease lets an opening state rise; both are refused, typed
/// ([`HnnError::ExcursionHeight`], [`HnnError::WindowDecrease`]).
///
/// **An interval that does not close is discarded whole.** The chain holds the opening state's
/// `Constitution` (one held state, not a tape) and discards every successor the interval admitted;
/// §12's `CheckpointGuard` indexes admitted states only, which is that law. No process of the rings
/// undoes a deposition: the discard is a selection among paths made by the receiver and has no
/// physical statement. A restart from the opening restores its whole continuing state, deposit
/// clock and carried Gram included, and repeats the same moves to the same end, so a refused
/// interval is reported, not restarted ([`RunEnd::Refused`]). The unchecked excursion is sound whatever its value: only
/// the chain reads an interval's states, and it releases only a closed interval's opening state,
/// which `NotBelow` on every step and the close certify.
///
/// **Why the range is finite.** A target's term `log((1 + a + r)/a)` grows without bound as its
/// reading `a` falls to zero (`lockFace_unbounded`), so the entry bound alone does not bound the
/// code length. It is bounded with a floor on every target's reading (`lockFace_le_of_floor`), and
/// the lattice supplies one: a growth over one period is zero or at least `1/Δ`
/// (`HNN/Floquet.integer_monodromy_floor`; [`crate::hnn::ring`]'s `growth_of`), and a zero target is
/// refused by [`lock_face`], so it is never admitted. [agent-inferred] The rivals' bound and a floor
/// uniform over a path (`Δ` varies with `E`) have no Lean statement yet (#62). This type holds only
/// the opening state's code length, which is all a step's comparison and the close read; the
/// interval's owner is [`release_run`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReleaseExcursion {
    /// The opening state's released code length; `None` is the incumbent's.
    pub checkpoint: Option<ExactInterval>,
    /// How far the released code length may rise above the opening state's inside the interval;
    /// `None`, unchecked (the code length's range bounds it).
    pub height: Option<Rat>,
}

impl ReleaseExcursion {
    /// Strict descent: the incumbent as opening state, no excursion.
    pub fn monotone() -> Self {
        Self {
            checkpoint: None,
            height: Some(Rat::zero()),
        }
    }

    /// An interval from a held opening state, the released code length unchecked until its close.
    pub fn from_checkpoint(checkpoint: ExactInterval) -> Self {
        Self {
            checkpoint: Some(checkpoint),
            height: None,
        }
    }

    /// **One receiver grain over the requests' decisions** (`σ`, in nats):
    /// `decisions · tolerance · ln 2`, read at the upper end of `ln 2`'s enclosure, so a closing
    /// interval certifies at least the grain.
    pub fn grain(
        decisions: usize,
        tolerance: &Rat,
    ) -> Result<Rat, crate::ratio::algebraic::ExactValueError> {
        let ln_two = ln_enclosure(&Rat::from_integer(BigInt::from(2)))?;
        Ok(Rat::from_integer(BigInt::from(decisions)) * tolerance * ln_two.upper)
    }

    /// The excursion's height checked: refused when held and negative
    /// ([`HnnError::ExcursionHeight`]).
    pub fn checked(&self) -> Result<&Self, HnnError> {
        match &self.height {
            Some(height) if height.is_negative() => Err(HnnError::ExcursionHeight {
                height: height.clone(),
            }),
            _ => Ok(self),
        }
    }

    /// The step's comparison of a successor's released code length with the opening state's:
    /// `own.upper < checkpoint.lower + height`, the opening state the incumbent (`before`) when none
    /// is held; every successor when the excursion is unchecked.
    pub fn admits(&self, before: &ExactInterval, own: &ExactInterval) -> bool {
        let checkpoint = self.checkpoint.as_ref().unwrap_or(before);
        match &self.height {
            Some(height) => own.upper < &checkpoint.lower + height,
            None => true,
        }
    }

    /// The interval's close: the released code length at its closing state strictly below the
    /// opening state's lower end less the certified decrease `σ`. A negative `σ` is refused
    /// ([`HnnError::WindowDecrease`]): it would let an interval close above its opening state, so
    /// the opening states could rise.
    pub fn closes(
        checkpoint: &ExactInterval,
        end: &ExactInterval,
        decrease: &Rat,
    ) -> Result<bool, HnnError> {
        if decrease.is_negative() {
            return Err(HnnError::WindowDecrease {
                decrease: decrease.clone(),
            });
        }
        Ok(end.upper < &checkpoint.lower - decrease)
    }
}

/// The trials' outcome: every trial, the adopted successor with its carried step, or the refusal.
type LadderOutcome = (Vec<Trial>, Option<(Constitution, SourceStep)>, Option<MoveRefusal>);

/// A carried move's first-order certificate: from the source port's move and the carried successor.
type FirstOrder<'a> =
    dyn Fn(&ExactRatMatrix, &Constitution) -> Result<FirstOrderReading, HnnError> + Sync + 'a;

/// [definition; agent-inferred, September 30] **The certified step's halving trials, one law for
/// every declared comparison** (module header, "The committed move"): from the first step (held so
/// that no entry of `E` moves by more than the founding's entry scale `½` in one move), halving
/// until the carried move falls below the lattice's resolution or moves no lattice coordinate; each
/// carried successor adopted only when all of these hold on it: the entry bound, the first-order
/// certificate on the carried move (`first`, negative), the successor's own certificates and the
/// fixed mask's value (`reread`) strictly lower by disjoint enclosures, and its own released code
/// length within the excursion ([`ReleaseExcursion`]).
#[allow(clippy::too_many_arguments)]
fn ladder(
    constitution: &Constitution,
    ring: usize,
    samples: &[Sample],
    before: &ExactInterval,
    start: Rat,
    unit_largest: &Rat,
    transport: Option<&Rat>,
    ceiling: &Rat,
    first: &FirstOrder<'_>,
    reread: &(dyn Fn(&Constitution) -> Result<Reread, HnnError> + Sync),
    excursion: &ReleaseExcursion,
) -> Result<LadderOutcome, HnnError> {
    let source = constitution
        .source_port(ring)
        .ok_or(HnnError::MissingSourcePort { ring })?
        .clone();
    let mut step = start;
    let lattice_unit = constitution
        .lattice(crate::hnn::constitution::Locus::SourcePort(ring))?
        .unit();
    let two = Rat::from_integer(BigInt::from(2));
    let mut trials = Vec::new();
    loop {
        // The lattice's resolution ends the halvings: below it every entry of the carried move
        // moves by less than half a lattice unit (`HNN/ReleaseRun.below_floor_one_coordinate`),
        // and the first step's `η₀ · 2u ≤ 1` bounds the trials by `log₂(1/λ) + 1`
        // (`attempted_halvings_le_lattice`). No count of trials is declared beside it.
        if step.is_zero() || &step * unit_largest * &two < lattice_unit {
            return Ok((trials, None, Some(MoveRefusal::Guards)));
        }
        let mut trial = Trial {
            step: step.clone(),
            modulus: None,
            moved: Rat::zero(),
            largest: Rat::zero(),
            first_order: None,
            excess_bound: None,
            value: None,
            excess: None,
            after: None,
            change: None,
            readings: 0,
            refusal: None,
            terms: None,
            leading: None,
            source: None,
        };
        let stepped = match constitution.stepped_source(ring, samples, &step) {
            Ok(Some(stepped)) => stepped,
            Ok(None) => return Ok((trials, None, Some(MoveRefusal::Unreached))),
            Err(error @ (HnnError::ConstitutionBudget { .. } | HnnError::UncertifiedStorage)) => {
                trial.refusal = Some(TrialRefusal::Constitution(error.to_string()));
                trials.push(trial);
                step /= &two;
                continue;
            }
            Err(error) => return Err(error),
        };
        let (successor, reading) = stepped;
        trial.source = Some(reading.clone());
        // The transport modulus's part of the move (module header, "The committed move"): `ρ + ηΔρ`
        // held within `[ρ/2, ceiling]` and read on the source port's lattice, nearest. The ceiling is
        // the one-turn alias bound, or the incumbent's modulus where that stands above it,
        // `max(ρ₀, ρ)`, under every metric.
        let (successor, modulus_moved) = match transport {
            Some(unit) if !unit.is_zero() => {
                let modulus = constitution.transport(ring);
                let target = (&modulus + &step * unit)
                    .max(&modulus / &two)
                    .min(ceiling.clone());
                let carried = ((&target / &lattice_unit)
                    + Rat::new(BigInt::one(), BigInt::from(2)))
                .floor()
                    * &lattice_unit;
                let carried = carried.min(ceiling.clone()).max(lattice_unit.clone());
                trial.modulus = Some(carried.clone());
                let moved_modulus = carried != modulus;
                (successor.with_transport(ring, carried)?, moved_modulus)
            }
            _ => (successor, false),
        };
        let moved = successor
            .source_port(ring)
            .ok_or(HnnError::MissingSourcePort { ring })?
            .subtract(&source)?;
        trial.moved = largest_entry(&moved);
        trial.largest = reading.largest.clone();
        if trial.moved.is_zero() && !modulus_moved {
            return Ok((trials, None, Some(MoveRefusal::Guards)));
        }
        if reading.largest > entry_bound() {
            trial.refusal = Some(TrialRefusal::EntryBound(reading.largest.clone()));
            trials.push(trial);
            step /= &two;
            continue;
        }
        let first_reading = first(&moved, &successor)?;
        let bound = first_reading.bound;
        trial.terms = Some(first_reading.terms);
        trial.leading = first_reading.leading;
        trial.excess_bound = Some(first_reading.excess);
        trial.first_order = Some(bound.clone());
        if !bound.upper.is_negative() {
            trial.refusal = Some(TrialRefusal::FirstOrder(bound));
            trials.push(trial);
            step /= &two;
            continue;
        }
        let read = reread(&successor)?;
        trial.value = Some(read.value.clone());
        trial.excess = Some(read.excess.clone());
        trial.change = read.comparison.as_ref().map(|own| ExactInterval {
            lower: &own.value.lower - &read.value.upper,
            upper: &own.value.upper - &read.value.lower,
        });
        trial.readings = read.readings;
        trial.after = read.comparison;
        trial.refusal = match (read.refusal, &trial.after) {
            (Some(refusal), _) => Some(refusal),
            (None, _) if read.value.upper >= before.lower => {
                Some(TrialRefusal::NotBelow(read.value.clone()))
            }
            (None, Some(own)) if excursion.admits(before, &own.value) => None,
            (None, Some(own)) => Some(TrialRefusal::OwnNotBelow(own.value.clone())),
            (None, None) => Some(TrialRefusal::Unsupported),
        };
        let adopted = trial.refusal.is_none();
        trials.push(trial);
        if adopted {
            return Ok((trials, Some((successor, reading)), None));
        }
        step /= &two;
    }
}

/// [definition; agent-inferred, September 30; the pin §13.1] **The successor's two readings**: its
/// own release compared under the declared comparison (its refusals: an inadmissible crossing, a
/// refused lock certificate, an unsupported reading), and the fixed incumbent mask's terms re-read at
/// the successor, each site's candidates taken from the own release's refinement at the same section
/// when it executed one (the same reading exactly), else read there.
#[allow(clippy::too_many_arguments)]
fn executed_reread(
    field: &Field,
    successor: &Constitution,
    requests: &[Request],
    declared: &Refinement,
    bank: &ReceivingBank,
    grain: u32,
    comparison: Comparison,
    mask: &[Vec<TermSite>],
) -> Result<Reread, HnnError> {
    let joined = mask_reads(field, successor, requests, declared, bank, grain, comparison, mask);
    let joined = match joined {
        Ok(joined) => joined,
        Err(HnnError::UncertifiedResonator { .. }) => {
            return Ok(Reread {
                value: nought(),
                excess: nought(),
                comparison: None,
                readings: 0,
                refusal: Some(TrialRefusal::Admission),
            });
        }
        Err(HnnError::NonpositiveDeclaration) => {
            return Ok(Reread {
                value: nought(),
                excess: nought(),
                comparison: None,
                readings: 0,
                refusal: Some(TrialRefusal::Unsupported),
            });
        }
        Err(error) => return Err(error),
    };
    let (mut value, mut excess, mut made) = (nought(), nought(), 0);
    let mut own = Vec::with_capacity(joined.len());
    for (compared, _, v, x, m) in joined {
        value = plus(&value, &v);
        excess = plus(&excess, &x);
        made += m;
        own.push(compared);
    }
    let own = batch_of(comparison, own);
    let readings = own.readings + made;
    let floquet = own
        .requests
        .iter()
        .any(|r| r.generation.as_ref().is_some_and(|g| g.uncertified.is_some()));
    Ok(Reread {
        value,
        excess,
        comparison: Some(own),
        readings,
        refusal: floquet.then_some(TrialRefusal::Floquet),
    })
}

/// Each request's own release at the successor and the fixed mask's terms re-read there (each
/// site's candidates from the own release's refinement at the same section when it executed one,
/// else read there), with the mask's composition, excess and the readings made.
#[allow(clippy::too_many_arguments, clippy::type_complexity)]
fn mask_reads(
    field: &Field,
    successor: &Constitution,
    requests: &[Request],
    declared: &Refinement,
    bank: &ReceivingBank,
    grain: u32,
    comparison: Comparison,
    mask: &[Vec<TermSite>],
) -> Result<Vec<(RequestComparison, Vec<TermReading>, ExactInterval, ExactInterval, usize)>, HnnError> {
    use rayon::prelude::*;
    let alphabet = field.alphabet();
    let termination = declared.termination();
    let read = |amplitudes: &[GaussianRat]| bank.read_turn(amplitudes, grain);
    requests
        .par_iter()
        .enumerate()
        .map(|(index, request)| {
            let (own, refinements, placement) =
                compare_request(field, successor, index, request, declared, bank, grain, comparison)?;
            let sites = mask[index].clone();
            let (reads, made) = site_reads(&sites, &refinements, &placement, alphabet, &read)?;
            let order_terms = match comparison.composition {
                Composition::LockOrder => {
                    order_terms(&sites, &reads, &request.targets, comparison.reading)?
                }
                _ => Vec::new(),
            };
            let (terms, mut value, mut excess) =
                terms_of(comparison.composition, &request.targets, sites, &reads, termination)?;
            for order in &order_terms {
                value = plus(&value, &order.value);
                excess = plus(&excess, &order.excess);
            }
            Ok((own, terms, value, excess, made))
        })
        .collect()
}

/// [measured-diagnostic; agent-inferred, October 1; the
/// [margins record](../../../../research/records/2026-10-01_THE_DECISION_MARGINS_THROUGH_THE_ACCEPTED_MOVE.md)]
/// **An accepted move read decision by decision**: from `before` to `after`, the incumbent's
/// comparison at `before`; at `after`, the own release and every incumbent term re-read on its own
/// fixed section (the mask, so a term's change is the constitution's alone); and each incumbent
/// term's first-order bound on the exact storage move from `before` to `after` (the proposal's own
/// certificate, `None` for a term with no resolved branch), aligned with `sites`, the proposal's
/// terms. The mask's terms align with the incumbent's; the own release's terms are its own sites.
/// No move is made.
pub struct MoveMargins {
    pub before: BatchComparison,
    pub after: BatchComparison,
    pub mask: Vec<Vec<TermReading>>,
    pub first_order: Vec<Option<ExactInterval>>,
    pub sites: Vec<TermSite>,
}

/// [measured-diagnostic] An accepted move read decision by decision ([`MoveMargins`]).
#[allow(clippy::too_many_arguments)]
pub fn move_margins(
    field: &Field,
    before: &Constitution,
    after: &Constitution,
    requests: &[Request],
    declared: &Refinement,
    bank: &ReceivingBank,
    grain: u32,
    comparison: Comparison,
) -> Result<MoveMargins, HnnError> {
    let (incumbent, reads) = incumbent(field, before, requests, declared, bank, grain, comparison)?;
    let proposal = propose(comparison.composition, &incumbent, &reads);
    drop(reads);
    let first = first_order(field, before, declared, requests, &proposal, after, None)?;
    let mask: Vec<Vec<TermSite>> = incumbent
        .requests
        .iter()
        .map(|r| r.terms.iter().map(|t| t.site.clone()).collect())
        .collect();
    let joined = mask_reads(field, after, requests, declared, bank, grain, comparison, &mask)?;
    let (own, terms): (Vec<RequestComparison>, Vec<Vec<TermReading>>) =
        joined.into_iter().map(|(o, t, ..)| (o, t)).unzip();
    Ok(MoveMargins {
        before: incumbent,
        after: batch_of(comparison, own),
        mask: terms,
        first_order: first.terms,
        sites: proposal.terms.iter().map(|t| t.site.clone()).collect(),
    })
}

/// **The persistence reads at a constitution** ([`Persistence`]): every lock of every open request's
/// release, its lock face at its refinement, and each solved lock with a later lock in its section
/// re-read with every other lock of the release placed.
fn persistence(
    field: &Field,
    constitution: &impl ConstitutionRead,
    requests: &[Request],
    declared: &Refinement,
    bank: &ReceivingBank,
    grain: u32,
    before: &BatchComparison,
) -> Result<Persistence, HnnError> {
    use rayon::prelude::*;
    let alphabet = field.alphabet();
    let read: Vec<Persistence> = requests
        .par_iter()
        .zip(&before.requests)
        .map(|(request, compared)| -> Result<Persistence, HnnError> {
            let mut out = Persistence::default();
            let Some(generation) = &compared.generation else {
                return Ok(out);
            };
            let mut section: Vec<Option<usize>> = vec![None; declared.stations()];
            for (station, class, ..) in &generation.decisions {
                section[*station] = Some(*class);
            }
            let placement =
                BankPlacement::of(field, constitution, &request.current, &request.moment, declared)?;
            for order in &compared.orders {
                for &station in &order.locked {
                    out.locks += 1;
                    let solved = compared.stations.iter().any(|s| {
                        s.context == Some(order.context)
                            && s.station == station
                            && s.solved == Predicate::Holds
                    });
                    if !solved {
                        continue;
                    }
                    out.solved += 1;
                    let placed_then = compared
                        .orders
                        .iter()
                        .filter(|o| o.context <= order.context)
                        .map(|o| o.locked.len())
                        .sum::<usize>();
                    let placed_all = section.iter().filter(|c| c.is_some()).count();
                    if placed_all <= placed_then {
                        continue;
                    }
                    out.reread += 1;
                    let mut cells = section.clone();
                    cells[station] = None;
                    let joints: Vec<Growth> = (0..alphabet)
                        .map(|class| {
                            let mut with = cells.clone();
                            with[station] = Some(class);
                            Ok(bank
                                .read_turn(&turn(&placement.storage(station, &with)), grain)?
                                .joint)
                        })
                        .collect::<Result<_, HnnError>>()?;
                    let lock = lock_face(&joints, request.targets[station])?;
                    match lock.solved {
                        Predicate::Holds => out.stay += 1,
                        Predicate::Fails => {
                            out.fall += 1;
                            out.reversed += 1;
                        }
                        Predicate::Undecided => {
                            out.fall += 1;
                            out.uncertified += 1;
                        }
                    }
                }
            }
            Ok(out)
        })
        .collect::<Result<_, HnnError>>()?;
    Ok(read.into_iter().fold(Persistence::default(), |a, b| Persistence {
        locks: a.locks + b.locks,
        solved: a.solved + b.solved,
        reread: a.reread + b.reread,
        stay: a.stay + b.stay,
        fall: a.fall + b.fall,
        reversed: a.reversed + b.reversed,
        uncertified: a.uncertified + b.uncertified,
    }))
}

/// **The committed move of `E` and `ρ` on a declared comparison** (module header, "The committed
/// move"): the requests read at the incumbent with every term's candidates' covectors, the proposal
/// and its returns, the modulus's least-squares unit move, the joint unit move's first order read
/// before any refusal, the first trial step from the excess, then the certified step's halving
/// trials ([`ladder`]), each carried successor re-read on the fixed incumbent mask and on its own
/// release, and adopted only when every condition of adoption holds. The targets are validated (one
/// per station, each a class of the chart); an unsupported reading at the incumbent refuses with
/// its typed error.
pub fn executed_move(
    field: &Field,
    constitution: &Constitution,
    requests: &[Request],
    declared: &Refinement,
    bank: &ReceivingBank,
    grain: u32,
    comparison: Comparison,
) -> Result<ExecutedMove, HnnError> {
    executed_move_in(
        field,
        constitution,
        requests,
        declared,
        bank,
        grain,
        comparison,
        MoveMetric::Coordinate,
    )
}

/// **The committed move under a declared metric** ([`MoveMetric`]; [`executed_move`] is the
/// coordinate metric's): the same proposal, conditions of adoption, halving trials and receipts,
/// the joint direction and the first trial step sized by the declared metric.
#[allow(clippy::too_many_arguments)]
pub fn executed_move_in(
    field: &Field,
    constitution: &Constitution,
    requests: &[Request],
    declared: &Refinement,
    bank: &ReceivingBank,
    grain: u32,
    comparison: Comparison,
    metric: MoveMetric,
) -> Result<ExecutedMove, HnnError> {
    executed_move_guarded(
        field,
        constitution,
        requests,
        declared,
        bank,
        grain,
        comparison,
        metric,
        &ReleaseExcursion::monotone(),
    )
}

/// **The committed move under a declared metric and an excursion of the released code length**
/// ([`ReleaseExcursion`]; [`executed_move_in`] is strict descent's): the same proposal, conditions
/// of adoption, halving trials and receipts, the own released code length admitted within the
/// excursion. A negative height is refused before any reading ([`HnnError::ExcursionHeight`]).
#[allow(clippy::too_many_arguments)]
pub fn executed_move_guarded(
    field: &Field,
    constitution: &Constitution,
    requests: &[Request],
    declared: &Refinement,
    bank: &ReceivingBank,
    grain: u32,
    comparison: Comparison,
    metric: MoveMetric,
    excursion: &ReleaseExcursion,
) -> Result<ExecutedMove, HnnError> {
    let excursion = excursion.checked()?;
    let ring = declared.ring();
    let composition = comparison.composition;
    let (before, reads) = incumbent(field, constitution, requests, declared, bank, grain, comparison)?;
    // The fixed incumbent mask: every term's section, transient within the move.
    let mask: Vec<Vec<TermSite>> = before
        .requests
        .iter()
        .map(|r| r.terms.iter().map(|t| t.site.clone()).collect())
        .collect();
    let proposal = propose(composition, &before, &reads);
    drop(reads);
    let persistence = persistence(field, constitution, requests, declared, bank, grain, &before)?;
    let unresolved_terms = proposal.unresolved_terms();
    let refused = certificate_refusal(&proposal);
    let mut receipt = ExecutedMove {
        comparison,
        metric,
        witness: None,
        kinetic: None,
        counts: before.counts(declared.stations()),
        before: before.clone(),
        contributions: proposal.contributions.len(),
        returns: 0,
        terms: proposal.terms.len(),
        unresolved: proposal.unresolved.clone(),
        unresolved_branches: unresolved_terms,
        slope: None,
        port_slope: None,
        excess_slope: None,
        start: None,
        modulus_slope: None,
        modulus_curvature: None,
        modulus_unit: None,
        modulus_held: None,
        split: None,
        trials: Vec::new(),
        adopted: None,
        refusal: None,
        sites: proposal.terms.iter().map(|t| t.site.clone()).collect(),
        unit_largest: None,
        persistence,
    };
    if refused.is_some() {
        receipt.refusal = refused;
        return Ok(receipt);
    }
    let (samples, step) = unit_step(field, constitution, declared, requests, &proposal)?;
    receipt.returns = samples.len();
    let Some(UnitStep {
        unit,
        unit_move,
        gamma,
        curvature,
        modulus_unit,
    }) = step
    else {
        receipt.refusal = Some(MoveRefusal::Unreached);
        return Ok(receipt);
    };
    // The kinetic metric's deposition: the same normal law, from the returns at the solve's
    // reading weights.
    // The bound on `ρ` under every metric that moves it: the founding's one-turn alias bound `ρ₀`,
    // or the incumbent's modulus where it already stands above it (no move lifts `ρ` past `ρ₀`;
    // October 2: the coordinate and witness moves were held only by the passive `1`).
    let joined = metric == MoveMetric::KineticModulus;
    let ceiling = constitution
        .founding_transport(field, ring)?
        .max(constitution.transport(ring).clone());
    let (samples, unit, unit_move, kinetic_modulus) = if metric == MoveMetric::Kinetic || joined {
        let mut solve =
            kinetic_solve(field, constitution, declared, requests, &proposal, &samples, None, joined)?;
        // At the bound an upward `Δρ` is held, and the least-energy move is `E`'s alone.
        if solve
            .as_ref()
            .and_then(|s| s.modulus.as_ref())
            .is_some_and(|x| x.is_positive() && constitution.transport(ring) >= ceiling)
        {
            receipt.modulus_held = solve;
            solve = kinetic_solve(field, constitution, declared, requests, &proposal, &samples, None, false)?;
        }
        let Some(solve) = solve else {
            receipt.refusal = Some(MoveRefusal::Invisible);
            return Ok(receipt);
        };
        let weighted = kinetic_contributions(&proposal, &solve);
        let modulus = solve.modulus.clone();
        receipt.kinetic = Some(solve);
        let port = constitution
            .source_port(ring)
            .ok_or(HnnError::MissingSourcePort { ring })?
            .clone();
        let samples = returns_coupled(
            field,
            constitution,
            declared,
            requests,
            &weighted,
            modulus.as_ref().map(|x| (x, &port)),
        )?;
        let Some((unit, _)) = constitution.stepped_source(ring, &samples, &Rat::one())? else {
            receipt.refusal = Some(MoveRefusal::Unreached);
            return Ok(receipt);
        };
        let unit_move = unit
            .source_port(ring)
            .ok_or(HnnError::MissingSourcePort { ring })?
            .subtract(&constitution.source_port(ring).ok_or(HnnError::MissingSourcePort { ring })?.clone())?;
        (samples, unit, unit_move, modulus)
    } else {
        (samples, unit, unit_move, None)
    };
    let unit_largest = largest_entry(&unit_move);
    receipt.unit_largest = Some(unit_largest.clone());
    receipt.modulus_slope = Some(gamma);
    receipt.modulus_curvature = Some(curvature);
    receipt.split = Some(slope_split(field, constitution, declared, requests, &proposal)?);
    // The declared metric's direction: the coordinate law's `Δρ`, or the witness's `β/α` per unit
    // of `E`'s step with its start `α`.
    let (modulus_unit, witness_start) = match metric {
        MoveMetric::Coordinate => (modulus_unit, None),
        MoveMetric::Kinetic => (Rat::zero(), Some(Rat::one())),
        MoveMetric::KineticModulus => (kinetic_modulus.unwrap_or_else(Rat::zero), Some(Rat::one())),
        MoveMetric::Witness => {
            let form = plane_form(field, constitution, declared, requests, &proposal, &unit)?;
            let step = form.as_ref().and_then(WitnessForm::step);
            receipt.witness = form;
            let Some([alpha, beta]) = step.and_then(|s| <[Rat; 2]>::try_from(s).ok()) else {
                receipt.refusal = Some(MoveRefusal::Invisible);
                return Ok(receipt);
            };
            if !alpha.is_positive() {
                receipt.refusal = Some(MoveRefusal::Reversed([alpha, beta]));
                return Ok(receipt);
            }
            // The witness's exact step stays in its form (the receipt); the trials carry it at the
            // face grain, toward zero (October 1: carried exactly, `α` reached a 1229-digit
            // denominator). Every trial is a carried successor read whole under every condition of
            // adoption, so the grain moves which step is tried, never what certifies it; the
            // residual is the form's exact step less the held one.
            let held = |x: Rat| {
                if x.is_negative() {
                    -significant(&-x, FACE_BITS, false)
                } else {
                    significant(&x, FACE_BITS, false)
                }
            };
            let unit = if constitution.transport(ring).is_one() && beta.is_positive() {
                Rat::zero()
            } else {
                held(&beta / &alpha)
            };
            (unit, Some(held(alpha)))
        }
    };
    receipt.modulus_unit = Some(modulus_unit.clone());
    // The slope's refusal, repaired (the pin §13.4): the slope is read on the joint unit direction,
    // the modulus's storage move joined, before any refusal. The port's part alone is a receipt.
    let port = first_order(field, constitution, declared, requests, &proposal, &unit, None)?;
    receipt.port_slope = Some(port.bound);
    let joint = first_order(
        field,
        constitution,
        declared,
        requests,
        &proposal,
        &unit,
        Some(&modulus_unit),
    )?;
    receipt.slope = Some(joint.bound.clone());
    receipt.excess_slope = Some(joint.excess.clone());
    if let Some(refusal) = slope_refusal(&joint) {
        receipt.refusal = Some(refusal);
        return Ok(receipt);
    }
    let (start, kind) = match witness_start {
        None => ladder_start(&before.excess.lower, &joint.excess.upper, &unit_largest),
        Some(alpha) => {
            let scale = if unit_largest.is_positive() {
                Rat::new(BigInt::one(), BigInt::from(2)) / &unit_largest
            } else {
                Rat::one()
            };
            let kinetic = matches!(metric, MoveMetric::Kinetic | MoveMetric::KineticModulus);
            match (alpha <= scale, kinetic) {
                (true, false) => (alpha, LadderStart::Witness),
                (false, false) => (power_below(&scale), LadderStart::WitnessEntryScale),
                (true, true) => (alpha, LadderStart::Kinetic),
                (false, true) => (power_below(&scale), LadderStart::KineticEntryScale),
            }
        }
    };
    receipt.start = Some((start.clone(), kind));
    let first = |_: &ExactRatMatrix, successor: &Constitution| {
        first_order(field, constitution, declared, requests, &proposal, successor, None)
    };
    let reread = |successor: &Constitution| {
        executed_reread(field, successor, requests, declared, bank, grain, comparison, &mask)
    };
    let (trials, adopted, refusal) = ladder(
        constitution,
        ring,
        &samples,
        &before.value,
        start,
        &unit_largest,
        Some(&modulus_unit),
        &ceiling,
        &first,
        &reread,
        excursion,
    )?;
    receipt.trials = trials;
    receipt.adopted = adopted;
    receipt.refusal = refusal;
    Ok(receipt)
}

/// [definition; proved-derived, October 2; the
/// [run-end record](../../../../research/records/2026-10-02_A_RUN_CLOSES_ON_A_CONDITION_NOT_A_LENGTH_AND_THE_HALVINGS_END_AT_THE_LATTICE.md)
/// §2, §4] **How a release run ended** ([`release_run`]).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RunEnd {
    /// The run closed: after `moves` adopted moves the closing state's own released code length
    /// `end` lies strictly below the opening's lower end less `σ` ([`ReleaseExcursion::closes`]).
    Closed {
        moves: usize,
        state: Box<Constitution>,
        end: ExactInterval,
    },
    /// The move from the state after `moves` adopted moves was refused, typed. The run ends: a
    /// restart from the opening restores the opening's whole continuing state and repeats the same
    /// moves to the same refusal (record §1).
    Refused {
        moves: usize,
        refusal: Option<MoveRefusal>,
    },
    /// The declared work cap was reached, or the caller stopped the run, after `moves` adopted moves
    /// with no close and no refusal: the run is incomplete, never refused. `state` is the last
    /// adopted state, from which the run can be continued with the same opening.
    Incomplete {
        moves: usize,
        state: Box<Constitution>,
    },
}

/// A release run's receipt: the opening's released code length, the decrease `σ` and the end.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReleaseRun {
    pub opening: ExactInterval,
    pub decrease: Rat,
    pub end: RunEnd,
}

/// [definition; proved-derived, October 2; the
/// [run-end record](../../../../research/records/2026-10-02_A_RUN_CLOSES_ON_A_CONDITION_NOT_A_LENGTH_AND_THE_HALVINGS_END_AT_THE_LATTICE.md)
/// §2, §4] **The release run: from an opening state, committed moves until the run closes or a move
/// is refused** ([`ReleaseExcursion`]'s chain owner). Each move is [`executed_move_guarded`] under the
/// declared metric with the excursion unchecked from the opening state
/// ([`ReleaseExcursion::from_checkpoint`]); after each adopted move the run reads its close on the
/// adopted trial's own release, `end.upper < opening.lower − σ`.
///
/// The repayment law fixes no length: a close is admitted at any length (Lean
/// `HNN/ReleaseRun.close_at_any_length`), so the run ends only at a close or a refusal. `cap`, at
/// most that many adopted moves, is a declared bound on work, and `each` (called with the move's index from zero and its receipt) may
/// stop the run at its own deadline by returning `false`; either ends the run
/// [`RunEnd::Incomplete`], reported as such and never as a refusal. `σ` is the declared decrease, at
/// least one receiver grain over the decisions ([`ReleaseExcursion::grain`]); a negative `σ` is
/// refused before any reading ([`HnnError::WindowDecrease`]).
#[allow(clippy::too_many_arguments)]
pub fn release_run(
    field: &Field,
    opening: &Constitution,
    requests: &[Request],
    declared: &Refinement,
    bank: &ReceivingBank,
    grain: u32,
    comparison: Comparison,
    metric: MoveMetric,
    decrease: &Rat,
    cap: Option<std::num::NonZeroUsize>,
    mut each: impl FnMut(usize, &ExecutedMove) -> bool,
) -> Result<ReleaseRun, HnnError> {
    if decrease.is_negative() {
        return Err(HnnError::WindowDecrease {
            decrease: decrease.clone(),
        });
    }
    let mut state = opening.clone();
    let mut excursion = ReleaseExcursion {
        checkpoint: None,
        height: None,
    };
    let mut moves = 0;
    loop {
        let moved = executed_move_guarded(
            field, &state, requests, declared, bank, grain, comparison, metric, &excursion,
        )?;
        let opening_value = excursion
            .checkpoint
            .get_or_insert_with(|| moved.before.value.clone())
            .clone();
        let go_on = each(moves, &moved);
        let Some((successor, _)) = moved.adopted else {
            return Ok(ReleaseRun {
                opening: opening_value,
                decrease: decrease.clone(),
                end: RunEnd::Refused {
                    moves,
                    refusal: moved.refusal,
                },
            });
        };
        moves += 1;
        // The adopted trial's own release: the successor's released code length (an adopted trial
        // always carries it; a trial without it is refused `Unsupported`).
        let end = moved
            .trials
            .last()
            .and_then(|t| t.after.as_ref())
            .map(|own| own.value.clone())
            .expect("an adopted trial carries its own release");
        if ReleaseExcursion::closes(&opening_value, &end, decrease)? {
            return Ok(ReleaseRun {
                opening: opening_value,
                decrease: decrease.clone(),
                end: RunEnd::Closed {
                    moves,
                    state: Box::new(successor),
                    end,
                },
            });
        }
        state = successor;
        if !go_on || cap.is_some_and(|cap| moves >= cap.get()) {
            return Ok(ReleaseRun {
                opening: opening_value,
                decrease: decrease.clone(),
                end: RunEnd::Incomplete {
                    moves,
                    state: Box::new(state),
                },
            });
        }
    }
}

/// **The committed move's unit step, formed and not taken** ([`executed_move`] and
/// [`unit_direction`] read it from this one function): the proposal's returns at `E` ([`returns`]),
/// the source port's normal law prepared and stepped at `η = 1` (`Constitution::stepped_source`) with
/// its move `ΔE`, and the transport modulus's unit move, the least-squares fit of its storage moves
/// to the proposal's descent covectors, `Δρ = −γ_ρ / Σ_c |∂z_c/∂ρ|²`, none upward from `ρ = 1`.
/// `None` beside the returns when they reach nothing.
struct UnitStep {
    unit: Constitution,
    unit_move: ExactRatMatrix,
    gamma: Rat,
    curvature: Rat,
    modulus_unit: Rat,
}

fn unit_step(
    field: &Field,
    constitution: &Constitution,
    declared: &Refinement,
    requests: &[Request],
    proposal: &Proposal,
) -> Result<(Vec<Sample>, Option<UnitStep>), HnnError> {
    let ring = declared.ring();
    let samples = returns(field, constitution, declared, requests, &proposal.contributions)?;
    let source = constitution
        .source_port(ring)
        .ok_or(HnnError::MissingSourcePort { ring })?
        .clone();
    let Some((unit, _)) = constitution.stepped_source(ring, &samples, &Rat::one())? else {
        return Ok((samples, None));
    };
    let unit_move = unit
        .source_port(ring)
        .ok_or(HnnError::MissingSourcePort { ring })?
        .subtract(&source)?;
    let (gamma, curvature) =
        modulus_normal(field, constitution, declared, requests, proposal)?;
    let modulus_unit = if gamma.is_zero() || !curvature.is_positive() {
        Rat::zero()
    } else {
        let unit = -&gamma / &curvature;
        if unit.is_positive() && constitution.transport(ring).is_one() {
            Rat::zero()
        } else {
            unit
        }
    };
    Ok((
        samples,
        Some(UnitStep {
            unit,
            unit_move,
            gamma,
            curvature,
            modulus_unit,
        }),
    ))
}

/// [measured-diagnostic; agent-inferred, October 1; the
/// [direction probe's pin](../../../../research/records/2026-10-01_THE_NATIVE_DIRECTION_PINNED_BEFORE_ITS_RUN.md)]
/// **The committed move's unit step at a constitution, not taken**: the incumbent's comparison and,
/// where [`executed_move`] would form its step, the step exactly as it forms it ([`unit_step`]): the
/// source port's unit move `ΔE` (the normal law's step at `η = 1`, through its solved chart), the
/// plain pullback of the same returns `G = Σ_t w_t g_t f_tᵀ` (the step before the chart: `ΔE` with
/// `X̂` replaced by the identity), and the modulus's slope, curvature and least-squares unit move.
/// No step is taken; nothing is retained.
#[derive(Clone, Debug)]
pub struct DirectionReading {
    pub before: BatchComparison,
    pub refusal: Option<MoveRefusal>,
    pub unit_move: Option<ExactRatMatrix>,
    pub pullback: Option<ExactRatMatrix>,
    pub modulus_slope: Option<Rat>,
    pub modulus_curvature: Option<Rat>,
    pub modulus_unit: Option<Rat>,
}

/// [measured-diagnostic] The committed move's unit step at a constitution ([`DirectionReading`]).
pub fn unit_direction(
    field: &Field,
    constitution: &Constitution,
    requests: &[Request],
    declared: &Refinement,
    bank: &ReceivingBank,
    grain: u32,
    comparison: Comparison,
) -> Result<DirectionReading, HnnError> {
    let (before, reads) = incumbent(field, constitution, requests, declared, bank, grain, comparison)?;
    let proposal = propose(comparison.composition, &before, &reads);
    drop(reads);
    let mut reading = DirectionReading {
        before,
        refusal: certificate_refusal(&proposal),
        unit_move: None,
        pullback: None,
        modulus_slope: None,
        modulus_curvature: None,
        modulus_unit: None,
    };
    if reading.refusal.is_some() {
        return Ok(reading);
    }
    let (samples, step) = unit_step(field, constitution, declared, requests, &proposal)?;
    let Some(step) = step else {
        reading.refusal = Some(MoveRefusal::Unreached);
        return Ok(reading);
    };
    let (rows, columns) = (step.unit_move.rows(), step.unit_move.columns());
    let mut pullback = vec![vec![Rat::zero(); columns]; rows];
    for sample in &samples {
        for (row, g) in pullback.iter_mut().zip(&sample.covector) {
            let scaled = &sample.weight * g;
            for (entry, f) in row.iter_mut().zip(&sample.feature) {
                if !f.is_zero() {
                    *entry += &scaled * f;
                }
            }
        }
    }
    reading.pullback = Some(ExactRatMatrix::new(pullback)?);
    reading.unit_move = Some(step.unit_move);
    reading.modulus_slope = Some(step.gamma);
    reading.modulus_curvature = Some(step.curvature);
    reading.modulus_unit = Some(step.modulus_unit);
    Ok(reading)
}

/// [definition; agent-inferred, October 1; the
/// [witness's metric record](../../../../research/records/2026-10-01_THE_MOVES_METRIC_IS_ITS_WITNESSS_THE_LOCKS_FISHER_FORM_ON_THE_MOVES_PLANE.md)]
/// **A lock's sheets at one common representative** ([`LockFace`]'s `sheets`): the resting
/// sheet's weight one and every candidate's reading `a_x ≥ 0`, normalized jointly,
/// `(1, a_0, …)/Π` with `Π = 1 + Σ a_x`. One representative for every sheet makes it one
/// categorical receiver (`Σ = 1`, the resting sheet's share `1/Π > 0`); independent per-candidate
/// faces of the shares' enclosures need not sum to one (Astra's review: three readings in `[1, 9]`
/// give share faces summing to `51/40`). `None` when a reading is negative.
fn lock_sheets(readings: &[Rat]) -> Option<Vec<Rat>> {
    if readings.iter().any(Signed::is_negative) {
        return None;
    }
    let mass = Rat::one() + readings.iter().sum::<Rat>();
    Some(
        std::iter::once(Rat::one())
            .chain(readings.iter().cloned())
            .map(|w| w / &mass)
            .collect(),
    )
}

/// [definition; agent-inferred, October 1] **One lock-face term on the move's plane**: its target,
/// the lock's one normalized reading (`sheets`, the resting sheet first: [`LockFace`]'s), and every
/// candidate's log-reading change along each of the span's directions, on the plane
/// `δ_x = (⟨ĝ_x, Δz_x(ΔE)⟩, ⟨ĝ_x, ∂z_x/∂ρ⟩)` (the resting sheet does not move). Every term of one
/// form has the same number of directions.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PlaneTerm {
    pub target: usize,
    pub sheets: Vec<Rat>,
    pub along: Vec<Vec<Rat>>,
}

/// [definition; agent-inferred, October 1] **The witness's form on the move's plane** (the record
/// above). A move's metric is a reading: the quadratic form by which a receiver measures a change.
/// The executed comparison's witness is the lock at each decision, a normalized receiver over its
/// sheets, whose form in the log-readings is the normalized face's Jacobian
/// `J_θ = diag θ − θθᵀ` ([`crate::receiver::face::softmax_jacobian`], admitted only on a normalized
/// face; Lean `Holon/Law.softmaxJacobian`): the Fisher form, and the lock face's Hessian in the
/// log-readings (`ℓ = log Π − u_t`). Each lock's map `D_j` (sheets × plane; the resting sheet's row
/// zero) pulls it back, and the terms join as one direct sum:
/// `G = Dᵀ(⊕_j J_θj)D` ([`SymmetricForm::direct_sum`], [`SymmetricForm::pullback`]), beside
/// `g = Dᵀ(⊕_j (θ_j − e_t))`, the descent covector's weights ([`LockFace::weight`]) on the same
/// reading.
/// - **Kernel** (Astra's review): `vᵀGv = Σ_j Var_θj(0, (D_j v)_x)`, a variance over each lock's
///   sheets with the resting sheet at zero, so `ker G = ∩_j ker D_j`: a plane direction no lock
///   reads. The step `−G⁻¹g` is defined exactly where `G ≻ 0`, decided by [`inertia`].
/// - **Scope**: `G` is the Gauss–Newton (Fisher) pullback, not the comparison's full Hessian on the
///   plane, which adds `Σ_j Σ_x (θ_x − [x = t]) Hess(u_x)`.
/// - **Charts**: every `δ` is a change of the witness's own reading, so `G`, `g` and the step are
///   unchanged by a storage rechart `z′ = Bz` (`ĝ′ = B⁻ᵀĝ`), and a rescaled plane direction rescales
///   its coordinate inversely. The coordinate control `−γ_ρ/Σ|∂z/∂ρ|²` has neither property.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct WitnessForm {
    pub form: SymmetricForm,
    pub gradient: Vec<Rat>,
}

impl WitnessForm {
    /// The determinant `G_EE G_ρρ − G_Eρ²` of a plane's form (two directions).
    pub fn determinant(&self) -> Rat {
        self.form.at(0, 0) * self.form.at(1, 1) - self.form.at(0, 1) * self.form.at(0, 1)
    }

    /// The witness's step on the span, `−G⁻¹g` (on the plane `(α, β)`), where `G ≻ 0`
    /// ([`inertia`]); `None` where some direction of the span lies in the witness's kernel.
    pub fn step(&self) -> Option<Vec<Rat>> {
        if inertia(&self.form).positive != self.form.extent() {
            return None;
        }
        let inverse = self.form.as_matrix().ok()?.inverse().ok()?;
        Some(inverse.apply(&self.gradient).ok()?.into_iter().map(|x| -x).collect())
    }

    /// Each coordinate's step with the cross terms dropped, `−g_i/G_ii` (the negative control).
    pub fn decoupled(&self) -> Vec<Option<Rat>> {
        (0..self.gradient.len())
            .map(|i| self.form.at(i, i).is_positive().then(|| -&self.gradient[i] / self.form.at(i, i)))
            .collect()
    }

    /// The Gauss–Newton model's change at the witness's step, `½ gᵀs = −½ gᵀG⁻¹g`.
    pub fn predicted(&self) -> Option<Rat> {
        self.step().map(|step| {
            self.gradient.iter().zip(&step).map(|(g, s)| g * s).sum::<Rat>()
                / Rat::from_integer(BigInt::from(2))
        })
    }
}

/// The witness's form from its terms on the plane ([`WitnessForm`]), exactly: the locks' Jacobians
/// joined by direct sum and pulled back once. `None` when a term's reading is not a normalized face
/// (refused by the Jacobian's admission) or its shapes disagree.
pub fn witness_form(terms: &[PlaneTerm]) -> Option<WitnessForm> {
    let width = terms.iter().flat_map(|t| t.along.first()).map(Vec::len).next().unwrap_or(2);
    let mut joined = SymmetricForm::zeros(0);
    let mut rows: Vec<Vec<Rat>> = Vec::new();
    let mut covector: Vec<Rat> = Vec::new();
    for term in terms {
        if term.along.len() + 1 != term.sheets.len()
            || term.target >= term.along.len()
            || term.along.iter().any(|d| d.len() != width)
        {
            return None;
        }
        joined = joined.direct_sum(&crate::receiver::face::softmax_jacobian(&term.sheets).ok()?);
        rows.push(vec![Rat::zero(); width]);
        covector.push(term.sheets[0].clone());
        for (x, delta) in term.along.iter().enumerate() {
            rows.push(delta.to_vec());
            let theta = &term.sheets[x + 1];
            covector.push(if x == term.target { theta - Rat::one() } else { theta.clone() });
        }
    }
    if rows.is_empty() {
        return Some(WitnessForm {
            form: SymmetricForm::zeros(width),
            gradient: vec![Rat::zero(); width],
        });
    }
    let map = ExactRatMatrix::new(rows).ok()?;
    let form = joined.pullback(&map).ok()?;
    let gradient = map.transpose().ok()?.apply(&covector).ok()?;
    Some(WitnessForm { form, gradient })
}

/// [definition; agent-inferred, October 1] **The proposal's terms on the move's plane** and the
/// witness's form over them, from the port's unit-step successor `unit`: one owner for the plane
/// reading ([`witness_plane`]) and the witness's metric ([`executed_move_in`]).
/// - **What `δ` differentiates.** The candidate's leading member's covector (the simple-root
///   derivative of `log ρ(M)` through the executed tick, at its dyadic faces) paired exactly with
///   its storage's move: along `ΔE` the exact difference of the placed storage (linear in `E` at
///   fixed weights), along `ρ` the placement's exact derivative of its unrounded transported
///   weights (`BankPlacement::modulus_derivative`). Each `δ` is then held at [`JOINT_BITS`]
///   significant bits.
/// - Only lock-face terms have a witness; `None` when the proposal has none.
fn plane_terms(
    field: &Field,
    constitution: &Constitution,
    declared: &Refinement,
    requests: &[Request],
    proposal: &Proposal,
    directions: &[&Constitution],
) -> Result<Vec<PlaneTerm>, HnnError> {
    use rayon::prelude::*;
    let moves: Vec<Vec<Vec<ExactInterval>>> = directions
        .iter()
        .map(|unit| section_moves(field, constitution, unit, declared, requests, &proposal.sections, None))
        .collect::<Result<_, HnnError>>()?;
    let derivatives = section_derivatives(field, constitution, declared, requests, proposal)?;
    let held = |x: Rat| {
        if x.is_zero() {
            x
        } else if x.is_negative() {
            -significant(&-x, JOINT_BITS, false)
        } else {
            significant(&x, JOINT_BITS, false)
        }
    };
    let pair = |covector: &[ExactInterval], section: usize| -> Vec<Rat> {
        let covector: Vec<Rat> = covector.iter().map(face).collect();
        moves
            .iter()
            .map(|m| held(covector.iter().zip(&m[section]).map(|(g, d)| g * &d.lower).sum()))
            .chain(std::iter::once(held(
                covector.iter().zip(&derivatives[section]).map(|(g, d)| g * d).sum(),
            )))
            .collect()
    };
    Ok(proposal
        .terms
        .par_iter()
        .filter_map(|term| match &term.certificate {
            Certificate::Lock { target, sheets, .. } => Some(PlaneTerm {
                target: *target,
                sheets: sheets.clone(),
                along: term.leading.iter().map(|c| pair(&c.covector, c.section)).collect(),
            }),
            // The order's lock over stations: no resting sheet, its sheets' log-gaps moving by
            // `(a_top δ_top − a_runner δ_runner)/g`.
            Certificate::Order(pieces) => Some(PlaneTerm {
                target: 0,
                sheets: std::iter::once(Rat::zero())
                    .chain(pieces.iter().map(|p| p.share.clone()))
                    .collect(),
                along: pieces
                    .iter()
                    .map(|p| {
                        let (top, runner) = (
                            pair(&p.top.leading, p.top.section),
                            pair(&p.runner.leading, p.runner.section),
                        );
                        let (a, b) = (face(&p.top.growth), face(&p.runner.growth));
                        top.iter()
                            .zip(&runner)
                            .map(|(t, r)| held((&a * t - &b * r) / &p.gap))
                            .collect()
                    })
                    .collect(),
            }),
            Certificate::Hinge(_) => None,
        })
        .collect())
}

/// The witness's form over the proposal's lock-face terms ([`plane_terms`], [`witness_form`]);
/// `None` when no term has a lock or a reading is not admitted.
fn plane_form(
    field: &Field,
    constitution: &Constitution,
    declared: &Refinement,
    requests: &[Request],
    proposal: &Proposal,
    unit: &Constitution,
) -> Result<Option<WitnessForm>, HnnError> {
    let terms = plane_terms(field, constitution, declared, requests, proposal, &[unit])?;
    Ok(if terms.is_empty() { None } else { witness_form(&terms) })
}

/// [measured-diagnostic; agent-inferred, October 1] **The committed move's plane read by its
/// witness** (the record above): the incumbent's comparison and, where [`executed_move`] would form
/// its step, the port's unit move `ΔE` and the coordinate control (`γ_ρ`, `G_ρ`, `−γ_ρ/G_ρ`)
/// exactly as it forms them ([`unit_step`]), and the witness's form on the plane of `ΔE` and `ρ`
/// ([`plane_form`]) over the proposal's lock-face terms, on the same normalized reading as the
/// proposal's covector. The hinge has no lock and no witness's form here. No step is taken;
/// nothing is retained.
#[derive(Clone, Debug)]
pub struct PlaneReading {
    pub before: BatchComparison,
    pub refusal: Option<MoveRefusal>,
    pub unit_move: Option<ExactRatMatrix>,
    pub modulus_slope: Option<Rat>,
    pub modulus_curvature: Option<Rat>,
    pub modulus_unit: Option<Rat>,
    pub witness: Option<WitnessForm>,
    pub terms: usize,
}

/// [measured-diagnostic] The committed move's plane read by its witness ([`PlaneReading`]).
pub fn witness_plane(
    field: &Field,
    constitution: &Constitution,
    requests: &[Request],
    declared: &Refinement,
    bank: &ReceivingBank,
    grain: u32,
    comparison: Comparison,
) -> Result<PlaneReading, HnnError> {
    witness_plane_along(field, constitution, None, requests, declared, bank, grain, comparison)
}

/// [measured-diagnostic; agent-inferred, October 1] **A plane read by the move's witness, its `E`
/// direction declared**: as [`witness_plane`], with the plane's `E` direction `E_along − E` (the
/// source port of `along`, read at this constitution's `ρ`) in place of the port's unit move when
/// `along` is given. Reads whether the witness's stiffness in `ρ` belongs to the plane's `E`
/// direction or to the witness itself. `unit_move` stays the port's own.
#[allow(clippy::too_many_arguments)]
pub fn witness_plane_along(
    field: &Field,
    constitution: &Constitution,
    along: Option<&Constitution>,
    requests: &[Request],
    declared: &Refinement,
    bank: &ReceivingBank,
    grain: u32,
    comparison: Comparison,
) -> Result<PlaneReading, HnnError> {
    let (before, reads) = incumbent(field, constitution, requests, declared, bank, grain, comparison)?;
    let proposal = propose(comparison.composition, &before, &reads);
    drop(reads);
    let mut reading = PlaneReading {
        before,
        refusal: certificate_refusal(&proposal),
        unit_move: None,
        modulus_slope: None,
        modulus_curvature: None,
        modulus_unit: None,
        witness: None,
        terms: 0,
    };
    if reading.refusal.is_some() {
        return Ok(reading);
    }
    let (_, step) = unit_step(field, constitution, declared, requests, &proposal)?;
    let Some(step) = step else {
        reading.refusal = Some(MoveRefusal::Unreached);
        return Ok(reading);
    };
    reading.modulus_slope = Some(step.gamma.clone());
    reading.modulus_curvature = Some(step.curvature.clone());
    reading.modulus_unit = Some(step.modulus_unit.clone());
    let direction = match along {
        Some(along) => {
            let ring = declared.ring();
            let e = along
                .source_port(ring)
                .ok_or(HnnError::MissingSourcePort { ring })?
                .clone();
            &constitution.clone().with_ports(ring, None, Some(e), None)?
        }
        None => &step.unit,
    };
    let terms = plane_terms(field, constitution, declared, requests, &proposal, &[direction])?;
    reading.terms = terms.len();
    reading.witness = (!terms.is_empty()).then(|| witness_form(&terms)).flatten();
    reading.unit_move = Some(step.unit_move);
    Ok(reading)
}

/// [measured-diagnostic; agent-inferred, October 1; the
/// [witness's span record](../../../../research/records/2026-10-01_THE_WITNESSS_DIRECTION_IN_THE_SPAN_OF_THE_RETURNS.md)]
/// **The witness's direction in the span of the requests' pullbacks**: the source port changes only
/// along covectors that reached it (deposition), so `E`'s directions are the returns' own. One
/// direction a request, `D_r = Σ_t w_t g_t f_tᵀ` over the returns its contributions make alone
/// (the per-return rank-one pieces number about 40 a request, and on two requests their form had a
/// six-dimensional kernel). The witness's form on the span of every `D_r` and `ρ`
/// ([`witness_form`], [`plane_terms`]) gives its step `s = −G⁻¹g`, weighing the requests against
/// each other by its own measure; its `E` move is `Σ_r s_r D_r` and its `ρ` move `s_ρ`. Each
/// `D_r`'s scale is immaterial: the step is covariant in every direction's chart. Beside it, the port's own unit move
/// `ΔE` (the normal law's chart over the same returns). No step is taken.
#[derive(Clone, Debug)]
pub struct SpanReading {
    pub before: BatchComparison,
    pub refusal: Option<MoveRefusal>,
    pub returns: usize,
    pub witness: Option<WitnessForm>,
    pub unit_move: Option<ExactRatMatrix>,
    pub witness_move: Option<ExactRatMatrix>,
    pub modulus_move: Option<Rat>,
}

/// [measured-diagnostic] The witness's direction in the span of the returns ([`SpanReading`]).
pub fn witness_span(
    field: &Field,
    constitution: &Constitution,
    requests: &[Request],
    declared: &Refinement,
    bank: &ReceivingBank,
    grain: u32,
    comparison: Comparison,
) -> Result<SpanReading, HnnError> {
    let ring = declared.ring();
    let (before, reads) = incumbent(field, constitution, requests, declared, bank, grain, comparison)?;
    let proposal = propose(comparison.composition, &before, &reads);
    drop(reads);
    let mut reading = SpanReading {
        before,
        refusal: certificate_refusal(&proposal),
        returns: 0,
        witness: None,
        unit_move: None,
        witness_move: None,
        modulus_move: None,
    };
    if reading.refusal.is_some() {
        return Ok(reading);
    }
    let (samples, step) = unit_step(field, constitution, declared, requests, &proposal)?;
    reading.returns = samples.len();
    let Some(step) = step else {
        reading.refusal = Some(MoveRefusal::Unreached);
        return Ok(reading);
    };
    let e = constitution
        .source_port(ring)
        .ok_or(HnnError::MissingSourcePort { ring })?
        .clone();
    // One direction a request: its own pullback `Σ_t w_t g_t f_tᵀ` over the returns its
    // contributions make alone (its phases and its sections' placements).
    let (rows, columns) = (e.rows(), e.columns());
    let pieces: Vec<ExactRatMatrix> = (0..requests.len())
        .filter_map(|index| {
            let own: Vec<Contribution> =
                proposal.contributions.iter().filter(|c| c.request == index).cloned().collect();
            (!own.is_empty()).then_some(own)
        })
        .map(|own| -> Result<ExactRatMatrix, HnnError> {
            let mut pullback = vec![vec![Rat::zero(); columns]; rows];
            for sample in returns(field, constitution, declared, requests, &own)? {
                for (row, g) in pullback.iter_mut().zip(&sample.covector) {
                    let scaled = &sample.weight * g;
                    for (entry, f) in row.iter_mut().zip(&sample.feature) {
                        if !f.is_zero() {
                            *entry += &scaled * f;
                        }
                    }
                }
            }
            Ok(ExactRatMatrix::new(pullback)?)
        })
        .collect::<Result<_, _>>()?;
    let successors: Vec<Constitution> = pieces
        .iter()
        .map(|d| {
            let moved = ExactRatMatrix::new(
                e.to_rows().iter().zip(d.to_rows()).map(|(a, b)| a.iter().zip(&b).map(|(x, y)| x + y).collect()).collect(),
            )?;
            constitution.clone().with_ports(ring, None, Some(moved), None)
        })
        .collect::<Result<_, HnnError>>()?;
    let directions: Vec<&Constitution> = successors.iter().collect();
    let terms = plane_terms(field, constitution, declared, requests, &proposal, &directions)?;
    let form = (!terms.is_empty()).then(|| witness_form(&terms)).flatten();
    if let Some(s) = form.as_ref().and_then(WitnessForm::step) {
        let mut moved = vec![vec![Rat::zero(); columns]; rows];
        for (coefficient, piece) in s.iter().zip(&pieces) {
            for (row, piece_row) in moved.iter_mut().zip(piece.to_rows()) {
                for (entry, x) in row.iter_mut().zip(&piece_row) {
                    *entry += coefficient * x;
                }
            }
        }
        reading.witness_move = Some(ExactRatMatrix::new(moved)?);
        reading.modulus_move = s.last().cloned();
    }
    reading.witness = form;
    reading.unit_move = Some(step.unit_move);
    Ok(reading)
}

/// [definition; agent-inferred, October 2; the
/// [representation record](../../../../research/records/2026-10-02_THE_REPRESENTATION_THE_REFITS_E_MAKES_RHO_A_MONOTONE_PATH_TO_THE_DECISIONS.md)]
/// **Each reading's gradient in all of `E`**: a section's storage is linear in the source port at
/// fixed weights ([`returns`]), so a member's pairing `⟨ĝ, z_S⟩` has the gradient
/// `G = Σ_c w_S(c) P^(c−λ)ĝ M[c]ᵀ + Σ_j w_S(j) P^(c_j−λ)ĝ e_(x_j)ᵀ` (rows × columns, row-major) over
/// the request's occupied phases and the section's placed stations: the per-member form of the
/// returns, which sum `−Σ_m c_m G_m` as their pullback. `⟨G, ΔE⟩ = ⟨ĝ, Δz_S(ΔE)⟩` exactly (the
/// owner's test).
fn reading_gradients(
    field: &Field,
    constitution: &Constitution,
    declared: &Refinement,
    requests: &[Request],
    members: &[&Contribution],
) -> Result<Vec<Vec<Rat>>, HnnError> {
    use rayon::prelude::*;
    let ring = declared.ring();
    let geometry = field.ring(ring);
    let period = geometry.period() as usize;
    let columns = field.alphabet();
    let rows = constitution
        .source_port(ring)
        .ok_or(HnnError::MissingSourcePort { ring })?
        .rows();
    let placements = placements_of(field, constitution, requests, declared)?;
    type Phases = Vec<(usize, Vec<Rat>)>;
    let shapes: Vec<(BigInt, usize, Phases)> = requests
        .iter()
        .map(|request| -> Result<_, HnnError> {
            let lift = request.current.lift()[ring].clone();
            let phase = request.current.phase(field, ring)? as usize;
            let mut phases = Vec::new();
            for c in 0..period {
                let counts = request.moment.phase_counts(ring, c)?;
                if counts.iter().any(|&n| n != 0) {
                    phases.push((c, counts.iter().map(|&n| Rat::from_integer(BigInt::from(n))).collect()));
                }
            }
            Ok((lift, phase, phases))
        })
        .collect::<Result<_, _>>()?;
    Ok(members
        .par_iter()
        .map(|member| {
            let (lift, phase, phases) = &shapes[member.request];
            let covector: Vec<Rat> = member.covector.iter().map(face).collect();
            let (request_weights, station_weights) =
                placements[member.request].weights(member.station, &member.cells);
            let mut gradient = vec![Rat::zero(); rows * columns];
            let mut add = |at: usize, weight: &Rat, feature: &mut dyn FnMut(usize) -> Option<Rat>| {
                let rotated = geometry.rotate(&covector, &(BigInt::from(at as u64) - lift));
                for column in 0..columns {
                    let Some(f) = feature(column).filter(|f| !f.is_zero()) else { continue };
                    let scale = weight * &f;
                    for (row, g) in rotated.iter().enumerate() {
                        if !g.is_zero() {
                            gradient[row * columns + column] += g * &scale;
                        }
                    }
                }
            };
            for ((c, counts), weight) in phases.iter().zip(&request_weights) {
                add(*c, weight, &mut |column| Some(counts[column].clone()));
            }
            for (station, (cell, weight)) in member.cells.iter().zip(&station_weights).enumerate() {
                let (Some(class), Some(weight)) = (cell, weight) else { continue };
                add((phase + 1 + station) % period, weight, &mut |column| {
                    (column == *class).then(Rat::one)
                });
            }
            gradient
        })
        .collect())
}

/// [definition; agent-inferred, October 2] **Why the receiver's Gauss–Newton solve stopped**
/// ([`KineticSolve`]).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum KineticStop {
    /// The residual's energy fell to `2^(−32)` of its opening (`2^(−16)` in its norm, the bank's grain).
    Converged,
    /// A search direction the witness does not read (`pᵀAᵀFAp ≤ 0`): the kernel of the readings.
    Kernel,
    /// As many iterations as reading coordinates, the exact solve's bound.
    Exhausted,
}

/// [definition; agent-inferred, October 2; the
/// [representation record](../../../../research/records/2026-10-02_THE_REPRESENTATION_THE_REFITS_E_MAKES_RHO_A_MONOTONE_PATH_TO_THE_DECISIONS.md)]
/// **The receiver's minimum-energy move over all of `E`**: the Gauss–Newton step of the witness's
/// readings, the port's retained mass settling every direction no reading fixes.
/// - **The pieces.** `A` maps a move of `E` to the readings' changes (each lock candidate's
///   log-reading, each order piece's log-gap; [`reading_gradients`]). The witness's Fisher form
///   `F = ⊕_j (diag θ_j − θ_jθ_jᵀ)` on the non-resting sheets ([`witness_form`]'s) and its covector
///   `c = ⊕_j (θ_j − e_t)`. The mass is the port's Gram with this passage deposited,
///   `M = I ⊗ H′`, `H′ = H + Σ_t w_t f_t f_tᵀ` (the normal law's own chart `X̂ ≈ H′⁻¹`).
/// - **The law.** Minimize `cᵀAv + ½ vᵀAᵀFAv` with the least kinetic energy `½⟨Mv, v⟩` among the
///   minimizers. Where `A` reaches every reading, its solution is Astra's kinetic face
///   (Lean `Holon/Element`): `v = M⁻¹Aᵀ M_F w` with `M_F = (AM⁻¹Aᵀ)⁻¹` and the readings' change
///   `w = −F⁻¹c`.
/// - **The solve.** Conjugate gradients on `AᵀFA v = −Aᵀc`, preconditioned by `M⁻¹` from `v = 0`,
///   so every iterate is `v_k = M⁻¹Aᵀμ_k`. It is a deposition of the returns with the reading
///   weights `−μ_k`, a normal-law step from the covectors that reached the port. The first iterate
///   is the normal law's own direction, `−M⁻¹Aᵀc`, and the iterates are the receiver's coupling of
///   the readings, which the normal law omits.
/// - **The grain.** Every vector and scalar of the recurrence is held at [`JOINT_BITS`]
///   significant bits toward zero. The solve proposes the direction, and every trial is certified
///   whole before it is adopted.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct KineticSolve {
    /// The reading coordinates: lock candidates and order pieces.
    pub readings: usize,
    /// `μ`, one per reading coordinate. The move's member weights are `−Σ coefficient · μ`.
    pub multipliers: Vec<Rat>,
    /// Each iterate's residual energy over the opening's, `rᵀM⁻¹r / r₀ᵀM⁻¹r₀`.
    pub residuals: Vec<Rat>,
    /// Each iterate's signed squared cosine with a declared `E` direction, `⟨v,t⟩|⟨v,t⟩|/(|v|²|t|²)`,
    /// when one is declared.
    pub cosines: Vec<Rat>,
    pub stop: KineticStop,
    /// `v = M⁻¹Aᵀμ`, rows × columns of `E`.
    pub moved: ExactRatMatrix,
    /// The Gauss–Newton model's change at `v`, `cᵀAv + ½(Av)ᵀF(Av)`.
    pub predicted: Rat,
    /// `Δρ`, the modulus's part of `v` per unit step, where the modulus is joined
    /// ([`ModulusCoupling`]); `None` where `ρ` is held.
    pub modulus: Option<Rat>,
    /// Where the modulus is joined, the two parts of its move at the solve's multipliers `μ`:
    /// `(own, supplied)` with `Δρ = (own − supplied)/s`. `own = Σ_m w_m a_m` is the readings' ask
    /// along `ρ` (its sign is the reach the readings want), and `supplied = ⟨bH′⁻¹, (Aᵀμ)_E⟩` is
    /// the part of that ask `E`'s own move already carries through the coupling `b`.
    pub modulus_drive: Option<(Rat, Rat)>,
}

/// [definition; agent-inferred, October 2; the
/// [joined move's record](../../../../research/records/2026-10-02_THE_TRANSPORT_MODULUS_JOINS_THE_RECEIVERS_MINIMUM_ENERGY_MOVE.md)]
/// **The transport modulus joined to the receiver's minimum-energy move** ([`KineticSolve`]): one
/// coordinate more, `v = (ΔE, Δρ)`.
/// - **Its column of `A`.** Each leading member's reading moves with `ρ` by `a_m = ⟨ĝ_m, ∂z_m/∂ρ⟩`
///   (the storage's exact derivative, `BankPlacement::modulus_derivative`): the pairing the
///   modulus's slope `γ_ρ` sums, without the normal law's weight.
/// - **Its mass.** The kinetic energy of a move is the squared norm of the storage change it causes on
///   the passage's data, read in `E`'s own frame as `E`'s mass is: a datum `k` of feature `f_k`
///   placed at weight `w_k` moves by `w_k ΔE f_k + w_k s_k Δρ E f_k`, `s_k = (r_k − r̄)/ρ` its reach
///   slope (`BankPlacement::reach_slopes`). Summed over the proposal's data, the mass is
///   `[[I ⊗ H′, b], [bᵀ, g]]` with `b = E Σ_k w_k² s_k f_k f_kᵀ` and `g = Σ_k w_k² s_k² |E f_k|²`.
///   The retained Gram `H` stays in `E`'s block only: it is the second moment of moments already
///   formed at their own passages' transport, so no retained datum's storage moves with today's `ρ`.
/// - **Its inverse.** One coordinate more is one Schur complement: with `y = (Y, y_ρ)`,
///   `x_ρ = (y_ρ − ⟨bH′⁻¹, Y⟩)/s` and `X = YH′⁻¹ − x_ρ bH′⁻¹`, `s = g − ⟨b, bH′⁻¹⟩ > 0`. Where
///   `s` is not positive the modulus moves no storage that `E` cannot, and it is not joined.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ModulusCoupling {
    /// `a_m`, one per leading member, in the proposal's order.
    pub columns: Vec<Rat>,
    /// `bH′⁻¹`, rows × columns of `E`, row-major.
    pub coupling: Vec<Rat>,
    /// `s = g − ⟨b, bH′⁻¹⟩`, the modulus's mass after `E`'s share.
    pub schur: Rat,
}

/// One reading coordinate of the kinetic solve: its members and their coefficients.
type ReadingRow = Vec<(usize, Rat)>;

/// [agent-inferred, October 2] **The readings of a proposal and their witness**: every lock or
/// order term's non-resting sheets `θ`, its target among them, and its reading coordinates over the
/// term's leading members, numbered in the order the proposal's contributions list them.
fn kinetic_readings(proposal: &Proposal) -> Vec<(Vec<Rat>, usize, Vec<ReadingRow>)> {
    let mut member = 0usize;
    let mut out = Vec::new();
    for term in &proposal.terms {
        let base = member;
        member += term.leading.len();
        match &term.certificate {
            Certificate::Lock { target, sheets, .. } => out.push((
                sheets[1..].to_vec(),
                *target,
                (0..term.leading.len()).map(|x| vec![(base + x, Rat::one())]).collect(),
            )),
            // The order's lock over stations: no resting sheet; each piece's log-gap moves by
            // `(a_top δ_top − a_runner δ_runner)/g` (its members top then runner).
            Certificate::Order(pieces) => out.push((
                pieces.iter().map(|p| p.share.clone()).collect(),
                0,
                pieces
                    .iter()
                    .enumerate()
                    .map(|(i, p)| {
                        vec![
                            (base + 2 * i, face(&p.top.growth) / &p.gap),
                            (base + 2 * i + 1, -face(&p.runner.growth) / &p.gap),
                        ]
                    })
                    .collect(),
            )),
            Certificate::Hinge(_) => {}
        }
    }
    out
}

/// A value held at [`JOINT_BITS`] significant bits toward zero.
fn joint_held(x: Rat) -> Rat {
    if x.is_zero() {
        x
    } else if x.is_negative() {
        -significant(&-x, JOINT_BITS, false)
    } else {
        significant(&x, JOINT_BITS, false)
    }
}

/// The receiver's Gauss–Newton solve ([`KineticSolve`]) at the proposal's returns `samples`, with
/// each iterate's squared cosine against `toward` when declared. `None` when the proposal has no
/// lock or order reading, or the passage's Gram is not invertible.
fn kinetic_solve(
    field: &Field,
    constitution: &Constitution,
    declared: &Refinement,
    requests: &[Request],
    proposal: &Proposal,
    samples: &[Sample],
    toward: Option<&ExactRatMatrix>,
    join: bool,
) -> Result<Option<KineticSolve>, HnnError> {
    let ring = declared.ring();
    let terms = kinetic_readings(proposal);
    let rows: Vec<&ReadingRow> = terms.iter().flat_map(|(_, _, r)| r).collect();
    if rows.is_empty() {
        return Ok(None);
    }
    let law = constitution
        .source_law(ring)
        .ok_or(HnnError::MissingSourcePort { ring })?;
    let columns = law.map().columns();
    // The mass's inverse on a row of `E`: `H′⁻¹`, exactly.
    let mut gram = law.gram().to_rows();
    for sample in samples.iter().filter(|s| !s.weight.is_zero()) {
        for (i, fi) in sample.feature.iter().enumerate() {
            for (j, fj) in sample.feature.iter().enumerate() {
                gram[i][j] += &sample.weight * fi * fj;
            }
        }
    }
    let Ok(chart) = ExactRatMatrix::new(gram)?.inverse() else {
        return Ok(None);
    };
    let members: Vec<&Contribution> = proposal.terms.iter().flat_map(|t| &t.leading).collect();
    let gradients = reading_gradients(field, constitution, declared, requests, &members)?;
    let toward: Option<Vec<Rat>> = toward.map(|t| t.entries().to_vec());
    let chart = chart.to_rows();
    let coupling = if join {
        modulus_coupling(field, constitution, declared, requests, proposal, &chart)?
    } else {
        None
    };
    kinetic_lift(&terms, &gradients, &chart, columns, toward.as_deref(), coupling.as_ref()).map(Some)
}

/// **Every datum's reach moments over the contributions** ([`ModulusCoupling`], "Its mass"):
/// `Σ_k w_k² s_k f_k f_kᵀ` and `Σ_k w_k² s_k² f_k f_kᵀ` over each contribution's data, read as
/// [`returns`] reads them (each request phase with its counts `M[c]`, each placed station with its
/// class `e_x`, at its transported weight from the contribution's station).
#[allow(clippy::type_complexity)]
fn reach_moments(
    field: &Field,
    constitution: &Constitution,
    declared: &Refinement,
    requests: &[Request],
    contributions: &[Contribution],
) -> Result<(Vec<Vec<Rat>>, Vec<Vec<Rat>>), HnnError> {
    let ring = declared.ring();
    let period = field.ring(ring).period() as usize;
    let alphabet = field.alphabet();
    let placements = placements_of(field, constitution, requests, declared)?;
    let mut first = vec![vec![Rat::zero(); alphabet]; alphabet];
    let mut second = vec![vec![Rat::zero(); alphabet]; alphabet];
    for (index, (request, placement)) in requests.iter().zip(&placements).enumerate() {
        let mine: Vec<&Contribution> = contributions.iter().filter(|c| c.request == index).collect();
        if mine.is_empty() {
            continue;
        }
        let counts: Vec<Vec<Rat>> = (0..period)
            .filter_map(|c| {
                let counts = request.moment.phase_counts(ring, c).ok()?;
                counts.iter().any(|&n| n != 0).then(|| {
                    counts.iter().map(|&n| Rat::from_integer(BigInt::from(n))).collect()
                })
            })
            .collect();
        for contribution in mine {
            let (request_weights, station_weights) =
                placement.weights(contribution.station, &contribution.cells);
            let (request_slopes, station_slopes) =
                placement.reach_slopes(contribution.station, &contribution.cells);
            for ((f, w), slope) in counts.iter().zip(&request_weights).zip(&request_slopes) {
                let once = w * w * slope;
                let twice = &once * slope;
                for (i, fi) in f.iter().enumerate().filter(|(_, x)| !x.is_zero()) {
                    for (j, fj) in f.iter().enumerate().filter(|(_, x)| !x.is_zero()) {
                        first[i][j] += &once * fi * fj;
                        second[i][j] += &twice * fi * fj;
                    }
                }
            }
            for ((cell, w), slope) in
                contribution.cells.iter().zip(&station_weights).zip(&station_slopes)
            {
                let (Some(class), Some(w), Some(slope)) = (cell, w, slope) else { continue };
                let once = w * w * slope;
                second[*class][*class] += &once * slope;
                first[*class][*class] += once;
            }
        }
    }
    Ok((first, second))
}

/// **The modulus's column and mass** ([`ModulusCoupling`]) at the proposal, with `E`'s mass inverse
/// `H′⁻¹` on a row (`chart`). `None` where the modulus moves no storage `E` cannot (`s ≤ 0`).
fn modulus_coupling(
    field: &Field,
    constitution: &Constitution,
    declared: &Refinement,
    requests: &[Request],
    proposal: &Proposal,
    chart: &[Vec<Rat>],
) -> Result<Option<ModulusCoupling>, HnnError> {
    let ring = declared.ring();
    let derivatives = section_derivatives(field, constitution, declared, requests, proposal)?;
    let columns: Vec<Rat> = proposal
        .terms
        .iter()
        .flat_map(|t| &t.leading)
        .map(|m| {
            joint_held(m.covector.iter().map(face).zip(&derivatives[m.section]).map(|(g, d)| g * d).sum())
        })
        .collect();
    let (first, second) = reach_moments(field, constitution, declared, requests, &proposal.contributions)?;
    let port = constitution
        .source_port(ring)
        .ok_or(HnnError::MissingSourcePort { ring })?
        .to_rows();
    let width = chart.len();
    if first.len() != width || port.iter().any(|row| row.len() != width) {
        return Ok(None);
    }
    let product = |row: &[Rat], matrix: &[Vec<Rat>]| -> Vec<Rat> {
        (0..width)
            .map(|j| row.iter().zip(matrix).map(|(x, m)| x * &m[j]).sum())
            .collect()
    };
    let mut coupling = Vec::with_capacity(port.len() * width);
    let mut energy = Rat::zero();
    let mut shared = Rat::zero();
    for row in &port {
        let b = product(row, &first);
        let b_chart = product(&b, chart);
        let c_row = product(row, &second);
        energy += row.iter().zip(&c_row).map(|(x, y)| x * y).sum::<Rat>();
        shared += b.iter().zip(&b_chart).map(|(x, y)| x * y).sum::<Rat>();
        coupling.extend(b_chart.into_iter().map(joint_held));
    }
    let schur = joint_held(energy - shared);
    Ok(schur.is_positive().then_some(ModulusCoupling { columns, coupling, schur }))
}

/// The solve's recurrence ([`KineticSolve`], "The solve") on given readings: each term's
/// non-resting sheets, target and reading coordinates over members, each member's gradient in `E`
/// (row-major, `columns` a row), and the mass's inverse on a row `chart`.
fn kinetic_lift(
    terms: &[(Vec<Rat>, usize, Vec<ReadingRow>)],
    gradients: &[Vec<Rat>],
    chart: &[Vec<Rat>],
    columns: usize,
    toward: Option<&[Rat]>,
    modulus: Option<&ModulusCoupling>,
) -> Result<KineticSolve, HnnError> {
    use rayon::prelude::*;
    let rows: Vec<&ReadingRow> = terms.iter().flat_map(|(_, _, r)| r).collect();
    let height = gradients.first().map_or(0, Vec::len) / columns.max(1);
    // `v` is `E`'s entries, then `Δρ` where the modulus is joined.
    let size = height * columns;
    let dot = |a: &[Rat], b: &[Rat]| -> Rat { a.iter().zip(b).map(|(x, y)| x * y).sum() };
    // `A v`: each reading coordinate's change.
    let forward = |v: &[Rat]| -> Vec<Rat> {
        let pairings: Vec<Rat> = gradients
            .par_iter()
            .enumerate()
            .map(|(m, g)| {
                let moved = dot(g, &v[..size]);
                match modulus {
                    Some(c) => moved + &c.columns[m] * &v[size],
                    None => moved,
                }
            })
            .collect();
        rows.iter()
            .map(|row| joint_held(row.iter().map(|(m, k)| k * &pairings[*m]).sum()))
            .collect()
    };
    // `Aᵀu`: the members' weights and their gradients summed.
    let pull = |u: &[Rat]| -> (Vec<Rat>, Vec<Rat>) {
        let mut weights = vec![Rat::zero(); gradients.len()];
        for (row, value) in rows.iter().zip(u) {
            for (m, k) in row.iter() {
                weights[*m] += k * value;
            }
        }
        let pulled: Vec<Rat> = (0..height * columns)
            .into_par_iter()
            .map(|e| {
                gradients
                    .iter()
                    .zip(&weights)
                    .filter(|(_, w)| !w.is_zero())
                    .map(|(g, w)| &g[e] * w)
                    .sum()
            })
            .collect();
        (weights, pulled)
    };
    // The modulus's two drives at `u` ([`KineticSolve::modulus_drive`]).
    let drive = |c: &ModulusCoupling, weights: &[Rat], pulled: &[Rat]| -> (Rat, Rat) {
        (weights.iter().zip(&c.columns).map(|(w, a)| w * a).sum(), dot(&c.coupling, pulled))
    };
    // `M⁻¹Aᵀu`: each row of `E` through `H′⁻¹`.
    let lift = |u: &[Rat]| -> Vec<Rat> {
        let (weights, pulled) = pull(u);
        let mut lifted: Vec<Rat> = (0..height * columns)
            .map(|e| {
                let (r, j) = (e / columns, e % columns);
                joint_held((0..columns).map(|i| &pulled[r * columns + i] * &chart[i][j]).sum())
            })
            .collect();
        // The modulus's row of `M⁻¹` by its Schur complement ([`ModulusCoupling`], "Its inverse").
        if let Some(c) = modulus {
            let (own, supplied) = drive(c, &weights, &pulled);
            let x = joint_held((own - supplied) / &c.schur);
            for (value, b) in lifted.iter_mut().zip(&c.coupling) {
                *value = joint_held(&*value - &x * b);
            }
            lifted.push(x);
        }
        lifted
    };
    // The witness's form and covector on the reading coordinates, term by term.
    let fisher = |delta: &[Rat]| -> Vec<Rat> {
        let mut out = Vec::with_capacity(delta.len());
        let mut at = 0;
        for (theta, _, r) in terms {
            let d = &delta[at..at + r.len()];
            let mean = dot(theta, d);
            out.extend(theta.iter().zip(d).map(|(t, x)| joint_held(t * (x - &mean))));
            at += r.len();
        }
        out
    };
    let covector: Vec<Rat> = terms
        .iter()
        .flat_map(|(theta, target, _)| {
            theta.iter().enumerate().map(move |(x, t)| if x == *target { t - Rat::one() } else { t.clone() })
        })
        .collect();
    let m = rows.len();
    let cosine = |v: &[Rat]| -> Option<Rat> {
        let t = toward?;
        let v = &v[..size];
        let (vt, vv, tt) = (dot(v, t), dot(v, v), dot(t, t));
        (vv.is_positive() && tt.is_positive()).then(|| joint_held(&vt * vt.abs() / (vv * tt)))
    };
    let mut s: Vec<Rat> = covector.iter().map(|c| -c).collect();
    let mut mu = vec![Rat::zero(); m];
    let mut v = vec![Rat::zero(); size + usize::from(modulus.is_some())];
    let mut z = lift(&s);
    let mut az = forward(&z);
    let mut rz = dot(&s, &az);
    let opening = rz.clone();
    let mut pi = s.clone();
    let mut p = z.clone();
    let mut ap = az.clone();
    let mut residuals = Vec::new();
    let mut cosines = Vec::new();
    let floor = &opening / Rat::from_integer(BigInt::one() << 32usize);
    let stop = loop {
        if !opening.is_positive() {
            break KineticStop::Converged;
        }
        let q = fisher(&ap);
        let curvature = dot(&ap, &q);
        if !curvature.is_positive() {
            break KineticStop::Kernel;
        }
        let alpha = joint_held(&rz / &curvature);
        for (x, y) in mu.iter_mut().zip(&pi) {
            *x = joint_held(&*x + &alpha * y);
        }
        for (x, y) in v.iter_mut().zip(&p) {
            *x = joint_held(&*x + &alpha * y);
        }
        for (x, y) in s.iter_mut().zip(&q) {
            *x = joint_held(&*x - &alpha * y);
        }
        z = lift(&s);
        az = forward(&z);
        let next = dot(&s, &az);
        residuals.push(joint_held(&next / &opening));
        if let Some(c) = cosine(&v) {
            cosines.push(c);
        }
        if next <= floor {
            break KineticStop::Converged;
        }
        if residuals.len() >= m {
            break KineticStop::Exhausted;
        }
        let beta = joint_held(&next / &rz);
        for (x, y) in pi.iter_mut().zip(&s) {
            *x = joint_held(y + &beta * &*x);
        }
        for (x, y) in p.iter_mut().zip(&z) {
            *x = joint_held(y + &beta * &*x);
        }
        for (x, y) in ap.iter_mut().zip(&az) {
            *x = joint_held(y + &beta * &*x);
        }
        rz = next;
    };
    let av = forward(&v);
    let predicted = dot(&covector, &av) + dot(&av, &fisher(&av)) / Rat::from_integer(BigInt::from(2));
    let moved = ExactRatMatrix::new(v[..size].chunks(columns).map(<[Rat]>::to_vec).collect())?;
    let modulus_drive = modulus.map(|c| {
        let (weights, pulled) = pull(&mu);
        drive(c, &weights, &pulled)
    });
    Ok(KineticSolve {
        readings: m,
        multipliers: mu,
        residuals,
        cosines,
        stop,
        moved,
        predicted,
        modulus: modulus.map(|_| v[size].clone()),
        modulus_drive,
    })
}

/// [agent-inferred, October 2] **The proposal's contributions carrying the kinetic weights**: each
/// leading member at `−Σ coefficient · μ` over its reading coordinates, so the normal law's step
/// with their returns is `M⁻¹Aᵀμ` ([`KineticSolve`]).
fn kinetic_contributions(proposal: &Proposal, solve: &KineticSolve) -> Vec<Contribution> {
    let members: Vec<&Contribution> = proposal.terms.iter().flat_map(|t| &t.leading).collect();
    let mut weights = vec![Rat::zero(); members.len()];
    let rows: Vec<ReadingRow> = kinetic_readings(proposal).into_iter().flat_map(|(_, _, r)| r).collect();
    for (row, mu) in rows.iter().zip(&solve.multipliers) {
        for (m, k) in row {
            weights[*m] -= k * mu;
        }
    }
    members
        .into_iter()
        .zip(weights)
        .filter(|(_, w)| !w.is_zero())
        .map(|(c, w)| Contribution { weight: w, ..c.clone() })
        .collect()
}

/// [measured-diagnostic; agent-inferred, October 2] **The receiver's minimum-energy move read, not
/// taken** ([`KineticSolve`]): the incumbent's comparison, the solve with each iterate's signed
/// squared cosine against `toward − E` when a target constitution is declared, the normal law's unit
/// move `ΔE` and its signed squared cosine against the same direction. With `join`, the solve is the
/// joined `(E, ρ)` move's ([`MoveMetric::KineticModulus`]), its `Δρ` and its two drives read before
/// any bound holds them. Nothing is retained.
#[derive(Clone, Debug)]
pub struct KineticReading {
    pub before: BatchComparison,
    pub refusal: Option<MoveRefusal>,
    pub returns: usize,
    pub solve: Option<KineticSolve>,
    pub unit_move: Option<ExactRatMatrix>,
    pub unit_cosine: Option<Rat>,
}

/// [measured-diagnostic] The receiver's minimum-energy move read ([`KineticReading`]).
#[allow(clippy::too_many_arguments)]
pub fn kinetic_reading(
    field: &Field,
    constitution: &Constitution,
    toward: Option<&Constitution>,
    requests: &[Request],
    declared: &Refinement,
    bank: &ReceivingBank,
    grain: u32,
    comparison: Comparison,
    join: bool,
) -> Result<KineticReading, HnnError> {
    let ring = declared.ring();
    let (before, reads) = incumbent(field, constitution, requests, declared, bank, grain, comparison)?;
    let proposal = propose(comparison.composition, &before, &reads);
    drop(reads);
    let mut reading = KineticReading {
        before,
        refusal: certificate_refusal(&proposal),
        returns: 0,
        solve: None,
        unit_move: None,
        unit_cosine: None,
    };
    if reading.refusal.is_some() {
        return Ok(reading);
    }
    let (samples, step) = unit_step(field, constitution, declared, requests, &proposal)?;
    reading.returns = samples.len();
    let Some(step) = step else {
        reading.refusal = Some(MoveRefusal::Unreached);
        return Ok(reading);
    };
    let port = |c: &Constitution| c.source_port(ring).cloned().ok_or(HnnError::MissingSourcePort { ring });
    let direction = toward.map(|t| port(t)?.subtract(&port(constitution)?).map_err(HnnError::from)).transpose()?;
    if let Some(d) = &direction {
        let (u, t) = (step.unit_move.entries(), d.entries());
        let dot = |a: &[Rat], b: &[Rat]| -> Rat { a.iter().zip(b).map(|(x, y)| x * y).sum() };
        let (ut, uu, tt) = (dot(u, t), dot(u, u), dot(t, t));
        if uu.is_positive() && tt.is_positive() {
            reading.unit_cosine = Some(joint_held(&ut * ut.abs() / (uu * tt)));
        }
    }
    reading.solve =
        kinetic_solve(field, constitution, declared, requests, &proposal, &samples, direction.as_ref(), join)?;
    reading.unit_move = Some(step.unit_move);
    Ok(reading)
}

/// The largest power of two at or below `x > 0`; zero at zero.
fn power_below(x: &Rat) -> Rat {
    if !x.is_positive() {
        return Rat::zero();
    }
    let e = crate::ratio::disk::floor_log2(x);
    if e >= 0 {
        Rat::from_integer(BigInt::one() << e as usize)
    } else {
        Rat::new(BigInt::one(), BigInt::one() << (-e) as usize)
    }
}

/// [definition; agent-inferred, September 30] **A carried move's pairing receipt** (the move's
/// requirement 3): for a candidate storage read at `E` and at the successor with the same section,
/// its member's `ln ρ` change enclosed exactly, and the covector paired with the exact storage move.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PairingReading {
    pub request: usize,
    pub station: usize,
    pub cells: Vec<Option<usize>>,
    pub member: usize,
    pub actual: ExactInterval,
    pub predicted: ExactInterval,
}

/// **The pairing receipt of an adopted move** on the proposal's first `2 · count` leading
/// contributions: each candidate's leading member read at `E` and at the successor on the same
/// section, the exact change of `ln ρ_m` against the covector paired with the carried storage move.
#[allow(clippy::too_many_arguments)]
pub fn pairing_receipt(
    field: &Field,
    before: &Constitution,
    after: &Constitution,
    requests: &[Request],
    declared: &Refinement,
    bank: &ReceivingBank,
    grain: u32,
    comparison: Comparison,
    count: usize,
) -> Result<Vec<PairingReading>, HnnError> {
    let (compared, reads) = incumbent(field, before, requests, declared, bank, grain, comparison)?;
    let proposal = propose(comparison.composition, &compared, &reads);
    let chosen: Vec<&Contribution> = proposal.contributions.iter().take(2 * count).collect();
    let sections: Vec<(usize, usize, Vec<Option<usize>>)> =
        chosen.iter().map(|c| (c.request, c.station, c.cells.clone())).collect();
    let moves = section_moves(field, before, after, declared, requests, &sections, None)?;
    let mut out = Vec::new();
    for (contribution, storage_move) in chosen.iter().zip(&moves) {
        let request = &requests[contribution.request];
        let at = |constitution: &Constitution| -> Result<TurnCovector, HnnError> {
            let placement =
                BankPlacement::of(field, constitution, &request.current, &request.moment, declared)?;
            bank.read_turn_covector(
                &turn(&placement.storage(contribution.station, &contribution.cells)),
                grain,
            )
        };
        let (old, new) = (at(before)?, at(after)?);
        let Ok(MemberCovector::Resolved { member, .. }) = leading_member(&old).cloned() else {
            continue;
        };
        let (a, b) = (ln_of(&old.reading.members[member])?, ln_of(&new.reading.members[member])?);
        out.push(PairingReading {
            request: contribution.request,
            station: contribution.station,
            cells: contribution.cells.clone(),
            member,
            actual: ExactInterval {
                lower: &b.lower - &a.upper,
                upper: &b.upper - &a.lower,
            },
            predicted: paired(&contribution.covector, storage_move),
        });
    }
    Ok(out)
}

// -------------------------------------------------------------------------------------------
// the owner's pure laws, exposed to its tests

/// **The move's refusals and certificate on synthetic readings** (the owner's tests of them): the
/// proposal formed from given terms and their candidates' covectors, its unresolved terms, and
/// its first-order reading on given section moves (a function of the proposal's sections, read in
/// its order).
#[cfg(test)]
pub(crate) struct ProposalProbe {
    pub unresolved_terms: usize,
    pub contributions: Vec<(usize, Rat)>,
    pub sections: Vec<(usize, usize, Vec<Option<usize>>)>,
    proposal: Proposal,
}

#[cfg(test)]
impl ProposalProbe {
    pub(crate) fn of(before: &BatchComparison, reads: &[Vec<Vec<TurnCovector>>]) -> Self {
        let proposal = propose(before.comparison.composition, before, reads);
        Self {
            unresolved_terms: proposal.unresolved_terms(),
            contributions: proposal
                .contributions
                .iter()
                .map(|c| (c.station, c.weight.clone()))
                .collect(),
            sections: proposal.sections.clone(),
            proposal,
        }
    }

    pub(crate) fn first_order(&self, moves: &[Vec<Rat>]) -> FirstOrderReading {
        let moves: Vec<Vec<ExactInterval>> = moves.iter().map(|m| points(m)).collect();
        first_order_on(&self.proposal, &moves)
    }

    /// The witness's form on the plane from the proposal's lock-face terms, each candidate's plane
    /// change given term by term ([`witness_form`] on the proposal's own sheets).
    pub(crate) fn plane(&self, along: &[Vec<Vec<Rat>>]) -> Option<WitnessForm> {
        let terms: Vec<PlaneTerm> = self
            .proposal
            .terms
            .iter()
            .filter_map(|t| match &t.certificate {
                Certificate::Lock { target, sheets, .. } => Some((*target, sheets.clone())),
                Certificate::Order(_) | Certificate::Hinge(_) => None,
            })
            .zip(along)
            .map(|((target, sheets), along)| PlaneTerm {
                target,
                sheets,
                along: along.clone(),
            })
            .collect();
        witness_form(&terms)
    }

    /// The move's refusal before any step ([`certificate_refusal`]).
    pub(crate) fn refusal(&self) -> Option<MoveRefusal> {
        certificate_refusal(&self.proposal)
    }

    /// The slope's refusal on a first-order reading ([`slope_refusal`]).
    pub(crate) fn slope_refusal(reading: &FirstOrderReading) -> Option<MoveRefusal> {
        slope_refusal(reading)
    }
}

/// The kinetic solve's recurrence on given readings (the owner's solve tests, [`kinetic_lift`]):
/// each term `(θ, target, rows)` with rows over members as `(member, coefficient)`.
#[cfg(test)]
pub(crate) fn kinetic_lift_probe(
    terms: &[(Vec<Rat>, usize, Vec<Vec<(usize, Rat)>>)],
    gradients: &[Vec<Rat>],
    chart: &[Vec<Rat>],
    columns: usize,
) -> Result<KineticSolve, HnnError> {
    kinetic_lift(terms, gradients, chart, columns, None, None)
}

/// The kinetic solve's recurrence with the modulus joined ([`ModulusCoupling`]; the owner's solve
/// tests).
#[cfg(test)]
pub(crate) fn kinetic_lift_joined_probe(
    terms: &[(Vec<Rat>, usize, Vec<Vec<(usize, Rat)>>)],
    gradients: &[Vec<Rat>],
    chart: &[Vec<Rat>],
    columns: usize,
    coupling: &ModulusCoupling,
) -> Result<KineticSolve, HnnError> {
    kinetic_lift(terms, gradients, chart, columns, None, Some(coupling))
}

/// **Each reading's gradient against its storage move** (the owner's gradient test): at a
/// constitution and a move `ΔE`, every leading member's `(⟨G, ΔE⟩, ⟨ĝ, Δz_S⟩)`, and the members'
/// weighted gradients `Σ c_m G_m` beside the returns' pullback `Σ_t w_t g_t f_tᵀ`, row-major.
#[cfg(test)]
#[allow(clippy::too_many_arguments, clippy::type_complexity)]
pub(crate) fn reading_gradient_probe(
    field: &Field,
    constitution: &Constitution,
    requests: &[Request],
    declared: &Refinement,
    bank: &ReceivingBank,
    grain: u32,
    comparison: Comparison,
    delta: &ExactRatMatrix,
) -> Result<(Vec<(Rat, Rat)>, Vec<Rat>, Vec<Rat>), HnnError> {
    let ring = declared.ring();
    let (before, reads) = incumbent(field, constitution, requests, declared, bank, grain, comparison)?;
    let proposal = propose(comparison.composition, &before, &reads);
    let members: Vec<&Contribution> = proposal.terms.iter().flat_map(|t| &t.leading).collect();
    let gradients = reading_gradients(field, constitution, declared, requests, &members)?;
    let port = constitution.source_port(ring).ok_or(HnnError::MissingSourcePort { ring })?;
    let successor = constitution.clone().with_ports(ring, None, Some(port.add(delta)?), None)?;
    let moves = section_moves(field, constitution, &successor, declared, requests, &proposal.sections, None)?;
    let dot = |a: &[Rat], b: &[Rat]| -> Rat { a.iter().zip(b).map(|(x, y)| x * y).sum() };
    let pairs = members
        .iter()
        .zip(&gradients)
        .map(|(m, g)| {
            let covector: Vec<Rat> = m.covector.iter().map(face).collect();
            let moved: Vec<Rat> = moves[m.section].iter().map(|x| x.lower.clone()).collect();
            (dot(g, delta.entries()), dot(&covector, &moved))
        })
        .collect();
    let mut weighted = vec![Rat::zero(); delta.rows() * delta.columns()];
    for (m, g) in members.iter().zip(&gradients) {
        for (w, x) in weighted.iter_mut().zip(g) {
            *w += &m.weight * x;
        }
    }
    let columns = delta.columns();
    let mut pullback = vec![Rat::zero(); delta.rows() * columns];
    for sample in returns(field, constitution, declared, requests, &proposal.contributions)? {
        for (row, g) in sample.covector.iter().enumerate() {
            for (column, f) in sample.feature.iter().enumerate() {
                pullback[row * columns + column] += &sample.weight * g * f;
            }
        }
    }
    Ok((pairs, weighted, pullback))
}

/// The requests' comparison built from terms read at given sections (the owner's tests of its
/// refusals).
#[cfg(test)]
pub(crate) fn synthetic_batch(
    comparison: Comparison,
    targets: &[Vec<usize>],
    sites: Vec<Vec<TermSite>>,
    reads: &[Vec<Vec<TurnCovector>>],
    termination: usize,
) -> Result<BatchComparison, HnnError> {
    let mut compared = Vec::new();
    for ((targets, sites), reads) in targets.iter().zip(sites).zip(reads) {
        let order_terms = match comparison.composition {
            Composition::LockOrder => order_terms(&sites, reads, targets, comparison.reading)?,
            _ => Vec::new(),
        };
        let (terms, mut value, mut excess) =
            terms_of(comparison.composition, targets, sites, reads, termination)?;
        for order in &order_terms {
            value = plus(&value, &order.value);
            excess = plus(&excess, &order.excess);
        }
        compared.push(RequestComparison {
            generation: None,
            stations: Vec::new(),
            orders: Vec::new(),
            terms,
            order_terms,
            consistent: None,
            value,
            excess,
            readings: 0,
        });
    }
    Ok(batch_of(comparison, compared))
}

/// The fixed mask's re-read at a constitution (the owner's mask test): the mask's composition and
/// excess, and the own release's comparison.
#[cfg(test)]
#[allow(clippy::too_many_arguments)]
pub(crate) fn mask_reread(
    field: &Field,
    constitution: &Constitution,
    requests: &[Request],
    declared: &Refinement,
    bank: &ReceivingBank,
    grain: u32,
    comparison: Comparison,
    mask: &[Vec<TermSite>],
) -> Result<(ExactInterval, ExactInterval, Option<BatchComparison>, Option<TrialRefusal>), HnnError>
{
    let read = executed_reread(field, constitution, requests, declared, bank, grain, comparison, mask)?;
    Ok((read.value, read.excess, read.comparison, read.refusal))
}

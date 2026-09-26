//! **The HNN law over aeons** (rebuild step 4, #73; design:
//! [THE_REBUILD](../../../../docs/plans/THE_REBUILD.md), "Step 4 design: the HNN law").
//! Campaign 1: keys, the change on a medium, and the collapse.
//!
//! [definition] The HNN is one Holon: closing rotor rings joined by pair contacts, the medium
//! `(Θ, λ)` fixing every operand of a word, and a change that opens at zero, propagates one contact
//! per tick and is released at the word's end. The forward machine is here:
//!
//! - [`field`]: the declaration ([`Ring`], [`Contact`], [`Field`]), the lift point [`Current`] and
//!   the read face of the constitution ([`ConstitutionRead`]); selective stepping on the port chart;
//! - [`moment`]: the phase-binned [`SourceMoment`] on closing source rings, its window, the pair
//!   port and its capacity `n*`;
//! - [`propagation`]: the junction Swing, the ring element's Cayley step with its contrast port,
//!   the contact's midpoint two-port, the global power and the causal cone;
//! - [`word`]: a [`Word`], one evaluation at one cut's fixed operands, opening at zero change and
//!   releasing it at its end;
//! - [`chart`]: the word on its declared lattices (Decision 24): every inverse a certified lattice
//!   chart refined by rounded Newton–Schulz steps, every transient carried with error feedback, the
//!   integer products under the carrier's ℓ1 certificate, and the declared precisions by rule;
//! - [`receiving`]: [`ReceivingPhases`], the receiving parametron's active suffix address
//!   ([`ActiveAddress`]) and the read at the receiver's grain `L_R`: the combined face of the
//!   landmark tree's face at each phase's causal address and the wave (Decisions 27 and 28);
//! - [`landmark`]: the receiving parametron's storage as a tree of landmarks ([`Landmarks`]): typed
//!   address letters, KT masses at nodes founded at first arrival, the path face mixed along the
//!   opened path, its deposit and its prequential measurement (Decision 28);
//! - [`keys`]: the data → menu map, key location per ring in carry order, and gauge fixing.
//!
//! The learning side (constitution, ratio, pending, retention, port, reference) composes these.
//! `realization` runs the regions whose effects commute together on the host's cores (the hardware
//! law); the reference's header records which.
//!
//! [definition] **Guards** (design (g)) carried by these files: no float enters a law (the lint
//! below, and every value is [`crate::ratio::Rat`] or an exact integer); the [`SourceMoment`] is
//! sized once from the field and accepts closing source rings only; a [`Word`] borrows its field,
//! is not `Clone`, and owns the only waves and contact states; [`Current`] holds the lift point and
//! nothing else, so no change outlives its word; `propagation` exposes only junction-local solves.
//! Their `compile_fail` proofs are doctests on the types, and their runtime tests are in
//! `tests/guards.rs`.
//!
//! | Law (design (b)) | Lean | Rust |
//! |---|---|---|
//! | the ring element | `HNN/Word.{reaction_stage_isometry, reaction_stage_balance, contrastPort_active}` | [`propagation::element_step`] |
//! | the tick's global power | `HNN/Word.word_tick_balance` | [`propagation::global_power`], [`propagation::TickBalance`] |
//! | the junction Swing | `HNN/Propagation.{anchor_is_participation, junctionSwing_involutive, junctionSwing_isometry}` | [`propagation::junction_swing`] |
//! | the contact two-port | `HNN/Propagation.{partialIsometry_transit, transit_balance, tick_well_defined}` | [`propagation::transit`], [`Contact`] |
//! | the causal cone | `HNN/Word.word_tick_cone` (the concrete tick) | [`Word::support`] |
//! | the word on declared lattices: certified inverse charts, error feedback, the executed adjoint, the balance up to the residual | `HNN/LatticeWord.{nsStep, rounded_refinement_certificate, roundedIter_certificate, warm_start_certificate, inverse_chart_deviation, feedback_tick, carried_word_accounting, executed_adjoint_unique, executed_adjoint_deviation, cayley_chart_energy}` | [`chart`], [`Word`], [`Word::pull_back`], [`propagation::TickBalance`] |
//! | the moment | `HNN/Moment.{encoderMoment_contract, encoder_covector_tape_free, closingRing_moment_is_phaseBinned, exteriorOffset_independent_of_E, selective_position, moment_capacity}` | [`SourceMoment`], [`moment::capacity`] |
//! | the receiving face: the landmark tree's face at each phase's causal address, read at the grain, plus the wave (Decisions 27 and 28; Decision 27's region table is the depth-one forced case of the whole-cell emission, kept in Lean, not of the digit tree) | `HNN/RegionCounts.{grain_log_iff_pow_bounds, grain_code_residual, combined_face_pullback}`, `HNN/LandmarkTree.{depth_one_is_decision_27, release_rule}` | [`receiving`], [`ReceivingRead::combined`], [`ActiveAddress`] |
//! | the receiving face compresses landmarks: the tree's path face, its opened-path deposit and telescope, the executed dyadic face (Decision 28) | `HNN/LandmarkTree.{path_face_normalized, weight_step, landmark_step, path_telescope_exact, depth_one_is_decision_27, executed_split_laws, cell_faces_partition, digit_log_residual}` ([`landmark`]'s header has the rest) | [`landmark`] |
//! | the word opens at zero | structural: [`Current`] has no wave field (`HNN/Retention.word_opens_at_zero` is the abstract trajectory's linearity) | [`Word::open`] |
//! | keys | `HNN/Keys.{field_loop_fibre, selective_step_dormant, propagation_eq_edge_fibre, gauge_fix_unique}` | [`keys`], [`crate::compression::Menu::propagate`] |
//! | the ring's navigator | `Holon/Generator.{mapRotor_order, map_pow_mod_order, map_turn_lossless}` | [`Ring::navigator`] over `navigator::Transport::Map` |
//! | the block incidence, the contrast map read from its blocks, and the Holarchy chart | `Holon/Complex.{blockIncidence, block_flat_closed}`, `Holarchy/Join.interconnect` | [`Field::connection`], [`Field::contrast`], [`Field::holon`] |
//! | the port's returns | `Holarchy/Reception.InteractionReturn` (the owner's, generic in its payloads) | [`ExecutionPort`] |
//! | the mount certifies the Holarchy; its parametric orientation carries the aeons | `Holarchy/Join.interconnect`, `Holarchy/Join.Holarchy.parametric` | [`Reference`] (`mount_with`), [`reference::Resident::parametric`] |
//! | the aeon at its boundary: readings, epochs as section flux, the carry-out's cycle | `Aeon/Clock/Winding.{reading_navigatorClock, torus_cycle_reads_whole_windings}`, `Aeon/Clock/Epoch.signed_count_is_flux`, `HNN/Retention.lift_reading` | [`retention::aeon_readings`], [`AeonBoundary`] |
//! | the first law over an aeon, on enclosed code lengths, with the face against the literal | `Aeon/Production/FirstLaw.{ledger_telescopes, enclosed_telescopes}` | [`crate::aeon::EnclosedLedger`] in the resident; [`AeonBoundary::first_law`], [`AeonBoundary::literal`] |
//!
//! Every Lean name cited in `hnn` resolves in `lean/`. The diamond, the release and
//! `deposit_descends` are proved on an abstract sparse linear block operator; their bridge to the
//! concrete tick is owed in #62 (`retention`'s header).

#![deny(
    clippy::float_arithmetic,
    clippy::disallowed_types,
    clippy::disallowed_methods
)]

pub mod chart;
pub mod constitution;
pub mod field;
pub mod keys;
pub mod landmark;
pub mod moment;
pub mod pending;
pub mod port;
pub mod propagation;
pub mod ratio;
pub(crate) mod realization;
pub mod receiving;
pub mod reference;
pub mod retention;
pub mod word;

pub use chart::{ChartKey, ChartReading, ChartStart, ChartWords, Charts, Remainders, WordLattice};
pub use constitution::{Carrier, CarrierBits, Constitution, Lattice, Locus, NormalLaw, Steps};

pub use field::{
    ConstitutionRead, Contact, ContactDeclaration, Current, Field, FieldDeclaration, Ring,
    RingDeclaration,
};
pub use keys::{KeyLocation, RingKeys, locate_keys};
pub use landmark::{LandmarkDeclaration, Landmarks, Letter};
pub use moment::{Capacity, PairPort, SourceMoment};
pub use pending::PendingRatio;
pub use port::{
    Deposit, ExecutionPort, Handle, MomentId, PendingId, Pullback, StagedId, Transpose,
};
pub use ratio::{Faces, HolonRatio, RatioCovector};
pub use receiving::{ActiveAddress, GrainCell, ReceivingPhases, ReceivingRead};
pub use reference::{Cut, Exposure, Reference, Resident};
pub use retention::AeonBoundary;
pub use word::{Released, Word};

#[cfg(test)]
mod tests;

use thiserror::Error;

use crate::aeon::AeonError;
use crate::compression::CompressionError;
use crate::holon::HolonError;
use crate::holon::contact::ContactError;
use crate::holon::contact::menu::MenuError;
use crate::holon::parametron::ParametronError;
use crate::ratio::Rat;
use crate::ratio::exponentiated::RatioError;
use crate::ratio::linear::ExactLinearError;
use crate::receiver::face::WidthRefusal;

/// Every refusal of the HNN. Bad input is a typed return, never a panic, and every refusal names its
/// loci, handles and decisions by their types, never by a string (guard 8). The owners' refusals
/// whose own largest variant is wide (`ContactError`, `ParametronError`, `CompressionError`,
/// `AeonError`) are carried boxed, so a `Result<_, HnnError>` stays narrow; each still converts by
/// `?` from its owner's error.
#[derive(Debug, Error, PartialEq)]
pub enum HnnError {
    #[error(transparent)]
    Linear(#[from] ExactLinearError),
    #[error(transparent)]
    Holon(#[from] HolonError),
    #[error(transparent)]
    Contact(Box<ContactError>),
    #[error(transparent)]
    Parametron(Box<ParametronError>),
    #[error(transparent)]
    Compression(Box<CompressionError>),
    #[error(transparent)]
    Menu(#[from] MenuError),
    #[error(transparent)]
    Aeon(Box<AeonError>),
    #[error(transparent)]
    Ratio(#[from] RatioError),
    #[error("{what}: expected {expected}, found {found}")]
    Shape {
        what: &'static str,
        expected: usize,
        found: usize,
    },
    #[error("ring {ring} has period {period}; a closing rotor ring needs a period of at least 2")]
    RingPeriod { ring: usize, period: u64 },
    #[error("ring {ring}'s node {node} is not a point of its screw's circle")]
    NotOnCircle { ring: usize, node: usize },
    #[error("ring {ring}'s screw has no rotating axis, so it has no circle")]
    NoRingAxis { ring: usize },
    #[error("ring {ring}'s notch {notch} lies outside its port chart of {period}")]
    Notch {
        ring: usize,
        notch: u64,
        period: u64,
    },
    #[error("ring {ring}'s reflector is not an involution of its port chart")]
    Reflector { ring: usize },
    #[error("ring {ring}'s declared initial configuration {initial} lies outside its period")]
    Initial { ring: usize, initial: u64 },
    #[error("ring {ring}'s lift coordinate is negative; a lift point only advances from rest")]
    NegativeLift { ring: usize },
    #[error("ring {ring} lies outside a field of {rings} rings")]
    RingOutside { ring: usize, rings: usize },
    #[error("contact {contact} joins ring {ring} to itself")]
    SelfContact { contact: usize, ring: usize },
    #[error("contact {contact}'s channel matches node {node} outside its ring, or twice")]
    Channel { contact: usize, node: usize },
    #[error("contact {contact}'s admittance {admittance} is not positive")]
    Admittance { contact: usize, admittance: Rat },
    #[error("ring {ring}'s storage admittance {admittance} is not positive")]
    RingAdmittance { ring: usize, admittance: Rat },
    #[error(
        "contact {contact}'s exponent {exponent} is not on its lattice (2 q_Q / L) Z = {lattice} Z"
    )]
    ExponentLattice {
        contact: usize,
        exponent: Box<Rat>,
        lattice: Box<Rat>,
    },
    #[error(
        "contact {contact}'s exponent has phase class {phase} of {grain}: a current in Q(theta) is not carried in campaign 1"
    )]
    ExponentPhase {
        contact: usize,
        phase: u64,
        grain: u64,
    },
    #[error("the declared loop {index} does not close through the field's contacts")]
    Loop { index: usize },
    #[error("the field declares no source ring")]
    NoSource,
    #[error("offset {offset} is not a positive declared offset")]
    Offset { offset: usize },
    #[error("the declared step and grains must be positive")]
    NonpositiveDeclaration,
    #[error("ring {ring} is not reached from any source ring")]
    Unreached { ring: usize },
    #[error(
        "the declared population of {population} cells is shorter than the capacity n* = {n_star}: the moment would be lossless"
    )]
    BelowCapacity { population: u64, n_star: u64 },
    #[error("cell code {code} lies outside the exterior chart of {alphabet}")]
    CellOutside { code: usize, alphabet: usize },
    #[error("a count of the moment would pass the machine word; the moment refuses it")]
    CountOverflow,
    #[error("ring {ring} is a source ring but the constitution carries no source port for it")]
    MissingSourcePort { ring: usize },
    #[error("the constitution carries no receiving map for ring {ring}")]
    MissingReceivingMap { ring: usize },
    #[error(
        "the landmark tree's declared population n* = {population} is passed; its chart's certificates hold only within it"
    )]
    PopulationReached { population: u64 },
    #[error(
        "aperture {aperture} exceeds the receiving ring's observability rank {rank} over the word"
    )]
    Observability { aperture: usize, rank: usize },
    #[error("the code tolerance must be a positive rational, found {tolerance}")]
    Tolerance { tolerance: Rat },
    #[error("the word has run its {ticks} junction steps")]
    WordEnded { ticks: usize },
    #[error("the crib of {cells} cells has no pair at offset {offset}")]
    Crib { cells: usize, offset: usize },
    #[error(
        "the successor constitution's {bits} exact bits exceed its budget of {budget} at commit {commit}; the loci that grew most: {loci:?}"
    )]
    ConstitutionBudget {
        bits: u64,
        budget: u64,
        commit: u64,
        loci: Vec<Locus>,
    },
    #[error(
        "locus {locus:?} has no declared carrier lattice, or a lattice is declared for a locus the field does not learn"
    )]
    Lattice { locus: Locus },
    #[error(
        "locus {locus:?} declares the lattice exponent {declared}, coarser than the rule's {rule}: the carried Gram's positivity and the read's bound below the grain would not hold"
    )]
    LatticeBelowRule {
        locus: Locus,
        declared: u32,
        rule: u32,
    },
    #[error("the carried factor statistic h_x = {statistic} of {locus:?} is not positive")]
    FactorStatistic { locus: Locus, statistic: Rat },
    #[error("deposits stopped at commit {commit}, when the constitution reached its budget")]
    DepositsStopped { commit: u64 },
    #[error(
        "the deposit was staged at commit {staged}; the published constitution is at {published}"
    )]
    StaleDeposit { staged: u64, published: u64 },
    #[error("the locus {locus:?} is released; no deposit reaches it")]
    ReleasedLocus { locus: Locus },
    #[error("the admitted family adds receivers on rings {receivers:?} to the previous boundary's")]
    AdmittedGrowth { receivers: Vec<usize> },
    #[error("the resident holds no open handle {handle:?}")]
    UnknownHandle { handle: Handle },
    #[error("the resident's {capacity} pending ratios are all open")]
    PendingCapacity { capacity: usize },
    #[error("the joint clock carried out; the aeon awaits close_aeon before any further cell")]
    AeonAwaitingClose,
    #[error("close_aeon is admitted only at a carry-out of the joint clock")]
    NotAtCarryOut,
    #[error(
        "keys are located only between close_aeon and the next ingest, from the crib that closed the aeon"
    )]
    KeysNotAdmitted,
    #[error("cell {position} is not a one-hot vector of the exterior chart")]
    CellNotOneHot { position: usize },
    #[error("the release was refused: {0}")]
    ReleaseRefused(#[from] WidthRefusal),
    #[error("the carrier refused {what}: nothing is rounded")]
    Carrier { what: &'static str },
    #[error("the execution port's realization refused: {what}")]
    Realization { what: &'static str },
    #[error(
        "the chart {chart:?} did not refine below its certificate {certificate}: the target is {target}"
    )]
    ChartCertificate {
        chart: ChartKey,
        certificate: Box<Rat>,
        target: Box<Rat>,
    },
}

macro_rules! boxed_from {
    ($($variant:ident($owner:ty)),* $(,)?) => {
        $(
            impl From<$owner> for HnnError {
                fn from(refusal: $owner) -> Self {
                    HnnError::$variant(Box::new(refusal))
                }
            }
        )*
    };
}

boxed_from!(
    Contact(ContactError),
    Parametron(ParametronError),
    Compression(CompressionError),
    Aeon(AeonError),
);

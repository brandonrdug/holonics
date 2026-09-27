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
//! - [`chart`]: the word on its declared lattices (the lattice word): every inverse a certified lattice
//!   chart refined by rounded Newton–Schulz steps, every transient carried with error feedback, the
//!   integer products under the carrier's ℓ1 certificate, and the declared precisions by rule;
//! - [`receiving`]: [`ReceivingPhases`], the receiving parametron's active suffix address
//!   ([`ActiveAddress`]) and the read at the receiver's grain `L_R`: the combined face of the
//!   context tree's face at each phase's causal address and the wave (the region table and the
//!   context tree);
//! - the receiving parametron's storage is the context tree, the shift navigator's landmarks
//!   ([`crate::compression::landmark::context`]): a mixture over the candidate standings of the
//!   pruned context trees, each node's arrivals the epochs of its section; typed address letters,
//!   KT masses at nodes founded at first arrival, the path face mixed along the opened path, its
//!   deposit and its prequential measurement;
//! - [`keys`]: the data → menu map, key location per ring in carry order, and gauge fixing;
//! - [`ring`] (campaign 2): the ring's parametron resonator at its storage port (its mode storage
//!   `Q = diag(K, C)`, its pump and sheets), its rotor clock's epoch ticks, and the junction's
//!   reference change;
//! - [`contact`] (campaign 2): the contact's transfer and site kind, its certified boost, its lock
//!   address and its break receipt, with [`contact_readings`], the lock and site readings the
//!   receiving join consumes;
//! - [`modes`] (campaign 3, first construction): a loaded ring's exact per-phase operators and its
//!   mode quotient: the admitted future kernel through the pump's period, the release by the one
//!   chart that closes every phase's squares, and the descended ring that returns the same wave;
//! - [`born`] (the Born face): the receiving ring's register read by the Born rule, a finitely
//!   correlated receiver whose density is the retained state, each digit split by its pair of
//!   operators' traces, the collapse its receipt, and the operators learned by the normal law's
//!   Fisher-scored prox step on declared lattices.
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
//! | the receiving face: the landmark tree's face at each phase's causal address, read at the grain, plus the wave (the region table and the landmark tree; the region table is the depth-one forced case of the whole-cell emission, kept in Lean, not of the digit tree) | `HNN/RegionCounts.{grain_log_iff_pow_bounds, grain_code_residual, combined_face_pullback}`, `Compression/Landmark/Context/Tree.{depth_one_is_the_whole_cell_table, release_rule}` | [`receiving`], [`ReceivingRead::combined`], [`ActiveAddress`] |
//! | the receiving face compresses landmarks: the tree's path face, its opened-path deposit and telescope, the executed dyadic face (the landmark tree) | `Compression/Landmark/Context/Tree.{path_face_normalized, weight_step, landmark_step, path_telescope_exact, depth_one_is_the_whole_cell_table, executed_split_laws, cell_faces_partition, digit_log_residual}` (the owner's header has the rest) | [`crate::compression::landmark::context`] |
//! | the word opens at zero | structural: [`Current`] has no wave field (`HNN/Retention.word_opens_at_zero` is the abstract trajectory's linearity) | [`Word::open`] |
//! | keys | `HNN/Keys.{field_loop_fibre, selective_step_dormant, propagation_eq_edge_fibre, gauge_fix_unique}` | [`keys`], [`crate::compression::Menu::propagate`] |
//! | the ring's mode tick, its pump and sheets, its clock, the junction's reference change (campaign 2) | `HNN/Ring.{ring_tick_conserves_mode_energy, ring_descriptor_tick_conserves, ring_cayley_denominator_nonsingular, ring_tick_executed_energy_balance, two_port_reference_balance, ring_crossings_are_epoch_ticks, pump_half_turn_invariant, pump_blind_to_sheets, locked_sheet_receiver_face}` | [`ring`] |
//! | the contact's transfer and site kind, its boost, its lock address, its break (campaign 2) | `HNN/Contact.{contact_transfer_kind_by_storage_sign, contact_mode_transfer, contact_boost_solve_or_singular_direction, contact_signed_storage_balance, contact_lock_address, lockAddress_unique, least_denominator_unique, lockAddress_closes}`, `HNN/ContactBreak.{break_release_balance, break_iff_release_covers_gluing, griffith_closed_port_case, parting_returns_gluing_defect}` | [`contact`], [`contact_readings`], [`Field::parted_holon`] |
//! | the loaded tick's field/resonator balance, separate element and returned-wave splits, the word's balance across the gain commit (the loaded resonator) | `HNN/Ring.{loaded_word_stage_balance, loaded_tick_executed_interconnection_balance}`, `HNN/Word.{field_commit_deposition}` | [`word::FieldBalance`], [`word::WordBalance`], [`word::PowerForm`] |
//! | a loaded ring's modes descend to their future quotient: the period lift, one chart for every phase, the descended run, the storage-null release (campaign 3, first construction) | `HNN/ModeQuotient.{periodic_lift_exact, phase_kernel_le_lift, descended_run_reads, released_pair_storage_null}` | [`modes`] |
//! | the wave read by the Born rule: the digit split and the dyadic cell face, the reception keeping a density, the density as the retained quotient, the absorbed tick, the interference zero, the covector and the Fisher-scored step (the Born face) | `HNN/BornFace.{born_face_normalized, born_executed_partition, born_update_trace_one, born_pure_stays_pure, born_state_future_sufficient, born_unitary_invariant, born_tick_absorbed, born_interference_zero, born_covector_eq, born_fisher_bound}` | [`born`] |
//! | the ring's navigator | `Holon/Navigator.{mapRotor_order, map_pow_mod_order, map_turn_lossless}` | [`Ring::navigator`] over `navigator::Transport::Map` |
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

pub mod born;
pub mod chart;
pub mod constitution;
pub mod contact;
pub mod field;
pub mod keys;
pub mod modes;
pub mod moment;
pub mod pending;
pub mod port;
pub mod propagation;
pub mod ratio;
pub(crate) mod realization;
pub mod receiving;
pub mod reference;
pub mod retention;
pub mod ring;
pub mod word;

pub use chart::{ChartKey, ChartReading, ChartStart, ChartWords, Charts, Remainders, WordLattice};
pub use constitution::{Carrier, CarrierBits, Constitution, Lattice, Locus, NormalLaw, Steps};
pub use contact::{
    BreakReceipt, ContactLock, ContactReading, KindCensus, LockDeclaration, SiteReading,
    contact_readings, site_kinds, site_readings,
};

pub use field::{
    ConstitutionRead, Contact, ContactDeclaration, Current, Field, FieldDeclaration, Ring,
    RingDeclaration,
};
pub use keys::{KeyLocation, RingKeys, locate_keys};
pub use moment::{Capacity, PairPort, SourceMoment};
pub use pending::PendingRatio;
pub use port::{
    Deposit, ExecutionPort, Handle, MomentId, PendingId, Pullback, StagedId, Transpose,
};
pub use ratio::{Faces, HolonRatio, RatioCovector};
pub use receiving::{ActiveAddress, GrainCell, LetterReader, ReceivingPhases, ReceivingRead};
pub use reference::{Cut, Exposure, Reference, Resident};
pub use retention::AeonBoundary;
pub use ring::{PumpDeclaration, ResonatorMaterial, RingClock};
pub use word::{Released, ResonatorBalance, Word};

#[cfg(test)]
pub(crate) mod tests;

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
        "the contact's transfer has no Cayley chart: its denominator 2c + p + hd + h²k/2 is zero"
    )]
    SingularTransfer,
    #[error(
        "contact {contact}'s boost has no solve at conductance {conductance}: its operator sends {direction:?} to zero"
    )]
    SingularContact {
        contact: usize,
        conductance: Box<Rat>,
        direction: Vec<Rat>,
    },
    #[error(
        "contact {contact}'s boost is not certified: its signed form is not positive semidefinite and its conductances are not a finite family"
    )]
    UncertifiedBoost { contact: usize },
    #[error(
        "ring {ring}'s resonator is not certified at pump phase {phase}: its signed form 2C + hD + (h²/2)K is not positive semidefinite"
    )]
    UncertifiedResonator { ring: usize, phase: usize },
    #[error("the Born receiver refused {what}")]
    BornZero { what: &'static str },
    #[error("ring {ring}'s resonator material is malformed: {what}")]
    Resonator { ring: usize, what: &'static str },
    #[error("ring {ring}'s mode quotient refused: {what}")]
    ModeQuotient { ring: usize, what: &'static str },
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

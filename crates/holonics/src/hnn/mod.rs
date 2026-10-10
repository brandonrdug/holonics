//! **The HNN law over aeons** (rebuild step 4, #73; design: the [construction record](../../../../research/records/2026-09-28_THE_REBUILDS_CONSTRUCTION_RECORD_STEPS_ZERO_TO_FIVE_THE_CAMPAIGNS_AND_THE_FORWARD_PLAN.md#step-4-design-the-hnn-law);
//! the order is [THE_REBUILD](../../../../docs/plans/THE_REBUILD.md)'s unified plan).
//! Campaign 1: keys, the change on a medium, and the collapse.
//!
//! [definition; Brandon, September 27: "Aeons and Holarchies are at the top"; the construction
//! agent-inferred, the unity audit of September 27, §2] **The HNN is a Holarchy, and its passage
//! is an aeon.**
//! - **The Holarchy.** Its closing rotor rings and its pair contacts are Holons, each certified on
//!   its own, joined at ports: the rings side by side, the contacts side by side, the two
//!   interconnected at every contact end ([`Field::holarchy`] returns the
//!   [`crate::holarchy::Holarchy`], and the mount certifies that it glues or refuses with its typed
//!   gluing defect). The receiving parametron's storage is the context tree, the shift navigator's
//!   landmarks ([`crate::compression::landmark::context`], held in `Θ` at the receiving locus).
//!   [`Field`] is the Holarchy's declaration, a chart of it; the constitution `Θ` holds its element
//!   relations.
//! - **The aeon.** Its passage is an aeon on the Holarchy's parametric orientation
//!   ([`crate::holarchy::Holarchy::parametric`], the lift of the rings' joint clock torus): the
//!   cells a receiver reads between two crossings of its section are an epoch; a pump period or a
//!   clock closure is a cycle; the aeon boundary is the collapse; and the first law over the aeon
//!   is [`crate::aeon::EnclosedLedger`]. [`Reference::expose`] is a cut's passage through the
//!   resident's aeons, one closed at each joint-clock carry-out (`close_aeon`).
//! - **What the code joins** (read from source): the resident's aeon is an [`crate::aeon::Aeon`] on
//!   the parametric orientation, from its opening lift point to the joint clock's carry-out; each
//!   ring's epochs are the flux through its own ring section, read at the boundary; the carry-out
//!   is an [`crate::aeon::Cycle`] of the last ring's clock when that ring opened on its section;
//!   the boundary runs the collapse; and the resident carries the ledger
//!   ([`retention::aeon_readings`], [`AeonBoundary`], [`Reference`]'s header).
//! - **The clocks are aeons** (THE_REBUILD U5; agent-inferred, each choice in its owner). The
//!   receiver's spans of cells are an [`crate::aeon::Epochs`] reading: the epochs of the cut's cell
//!   clock at the receiver's section ([`ReceivingPhases::windows`], which the exposure reads). A
//!   pump's period is an [`crate::aeon::Cycle`] of its own clock ([`PumpDeclaration::period`]; the mode
//!   quotient's lift period, Lean `HNN/ModeQuotient.periodic_lift_exact`, is that cycle's). Every
//!   ring clock the machine keeps is its navigator's `navigator::Clock` (`field`'s header, "The
//!   rings' clocks"), and the selective step's carry is its jumps, the flux of its section. The
//!   word's clock is an unwound `navigator::Clock` whose ticks the receiver reads at `e_0 … e_last`.
//!   The exposure's own counters (compares, deposits, the deadline in epochs) are the program's,
//!   disclosed as such in [`reference::Exposure`].
//! - [open] One join the sentence names is not yet in the code: the receiving tree is storage read
//!   by the receiving face, not a Holon joined at ports in [`Field::holarchy`] (U1 named the missing
//!   maps; owed in #62).
//!
//! Within an aeon the medium `(Θ, λ)` fixes every operand of a word, and a change opens at zero,
//! propagates one contact per tick and is released at the word's end. The forward machine is here:
//!
//! - [`field`]: the declaration ([`Ring`], [`Contact`], [`Field`]), the lift point [`Current`] and
//!   the read face of the constitution ([`ConstitutionRead`]); selective stepping on the encoding's
//!   classes ([`Encoded`], THE_MACHINE guard 9: the codec's residue chart is deleted);
//! - [`encoding`] (U6): Holonic Encoding, a passage chart's minimal realization founded by
//!   closing the receiving forms under the chart's declared transports ([`Encoding`],
//!   [`PassageChart`]), its squares `D E = ρ`, `E T = U E` and the injection square, its Preimage
//!   Fibre and separator;
//! - [`moment`]: the phase-binned [`SourceMoment`] on closing source rings, its pair buffer, the
//!   pair port read over the whole offset moment (no held cell), and its capacity `n*`;
//! - [`paired`] (the helical code, step 2): the paired carrier. A ring's reflector `F_g` is admitted
//!   as a dihedral reflection of its rotor (`F(F(i)+1) = i−1`), its realified lift `B_g` inverts the
//!   rotor on the carrier, and a typed class pairing `σ` is carried by the source port exactly where
//!   `B_g E_g = E_g Σ_σ`, which every read re-certifies on the port it reads. The partner strand's
//!   face is read through the actual moment ([`SourceMoment::dyad`], then `encode` and
//!   `open_storage`), never beside it;
//! - [`propagation`]: the junction Swing, the ring element's Cayley step with its contrast port,
//!   the contact's midpoint two-port, the global power and the causal cone;
//! - [`word`]: a [`Word`], one evaluation at one cut's fixed operands, opening at zero change and
//!   releasing it at its end;
//! - [`chart`]: the word on its declared lattices (the lattice word): every inverse a certified lattice
//!   chart refined by rounded Newton–Schulz steps, every transient carried with error feedback, the
//!   integer products under the carrier's ℓ1 certificate, and the declared precisions by rule;
//! - [`receiving`]: [`ReceivingPhases`], the receiving parametron's active suffix address
//!   ([`ActiveAddress`]), its letters' readers (`receiving::{Feature, FeatureFamily}`, whose
//!   alphabets the tree reads) and the read at the receiver's grain `L_R`: the combined face of the
//!   context tree's face at each phase's causal address and the wave (the region table and the
//!   context tree), the tree's read over an epoch with its phases run together;
//! - the receiving parametron's storage is the context tree, the shift navigator's landmarks
//!   ([`crate::compression::landmark::context`]): a mixture over the candidate standings of the
//!   pruned context trees, each node's arrivals the epochs of its section; typed address letters,
//!   KT masses at nodes founded at first arrival, the path face mixed along the opened path, its
//!   deposit and its prequential measurement;
//! - [`keys`]: the data → menu map, key location per ring in carry order, and gauge fixing;
//! - [`ring`] (campaign 2): the ring's parametron resonator at its storage port (its mode storage
//!   `Q = diag(K, C)`, its pump and sheets), its rotor clock's epoch ticks, and the junction's
//!   reference change;
//! - [`wave`] (the acoustic line, second rung): a [`wave::MatchedWave`], the incident wave of a
//!   source matched to a loaded ring's port (an exact amplitude with a power pairing, never an
//!   [`Encoded`] and never convertible into one), and [`wave::WavePort`], the unpumped ring
//!   continuing across its stream with its mode state as the carried quotient;
//! - [`dynamic_section`] (the acoustic line, second rung): the signed crossing of a ring's own
//!   `(w, u)` state through its four quarter-turn rays, with the lift carried
//!   ([`dynamic_section::SectionReader`]), read as the aeon's reading and its section's ticks;
//! - [`section_lock`] (the acoustic line, second rung, items 4 and 5): the lock reader, a consumer of
//!   the dynamic section's stream (the least period of the settled symbol word, the winding and the
//!   address, the observed arrival word kept with the mean-rate face beside it) and the joint period
//!   of several rings;
//! - [`contact`] (campaign 2): the contact's transfer and site kind, its certified boost, its lock
//!   address and its break receipt, with [`contact_readings`], the lock and site readings the
//!   receiving join consumes;
//! - [`prediction`] (THE_REBUILD U6, native generation): the section's declaration, the partition
//!   law and the receiving bank's lock iteration over the passage's station-framed placement,
//!   released at width zero through `receiver::release` (a plural section held); the linear
//!   readout (`K` continuing words read from one anchor) and the bank's face were retired
//!   September 30 (batch H, at `f5fd8f3b`);
//! - [`executed`] (THE_REBUILD U6, September 30): the release's own comparison (the receiving
//!   bank's class, threshold, order and section predicates along the machine's own trajectory), its
//!   exact pullback to `E` through the executed monodromy's certified eigen-derivative (`ring`), and
//!   a carried update of `E` adopted only where the re-read successor's comparison is certified
//!   lower and its certificates hold.
//!
//! [definition; agent-inferred, U2] A loaded ring's mode quotient (campaign 3's first construction)
//! is Lean's (`HNN/ModeQuotient`); its Rust realization (`hnn::modes`, at commit `1bdacc8f`) was
//! retired at U2. It quotients the ring's word-local state, which leaves at every word's end, so the
//! aeon's retention contract has nothing of it to collapse; the laws only it held are in
//! [HNN_FORMULA §4](../../../../docs/HNN_FORMULA.md#the-loaded-rings-mode-quotient).
//!
//! The learning side (constitution, ratio, pending, retention, port, reference) composes these.
//! `realization` runs the regions whose effects commute together on the host's cores (the hardware
//! law); the reference's header records which.
//!
//! [definition] **Guards** (design (g)) carried by these files: no float enters a law (the lint
//! below, and every value is [`crate::ratio::Rat`] or an exact integer); the [`SourceMoment`] is
//! sized once from the field and accepts closing source rings only; a [`Word`] borrows its field,
//! is not `Clone`, and owns the only waves and contact states; [`Current`] holds the lift point and
//! nothing else, so no change outlives its word, or, for a continuing word, the refinement that
//! owns it until its return (`word`'s "Continuing motion within a refinement"); `propagation`
//! exposes only junction-local solves.
//! Their `compile_fail` proofs are doctests on the types, and their runtime tests are in
//! `tests/guards.rs`.
//!
//! | Law (design (b)) | Lean | Rust |
//! |---|---|---|
//! | the ring element | `HNN/Word.{reaction_stage_isometry, reaction_stage_balance, contrastPort_active}` | [`propagation::element_step`] |
//! | the tick's global power | `HNN/Word.word_tick_balance` | [`propagation::global_power`], [`propagation::TickBalance`] |
//! | the junction's scattering (a half-turn about the participation anchor) | `HNN/Propagation.{anchor_is_participation, junctionScattering_involutive, junctionScattering_isometry}` | [`propagation::participation`], [`propagation::scattering_about`] (`propagation::junction_scattering` the tests' exact reference) |
//! | the contact two-port | `HNN/Propagation.{partialIsometry_transit, transit_balance, tick_well_defined}` | [`propagation::transit`], [`Contact`] |
//! | the causal cone | `HNN/Word.word_tick_cone` (the concrete tick) | [`Word::support`] |
//! | the word on declared lattices: certified inverse charts, error feedback, the executed adjoint, the balance up to the residual | `HNN/LatticeWord.{nsStep, rounded_refinement_certificate, roundedIter_certificate, warm_start_certificate, inverse_chart_deviation, feedback_tick, carried_word_accounting, executed_adjoint_unique, executed_adjoint_deviation, cayley_chart_energy}` | [`chart`], [`Word`], [`Word::pull_back`], [`propagation::TickBalance`] |
//! | the moment | `HNN/Moment.{encoderMoment_contract, encoder_covector_tape_free, closingRing_moment_is_phaseBinned, exteriorOffset_independent_of_E, selective_position, moment_capacity}`; the capacity on the located clock and the retained leaky coordinates `HNN/RangedMoment.SourceDecl.located_moment_capacity`, `HNN/LeakyCapacity.joint_card_bound`; the open that reads no held cell `HNN/Encoding.{whole_pair_read_counts, whole_pair_read_offset_moment}` | [`SourceMoment`], [`moment::capacity`], [`moment::capacity_located`], [`moment::SourceCapacity::checked_of`] |
//! | the paired carrier: a ring's reflector as a dihedral reflection of its rotor, its realified lift, a class pairing carried by an equivariant source port, and the partner strand's face read through the actual moment (the helical code, step 2) | `Transport/HelicalCode.{dihedral_swap, dihedral_reflection_sq, dihedral_conj, strandFace_complementReverse_nat, face_complementReverse}`; the bridge `moment l = U^(n−1)·strandFace U⁻¹ (I∘E) l` is owed (#62) | [`paired::PairedCarrier`], [`SourceMoment::dyad`] |
//! | Holonic Encoding (U6) | `HNN/Encoding.{injection_square, encoding_reduced_recurrence, moment_reduced_recurrence, encoding_separator, encoding_descends_iff}`, `Compression/Landmark/Context/Birth.founding_intertwines` | [`encoding`] |
//! | the receiving face: the landmark tree's face at each phase's causal address, read at the grain, plus the wave (the region table and the landmark tree; the region table is the depth-one forced case of the whole-cell emission, kept in Lean, not of the digit tree) | `HNN/RegionCounts.{grain_log_iff_pow_bounds, grain_code_residual, combined_face_pullback}`, `Compression/Landmark/Context/Tree.{depth_one_is_the_whole_cell_table, release_rule}` | [`receiving`], [`ReceivingRead::combined`], [`ActiveAddress`]; the grain read is [`crate::receiver::face::grain_exponent`]'s |
//! | the receiving face compresses landmarks: the tree's path face, its opened-path deposit and telescope, the executed dyadic face (the landmark tree) | `Compression/Landmark/Context/Tree.{path_face_normalized, weight_step, landmark_step, path_telescope_exact, depth_one_is_the_whole_cell_table, executed_split_laws, cell_faces_partition, digit_log_residual}` (the owner's header has the rest) | [`crate::compression::landmark::context`] |
//! | the word opens at zero, the rest limit of the reception carry | structural: [`Current`] has no wave field (`HNN/Retention.word_opens_at_zero` is the abstract trajectory's linearity; the chained balance across receptions is owed in #62) | [`Word::open`], [`Word::open_received`] |
//! | keys | `HNN/Keys.{field_loop_fibre, selective_step_dormant, propagation_eq_edge_fibre, gauge_fix_unique}` | [`keys`], [`crate::compression::Menu::propagate`] |
//! | the ring's mode tick, its pump and sheets, its clock, the junction's reference change (campaign 2) | `HNN/Ring.{ring_tick_conserves_mode_energy, ring_descriptor_tick_conserves, ring_cayley_denominator_nonsingular, ring_tick_executed_energy_balance, two_port_reference_balance, ring_crossings_are_epoch_ticks, pump_period_is_cycle, pump_half_turn_invariant, pump_blind_to_sheets, locked_sheet_receiver_face}` | [`ring`] |
//! | the contact's transfer and site kind, its boost, its lock address, its break (campaign 2) | `HNN/Contact.{contact_transfer_kind_by_storage_sign, contact_mode_transfer, contact_boost_solve_or_singular_direction, contact_signed_storage_balance, contact_lock_address, lockAddress_unique, least_denominator_unique, lockAddress_closes}`, `HNN/ContactBreak.{break_release_balance, break_iff_release_covers_gluing, griffith_closed_port_case, parting_returns_gluing_defect}` | [`contact`], [`contact_readings`] (`Field::parted_holarchy` the tests') |
//! | the loaded tick's field/resonator balance, separate element and returned-wave splits, the word's balance across the gain commit (the loaded resonator) | `HNN/Ring.{loaded_word_stage_balance, loaded_tick_executed_interconnection_balance}`, `HNN/Word.{field_commit_deposition}` | [`word::FieldBalance`], [`word::WordBalance`], [`word::PowerForm`] |
//! | a matched wave at a loaded ring's port: the executed tick's balance with the wave's `(hY/4)(a² − b²)` booked as boundary work, the ring continuing across the stream (a wave is not an `Encoded`) | `HNN/Ring.ring_tick_executed_energy_balance`; the matched port and the continuing state owed (#62) | [`wave::MatchedWave`], [`wave::WavePort`], [`wave::ReceivedTick::closes`] |
//! | the dynamic section: a ring's state point crossing its quarter-turn rays, the lift `ℓ` (class plus carry) with its advance, the signed crossing of the ring section, the polarity `ℓ(−z) = ℓ(z) + 2` | `Geometry/PhaseCarry.winding_add`, `Aeon/Clock/Epoch.signed_count_is_flux`; the chord's advance and the polarity owed (#62) | [`dynamic_section::SectionReader`], [`dynamic_section::chord`] |
//! | the lock: the least period of a ring's settled symbol word, the winding of its cycle (whole turns), the address `W/τ`, the observed arrival word, `TwoClocks(W/τ)` only as the mean-rate face beside it; the joint period (the lcm) | `Geometry/PhaseCarry.closed_loop_has_integer_winding`, `Aeon/Clock/CarryWord.carry_balanced`, `Aeon/Clock/Lock.lock_at_address`; the joint period owed (#62) | [`section_lock::Settled::lock`], [`section_lock::Lock`], [`section_lock::JointLock`], [`section_lock::LockReader`] |
//! | the ring's navigator | `Holon/Navigator.{mapRotor_order, map_pow_mod_order, map_turn_lossless}` | [`Ring::navigator`] over `navigator::Transport::Map` |
//! | the block incidence, the contrast map read from its blocks, and the Holarchy chart | `Holon/Complex.{blockIncidence, block_flat_closed}`, `Holarchy/Join.interconnect` | [`Field::connection`], [`Field::contrast`], [`Field::holarchy`] |
//! | the port's returns | `Holarchy/Reception.InteractionReturn` (the owner's, generic in its payloads) | [`ExecutionPort`] |
//! | the mount certifies the Holarchy; its parametric orientation carries the aeons | `Holarchy/Join.interconnect`, `Holarchy/Join.Holarchy.parametric` | [`Reference`] (`mount_with`), [`reference::Resident::parametric`] |
//! | native generation: the joint section, joint against marginals, the release at width zero, the consumer equation (U6) | `HNN/Prediction.{refine_iterate, jointSection, jointSection_receive, joint_not_marginals, release_width_zero, plural_section_held, consumer_eq}` | [`prediction`] (the bank's release; the linear readout that realized `refine_iterate` and `jointSection` was retired, batch H) |
//! | the release's own comparison: the eigen-derivative at a simple root, a max comparison's descent, a strict decrease by disjoint enclosures (U6) | `HNN/ExecutedComparison.{product_deriv, simple_root_deriv, log_modulus_deriv, max_descends, sum_max_descends, disjoint_enclosures_decrease, predicates_release_the_section}` | [`executed`] |
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
pub mod contact;
pub mod dynamic_section;
pub mod encoding;
pub mod executed;
pub mod field;
pub mod keys;
pub mod moment;
pub mod paired;
pub mod pending;
pub mod phase_family;
pub mod port;
pub mod prediction;
pub mod physical;
pub mod propagation;
pub mod ratio;
pub(crate) mod realization;
pub mod receiving;
pub mod reference;
pub mod retention;
pub(crate) mod state_text;
pub mod ring;
pub mod section_lock;
pub mod wave;
pub mod word;

pub use chart::{ChartKey, ChartReading, ChartStart, ChartWords, Charts, Remainders, WordLattice};
pub use constitution::{
    Carrier, CarrierBits, Constitution, Family, Lattice, Locus, NormalLaw, Reach, StepReading,
};
pub use contact::{
    BreakReceipt, ContactLock, ContactReading, KindCensus, LockDeclaration, SiteReading,
    contact_readings, site_kinds, site_readings,
};

pub use encoding::{Encoded, Encoding, EncodingError, PassageChart, PortCell};
pub use field::{
    ConstitutionRead, Contact, FieldMaterial, ContactDeclaration, Current, Field, FieldDeclaration, Ring,
    RingDeclaration,
};
pub use keys::{KeyLocation, RingKeys, locate_keys};
pub use moment::{Capacity, PairPort, SourceMoment};
pub use pending::PendingRatio;
pub use port::{
    Deposit, ExecutionPort, Handle, MomentId, PendingId, Pullback, StagedId, Transpose,
};
pub use ratio::{Faces, HolonRatio, RatioCovector};
pub use receiving::{ActiveAddress, LetterReader, ReceivingPhases, ReceivingRead};
pub use reference::{Cut, Exposure, Reference, Resident};
pub use retention::AeonBoundary;
pub use ring::{Floquet, FloquetReading, PumpDeclaration, PumpSchedule, ResonatorMaterial};
pub use word::{
    Absorption, ChainedBalance, ReceptionCarry, Released, ResonatorBalance, SourceOpeningReceipt,
    Word, WordOpening,
};

#[cfg(test)]
pub(crate) mod tests;

use thiserror::Error;

use crate::aeon::AeonError;
use crate::compression::CompressionError;
use crate::compression::landmark::context::ContextError;
use crate::holon::HolonError;
use crate::holon::contact::ContactError;
use crate::holon::contact::menu::MenuError;
use crate::holon::parametron::ParametronError;
use crate::ratio::Rat;
use crate::ratio::algebraic::ExactValueError;
use crate::ratio::exponentiated::RatioError;
use crate::ratio::linear::ExactLinearError;
use crate::ratio::polynomial::ExactPolynomialError;
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
    #[error(transparent)]
    Exact(#[from] ExactValueError),
    #[error(transparent)]
    Context(#[from] ContextError),
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
    #[error("class {code} lies outside the field's {alphabet} classes")]
    CellOutside { code: usize, alphabet: usize },
    /// THE_MACHINE guard 9: an encoded passage this field does not read.
    #[error("the encoded passage does not enter this field: {reason}")]
    Unadmitted { reason: &'static str },
    /// The encoding's refusal at a consuming call (its squares on the stepped lift). Boxed: the
    /// encoding's refusals are wide.
    #[error(transparent)]
    Encoding(Box<encoding::EncodingError>),
    #[error("a count of the moment would pass the machine word; the moment refuses it")]
    CountOverflow,
    #[error("ring {ring} is a source ring but the constitution carries no source port for it")]
    MissingSourcePort { ring: usize },
    #[error("the constitution carries no receiving map for ring {ring}")]
    MissingReceivingMap { ring: usize },
    #[error(
        "aperture {aperture} exceeds the receiving ring's observability rank {rank} over the word"
    )]
    Observability { aperture: usize, rank: usize },
    #[error("the code tolerance must be a positive rational, found {tolerance}")]
    Tolerance { tolerance: Rat },
    #[error("the released code length's excursion height must be nonnegative, found {height}")]
    ExcursionHeight { height: Rat },
    #[error("an excursion's certified decrease must be nonnegative, found {decrease}")]
    WindowDecrease { decrease: Rat },
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
        "a carrier on 2^-{exponent} Z re-bases {levels} levels only before its deposit stages an entry ({staged} staged) and onto an exponent that fits a u32"
    )]
    Rebase {
        exponent: u32,
        levels: u32,
        staged: usize,
    },
    #[error(
        "locus {locus:?} reads its lattice outside its deposits, so its re-base is not this move: only a contact's channel re-bases"
    )]
    RebaseLocus { locus: Locus },
    #[error(
        "ring {ring}'s transport modulus {modulus} is not a passive modulus on the source port's lattice (0 < ρ ≤ 1)"
    )]
    Transport { ring: usize, modulus: Rat },
    #[error(
        "ring {ring}'s passage spans {span} ticks against its period {period} (or was re-keyed): a transport of modulus below one reads each datum's age from its phase, which aliases past one turn; a moment opened at the constitution carries the leaky count instead (`SourceMoment::open_with`)"
    )]
    AliasedAges { ring: usize, span: u64, period: u64 },
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
    #[error(
        "the deposit's linear steps declare no reach: their certified step reads the stations, re-entries and ticks their covectors summed"
    )]
    MissingReach,
    #[error(
        "the deposit steps locus {locus:?} by more than one linear step; its certified step reads one compare's returns at a locus, through the deposit's one reach"
    )]
    RepeatedLinearStep { locus: Locus },
    #[error(
        "the deposit steps the family {family:?} of locus {locus:?} more than once; its certified step reads one compare's returns at a family, through the deposit's one reach"
    )]
    RepeatedFactorStep {
        locus: Locus,
        family: crate::hnn::constitution::Family,
    },
    #[error(
        "ring {ring}'s resonator is not certified passive and its Floquet reach is refused ({refusal:?}): no step is certified through it"
    )]
    UncertifiedGain {
        ring: usize,
        refusal: ring::FloquetRefusal,
    },
    #[error(
        "contact {contact}'s declared boost stores indefinite energy in its signed stiffness, so the medium's growth is not certified (owed in #62): no step is certified through it"
    )]
    ActiveContact { contact: usize },
    #[error(
        "contact {contact}'s conductance has no bound at every lift (its exponent β_a is negative): no channel family's step is certified there"
    )]
    UncertifiedConductance { contact: usize },
    #[error(
        "contact {contact}'s carried momentum lies outside the range of its storage after the deposit: the law of a momentum a singular storage cannot hold is owed (#62)"
    )]
    HeldMomentum { contact: usize },
    #[error(
        "the deposit's storage growth is not certified: no dyadic ε in the declared search makes Q_(k+1) ⪯ (1 + ε) Q_k on the contacts' and resonators' storage forms"
    )]
    UncertifiedStorage,
    #[error("deposits stopped at commit {commit}, when the constitution reached its budget")]
    DepositsStopped { commit: u64 },
    #[error(
        "the deposit was staged at commit {staged}; the published constitution is at {published}"
    )]
    StaleDeposit { staged: u64, published: u64 },
    #[error("the locus {locus:?} is released; no deposit reaches it")]
    ReleasedLocus { locus: Locus },
    #[error("the continuing state refused: {what}")]
    ContinuingState { what: &'static str },
    #[error("the admitted family adds receivers on rings {receivers:?} to the previous boundary's")]
    AdmittedGrowth { receivers: Vec<usize> },
    #[error("the resident handle counter has exhausted its u64 carrier")]
    HandleCounterExhausted,
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
    #[error("ring {ring}'s resonator material is malformed: {what}")]
    Resonator { ring: usize, what: &'static str },
    /// [definition; agent-inferred, October 9] A matched wave the port does not take
    /// (`hnn::wave`): not matched to the port, or a tick whose balance does not close.
    #[error("the matched wave refused: {what}")]
    Wave { what: &'static str },
    #[error("ring {ring}'s Floquet certificate is refused: {refusal:?}")]
    UncertifiedFloquet {
        ring: usize,
        refusal: ring::FloquetRefusal,
    },
    #[error(transparent)]
    Polynomial(Box<ExactPolynomialError>),
    #[error(
        "the chart {chart:?} did not refine below its certificate {certificate}: the target is {target}"
    )]
    ChartCertificate {
        chart: ChartKey,
        certificate: Box<Rat>,
        target: Box<Rat>,
    },
    /// [definition; agent-inferred, October 9] A paired port's map is off its subspace
    /// (`hnn::paired`, "The paired deposit"): the first failing column, its partner and row.
    #[error(
        "a paired port is not equivariant: column {column} against its partner column {partner} first differs at row {row}"
    )]
    PairedPort {
        column: usize,
        partner: usize,
        row: usize,
    },
    /// [definition; agent-inferred, October 9] A paired port's deposit reaches a class outside its
    /// pairing's family, where the subspace does not constrain the port.
    #[error("a paired port's deposit reaches class {class}, outside its pairing's family")]
    PairedOutside { class: usize },
}

impl From<encoding::EncodingError> for HnnError {
    fn from(error: encoding::EncodingError) -> Self {
        Self::Encoding(Box::new(error))
    }
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
    Polynomial(ExactPolynomialError),
);

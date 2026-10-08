//! **The word: one evaluation at one cut's fixed operands, opening at zero change.**
//!
//! [definition] A word reads the medium `(Θ, λ)` at the cut once ([`Operands::at_cut`]) and
//! propagates the change on it (design (a), "The law of one passage", `open`, `tick`, `release`):
//!
//! - **open**: every wave and contact state is zero; the only nonzero storage is
//!   `s_g(0) = P_g^(τ_g) m̃_g` on the source rings, from the moment's counts (Lean
//!   `HNN/Retention.word_opens_at_zero`). Nothing of an earlier word is read, because nothing of it
//!   persists: [`crate::hnn::Current`] has no wave field;
//! - **ticks**: one contact hop per tick of the word's own hop clock (a [`Clock`] of step `h`), every
//!   operand fixed; each tick's global power balance is recorded and closes up to its reported
//!   residual ([`TickBalance::closes`]);
//! - **the receiving epochs**: `e_j = e_0 + j`, `j < A`, each read by tick `e_j`'s junction; the word
//!   evaluates `e_max = e_0 + A` junction steps, and the last stops after its junction;
//! - **release**: at the word's end every wave and contact state is released as the word's emitted
//!   exchange, with its power, and every carried remainder is released and reported with it;
//!   nothing is carried to the next word ([`Word::release`] consumes it) unless a declared reception
//!   carry reads its end change ("Continuing motion across receptions" below).
//!
//! [definition] **The carried transients** (the lattice word; Lean `HNN/LatticeWord.{feedback_tick,
//! carried_word_accounting}`). On the field's declared lattices ([`crate::hnn::chart`]) the word
//! carries every transient on `2^(−L_w)ℤ` with error feedback: the opening storage, and at each tick
//! the junction's anchor `v_r`, the element output, a loaded ring's returned storage `s_r′`, the
//! resonator's solve rate and state, the contact's solved `ζ_a`, its state `(u_a, w_a)` and the
//! arriving waves. The element drive and returned storage have separate carries. Each is the exact image of the carried values under the
//! executed tick plus its carried remainder, split at the nearest lattice point, ties upward
//! ([`crate::hnn::chart::carry`]); `Σ_t x_t + r_T = Σ_t y_t` entry by entry, and the word releases
//! the remainders `r_T` at its end ([`Released::remainders`]). Every product with a chart runs on
//! the carried values' integer coordinates. Under the exact law nothing is split and every
//! remainder stays zero.
//!
//! [definition] **The loaded field balance** (Lean `HNN/Word`, `HNN/Ring`). A junction sends `(b,c)`
//! to the ring element; its output `e` is split at the word lattice and drives a declared resonator.
//! The resonator returns `s′ = e − (2/Y)ω`, which is split independently and becomes the next ring
//! storage. Its port work cancels the field's signed loaded-port term; element, returned-wave and
//! resonator-state splits remain explicit in [`FieldBalance`]. The resonator's two-state motion and
//! its adjoint live only in this word. Its four learned gain coordinates update only through the
//! post-word [`PowerForm`] deposit, whose work includes the resonator's end-state form change.
//! [`WordBalance::of`] closes the whole word from its release, on every realization of the port,
//! and [`Word::partings`] reads each declared contact's break receipt at every transit
//! (`hnn::contact::BreakReceipt`).
//!
//! [definition] The word keeps its own per-tick waves, bounded by its `e_max` junction steps, for
//! its return to read in reverse; that memory lives only in the word and is dropped with it
//! (design R2 H2). It is one evaluation on one moment, not an occurrence tape. A refine keeps its
//! word, without the borrow of its field (`KeptWord`), for the compare at the same commit, whose
//! return consumes it.
//!
//! [definition; agent-inferred, U6's native generation (Brandon, September 29); its consumer, the
//! linear readout, retired September 30 (batch H, at `f5fd8f3b`), the law held here]
//! **Continuing motion within a refinement.** A word may open on the change the previous word of
//! the same refinement left ([`Word::continuing`]): its storage waves, arriving waves, contact
//! states and resonator states carry across the word's boundary instead of being released, with a
//! declared injection added at the storage ports (the request's moment re-entering). The word then
//! ticks on the refinement's clock: its hop clock and every resonator's pump phase read the ticks
//! since the refinement opened ([`Word::opened_at`]), so a pump's cycle and the balance's resonator
//! energies chain across the boundary. Only a refinement, or a reception under a declared carry
//! (below), opens a continuing word; the refinement
//! owns its words until its return consumes them, so the change still lives only inside the
//! refinement (bounded by its words' ticks, never by a source length), and [`Current`] still holds
//! no wave (guard 16). A word opened at rest ([`Word::open`]) is the continuing word opened on the
//! zero change at tick zero (Lean `HNN/Retention.word_opens_at_zero` is that case).
//!
//! [definition; agent-inferred, October 3; the
//! [reception carry](../../../../research/records/2026-10-03_THE_RECEPTION_CARRIES_THE_INTERIOR_CHANGE_THE_SOURCE_PORT_IMPOSES_THE_MOMENT_AND_REST_IS_COMPLETE_ABSORPTION.md)]
//! **Continuing motion across receptions.** Under a declared carry, a reception's word opens on the
//! interior of the change arriving at the last crossing of the previous word read,
//! with the source rings' storage imposed by the moment ([`Word::open_received`],
//! [`ReceptionCarry`]), at that crossing's tick: the field's elapsed ticks are the hops every
//! earlier word ran, so a declared resonator's pump continues across receptions. The resident, not [`Current`], holds the one carried change and its tick (guard
//! 16 stands). Complete absorption ([`Absorption::Complete`]) is the rest limit: the word at rest,
//! exactly, on a field with no declared resonator. The conditional return stops at the opening.
//! The opt-in held-contact domain ([`variation::HeldContactVariation`]) retains the complete
//! material first variation of that current and pairs it with the next full opening covector.
//! Its continuing consumer binds the reached current+delayed covector to the actual native
//! contact cut, applies a physically admitted factor proposal, and transports the full
//! differential through the canonical held-momentum crossing. The explicit realized-translation
//! action holds applied increments as controls; it does not differentiate the learner policy or
//! certify historical finite score decrease. Neither path keeps a tape of Words.
//!
//! [definition; agent-inferred] **Within a step the rings, then the contacts, run together** (the
//! hardware law; `hnn::realization`): every junction reads only its own storage and arrivals and
//! its own anchor's remainder, every element only its own junction and storage remainder, and every
//! transit only its two ends' outgoing waves and its own state and remainders, and each writes only
//! its own slot; the balance terms are summed after, in ring and contact order.
//!
//! A word is not `Clone` (guard 2):
//!
//! ```compile_fail,E0599
//! use holonics::hnn::Word;
//! fn duplicate(word: Word<'_>) -> (Word<'_>, Word<'_>) {
//!     (word.clone(), word)
//! }
//! ```
//!
//! and the field it borrows has no lifetime parameter (guard 2):
//!
//! ```compile_fail,E0107
//! fn borrowed(field: holonics::hnn::Field<'static>) {}
//! ```

pub mod continuation;
pub mod finite_gain;
pub mod work;
pub mod variation;

use std::collections::BTreeSet;

use num_bigint::BigUint;
use num_traits::{Signed, Zero};

use crate::hnn::HnnError;
use crate::hnn::chart::{ChartReading, Charts, Remainders, carry};
use crate::hnn::constitution::{Lattice, Locus};
use crate::hnn::contact::{BreakReceipt, signed_stiffness};
use crate::hnn::field::{ConstitutionRead, Current, Field};
use crate::hnn::moment::SourceMoment;
use crate::hnn::propagation::{
    Junction, Operands, TickBalance, contact_exponent, element_step, global_power, gram,
    participation, scattering_about, transit_defect, transit_solve, transit_update,
};
use crate::hnn::realization::indexed;
use crate::hnn::receiving::ReceivingPhases;
use crate::hnn::ring::{ResonatorMaterial, ResonatorRemainders, ResonatorStep};
use crate::navigator::Clock;
use crate::ratio::exponentiated::power_of_two;
use crate::ratio::linear::ExactRatMatrix;
use crate::ratio::linear::vector::{add, dot, sub};
use crate::ratio::{Rat, integer};

/// One junction step's record: the change at the step's start, every ring's carried anchor, and
/// for a full tick every ring element's midpoint `x̄_r` and every contact's midpoint rate `ω_a` as
/// executed. The word's return reads these in reverse.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Passage {
    pub(crate) storage: Vec<Vec<Rat>>,
    pub(crate) arrivals: Vec<[Vec<Rat>; 2]>,
    pub(crate) states: Vec<[Vec<Rat>; 2]>,
    pub(crate) anchors: Vec<Vec<Rat>>,
    pub(crate) midpoints: Vec<Vec<Rat>>,
    pub(crate) rates: Vec<Vec<Rat>>,
}

/// [definition] **The word's carried remainders**: one per carried transient's coordinate (the
/// opening storage's included in the storage's), each in the half-open cell of the transients'
/// lattice. Zero under the exact law.
#[derive(Clone, Debug, PartialEq, Eq)]
struct Carried {
    anchors: Vec<Vec<Rat>>,
    /// The returned ring-storage stream's split remainder; zero at open for a loaded port.
    storage: Vec<Vec<Rat>>,
    /// The element-output stream's split remainder; a loaded ring inherits the source-open split.
    element_drive: Vec<Vec<Rat>>,
    solves: Vec<Vec<Rat>>,
    arrivals: Vec<[Vec<Rat>; 2]>,
    states: Vec<[Vec<Rat>; 2]>,
}

impl Carried {
    fn released(&self) -> Remainders {
        Remainders::of(
            self.anchors
                .iter()
                .chain(&self.storage)
                .chain(&self.element_drive)
                .chain(&self.solves)
                .flatten()
                .chain(self.arrivals.iter().flatten().flatten())
                .chain(self.states.iter().flatten().flatten()),
        )
    }
}

/// [definition] **A word** over a borrowed field. It owns its operands, its hop clock and the
/// change: the storage waves, the arriving waves, the contact states, their per-tick values and
/// the carried remainders.
#[derive(Debug)]
pub struct Word<'c> {
    /// The native source/material producer of a source-bound continuing word.
    native_source: Option<(
        crate::hnn::constitution::Constitution,
        Current,
        std::sync::Arc<SourceMoment>,
        // Support read at the actual opening, before any tick; never the cut-end support.
        Vec<usize>,
    )>,
    field: &'c Field,
    operands: Operands,
    clock: Clock,
    storage: Vec<Vec<Rat>>,
    arrivals: Vec<[Vec<Rat>; 2]>,
    states: Vec<[Vec<Rat>; 2]>,
    carried: Carried,
    passage: Vec<Passage>,
    balances: Vec<TickBalance>,
    ended: bool,
    peak_bits: u64,
    /// The last junction's residual: the executed anchors' power against the participation mean.
    last: Rat,
    /// The last junction's certified bound on its residual.
    last_bound: Rat,
    /// The power of the change as the last full tick left it: the next tick's `before`, read once.
    /// Only `tick` sets it and `last_junction` clears it, so it is always the current change's.
    settled: Option<Rat>,
    /// Each ring's resonator inside the word (campaign 2, `hnn::ring`), where one is declared: its
    /// state, its carried remainders and its executed ticks. It opens at zero with the word and is
    /// released with it.
    resonators: Vec<Option<Resonance>>,
    /// Every full tick's field balance with every term stated.
    fields: Vec<FieldBalance>,
    /// Every full tick's break receipts, per contact where its break law is declared.
    partings: Vec<Vec<Option<BreakReceipt>>>,
    /// The refinement clock's ticks at the word's open: zero for a word opened at rest, the ticks
    /// of the refinement's earlier words for a continuing word ([`Word::continuing`]).
    opened_at: usize,
}

/// [definition] **A resonator inside a word**: its state `[u, w]`, its carried remainders, and its
/// executed ticks in order.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Resonance {
    /// Opening storage at the carried state and actual previous pump phase.
    pub open: Rat,
    pub state: [Vec<Rat>; 2],
    pub remainders: ResonatorRemainders,
    pub steps: Vec<ResonatorStep>,
}

/// [definition] **A resonator's balance over one word** (campaign 2, `hnn::ring`; Lean
/// `HNN/Ring.ring_tick_executed_energy_balance` summed over the word's ticks): its ring, its ticks,
/// its storage at the word's open and end, its pump, port and dissipation
/// work, its chart defect and its split summed over the ticks with their certified bound
/// ([`crate::hnn::ring::ResonatorStep::bound`] summed), and the remainders its end releases. It is
/// what the word's release returns of a resonator, so every realization of the port reads it alike
/// ([`Released::resonators`]).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ResonatorBalance {
    pub ring: usize,
    pub ticks: usize,
    pub open: Rat,
    pub end: Rat,
    pub pump: Rat,
    pub port: Rat,
    pub dissipation: Rat,
    /// The signed defect of the executed nonlinear constitutive integration, separate from
    /// the numerical solve and split certificates. Zero for the quadratic midpoint law.
    pub integration: Rat,
    pub chart: Rat,
    pub split: Rat,
    /// The certified bound on `|chart + split|`, the ticks' bounds summed.
    pub bound: Rat,
    pub released: Remainders,
}

impl ResonatorBalance {
    /// **The balance of a resonator's executed ticks** in a word.
    pub fn of(ring: usize, resonance: &Resonance) -> Self {
        let sum =
            |term: fn(&ResonatorStep) -> &Rat| -> Rat { resonance.steps.iter().map(term).sum() };
        Self {
            ring,
            ticks: resonance.steps.len(),
            open: resonance.open.clone(),
            end: resonance
                .steps
                .last()
                .map_or_else(|| resonance.open.clone(), |step| step.after.clone()),
            pump: sum(|step| &step.pump),
            port: sum(|step| &step.port),
            dissipation: sum(|step| &step.dissipation),
            integration: sum(|step| &step.integration),
            chart: sum(|step| &step.chart),
            split: sum(|step| &step.split),
            bound: sum(|step| &step.bound),
            released: Remainders::of(resonance.remainders.all()),
        }
    }

    /// **It closes**: `E_end − E_open = pump + port − dissipation + chart + split`,
    /// with `|chart + split| ≤ bound`.
    pub fn closes(&self) -> bool {
        &self.end - &self.open
            == &self.pump + &self.port - &self.dissipation
                + &self.integration
                + &self.chart
                + &self.split
            && (&self.chart + &self.split).abs() <= self.bound
    }
}

/// [definition] **One executed tick's loaded balance, every term stated** (Lean
/// `HNN/Ring.{loaded_word_stage_balance, loaded_tick_executed_interconnection_balance}`). The
/// junction's anchor sends `(b,c)` to the ring element, which returns `e`; a
/// declared resonator is driven by carried `e` and returns `s′ = e−(2/Y)ω` as the ring's next
/// storage. Its received port work equals the field's signed loaded-port term with opposite sign.
/// The balance separately reports the element split, returned-wave split, resonator's internal
/// state split, and each chart residual, and bounds them together: the field's executed residual
/// plus the resonator's chart and split lie within the tick's field bound plus the resonator's
/// ([`crate::hnn::ring::ResonatorStep::bound`]). No deposit happens within a tick; the gain
/// deposition work is read at the commit that follows it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FieldBalance {
    pub before: Rat,
    pub after: Rat,
    pub dissipation: Rat,
    pub resist: Rat,
    pub contrast: Rat,
    pub junction: Rat,
    pub element_chart: Rat,
    pub element_split: Rat,
    pub transit_chart: Rat,
    pub transit_split: Rat,
    pub resonator_before: Rat,
    pub resonator_after: Rat,
    pub pump: Rat,
    pub port: Rat,
    pub resonator_dissipation: Rat,
    pub resonator_integration: Rat,
    pub resonator_chart: Rat,
    pub resonator_split: Rat,
    /// The field's signed port term, equal to minus the loaded resonator's received port work.
    pub loaded_port: Rat,
    /// The loaded return's lattice split, an explicit field residual.
    pub loaded_split: Rat,
    /// **The interconnection's defect**: resonator port work plus the field's signed loaded-port
    /// work. [definition] It is zero **by construction** for a loaded port: the field's term is
    /// formed as the negative of the resonator's received work (`loaded_port = −port`), the
    /// power-neutral interconnection stated structurally, not measured. It equals the resonator's
    /// port work when the port is unloaded. The loaded balance's evidence is its bounded
    /// residuals: the field's executed residual and the resonator's chart and split within
    /// [`FieldBalance::bound`] plus [`FieldBalance::resonator_bound`].
    pub interconnection: Rat,
    /// The tick's certified bound on the field's executed residual ([`TickBalance::bound`]).
    pub bound: Rat,
    /// The resonators' certified bound on their chart and split terms at this tick.
    pub resonator_bound: Rat,
}

impl FieldBalance {
    /// The field's defects: the sum [`TickBalance`]'s `residual` lumps.
    pub fn residual(&self) -> Rat {
        &self.junction
            + &self.element_chart
            + &self.element_split
            + &self.transit_chart
            + &self.transit_split
            + &self.loaded_split
    }

    /// **The combined balance closes exactly with its stated terms** (Lean
    /// `HNN/Ring.loaded_tick_executed_interconnection_balance`):
    /// `(P′ + E′) − (P + E) = − dissipation + resist + Π_c +
    /// defects + pump − resonator dissipation + resonator chart + resonator split +
    /// interconnection`, and the executed residuals lie within their certified bounds:
    /// `|defects + resonator chart + resonator split| ≤ bound + resonator bound`.
    pub fn closes(&self) -> bool {
        let executed = self.residual() + &self.resonator_chart + &self.resonator_split;
        &self.after + &self.resonator_after - &self.before - &self.resonator_before
            == -&self.dissipation + &self.resist + &self.contrast + self.residual() + &self.pump
                - &self.resonator_dissipation
                + &self.resonator_integration
                + &self.resonator_chart
                + &self.resonator_split
                + &self.interconnection
            && executed.abs() <= &self.bound + &self.resonator_bound
    }
}

/// [definition] **A word's end change** (`x`, the change the word releases and its commit reads):
/// the storage waves per ring, the arriving waves per contact (`[at from, at to]`) and the contact
/// states `[u, w]`, as the last junction step left them. A reception's carried change is the same
/// object at the word's last crossing, before that junction scatters it
/// ([`Word::reception_end`]).
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct EndChange {
    pub storage: Vec<Vec<Rat>>,
    pub arrivals: Vec<[Vec<Rat>; 2]>,
    pub states: Vec<[Vec<Rat>; 2]>,
    /// Word-local resonator states at the end and the phase whose form measures them.
    pub resonators: Vec<Option<[Vec<Rat>; 2]>>,
    /// [definition] The pump phase whose form measures a loaded ring's end state: its last executed
    /// tick's, and with no full tick the phase `0` at which the open state is read
    /// ([`crate::hnn::ring::ResonatorOperands::step`] reads `before` at tick `0` on phase `0`).
    /// `None` where no resonator is declared.
    pub resonator_phases: Vec<Option<usize>>,
}

/// [definition; agent-inferred, October 3; the
/// [reception carry](../../../../research/records/2026-10-03_THE_RECEPTION_CARRIES_THE_INTERIOR_CHANGE_THE_SOURCE_PORT_IMPOSES_THE_MOMENT_AND_REST_IS_COMPLETE_ABSORPTION.md)
/// §2.1, §2.4] **A reception's carried end**: the change `x_k(end)` the word's motion
/// reached, arriving at its last crossing, and that crossing's tick `t_(k+1)`, the sum of the hops
/// every word of the chain executed (record B §2.4: the last junction is a crossing whose hop has
/// not run, so the next word opens on it and scatters it). It is the field's present motion, of
/// the field's fixed shape, overwritten at every reception: not a record of which windows preceded.
///
/// [definition; record B §2.3a, the deposit record §3] Beside the change it carries the references
/// the motion was measured in at word `k`'s cut: each contact's conductance `G_a`, the reference of
/// its arriving waves, and each contact's momentum `π_a = C_a w_a`, the canonical state the deposit
/// holds, and each carried resonator's momentum `π_r = C_r w_r`, the canonical state its step
/// advances on (record B §2.4). The next opening crosses the change into its own references
/// ([`ReceptionCarry::crossed`]).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReceptionCarry {
    pub change: EndChange,
    pub ticks: usize,
    /// `G_a` at word `k`'s cut, per contact.
    pub conductances: Vec<Rat>,
    /// `π_a = C_a w_a` with word `k`'s storage, per contact.
    pub momenta: Vec<Vec<Rat>>,
    /// `π_r = C_r w_r` with word `k`'s resonator capacity, per ring slot; `None` where no resonator
    /// state is carried.
    pub resonator_momenta: Vec<Option<Vec<Rat>>>,
}

/// [definition; the deposit record (October 3) §2–§3, Lean
/// `HolonicsResearch/HNN/MoveDirection.held_momentum_loss`] **The rate a contact carries across a
/// change of its storage at held momentum**: `w′ = w + δ` with `C′ δ = π − C′ w`, so `C′ w′ = π`.
/// The solve fixes `w′` only modulo `ker C′`, which no later tick reads (the transit reads `w` only
/// through `C w`); [agent-inferred] the jump `δ` is the particular point of the reduced solve, so
/// `w′ = w` exactly where `C′ w = π` (no mass moved). A momentum outside `range C′` is refused,
/// naming the contact.
fn held_rate(
    contact: usize,
    rate: &[Rat],
    momentum: &[Rat],
    storage: &ExactRatMatrix,
) -> Result<Vec<Rat>, HnnError> {
    let target = sub(momentum, &storage.apply(rate)?);
    if target.iter().all(Zero::is_zero) {
        return Ok(rate.to_vec());
    }
    match storage.preimage_fibre(&target)? {
        Some((jump, _)) => Ok(add(rate, &jump)),
        None => Err(HnnError::HeldMomentum { contact }),
    }
}

/// [definition; record B §2.4] **The rate a resonator carries across a change of its capacity at
/// held momentum**: the resonator's step advances on `(u, 2C_r w)` (`ResonatorOperands::step`'s
/// right side `2C w + hβ − hK u`), the contact transit's canonical state, so the deposit holds
/// `C′_r w′_r = π_r` exactly as [`held_rate`] holds a contact's; refused, naming the ring, on a
/// momentum outside `range C′_r`.
fn held_resonator_rate(
    ring: usize,
    rate: &[Rat],
    momentum: &[Rat],
    capacity: &ExactRatMatrix,
) -> Result<Vec<Rat>, HnnError> {
    held_rate(ring, rate, momentum, capacity).map_err(|refusal| match refusal {
        HnnError::HeldMomentum { .. } => HnnError::Resonator {
            ring,
            what: "a carried resonator momentum outside its capacity's range",
        },
        other => other,
    })
}

/// [definition; record B §2.3a, Lean `HNN/Ring.two_port_reference_balance`] **A wave crossing a
/// reference change** from `G` to `G′`: the transmitted wave `(1 + Γ) a = 2G/(G + G′) · a` in `G′`.
/// The reflection `Γ a`, `Γ = (G − G′)/(G + G′)`, leaves in `G`.
fn transmitted(wave: &[Rat], from: &Rat, to: &Rat) -> Vec<Rat> {
    if from == to {
        return wave.to_vec();
    }
    let gain = integer(2) * from / (from + to);
    wave.iter().map(|x| x * &gain).collect()
}

/// [definition; record B §2.3a] **The power a reference change reflects**:
/// `(h/4) Γ² G |a|²`, the wave's power `(h/4) G |a|²` less the transmitted wave's `(h/4) G′ |(1 + Γ) a|²`.
fn reflected_power(step: &Rat, wave: &[Rat], from: &Rat, to: &Rat) -> Rat {
    if from == to {
        return Rat::zero();
    }
    let reflection = (from - to) / (from + to);
    step / integer(4) * &reflection * &reflection * from * dot(wave, wave)
}

impl ReceptionCarry {
    /// [definition; the reception carry §2.1] **The interior change** `Π_int x_k(end)`: the carried
    /// change with every source ring's storage at zero, which the moment's imposed storage then
    /// replaces at the source port. Arrivals, contact states and resonator states are interior.
    pub fn interior(&self, field: &Field) -> EndChange {
        interior_of(field, self.change.clone())
    }

    /// [definition; record B §2.3a, §2.4, the deposit record §3] **The carried change crossed into
    /// the next opening's references**, given its contacts' conductances `G′_a` and storage `C′_a`
    /// and its resonators' capacities `C′_r`: each contact's arriving waves transmitted,
    /// `a′ = (1 + Γ_a) a`, each contact's rate held at momentum, `C′_a w′_a = π_a`, and each
    /// carried resonator's rate held at its momentum, `C′_r w′_r = π_r`; the storage waves and every
    /// displacement as carried. Refused on a momentum a storage cannot hold, or a carried resonator
    /// state with no declared resonator.
    pub fn crossed(
        &self,
        conductances: &[Rat],
        storage: &[&ExactRatMatrix],
        resonators: &[Option<&ExactRatMatrix>],
    ) -> Result<EndChange, HnnError> {
        let shaped = conductances.len() == self.conductances.len()
            && storage.len() == self.momenta.len()
            && self.change.arrivals.len() == self.conductances.len()
            && resonators.len() == self.change.resonators.len()
            && self.resonator_momenta.len() == self.change.resonators.len();
        if !shaped {
            return Err(HnnError::Shape {
                what: "the next opening's contacts against the carry's",
                expected: self.conductances.len(),
                found: conductances.len(),
            });
        }
        let mut change = self.change.clone();
        for (a, ((pair, state), (to, after))) in change
            .arrivals
            .iter_mut()
            .zip(change.states.iter_mut())
            .zip(conductances.iter().zip(storage))
            .enumerate()
        {
            let from = &self.conductances[a];
            for wave in pair.iter_mut() {
                *wave = transmitted(wave, from, to);
            }
            state[1] = held_rate(a, &state[1], &self.momenta[a], after)?;
        }
        for (ring, ((state, momentum), capacity)) in change
            .resonators
            .iter_mut()
            .zip(&self.resonator_momenta)
            .zip(resonators)
            .enumerate()
        {
            match (state, momentum, capacity) {
                (None, None, _) => {}
                (Some(state), Some(momentum), Some(capacity)) => {
                    state[1] = held_resonator_rate(ring, &state[1], momentum, capacity)?;
                }
                _ => {
                    return Err(HnnError::Resonator {
                        ring,
                        what: "a carried resonator state crosses only onto a declared resonator, with its momentum",
                    });
                }
            }
        }
        Ok(change)
    }

    /// [definition; record B §2.3a] **What the lift's reference change emits**:
    /// `Σ_a (h/4) Γ_a² G_a (|a_g|² + |a_h|²)` at the next opening's conductances `G′_a`. It is the
    /// lift's work on the carried waves with the sign reversed, so the lift never raises them.
    pub fn reflected(&self, step: &Rat, conductances: &[Rat]) -> Rat {
        self.change
            .arrivals
            .iter()
            .zip(self.conductances.iter().zip(conductances))
            .map(|([g, h], (from, to))| {
                reflected_power(step, g, from, to) + reflected_power(step, h, from, to)
            })
            .sum()
    }

    /// [definition; record B §2.1, §2.3a] **The next opening's interior change**: the carried change
    /// crossed into the opening's references ([`ReceptionCarry::crossed`]) with every source ring's
    /// storage at zero, which the moment's imposed storage then replaces.
    pub fn opening(
        &self,
        field: &Field,
        conductances: &[Rat],
        storage: &[&ExactRatMatrix],
        resonators: &[Option<&ExactRatMatrix>],
    ) -> Result<EndChange, HnnError> {
        Ok(interior_of(
            field,
            self.crossed(conductances, storage, resonators)?,
        ))
    }

    /// [definition; agent-inferred, October 3; the reception carry §2.2] **The carry after the
    /// boundary's absorption at the word's end**: under [`Absorption::Nothing`] the end change as it
    /// stands; under [`Absorption::Complete`] every coordinate emitted, so only the field's elapsed
    /// ticks remain (the rest change, every declared resonator at rest in the carried clock).
    pub fn absorbed(self, absorption: Absorption) -> Self {
        match absorption {
            Absorption::Nothing => self,
            Absorption::Complete => {
                let rest = |waves: &[Vec<Rat>]| waves.iter().map(|w| zeros(w.len())).collect();
                let pairs = |pairs: &[[Vec<Rat>; 2]]| {
                    pairs
                        .iter()
                        .map(|[a, b]| [zeros(a.len()), zeros(b.len())])
                        .collect()
                };
                let EndChange {
                    storage,
                    arrivals,
                    states,
                    resonators,
                    ..
                } = &self.change;
                Self {
                    change: EndChange {
                        storage: rest(storage),
                        arrivals: pairs(arrivals),
                        states: pairs(states),
                        resonators: vec![None; resonators.len()],
                        resonator_phases: vec![None; resonators.len()],
                    },
                    ticks: self.ticks,
                    momenta: rest(&self.momenta),
                    resonator_momenta: vec![None; resonators.len()],
                    conductances: self.conductances,
                }
            }
        }
    }

    /// [definition; agent-inferred, October 4; the reception carry §8] **The carry across a
    /// releasing collapse**: the motion each released locus's material held is released with
    /// it. A released channel `a` takes its storage, stiffness and dissipation to zero, so its
    /// state `[u, w]` and momentum `π_a = C_a w_a` (the energy `½(⟨w, C_a w⟩ + ⟨u, K_a u⟩)` its
    /// material held) leave with the material. Its arriving waves are held by the contact's
    /// conductance at the lift, which the field declares and the collapse does not release, and
    /// stay. A released resonator leaves with its state and momentum. Ring storage waves are held
    /// by the rings' declared admittances and stay.
    ///
    /// [proved-derived, on formal-checked theorems] Under the carry the collapse releases exactly
    /// the loci no walk from a source to an admitted receiver passes (Lean `HNN/Retention`,
    /// `continuing_release_indistinguishable`, `continuing_collapse_connected`). Motion at such a
    /// locus reaches no admitted receiver along any walk, so releasing it changes no admitted
    /// reading, as releasing its material does not. Without it the next opening would have to
    /// hold a nonzero momentum on a zero storage, which no rate does (`HnnError::HeldMomentum`).
    ///
    /// Returns the carry and the released loci whose carried motion was off zero.
    pub fn released(&self, released: &BTreeSet<Locus>) -> (Self, Vec<Locus>) {
        let mut carry = self.clone();
        let mut moved = Vec::new();
        let off = |values: &[Rat]| values.iter().any(|x| !x.is_zero());
        for locus in released {
            match *locus {
                Locus::Channel(a) if a < carry.momenta.len() => {
                    let [u, w] = &mut carry.change.states[a];
                    if off(u) || off(w) || off(&carry.momenta[a]) {
                        moved.push(*locus);
                    }
                    *u = zeros(u.len());
                    *w = zeros(w.len());
                    carry.momenta[a] = zeros(carry.momenta[a].len());
                }
                Locus::Resonator(g) if g < carry.change.resonators.len() => {
                    let held = carry.change.resonators[g].is_some();
                    if held || carry.resonator_momenta[g].is_some() {
                        moved.push(*locus);
                    }
                    carry.change.resonators[g] = None;
                    carry.change.resonator_phases[g] = None;
                    carry.resonator_momenta[g] = None;
                }
                _ => {}
            }
        }
        (carry, moved)
    }

    /// [definition; agent-inferred, October 3; the reception carry §2.4] **The carry as text**,
    /// every value exact, appended to `s`: `carry t r c n` (the elapsed ticks, the rings, the
    /// contacts and the resonator slots), one line per ring's storage wave, two per contact's
    /// arriving waves (`at from`, `at to`), two per contact's state (`u`, `w`), the line
    /// `reference` with each contact's conductance, one line per contact's momentum, and per
    /// resonator slot `resonator s p` (`s` is `1` with the slot's two state lines following, `0`
    /// without; `p` the measuring phase or `-`), the state's lines followed by its momentum's. A
    /// wave is its values on one line, empty when it has none.
    /// [`crate::hnn::constitution::ContinuingState`] carries it inside its check.
    pub fn write(&self, s: &mut String) {
        let line = |s: &mut String, wave: &[Rat]| {
            *s += &wave
                .iter()
                .map(ToString::to_string)
                .collect::<Vec<_>>()
                .join(" ");
            s.push('\n');
        };
        let change = &self.change;
        *s += &format!(
            "carry {} {} {} {}\n",
            self.ticks,
            change.storage.len(),
            change.arrivals.len(),
            change.resonators.len()
        );
        for wave in &change.storage {
            line(s, wave);
        }
        for pair in change.arrivals.iter().chain(&change.states) {
            line(s, &pair[0]);
            line(s, &pair[1]);
        }
        *s += "reference";
        for conductance in &self.conductances {
            *s += &format!(" {conductance}");
        }
        s.push('\n');
        for momentum in &self.momenta {
            line(s, momentum);
        }
        for ((state, phase), momentum) in change
            .resonators
            .iter()
            .zip(&change.resonator_phases)
            .zip(&self.resonator_momenta)
        {
            let phase = phase.map_or("-".to_string(), |p| p.to_string());
            *s += &format!("resonator {} {phase}\n", u8::from(state.is_some()));
            if let Some([u, w]) = state {
                line(s, u);
                line(s, w);
                line(s, momentum.as_deref().unwrap_or(&[]));
            }
        }
    }

    /// **The carry read back from its text** ([`ReceptionCarry::write`]), its head line given and
    /// the rest drawn from `next`; refused, typed, on any line out of its form.
    pub fn read<'a>(
        head: &str,
        next: &mut dyn FnMut(&'static str) -> Result<&'a str, HnnError>,
    ) -> Result<Self, HnnError> {
        let refuse = |what: &'static str| HnnError::ContinuingState { what };
        let mut words = head.split_whitespace();
        if words.next() != Some("carry") {
            return Err(refuse("the carry's head"));
        }
        let counts: Vec<usize> = words
            .map(|w| w.parse().map_err(|_| refuse("the carry's head")))
            .collect::<Result<_, _>>()?;
        let [ticks, rings, contacts, slots] = counts[..] else {
            return Err(refuse("the carry's head"));
        };
        type Next<'n, 'a> = &'n mut dyn FnMut(&'static str) -> Result<&'a str, HnnError>;
        fn wave(next: Next<'_, '_>, what: &'static str) -> Result<Vec<Rat>, HnnError> {
            next(what)?
                .split_whitespace()
                .map(|x| {
                    x.parse::<Rat>()
                        .map_err(|_| HnnError::ContinuingState { what })
                })
                .collect()
        }
        fn pairs(
            next: Next<'_, '_>,
            count: usize,
            what: &'static str,
        ) -> Result<Vec<[Vec<Rat>; 2]>, HnnError> {
            (0..count)
                .map(|_| Ok([wave(next, what)?, wave(next, what)?]))
                .collect()
        }
        let storage = (0..rings)
            .map(|_| wave(next, "a carried storage wave"))
            .collect::<Result<Vec<_>, _>>()?;
        let arrivals = pairs(next, contacts, "a carried arriving wave")?;
        let states = pairs(next, contacts, "a carried contact state")?;
        let reference = next("the carry's reference")?;
        let mut words = reference.split_whitespace();
        if words.next() != Some("reference") {
            return Err(refuse("the carry's reference"));
        }
        let conductances = words
            .map(|g| {
                g.parse::<Rat>()
                    .map_err(|_| refuse("the carry's reference"))
            })
            .collect::<Result<Vec<_>, _>>()?;
        if conductances.len() != contacts {
            return Err(refuse("the carry's reference"));
        }
        let momenta = (0..contacts)
            .map(|_| wave(next, "a carried momentum"))
            .collect::<Result<Vec<_>, _>>()?;
        let (mut resonators, mut resonator_phases, mut resonator_momenta) =
            (Vec::new(), Vec::new(), Vec::new());
        for _ in 0..slots {
            let line = next("a carried resonator slot")?;
            let fields: Vec<&str> = line.split_whitespace().collect();
            let ["resonator", state, phase] = fields[..] else {
                return Err(refuse("a carried resonator slot"));
            };
            resonator_phases.push(match phase {
                "-" => None,
                p => Some(p.parse().map_err(|_| refuse("a carried resonator phase"))?),
            });
            match state {
                "0" => {
                    resonators.push(None);
                    resonator_momenta.push(None);
                }
                "1" => {
                    resonators.push(Some([
                        wave(next, "a carried resonator state")?,
                        wave(next, "a carried resonator state")?,
                    ]));
                    resonator_momenta.push(Some(wave(next, "a carried resonator momentum")?));
                }
                _ => return Err(refuse("a carried resonator slot")),
            }
        }
        Ok(Self {
            change: EndChange {
                storage,
                arrivals,
                states,
                resonators,
                resonator_phases,
            },
            ticks,
            conductances,
            momenta,
            resonator_momenta,
        })
    }

    /// [definition; agent-inferred, October 3; the reception carry §2.4] Whether the carry has the
    /// field's shape: each ring's storage wave, each contact's arriving pair at its two rings'
    /// widths and its state pair at the contact's width, a positive conductance and a momentum at
    /// the contact's width per contact, and a measuring phase per resonator slot.
    /// A restored carry of another shape is refused at its mount.
    pub fn fits(&self, field: &Field) -> bool {
        let change = &self.change;
        let widths: Vec<usize> = field.rings().iter().map(|ring| ring.width()).collect();
        let contacts = field.contacts();
        change.storage.len() == widths.len()
            && change
                .storage
                .iter()
                .zip(&widths)
                .all(|(wave, n)| wave.len() == *n)
            && change.arrivals.len() == contacts.len()
            && change.states.len() == contacts.len()
            && contacts
                .iter()
                .zip(&change.arrivals)
                .zip(&change.states)
                .all(|((contact, [from, to]), [u, w])| {
                    let (a, b) = contact.ends();
                    from.len() == widths[a]
                        && to.len() == widths[b]
                        && u.len() == contact.width()
                        && w.len() == contact.width()
                })
            && self.conductances.len() == contacts.len()
            && self.conductances.iter().all(Signed::is_positive)
            && self.momenta.len() == contacts.len()
            && contacts
                .iter()
                .zip(&self.momenta)
                .all(|(contact, momentum)| momentum.len() == contact.width())
            && change.resonators.len() == change.resonator_phases.len()
            && self.resonator_momenta.len() == change.resonators.len()
            && change.resonators.iter().zip(&self.resonator_momenta).all(
                |(state, momentum)| match (state, momentum) {
                    (None, None) => true,
                    (Some([_, w]), Some(momentum)) => momentum.len() == w.len(),
                    _ => false,
                },
            )
    }
}

/// [definition; agent-inferred, October 3; the reception carry §2.2] **The boundary's absorption
/// at a word's end**, `A`. [`Absorption::Complete`] (`A = I`) emits every interior coordinate at the
/// end, so the next word opens on the rest change: today's word exactly on a field with no declared
/// resonator. [`Absorption::Nothing`] (`A = 0`) absorbs nothing beyond the field's own conductances
/// within the ticks, so the interior change carries. An intermediate absorption would need a
/// declared exterior admittance at the receiver's section, a locus that does not exist; none is
/// built.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Absorption {
    Complete,
    Nothing,
}

/// The source port's exact imposition after the declared boundary absorption and crossing.
/// Both energy readings include contact storage and loaded resonator energy. This receipt
/// measures no earlier deposition, reflection, pump advance or complete-absorption emission.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SourceOpeningReceipt {
    pub before: Rat,
    pub after: Rat,
    pub absorbed: Rat,
    pub imposed: Rat,
}

impl SourceOpeningReceipt {
    /// E_after - E_before = imposed - absorbed, at the same contemporary power form.
    pub fn closes(&self) -> bool {
        &self.after - &self.before == &self.imposed - &self.absorbed
    }
}

/// The same source imposition on the Word's declared charts. `split` is the signed work
/// released by its actual opening split; `error` is the coordinate difference from the
/// unsplit imposition, including crossed arriving waves and held interior states. The work
/// residual is not used as a state or receiving error bound (Refs #73, #62).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ChartedSourceOpeningReceipt {
    pub source: SourceOpeningReceipt,
    pub split: Rat,
    pub error: EndChange,
}

impl ChartedSourceOpeningReceipt {
    pub fn closes(&self) -> bool {
        &self.source.after - &self.source.before + &self.split
            == &self.source.imposed - &self.source.absorbed
    }
}

/// [definition; agent-inferred, October 3; the reception carry §2.1] **What a reception's word
/// opens on**: at rest at tick zero (today's reception, [`Word::open_charted`]), or on the previous
/// reception's carried end under a declared absorption ([`Word::open_received`]).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum WordOpening {
    Rest,
    Received {
        carry: ReceptionCarry,
        absorption: Absorption,
    },
}

impl WordOpening {
    /// [definition; agent-inferred, October 4; the reception carry §8] **The opening across a
    /// releasing collapse** ([`ReceptionCarry::released`]): at rest unchanged.
    pub fn released(&self, released: &BTreeSet<Locus>) -> Self {
        match self {
            WordOpening::Rest => WordOpening::Rest,
            WordOpening::Received { carry, absorption } => WordOpening::Received {
                carry: carry.released(released).0,
                absorption: *absorption,
            },
        }
    }

    /// [definition; October 4, the reception carry §8] **The rings the opening's interior change
    /// occupies** ([`EndChange::support`]): none at rest or under complete absorption, the carried
    /// interior's otherwise (the crossing into the next references keeps a zero coordinate zero).
    pub fn support(&self, field: &Field) -> Vec<usize> {
        match self {
            WordOpening::Received {
                carry,
                absorption: Absorption::Nothing,
            } => carry.interior(field).support(field),
            _ => Vec::new(),
        }
    }
}

/// [definition] **The field's power form at a cut**, `P(x) = (h/4)[Σ_r Y_r|s_r|² + Σ_a G_a(|a_g|² +
/// |a_h|²)] + Σ_a ½(⟨w, C_a w⟩ + ⟨u, K_a u⟩)`: the hop, the rings' storage admittances and the
/// contacts' conductances at the lift (declared by the field), each contact's storage `C_a = c cᵀ`
/// and signed stiffness `K_a` (the constitution's), and each ring's declared resonator material.
/// Read before and after a deposit at the same cut, it gives the commit's deposition work.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PowerForm {
    step: Rat,
    admittances: Vec<Rat>,
    conductances: Vec<Rat>,
    storage: Vec<ExactRatMatrix>,
    stiffness: Vec<ExactRatMatrix>,
    resonators: Vec<Option<ResonatorMaterial>>,
}

impl PowerForm {
    /// **The power form at a cut** from the field, a constitution and the lift point.
    pub fn read(
        field: &Field,
        constitution: &dyn crate::hnn::field::FieldMaterial,
        current: &Current,
    ) -> Result<Self, HnnError> {
        let contacts = field.contacts().len();
        let conductances = (0..contacts)
            .map(|a| {
                let exponent = contact_exponent(field, a, current.lift())?;
                if exponent.phase != 0 {
                    return Err(HnnError::ExponentPhase {
                        contact: a,
                        phase: exponent.phase,
                        grain: field.exponent_grain(),
                    });
                }
                Ok(power_of_two(&exponent.carry)? * field.contact(a).admittance())
            })
            .collect::<Result<Vec<_>, HnnError>>()?;
        let storage = (0..contacts)
            .map(|a| gram(constitution.contact_storage(a)))
            .collect::<Result<Vec<_>, HnnError>>()?;
        let stiffness = (0..contacts)
            .map(|a| {
                signed_stiffness(
                    constitution.contact_stiffness(a),
                    constitution.contact_stiffness_signature(a),
                )
            })
            .collect::<Result<Vec<_>, HnnError>>()?;
        Ok(Self {
            step: field.step().clone(),
            admittances: field
                .rings()
                .iter()
                .map(|ring| ring.admittance().clone())
                .collect(),
            conductances,
            storage,
            stiffness,
            resonators: (0..field.rings().len())
                .map(|ring| constitution.ring_resonator(ring).cloned())
                .collect(),
        })
    }

    /// [definition; record B §2.1, §2.3a] **The opening a carry crosses into at this form's cut**:
    /// [`ReceptionCarry::opening`] at this form's conductances and storage.
    pub fn opening(&self, field: &Field, carry: &ReceptionCarry) -> Result<EndChange, HnnError> {
        let storage: Vec<&ExactRatMatrix> = self.storage.iter().collect();
        carry.opening(
            field,
            &self.conductances,
            &storage,
            &self.resonator_capacities(),
        )
    }

    /// Each ring's declared resonator capacity `C_r` under this form, `None` where none is declared.
    pub fn resonator_capacities(&self) -> Vec<Option<&ExactRatMatrix>> {
        self.resonators
            .iter()
            .map(|material| material.as_ref().map(|material| material.forms().0))
            .collect()
    }

    /// **One ring's storage power** under this form, `(h/4)·Y_g·|s|²`: the storage term
    /// [`PowerForm::power`] sums over the rings.
    pub fn ring_power(&self, ring: usize, wave: &[Rat]) -> Rat {
        &self.step / integer(4) * &self.admittances[ring] * dot(wave, wave)
    }

    /// **The power of a change** under this form.
    pub fn power(&self, change: &EndChange) -> Result<Rat, HnnError> {
        let mut waves = Rat::zero();
        for (admittance, wave) in self.admittances.iter().zip(&change.storage) {
            waves += admittance * dot(wave, wave);
        }
        let mut stored = Rat::zero();
        for (a, (pair, state)) in change.arrivals.iter().zip(&change.states).enumerate() {
            waves += &self.conductances[a] * (dot(&pair[0], &pair[0]) + dot(&pair[1], &pair[1]));
            stored += (dot(&state[1], &self.storage[a].apply(&state[1])?)
                + dot(&state[0], &self.stiffness[a].apply(&state[0])?))
                / integer(2);
        }
        Ok(&self.step / integer(4) * waves + stored)
    }

    /// **The declared resonators' energy at a change**, measured with this form's materials at each
    /// resonator's form phase.
    pub fn resonator_power(&self, change: &EndChange) -> Result<Rat, HnnError> {
        let mut total = Rat::zero();
        for (ring, state) in change.resonators.iter().enumerate() {
            let (Some(material), Some(state), Some(phase)) = (
                self.resonators.get(ring).and_then(Option::as_ref),
                state,
                change.resonator_phases.get(ring).copied().flatten(),
            ) else {
                continue;
            };
            total += material.energy(phase, &state[0], &state[1])?;
        }
        Ok(total)
    }

    /// [definition; the deposit record (October 3) §3–§4, Lean
    /// `HolonicsResearch/HNN/MoveDirection.held_momentum_loss`] **The commit from this form to
    /// `after` at held momentum**: the change `x′` with each contact's rate held at its momentum,
    /// `C′_a w′_a = C_a w_a` ([`held_rate`]), and the deposition work read from the identity
    /// `½⟨w′, C′ w′⟩ − ½⟨w, C w⟩ = −½⟨w′, ΔC w′⟩ − ½⟨w − w′, C (w − w′)⟩` for the storage, the
    /// same-state work `½⟨x, ΔΘ x⟩` ([`PowerForm::deposition_work`]) for every other coordinate.
    /// A carried resonator's rate is held at its momentum the same way (record B §2.4,
    /// [`held_resonator_rate`]), its stiffness work read at its form phase with `u` held.
    /// Where no storage moves, `x′ = x` and the work is the same-state work.
    pub fn held(&self, after: &PowerForm, change: &EndChange) -> Result<Held, HnnError> {
        // The resonator family is the deposit's to preserve: refused here as the same-state work
        // refuses it.
        self.deposition_work(after, change)?;
        let mut held = change.clone();
        let mut storage_work = Rat::zero();
        for (a, state) in held.states.iter_mut().enumerate() {
            let (before, moved) = (&self.storage[a], &after.storage[a]);
            if before == moved {
                continue;
            }
            let rate = state[1].clone();
            let next = held_rate(a, &rate, &before.apply(&rate)?, moved)?;
            let jump = sub(&rate, &next);
            storage_work -= (dot(&next, &moved.subtract(before)?.apply(&next)?)
                + dot(&jump, &before.apply(&jump)?))
                / integer(2);
            state[1] = next;
        }
        let mut resonator_work = Rat::zero();
        for (ring, (state, phase)) in held
            .resonators
            .iter_mut()
            .zip(&change.resonator_phases)
            .enumerate()
        {
            let (Some(old), Some(new), Some(state), Some(phase)) = (
                self.resonators.get(ring).and_then(Option::as_ref),
                after.resonators.get(ring).and_then(Option::as_ref),
                state.as_mut(),
                *phase,
            ) else {
                continue;
            };
            if old == new {
                continue;
            }
            let stiffness = new
                .pumped_stiffness(phase)?
                .subtract(&old.pumped_stiffness(phase)?)?;
            resonator_work += dot(&state[0], &stiffness.apply(&state[0])?) / integer(2)
                + new.quartic_energy(&state[0])?
                - old.quartic_energy(&state[0])?;
            let (before, moved) = (old.forms().0, new.forms().0);
            if before == moved {
                continue;
            }
            let rate = state[1].clone();
            let next = held_resonator_rate(ring, &rate, &before.apply(&rate)?, moved)?;
            let jump = sub(&rate, &next);
            resonator_work -= (dot(&next, &moved.subtract(before)?.apply(&next)?)
                + dot(&jump, &before.apply(&jump)?))
                / integer(2);
            state[1] = next;
        }
        // The same-state work of every coordinate but the contacts' storage and the resonators.
        let same = Self {
            storage: self.storage.clone(),
            resonators: self.resonators.clone(),
            ..after.clone()
        };
        let deposition = self.deposition_work(&same, change)? + storage_work + resonator_work;
        Ok(Held {
            change: held,
            deposition,
        })
    }

    /// **The deposition work of the commit from this form to `after`** on the change `x` (Lean
    /// `HNN/Word.field_commit_deposition`, `Holon/Deposition.deposition_work`): `½⟨x, ΔΘ x⟩`,
    /// formed from the forms' differences, `(h/4)[Σ ΔY|s|² + Σ ΔG|a|²] + ½Σ_a(⟨w, ΔC_a w⟩ +
    /// ⟨u, ΔK_a u⟩)`, including each loaded resonator's end-state form change.
    pub fn deposition_work(&self, after: &PowerForm, change: &EndChange) -> Result<Rat, HnnError> {
        if self.step != after.step {
            return Err(HnnError::Shape {
                what: "a commit that keeps the hop fixed",
                expected: 0,
                found: 1,
            });
        }
        let mut waves = Rat::zero();
        for ((old, new), wave) in self
            .admittances
            .iter()
            .zip(&after.admittances)
            .zip(&change.storage)
        {
            if old != new {
                waves += (new - old) * dot(wave, wave);
            }
        }
        let mut stored = Rat::zero();
        for (a, (pair, state)) in change.arrivals.iter().zip(&change.states).enumerate() {
            if self.conductances[a] != after.conductances[a] {
                waves += (&after.conductances[a] - &self.conductances[a])
                    * (dot(&pair[0], &pair[0]) + dot(&pair[1], &pair[1]));
            }
            let storage = after.storage[a].subtract(&self.storage[a])?;
            let stiffness = after.stiffness[a].subtract(&self.stiffness[a])?;
            stored += (dot(&state[1], &storage.apply(&state[1])?)
                + dot(&state[0], &stiffness.apply(&state[0])?))
                / integer(2);
        }
        for ring in 0..self.resonators.len().max(after.resonators.len()) {
            match (
                self.resonators.get(ring).and_then(Option::as_ref),
                after.resonators.get(ring).and_then(Option::as_ref),
                change.resonators.get(ring).and_then(Option::as_ref),
                change.resonator_phases.get(ring).copied().flatten(),
            ) {
                (Some(old), Some(new), Some(state), Some(phase)) if old != new => {
                    if old.base_saturation() != new.base_saturation() {
                        return Err(HnnError::Resonator {
                            ring,
                            what: "a deposit preserves the declared quartic family and coefficient",
                        });
                    }
                    let (old_c, _, _) = old.forms();
                    let (new_c, _, _) = new.forms();
                    let old_k = old.pumped_stiffness(phase)?;
                    let new_k = new.pumped_stiffness(phase)?;
                    let dc = new_c.subtract(old_c)?;
                    let dk = new_k.subtract(&old_k)?;
                    stored += (dot(&state[1], &dc.apply(&state[1])?)
                        + dot(&state[0], &dk.apply(&state[0])?))
                        / integer(2)
                        + new.quartic_energy(&state[0])?
                        - old.quartic_energy(&state[0])?;
                }
                (None, None, None, _) | (Some(_), Some(_), None, _) => {}
                (a, b, _, _) if a == b => {}
                _ => {
                    return Err(HnnError::Shape {
                        what: "a deposit that preserves the declared resonator family",
                        expected: self.resonators.len(),
                        found: after.resonators.len(),
                    });
                }
            }
        }
        Ok(&self.step / integer(4) * waves + stored)
    }
}

/// [definition; the deposit record (October 3) §3] **A change carried across a commit at held
/// momentum** ([`PowerForm::held`]): the held change and the deposition work on it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Held {
    pub change: EndChange,
    pub deposition: Rat,
}

/// [definition] **The commit a word's balance is carried across** (Lean
/// `HNN/Word.field_commit_deposition`): the deposition work `½⟨x, ΔΘ x⟩` on the word's end change,
/// formed from the operand differences, and the end change's power under the committed
/// constitution, formed from the committed operands alone.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CommitWork {
    pub deposition: Rat,
    pub committed: Rat,
    /// The resonators' end storage before the commit, under the word's own constitution.
    pub resonator_before: Rat,
}

/// [definition] **The whole word's balance** (campaign 2's committed balance over one word, formed
/// from its release on every realization of the port, [`WordBalance::of`]): the field's power at the
/// open (after the opening split) and at the end, every tick's stated terms summed, the defects
/// (the ticks' residuals) and the last junction's residual with their certified bound, the
/// resonators' storage at both endpoints with their terms, the signed port pairing,
/// the end change the commit reads, the commit when one follows
/// ([`WordBalance::commit`]), and the remainders the end releases, the word's and the resonators'.
/// Its certified bound covers the executed residual of the field and of the resonators alike: the
/// ticks' bounds, the last junction's and the resonators' ([`ResonatorBalance::bound`]).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct WordBalance {
    pub open: Rat,
    pub end: Rat,
    pub dissipation: Rat,
    pub resist: Rat,
    pub contrast: Rat,
    pub defects: Rat,
    pub last: Rat,
    pub bound: Rat,
    pub resonator_open: Rat,
    pub resonator_end: Rat,
    pub pump: Rat,
    pub port: Rat,
    pub resonator_dissipation: Rat,
    pub resonator_integration: Rat,
    pub resonator_chart: Rat,
    pub resonator_split: Rat,
    /// The resonators' certified bound on their chart and split terms, summed into `bound`.
    pub resonator_bound: Rat,
    /// The interconnection's defect, zero by construction for a loaded port
    /// ([`FieldBalance::interconnection`]).
    pub interconnection: Rat,
    /// The field's loaded-return split work over the word.
    pub loaded_split: Rat,
    pub change: EndChange,
    pub commit: Option<CommitWork>,
    pub released: Remainders,
    pub resonator_released: Remainders,
}

impl WordBalance {
    /// **The word's balance from its release**: the ticks' balances summed, the last junction's
    /// residual and bound, and the resonators' balances with their bounds (their port work against
    /// the field's signed loaded-port term is the interconnection's defect).
    pub fn of(released: &Released) -> Self {
        let end = released.power.clone();
        let open = released
            .balances
            .first()
            .map_or_else(|| end.clone(), |tick| tick.before.clone());
        let sum =
            |term: fn(&TickBalance) -> &Rat| -> Rat { released.balances.iter().map(term).sum() };
        let resonators = |term: fn(&ResonatorBalance) -> &Rat| -> Rat {
            released.resonators.iter().map(term).sum()
        };
        let port = resonators(|r| &r.port);
        let loaded_port: Rat = released.balances.iter().map(|tick| &tick.loaded_port).sum();
        let loaded_split = sum(|tick| &tick.loaded_split);
        let resonator_bound = resonators(|r| &r.bound);
        Self {
            open,
            end,
            dissipation: sum(|t| &t.dissipation),
            resist: sum(|t| &t.resist),
            contrast: sum(|t| &t.contrast),
            defects: sum(|t| &t.residual),
            last: released.last.clone(),
            bound: sum(|t| &t.bound) + &released.last_bound + &resonator_bound,
            resonator_bound,
            resonator_open: resonators(|r| &r.open),
            resonator_end: resonators(|r| &r.end),
            pump: resonators(|r| &r.pump),
            interconnection: &port + loaded_port,
            loaded_split,
            port,
            resonator_dissipation: resonators(|r| &r.dissipation),
            resonator_integration: resonators(|r| &r.integration),
            resonator_chart: resonators(|r| &r.chart),
            resonator_split: resonators(|r| &r.split),
            change: released.end.clone(),
            commit: None,
            released: released.remainders.clone(),
            resonator_released: released
                .resonators
                .iter()
                .fold(Remainders::default(), |joined, resonator| {
                    joined.join(&resonator.released)
                }),
        }
    }

    /// [definition; record B §2.4] **The word's balance at the crossing its reception carries**
    /// (`Absorption::Nothing`): the balance up to the last crossing, whose change `crossing` the
    /// next word opens on and scatters ([`Word::reception_end`]). The last junction is that
    /// crossing read by this word's receiver, its outputs not carried, so its residual leaves the
    /// balance: the end is `P(crossing) = P(end) − last`, the power of the change before that
    /// junction, and its bound is dropped with it. Every tick's term is the word's own.
    pub fn carried(released: &Released, crossing: EndChange) -> Self {
        let mut balance = Self::of(released);
        balance.end = &released.power - &released.last;
        balance.bound = &balance.bound - &released.last_bound;
        balance.last = Rat::zero();
        balance.change = crossing;
        balance
    }

    /// **Carry the balance across the commit** from the form `before` to `after` (both read at the
    /// word's cut, before and after the deposit): the deposition work `½⟨x, ΔΘ x⟩` from the forms'
    /// differences and the end change's power under the committed form alone.
    pub fn commit(&mut self, before: &PowerForm, after: &PowerForm) -> Result<(), HnnError> {
        // Every fallible reading first: a refusal leaves the balance as it was.
        let deposition = before.deposition_work(after, &self.change)?;
        let committed = after.power(&self.change)?;
        let resonator_end = after.resonator_power(&self.change)?;
        let resonator_before = std::mem::replace(&mut self.resonator_end, resonator_end);
        self.commit = Some(CommitWork {
            deposition,
            committed,
            resonator_before,
        });
        Ok(())
    }

    /// [definition; the deposit record (October 3) §3; record B §2.3] **Carry the balance across
    /// the commit at held momentum**, the reception carry's commit: the deposition work read on the
    /// held change ([`PowerForm::held`]) and the held change's power under the committed form. The
    /// word's identity is unchanged: the held change's committed power is the end plus that work.
    pub fn commit_held(&mut self, before: &PowerForm, after: &PowerForm) -> Result<(), HnnError> {
        let held = before.held(after, &self.change)?;
        let committed = after.power(&held.change)?;
        let resonator_end = after.resonator_power(&held.change)?;
        let resonator_before = std::mem::replace(&mut self.resonator_end, resonator_end);
        self.commit = Some(CommitWork {
            deposition: held.deposition,
            committed,
            resonator_before,
        });
        Ok(())
    }

    /// The executed residual: the ticks' defects and loaded splits, the last junction's, and the
    /// resonators' chart and split terms.
    pub fn residual(&self) -> Rat {
        &self.defects
            + &self.last
            + &self.loaded_split
            + &self.resonator_chart
            + &self.resonator_split
    }

    /// **The word closes with its stated defects, the combined system in one identity** (Lean
    /// `HNN/Word.{field_executed_balance_with_defects, field_commit_deposition}`):
    /// `P_end + E_end = P_open + E_open − dissipation + resist + Π_c +
    /// defects + last + pump − resonator dissipation + resonator chart + resonator split +
    /// interconnection`, with `P_end` the committed power and `deposition` added when a commit
    /// follows; and the executed residual, the resonators' chart and split included, lies within
    /// its certified bound.
    pub fn closes(&self) -> bool {
        let terms = &self.open + &self.resonator_open - &self.dissipation
            + &self.resist
            + &self.contrast
            + self.residual()
            + &self.pump
            - &self.resonator_dissipation
            + &self.resonator_integration
            + &self.interconnection;
        let identity = match &self.commit {
            Some(commit) => &commit.committed + &self.resonator_end == terms + &commit.deposition,
            None => &self.end + &self.resonator_end == terms,
        };
        identity && self.residual().abs() <= self.bound
    }
}

/// [definition; agent-inferred, October 3; the reception carry §2.3] **The chained balance at a
/// reception's opening**: how the power the previous word ended with reaches the next word's
/// opening and its end, every term exact, on one baseline. With `x = x_k(end)` the carried change,
/// `y = Π_int x` its interior (the source rings' storage absorbed), `s = s_(k+1)(0)` the moment the
/// source port imposes, `Θ, λ` the constitution and lift at word `k`'s cut, `Θ'` after its commit
/// and `λ'` at the next opening, and `E_S(z) = Σ_(g∈𝒮) (h/4) Y_g |z_g|²` the source rings' storage
/// (the ring admittances are field constants, so `E_S` is the same under every form):
///
/// ```text
/// P_(Θ,λ)(x)    = P_(Θ,λ)(y) + E_S(x)                                  (absorbed, emitted)
/// P_open(k+1)   = P_(Θ,λ)(y) + deposition_k + ingest_k + E_S(s)        (the opening)
/// E_end(k+1)    = P_open(k+1) − L_(k+1) + Π_c + pump + interconnection + residual
/// ```
///
/// - `interior = P_(Θ,λ)(y) = end_k − E_S(x)`; `absorbed = E_S(x)`, which leaves through the
///   source port at the reception and is subtracted once, here; `end_k` is the power at the
///   crossing the carry holds ([`WordBalance::carried`], record B §2.4);
/// - `resonator_interior`, the carried resonators' storage under `Θ` before the commit, which
///   enters the next word as its resonator storage at the opening (§2.4); with it the opening line
///   reads `P_open(k+1) + R_open(k+1) = interior + resonator_interior + work + imposed`;
/// - `deposition`, its commit's work at held momentum ([`WordBalance::commit_held`]: `x′` with
///   `C′_a w′_a = C_a w_a`, zero where no commit followed);
/// - `ingest = P_(Θ',λ')(x″) − P_(Θ',λ)(x′)`: the window's ingest moves the lift and with it every
///   contact's conductance, and each carried wave crosses that reference change,
///   `x″ = x′` with `a″ = (1 + Γ_a) a`, `Γ_a = (G_a − G′_a)/(G_a + G′_a)` (§2.3a);
/// - `reflected = Σ_a (h/4) Γ_a² G_a |a|²`, what the reference change emits, so that
///   `ingest = −reflected ≤ 0` (Lean `HNN/Ring.two_port_reference_balance`);
/// - `imposed = E_S(s)`, the moment's storage the source port imposes;
/// - `L = dissipation − resist + resonator dissipation ≥ 0`, the next word's certified loss.
///
/// Deposition and ingest act only on the contacts, so they read `x` and `y` alike.
///
/// **The law the carry satisfies** is dissipativity with respect to its declared supply: the next
/// word ends with at most the interior plus everything its ports supplied (deposition, ingest,
/// imposition, contrast, pump, interconnection) within the residual's certified bound
/// ([`ChainedBalance::dissipative`]). It follows from the opening identity, the word's balance and
/// `L ≥ 0`. **The stronger reading, that the work done on the carried change between the words is
/// within the next word's loss** ([`ChainedBalance::within_loss`]), is read, not asserted: the lift
/// emits and never works on the carried waves, so the work between the words is the deposit's.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ChainedBalance {
    pub interior: Rat,
    /// The carried resonators' storage at the crossing, under word `k`'s constitution.
    pub resonator_interior: Rat,
    pub absorbed: Rat,
    pub deposition: Rat,
    pub ingest: Rat,
    /// What the lift's reference change emits from the carried waves.
    pub reflected: Rat,
    pub imposed: Rat,
    /// `P_(Θ',λ')(Π_int x″ + s)`, the opening change's power under the next opening's form.
    pub open: Rat,
    /// The next word's balance at its opening ([`WordBalance::open`]), after its opening split.
    pub next_open: Rat,
    /// The opening's split at the transients' lattice, the field's and the carried resonators',
    /// `(open + resonator_open) − (next_open + next_resonator_open)`: the crossed change's power
    /// less its representative's, an executed residual read exactly (zero on the exact word).
    pub split: Rat,
    /// The next word's certified loss `L`.
    pub loss: Rat,
    /// The next word's port terms: contrast, pump and interconnection.
    pub ported: Rat,
    /// The carried resonators' storage at the opening under the next opening's form, before its
    /// split (record B §2.4: a rate held at momentum is split at the opening as a contact's is).
    pub resonator_open: Rat,
    /// The next word's resonator storage at its opening, after its split, and at its end.
    pub next_resonator_open: Rat,
    pub resonator_end: Rat,
    /// The next word's end power, its executed residual and that residual's certified bound.
    pub end: Rat,
    pub residual: Rat,
    pub bound: Rat,
}

impl ChainedBalance {
    /// **Read the chained balance** from the previous word's balance (carried across its commit at
    /// held momentum when one followed), the power form at the next opening, the carry, the next
    /// word's opening change (before its split) and the next word's balance.
    pub fn read(
        field: &Field,
        previous: &WordBalance,
        form: &PowerForm,
        carry: &ReceptionCarry,
        opening: &EndChange,
        next: &WordBalance,
    ) -> Result<Self, HnnError> {
        let (deposition, committed, resonator_interior) = match &previous.commit {
            Some(commit) => (
                commit.deposition.clone(),
                commit.committed.clone(),
                commit.resonator_before.clone(),
            ),
            None => (
                Rat::zero(),
                previous.end.clone(),
                previous.resonator_end.clone(),
            ),
        };
        let storage: Vec<&ExactRatMatrix> = form.storage.iter().collect();
        let crossed = carry.crossed(&form.conductances, &storage, &form.resonator_capacities())?;
        let (mut absorbed, mut imposed) = (Rat::zero(), Rat::zero());
        for ring in (0..field.rings().len()).filter(|ring| field.is_source(*ring)) {
            absorbed += form.ring_power(ring, &carry.change.storage[ring]);
            imposed += form.ring_power(ring, &opening.storage[ring]);
        }
        Ok(Self {
            interior: &previous.end - &absorbed,
            resonator_interior,
            absorbed,
            deposition,
            ingest: form.power(&crossed)? - committed,
            reflected: carry.reflected(&form.step, &form.conductances),
            imposed,
            split: form.power(opening)? + form.resonator_power(&crossed)?
                - &next.open
                - &next.resonator_open,
            open: form.power(opening)?,
            next_open: next.open.clone(),
            loss: &next.dissipation - &next.resist + &next.resonator_dissipation,
            ported: &next.contrast + &next.pump + &next.interconnection,
            resonator_open: form.resonator_power(&crossed)?,
            next_resonator_open: next.resonator_open.clone(),
            resonator_end: next.resonator_end.clone(),
            end: next.end.clone(),
            residual: next.residual(),
            bound: next.bound.clone(),
        })
    }

    /// The work done on the carried change between the two words: `deposition + ingest`.
    pub fn work(&self) -> Rat {
        &self.deposition + &self.ingest
    }

    /// Everything the ports supplied from the interior to the next word's end: the work between
    /// the words, the imposed moment, and the next word's port terms.
    pub fn supplied(&self) -> Rat {
        self.work() + &self.imposed + &self.ported
    }

    /// **It closes**: the opening, the carried resonators' storage included, is
    /// `interior + resonator_interior + deposition + ingest + imposed` exactly, and it is the
    /// opening the next word's balance starts from, its resonators' included, but for the opening's
    /// split.
    pub fn closes(&self) -> bool {
        &self.open + &self.resonator_open
            == &self.interior + &self.resonator_interior + self.work() + &self.imposed
            && &self.open + &self.resonator_open - &self.split
                == &self.next_open + &self.next_resonator_open
    }

    /// **The lift only emits** (record B §2.3a): the ingest is exactly minus the reflected power,
    /// so the lift's reference change does no work on the carried waves.
    pub fn lift_emits(&self) -> bool {
        &self.ingest + &self.reflected == Rat::zero() && !self.reflected.is_negative()
    }

    /// **Dissipative with respect to the declared supply**: `E_end ≤ interior + carried resonator
    /// storage + supplied − opening split + bound`, the resonators' end storage on the left.
    pub fn dissipative(&self) -> bool {
        &self.end + &self.resonator_end
            <= &self.interior + &self.resonator_interior + self.supplied() - &self.split
                + &self.bound
    }

    /// The stronger reading, not a law: `deposition + ingest ≤ L`.
    pub fn within_loss(&self) -> bool {
        self.work() <= self.loss
    }

    /// The work beyond the next word's loss: `(deposition + ingest − L)₊`.
    pub fn excess(&self) -> Rat {
        let excess = self.work() - &self.loss;
        if excess.is_positive() {
            excess
        } else {
            Rat::zero()
        }
    }
}

/// [definition] **What a word's end releases**: the power of the unread change, which leaves as
/// the word's emitted exchange; the junction steps taken; the peak exact bits of any entry of the
/// change inside the word; every tick's balance; the last junction's residual and bound; the end
/// change itself (its commit's operand); every carried
/// remainder, released and read ([`Remainders`]); every chart's reading (its certificate against
/// the target, its refinement's steps and seed); and each declared resonator's balance
/// ([`ResonatorBalance`]).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Released {
    pub power: Rat,
    pub ticks: usize,
    pub peak_bits: u64,
    pub balances: Vec<TickBalance>,
    pub last: Rat,
    /// The last junction's certified bound on its residual.
    pub last_bound: Rat,
    /// The change the word releases, which its commit reads ([`WordBalance::commit`]).
    pub end: EndChange,
    pub remainders: Remainders,
    pub charts: Vec<ChartReading>,
    /// Each declared resonator's balance over the word, in ring order (campaign 2).
    pub resonators: Vec<ResonatorBalance>,
}

/// One ring's junction at a step: the executed Swing, the anchor's next remainder, and the
/// junction's residual term with its bound.
struct Swung {
    junction: Junction,
    remainder: Vec<Rat>,
    residual: Rat,
    bound: Rat,
}

/// One ring's element at a tick: the carried storage, its remainder, the midpoint, and its balance
/// terms (passive, contrast, chart, split) with the bound.
struct Stepped {
    next: Vec<Rat>,
    remainder: Vec<Rat>,
    drive_remainder: Vec<Rat>,
    midpoint: Vec<Rat>,
    resist: Rat,
    drive: Rat,
    chart: Rat,
    split: Rat,
    bound: Rat,
    resonance: Option<ResonatorStep>,
    loaded_port: Rat,
    loaded_split: Rat,
}

/// One contact's transit at a tick: the carried arrivals, state and solve with their remainders,
/// the midpoint rate, the dissipation and its residual terms with the bound.
struct Passed {
    arrivals: [Vec<Rat>; 2],
    states: [Vec<Rat>; 2],
    remainders: ([Vec<Rat>; 2], [Vec<Rat>; 2], Vec<Rat>),
    midpoint: Vec<Rat>,
    dissipation: Rat,
    chart: Rat,
    split: Rat,
    bound: Rat,
    parting: Option<BreakReceipt>,
}

/// The change with every source ring's storage at zero (`Π_int`, record B §2.1).
fn interior_of(field: &Field, mut change: EndChange) -> EndChange {
    for (ring, wave) in change.storage.iter_mut().enumerate() {
        if field.is_source(ring) {
            *wave = zeros(wave.len());
        }
    }
    change
}

fn zeros(n: usize) -> Vec<Rat> {
    vec![Rat::zero(); n]
}

fn l1(vector: &[Rat]) -> Rat {
    vector.iter().map(|x| x.abs()).sum()
}

fn sup(vector: &[Rat]) -> Rat {
    vector
        .iter()
        .map(|x| x.abs())
        .max()
        .unwrap_or_else(Rat::zero)
}

/// **Split at the transients' lattice with error feedback**, or leave the image under the exact
/// law: the carried values and the next remainders.
fn split(lattice: Option<&Lattice>, image: Vec<Rat>, remainder: &[Rat]) -> (Vec<Rat>, Vec<Rat>) {
    match lattice {
        Some(lattice) => {
            let mut next = remainder.to_vec();
            let carried = carry(lattice, &image, &mut next);
            (carried, next)
        }
        None => (image, remainder.to_vec()),
    }
}

/// `|x|² − |x̂|² = ⟨x − x̂, x + x̂⟩` with its bound `u ‖x + x̂‖₁` (`|x − x̂| < u` a split).
fn split_energy(carried: &[Rat], image: &[Rat], unit: &Rat) -> (Rat, Rat) {
    let sum = add(carried, image);
    (dot(&sub(carried, image), &sum), unit * l1(&sum))
}

impl<'c> Word<'c> {
    /// **Open a word at the cut** on the moment: zero change, with `s_g(0) = P_g^(τ_g) m̃_g` on the
    /// source rings; every solve seeded afresh.
    pub fn open(
        field: &'c Field,
        constitution: &impl ConstitutionRead,
        current: &Current,
        moment: &SourceMoment,
    ) -> Result<Self, HnnError> {
        Self::open_charted(field, constitution, current, moment, &mut Charts::new())
    }

    /// **Open a word at the cut, its solves warm-started from a resident's charts**.
    pub fn open_charted(
        field: &'c Field,
        constitution: &impl ConstitutionRead,
        current: &Current,
        moment: &SourceMoment,
        charts: &mut Charts,
    ) -> Result<Self, HnnError> {
        let storage = moment.open_storage(field, constitution, current)?;
        Self::on_operands(
            field,
            Operands::at_cut_charted(field, constitution, current, charts)?,
            storage,
        )
    }

    /// [definition; agent-inferred, October 3; the reception carry §2.1–§2.4, §2.3a] **Open a
    /// reception's word on its opening**: at [`WordOpening::Rest`], exactly [`Word::open_charted`].
    /// On a received carry, `x_(k+1)(0) = Π_int x_k(end) + s_(k+1)(0)` through [`Word::continuing`]
    /// at the carried tick, the carried change first crossed into this cut's references
    /// ([`ReceptionCarry::crossed`]: each contact's waves transmitted at its conductance, its rate
    /// held at momentum against its storage): `Π_int` keeps every interior coordinate and zeroes each source ring's storage,
    /// so the moment's open storage, nonzero only on the source rings, is imposed there and adds to
    /// nothing elsewhere (the source port is an imposed port; adding would count the passage once
    /// per reception). Under [`Absorption::Complete`] the carried change is the rest change, with
    /// every declared resonator opening at rest at the carried tick. Under [`Absorption::Nothing`]
    /// the carried change crosses into this cut's references and every declared resonator continues
    /// (record B §2.4): its state, held at momentum across the deposit, opens at the carried
    /// crossing's tick, whose previous phase is the one its last hop left, so its pump phase
    /// continues where the previous word's stopped.
    pub fn open_received(
        field: &'c Field,
        constitution: &impl ConstitutionRead,
        current: &Current,
        moment: &SourceMoment,
        charts: &mut Charts,
        opening: &WordOpening,
    ) -> Result<Self, HnnError> {
        let WordOpening::Received { carry, absorption } = opening else {
            return Self::open_charted(field, constitution, current, moment, charts);
        };
        let storage = moment.open_storage(field, constitution, current)?;
        let operands = Operands::at_cut_charted(field, constitution, current, charts)?;
        let change = match absorption {
            Absorption::Complete => {
                let rings = field.rings().len();
                EndChange {
                    resonators: vec![None; rings],
                    resonator_phases: vec![None; rings],
                    ..EndChange::rest(field, &operands)
                }
            }
            Absorption::Nothing => {
                let contacts = operands.contacts();
                let conductances: Vec<Rat> =
                    contacts.iter().map(|c| c.conductance().clone()).collect();
                let storage: Vec<&ExactRatMatrix> = contacts.iter().map(|c| c.forms().0).collect();
                let resonators: Vec<Option<&ExactRatMatrix>> = operands
                    .resonators()
                    .iter()
                    .map(|r| r.as_ref().map(|r| r.material().forms().0))
                    .collect();
                carry.opening(field, &conductances, &storage, &resonators)?
            }
        };
        Self::continuing(field, operands, &change, &storage, carry.ticks)
    }

    /// [definition; agent-inferred, October 5] Enter the exact physical field on its
    /// contemporary material, continuing its received interior and imposing this source once.
    /// The material-only interface admits no receiving storage, target or reference family.
    /// SourceMoment supplies the source chart; it is never a loaded displacement.
    /// The material is read once at the cut through its shared read face; the Word owns
    /// the copied operands, so this interface carries no material borrow into a tick.
    ///
    /// The receipt starts after the declared absorption and material/reference crossing:
    /// E_after - E_before = imposed - absorbed. Previous crossing/deposition work belongs
    /// to PowerForm::held and ChainedBalance, not to this source-imposition receipt.
    /// Subsequent Word::tick executes the actual junction, element and loaded port drive;
    /// this opening does not certify a frozen-drive periodic component or release a symbol.
    pub fn open_exact_received(
        field: &'c Field,
        material: &dyn crate::hnn::field::FieldMaterial,
        current: &Current,
        source: &SourceMoment,
        opening: &WordOpening,
    ) -> Result<(Self, SourceOpeningReceipt), HnnError> {
        let injection = source.open_storage(field, material, current)?;
        let operands = Operands::exact_at_cut(field, material, current)?;
        let (change, opened_at) = match opening {
            WordOpening::Rest => (EndChange::rest(field, &operands), 0),
            WordOpening::Received {
                carry,
                absorption: Absorption::Complete,
            } => (
                EndChange {
                    resonators: vec![None; field.rings().len()],
                    resonator_phases: vec![None; field.rings().len()],
                    ..EndChange::rest(field, &operands)
                },
                carry.ticks,
            ),
            WordOpening::Received {
                carry,
                absorption: Absorption::Nothing,
            } => {
                let contacts = operands.contacts();
                let conductances: Vec<Rat> =
                    contacts.iter().map(|c| c.conductance().clone()).collect();
                let capacities: Vec<&ExactRatMatrix> =
                    contacts.iter().map(|c| c.forms().0).collect();
                let resonators: Vec<Option<&ExactRatMatrix>> = operands
                    .resonators()
                    .iter()
                    .map(|r| r.as_ref().map(|r| r.material().forms().0))
                    .collect();
                (
                    carry.crossed(&conductances, &capacities, &resonators)?,
                    carry.ticks,
                )
            }
        };
        // Validate the entered state and its actual pump phase before reading any energy.
        // Exact operands split nothing; an absent declared state is its clock's rest point.
        let entered = Self::on_change(field, operands.clone(), change, opened_at)?;
        let before_change = entered.change()?;
        let form = PowerForm::read(field, material, current)?;
        let before = form.power(&before_change)? + form.resonator_power(&before_change)?;
        let absorbed: Rat = before_change
            .storage
            .iter()
            .enumerate()
            .filter(|(ring, _)| field.is_source(*ring))
            .map(|(ring, wave)| form.ring_power(ring, wave))
            .sum();
        let interior = interior_of(field, before_change);
        let word = Self::continuing(field, operands, &interior, &injection, opened_at)?;
        let after_change = word.change()?;
        let after = form.power(&after_change)? + form.resonator_power(&after_change)?;
        let imposed: Rat = injection
            .iter()
            .enumerate()
            .filter(|(ring, _)| field.is_source(*ring))
            .map(|(ring, wave)| form.ring_power(ring, wave))
            .sum();
        let receipt = SourceOpeningReceipt {
            before,
            after,
            absorbed,
            imposed,
        };
        if !receipt.closes() {
            return Err(HnnError::ContinuingState {
                what: "the exact source imposition does not close its work balance",
            });
        }
        Ok((word, receipt))
    }

    /// [agent-inferred] Impose the actual source once, on warm certified charts, while
    /// retaining the declared carry's crossed interior and absolute pump clock. The source
    /// work and the coordinate opening split have separate producing receipts. Existing
    /// exact and charted entries keep their contracts; this entry adds their physical join.
    pub fn open_charted_received(
        field: &'c Field,
        material: &dyn crate::hnn::field::FieldMaterial,
        current: &Current,
        source: &SourceMoment,
        charts: &mut Charts,
        opening: &WordOpening,
    ) -> Result<(Self, ChartedSourceOpeningReceipt), HnnError> {
        let injection = source.open_storage(field, material, current)?;
        let operands = Operands::at_cut_charted(field, material, current, charts)?;
        let (mut entered, opened_at) = match opening {
            WordOpening::Rest => (EndChange::rest(field, &operands), 0),
            WordOpening::Received { carry, absorption: Absorption::Complete } =>
                (EndChange::rest(field, &operands), carry.ticks),
            WordOpening::Received { carry, absorption: Absorption::Nothing } => {
                let conductances: Vec<_> = operands.contacts().iter()
                    .map(|c| c.conductance().clone()).collect();
                let storage: Vec<_> = operands.contacts().iter().map(|c| c.forms().0).collect();
                let resonators: Vec<_> = operands.resonators().iter()
                    .map(|r| r.as_ref().map(|r| r.material().forms().0)).collect();
                (carry.crossed(&conductances, &storage, &resonators)?, carry.ticks)
            }
        };
        let shaped = entered.storage.len() == field.rings().len()
            && entered.storage.iter().zip(field.rings()).all(|(s,r)|s.len()==r.width())
            && entered.arrivals.len()==field.contacts().len()
            && entered.states.len()==field.contacts().len()
            && entered.resonators.len()==field.rings().len()
            && entered.resonator_phases.len()==field.rings().len()
            && entered.arrivals.iter().zip(&entered.states).zip(operands.contacts()).all(|((a,s),c)| {
                let (g,h)=c.ends(); a[0].len()==field.ring(g).width() && a[1].len()==field.ring(h).width()
                    && s.iter().all(|s|s.len()==c.width())
            })
            && entered.resonators.iter().zip(operands.resonators()).all(|(s,r)|match(s,r) {
                (Some(s),Some(r))=>s.iter().all(|s|s.len()==r.width()), (None,_)=>true, _=>false,
            });
        if !shaped {
            return Err(HnnError::ContinuingState { what: "the charted source opening has a foreign carried field shape" });
        }
        for (ring, resonator) in operands.resonators().iter().enumerate() {
            if let Some(resonator) = resonator {
                let phase = resonator.phase_at(opened_at.saturating_sub(1));
                if matches!(opening, WordOpening::Received { absorption: Absorption::Nothing, .. })
                    && entered.resonator_phases[ring].is_some_and(|p| p != phase)
                {
                    return Err(HnnError::Resonator {
                        ring, what: "the charted opening keeps the carry's actual pump clock",
                    });
                }
                entered.resonator_phases[ring] = Some(phase);
            }
        }
        let form = PowerForm::read(field, material, current)?;
        let before = form.power(&entered)? + form.resonator_power(&entered)?;
        let absorbed = field.sources().iter()
            .map(|&g| form.ring_power(g, &entered.storage[g])).sum();
        let interior = interior_of(field, entered);
        let mut raw = interior.clone();
        for (storage, injection) in raw.storage.iter_mut().zip(&injection) {
            *storage = add(storage, injection);
        }
        let word = Self::continuing(field, operands, &interior, &injection, opened_at)?;
        let actual = word.change()?;
        let after = form.power(&actual)? + form.resonator_power(&actual)?;
        let raw_power = form.power(&raw)? + form.resonator_power(&raw)?;
        let imposed = field.sources().iter()
            .map(|&g| form.ring_power(g, &injection[g])).sum();
        let difference = |a: &[Rat], b: &[Rat]| a.iter().zip(b)
            .map(|(a, b)| (a-b).abs()).collect::<Vec<_>>();
        let mut error = actual.clone();
        for ((e, a), b) in error.storage.iter_mut().zip(&actual.storage).zip(&raw.storage) {
            *e = difference(a, b);
        }
        for (errors, (actual, raw)) in error.arrivals.iter_mut().zip(actual.arrivals.iter().zip(&raw.arrivals)) {
            for k in 0..2 { errors[k] = difference(&actual[k], &raw[k]); }
        }
        for (errors, (actual, raw)) in error.states.iter_mut().zip(actual.states.iter().zip(&raw.states)) {
            for k in 0..2 { errors[k] = difference(&actual[k], &raw[k]); }
        }
        for (errors, (actual, raw)) in error.resonators.iter_mut().zip(actual.resonators.iter().zip(&raw.resonators)) {
            if let (Some(errors), Some(actual)) = (errors, actual) {
                for k in 0..2 {
                    errors[k] = match raw { Some(raw) => difference(&actual[k], &raw[k]),
                        None => actual[k].iter().map(|a| a.abs()).collect() };
                }
            }
        }
        let receipt = ChartedSourceOpeningReceipt {
            source: SourceOpeningReceipt { before, after: after.clone(), absorbed, imposed },
            split: raw_power - after,
            error,
        };
        if !receipt.closes() {
            return Err(HnnError::ContinuingState {
                what: "the charted source imposition does not close with its opening split",
            });
        }
        Ok((word, receipt))
    }

    /// Open a word on a declared storage injection (every wave and contact state still zero), every
    /// solve seeded afresh: the impulse of the law's own tests.
    #[cfg(test)]
    pub(crate) fn open_on(
        field: &'c Field,
        constitution: &impl ConstitutionRead,
        current: &Current,
        storage: Vec<Vec<Rat>>,
    ) -> Result<Self, HnnError> {
        Self::on_operands(
            field,
            Operands::at_cut(field, constitution, current)?,
            storage,
        )
    }

    /// Open a word on operands already read at the cut (the basis of the observability rank, on the
    /// exact law's operands). On the word's lattices the opening storage is carried at once: split
    /// with its remainder, the first tick of its error feedback.
    pub(crate) fn on_operands(
        field: &'c Field,
        operands: Operands,
        storage: Vec<Vec<Rat>>,
    ) -> Result<Self, HnnError> {
        let rest = EndChange::rest(field, &operands);
        let storage_shaped = storage.len() == field.rings().len()
            && field
                .rings()
                .iter()
                .zip(&storage)
                .all(|(ring, wave)| wave.len() == ring.width());
        if !storage_shaped {
            return Err(HnnError::Shape {
                what: "open storage (one wave per ring, each of its ring's width)",
                expected: field.rings().len(),
                found: storage.len(),
            });
        }
        Self::on_change(field, operands, EndChange { storage, ..rest }, 0)
    }

    /// [definition; agent-inferred] **Open a continuing word** (module header, "Continuing motion
    /// within a refinement"): on the change `change` the previous word of the same refinement left
    /// (its storage waves, arriving waves, contact states and resonator states), with `injection`
    /// added at every ring's storage port, at the refinement clock's tick `opened_at`. Every carried
    /// remainder opens at zero: the previous word released its own at its end, and the opening
    /// storage is split once at the transients' lattice, as at rest. Refused on a change or an
    /// injection not of the field's shape, or on resonator states where none is declared.
    pub fn continuing(
        field: &'c Field,
        operands: Operands,
        change: &EndChange,
        injection: &[Vec<Rat>],
        opened_at: usize,
    ) -> Result<Self, HnnError> {
        if injection.len() != change.storage.len() {
            return Err(HnnError::Shape {
                what: "the injection (one wave per ring)",
                expected: change.storage.len(),
                found: injection.len(),
            });
        }
        let mut storage = Vec::with_capacity(change.storage.len());
        for (wave, added) in change.storage.iter().zip(injection) {
            if wave.len() != added.len() {
                return Err(HnnError::Shape {
                    what: "an injected wave against its ring's carried storage",
                    expected: wave.len(),
                    found: added.len(),
                });
            }
            storage.push(add(wave, added));
        }
        Self::on_change(
            field,
            operands,
            EndChange {
                storage,
                ..change.clone()
            },
            opened_at,
        )
    }

    /// Open on a change at the refinement clock's tick `opened_at`: every shape checked, the
    /// opening storage split once at the transients' lattice (the first tick of its error
    /// feedback), every other carried remainder zero.
    fn on_change(
        field: &'c Field,
        operands: Operands,
        change: EndChange,
        opened_at: usize,
    ) -> Result<Self, HnnError> {
        work::reached(work::Event::WordOpenAttempt);
        let EndChange {
            storage,
            arrivals,
            states,
            resonators: resonator_states,
            resonator_phases,
        } = change;
        let widths: Vec<usize> = field.rings().iter().map(|ring| ring.width()).collect();
        let shaped = storage.len() == widths.len()
            && storage
                .iter()
                .zip(&widths)
                .all(|(wave, n)| wave.len() == *n)
            && arrivals.len() == field.contacts().len()
            && states.len() == field.contacts().len()
            && field
                .contacts()
                .iter()
                .zip(arrivals.iter().zip(&states))
                .all(|(contact, (pair, state))| {
                    let (from, to) = contact.ends();
                    pair[0].len() == widths[from]
                        && pair[1].len() == widths[to]
                        && state.iter().all(|x| x.len() == contact.width())
                })
            && resonator_phases.len() == widths.len()
            && resonator_states.len() == widths.len()
            && resonator_states
                .iter()
                .zip(operands.resonators())
                .all(|(state, declared)| match (state, declared) {
                    (None, _) => true,
                    (Some(state), Some(resonator)) => {
                        state.iter().all(|x| x.len() == resonator.width())
                    }
                    (Some(_), None) => false,
                });
        if !shaped {
            return Err(HnnError::Shape {
                what: "a word's opening change (storage per ring, arrivals and states per contact, resonator states only where declared)",
                expected: widths.len(),
                found: storage.len(),
            });
        }
        // [agent-inferred] A supplied phase certifies this clock; it never requests a new clock.
        // An absent state/phase opens at rest in that clock. A supplied phase must fit even at
        // rest; a present state must supply its frame. No phase exists on an undeclared resonator.
        for (ring, ((state, phase), declared)) in resonator_states
            .iter()
            .zip(&resonator_phases)
            .zip(operands.resonators())
            .enumerate()
        {
            match declared {
                Some(resonator) => {
                    let expected = resonator.phase_at(opened_at.saturating_sub(1));
                    if phase.is_some_and(|phase| phase != expected)
                        || (state.is_some() && phase.is_none())
                    {
                        return Err(HnnError::Resonator {
                            ring,
                            what: "the carried resonator phase does not fit the opening clock",
                        });
                    }
                }
                None if phase.is_some() => {
                    return Err(HnnError::Resonator {
                        ring,
                        what: "an opening phase was supplied without a declared resonator",
                    });
                }
                None => {}
            }
        }
        let lattice = operands.lattice().map(|word| word.transient());
        // [definition; agent-inferred, record B §2.3a] The opening's waves and states are split
        // once at the transients' lattice, as the storage is: a carried change crossed into this
        // cut's references (a transmitted wave, a rate held at momentum) need not lie on it, and
        // its remainder opens the error feedback. A change already on the lattice splits to itself
        // with a zero remainder.
        let mut split_pair = |pair: [Vec<Rat>; 2]| -> ([Vec<Rat>; 2], [Vec<Rat>; 2]) {
            let [first, second] = pair;
            let (first, first_remainder) =
                split(lattice.as_ref(), first.clone(), &zeros(first.len()));
            let (second, second_remainder) =
                split(lattice.as_ref(), second.clone(), &zeros(second.len()));
            ([first, second], [first_remainder, second_remainder])
        };
        let (arrivals, arrival_remainders): (Vec<_>, Vec<_>) =
            arrivals.into_iter().map(&mut split_pair).unzip();
        let (states, state_remainders): (Vec<_>, Vec<_>) =
            states.into_iter().map(&mut split_pair).unzip();
        let mut carried = Carried {
            anchors: widths.iter().map(|n| zeros(*n)).collect(),
            storage: Vec::with_capacity(widths.len()),
            element_drive: widths.iter().map(|n| zeros(*n)).collect(),
            solves: field
                .contacts()
                .iter()
                .map(|contact| zeros(contact.width()))
                .collect(),
            arrivals: arrival_remainders,
            states: state_remainders,
        };
        // The source-open split belongs to the ordinary ring element's incoming storage chart.
        // Once a resonator is inserted after that element, the returned wave starts a distinct
        // output chart with no prior returned-wave remainder.
        let storage: Vec<Vec<Rat>> = storage
            .into_iter()
            .enumerate()
            .map(|(ring, wave)| {
                let (opened, remainder) = split(lattice.as_ref(), wave.clone(), &zeros(wave.len()));
                if operands.resonators()[ring].is_some() {
                    // The opening storage remainder belongs to the element-output stream. A
                    // loaded returned wave starts its own carry chain at zero.
                    carried.storage.push(zeros(wave.len()));
                    carried.element_drive[ring] = remainder;
                } else {
                    carried.storage.push(remainder);
                }
                opened
            })
            .collect();
        // [definition; agent-inferred, record B §2.4] A carried resonator state is split once at
        // the transients' lattice, as the contacts' states are: a rate held at momentum across a
        // moved capacity need not lie on it, and its remainder opens the state's error feedback
        // (`ResonatorRemainders::state`). A state on the lattice splits to itself.
        let resonators = operands
            .resonators()
            .iter()
            .zip(resonator_states)
            .map(
                |(resonator, state)| -> Result<Option<Resonance>, HnnError> {
                    let Some(resonator) = resonator else {
                        return Ok(None);
                    };
                    let n = resonator.width();
                    let (state, remainders) = match state {
                        Some(state) => {
                            let ([u, w], [u_rest, w_rest]) = split_pair(state);
                            (
                                [u, w],
                                ResonatorRemainders {
                                    rate: zeros(n),
                                    state: [u_rest, w_rest],
                                },
                            )
                        }
                        None => ([zeros(n), zeros(n)], ResonatorRemainders::default()),
                    };
                    let open = resonator.energy_at(
                        resonator.phase_at(opened_at.saturating_sub(1)),
                        &state[0],
                        &state[1],
                    )?;
                    Ok(Some(Resonance {
                        open,
                        state,
                        remainders,
                        steps: Vec::new(),
                    }))
                },
            )
            .collect::<Result<Vec<_>, HnnError>>()?;
        // The hop clock reads the refinement's ticks: a continuing word's clock opens where the
        // previous word's stopped.
        let mut clock = Clock::unwound(field.step().clone())?;
        if opened_at > 0 {
            clock.advance(&BigUint::from(opened_at));
        }
        let mut word = Self {
            native_source: None,
            field,
            operands,
            clock,
            storage,
            arrivals,
            states,
            carried,
            passage: Vec::new(),
            balances: Vec::new(),
            ended: false,
            peak_bits: 0,
            last: Rat::zero(),
            last_bound: Rat::zero(),
            settled: None,
            resonators,
            fields: Vec::new(),
            partings: Vec::new(),
            opened_at,
        };
        word.peak_bits = word.state_bits();
        work::reached(work::Event::WordOpen);
        Ok(word)
    }

    /// The field the word borrows.
    pub fn field(&self) -> &'c Field {
        self.field
    }

    /// The operands fixed at the cut.
    pub fn operands(&self) -> &Operands {
        &self.operands
    }

    /// The word's own hop clock.
    pub fn clock(&self) -> &Clock {
        &self.clock
    }

    /// The junction steps taken: every ring's tick count, since every junction ticks once per hop.
    pub fn ticks(&self) -> usize {
        self.passage.len()
    }

    /// The refinement clock's tick at the word's open (module header): zero at rest.
    pub fn opened_at(&self) -> usize {
        self.opened_at
    }

    /// Whether the word has run its last junction and ended.
    pub fn is_ended(&self) -> bool {
        self.ended
    }

    /// **Run `ticks` full ticks** (junction, element, loaded resonator, contact transit), each
    /// balance recorded; refused once the word has ended.
    pub fn run(&mut self, ticks: usize) -> Result<(), HnnError> {
        for _ in 0..ticks {
            self.tick()?;
        }
        Ok(())
    }

    /// **The change now** (module header, "Continuing motion within a refinement"): the storage
    /// waves, the arriving waves, the contact states and the resonator states as the last full
    /// tick left them, with the pump phase of each resonator's form, which a continuing word opens
    /// on. Refused once the word has ended at a last junction, whose arriving waves are outgoing.
    pub fn change(&self) -> Result<EndChange, HnnError> {
        if self.ended {
            return Err(HnnError::WordEnded {
                ticks: self.passage.len(),
            });
        }
        Ok(self.end_change())
    }

    /// The change as the word holds it, with each resonator's form phase: its last executed
    /// tick's, and with no tick of this word the phase at the word's open.
    fn end_change(&self) -> EndChange {
        EndChange {
            storage: self.storage.clone(),
            arrivals: self.arrivals.clone(),
            states: self.states.clone(),
            resonators: self
                .resonators
                .iter()
                .map(|resonance| resonance.as_ref().map(|r| r.state.clone()))
                .collect(),
            // The last executed tick's phase; with no full tick, the phase at the word's open,
            // where the open state is read (`EndChange::resonator_phases`).
            resonator_phases: self
                .resonators
                .iter()
                .zip(self.operands.resonators())
                .map(|(resonance, operands)| {
                    resonance.as_ref().map(|r| {
                        r.steps.last().map_or_else(
                            || {
                                // The open state is read at the phase the previous tick left
                                // (`ResonatorOperands::step` reads `before` there), phase 0 at rest.
                                operands.as_ref().map_or(0, |operands| {
                                    operands.phase_at(self.opened_at.saturating_sub(1))
                                })
                            },
                            |step| step.phase,
                        )
                    })
                })
                .collect(),
        }
    }

    /// [definition; agent-inferred, October 3; the reception carry §2.1, §2.4] **The reception's
    /// carried end**: the change the word's motion reached at its last crossing and that crossing's
    /// tick, with each contact's conductance and momentum and each resonator's momentum at the
    /// word's cut, read when its return consumes it.
    ///
    /// [definition; record B §2.4] A junction is a crossing, the clock's tick; the hop after it
    /// runs the elements, the resonators at that tick's pump phase, and the transits. A word that
    /// ended at a last junction has scattered its last crossing `T = opened_at + junction steps − 1`
    /// for its receiver's reading but has not run hop `T`, so its motion stands at that crossing:
    /// the change arriving there ([`Passage`]'s record before the junction, its arriving waves
    /// arrivals and its storage the elements' last output), every resonator state and phase as hop
    /// `T − 1` left them, at tick `T`. The next word opens there and scatters crossing `T` in the
    /// medium the reception leaves, and its first hop is `T`, at pump phase `T`. A word not ended at
    /// a junction carries its full-tick change at `opened_at + ticks`, the within-refinement cut.
    pub fn reception_end(&self) -> Result<ReceptionCarry, HnnError> {
        let mut change = self.end_change();
        let mut ticks = self.opened_at + self.passage.len();
        if self.ended {
            let crossing = self
                .passage
                .last()
                .ok_or(HnnError::WordEnded { ticks: 0 })?;
            change.storage = crossing.storage.clone();
            change.arrivals = crossing.arrivals.clone();
            change.states = crossing.states.clone();
            ticks -= 1;
        }
        let contacts = self.operands.contacts();
        let momenta = contacts
            .iter()
            .zip(&change.states)
            .map(|(contact, [_, rate])| Ok(contact.forms().0.apply(rate)?))
            .collect::<Result<Vec<_>, HnnError>>()?;
        let resonator_momenta = change
            .resonators
            .iter()
            .zip(self.operands.resonators())
            .map(|(state, resonator)| match (state, resonator) {
                (Some([_, rate]), Some(resonator)) => {
                    Ok(Some(resonator.material().forms().0.apply(rate)?))
                }
                _ => Ok(None),
            })
            .collect::<Result<Vec<_>, HnnError>>()?;
        Ok(ReceptionCarry {
            ticks,
            conductances: contacts.iter().map(|c| c.conductance().clone()).collect(),
            momenta,
            resonator_momenta,
            change,
        })
    }

    /// Every full tick's balance, in order.
    pub fn balances(&self) -> &[TickBalance] {
        &self.balances
    }

    /// The anchor `v_r` read by junction step `step`, when it has run: the carried anchor on the
    /// word's lattices.
    pub fn anchor(&self, step: usize, ring: usize) -> Option<&[Rat]> {
        self.passage
            .get(step)
            .and_then(|record| record.anchors.get(ring))
            .map(Vec::as_slice)
    }

    /// The change at the start of each junction step, in order, with its anchors and executed
    /// midpoints: the records the word's return reads in reverse (design R2 H2). They live only in
    /// the word.
    pub(crate) fn recorded(&self) -> &[Passage] {
        &self.passage
    }

    /// Each contact's carried transit-solve remainder `r_ζ` (zero under the exact law). Two words
    /// holding equal representatives differ here by their accumulated image difference.
    #[cfg(test)]
    pub(crate) fn solve_remainders(&self) -> &[Vec<Rat>] {
        &self.carried.solves
    }

    /// Each contact's carried state remainders `[σ, ρ]` (displacement, rate; zero under the exact
    /// law). At an opening they hold what the split of a held rate left off the lattice.
    #[cfg(test)]
    pub(crate) fn state_remainders(&self) -> &[[Vec<Rat>; 2]] {
        &self.carried.states
    }

    /// The peak exact bits of any entry of the change so far, a reading.
    pub fn peak_bits(&self) -> u64 {
        self.peak_bits
    }

    /// **The global power of the change now.**
    pub fn power(&self) -> Result<Rat, HnnError> {
        global_power(&self.operands, &self.storage, &self.arrivals, &self.states)
    }

    /// **The support of the change over the rings**: ring `r` carries change when its storage or
    /// any wave arriving at it is nonzero (its block, design (a), retention item 3).
    pub fn support(&self) -> Vec<bool> {
        let mut carried: Vec<bool> = self
            .storage
            .iter()
            .map(|wave| wave.iter().any(|x| !x.is_zero()))
            .collect();
        for (contact, pair) in self.operands.contacts().iter().zip(&self.arrivals) {
            let (from, to) = contact.ends();
            carried[from] |= pair[0].iter().any(|x| !x.is_zero());
            carried[to] |= pair[1].iter().any(|x| !x.is_zero());
        }
        carried
    }

    /// **The front**: the rings at which some arriving wave is nonzero.
    pub fn front(&self) -> Vec<bool> {
        let mut front = vec![false; self.storage.len()];
        for (contact, pair) in self.operands.contacts().iter().zip(&self.arrivals) {
            let (from, to) = contact.ends();
            front[from] |= pair[0].iter().any(|x| !x.is_zero());
            front[to] |= pair[1].iter().any(|x| !x.is_zero());
        }
        front
    }

    /// The support of the change over the contacts' own states.
    #[cfg(test)]
    pub(crate) fn contact_support(&self) -> Vec<bool> {
        self.states
            .iter()
            .map(|state| state.iter().flatten().any(|x| !x.is_zero()))
            .collect()
    }

    /// Largest rational coordinate of the current wave/contact/mode state. Carried residuals
    /// have their own complete bit receipt in Released and ResonatorBalance.
    fn state_bits(&self) -> u64 {
        let bits = |x: &Rat| x.numer().bits() + x.denom().bits();
        let field = self
            .storage
            .iter()
            .flatten()
            .chain(self.arrivals.iter().flatten().flatten())
            .chain(self.states.iter().flatten().flatten())
            .map(bits)
            .max()
            .unwrap_or(0);
        self.resonators
            .iter()
            .filter_map(Option::as_ref)
            .flat_map(|resonance| resonance.state.iter().flatten())
            .map(bits)
            .max()
            .unwrap_or(0)
            .max(field)
    }

    /// The transients' lattice, or `None` under the exact law.
    fn transient(&self) -> Option<Lattice> {
        self.operands.lattice().map(|word| word.transient())
    }

    /// Every ring's junction at this step, its anchor carried, recorded; with the junctions'
    /// residual term and its bound.
    fn junctions(&mut self) -> Result<(Vec<Junction>, Rat, Rat), HnnError> {
        work::reached(work::Event::JunctionAttempt);
        if self.ended {
            return Err(HnnError::WordEnded {
                ticks: self.passage.len(),
            });
        }
        let lattice = self.transient();
        // Every junction reads only its own storage, arrivals and anchor remainder: the rings run
        // together.
        let (operands, storage, arrivals, remainders) = (
            &self.operands,
            &self.storage,
            &self.arrivals,
            &self.carried.anchors,
        );
        let h = operands.step();
        let swung = indexed(operands.rings().len(), |ring| {
            let incoming: Vec<&[Rat]> = operands
                .incident(ring)
                .iter()
                .map(|&a| arrivals[a][operands.end_slot(a, ring)].as_slice())
                .collect();
            let image = participation(operands.weights(ring), &storage[ring], &incoming)?;
            let (anchor, remainder) = split(lattice.as_ref(), image, &remainders[ring]);
            let (residual, bound) = match &lattice {
                Some(lattice) => {
                    // h W ⟨v, v − v*⟩, with ‖v − v*‖∞ ≤ ‖ŵ − w‖₁ max_p ‖x_p‖∞ + u.
                    let exact =
                        participation(operands.exact_weights(ring), &storage[ring], &incoming)?;
                    let total = admittance_total(operands, ring);
                    let largest = std::iter::once(storage[ring].as_slice())
                        .chain(incoming.iter().copied())
                        .map(sup)
                        .max()
                        .unwrap_or_else(Rat::zero);
                    (
                        h * &total * dot(&anchor, &sub(&anchor, &exact)),
                        h * &total
                            * l1(&anchor)
                            * (operands.junction_certificate(ring) * largest + lattice.unit()),
                    )
                }
                None => (Rat::zero(), Rat::zero()),
            };
            Ok::<_, HnnError>(Swung {
                junction: scattering_about(anchor, &storage[ring], &incoming),
                remainder,
                residual,
                bound,
            })
        })?;
        let mut junctions = Vec::with_capacity(swung.len());
        let (mut residual, mut bound) = (Rat::zero(), Rat::zero());
        for (ring, part) in swung.into_iter().enumerate() {
            self.carried.anchors[ring] = part.remainder;
            residual += part.residual;
            bound += part.bound;
            junctions.push(part.junction);
        }
        self.passage.push(Passage {
            storage: self.storage.clone(),
            arrivals: self.arrivals.clone(),
            states: self.states.clone(),
            anchors: junctions.iter().map(|j| j.anchor.clone()).collect(),
            midpoints: Vec::new(),
            rates: Vec::new(),
        });
        self.clock.advance(&1u32.into());
        work::reached(work::Event::Junction);
        Ok((junctions, residual, bound))
    }

    /// **One full tick**: every junction, then every ring element, then every contact transit,
    /// each carried output split with its remainder. Returns its balance, which closes up to its
    /// reported residual (Lean `HNN/Word.word_tick_balance`; exactly under the exact law).
    pub fn tick(&mut self) -> Result<TickBalance, HnnError> {
        // The previous tick's `after` is this tick's `before`: the change has not moved since.
        let before = match self.settled.take() {
            Some(power) => power,
            None => self.power()?,
        };
        let (junctions, junction_defect, mut bound) = self.junctions()?;
        let (mut element_chart, mut element_split) = (Rat::zero(), Rat::zero());
        let (mut transit_chart, mut transit_split) = (Rat::zero(), Rat::zero());
        let lattice = self.transient();
        let unit = lattice.as_ref().map_or_else(Rat::zero, Lattice::unit);
        let h = self.operands.step().clone();
        let half = &h / integer(2);
        let quarter = &h / integer(4);
        let (mut resist, mut contrast, mut dissipation) = (Rat::zero(), Rat::zero(), Rat::zero());
        // Every element reads only its own junction and storage remainder: the rings run together,
        // and their balance terms are summed afterwards in ring order.
        let (operands, remainders, drive_remainders, resonances) = (
            &self.operands,
            &self.carried.storage,
            &self.carried.element_drive,
            &self.resonators,
        );
        // The pump reads the refinement's clock: its phase at this tick continues across a
        // continuing word's boundary (module header).
        let tick = self.opened_at + self.passage.len() - 1;
        let steps = indexed(junctions.len(), |ring| {
            let element = element_step(
                &operands.rings()[ring],
                &junctions[ring].storage_wave,
                &junctions[ring].contrast,
            )?;
            let (
                next,
                remainder,
                drive_remainder,
                resonance,
                loaded_port,
                element_split,
                loaded_split,
                element_bound,
            ) = match (&operands.resonators()[ring], &resonances[ring]) {
                (Some(resonator), Some(resonance)) => {
                    let (drive, drive_remainder) = split(
                        lattice.as_ref(),
                        element.next.clone(),
                        &drive_remainders[ring],
                    );
                    let driven = resonator.step(
                        tick,
                        &drive,
                        [&resonance.state[0], &resonance.state[1]],
                        &resonance.remainders,
                        lattice.as_ref(),
                    )?;
                    // Enforce each producing tick's independent numerical certificates before
                    // aggregation; errors at different ticks must not cancel into acceptance.
                    if !driven.closes() {
                        return Err(HnnError::Resonator {
                            ring,
                            what: "an executed tick exceeds its chart or split certificate",
                        });
                    }
                    let (next, remainder) =
                        split(lattice.as_ref(), driven.output.clone(), &remainders[ring]);
                    let (element_power, element_bound) = split_energy(&drive, &element.next, &unit);
                    let (loaded_power, loaded_bound) = split_energy(&next, &driven.output, &unit);
                    let admittance = operands.rings()[ring].admittance();
                    let element_split = &quarter * admittance * element_power;
                    let loaded_split = &quarter * admittance * loaded_power;
                    let element_bound = &quarter * admittance * element_bound
                        + &quarter * admittance * loaded_bound;
                    let loaded_port = -driven.port.clone();
                    (
                        next,
                        remainder,
                        drive_remainder,
                        Some(driven),
                        loaded_port,
                        element_split,
                        loaded_split,
                        element_bound,
                    )
                }
                _ => {
                    let (next, remainder) =
                        split(lattice.as_ref(), element.next.clone(), &remainders[ring]);
                    let (split_power, split_bound) = split_energy(&next, &element.next, &unit);
                    (
                        next,
                        remainder,
                        drive_remainders[ring].clone(),
                        None,
                        Rat::zero(),
                        &quarter * operands.rings()[ring].admittance() * split_power,
                        Rat::zero(),
                        &quarter * operands.rings()[ring].admittance() * split_bound,
                    )
                }
            };
            let admittance = operands.rings()[ring].admittance();
            Ok::<_, HnnError>(Stepped {
                remainder,
                drive_remainder,
                midpoint: element.midpoint,
                resist: &half * admittance * &element.resist,
                drive: &half * admittance * &element.drive,
                chart: &half * admittance * &element.defect,
                split: element_split,
                bound: &half * admittance * &element.bound + element_bound,
                next,
                resonance,
                loaded_port,
                loaded_split,
            })
        })?;
        let mut midpoints = Vec::with_capacity(steps.len());
        let mut loaded_port = Rat::zero();
        let mut loaded_split = Rat::zero();
        let mut resonance_terms: [Rat; 9] = std::array::from_fn(|_| Rat::zero());
        for (ring, step) in steps.into_iter().enumerate() {
            resist += step.resist;
            contrast += step.drive;
            element_chart += step.chart;
            element_split += step.split;
            bound += step.bound;
            loaded_port += &step.loaded_port;
            loaded_split += &step.loaded_split;
            self.storage[ring] = step.next;
            self.carried.storage[ring] = step.remainder;
            self.carried.element_drive[ring] = step.drive_remainder;
            midpoints.push(step.midpoint);
            if let (Some(step), Some(resonance)) = (step.resonance, self.resonators[ring].as_mut())
            {
                for (total, term) in resonance_terms.iter_mut().zip([
                    &step.before,
                    &step.after,
                    &step.pump,
                    &step.port,
                    &step.dissipation,
                    &step.integration,
                    &step.chart,
                    &step.split,
                    &step.bound,
                ]) {
                    *total += term;
                }
                resonance.state = step.state.clone();
                resonance.remainders = step.remainders().clone();
                resonance.steps.push(step);
            }
        }
        // Every contact reads the outgoing waves of its two ends, its own state and its own
        // remainders, and writes only its own arrivals, state and remainders: the contacts run
        // together.
        let (operands, states, carried) = (&self.operands, &self.states, &self.carried);
        let transits = indexed(operands.contacts().len(), |a| {
            let contact = &operands.contacts()[a];
            let (from, to) = contact.ends();
            let outgoing = |ring: usize| {
                let position = operands
                    .incident(ring)
                    .iter()
                    .position(|&b| b == a)
                    .expect("a contact is incident to its ends");
                &junctions[ring].outgoing[position]
            };
            let (displacement, rate) = (&states[a][0], &states[a][1]);
            let (right, image) = transit_solve(
                contact,
                &h,
                outgoing(from),
                outgoing(to),
                displacement,
                rate,
            )?;
            let (solved, solve_remainder) = split(lattice.as_ref(), image, &carried.solves[a]);
            let passed = transit_update(
                contact,
                &h,
                &solved,
                outgoing(from),
                outgoing(to),
                displacement,
                rate,
            );
            let (chart_term, chart_bound) =
                transit_defect(contact, &solved, &passed.midpoint, &right, &unit);
            let (arrive_from, from_remainder) = split(
                lattice.as_ref(),
                passed.arrive_from.clone(),
                &carried.arrivals[a][0],
            );
            let (arrive_to, to_remainder) = split(
                lattice.as_ref(),
                passed.arrive_to.clone(),
                &carried.arrivals[a][1],
            );
            let (next_displacement, displacement_remainder) = split(
                lattice.as_ref(),
                passed.displacement.clone(),
                &carried.states[a][0],
            );
            let (next_rate, rate_remainder) =
                split(lattice.as_ref(), passed.rate.clone(), &carried.states[a][1]);
            let (mut split_power, mut split_bound) = (Rat::zero(), Rat::zero());
            if lattice.is_some() {
                // E(u′, w′) − E(û′, ŵ′) + (hG/4)(|a′|² − |â′|²), each within its cells.
                let conductance = contact.conductance();
                let (storage_form, stiffness_form, _) = contact.forms();
                split_power = contact.energy(&next_displacement, &next_rate)?
                    - contact.energy(&passed.displacement, &passed.rate)?;
                let stored = storage_form.apply(&add(&next_rate, &passed.rate))?;
                let stiffened =
                    stiffness_form.apply(&add(&next_displacement, &passed.displacement))?;
                split_bound = &unit * (l1(&stored) + l1(&stiffened)) / integer(2);
                for (carried_wave, image) in [
                    (&arrive_from, &passed.arrive_from),
                    (&arrive_to, &passed.arrive_to),
                ] {
                    let (power, cell) = split_energy(carried_wave, image, &unit);
                    split_power += &quarter * conductance * power;
                    split_bound += &quarter * conductance * cell;
                }
            }
            // The break's receipt for the whole contact's parting, where its law is declared.
            let parting = match &operands.surfaces()[a] {
                Some(density) => {
                    let nodes: Vec<usize> = (0..contact.width() / 2).collect();
                    Some(BreakReceipt::read(
                        contact,
                        &h,
                        [displacement, rate],
                        [&next_displacement, &next_rate],
                        &passed,
                        &nodes,
                        density,
                    )?)
                }
                None => None,
            };
            Ok::<_, HnnError>(Passed {
                parting,
                arrivals: [arrive_from, arrive_to],
                states: [next_displacement, next_rate],
                remainders: (
                    [from_remainder, to_remainder],
                    [displacement_remainder, rate_remainder],
                    solve_remainder,
                ),
                midpoint: passed.midpoint,
                dissipation: passed.dissipation,
                chart: chart_term,
                split: split_power,
                bound: chart_bound + split_bound,
            })
        })?;
        let mut rates = Vec::with_capacity(transits.len());
        let mut partings = Vec::with_capacity(transits.len());
        for (a, passed) in transits.into_iter().enumerate() {
            partings.push(passed.parting.clone());
            dissipation += &passed.dissipation;
            transit_chart += passed.chart;
            transit_split += passed.split;
            bound += passed.bound;
            self.arrivals[a] = passed.arrivals;
            self.states[a] = passed.states;
            let (arrivals, states, solve) = passed.remainders;
            self.carried.arrivals[a] = arrivals;
            self.carried.states[a] = states;
            self.carried.solves[a] = solve;
            rates.push(passed.midpoint);
        }
        if let Some(record) = self.passage.last_mut() {
            record.midpoints = midpoints;
            record.rates = rates;
        }
        let residual =
            &junction_defect + &element_chart + &element_split + &transit_chart + &transit_split;
        let balance = TickBalance {
            before,
            after: self.power()?,
            dissipation,
            resist,
            contrast,
            loaded_port: loaded_port.clone(),
            loaded_split: loaded_split.clone(),
            residual,
            bound,
        };
        let [
            resonator_before,
            resonator_after,
            pump,
            port,
            resonator_dissipation,
            resonator_integration,
            resonator_chart,
            resonator_split,
            resonator_bound,
        ] = resonance_terms;
        self.fields.push(FieldBalance {
            before: balance.before.clone(),
            after: balance.after.clone(),
            dissipation: balance.dissipation.clone(),
            resist: balance.resist.clone(),
            contrast: balance.contrast.clone(),
            junction: junction_defect,
            element_chart,
            element_split,
            transit_chart,
            transit_split,
            resonator_before,
            resonator_after,
            pump,
            loaded_port: loaded_port.clone(),
            loaded_split: loaded_split.clone(),
            interconnection: &port + &loaded_port,
            port,
            resonator_dissipation,
            resonator_integration,
            resonator_chart,
            resonator_split,
            bound: balance.bound.clone(),
            resonator_bound,
        });
        self.partings.push(partings);
        self.peak_bits = self.peak_bits.max(self.state_bits());
        self.settled = Some(balance.after.clone());
        self.balances.push(balance.clone());
        work::reached(work::Event::FullTick);
        Ok(balance)
    }

    /// **Every full tick's break receipts**, per contact where its break law is declared
    /// (`hnn::contact::BreakReceipt`, Lean `HNN/ContactBreak`): the whole contact's parting read at
    /// each transit.
    pub fn partings(&self) -> &[Vec<Option<BreakReceipt>>] {
        &self.partings
    }

    /// **Every full tick's field balance**, every term stated (Lean
    /// `HNN/Word.field_executed_balance_with_defects`).
    pub fn field_balances(&self) -> &[FieldBalance] {
        &self.fields
    }

    /// Each ring's resonator inside the word, where one is declared.
    pub fn resonances(&self) -> &[Option<Resonance>] {
        &self.resonators
    }

    /// The loaded port's two nested wave-chart remainders, used by its smallest law fixture.
    #[cfg(test)]
    pub(crate) fn loaded_wave_remainders(&self, ring: usize) -> Option<(&[Rat], &[Rat])> {
        self.resonators.get(ring)?.as_ref()?;
        Some((
            &self.carried.element_drive[ring],
            &self.carried.storage[ring],
        ))
    }

    /// **The whole word's balance**, read at any point of the word: [`WordBalance::of`] its release.
    #[cfg(test)]
    pub(crate) fn word_balance(&self) -> Result<WordBalance, HnnError> {
        Ok(WordBalance::of(&self.released()?))
    }

    /// **The last junction step**: the junctions run and are read, and the word ends there. The
    /// change is then the junctions' outgoing and storage waves with the contact states; the
    /// junction is a `W`-isometry about the participation mean, so its power moves only by the
    /// executed anchor's residual ([`Released::last`]).
    pub fn last_junction(&mut self) -> Result<(), HnnError> {
        self.settled = None;
        let (junctions, residual, bound) = self.junctions()?;
        for (ring, junction) in junctions.iter().enumerate() {
            self.storage[ring] = junction.storage_wave.clone();
            for (position, &a) in self.operands.incident(ring).iter().enumerate() {
                let slot = self.operands.end_slot(a, ring);
                self.arrivals[a][slot] = junction.outgoing[position].clone();
            }
        }
        self.last = residual;
        self.last_bound = bound;
        self.ended = true;
        Ok(())
    }

    /// **The forward word over one epoch the receiver reads**: `e_max − 1` full ticks and the last
    /// junction, returning the receiving ring's anchors `v_R(e_j)` at the ring's own epochs
    /// `e_0 … e_last`, its ticks, which that one coarser epoch merges. A word runs through those
    /// cells once, from its open.
    pub fn forward(&mut self, phases: &ReceivingPhases) -> Result<Vec<Vec<Rat>>, HnnError> {
        if !self.passage.is_empty() {
            return Err(HnnError::WordEnded {
                ticks: self.passage.len(),
            });
        }
        let steps = phases.junction_steps();
        for _ in 1..steps {
            self.tick()?;
        }
        self.last_junction()?;
        phases
            .epochs()
            .map(|epoch| {
                self.anchor(epoch, phases.ring())
                    .map(<[Rat]>::to_vec)
                    .ok_or(HnnError::WordEnded {
                        ticks: self.passage.len(),
                    })
            })
            .collect()
    }

    /// **Release the change** at the word's end: its power leaves as the word's emitted exchange,
    /// every carried remainder is released with it, and the word, its waves and its per-tick record
    /// are dropped.
    pub fn release(self) -> Result<Released, HnnError> {
        self.released()
    }

    /// **The release read at the word's end, the word kept**: what [`Word::release`] returns,
    /// read without dropping the word, so that the refine that read it can keep the word for its
    /// own return ([`Word::keep`]).
    pub(crate) fn released(&self) -> Result<Released, HnnError> {
        Ok(Released {
            power: self.power()?,
            ticks: self.passage.len(),
            peak_bits: self.peak_bits,
            balances: self.balances.clone(),
            last: self.last.clone(),
            last_bound: self.last_bound.clone(),
            end: self.end_change(),
            remainders: self.carried.released(),
            charts: self.operands.charts(),
            resonators: self
                .resonators
                .iter()
                .enumerate()
                .filter_map(|(ring, resonance)| {
                    resonance
                        .as_ref()
                        .map(|resonance| ResonatorBalance::of(ring, resonance))
                })
                .collect(),
        })
    }

    /// **Keep the word for its return**: the word without the borrow of its field
    /// (`KeptWord`).
    pub(crate) fn keep(self) -> KeptWord {
        let Word {
            native_source: _,
            field: _,
            operands,
            clock,
            storage,
            arrivals,
            states,
            carried,
            passage,
            balances,
            ended,
            peak_bits,
            last,
            last_bound,
            settled,
            resonators,
            fields,
            partings,
            opened_at,
        } = self;
        KeptWord {
            operands,
            clock,
            storage,
            arrivals,
            states,
            carried,
            passage,
            balances,
            ended,
            peak_bits,
            last,
            last_bound,
            settled,
            resonators,
            fields,
            partings,
            opened_at,
        }
    }
}

impl EndChange {
    /// [definition; October 4, the reception carry §8] **The rings this change occupies**: a ring
    /// whose storage wave or resonator state is nonzero, the end a nonzero arriving wave arrives at,
    /// and both ends of a contact whose state is nonzero. A word opened on this change can move at
    /// tick 0 exactly there and at the sources, which seeds its diamond
    /// ([`crate::hnn::retention::Diamond::opened`]); the rest change occupies none.
    pub fn support(&self, field: &Field) -> Vec<usize> {
        let nonzero = |wave: &[Rat]| wave.iter().any(|x| !x.is_zero());
        let mut rings = BTreeSet::new();
        for (ring, wave) in self.storage.iter().enumerate() {
            if nonzero(wave) {
                rings.insert(ring);
            }
        }
        for (ring, state) in self.resonators.iter().enumerate() {
            if state
                .as_ref()
                .is_some_and(|[u, w]| nonzero(u) || nonzero(w))
            {
                rings.insert(ring);
            }
        }
        for (a, contact) in field.contacts().iter().enumerate() {
            let (from, to) = contact.ends();
            let [at_from, at_to] = &self.arrivals[a];
            let [u, w] = &self.states[a];
            if nonzero(at_from) || nonzero(u) || nonzero(w) {
                rings.insert(from);
            }
            if nonzero(at_to) || nonzero(u) || nonzero(w) {
                rings.insert(to);
            }
        }
        rings.into_iter().collect()
    }

    /// **The rest change** of a field at its operands: every storage wave, arriving wave and
    /// contact state zero, and each declared resonator at rest at phase 0; the change a word opened
    /// at rest carries (Lean `HNN/Retention.word_opens_at_zero`).
    pub fn rest(field: &Field, operands: &Operands) -> Self {
        let widths: Vec<usize> = field.rings().iter().map(|ring| ring.width()).collect();
        Self {
            storage: widths.iter().map(|n| zeros(*n)).collect(),
            arrivals: field
                .contacts()
                .iter()
                .map(|contact| {
                    let (from, to) = contact.ends();
                    [zeros(widths[from]), zeros(widths[to])]
                })
                .collect(),
            states: field
                .contacts()
                .iter()
                .map(|contact| [zeros(contact.width()), zeros(contact.width())])
                .collect(),
            resonators: operands
                .resonators()
                .iter()
                .map(|resonator| {
                    resonator
                        .as_ref()
                        .map(|r| [zeros(r.width()), zeros(r.width())])
                })
                .collect(),
            resonator_phases: operands
                .resonators()
                .iter()
                .map(|resonator| resonator.as_ref().map(|_| 0))
                .collect(),
        }
    }
}

/// `Y_r + Σ_a G_a`: the junction's admittance sum.
fn admittance_total(operands: &Operands, ring: usize) -> Rat {
    operands
        .incident(ring)
        .iter()
        .fold(operands.rings()[ring].admittance().clone(), |sum, &a| {
            sum + operands.contacts()[a].conductance()
        })
}

/// [definition; agent-inferred] **A word kept for its own return**: every part of a word but the
/// borrow of its field, so that the resident that owns the field can hold it (design R2 H2: the
/// word keeps its per-tick waves for its return to read in reverse, and they are dropped with it).
/// The reference's pending slot keeps one from its refine's read, tagged with the commit it was
/// read at, for the compare at that commit ([`crate::hnn::reference`], "The kept read"); it
/// resumes onto the same field only to be consumed by [`Word::pull_back`] (guard 2: no word
/// outlives its return). It is not `Clone`: a clone of the slot drops it and reads again.
#[derive(Debug)]
pub(crate) struct KeptWord {
    operands: Operands,
    clock: Clock,
    storage: Vec<Vec<Rat>>,
    arrivals: Vec<[Vec<Rat>; 2]>,
    states: Vec<[Vec<Rat>; 2]>,
    carried: Carried,
    passage: Vec<Passage>,
    balances: Vec<TickBalance>,
    ended: bool,
    peak_bits: u64,
    last: Rat,
    last_bound: Rat,
    settled: Option<Rat>,
    resonators: Vec<Option<Resonance>>,
    fields: Vec<FieldBalance>,
    partings: Vec<Vec<Option<BreakReceipt>>>,
    opened_at: usize,
}

impl KeptWord {
    /// The kept word's anchor at a junction step on a ring (read-only; [`Word::anchor`]'s).
    pub(crate) fn anchor(&self, step: usize, ring: usize) -> Option<&[Rat]> {
        self.passage
            .get(step)
            .and_then(|record| record.anchors.get(ring))
            .map(Vec::as_slice)
    }

    /// **Resume the word on its field**: the field it was read on, which the resident owns.
    pub(crate) fn resume(self, field: &Field) -> Word<'_> {
        let KeptWord {
            operands,
            clock,
            storage,
            arrivals,
            states,
            carried,
            passage,
            balances,
            ended,
            peak_bits,
            last,
            last_bound,
            settled,
            resonators,
            fields,
            partings,
            opened_at,
        } = self;
        Word {
            native_source: None,
            field,
            operands,
            clock,
            storage,
            arrivals,
            states,
            carried,
            passage,
            balances,
            ended,
            peak_bits,
            last,
            last_bound,
            settled,
            resonators,
            fields,
            partings,
            opened_at,
        }
    }
}

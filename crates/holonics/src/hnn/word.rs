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
//!   nothing is carried to the next word ([`Word::release`] consumes it).
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

use num_traits::{Signed, Zero};

use crate::hnn::HnnError;
use crate::hnn::chart::{ChartReading, Charts, Remainders, carry};
use crate::hnn::constitution::Lattice;
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
}

/// [definition] **A resonator inside a word**: its state `[u, w]`, its carried remainders, and its
/// executed ticks in order.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Resonance {
    pub state: [Vec<Rat>; 2],
    pub remainders: ResonatorRemainders,
    pub steps: Vec<ResonatorStep>,
}

/// [definition] **A resonator's balance over one word** (campaign 2, `hnn::ring`; Lean
/// `HNN/Ring.ring_tick_executed_energy_balance` summed over the word's ticks): its ring, its ticks,
/// its storage at the word's end (it opens at zero with the word), its pump, port and dissipation
/// work, its chart defect and its split summed over the ticks with their certified bound
/// ([`crate::hnn::ring::ResonatorStep::bound`] summed), and the remainders its end releases. It is
/// what the word's release returns of a resonator, so every realization of the port reads it alike
/// ([`Released::resonators`]).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ResonatorBalance {
    pub ring: usize,
    pub ticks: usize,
    pub end: Rat,
    pub pump: Rat,
    pub port: Rat,
    pub dissipation: Rat,
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
            end: resonance
                .steps
                .last()
                .map_or_else(Rat::zero, |step| step.after.clone()),
            pump: sum(|step| &step.pump),
            port: sum(|step| &step.port),
            dissipation: sum(|step| &step.dissipation),
            chart: sum(|step| &step.chart),
            split: sum(|step| &step.split),
            bound: sum(|step| &step.bound),
            released: Remainders::of(resonance.remainders.all()),
        }
    }

    /// **It closes**: `E_end = pump + port − dissipation + chart + split`, from zero at the open,
    /// with `|chart + split| ≤ bound`.
    pub fn closes(&self) -> bool {
        self.end == &self.pump + &self.port - &self.dissipation + &self.chart + &self.split
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
                + &self.resonator_chart
                + &self.resonator_split
                + &self.interconnection
            && executed.abs() <= &self.bound + &self.resonator_bound
    }
}

/// [definition] **A word's end change** (`x`, the change the word releases and its commit reads):
/// the storage waves per ring, the arriving waves per contact (`[at from, at to]`) and the contact
/// states `[u, w]`, as the last junction step left them.
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
        constitution: &impl ConstitutionRead,
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

    /// The declared resonator energy at the end state, measured with this constitution.
    fn resonator_power(&self, change: &EndChange) -> Result<Rat, HnnError> {
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
                    let (old_c, _, _) = old.forms();
                    let (new_c, _, _) = new.forms();
                    let old_k = old.pumped_stiffness(phase)?;
                    let new_k = new.pumped_stiffness(phase)?;
                    let dc = new_c.subtract(old_c)?;
                    let dk = new_k.subtract(&old_k)?;
                    stored += (dot(&state[1], &dc.apply(&state[1])?)
                        + dot(&state[0], &dk.apply(&state[0])?))
                        / integer(2);
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

/// [definition] **The commit a word's balance is carried across** (Lean
/// `HNN/Word.field_commit_deposition`): the deposition work `½⟨x, ΔΘ x⟩` on the word's end change,
/// formed from the operand differences, and the end change's power under the committed
/// constitution, formed from the committed operands alone.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CommitWork {
    pub deposition: Rat,
    pub committed: Rat,
}

/// [definition] **The whole word's balance** (campaign 2's committed balance over one word, formed
/// from its release on every realization of the port, [`WordBalance::of`]): the field's power at the
/// open (after the opening split) and at the end, every tick's stated terms summed, the defects
/// (the ticks' residuals) and the last junction's residual with their certified bound, the
/// resonators' storage at the end with their terms (they open at zero), the signed port pairing,
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
    pub resonator_end: Rat,
    pub pump: Rat,
    pub port: Rat,
    pub resonator_dissipation: Rat,
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
            resonator_end: resonators(|r| &r.end),
            pump: resonators(|r| &r.pump),
            interconnection: &port + loaded_port,
            loaded_split,
            port,
            resonator_dissipation: resonators(|r| &r.dissipation),
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

    /// **Carry the balance across the commit** from the form `before` to `after` (both read at the
    /// word's cut, before and after the deposit): the deposition work `½⟨x, ΔΘ x⟩` from the forms'
    /// differences and the end change's power under the committed form alone.
    pub fn commit(&mut self, before: &PowerForm, after: &PowerForm) -> Result<(), HnnError> {
        // Every fallible reading first: a refusal leaves the balance as it was.
        let deposition = before.deposition_work(after, &self.change)?;
        let committed = after.power(&self.change)?;
        let resonator_end = after.resonator_power(&self.change)?;
        self.resonator_end = resonator_end;
        self.commit = Some(CommitWork {
            deposition,
            committed,
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
    /// `P_end + E_end = P_open − dissipation + resist + Π_c +
    /// defects + last + pump − resonator dissipation + resonator chart + resonator split +
    /// interconnection`, with `P_end` the committed power and `deposition` added when a commit
    /// follows; and the executed residual, the resonators' chart and split included, lies within
    /// its certified bound.
    pub fn closes(&self) -> bool {
        let terms = &self.open - &self.dissipation
            + &self.resist
            + &self.contrast
            + self.residual()
            + &self.pump
            - &self.resonator_dissipation
            + &self.interconnection;
        let identity = match &self.commit {
            Some(commit) => &commit.committed + &self.resonator_end == terms + &commit.deposition,
            None => &self.end + &self.resonator_end == terms,
        };
        identity && self.residual().abs() <= self.bound
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
        if storage.len() != field.rings().len() {
            return Err(HnnError::Shape {
                what: "open storage",
                expected: field.rings().len(),
                found: storage.len(),
            });
        }
        for (ring, wave) in field.rings().iter().zip(&storage) {
            if wave.len() != ring.width() {
                return Err(HnnError::Shape {
                    what: "ring storage wave",
                    expected: ring.width(),
                    found: wave.len(),
                });
            }
        }
        let widths: Vec<usize> = field.rings().iter().map(|ring| ring.width()).collect();
        let arrivals: Vec<[Vec<Rat>; 2]> = field
            .contacts()
            .iter()
            .map(|contact| {
                let (from, to) = contact.ends();
                [zeros(widths[from]), zeros(widths[to])]
            })
            .collect();
        let states: Vec<[Vec<Rat>; 2]> = field
            .contacts()
            .iter()
            .map(|contact| [zeros(contact.width()), zeros(contact.width())])
            .collect();
        let lattice = operands.lattice().map(|word| word.transient());
        let mut carried = Carried {
            anchors: widths.iter().map(|n| zeros(*n)).collect(),
            storage: Vec::with_capacity(widths.len()),
            element_drive: widths.iter().map(|n| zeros(*n)).collect(),
            solves: field
                .contacts()
                .iter()
                .map(|contact| zeros(contact.width()))
                .collect(),
            arrivals: arrivals.clone(),
            states: states.clone(),
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
        let resonators = operands
            .resonators()
            .iter()
            .map(|resonator| {
                resonator.as_ref().map(|resonator| {
                    let n = resonator.width();
                    Resonance {
                        state: [zeros(n), zeros(n)],
                        remainders: ResonatorRemainders::default(),
                        steps: Vec::new(),
                    }
                })
            })
            .collect();
        let mut word = Self {
            field,
            operands,
            clock: Clock::unwound(field.step().clone())?,
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
        };
        word.peak_bits = word.state_bits();
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
    pub fn contact_support(&self) -> Vec<bool> {
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
        let tick = self.passage.len() - 1;
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
        let mut resonance_terms: [Rat; 8] = std::array::from_fn(|_| Rat::zero());
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
            resonator_chart,
            resonator_split,
            bound: balance.bound.clone(),
            resonator_bound,
        });
        self.partings.push(partings);
        self.peak_bits = self.peak_bits.max(self.state_bits());
        self.settled = Some(balance.after.clone());
        self.balances.push(balance.clone());
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

    /// The driven wave at junction step `step`: the element output `e` when a loaded resonator is
    /// declared, otherwise the junction's storage wave `b = 2v−s`. `None` past the steps taken.
    pub fn storage_waves(&self, step: usize) -> Option<Vec<Vec<Rat>>> {
        let record = self.passage.get(step)?;
        Some(
            record
                .anchors
                .iter()
                .zip(&record.storage)
                .enumerate()
                .map(|(ring, (anchor, storage))| {
                    self.resonators[ring]
                        .as_ref()
                        .and_then(|resonance| resonance.steps.get(step))
                        .map_or_else(
                            || crate::geometry::swing::half_turn(anchor, storage),
                            |resonance| resonance.drive.clone(),
                        )
                })
                .collect(),
        )
    }

    /// **The whole word's balance**, read at any point of the word: [`WordBalance::of`] its release.
    pub fn word_balance(&self) -> Result<WordBalance, HnnError> {
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

    /// **The forward word for one receiving window**: `e_max − 1` full ticks and the last junction,
    /// returning the receiving ring's anchors `v_R(e_j)` at its epochs `e_0 … e_last`. A word runs
    /// its window once, from its open.
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
            end: EndChange {
                storage: self.storage.clone(),
                arrivals: self.arrivals.clone(),
                states: self.states.clone(),
                resonators: self
                    .resonators
                    .iter()
                    .map(|resonance| resonance.as_ref().map(|r| r.state.clone()))
                    .collect(),
                // The last executed tick's phase; with no full tick, phase 0, where the open
                // state is read (`EndChange::resonator_phases`).
                resonator_phases: self
                    .resonators
                    .iter()
                    .map(|resonance| {
                        resonance
                            .as_ref()
                            .map(|r| r.steps.last().map_or(0, |step| step.phase))
                    })
                    .collect(),
            },
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
}

impl KeptWord {
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
        } = self;
        Word {
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
        }
    }
}

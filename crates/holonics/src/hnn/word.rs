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
//! [definition] **The carried transients** (Decision 24; Lean `HNN/LatticeWord.{feedback_tick,
//! carried_word_accounting}`). On the field's declared lattices ([`crate::hnn::chart`]) the word
//! carries every transient on `2^(−L_w)ℤ` with error feedback: the opening storage, and at each tick
//! the junction's anchor `v_r`, the element's next storage `s_r′`, the contact's solved `ζ_a`, its
//! state `(u_a, w_a)` and the arriving waves. Each is the exact image of the carried values under the
//! executed tick plus its carried remainder, split at the nearest lattice point, ties upward
//! ([`crate::hnn::chart::carry`]); `Σ_t x_t + r_T = Σ_t y_t` entry by entry, and the word releases
//! the remainders `r_T` at its end ([`Released::remainders`]). Every product with a chart runs on
//! the carried values' integer coordinates. Under the exact law nothing is split and every
//! remainder stays zero.
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
use crate::hnn::field::{ConstitutionRead, Current, Field};
use crate::hnn::moment::SourceMoment;
use crate::hnn::propagation::{
    Junction, Operands, TickBalance, element_step, global_power, participation, swing_about,
    transit_defect, transit_solve, transit_update,
};
use crate::hnn::realization::indexed;
use crate::hnn::receiving::ReceivingPhases;
use crate::navigator::Clock;
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
    storage: Vec<Vec<Rat>>,
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
    /// The power of the change as the last full tick left it: the next tick's `before`, read once.
    /// Only `tick` sets it and `last_junction` clears it, so it is always the current change's.
    settled: Option<Rat>,
}

/// [definition] **What a word's end releases**: the power of the unread change, which leaves as
/// the word's emitted exchange; the junction steps taken; the peak exact bits of any entry of the
/// change inside the word; every tick's balance; the last junction's residual; every carried
/// remainder, released and read ([`Remainders`]); and every chart's reading (its certificate
/// against the target, its refinement's steps and seed).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Released {
    pub power: Rat,
    pub ticks: usize,
    pub peak_bits: u64,
    pub balances: Vec<TickBalance>,
    pub last: Rat,
    pub remainders: Remainders,
    pub charts: Vec<ChartReading>,
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
    midpoint: Vec<Rat>,
    resist: Rat,
    drive: Rat,
    residual: Rat,
    bound: Rat,
}

/// One contact's transit at a tick: the carried arrivals, state and solve with their remainders,
/// the midpoint rate, the dissipation and its residual terms with the bound.
struct Passed {
    arrivals: [Vec<Rat>; 2],
    states: [Vec<Rat>; 2],
    remainders: ([Vec<Rat>; 2], [Vec<Rat>; 2], Vec<Rat>),
    midpoint: Vec<Rat>,
    dissipation: Rat,
    residual: Rat,
    bound: Rat,
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
            solves: field
                .contacts()
                .iter()
                .map(|contact| zeros(contact.width()))
                .collect(),
            arrivals: arrivals.clone(),
            states: states.clone(),
        };
        let storage: Vec<Vec<Rat>> = storage
            .into_iter()
            .map(|wave| {
                let (opened, remainder) = split(lattice.as_ref(), wave.clone(), &zeros(wave.len()));
                carried.storage.push(remainder);
                opened
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
            settled: None,
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

    fn state_bits(&self) -> u64 {
        let bits = |x: &Rat| x.numer().bits() + x.denom().bits();
        self.storage
            .iter()
            .flatten()
            .chain(self.arrivals.iter().flatten().flatten())
            .chain(self.states.iter().flatten().flatten())
            .map(bits)
            .max()
            .unwrap_or(0)
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
                junction: swing_about(anchor, &storage[ring], &incoming),
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
        let (junctions, mut residual, mut bound) = self.junctions()?;
        let lattice = self.transient();
        let unit = lattice.as_ref().map_or_else(Rat::zero, Lattice::unit);
        let h = self.operands.step().clone();
        let half = &h / integer(2);
        let quarter = &h / integer(4);
        let (mut resist, mut contrast, mut dissipation) = (Rat::zero(), Rat::zero(), Rat::zero());
        // Every element reads only its own junction and storage remainder: the rings run together,
        // and their balance terms are summed afterwards in ring order.
        let (operands, remainders) = (&self.operands, &self.carried.storage);
        let steps = indexed(junctions.len(), |ring| {
            let step = element_step(
                &operands.rings()[ring],
                &junctions[ring].storage_wave,
                &junctions[ring].contrast,
            )?;
            let (next, remainder) = split(lattice.as_ref(), step.next.clone(), &remainders[ring]);
            let admittance = operands.rings()[ring].admittance();
            let (split_power, split_bound) = split_energy(&next, &step.next, &unit);
            Ok::<_, HnnError>(Stepped {
                remainder,
                midpoint: step.midpoint,
                resist: &half * admittance * &step.resist,
                drive: &half * admittance * &step.drive,
                residual: &half * admittance * &step.defect + &quarter * admittance * &split_power,
                bound: &half * admittance * &step.bound + &quarter * admittance * &split_bound,
                next,
            })
        })?;
        let mut midpoints = Vec::with_capacity(steps.len());
        for (ring, step) in steps.into_iter().enumerate() {
            resist += step.resist;
            contrast += step.drive;
            residual += step.residual;
            bound += step.bound;
            self.storage[ring] = step.next;
            self.carried.storage[ring] = step.remainder;
            midpoints.push(step.midpoint);
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
            Ok::<_, HnnError>(Passed {
                arrivals: [arrive_from, arrive_to],
                states: [next_displacement, next_rate],
                remainders: (
                    [from_remainder, to_remainder],
                    [displacement_remainder, rate_remainder],
                    solve_remainder,
                ),
                midpoint: passed.midpoint,
                dissipation: passed.dissipation,
                residual: chart_term + split_power,
                bound: chart_bound + split_bound,
            })
        })?;
        let mut rates = Vec::with_capacity(transits.len());
        for (a, passed) in transits.into_iter().enumerate() {
            dissipation += &passed.dissipation;
            residual += passed.residual;
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
        let balance = TickBalance {
            before,
            after: self.power()?,
            dissipation,
            resist,
            contrast,
            residual,
            bound,
        };
        self.peak_bits = self.peak_bits.max(self.state_bits());
        self.settled = Some(balance.after.clone());
        self.balances.push(balance.clone());
        Ok(balance)
    }

    /// **The last junction step**: the junctions run and are read, and the word ends there. The
    /// change is then the junctions' outgoing and storage waves with the contact states; the
    /// junction is a `W`-isometry about the participation mean, so its power moves only by the
    /// executed anchor's residual ([`Released::last`]).
    pub fn last_junction(&mut self) -> Result<(), HnnError> {
        self.settled = None;
        let (junctions, residual, _) = self.junctions()?;
        for (ring, junction) in junctions.iter().enumerate() {
            self.storage[ring] = junction.storage_wave.clone();
            for (position, &a) in self.operands.incident(ring).iter().enumerate() {
                let slot = self.operands.end_slot(a, ring);
                self.arrivals[a][slot] = junction.outgoing[position].clone();
            }
        }
        self.last = residual;
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
            remainders: self.carried.released(),
            charts: self.operands.charts(),
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
            settled,
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
            settled,
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
    settled: Option<Rat>,
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
            settled,
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
            settled,
        }
    }
}

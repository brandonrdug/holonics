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
//!   operand fixed; each tick's global power balance is recorded and closes exactly;
//! - **the receiving epochs**: `e_j = e_0 + j`, `j < A`, each read by tick `e_j`'s junction; the word
//!   evaluates `e_max = e_0 + A` junction steps, and the last stops after its junction;
//! - **release**: at the word's end every wave and contact state is released as the word's emitted
//!   exchange, with its power; nothing is carried to the next word ([`Word::release`] consumes it).
//!
//! [definition] The word keeps its own per-tick waves, bounded by its `e_max` junction steps, for
//! its return to read in reverse; that memory lives only in the word and is dropped with it
//! (design R2 H2). It is one evaluation on one moment, not an occurrence tape. A refine keeps its
//! word, without the borrow of its field (`KeptWord`), for the compare at the same commit, whose
//! return consumes it.
//!
//! [definition; agent-inferred] **Within a step the rings, then the contacts, run together** (the
//! hardware law; `hnn::realization`): every junction reads only its own storage and
//! arrivals, every element only its own junction, and every transit only its two ends' outgoing
//! waves and its own state, and each writes only its own slot; the balance terms are summed after,
//! in ring and contact order.
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

use num_traits::Zero;

use crate::hnn::HnnError;
use crate::hnn::field::{ConstitutionRead, Current, Field};
use crate::hnn::moment::SourceMoment;
use crate::hnn::propagation::{
    Operands, TickBalance, element_step, global_power, junction_swing, transit,
};
use crate::hnn::realization::indexed;
use crate::hnn::receiving::ReceivingPhases;
use crate::navigator::Clock;
use crate::ratio::{Rat, integer};

/// One junction step's record: the change at the step's start and every ring's anchor. The word's
/// return reads these in reverse.
#[derive(Clone, Debug, PartialEq, Eq)]
struct Passage {
    storage: Vec<Vec<Rat>>,
    arrivals: Vec<[Vec<Rat>; 2]>,
    states: Vec<[Vec<Rat>; 2]>,
    anchors: Vec<Vec<Rat>>,
}

/// [definition] **A word** over a borrowed field. It owns its operands, its hop clock and the
/// change: the storage waves, the arriving waves, the contact states and their per-tick values.
#[derive(Debug)]
pub struct Word<'c> {
    field: &'c Field,
    operands: Operands,
    clock: Clock,
    storage: Vec<Vec<Rat>>,
    arrivals: Vec<[Vec<Rat>; 2]>,
    states: Vec<[Vec<Rat>; 2]>,
    passage: Vec<Passage>,
    balances: Vec<TickBalance>,
    ended: bool,
    peak_bits: u64,
    /// The power of the change as the last full tick left it: the next tick's `before`, read once.
    /// Only `tick` sets it and `last_junction` clears it, so it is always the current change's.
    settled: Option<Rat>,
}

/// [definition] **What a word's end releases**: the power of the unread change, which leaves as
/// the word's emitted exchange; the junction steps taken; the peak exact bits of any entry of the
/// change inside the word; and every tick's balance.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Released {
    pub power: Rat,
    pub ticks: usize,
    pub peak_bits: u64,
    pub balances: Vec<TickBalance>,
}

impl<'c> Word<'c> {
    /// **Open a word at the cut** on the moment: zero change, with `s_g(0) = P_g^(τ_g) m̃_g` on the
    /// source rings.
    pub fn open(
        field: &'c Field,
        constitution: &impl ConstitutionRead,
        current: &Current,
        moment: &SourceMoment,
    ) -> Result<Self, HnnError> {
        let storage = moment.open_storage(field, constitution, current)?;
        Self::open_on(field, constitution, current, storage)
    }

    /// Open a word on a declared storage injection (every wave and contact state still zero): the
    /// impulse of the cone test and the basis of the observability rank.
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

    /// Open a word on operands already read at the cut.
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
        let arrivals = field
            .contacts()
            .iter()
            .map(|contact| {
                let (from, to) = contact.ends();
                [
                    vec![Rat::zero(); field.ring(from).width()],
                    vec![Rat::zero(); field.ring(to).width()],
                ]
            })
            .collect();
        let states = field
            .contacts()
            .iter()
            .map(|contact| {
                [
                    vec![Rat::zero(); contact.width()],
                    vec![Rat::zero(); contact.width()],
                ]
            })
            .collect();
        let mut word = Self {
            field,
            operands,
            clock: Clock::unwound(field.step().clone())?,
            storage,
            arrivals,
            states,
            passage: Vec::new(),
            balances: Vec::new(),
            ended: false,
            peak_bits: 0,
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

    /// The anchor `v_r` read by junction step `step`, when it has run.
    pub fn anchor(&self, step: usize, ring: usize) -> Option<&[Rat]> {
        self.passage
            .get(step)
            .and_then(|record| record.anchors.get(ring))
            .map(Vec::as_slice)
    }

    /// The change at the start of each junction step, in order: the storage waves, the arriving
    /// waves and the contact states the word's return reads in reverse (design R2 H2). They live
    /// only in the word.
    pub(crate) fn recorded(
        &self,
    ) -> impl Iterator<Item = (&[Vec<Rat>], &[[Vec<Rat>; 2]], &[[Vec<Rat>; 2]])> {
        self.passage.iter().map(|record| {
            (
                record.storage.as_slice(),
                record.arrivals.as_slice(),
                record.states.as_slice(),
            )
        })
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

    /// Every ring's junction at this step, recorded.
    fn junctions(&mut self) -> Result<Vec<crate::hnn::propagation::Junction>, HnnError> {
        if self.ended {
            return Err(HnnError::WordEnded {
                ticks: self.passage.len(),
            });
        }
        // Every junction reads only its own storage and arrivals: the rings run together.
        let (operands, storage, arrivals) = (&self.operands, &self.storage, &self.arrivals);
        let junctions = indexed(operands.rings().len(), |ring| {
            let incoming: Vec<(&Rat, &[Rat])> = operands
                .incident(ring)
                .iter()
                .map(|&a| {
                    let slot = operands.end_slot(a, ring);
                    (
                        operands.contacts()[a].conductance(),
                        arrivals[a][slot].as_slice(),
                    )
                })
                .collect();
            junction_swing(
                operands.rings()[ring].admittance(),
                &storage[ring],
                &incoming,
            )
        })?;
        self.passage.push(Passage {
            storage: self.storage.clone(),
            arrivals: self.arrivals.clone(),
            states: self.states.clone(),
            anchors: junctions.iter().map(|j| j.anchor.clone()).collect(),
        });
        self.clock.advance(&1u32.into());
        Ok(junctions)
    }

    /// **One full tick**: every junction, then every ring element, then every contact transit.
    /// Returns its balance, which closes exactly (Lean `HNN/Word.word_tick_balance`).
    pub fn tick(&mut self) -> Result<TickBalance, HnnError> {
        // The previous tick's `after` is this tick's `before`: the change has not moved since.
        let before = match self.settled.take() {
            Some(power) => power,
            None => self.power()?,
        };
        let junctions = self.junctions()?;
        let h = self.operands.step().clone();
        let half = &h / integer(2);
        let (mut resist, mut contrast, mut dissipation) = (Rat::zero(), Rat::zero(), Rat::zero());
        // Every element reads only its own junction: the rings run together, and their balance
        // terms are summed afterwards in ring order.
        let operands = &self.operands;
        let steps = indexed(junctions.len(), |ring| {
            element_step(
                &operands.rings()[ring],
                &junctions[ring].storage_wave,
                &junctions[ring].contrast,
            )
        })?;
        for (ring, step) in steps.into_iter().enumerate() {
            let admittance = self.operands.rings()[ring].admittance();
            resist += &half * admittance * &step.resist;
            contrast += &half * admittance * &step.drive;
            self.storage[ring] = step.next;
        }
        // Every contact reads the outgoing waves of its two ends and its own state, and writes only
        // its own arrivals and state: the contacts run together.
        let (operands, states) = (&self.operands, &self.states);
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
            transit(
                contact,
                &h,
                outgoing(from),
                outgoing(to),
                &states[a][0],
                &states[a][1],
            )
        })?;
        for (a, passed) in transits.into_iter().enumerate() {
            dissipation += &passed.dissipation;
            self.arrivals[a] = [passed.arrive_from, passed.arrive_to];
            self.states[a] = [passed.displacement, passed.rate];
        }
        let balance = TickBalance {
            before,
            after: self.power()?,
            dissipation,
            resist,
            contrast,
        };
        self.peak_bits = self.peak_bits.max(self.state_bits());
        self.settled = Some(balance.after.clone());
        self.balances.push(balance.clone());
        Ok(balance)
    }

    /// **The last junction step**: the junctions run and are read, and the word ends there. The
    /// change is then the junctions' outgoing and storage waves with the contact states; the
    /// junction is a `W`-isometry, so its power is unchanged.
    pub fn last_junction(&mut self) -> Result<(), HnnError> {
        self.settled = None;
        let junctions = self.junctions()?;
        for (ring, junction) in junctions.iter().enumerate() {
            self.storage[ring] = junction.storage_wave.clone();
            for (position, &a) in self.operands.incident(ring).iter().enumerate() {
                let slot = self.operands.end_slot(a, ring);
                self.arrivals[a][slot] = junction.outgoing[position].clone();
            }
        }
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
    /// and the word, its waves and its per-tick record are dropped.
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
            passage,
            balances,
            ended,
            peak_bits,
            settled,
        } = self;
        KeptWord {
            operands,
            clock,
            storage,
            arrivals,
            states,
            passage,
            balances,
            ended,
            peak_bits,
            settled,
        }
    }
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
    passage: Vec<Passage>,
    balances: Vec<TickBalance>,
    ended: bool,
    peak_bits: u64,
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
            passage,
            balances,
            ended,
            peak_bits,
            settled,
        } = self;
        Word {
            field,
            operands,
            clock,
            storage,
            arrivals,
            states,
            passage,
            balances,
            ended,
            peak_bits,
            settled,
        }
    }
}

//! **Retention: the collapse onto what the admitted future distinguishes.**
//!
//! [definition] Between words only the medium `(Θ, λ)`, the open moments and the pending ratios
//! persist (design (a), "Retention"). The change is released at every word's end
//! ([`crate::hnn::Word::release`]); at an aeon boundary the constitution is reduced to what the
//! admitted future still distinguishes. Campaign 1 admits learning aeons only.
//!
//! [definition] **The time-indexed causal diamond** ([`Diamond`], R3 R1–R2). Two per-ring
//! recursions, one neighbour exchange per round, `e_last` rounds: reach `r_g = dist(𝒮, g)` and
//! observe `o_g = dist(g, R)`. An edge `x → y` of the word is used on a change that some admitted
//! reading sees exactly when `r_x + 1 + o_y ≤ e_last`, so per locus:
//!
//! | Locus | Retained exactly when |
//! |---|---|
//! | ring `g`'s element (edge `g → g`) | `r_g + 1 + o_g ≤ e_last` |
//! | ring `g`'s junction (`Y_g`) | `r_g + o_g ≤ e_last` (always at `R`) |
//! | contact `a = (g, h)`'s channel | `min(r_g, r_h) + 1 + min(o_g, o_h) ≤ e_last` |
//! | contact `a`'s conductance `G_a` | its channel or either end's junction is retained |
//! | source ports on `g ∈ 𝒮` | `o_g ≤ e_last` |
//! | the standing `q_g` | the element of `g` or of a neighbour is retained |
//! | the receiving map `R` and the receiving parametron's landmark tree | always |
//!
//! [definition; agent-inferred] **The collapse keeps the whole tree and the active address**
//! (Decision 28). The tree sits at the receiving locus beside `R`, which is never released. Lean
//! `HNN/LandmarkTree.release_rule` proves that nodes deeper than the address depth `D` are
//! releasable, of which the tree founds none, and that a retention is lawful exactly when it
//! refines the causal signature; it does not prove that no shallower merge is lawful, and the
//! collapse attempts none. The receiving parametron's active suffix address
//! (`hnn::receiving::ActiveAddress`) is resident state beside it, which the collapse does not
//! touch.
//!
//! The time-indexed window of a locus is the ticks at which its output is read within the word:
//! the element of `g` at tick `t` when `r_g ≤ t` and `t + 1 + o_g ≤ e_last`; a channel likewise with
//! the ends' minima. A deposit's statistics sum only over these windows, which is why a deposit
//! gives the same result with or without the collapse (`deposit_descends`).
//!
//! [definition] **The collapse** ([`collapse`]) runs the recursions for every admitted receiver,
//! retains the union, and releases the rest: `V = ⊕V_g`, a 0/1 projection per locus, keeping the
//! contact graph. A released locus's learned material becomes the zero map and its statistics are
//! dropped; the retained loci keep their laws and exact values; no denominator is introduced. The
//! release is computed on the loci's sparsity, so no deposit resurrects a released locus. Its
//! value kernel beyond the structural release is campaign 3's (a frozen aeon's descended tick is
//! not yet specified), and is reported as a declared absence.
//!
//! [definition; agent-inferred] **The collapse and the carried remainders.** The aeon collapse
//! releases only exact complements, and a carried remainder is not one (releasing it could move a
//! later lattice value by a unit and so a later admitted reading), so it releases no carried
//! remainder of a retained locus and resets no deposit clock. The budgeted carry
//! (`hnn::constitution`, Lean `HNN/LatticeDeposit`) releases each deposit's residual at the deposit,
//! within half a lattice unit per entry since the locus's founding
//! (`release_bounded_since_founding`). A locus `V` deletes leaves whole: its value, its remainders
//! and its clock, reported with the locus in [`Collapse::released`].
//!
//! | Lean `HNN/Retention` | Rust |
//! |---|---|
//! | `diamond_recursion`, `reachRound_le_iff`, `blind_outside_observe` | [`Diamond::of`] |
//! | `release_indistinguishable`, `Propagation.release_past_diamond` | [`collapse`] |
//! | `deposit_descends`, `windowTicks_eq_nil`, `depositData_eq_nil` | [`Diamond::element_window`], [`Diamond::channel_window`] |
//! | `release_structural` | [`collapse`] (on sparsity) |
//! | `admitted_nonincreasing`, `admitted_growth_reads_released` | [`contained`] |
//! | `local_retention_blocks`, `constitution_descends` | [`Constitution::release`](crate::hnn::Constitution) |
//! | `HNN/LatticeDeposit.lattice_deposit_descends` (the budgeted carry, `carry_zero`) | [`collapse`] |
//! | `lift_reading`; `Aeon/Clock/Winding.{reading_navigatorClock, torus_cycle_reads_whole_windings}`, `Aeon/Clock/Epoch.signed_count_is_flux` | [`aeon_readings`], [`AeonBoundary`] |
//! | `Aeon/Production/FirstLaw.{ledger_telescopes, enclosed_telescopes}` | [`AeonBoundary::first_law`] through [`crate::aeon::EnclosedLedger`] |
//!
//! [definition] **What the Lean covers.** `release_indistinguishable`, `release_past_diamond`,
//! `deposit_descends`, `release_structural` and `admitted_nonincreasing` are proved for an abstract
//! time-invariant sparse linear block operator (`HNN/Propagation`'s `BlockOp`), not yet for the
//! concrete tick `HNN/Word.fieldTick`, which has its balance, locality and cone
//! (`fieldTick_balance`, `fieldTick_local`, `word_tick_cone`). The bridge (`fieldTick` linear in
//! the change at fixed operands, as a `BlockOp` on rings and contacts with `blockAdj` sparsity) is
//! owed in #62, "Step 4 (#73) owed: the diamond on the concrete tick". The Rust tests check these
//! laws on the concrete word (`tests/retention.rs`).

use std::collections::BTreeSet;

use num_bigint::BigInt;

use crate::aeon::{
    Aeon, AeonError, ClockLift, Cycle, EnclosedBalance, LiteralComparison, Reading, TorusClock,
    epochs, reading,
};
use crate::hnn::HnnError;
use crate::hnn::constitution::{Carrier, Constitution, Locus};
use crate::hnn::field::Field;
use crate::hnn::port::{PendingId, StagedId};
use crate::hnn::receiving::ReceivingPhases;
use crate::holarchy::Count;
use crate::ratio::Rat;
use crate::receiver::reception::Component;

// -------------------------------------------------------------------------------------------
// the diamond

/// [definition] **One admitted receiver's time-indexed causal diamond**: the reach and observe
/// distances after `e_last` rounds (`None` beyond them) and `e_last`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Diamond {
    receiver: usize,
    last_epoch: usize,
    reach: Vec<Option<usize>>,
    observe: Vec<Option<usize>>,
}

/// One recursion: `x⁰ = 0` on the seeds, then `rounds` neighbour exchanges `x_h ← min(x_h, x_g + 1)`.
fn recursion(field: &Field, seeds: &[usize], rounds: usize) -> Vec<Option<usize>> {
    let mut distance: Vec<Option<usize>> = (0..field.rings().len())
        .map(|g| seeds.contains(&g).then_some(0))
        .collect();
    for _ in 0..rounds {
        let previous = distance.clone();
        for contact in field.contacts() {
            let (g, h) = contact.ends();
            for (here, there) in [(g, h), (h, g)] {
                if let Some(d) = previous[here] {
                    let candidate = d + 1;
                    if distance[there].is_none_or(|current| candidate < current) {
                        distance[there] = Some(candidate);
                    }
                }
            }
        }
    }
    distance
}

fn le(sum: Option<usize>, bound: usize) -> bool {
    sum.is_some_and(|value| value <= bound)
}

fn add(a: Option<usize>, b: Option<usize>, extra: usize) -> Option<usize> {
    Some(a? + b? + extra)
}

fn min(a: Option<usize>, b: Option<usize>) -> Option<usize> {
    match (a, b) {
        (Some(x), Some(y)) => Some(x.min(y)),
        (x, None) | (None, x) => x,
    }
}

impl Diamond {
    /// **The two recursions** for the field's source rings and one admitted receiver, `e_last`
    /// rounds each (Lean `HNN/Retention.diamond_recursion`).
    pub fn of(field: &Field, phases: &ReceivingPhases) -> Self {
        let last_epoch = phases.last_epoch();
        Self {
            receiver: phases.ring(),
            last_epoch,
            reach: recursion(field, field.sources(), last_epoch),
            observe: recursion(field, &[phases.ring()], last_epoch),
        }
    }

    /// `e_last`.
    pub fn last_epoch(&self) -> usize {
        self.last_epoch
    }

    /// The receiving ring.
    pub fn receiver(&self) -> usize {
        self.receiver
    }

    /// `r_g`, `None` beyond `e_last` hops.
    pub fn reach(&self, ring: usize) -> Option<usize> {
        self.reach[ring]
    }

    /// `o_g`, `None` beyond `e_last` hops.
    pub fn observe(&self, ring: usize) -> Option<usize> {
        self.observe[ring]
    }

    pub fn element(&self, ring: usize) -> bool {
        le(
            add(self.reach[ring], self.observe[ring], 1),
            self.last_epoch,
        )
    }

    pub fn junction(&self, ring: usize) -> bool {
        le(
            add(self.reach[ring], self.observe[ring], 0),
            self.last_epoch,
        )
    }

    pub fn channel(&self, field: &Field, contact: usize) -> bool {
        let (g, h) = field.contact(contact).ends();
        le(
            add(
                min(self.reach[g], self.reach[h]),
                min(self.observe[g], self.observe[h]),
                1,
            ),
            self.last_epoch,
        )
    }

    pub fn conductance(&self, field: &Field, contact: usize) -> bool {
        let (g, h) = field.contact(contact).ends();
        self.channel(field, contact) || self.junction(g) || self.junction(h)
    }

    pub fn source_port(&self, field: &Field, ring: usize) -> bool {
        field.is_source(ring) && le(self.observe[ring], self.last_epoch)
    }

    pub fn standing(&self, field: &Field, ring: usize) -> bool {
        self.element(ring)
            || field.incident(ring).iter().any(|&a| {
                let (g, h) = field.contact(a).ends();
                self.element(if g == ring { h } else { g })
            })
    }

    /// Whether a locus is retained for this receiver.
    pub fn retains(&self, field: &Field, locus: Locus) -> bool {
        match locus {
            Locus::Element(g) => self.element(g),
            Locus::Junction(g) => self.junction(g),
            Locus::Channel(a) => self.channel(field, a),
            Locus::Conductance(a) => self.conductance(field, a),
            Locus::SourcePort(g) => self.source_port(field, g),
            Locus::Standing(g) => self.standing(field, g),
            Locus::ReceivingMap(g) => g == self.receiver,
        }
    }

    /// **The element's window**: tick `t` of ring `g`'s element is read within the word when
    /// `r_g ≤ t` and `t + 1 + o_g ≤ e_last`.
    pub fn element_window(&self, ring: usize, tick: usize) -> bool {
        self.reach[ring].is_some_and(|r| r <= tick)
            && le(self.observe[ring].map(|o| tick + 1 + o), self.last_epoch)
    }

    /// **The channel's window**: tick `t` of contact `a`'s transit is read within the word when
    /// `min(r_g, r_h) ≤ t` and `t + 1 + min(o_g, o_h) ≤ e_last`.
    pub fn channel_window(&self, field: &Field, contact: usize, tick: usize) -> bool {
        let (g, h) = field.contact(contact).ends();
        min(self.reach[g], self.reach[h]).is_some_and(|r| r <= tick)
            && le(
                min(self.observe[g], self.observe[h]).map(|o| tick + 1 + o),
                self.last_epoch,
            )
    }

    /// The loci this receiver retains.
    pub fn retained(&self, field: &Field) -> BTreeSet<Locus> {
        loci(field)
            .into_iter()
            .filter(|locus| self.retains(field, *locus))
            .collect()
    }
}

/// Every locus of the field, in a fixed order.
pub fn loci(field: &Field) -> Vec<Locus> {
    let mut all = Vec::new();
    for g in 0..field.rings().len() {
        all.extend([Locus::Element(g), Locus::Junction(g), Locus::Standing(g)]);
        if field.is_source(g) {
            all.push(Locus::SourcePort(g));
        }
        if field.receivers().iter().any(|receiver| receiver.ring == g) {
            all.push(Locus::ReceivingMap(g));
        }
    }
    for a in 0..field.contacts().len() {
        all.extend([Locus::Channel(a), Locus::Conductance(a)]);
    }
    all
}

/// **The union of the admitted receivers' retentions.** The receiving maps are always retained.
pub fn retained(field: &Field, admitted: &[ReceivingPhases]) -> BTreeSet<Locus> {
    let mut kept: BTreeSet<Locus> = loci(field)
        .into_iter()
        .filter(|locus| matches!(locus, Locus::ReceivingMap(_)))
        .collect();
    for phases in admitted {
        kept.extend(Diamond::of(field, phases).retained(field));
    }
    kept
}

/// **An admitted family is contained in the previous boundary's** exactly when each of its
/// receivers reads a ring, grain and epoch range some previous receiver read (Lean
/// `HNN/Retention.admitted_nonincreasing`). Refused otherwise, naming the receivers it would add.
pub fn contained(
    admitted: &[ReceivingPhases],
    previous: &[ReceivingPhases],
) -> Result<(), HnnError> {
    let added: Vec<usize> = admitted
        .iter()
        .filter(|phases| {
            !previous.iter().any(|earlier| {
                earlier.ring() == phases.ring()
                    && earlier.grain() == phases.grain()
                    && earlier.first_epoch() <= phases.first_epoch()
                    && phases.last_epoch() <= earlier.last_epoch()
            })
        })
        .map(ReceivingPhases::ring)
        .collect();
    if added.is_empty() {
        Ok(())
    } else {
        Err(HnnError::AdmittedGrowth { receivers: added })
    }
}

// -------------------------------------------------------------------------------------------
// the collapse

/// [definition] **What the collapse did to the constitution**: the loci it retains and the ones it
/// newly released (each whole: value, carried remainders and deposit clock), the carried remainders
/// that left with them (exact, each with its locus, array and entry: Decision 22's "leaves whole,
/// with its remainder, reported"), their operator entries (the design's count: an element's
/// `n_g²`, a channel's `3k_a²`) against the field's total, and the constitution's exact bits before
/// and after.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Collapse {
    pub retained: BTreeSet<Locus>,
    pub released: BTreeSet<Locus>,
    pub released_remainders: Vec<(Locus, Carrier, usize, Rat)>,
    pub released_entries: usize,
    pub total_entries: usize,
    pub bits: [u64; 2],
}

/// **The collapse at an aeon boundary** (design (a), retention items 1–7; Lean
/// `HNN/Retention.collapse` at the budgeted carry, `HNN/LatticeDeposit.lattice_deposit_descends`):
/// every locus no admitted receiver's diamond retains is released, exactly and whole, through the
/// constitution's one release mutator; the retained loci keep their values, their carried
/// remainders and their deposit clocks. Released loci stay released.
pub fn collapse(
    field: &Field,
    constitution: &mut Constitution,
    admitted: &[ReceivingPhases],
) -> Result<Collapse, HnnError> {
    let kept = retained(field, admitted);
    let before = constitution.exact_bits();
    let released: BTreeSet<Locus> = loci(field)
        .into_iter()
        .filter(|locus| !kept.contains(locus) && !constitution.released().contains(locus))
        .collect();
    // The receiving map is never released, so its remainders stay (`Constitution::release`).
    let released_remainders = constitution
        .carried_remainders()
        .into_iter()
        .filter(|(locus, ..)| released.contains(locus) && !matches!(locus, Locus::ReceivingMap(_)))
        .collect();
    constitution.release(&released)?;
    let total_entries = loci(field).iter().map(|locus| locus.entries(field)).sum();
    let released_entries = constitution
        .released()
        .iter()
        .map(|locus| locus.entries(field))
        .sum();
    Ok(Collapse {
        retained: kept,
        released,
        released_remainders,
        released_entries,
        total_entries,
        bits: [before, constitution.exact_bits()],
    })
}

/// **A pending ratio's separator**: the loci its own receiver's diamond reads that the admitted
/// family releases. Empty exactly when its reading factors through the collapse.
pub fn separator(field: &Field, phases: &ReceivingPhases, kept: &BTreeSet<Locus>) -> Vec<Locus> {
    Diamond::of(field, phases)
        .retained(field)
        .into_iter()
        .filter(|locus| !kept.contains(locus))
        .collect()
}

// -------------------------------------------------------------------------------------------
// the boundary

/// [definition] **The aeon's readings on the joint clock** (design (c), `close_aeon`'s source order;
/// objects §12). The resident's aeon is an [`Aeon<ClockLift>`] on the Holarchy's parametric
/// orientation, from its opening lift point to the joint clock's carry-out, carried by those two
/// points and built as their forward word ([`ClockLift::forward`]), which every clock of the lift
/// reads as the motion itself. Through the aeon owners:
///
/// - each ring's reading is `aeon::reading` of its own clock `dθ_g`
///   ([`TorusClock::navigator`]): its lift displacement in turns, whole windings and open phase
///   (Lean `Aeon/Clock/Winding.reading_navigatorClock`, `HNN/Retention.lift_reading`);
/// - each ring's epochs are the flux through its ring section ([`aeon::epochs`] at
///   [`ClockLift::ring_section`], [`crate::aeon::Epochs::flux`]; Lean
///   `Aeon/Clock/Epoch.signed_count_is_flux`);
/// - the carry-out is the aeon closing on the last ring's clock: read on that ring's own circle
///   the aeon is an [`aeon::Cycle`] exactly when the ring opened on its section, and the cycle then
///   reads one whole winding (Lean `Winding.torus_cycle_reads_whole_windings`). Campaign 1's last
///   ring steps only by carry, so from its section it returns to it exactly at the carry-out. A
///   published key that opened it off its section, or a lock of its own that steps it past the
///   section, leaves the carry-out one crossing of the section (flux 1) that is not a cycle: a
///   declared absence.
///
/// [`aeon::epochs`]: crate::aeon::epochs
/// [`aeon::Cycle`]: crate::aeon::Cycle
pub fn aeon_readings(
    lift: &ClockLift,
    opening: &[BigInt],
    carry_out: &[BigInt],
) -> Result<(Vec<Reading>, Vec<BigInt>, Component<Reading>), HnnError> {
    let aeon = lift.forward(opening.to_vec(), carry_out)?;
    let mut readings = Vec::with_capacity(lift.navigators());
    let mut fluxes = Vec::with_capacity(lift.navigators());
    for (ring, period) in lift.periods().iter().enumerate() {
        readings.push(reading(&TorusClock::navigator(lift, ring)?, &aeon)?);
        fluxes.push(epochs(&aeon, lift.ring_section(ring, period.clone())?).flux());
    }
    let last = lift.navigators().saturating_sub(1);
    let circle = ClockLift::new(vec![lift.periods()[last].clone()])?;
    let closed = circle.forward(vec![opening[last].clone()], &[carry_out[last].clone()])?;
    let closing = match Cycle::close(&circle, closed) {
        Ok(cycle) => {
            Component::Present(reading(&TorusClock::navigator(&circle, 0)?, cycle.aeon())?)
        }
        Err(AeonError::NotACycle) => Component::Absent(
            "the aeon does not return the last ring to its phase state (a published key opened it \
             off its section, or its own lock stepped it past the section): the carry-out is one \
             crossing of its section, not a cycle of its clock",
        ),
        Err(refusal) => return Err(refusal.into()),
    };
    Ok((readings, fluxes, closing))
}

/// [definition] **What the collapse returns at an aeon boundary** (design (c), `AeonBoundary`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AeonBoundary {
    /// The admitted family it collapsed onto.
    pub admitted: Vec<ReceivingPhases>,
    /// The constitution's collapse: `V = ⊕V_g` as retained and released loci, entries and bits.
    pub collapse: Collapse,
    /// The value kernel beyond the structural release: a reading owed by campaign 3.
    pub value_kernel: Component<()>,
    /// The aeon's two lift points, its opening and the joint clock's carry-out, on the Holarchy's
    /// parametric orientation ([`AeonBoundary::aeon`] builds its word).
    pub opening: Vec<BigInt>,
    pub carry_out: Vec<BigInt>,
    /// Each ring's aeon reading on its own clock, as windings and open phase ([`aeon_readings`]).
    pub readings: Vec<Reading>,
    /// Each ring's epochs over the aeon: the flux through its ring section ([`aeon_readings`]).
    pub epochs: Vec<BigInt>,
    /// The carry-out read on the last ring's clock: its cycle's whole reading, or a declared
    /// absence when the aeon is not a cycle of that clock ([`aeon_readings`]).
    pub closing: Component<Reading>,
    /// The aeon's length in cells.
    pub cells: u64,
    /// The first law of learning over the aeon, read on enclosed code lengths
    /// ([`crate::aeon::EnclosedLedger`]): exchange and deposition, telescoping to the aeon's change
    /// of code length.
    pub first_law: EnclosedBalance,
    /// Beside it, the face against the literal over the aeon's arrivals:
    /// `Σ ℓ_k + Σ g_k = n·log₂|A|`, a reading, not a budget.
    pub literal: LiteralComparison,
    /// The Holarchy's receiver-relative view and count of its regions at the boundary. The field's
    /// chart glues its rings and contacts at their ports with no glued cell complex, so no
    /// receiver has regions to partition: a declared absence until the cellular gluing exists.
    pub view: Component<Vec<Count>>,
    /// The pending ratios carried, and those refused with their separators (and discarded).
    pub carried: Vec<PendingId>,
    pub refused: Vec<(PendingId, Vec<Locus>)>,
    /// The staged deposits refused with the released loci they would reach (and discarded); every
    /// other staged deposit is carried.
    pub refused_staged: Vec<(StagedId, Vec<Locus>)>,
    /// The resident's state bits (lift point, open moments, pending ratios, staged deposits, the
    /// first law's arrived source and the constitution) before and after.
    pub state_bits: [u64; 2],
}

impl AeonBoundary {
    /// **The aeon** on the parametric orientation `lift`: the forward word between its two lift
    /// points, which every clock of the lift reads as the motion itself ([`ClockLift::forward`]).
    pub fn aeon(&self, lift: &ClockLift) -> Result<Aeon<ClockLift>, HnnError> {
        Ok(lift.forward(self.opening.clone(), &self.carry_out)?)
    }
}

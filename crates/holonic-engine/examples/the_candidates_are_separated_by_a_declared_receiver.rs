//! **Phoenix station five, its dissection half: the open candidate compositions are separated by a
//! declared receiver family, not by anyone reading the output.**
//!
//! Plan: `blueprint/THE_GEMMA_MAP_IS_DISSECTED_CONDENSED_CULTIVATED_AND_REBORN_AS_A_FROZEN_NATIVE_MODEL.md`.
//! Derivation:
//! `research/records/2026-08-18_THE_HOLON_IS_THE_OPERATION_COMPLEX_THE_FOREIGN_MAP_IS_A_PORTED_WORD_AND_THE_CARD_CARRIES_ITS_FRONTS.md`
//! §§7, 12.5.
//!
//! # What this settles and what it cannot
//!
//! Station one returned four bindings the admitted testimony does not decide. The plan forbids
//! settling them by inspecting a plausible surface, and it is right to: a reading that looks like
//! language is a receiver's coarse face and cannot adjudicate a transport.
//!
//! What *can* be settled here is which of those questions are **real**. Two candidates that no
//! declared receiver separates are one composition for that family, and the question between them
//! is moot at this aperture. Two that separate are genuinely different transports, and the
//! **shortest history that separates them** is what a later station must acquire source evidence
//! about. `receiver_exact_compression` returns exactly that, and nothing here chooses.
//!
//! # Matched siblings
//!
//! Each sibling differs from the base in **exactly one relation**, so a separation is attributable.
//!
//! # The anti-vacuity control, and the obvious reading of it is wrong
//!
//! Withdrawing one receiver and finding the partition unmoved does **not** show that receiver is
//! decorative — it shows it is **redundant with the others**. Measured here: all thirty-two are
//! individually redundant, and the family still does work. The two honest controls are withdrawing
//! the whole family, which must coarsen the partition, and finding a **minimal subfamily** that
//! returns the same one. Both run below.
//!
//! ```text
//! cargo run --release -q -p holonic-engine \
//!   --example the_candidates_are_separated_by_a_declared_receiver -- /home/b/models/gemma-4-E4B-it
//! ```

#[path = "phoenix/site.rs"]
mod site;

use holonic_engine::embedding_fiber::ResidentReadout;
use holonic_engine::receiver_exact_compression::{
    compress, AblatedSystem, InputId, ItemId, Observation, ObservedSystem, ReceiverId,
};
use num_traits::{Signed, Zero};
use relational_geometry::Rat;
use site::{conduct, Candidate, BASE, CAUSED, SIBLINGS};

// ---------------------------------------------------------------------------------------------
// THE DECLARED RECEIVER FAMILY
// ---------------------------------------------------------------------------------------------

/// The candidates and what a declared family of receivers reads of each, at each caused position.
///
/// **The receivers are faces, not magnitudes.** A hand is the phase a magnitude reading deletes, and
/// an ordering is what survives a rebase; both cross a frame where a value does not.
struct CandidateSystem {
    /// `returns[item][position]` — the carried standing under one candidate at one position.
    returns: Vec<Vec<Vec<Rat>>>,
    /// `state[item]` is `(candidate, position)`, flattened.
    states: Vec<(usize, usize)>,
    coordinates: Vec<usize>,
}

impl CandidateSystem {
    fn item_of(&self, candidate: usize, position: usize) -> ItemId {
        ItemId(
            self.states
                .iter()
                .position(|held| *held == (candidate, position))
                .expect("declared") as u64,
        )
    }
}

impl ObservedSystem for CandidateSystem {
    fn items(&self) -> Vec<ItemId> {
        (0..self.states.len() as u64).map(ItemId).collect()
    }

    fn receivers(&self) -> Vec<ReceiverId> {
        // One hand receiver and one order receiver per declared coordinate.
        (0..(self.coordinates.len() * 2) as u64)
            .map(ReceiverId)
            .collect()
    }

    fn inputs(&self) -> Vec<InputId> {
        vec![InputId(0)]
    }

    fn observation(&self, item: ItemId, receiver: ReceiverId) -> Observation {
        let (candidate, position) = self.states[item.0 as usize];
        let section = &self.returns[candidate][position];
        let which = receiver.0 as usize / 2;
        let coordinate = self.coordinates[which];
        let value = section.get(coordinate).cloned().unwrap_or_else(Rat::zero);
        if receiver.0 % 2 == 0 {
            // THE HAND: the phase a magnitude reading deletes.
            Observation(if value.is_positive() {
                1
            } else if value.is_negative() {
                2
            } else {
                0
            })
        } else {
            // AN ORDER: this coordinate against the next declared one. A relation, not a value.
            let other = self
                .coordinates
                .get(which + 1)
                .and_then(|at| section.get(*at))
                .cloned()
                .unwrap_or_else(Rat::zero);
            Observation(match value.cmp(&other) {
                std::cmp::Ordering::Less => 1,
                std::cmp::Ordering::Equal => 2,
                std::cmp::Ordering::Greater => 3,
            })
        }
    }

    fn successor(&self, item: ItemId, _input: InputId) -> Option<ItemId> {
        let (candidate, position) = self.states[item.0 as usize];
        if position + 1 < self.returns[candidate].len() {
            Some(self.item_of(candidate, position + 1))
        } else {
            None
        }
    }
}

/// A declared subfamily of receivers. `AblatedSystem` withdraws one; this keeps a stated set, which
/// is what a MINIMAL separating family needs.
struct RestrictedSystem<'a> {
    inner: &'a dyn ObservedSystem,
    kept: Vec<ReceiverId>,
}

impl ObservedSystem for RestrictedSystem<'_> {
    fn items(&self) -> Vec<ItemId> {
        self.inner.items()
    }
    fn receivers(&self) -> Vec<ReceiverId> {
        self.kept.clone()
    }
    fn inputs(&self) -> Vec<InputId> {
        self.inner.inputs()
    }
    fn observation(&self, item: ItemId, receiver: ReceiverId) -> Observation {
        self.inner.observation(item, receiver)
    }
    fn successor(&self, item: ItemId, input: InputId) -> Option<ItemId> {
        self.inner.successor(item, input)
    }
}

// ---------------------------------------------------------------------------------------------

fn main() {
    let root = std::env::args()
        .nth(1)
        .unwrap_or_else(|| "/home/b/models/gemma-4-E4B-it".to_owned());
    let terms: usize = std::env::var("TERMS")
        .ok()
        .and_then(|value| value.parse().ok())
        .unwrap_or(20);

    let chart = match ResidentReadout::new() {
        Ok(chart) => chart,
        Err(error) => {
            println!("the resident chart refused: {error:?}");
            println!("The admitted hot deed returns a typed refusal. No CPU answer appears.");
            std::process::exit(1);
        }
    };

    println!("PHOENIX STATION FIVE (DISSECTION) — THE CANDIDATES ARE SEPARATED");
    println!();
    println!("  resident chart                    {}", chart.device_name());
    println!("  caused positions                  {}", CAUSED.len());
    println!("  declared aperture                 the receiver/presented/carried front, its");
    println!("                                    chronology and its contact. The constitutive");
    println!("                                    passage is EXCLUDED and reported as excluded.");
    println!();

    let mut population = vec![BASE];
    population.extend(SIBLINGS);
    let mut returns = Vec::with_capacity(population.len());
    for candidate in &population {
        let clock = std::time::Instant::now();
        match conduct(&root, &chart, *candidate, terms, None) {
            Ok(carried) => {
                println!(
                    "  conducted  {:<44} {:?}",
                    candidate.name,
                    clock.elapsed()
                );
                returns.push(carried);
            }
            Err(error) => {
                println!("  REFUSED    {:<44} {error}", candidate.name);
                println!("  A refusal is the return. Nothing is substituted for it.");
                std::process::exit(1);
            }
        }
    }

    // The declared coordinate family: a spread across the carried chart, stated rather than sought.
    let width = returns[0][0].len();
    let coordinates: Vec<usize> = (0..16).map(|k| k * width / 16).collect();
    let mut states = Vec::new();
    for candidate in 0..population.len() {
        for position in 0..CAUSED.len() {
            states.push((candidate, position));
        }
    }
    let system = CandidateSystem {
        returns,
        states,
        coordinates: coordinates.clone(),
    };

    println!();
    println!("  THE DECLARED RECEIVER FAMILY");
    println!("    coordinates declared            {}", coordinates.len());
    println!("    receivers                       {} — a HAND and an ORDER at each", coordinates.len() * 2);
    println!("    items                           {} — one per candidate per position", system.states.len());
    println!("    (a hand is the phase a magnitude reading deletes; an order is a relation. Both");
    println!("     cross a frame where a value does not.)");

    let reading = compress(&system);
    println!();
    println!("  THE RECEIVER-EXACT QUOTIENT");
    println!("    one-shot blocks                 {}", reading.one_shot.len());
    println!("    blocks under successor conduct  {}", reading.conduct.len());
    println!("    refinement rounds               {}", reading.rounds);
    println!("    one-shot reading is exact       {}", reading.is_exact());
    println!("    collapsed pairs later conduct separates  {}", reading.collapsed.len());

    println!();
    println!("  WHAT THIS SETTLES, QUESTION BY QUESTION");
    println!();
    let base_item = system.item_of(0, 0);
    for (at, candidate) in population.iter().enumerate().skip(1) {
        let sibling = system.item_of(at, 0);
        let together = reading.conduct.block_of(base_item) == reading.conduct.block_of(sibling);
        println!("    {}", candidate.question);
        println!("        sibling                 {}", candidate.name);
        if together {
            println!("        SEPARATED               no — no declared receiver tells them apart");
            println!("        so the question is      MOOT at this aperture; both are one transport");
            println!("                                for this family, and a richer receiver may reopen it");
        } else {
            println!("        SEPARATED               YES — the family tells them apart");
            println!("        so the question is      REAL, and settling it needs SOURCE conduct,");
            println!("                                which this machine does not hold");
        }
        println!();
    }

    for pair in reading.collapsed.iter().take(4) {
        println!(
            "    a one-shot collapse later conduct separates: {:?} against {:?} after {} input(s)",
            pair.left,
            pair.right,
            pair.distinguishing_word.len()
        );
        if let Some((receiver, left, right)) = &pair.witness {
            println!("        the receiver that finally saw it: {receiver:?} returning {left:?} against {right:?}");
        }
    }

    println!();
    println!("  THE ANTI-VACUITY CONTROL — and the first reading of it was wrong");
    println!();
    let mut individually_redundant = 0usize;
    for receiver in system.receivers() {
        let ablated = AblatedSystem {
            inner: &system,
            without: receiver,
        };
        if compress(&ablated).conduct.len() == reading.conduct.len() {
            individually_redundant += 1;
        }
    }
    println!("    receivers withdrawn one at a time          {}", system.receivers().len());
    println!("    whose single withdrawal changed nothing    {individually_redundant}");
    println!();
    println!("    **That is redundancy, not decoration**, and reading it as decoration would be");
    println!("    the error. Many receivers witness the same separation, so no SINGLE one is");
    println!("    necessary. The honest controls are the two below.");
    println!();

    // Control one: withdraw the whole family. The partition must collapse.
    let empty = RestrictedSystem {
        inner: &system,
        kept: Vec::new(),
    };
    let without_any = compress(&empty);
    println!("    with NO receiver at all, blocks            {}", without_any.conduct.len());
    println!("    with the whole family, blocks              {}", reading.conduct.len());
    println!(
        "    the family does work                       {}",
        without_any.conduct.len() < reading.conduct.len()
    );
    println!();

    // Control two: a MINIMAL subfamily that still returns the same partition.
    let mut kept: Vec<ReceiverId> = system.receivers();
    for receiver in system.receivers() {
        let trial: Vec<ReceiverId> = kept.iter().copied().filter(|held| *held != receiver).collect();
        let restricted = RestrictedSystem {
            inner: &system,
            kept: trial.clone(),
        };
        if compress(&restricted).conduct == reading.conduct {
            kept = trial;
        }
    }
    println!("    a MINIMAL subfamily returning the same partition: {} of {}", kept.len(), system.receivers().len());
    for receiver in &kept {
        let which = receiver.0 as usize / 2;
        println!(
            "        {receiver:?}  the {} at declared coordinate {}",
            if receiver.0 % 2 == 0 { "HAND" } else { "ORDER" },
            coordinates[which]
        );
    }
    println!("    every receiver outside it is redundant WITH these, not idle.");

    println!();
    println!("THE STATION'S VERDICT");
    println!();
    println!("  The candidates were separated by a declared receiver family and by nothing else.");
    println!("  No plausible surface was read and no composition was selected.");
    println!("  A question whose siblings collapse is MOOT at this aperture and is recorded so.");
    println!("  A question whose siblings separate is REAL, and the evidence that would settle it");
    println!("  is source conduct, which is absent on this machine and named as absent.");
    println!();
    println!("  The constitutive passage is excluded from this aperture. CONSTRUCTION_STATE is");
    println!("  untouched.");
}

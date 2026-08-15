//! Our chains **are** Markov chains, and softmax is the exponentiated difference
//! with the division removed.
//!
//! # Two readings, on one real chain
//!
//! The chain is this repository's own records, decomposed at a declared grain
//! into parts. Part follows part; that is the chain.
//!
//! ## Reading one — "Markov" is a property of the receiver, not of the material
//!
//! `receiver_exact_compression::compress` refines a one-shot reading to the
//! coarsest partition for which conduct is determined by the block. **That is
//! the causal-state construction**: a state is a set of histories with identical
//! futures.
//!
//! So the machine already computes the minimal Markov model of its material. And
//! the **memory order** is the longest shortest-word that separates a collapsed
//! pair — how far back the reading had to look to make every distinction it can
//! make. A pair that outruns a declared order is the **non-Markovianity at that
//! order, exhibited by name** rather than counted.
//!
//! Two readings of one chain make the point: the same material read through a
//! coarse family needs history, and read through a fine one needs none. The
//! material did not change, so the order is saying something about the receiver.
//!
//! ## Reading two — softmax is a ratio, and the partition function is a null
//!
//! ```text
//! softmax(x)_i = e^{x_i} / Σ_j e^{x_j}
//! ```
//!
//! It is invariant under `x → x + c`, so **the absolute values are gauge and the
//! differences are the content**; `p_i/p_j = e^{x_i − x_j}`, so **the exponential
//! is the map from an additive difference to a multiplicative ratio**; and `Z` is
//! a **declared null** that forces the total to one and contributes to no ratio.
//!
//! On `SymbolicSurprisal`'s prime-log carrier the exponential closes in ℚ:
//! `2^{Σ q_k log₂ p_k} = Π p_k^{q_k}`. So each row of the transition chart is a
//! **cocycle of exact rational ratios** — `r(i,j)·r(j,k) = r(i,k)` identically —
//! and a distribution appears only when a caller **names a null**, which does not
//! move the answer.
//!
//! **Temperature is a root on the ratio.** `T → 0` is argmax, and it is the limit
//! this reading does not take: every member's ratio against every other is
//! returned and none is discarded.
//!
//! # What would refute either reading
//!
//! A memory order that does not move when the receiver family changes on fixed
//! material; a collapsed pair whose word is longer than the reported order; a
//! ratio family whose cocycle fails; a declared null that moves the induced
//! distribution; or a temperature rebase that moves nothing.
//!
//! ```text
//! cargo run --release -p life --example the_chain_is_markov_and_the_softmax_is_a_ratio
//! ```

use std::collections::BTreeMap;

use holonic_engine::exponentiated_ratio::RatioFamily;
use holonic_engine::receiver_exact_compression::{
    InputId, ItemId, Observation, ObservedSystem, ReceiverId, compress,
};
use holonic_engine::surprisal::SymbolicSurprisal;
use life::decomposing_codec::{DecompositionGrain, Symbol, read, render_word};
use num_bigint::BigInt;
use relational_geometry::Rat;

const MATERIAL: [&str; 2] = [
    "canon/TABLET_THE_COMPRESSION.md",
    "canon/TABLET_THE_CIRCULATING_CARTOGRAPHER.md",
];

fn lines_of(path: &str) -> Vec<Vec<Symbol>> {
    std::fs::read_to_string(path)
        .unwrap_or_else(|error| panic!("declared material: {path}: {error}"))
        .lines()
        .filter(|line| !line.trim().is_empty())
        .map(|line| line.bytes().map(Symbol).collect())
        .collect()
}

/// The chain: a state is a part, an input is the part that follows it, and the
/// observation a receiver returns is a **declared coarse face** of that part.
///
/// Two receiver families are declared over the same chain — a coarse one that
/// sees only a part's length, and a fine one that sees the part's first symbol
/// as well. Neither is chosen; both are read, and the memory order is compared.
struct PartChain {
    /// state -> the successor states it was followed by, with counts.
    successors: Vec<BTreeMap<usize, usize>>,
    /// The part each state names.
    parts: Vec<Vec<Symbol>>,
    /// Whether the fine receiver family is in force.
    fine: bool,
}

impl PartChain {
    fn build(parts_in_order: &[Vec<Symbol>], fine: bool) -> Self {
        let mut index: BTreeMap<Vec<Symbol>, usize> = BTreeMap::new();
        let mut parts: Vec<Vec<Symbol>> = Vec::new();
        for part in parts_in_order {
            if !index.contains_key(part) {
                index.insert(part.clone(), parts.len());
                parts.push(part.clone());
            }
        }
        let mut successors = vec![BTreeMap::new(); parts.len()];
        for window in parts_in_order.windows(2) {
            let from = index[&window[0]];
            let to = index[&window[1]];
            *successors[from].entry(to).or_insert(0) += 1;
        }
        Self {
            successors,
            parts,
            fine,
        }
    }

    /// The declared face: what a receiver returns when it looks at a state.
    fn face(&self, state: usize) -> u64 {
        let part = &self.parts[state];
        if self.fine {
            // length and first symbol
            (part.len() as u64) * 256 + part.first().map(|s| u64::from(s.0)).unwrap_or(0)
        } else {
            // length alone
            part.len() as u64
        }
    }
}

impl ObservedSystem for PartChain {
    fn items(&self) -> Vec<ItemId> {
        (0..self.parts.len()).map(|at| ItemId(at as u64)).collect()
    }

    fn inputs(&self) -> Vec<InputId> {
        // One input per distinct declared face: "step to a successor whose face
        // is this". The input alphabet is therefore the receiver's own
        // vocabulary rather than the full state set.
        let mut faces: Vec<u64> = (0..self.parts.len()).map(|s| self.face(s)).collect();
        faces.sort_unstable();
        faces.dedup();
        faces.into_iter().map(InputId).collect()
    }

    fn receivers(&self) -> Vec<ReceiverId> {
        vec![ReceiverId(0)]
    }

    fn observation(&self, item: ItemId, _receiver: ReceiverId) -> Observation {
        Observation(self.face(item.0 as usize))
    }

    fn successor(&self, item: ItemId, input: InputId) -> Option<ItemId> {
        let state = item.0 as usize;
        self.successors
            .get(state)?
            .keys()
            .find(|to| self.face(**to) == input.0)
            .map(|to| ItemId(*to as u64))
    }
}

fn main() {
    println!("{}", "=".repeat(100));
    println!("THE CHAIN IS MARKOV AND THE SOFTMAX IS A RATIO");
    println!("{}", "=".repeat(100));
    println!();

    let material: Vec<Vec<Symbol>> = MATERIAL.iter().flat_map(|p| lines_of(p)).collect();
    let grain = DecompositionGrain::declare([vec![Symbol(b' ')]]).expect("a declared grain");
    let pass = read(&grain, &material).expect("the material reads");
    let sequence: Vec<Vec<Symbol>> = pass
        .decomposed
        .iter()
        .flat_map(|whole| whole.parts.iter().cloned())
        .collect();
    println!("  material   {} lines over {} records", material.len(), MATERIAL.len());
    println!("  the chain  {} parts in order, {} distinct", sequence.len(), pass.parts().len());
    println!();

    // ---------------------------------------------------------------------------------
    // READING ONE -- the memory order, under two declared receiver families.
    // ---------------------------------------------------------------------------------
    println!("{}", "-".repeat(100));
    println!("READING ONE -- 'Markov' is a property of the RECEIVER, not of the material");
    println!("{}", "-".repeat(100));

    let mut orders = Vec::new();
    for fine in [false, true] {
        let chain = PartChain::build(&sequence, fine);
        let compression = compress(&chain);
        let order = compression.memory_order();
        println!(
            "  family: {:<26}  states {:>5}  one-shot {:>5}  conduct {:>5}  collapsed {:>6}  order {}",
            if fine { "length and first symbol" } else { "length alone" },
            chain.parts.len(),
            compression.one_shot.len(),
            compression.conduct.len(),
            compression.collapsed.len(),
            match order {
                Some(k) => k.to_string(),
                None => "none -- memoryless for this family".to_owned(),
            }
        );
        if let Some(k) = order {
            let beyond_zero = compression.beyond_order(0).len();
            let beyond_half = compression.beyond_order(k.saturating_sub(1)).len();
            println!(
                "      pairs needing more than 0 symbols {beyond_zero}; more than {} symbols {beyond_half}",
                k.saturating_sub(1)
            );
            for pair in compression.beyond_order(k.saturating_sub(1)).iter().take(3) {
                println!(
                    "          {:?} vs {:?} separated only at depth {}",
                    chain.parts.get(pair.left.0 as usize).map(|p| render_word(p)),
                    chain.parts.get(pair.right.0 as usize).map(|p| render_word(p)),
                    pair.distinguishing_word.len()
                );
            }
            assert!(compression.is_markov_at(k), "the order must bound its own population");
            assert!(!compression.is_markov_at(k - 1) || k == 0);
        }
        orders.push(order);
    }
    let order_moved = orders[0] != orders[1];
    println!();
    println!(
        "  the SAME material read two ways returned different orders   {}",
        if order_moved { "YES -- the order is the receiver's" } else { "NO" }
    );

    // ---------------------------------------------------------------------------------
    // READING TWO -- the transition row as an exact ratio cocycle.
    // ---------------------------------------------------------------------------------
    println!();
    println!("{}", "-".repeat(100));
    println!("READING TWO -- a transition row is a COCYCLE OF EXACT RATIOS, and Z is a declared null");
    println!("{}", "-".repeat(100));

    let chain = PartChain::build(&sequence, true);
    // The state with the most distinct successors: the richest row in the chain.
    let (widest, row) = chain
        .successors
        .iter()
        .enumerate()
        .max_by_key(|(_, row)| row.len())
        .expect("the chain has a state");
    println!(
        "  widest row: the part {} is followed by {} distinct parts",
        render_word(&chain.parts[widest]),
        row.len()
    );

    let total: usize = row.values().sum();
    let population: BTreeMap<u64, SymbolicSurprisal> = row
        .iter()
        .map(|(to, count)| {
            let probability = Rat::new(BigInt::from(*count as i64), BigInt::from(total as i64));
            (
                *to as u64,
                SymbolicSurprisal::of_probability(&probability).expect("a probability"),
            )
        })
        .collect();

    let family = RatioFamily::read(&population).expect("a family of at least two");
    println!("  members {}", family.members().len());

    let cocycle = family.cocycle_holds();
    let null_trivial = family.null_orbit_is_trivial().expect("a distribution");
    println!("  the ratios compose over every triple                        {cocycle}");
    println!("  the declared null does not move the induced distribution    {null_trivial}");

    // Show a few exact ratios, and the distribution recovered from them alone.
    println!();
    println!("  exact pairwise ratios -- no float, no logarithm evaluated, no normalisation:");
    let shown: Vec<u64> = family.members().iter().copied().take(4).collect();
    for left in &shown {
        for right in &shown {
            if left == right {
                continue;
            }
            if let Some(ratio) = family.ratio(*left, *right) {
                println!(
                    "      p({:<14}) / p({:<14}) = {}",
                    render_word(&chain.parts[*left as usize]),
                    render_word(&chain.parts[*right as usize]),
                    ratio
                );
            }
        }
    }

    let reference = family.members()[0];
    let weights = family.normalised_against(reference).expect("a distribution");
    let weight_total: Rat = weights.values().cloned().sum();
    println!();
    println!(
        "  declaring {} the null recovers the row exactly; the weights sum to {}",
        render_word(&chain.parts[reference as usize]),
        weight_total
    );

    // Temperature is a root on the ratio, and it moves the family.
    let colder = family.rebased_by(3).expect("a positive reciprocal");
    let temperature_moves = colder != family;
    let colder_cocycle = colder.cocycle_holds();
    println!(
        "  a temperature rebase moves the family {temperature_moves} and stays a cocycle {colder_cocycle}"
    );

    println!();
    println!("{}", "=".repeat(100));
    println!("WHAT RETURNED");
    println!("{}", "=".repeat(100));
    println!("  the memory order moved with the receiver family      {order_moved}");
    println!("  the transition row is an exact cocycle                {cocycle}");
    println!("  the declared null carries no information             {null_trivial}");
    println!("  the weights sum to exactly one over the rationals     {}", weight_total == Rat::from_integer(BigInt::from(1)));
    println!("  temperature rebases the winding and stays a cocycle   {}", temperature_moves && colder_cocycle);

    println!();
    println!("{}", "-".repeat(100));
    println!("WHAT THIS RUN DOES NOT ESTABLISH");
    println!("{}", "-".repeat(100));
    println!("  No argmax is taken anywhere: every member's ratio against every other is returned");
    println!("  and none is discarded. T -> 0 is where softmax becomes a chooser and no path here");
    println!("  reaches it. The row's counts are what happened; the ratios are their invariant face;");
    println!("  and the normalisation appears only in a function whose name says a null was named.");
    println!("{}", "=".repeat(100));

    let held = order_moved && cocycle && null_trivial && temperature_moves && colder_cocycle;
    println!();
    println!("{}", "=".repeat(100));
    if held {
        println!("HELD -- the order is the receiver's, the row is a cocycle, the null is a frame,");
        println!("        and temperature is a root on a ratio rather than a new quantity.");
    } else {
        println!("REFUTED -- order_moved={order_moved} cocycle={cocycle} null={null_trivial} temperature={temperature_moves}");
        println!("{}", "=".repeat(100));
        std::process::exit(1);
    }
    println!("{}", "=".repeat(100));
}

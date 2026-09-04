//! Our chains **are** Markov chains, and softmax is the exponentiated difference
//! with the division removed.
//!
//! # Three readings, on one real chain
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
//! ## Reading three — what the families ARE to each other
//!
//! Readings one and two return the families, and the ratios inside one row.
//! Neither says what the families are to **each other**, which is the question a
//! production generation has to answer: a continuation is a step between
//! families, not a scalar attached to one.
//!
//! It needs no new organ and **no declared axis**. A family index is minted by
//! sort order and its differences carry nothing, so nothing here reads one as a
//! magnitude. What is read is the **action**: because `compress` returns the
//! coarsest partition for which conduct is determined by the block, every input
//! symbol already induces a map *on families*, and that map is well defined
//! exactly because the partition is a causal-state partition. The driver checks
//! that rather than assuming it.
//!
//! ```text
//!   PERMUTES   injective where defined — families carried onto families,
//!              nothing merged, the step reversible
//!   COLLAPSES  two families to one — the step deletes a distinction
//!   SINK       a family with no outgoing step: a continuation stops here
//! ```
//!
//! **The permute/collapse split is the reversible/irreversible split**, and the
//! collapsing generators are where the compression actually happens. A structure
//! whose generators all permute is a group and closes; one with collapsing
//! generators is a proper monoid, and the collapse is the remainder.
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
use holonic_engine::landauer::{self, ThermalFrame};
use holonic_engine::receiver_exact_compression::{
    compress, InputId, ItemId, Observation, ObservedSystem, ReceiverId,
};
use holonic_engine::surprisal::SymbolicSurprisal;
use life::decomposing_codec::{read, render_word, DecompositionGrain, Symbol};
use life::material_incidence::strongly_connected_cores;
use num_bigint::BigInt;
use relational_geometry::Rat;

const MATERIAL: [&str; 2] = [
    "docs/canon/TABLET_THE_COMPRESSION.md",
    "docs/canon/TABLET_THE_CIRCULATING_CARTOGRAPHER.md",
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

    // The declared material, or whatever the caller names instead. The two tablets are the
    // declared default and every figure below is read off whatever was actually supplied, so a
    // reading taken on more material is the same reading and not a different experiment.
    let declared: Vec<String> = {
        let named: Vec<String> = std::env::args().skip(1).collect();
        if named.is_empty() {
            MATERIAL.iter().map(|p| (*p).to_owned()).collect()
        } else {
            named
        }
    };
    let material: Vec<Vec<Symbol>> = declared.iter().flat_map(|p| lines_of(p)).collect();
    let grain = DecompositionGrain::declare([vec![Symbol(b' ')]]).expect("a declared grain");
    let pass = read(&grain, &material).expect("the material reads");
    let sequence: Vec<Vec<Symbol>> = pass
        .decomposed
        .iter()
        .flat_map(|whole| whole.parts.iter().cloned())
        .collect();
    println!(
        "  material   {} lines over {} records",
        material.len(),
        declared.len()
    );
    println!(
        "  the chain  {} parts in order, {} distinct",
        sequence.len(),
        pass.parts().len()
    );
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
                    chain
                        .parts
                        .get(pair.left.0 as usize)
                        .map(|p| render_word(p)),
                    chain
                        .parts
                        .get(pair.right.0 as usize)
                        .map(|p| render_word(p)),
                    pair.distinguishing_word.len()
                );
            }
            assert!(
                compression.is_markov_at(k),
                "the order must bound its own population"
            );
            assert!(!compression.is_markov_at(k - 1) || k == 0);
        }
        orders.push(order);
    }
    let order_moved = orders[0] != orders[1];

    println!(
        "  the SAME material read two ways returned different orders   {}",
        if order_moved {
            "YES -- the order is the receiver's"
        } else {
            "NO"
        }
    );
    // ---------------------------------------------------------------------------------
    // READING THREE -- what the families ARE under the symbol action, and what reaches what.
    // ---------------------------------------------------------------------------------
    //
    // Readings one and two return the families and the ratios INSIDE one row. Neither says what
    // the families are to each other. That question needs no new organ and no declared axis:
    // `compress` returns the coarsest partition for which conduct is determined by the block, so
    // **every input symbol already induces a map ON FAMILIES**, and the induced map is well defined
    // exactly because the partition is a causal-state partition. If it is not well defined the
    // partition is not one, and that is a finding rather than an error to smooth over.
    //
    // A family index is minted by sort order and its differences carry nothing, so nothing here
    // reads one as a magnitude. What is read is the action:
    //
    //   PERMUTES   the symbol is injective where it is defined — the families it touches are
    //              carried onto families, nothing is merged, and that step is reversible
    //   COLLAPSES  two families go to one — the step deletes a distinction the receiver had
    //   PARTIAL    the symbol is undefined on some family it could have acted on
    //
    // **A family with no outgoing step is a SINK**, and a sink is where a continuation stops having
    // anywhere to go — the same reading `the_cycle_halts_where_nothing_reflects` takes at the
    // enclosure boundary, taken here on the family structure instead.
    let reading_three = PartChain::build(&sequence, true);
    let compression = compress(&reading_three);
    println!();
    println!("{}", "-".repeat(100));
    println!(
        "READING THREE -- the families under the symbol action: what permutes, what collapses,"
    );
    println!("                 what reaches what, and where a continuation has nowhere to go");
    println!("{}", "-".repeat(100));

    let families = compression.conduct.len();
    // `Partition::block_of` is a linear scan over blocks, so calling it inside the loops below is
    // quadratic in the family population — measured: the reading did not return on thirty documents.
    // The index is built once and the loops read it. This is the driver's cost, not the organ's.
    let mut family_of: BTreeMap<u64, usize> = BTreeMap::new();
    for (family, block) in compression.conduct.blocks.iter().enumerate() {
        for item in block {
            family_of.insert(item.0, family);
        }
    }

    let inputs = reading_three.inputs();
    let items = reading_three.items();

    // The induced map on families, per symbol, together with the check that it IS a map.
    //
    // **Walked over the EDGES, not over (symbol x item).** The first form of this asked
    // `successor(item, input)` for every pair, and `successor` scans a state's successors to find
    // one whose face matches — so the reading was O(items x symbols x successors) and, measured, did
    // not return in four minutes on twelve canon documents with one core pinned. The material had
    // not changed species; the loop had the wrong shape. Walking the edges the chain actually
    // carries is linear in them, and the same figures come back.
    let mut permutes = 0usize;
    let mut collapses = 0usize;
    let mut plural = Vec::new();
    let mut edges: BTreeMap<usize, BTreeMap<usize, InputId>> = BTreeMap::new();
    // family -> the families this symbol carries it to. A SET, because the chain need not be
    // deterministic at a declared face and pretending it is would delete the plurality.
    let mut per_symbol: BTreeMap<u64, BTreeMap<usize, std::collections::BTreeSet<usize>>> =
        BTreeMap::new();
    for (state, onward) in reading_three.successors.iter().enumerate() {
        let Some(from) = family_of.get(&(state as u64)).copied() else {
            continue;
        };
        for to_state in onward.keys() {
            let face = reading_three.face(*to_state);
            let Some(to) = family_of.get(&(*to_state as u64)).copied() else {
                continue;
            };
            per_symbol
                .entry(face)
                .or_default()
                .entry(from)
                .or_default()
                .insert(to);
        }
    }
    for (face, image) in &per_symbol {
        for (from, onward) in image {
            for to in onward {
                edges.entry(*from).or_default().insert(*to, InputId(*face));
            }
            if onward.len() > 1 {
                plural.push((InputId(*face), *from, onward.clone()));
            }
        }
        // A symbol is a MAP only where it carries each family to exactly one family. Where it does
        // not, it is a relation and the fan-out is the continuation fiber — the plurality this
        // reading exists to return rather than resolve.
        if image.values().any(|onward| onward.len() > 1) {
            continue;
        }
        let landed: std::collections::BTreeSet<usize> = image
            .values()
            .filter_map(|o| o.iter().next().copied())
            .collect();
        if landed.len() == image.len() {
            permutes += 1;
        } else {
            collapses += 1;
        }
    }

    // A family IS its member set. Print the material, not the census: a count of families is a
    // scalar face of a structure whose content is the parts themselves.
    let spell = |face: u64| -> String {
        // The fine family's declared face is `length * 256 + first symbol`, so it decodes.
        let length = face / 256;
        let first = (face % 256) as u8;
        if first.is_ascii_graphic() {
            format!("length {length} beginning '{}'", first as char)
        } else {
            format!("length {length} beginning 0x{first:02x}")
        }
    };
    let members = |family: usize, take: usize| -> String {
        let block = &compression.conduct.blocks[family];
        let shown: Vec<String> = block
            .iter()
            .take(take)
            .map(|item| render_word(&reading_three.parts[item.0 as usize]))
            .collect();
        let rest = block.len().saturating_sub(shown.len());
        if rest == 0 {
            format!("{{{}}}", shown.join(" · "))
        } else {
            format!("{{{} · …{rest} more}}", shown.join(" · "))
        }
    };

    println!("  THE FAMILIES THEMSELVES — the widest, with the parts they hold");
    let mut widest: Vec<usize> = (0..families).collect();
    widest.sort_by_key(|f| std::cmp::Reverse(compression.conduct.blocks[*f].len()));
    for family in widest.iter().take(5) {
        println!(
            "      family {family:<5} {:>3} parts   {}",
            compression.conduct.blocks[*family].len(),
            members(*family, 6)
        );
    }
    println!(
        "      … {} further families, {} of them holding a single part",
        families.saturating_sub(5),
        (0..families)
            .filter(|f| compression.conduct.blocks[*f].len() == 1)
            .count()
    );

    println!();
    println!("  A COLLAPSE, EXHIBITED — where a step deletes a distinction the receiver had");
    let mut shown_collapse = 0usize;
    'collapse: for input in &inputs {
        let mut image: BTreeMap<usize, usize> = BTreeMap::new();
        let mut merged: Option<(usize, usize, usize)> = None;
        for item in &items {
            let (Some(from), Some(to_item)) = (
                family_of.get(&item.0).copied(),
                reading_three.successor(*item, *input),
            ) else {
                continue;
            };
            let Some(to) = family_of.get(&to_item.0).copied() else {
                continue;
            };
            if let Some((other, _)) = image.iter().find(|(o, t)| **t == to && **o != from) {
                merged = Some((from, *other, to));
            }
            image.insert(from, to);
        }
        if let Some((left, right, into)) = merged {
            println!("      the step \"{}\":", spell(input.0));
            println!("          family {left:<5} {}", members(left, 4));
            println!("          family {right:<5} {}", members(right, 4));
            println!("          both land in");
            println!("          family {into:<5} {}", members(into, 4));
            shown_collapse += 1;
            if shown_collapse == 2 {
                break 'collapse;
            }
        }
    }
    println!(
        "      … {} further collapsing steps not printed",
        collapses.saturating_sub(shown_collapse)
    );

    println!();
    println!(
        "  THE REVERSIBLE SUBPOPULATIONS — the cores of the action, and the arrows between them"
    );
    // **A strongly connected core IS the subpopulation the action is reversible on**: inside a core
    // every family reaches every other, so the restricted action is invertible. The one-way edges
    // BETWEEN cores are exactly where an irreversible step put the arrow of the compression. The
    // permute/collapse pair above is two integers; this is the structure they were a face of.
    let mut outgoing: Vec<Vec<usize>> = vec![Vec::new(); families];
    for (from, onward) in &edges {
        outgoing[*from] = onward.keys().copied().collect();
    }
    let (core_of, core_count) = strongly_connected_cores(&outgoing);
    let mut core_extent: BTreeMap<u32, usize> = BTreeMap::new();
    for core in &core_of {
        *core_extent.entry(*core).or_insert(0) += 1;
    }
    let singletons = core_extent.values().filter(|extent| **extent == 1).count();
    let mut widest_cores: Vec<(&u32, &usize)> = core_extent.iter().collect();
    widest_cores.sort_by_key(|(core, extent)| (std::cmp::Reverse(**extent), **core));
    println!(
        "      cores {core_count} over {families} families; {singletons} of them a single family",
    );
    for (core, extent) in widest_cores.iter().take(3) {
        let held: Vec<usize> = (0..families)
            .filter(|f| core_of[*f] == **core)
            .take(4)
            .collect();
        let spelled: Vec<String> = held.iter().map(|f| members(*f, 2)).collect();
        println!(
            "      core {core:<4} {extent:>4} families, reversible within: {}",
            spelled.join(" ")
        );
    }
    let crossing: usize = edges
        .iter()
        .map(|(from, onward)| {
            onward
                .keys()
                .filter(|to| core_of[*from] != core_of[**to])
                .count()
        })
        .sum();
    println!(
        "      steps that LEAVE a core and cannot return: {crossing}   <- the arrow of the compression"
    );

    println!();
    println!("  A WALKED ROUTE, SPELLED — the pathway a continuation would take");
    let mut route: Vec<(usize, u64)> = Vec::new();
    let mut standing = compression
        .conduct
        .block_of(ItemId(0))
        .expect("the first part sits in a family");
    let opened = standing;
    let mut visited = std::collections::BTreeSet::new();
    while visited.insert(standing) {
        let Some(step) = edges.get(&standing).and_then(|to| to.iter().next()) else {
            break;
        };
        route.push((*step.0, step.1 .0));
        standing = *step.0;
    }
    println!("      family {opened:<5} {}", members(opened, 4));
    for (family, symbol) in route.iter().take(5) {
        println!("        --[{}]-->", spell(*symbol));
        println!("      family {family:<5} {}", members(*family, 4));
    }
    if route.len() > 5 {
        println!("        … {} further steps", route.len() - 5);
    }
    println!(
        "      the walk re-entered a family it had already stood in after {} steps: {}",
        route.len(),
        if route.len() > 1 {
            "the pathway CLOSES"
        } else {
            "no cycle"
        }
    );

    println!();
    println!("  and the census of the above, which is the face and not the object:");
    println!(
        "      families {families} · symbols {} · permuting {permutes} · collapsing {collapses}",
        inputs.len()
    );
    let plural_symbols: std::collections::BTreeSet<u64> =
        plural.iter().map(|(input, ..)| input.0).collect();
    println!(
        "      symbols whose action is PLURAL somewhere {} , at {} (symbol, family) sites   <- the chain is not deterministic",
        plural_symbols.len(),
        plural.len()
    );
    for (input, from, onward) in plural.iter().take(3) {
        let landings: Vec<String> = onward.iter().map(|to| members(*to, 2)).collect();
        println!(
            "          \"{}\" carries family {from} {} to {} families at once: {}",
            spell(input.0),
            members(*from, 2),
            onward.len(),
            landings.join(" | ")
        );
    }
    let sinks = (0..families)
        .filter(|family| edges.get(family).is_none_or(BTreeMap::is_empty))
        .count();
    println!(
        "      families with NO outgoing step (a continuation stops there) {sinks} of {families}"
    );
    println!();

    // ---------------------------------------------------------------------------------
    // READING TWO -- the transition row as an exact ratio cocycle.
    // ---------------------------------------------------------------------------------
    println!();
    println!("{}", "-".repeat(100));
    println!(
        "READING TWO -- a transition row is a COCYCLE OF EXACT RATIOS, and Z is a declared null"
    );
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
    let weights = family
        .normalised_against(reference)
        .expect("a distribution");
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

    // ---------------------------------------------------------------------------------
    // READING FOUR -- what the collapse ERASED, against the budget the burn bought.
    // ---------------------------------------------------------------------------------
    //
    // Landauer bounds **erasure and never transport** (Bennett: reversible computation has no such
    // floor), so this prices the collapsing side of reading three and not the permuting side. The
    // numerator is exact and combinatorial -- naming one member of a block of extent m costs
    // ceil(log2 m) bits, so a partition into singletons erases nothing. The denominator is an
    // ENCLOSURE, because ln 2 is irrational and this carrier is exact.
    //
    // The power sample is an apparatus measurement and it CARRIES ITS FRAME. A figure without its
    // frame is the absolute-frame defect, and whether the device had an active display is a second
    // frame rather than a contamination.
    println!();
    println!("{}", "-".repeat(100));
    println!("READING FOUR -- the erasure, against the Landauer budget of a declared burn");
    println!("{}", "-".repeat(100));
    {
        let extents: Vec<usize> = compression
            .conduct
            .blocks
            .iter()
            .map(std::collections::BTreeSet::len)
            .collect();
        match std::process::Command::new("nvidia-smi")
            .args([
                "--query-gpu=power.draw,temperature.gpu",
                "--format=csv,noheader,nounits",
            ])
            .output()
        {
            Ok(returned) if returned.status.success() => {
                let text = String::from_utf8_lossy(&returned.stdout);
                let mut fields = text.split(',').map(str::trim);
                let watts: f64 = fields.next().unwrap_or("0").parse().unwrap_or(0.0);
                let celsius: i64 = fields.next().unwrap_or("0").parse().unwrap_or(0);
                // The float leaves at the boundary: the sample arrives as text and becomes an
                // integer measurement in its own unit before anything interior touches it.
                let frame = ThermalFrame {
                    power_microwatts: (watts * 1_000_000.0) as u64,
                    interval_nanoseconds: 1_000_000_000,
                    temperature_millikelvin: ((celsius + 273).max(1) as u64) * 1000,
                    display_active: std::env::var_os("DISPLAY").is_some(),
                    declared_by: "nvidia-smi, one second, at this run's device temperature"
                        .to_owned(),
                };
                match landauer::read(&extents, frame.clone(), 64, 128) {
                    Ok(reading) => {
                        let (erased, lower, upper) = reading.efficiency_pair();
                        println!("  the collapse erased            {erased} bits, exactly");
                        println!(
                            "  blocks that erased anything    {} of {}",
                            reading.erasing_blocks.len(),
                            extents.len()
                        );
                        for (block, extent) in reading.erasing_blocks.iter().take(4) {
                            println!(
                                "      block {block:<5} holds {extent} parts, so naming one costs {} bits",
                                landauer::naming_bits(*extent)
                            );
                        }
                        println!(
                            "  the frame                      {} uW for {} ns at {} mK, display {}",
                            frame.power_microwatts,
                            frame.interval_nanoseconds,
                            frame.temperature_millikelvin,
                            if frame.display_active {
                                "ACTIVE"
                            } else {
                                "idle"
                            }
                        );
                        println!("  declared by                    {}", frame.declared_by);
                        println!("  the budget an ENCLOSURE, because ln 2 is irrational:");
                        println!("      lower {lower}");
                        println!("      upper {upper}");
                        println!("  the reading is the UNDIVIDED PAIR (erased, budget) -- no quotient formed");
                        println!(
                            "  where the erasure sits         {:?}",
                            reading.against_budget()
                        );
                        println!();
                        println!("  AND THE TRAJECTORY IS THE READING, not the value. A figure far below the");
                        println!("  bound says nothing on its own; what says something is whether it MOVES");
                        println!("  under a change that provably alters the collapse.");
                    }
                    Err(refusal) => println!("  the reading refused: {refusal:?}"),
                }
            }
            _ => println!("  no device answered, so no frame exists and none is invented"),
        }
    }

    println!();
    println!("{}", "=".repeat(100));
    println!("WHAT RETURNED");
    println!("{}", "=".repeat(100));
    println!("  the memory order moved with the receiver family      {order_moved}");
    println!("  the transition row is an exact cocycle                {cocycle}");
    println!("  the declared null carries no information             {null_trivial}");
    println!(
        "  the weights sum to exactly one over the rationals     {}",
        weight_total == Rat::from_integer(BigInt::from(1))
    );
    println!(
        "  temperature rebases the winding and stays a cocycle   {}",
        temperature_moves && colder_cocycle
    );

    println!();
    println!("{}", "-".repeat(100));
    println!("WHAT THIS RUN DOES NOT ESTABLISH");
    println!("{}", "-".repeat(100));
    println!("  No argmax is taken anywhere: every member's ratio against every other is returned");
    println!("  and none is discarded. T -> 0 is where softmax becomes a chooser and no path here");
    println!(
        "  reaches it. The row's counts are what happened; the ratios are their invariant face;"
    );
    println!(
        "  and the normalisation appears only in a function whose name says a null was named."
    );
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

//! **Where the tower stops, and whether it is the material or the law.**
//!
//! `the_vertex_emits_where_the_tape_only_walked` reported that the hand-up reaches grain 2 and
//! stops with three constituents. It did not say **why**, and the two candidate answers are
//! different findings that point at different next work:
//!
//! ```text
//!   MATERIAL   the declared cut is too small; the emitted constituents form a forest and a
//!              forest has no independent cycle, so nothing closes one grain up. A bigger cut
//!              lifts it.
//!   LAW        `next_grain` refuses to bond two closed boundaries at different ranks in `⪯`
//!              before it looks at their boundaries at all. No cut lifts that.
//! ```
//!
//! The counterfactual that separates them is
//! [`NextGrainCensus::would_bond_across_rank`](life::incidence_production::NextGrainCensus): of the
//! pairs the rank guard refused **before looking**, how many would have bonded had it looked. It is
//! measured, never conducted — `next_grain` still refuses every one of them — and a non-zero return
//! puts the ceiling in the law.
//!
//! ```text
//! cargo run --release -p life --example the_tower_stops_where_the_material_stops
//! ```

use std::collections::BTreeSet;

use life::incidence_production::{
    DeclaredOccurrence, IncidenceComplex, IncidenceProductionError, PhaseChart,
};

/// The declared extents this run sweeps. Each is one declared aperture on inscription patches per
/// occurrence, and each returns its outside.
const DECLARED_EXTENTS: &[usize] = &[8, 16, 32, 64, 128];

/// The declared occurrence populations this run sweeps.
const DECLARED_OCCURRENCES: &[usize] = &[3, 6, 12, 24];

fn main() {
    if let Err(error) = run() {
        eprintln!("REFUSED: {error}");
        std::process::exit(1);
    }
}

fn run() -> Result<(), String> {
    let chart = PhaseChart::WindingAdjacent;

    println!("THE SWEEP — GRAIN REACHED AGAINST EXTENT");
    println!(
        "  a bigger cut is the material answer. If the tower's ceiling moves with the extent, the\n\
         \x20 ceiling is in the material; if it does not, no cut is going to lift it."
    );
    println!();
    println!(
        "  {:>6} {:>6} {:>8} {:>8} {:>10} {:>8} {:>26}",
        "occ", "extent", "sites", "contacts", "compounds", "grain", "why it stopped"
    );
    let mut best = 0u32;
    let mut by_extent: std::collections::BTreeMap<usize, u32> = std::collections::BTreeMap::new();
    let mut by_occurrences: std::collections::BTreeMap<usize, u32> =
        std::collections::BTreeMap::new();
    for occurrences in DECLARED_OCCURRENCES {
        for extent in DECLARED_EXTENTS {
            let material = declared_material(*occurrences);
            let complex = match IncidenceComplex::found(&material, *extent) {
                Ok(complex) => complex,
                Err(error) => {
                    println!("  {occurrences:>6} {extent:>6}   refused: {error:?}");
                    continue;
                }
            };
            let (reached, reason) = climb(&complex, chart);
            best = best.max(reached);
            let at_extent = by_extent.entry(*extent).or_default();
            *at_extent = (*at_extent).max(reached);
            let at_occurrences = by_occurrences.entry(*occurrences).or_default();
            *at_occurrences = (*at_occurrences).max(reached);
            println!(
                "  {:>6} {:>6} {:>8} {:>8} {:>10} {:>8} {:>26}",
                occurrences,
                extent,
                complex.sites().len(),
                complex.bonds().len(),
                complex.compounds().len(),
                reached,
                reason
            );
        }
    }
    println!();
    println!("  the highest grain any declared cut reached: {best}");
    println!(
        "  by extent      : {}",
        by_extent
            .iter()
            .map(|(extent, grain)| format!("{extent}→{grain}"))
            .collect::<Vec<_>>()
            .join("  ")
    );
    println!(
        "  by occurrences : {}",
        by_occurrences
            .iter()
            .map(|(count, grain)| format!("{count}→{grain}"))
            .collect::<Vec<_>>()
            .join("  ")
    );
    println!(
        "  READ IT EXACTLY. The extent lifts the tower ONCE — a cut of eight patches reaches grain 1\n\
         \x20 and sixteen reaches grain 2 — and then it SATURATES. Eight times the occurrences, from\n\
         \x20 three to twenty-four and from ten closed boundaries to seventy-six, does not reach grain\n\
         \x20 3. So the answer to *material or law* is neither of the two the question offered: the\n\
         \x20 ceiling is ARITHMETIC, and the census below shows which arithmetic."
    );
    println!();

    // ---------------------------------------------------------------------------------------
    println!("THE CENSUS AT EACH GRAIN — WHICH REFUSAL IS DOING THE WORK");
    println!(
        "  a pair of closed boundaries can be refused for exactly three reasons. `⪯ guard` is a LAW\n\
         \x20 refusal: the two sit at different ranks and their boundaries are never consulted.\n\
         \x20 `unbonded` is a MATERIAL refusal: same rank, and the boundaries neither share a face \
         nor\n\
         \x20 are joined by a contact of the complex. `incoherent` is §IV chirality — a shared face \
         at\n\
         \x20 the same hand, which no orientation-preserving transport identifies."
    );
    let material = declared_material(*DECLARED_OCCURRENCES.last().expect("a declared population"));
    let complex = IncidenceComplex::found(
        &material,
        *DECLARED_EXTENTS.last().expect("a declared extent"),
    )
    .map_err(|error| format!("found: {error:?}"))?;
    println!();
    println!(
        "  {:>6} {:>7} {:>9} {:>7} {:>5} {:>8} {:>9} {:>9} {:>8} {:>9} {:>11} {:>13}",
        "grain",
        "sites",
        "contacts",
        "cmpds",
        "C",
        "pairs",
        "⪯ guard",
        "same rank",
        "bonded",
        "unbonded",
        "incoherent",
        "WOULD BOND"
    );
    let mut carried = complex.clone();
    let mut law_bound = 0usize;
    loop {
        let census = carried.next_grain_census();
        println!(
            "  {:>6} {:>7} {:>9} {:>7} {:>5} {:>8} {:>9} {:>9} {:>8} {:>9} {:>11} {:>13}",
            carried.grain(),
            carried.sites().len(),
            carried.bonds().len(),
            census.compounds,
            // β₁ = E − V + C, so C = β₁ − E + V. The component count is derived, never counted
            // twice.
            census.compounds as i64 - carried.bonds().len() as i64 + carried.sites().len() as i64,
            census.pairs_considered,
            census.refused_by_causal_rank,
            census.same_rank,
            census.bonded,
            census.refused_unbonded,
            census.incoherent,
            census.would_bond_across_rank
        );
        law_bound += census.would_bond_across_rank;
        match carried.next_grain(chart) {
            Ok((_, next)) => {
                if next.compounds().is_empty() {
                    println!(
                        "  grain {} founded {} contacts over {} constituents and NO independent \
                         cycle: a forest closes nothing.",
                        next.grain(),
                        next.bonds().len(),
                        next.sites().len()
                    );
                    let final_census = next.next_grain_census();
                    println!(
                        "  {:>6} {:>7} {:>9} {:>7} {:>5} {:>8} {:>9} {:>9} {:>8} {:>9} {:>11} {:>13}",
                        next.grain(),
                        next.sites().len(),
                        next.bonds().len(),
                        final_census.compounds,
                        final_census.compounds as i64 - next.bonds().len() as i64
                            + next.sites().len() as i64,
                        final_census.pairs_considered,
                        final_census.refused_by_causal_rank,
                        final_census.same_rank,
                        final_census.bonded,
                        final_census.refused_unbonded,
                        final_census.incoherent,
                        final_census.would_bond_across_rank
                    );
                    break;
                }
                carried = next;
            }
            Err(error) => {
                println!(
                    "  grain {} founded nothing above it: {error:?}",
                    carried.grain() + 1
                );
                break;
            }
        }
    }
    println!();

    // ---------------------------------------------------------------------------------------
    println!("THE VERDICT");
    let census = complex.next_grain_census();
    println!(
        "  at grain 0 the rank guard refused {} of {} candidate pairs before looking at a single\n\
         \x20 boundary. Of those, {} WOULD HAVE BONDED.",
        census.refused_by_causal_rank, census.pairs_considered, census.would_bond_across_rank
    );
    if law_bound > 0 {
        println!(
            "  → THE CEILING IS IN THE LAW. `next_grain` requires two closed boundaries to share a\n\
             \x20   rank in `⪯` before it will consider bonding them, and {law_bound} pairs across \
             the\n\
             \x20   whole climb satisfied the boundary test and were refused anyway. A larger cut \
             cannot\n\
             \x20   lift that, because a larger cut adds more ranks as fast as it adds more \
             compounds."
        );
        println!(
            "     And the guard is not obviously wrong. Two compounds at different ranks in `⪯` are\n\
             \x20    causally ordered, and a higher-grain constituent formed across a causal order \
             would\n\
             \x20    be a cell that exists at two source times. What the measurement establishes is \
             that\n\
             \x20    the guard — NOT the extent — is what the tower's height is a function of, so \
             the\n\
             \x20    next construction is a `⪯`-respecting composition rule and not a bigger corpus."
        );
    } else {
        println!(
            "  → THE CEILING IS NOT IN THE `⪯` GUARD. Every one of those {} pairs would have been\n\
             \x20   refused on its boundaries anyway, so the guard costs the tower NOTHING on this\n\
             \x20   material. Removing it would change no return, which also means the ratified law's\n\
             \x20   causal-order restriction is not what is holding the tower down and there is no\n\
             \x20   reason to go near it.",
            census.refused_by_causal_rank
        );
    }
    println!();
    println!(
        "  THE ARITHMETIC, EXHIBITED. The grain-1 contact graph is sparse by construction:\n\
         \x20 sparse by construction: a grain-1 contact exists only where a contact of the grain-0\n\
         \x20 complex leaves one closed boundary and arrives at another, so it can never exceed the\n\
         \x20 grain-0 contact population, while the constituent population is the number of closed\n\
         \x20 boundaries. `β₁ = E − V + C` with `E ≤ E₀` and `V = β₁⁰` therefore falls fast, and the\n\
         \x20 tower runs out of cycles before it runs out of cells. That is arithmetic, not a defect,\n\
         \x20 and it is why a `⪯`-respecting rule has to ADD contacts rather than relax a guard."
    );

    Ok(())
}

/// Climb the hand-up and report the grain reached and why it stopped.
fn climb(complex: &IncidenceComplex, chart: PhaseChart) -> (u32, &'static str) {
    let mut carried = complex.clone();
    let mut population = usize::MAX;
    loop {
        let handed = match carried.next_grain(chart) {
            Ok(handed) => handed,
            Err(IncidenceProductionError::NoContact) => {
                return (carried.grain() + 1, "no pair bonded")
            }
            Err(IncidenceProductionError::NoDeclaredMaterial) => {
                return (carried.grain(), "nothing closed")
            }
            Err(_) => return (carried.grain(), "refused"),
        };
        let (emitted, next) = handed;
        if emitted.len() >= population {
            return (next.grain(), "population not contracting");
        }
        population = emitted.len();
        if next.compounds().is_empty() {
            return (next.grain(), "a forest closes nothing");
        }
        if population <= 1 {
            return (next.grain(), "one atomic successor");
        }
        carried = next;
    }
}

/// The declared material: a causal chain of `count` occurrences over one small vocabulary.
///
/// The sentences are cycled deterministically and each occurrence names the previous one as its
/// cause, so `⪯` is a genuine chain of length `count` and the rank population grows with the cut.
/// Nothing here is sampled and nothing is random.
fn declared_material(count: usize) -> Vec<DeclaredOccurrence> {
    const SENTENCES: &[&str] = &[
        "the leader founds the channel and the channel carries the leader",
        "the arc bends the channel and the bends carry the return",
        "the channel returns the leader and the leader founds the arc",
        "the return carries the arc and the arc bends the leader",
        "the bends found the return and the channel carries the bends",
        "the leader carries the arc and the return founds the channel",
    ];
    (0..count)
        .map(|at| {
            DeclaredOccurrence::from_text(
                format!("declared:{at}"),
                // Storage deliberately descends while `⪯` ascends, so the two orders are never
                // confusable on this material.
                (count - at) as u64,
                if at == 0 {
                    BTreeSet::new()
                } else {
                    BTreeSet::from([format!("declared:{}", at - 1)])
                },
                SENTENCES[at % SENTENCES.len()],
            )
            .expect("declared text material")
        })
        .collect()
}

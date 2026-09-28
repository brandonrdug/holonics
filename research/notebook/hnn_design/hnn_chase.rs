//! **The chase terrain's reception phase** (THE_REBUILD F6; `holonics::holarchy::terrain::chase`,
//! `holonics::receiver::population::ChaseFamily`): on hash-seeded arenas a fast runner flees a
//! scripted pursuer, and the receiver's population over the declared candidate runners reads its
//! passage. Count-only **development receipts** on terrain whose truth is exact, a committed
//! command run once in release, never a test.
//!
//! ```sh
//! cargo run --release -p holonics --example hnn_chase
//! ```
//!
//! [definition; agent-inferred] **The declaration** (the tests' own, `chase_tests.rs`): a `16 × 16`
//! arena of `4 × 4` friction patches, classes ice `1/2`, grass `1` and track `3/2`, `g = 8`,
//! `h = 1/2`, `ℓ = 1` (so `k = g h²/ℓ = 2`, and every class resolves on the lattice); the runner family of speeds `2, 3`, traction
//! coefficients `1, 3/2`, slip holds `1, 2` and the navigators flee, circle (both orientations) and
//! zig-zag at periods `2` and `3`, `40 = 2³·5` candidates named by `6` bits each; the pursuer of
//! speed `3/2` and traction `2`, capturing at `ρ² = 2`; escape mass `2^(−12)`; passages of at most
//! `2^8` ticks, ended by capture; seeds `SEED + s`, `s < 16`, the terrain notebook's seed.
//!
//! [definition] **Printed, exactly**, for each seed: the truth (the candidate, its key description,
//! the openings, the friction field's classes by patch count, the slips, wall meetings and the
//! capture tick, which ends the passage); the
//! population's code, the truth family's own code and their exact difference against the naming
//! margin; the landmark tree's code alone at each depth of `1, 2, 4, 8` over the same cells and the
//! population's ordering against its least; the selected family (posterior decided above one half)
//! or none; the population's selected fibre (its greatest posterior, read exactly) against the
//! surviving fibre (the candidates the passage never contradicts); the fibre's joint posterior;
//! and the fibre's future classes over every admitted pursuer word of five ticks, with a
//! separating word where one exists. Bits are enclosures with exact endpoints read at
//! `L_R = 16` as `n + k/16 + ε`; no decimal is printed.

#[path = "exterior.rs"]
mod exterior;

use std::time::Instant;

use holonics::compression::landmark::context::{
    Capacity, LandmarkDeclaration, LetterFamily, StopPrior,
};
use holonics::holarchy::terrain::{
    ArenaDeclaration, Chase, Constitution, Policy, Pursuer, RunnerFamily,
};
use holonics::ratio::algebraic::ExactInterval;
use holonics::ratio::surprisal::SymbolicSurprisal;
use holonics::ratio::{Rat, rat};
use holonics::receiver::population::{
    ChaseFamily, Family, Population, Posterior, TreeFamily, selected_fibre,
};
use num_bigint::{BigInt, BigUint};

use exterior::{against, difference, enclosure, per};

/// The terrain notebook's seed.
const SEED: u64 = 20_260_927;

/// The seeds read.
const SEEDS: u64 = 16;

/// The passage `2^8` ticks.
const TICKS: usize = 1 << 8;

/// The receiver's grain `L_R`.
const GRAIN: u64 = 16;

/// The escape exponent `j`.
const ESCAPE: u32 = 12;

/// The future classes' horizon.
const HORIZON: usize = 5;

/// The tree's depth ladder.
const DEPTHS: [usize; 4] = [1, 2, 4, 8];

fn declaration() -> ArenaDeclaration {
    ArenaDeclaration {
        width: 16,
        height: 16,
        patch: 4,
        classes: vec![rat(1, 2), rat(1, 1), rat(3, 2)],
        gravity: rat(8, 1),
        tick: rat(1, 2),
        spacing: rat(1, 1),
    }
}

fn family() -> RunnerFamily {
    RunnerFamily {
        speeds: vec![rat(2, 1), rat(3, 1)],
        tractions: vec![rat(1, 1), rat(3, 2)],
        holds: vec![1, 2],
        policies: vec![
            Policy::Flee,
            Policy::Circle { clockwise: false },
            Policy::Circle { clockwise: true },
            Policy::ZigZag { period: 2 },
            Policy::ZigZag { period: 3 },
        ],
    }
}

fn pursuer() -> Pursuer {
    Pursuer {
        constitution: Constitution {
            speed: rat(3, 2),
            traction: rat(2, 1),
        },
        capture: rat(2, 1),
    }
}

/// **An integer with its factorization**, `n = p^a·q^b…` (read from `log₂ n`'s exact form).
fn factored(value: &BigUint) -> String {
    if value <= &BigUint::from(1u32) {
        return value.to_string();
    }
    let form = SymbolicSurprisal::log2_of_ratio(&Rat::from_integer(BigInt::from(value.clone())))
        .expect("a positive integer");
    let factors: Vec<String> = form
        .terms()
        .iter()
        .map(|(prime, exponent)| {
            if exponent == &Rat::from_integer(BigInt::from(1)) {
                prime.to_string()
            } else {
                format!("{prime}^{exponent}")
            }
        })
        .collect();
    format!("{value} = {}", factors.join("·"))
}

fn tree(alphabet: usize, depth: usize, population: usize) -> LandmarkDeclaration {
    LandmarkDeclaration {
        alphabet,
        depth,
        forced: 0,
        population: population as u64,
        grain: GRAIN,
        family: LetterFamily::cells(),
        prior: StopPrior::half(),
        capacity: Capacity::Unbounded,
    }
}

fn posterior_line(posterior: &Posterior) -> String {
    match posterior {
        Posterior::Dead => "exactly 0 (dead)".to_string(),
        Posterior::Bits(bits) => format!("−log₂ w: {}", enclosure(bits, GRAIN)),
    }
}

fn main() {
    let declaration = declaration();
    let family = family();
    let pursuer = pursuer();
    let margin = family.description();
    println!(
        "hnn_chase: a {} × {} arena, patches of side {}, friction classes {:?}, g = {}, h = {}, ℓ = {} (k = g h²/ℓ = {}); {} candidate runners named by {} bits each; pursuer v = {}, γ = {}, capture ρ² = {}; escape 2^(−{ESCAPE}); at most n = {TICKS} = 2^8 ticks",
        declaration.width,
        declaration.height,
        declaration.patch,
        declaration
            .classes
            .iter()
            .map(ToString::to_string)
            .collect::<Vec<_>>(),
        declaration.gravity,
        declaration.tick,
        declaration.spacing,
        declaration.scale(),
        factored(&BigUint::from(family.len())),
        margin,
        pursuer.constitution.speed,
        pursuer.constitution.traction,
        pursuer.capture,
    );
    let (mut within, mut below, mut in_fibre, mut singletons) = (0, 0, 0, 0);
    for s in 0..SEEDS {
        let seed = SEED + s;
        let started = Instant::now();
        let chase =
            Chase::draw(&declaration, &family, &pursuer, TICKS, seed).expect("a drawn chase");
        let truth = &chase.truth;
        let moves = &chase.ports.moves;
        println!();
        println!("seed {seed}:");
        println!("  the truth: [{}] {}", truth.index, truth.runner.label());
        println!(
            "    key space {} (⌈log₂⌉ = {} bits); openings runner {:?}, pursuer {:?}",
            factored(&truth.key_space),
            truth.key_bits,
            truth.runner_start,
            truth.chaser_start
        );
        let patches = chase.ports.arena.patches();
        let counts: Vec<usize> = (0..declaration.classes.len())
            .map(|class| patches.iter().filter(|&&c| c == class).count())
            .collect();
        println!(
            "    friction patches by class (ice, grass, track): {counts:?} of {}",
            patches.len()
        );
        println!(
            "    the runner's slips: {} onsets, {} slipping ticks; wall meetings: {}; alphabet {} letters ({} moves, slip, wall)",
            truth.slips,
            truth.slip_ticks,
            truth.walls,
            moves.alphabet(),
            moves.vectors().len()
        );
        let ticks = chase.cells.len();
        match truth.captured {
            Some(tick) => println!("    captured at tick {tick}: the passage holds {ticks} cells"),
            None => println!("    not captured: the passage holds {ticks} cells"),
        }
        let mut population = Population::new(
            ChaseFamily::declare(&chase, &family, ESCAPE).expect("the declared candidates"),
        )
        .expect("a declared population");
        population
            .receive_passage(&chase.cells)
            .expect("the passage");
        let receipt = population.receipt().expect("the population's receipt");
        let truth_code = receipt.families[truth.index]
            .code
            .clone()
            .expect("the truth lives");
        println!(
            "  the population's code −log₂ Σ π_f L_f: {}",
            enclosure(&receipt.code, GRAIN)
        );
        println!("    a tick: {}", per(&receipt.code, ticks as u64, GRAIN));
        println!(
            "  the truth family's own code −log₂ L: {}",
            enclosure(&truth_code, GRAIN)
        );
        println!(
            "  the population's code − the truth's: {}",
            difference(&receipt.code, &truth_code, GRAIN)
        );
        let margin_rat = Rat::from_integer(BigInt::from(margin));
        let is_within = &receipt.code.upper - &truth_code.lower <= margin_rat;
        within += usize::from(is_within);
        println!("    within the naming margin of {margin} bits: {is_within}");
        let mut least: Option<ExactInterval> = None;
        for depth in DEPTHS {
            let mut tree_family =
                TreeFamily::new(tree(moves.alphabet(), depth, ticks), 0).expect("a declared tree");
            for &cell in &chase.cells {
                tree_family.receive(cell).expect("a tree cell");
            }
            let code = tree_family
                .likelihood()
                .code()
                .expect("a code")
                .expect("a tree never dies");
            println!(
                "  the landmark tree D = {depth}, code alone: {}",
                enclosure(&code, GRAIN)
            );
            if least.as_ref().is_none_or(|l| code.lower < l.lower) {
                least = Some(code);
            }
        }
        let least = least.expect("a ladder");
        let is_below = receipt.code.upper < least.lower;
        below += usize::from(is_below);
        println!(
            "  the population against the tree's least: {} by {}",
            against(&receipt.code, &least),
            difference(&receipt.code, &least, GRAIN)
        );
        match receipt.selected {
            Some(index) => println!(
                "  selected (posterior decided above ½): {}",
                receipt.families[index].label
            ),
            None => println!("  selected: none decided above ½"),
        }
        let fibre = chase.fibre(&family).expect("the fibre");
        let chosen = selected_fibre(&population);
        println!(
            "  the surviving fibre: {} of {} candidates; the population's selected fibre is it: {}; the truth in it: {}",
            fibre.len(),
            family.len(),
            chosen == fibre,
            fibre.contains(&truth.index)
        );
        in_fibre += usize::from(chosen == fibre && fibre.contains(&truth.index));
        singletons += usize::from(fibre.len() == 1);
        for &index in &fibre {
            println!("    {}", receipt.families[index].label);
        }
        println!(
            "  the fibre's joint posterior {}",
            posterior_line(&population.posterior_of(&fibre).expect("a posterior"))
        );
        let futures = chase
            .futures(&family, &fibre, &pursuer, HORIZON)
            .expect("the future classes");
        let classes: Vec<Vec<usize>> = futures.classes.clone();
        println!(
            "  future classes over {} admitted pursuer words of {} ticks: {} {classes:?} (the truth's first)",
            futures.words,
            futures.horizon,
            classes.len()
        );
        match &futures.separating {
            Some(word) => println!("    a separating pursuer word (positions by tick): {word:?}"),
            None => println!("    no admitted word separates the fibre within the horizon"),
        }
        println!(
            "  read in {} ms (exterior wall)",
            started.elapsed().as_millis()
        );
    }
    println!();
    println!(
        "over {SEEDS} seeds: the selected fibre is the surviving fibre and holds the truth on {in_fibre}; a single candidate survives on {singletons}; the population's code lies within the naming margin on {within} and strictly below the tree's least on {below}"
    );
}

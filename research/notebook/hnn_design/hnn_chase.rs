//! **The chase terrain: its reception phase and its action phase** (THE_REBUILD F6;
//! `holonics::holarchy::terrain::{chase, pursuit}`, `holonics::receiver::population::{ChaseFamily,
//! MachineChaser}`): on hash-seeded arenas a fast runner flees a chaser. In the reception phase a
//! scripted pursuer chases and the receiver's population over the declared candidate runners reads
//! the passage; in the action phase the machine chases, reading the runner through that population,
//! against pure pursuit and constant bearing under the same traction bound. Count-only **development
//! receipts** on terrain whose truth is exact, committed commands run once in release, never a test.
//!
//! ```sh
//! cargo run --release -p holonics --example hnn_chase             # the reception phase
//! cargo run --release -p holonics --example hnn_chase -- choose   # the action phase's choosing sweep
//! cargo run --release -p holonics --example hnn_chase -- action   # the action phase's acceptance
//! ```
//!
//! [definition; agent-inferred] **The declaration** (the tests' own, `chase_tests.rs`): a `16 × 16`
//! arena of `4 × 4` friction patches, classes ice `1/2`, grass `1` and track `3/2`, `g = 8`,
//! `h = 1/2`, `ℓ = 1` (so `k = g h²/ℓ = 2`, and every class resolves on the lattice); the runner
//! family of speeds `2, 3`, traction coefficients `1, 3/2`, slip holds `1, 2` and the navigators
//! flee, circle (both orientations) and zig-zag at periods `2` and `3`, `40 = 2³·5` candidates named
//! by `6` bits each; the pursuer (and every chaser) of speed `3/2` and traction `2`, capturing at
//! `ρ² = 2`; escape mass `2^(−12)`; seeds `SEED + s`, `s < 16`, the terrain notebook's seed.
//!
//! [definition] **The reception phase, printed exactly**, for each seed, over passages of at most
//! `2^8` ticks ended by capture: the truth (the candidate, its key description, the openings, the
//! friction field's classes by patch count, the slips, wall meetings and the capture tick); the
//! population's code, the truth family's own code and their exact difference against the naming
//! margin; the landmark tree's code alone at each depth of `1, 2, 4, 8` over the same cells and the
//! population's ordering against its least; the selected family (posterior decided above one half)
//! or none; the population's selected fibre against the surviving fibre; the fibre's joint
//! posterior; and the fibre's future classes over every admitted pursuer word of five ticks, with a
//! separating word where one exists. Bits are enclosures with exact endpoints read at `L_R = 16` as
//! `n + k/16 + ε`; no decimal is printed.
//!
//! [definition; agent-inferred] **The action phase.** Passages of at most `2^9` ticks from the
//! reception's draw (the same candidate, arena and openings a seed names), ended by capture, for the
//! machine and both controls. The machine's free parameters (the viable tube's horizon `n`, the
//! capture basin's horizon `m`, the price `d` of a probing tick; `receiver::population::chaser`)
//! are chosen by `choose` on the pinned **choosing seeds** `CHOOSING_SEED + s`, `s < 16`, disjoint
//! from the acceptance seeds: first `n ∈ {2, 3, 4}` by `m ∈ {4, 8, 12, 16}` at `d = 0`, then
//! `d ∈ {0, 1, 4, 16, 64, 256}` at the chosen `(n, m)`; the rule is the least sum of capture ticks
//! (an uncaptured passage counts its cap, a lower bound), then the most seeds won against both
//! controls, then the least work. The cornering receipt's horizon is declared, not chosen: `4`
//! ticks, over which the runner's top speed `3` carries it `12` lattice steps, three quarters of the
//! arena's side.
//!
//! [definition] **The action phase, printed exactly**, for each acceptance seed: the truth; the
//! capture tick of the machine, pure pursuit and constant bearing (or none within the cap); the
//! truth-only capture basin's least capture from the opening (every adaptive chaser strategy that
//! knows the truth, a lower bound for any chaser, read to at most `16` ticks and to at most the
//! machine's own capture); the cornering receipt, the runner's viable tube at horizon `4` under the
//! truth's constitution summed over each passage and over the ticks before the first of the three
//! captures; the runner's slips (onsets and slipping ticks) and wall meetings under each chaser;
//! the machine's releases (certified, commits, probes), the misses of its predicted consequence and
//! the fibre's size at its last tick. Then the sums, the seeds won, and the verdict against F6's
//! acceptance: capture in strictly fewer ticks than both controls in sum and in more than half of
//! the seeds. `action trace` prints each passage's tube sizes tick by tick as well.

#[path = "exterior.rs"]
mod exterior;

use std::time::Instant;

use holonics::compression::landmark::context::{
    Capacity, LandmarkDeclaration, LetterFamily, StopPrior,
};
use holonics::holarchy::terrain::{
    ActionDeclaration, ActionPassage, ArenaDeclaration, Basin, BasinMemo, Candidate, Chase,
    ConstantBearing, Constitution, Motion, Moves, Policy, PurePursuit, Pursuer, RunnerFamily,
    act_drawn,
};
use holonics::ratio::algebraic::ExactInterval;
use holonics::ratio::surprisal::SymbolicSurprisal;
use holonics::ratio::{Rat, rat};
use holonics::receiver::population::{
    ChaseFamily, Family, MachineChaser, MachineDeclaration, MachineReceipt, Population, Posterior,
    Release, TreeFamily, selected_fibre,
};
use num_bigint::{BigInt, BigUint};

use exterior::{against, difference, enclosure, per};

/// The terrain notebook's seed.
const SEED: u64 = 20_260_927;

/// The seeds read.
const SEEDS: u64 = 16;

/// [definition; agent-inferred] **The choosing seeds** `CHOOSING_SEED + s`, `s < 16`: pinned, disjoint
/// from the acceptance seeds `SEED + s`; the action phase's free parameters are chosen on them alone.
const CHOOSING_SEED: u64 = 20_261_001;

/// The action passage's cap, `2^9` ticks.
const ACTION_TICKS: usize = 1 << 9;

/// [definition; agent-inferred, chosen on the choosing seeds] **The machine's viable tube horizon**
/// `n`: every rung of `n ∈ {2, 3, 4}` at `m = 12` read the same least sum; ties go to the least work.
const TUBE_HORIZON: usize = 2;

/// [definition; agent-inferred, chosen on the choosing seeds] **The machine's capture basin horizon**
/// `m`: `m = 12` and `m = 16` read the least sum, `150` ticks; ties go to the least work.
const BASIN_HORIZON: usize = 12;

/// [definition; agent-inferred, chosen on the choosing seeds] **The price `d` of a probing tick**:
/// every rung of `d ∈ {0, 1, 4, 16, 64, 256}` read the same 150 ticks and no probe fired; ties go to
/// the least rung.
const PRICE: u64 = 0;

/// [definition; agent-inferred] **The cornering receipt's horizon** (module header), declared.
const RECEIPT_HORIZON: usize = 4;

/// The truth-only basin's reading limit.
const OPTIMUM_LIMIT: usize = 16;

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
    let mode: Vec<String> = std::env::args().skip(1).collect();
    match mode.first().map(String::as_str) {
        Some("choose") => choose(&mode[1..]),
        Some("action") => action(mode.get(1).is_some_and(|a| a == "trace")),
        _ => reception(),
    }
}

/// The machine of a declaration.
fn machine(horizon: usize, basin: usize, price: u64) -> MachineChaser {
    MachineChaser::new(MachineDeclaration {
        family: family(),
        escape: ESCAPE,
        horizon,
        basin,
        price,
    })
    .expect("a declared machine")
}

/// **One seed's three passages**: the machine at a tube horizon, basin horizon and price, pure
/// pursuit and constant bearing, the cornering receipt at its declared horizon; the machine's
/// receipt, its fibre's size at its last tick and its wall time.
fn passages(
    seed: u64,
    horizon: usize,
    basin: usize,
    price: u64,
) -> ([ActionPassage; 3], MachineReceipt, usize, u128) {
    let declaration = declaration();
    let family = family();
    let action = ActionDeclaration {
        pursuer: pursuer(),
        ticks: ACTION_TICKS,
        horizon: RECEIPT_HORIZON,
    };
    let started = Instant::now();
    let mut chaser = machine(horizon, basin, price);
    let m = act_drawn(&declaration, &family, &action, seed, &mut chaser).expect("the machine");
    let ms = started.elapsed().as_millis();
    let fibre = chaser.fibre().len();
    let p = act_drawn(&declaration, &family, &action, seed, &mut PurePursuit).expect("pursuit");
    let b = act_drawn(&declaration, &family, &action, seed, &mut ConstantBearing).expect("bearing");
    ([m, p, b], chaser.receipt().clone(), fibre, ms)
}

/// A comma list of a ladder's rungs.
fn ladder<T>(arg: Option<&String>, default: &[T]) -> Vec<T>
where
    T: std::str::FromStr + Clone,
    T::Err: std::fmt::Debug,
{
    arg.map_or(default.to_vec(), |a| {
        a.split(',').map(|r| r.parse().expect("a rung")).collect()
    })
}

/// **The choosing sweep** (module header): each rung over the choosing seeds, its sums, the seeds
/// it wins against each control and its work.
fn choose(args: &[String]) {
    let horizons: Vec<usize> = ladder(args.first(), &[2, 3, 4]);
    let basins: Vec<usize> = ladder(args.get(1), &[4, 8, 12, 16]);
    let prices: Vec<u64> = ladder(args.get(2), &[0]);
    println!(
        "hnn_chase choose: choosing seeds {CHOOSING_SEED} + s, s < {SEEDS}; passages of at most {ACTION_TICKS} = 2^9 ticks"
    );
    for &horizon in &horizons {
        for &basin in &basins {
            for &price in &prices {
                let started = Instant::now();
                let (mut sums, mut wins) = ([0usize; 3], [0usize; 2]);
                let mut line = Vec::new();
                for s in 0..SEEDS {
                    let ([m, p, b], receipt, _, _) =
                        passages(CHOOSING_SEED + s, horizon, basin, price);
                    for (sum, passage) in sums.iter_mut().zip([&m, &p, &b]) {
                        *sum += passage.ticks();
                    }
                    wins[0] += usize::from(m.ticks() < p.ticks());
                    wins[1] += usize::from(m.ticks() < b.ticks());
                    line.push(format!(
                        "[{}] {}/{}/{} p{}",
                        m.index,
                        m.ticks(),
                        p.ticks(),
                        b.ticks(),
                        receipt.count(Release::Probe)
                    ));
                }
                println!(
                    "n = {horizon}, m = {basin}, d = {price}: capture ticks in sum machine {}, pursuit {}, bearing {}; seeds won {} against pursuit, {} against bearing, of {SEEDS}; {} ms",
                    sums[0],
                    sums[1],
                    sums[2],
                    wins[0],
                    wins[1],
                    started.elapsed().as_millis()
                );
                println!("  machine/pursuit/bearing: {}", line.join("  "));
            }
        }
    }
}

/// **The truth-only capture basin's least capture** from the opening, within `limit` ticks: every
/// adaptive chaser strategy that knows the truth's law (`pursuit::Basin` on the truth alone).
fn least_capture(seed: u64, limit: usize) -> Option<usize> {
    let declaration = declaration();
    let family = family();
    let pursuer = pursuer();
    let (index, arena, openings) = Chase::drawn(&declaration, &family, seed).expect("a draw");
    let moves = family.moves(&declaration).expect("the alphabet");
    let caps = pursuer.constitution.caps(&declaration).expect("the caps");
    let disk = Moves::within(caps.top()).expect("the disk");
    let truth: Vec<Candidate> = Candidate::opening(&family, &arena, openings[0])
        .expect("the candidates")
        .into_iter()
        .filter(|candidate| candidate.index == index)
        .collect();
    let basin = Basin {
        arena: &arena,
        moves: &moves,
        pursuer: &pursuer,
        caps: &caps,
        disk: &disk,
    };
    basin
        .capture_ticks(
            &mut BasinMemo::default(),
            Motion::rest(openings[1]),
            0,
            &truth,
            limit,
        )
        .expect("the basin")
}

/// A capture tick, or none within the cap.
fn capture_line(passage: &ActionPassage) -> String {
    match passage.captured {
        Some(tick) => tick.to_string(),
        None => format!("none by {ACTION_TICKS}"),
    }
}

/// **The action phase's acceptance** (module header) on the acceptance seeds.
fn action(trace: bool) {
    let declaration = declaration();
    let pursuer = pursuer();
    println!(
        "hnn_chase action: a {} × {} arena, patches of side {}, classes {:?}; {} candidate runners; every chaser v = {}, γ = {}, capture ρ² = {}; the machine n = {TUBE_HORIZON}, m = {BASIN_HORIZON}, d = {PRICE}, escape 2^(−{ESCAPE}); the cornering receipt's horizon {RECEIPT_HORIZON}; passages of at most {ACTION_TICKS} = 2^9 ticks; acceptance seeds {SEED} + s, s < {SEEDS}",
        declaration.width,
        declaration.height,
        declaration.patch,
        declaration
            .classes
            .iter()
            .map(ToString::to_string)
            .collect::<Vec<_>>(),
        family().len(),
        pursuer.constitution.speed,
        pursuer.constitution.traction,
        pursuer.capture,
    );
    let names = ["the machine", "pure pursuit", "constant bearing"];
    let (mut sums, mut kernels, mut prefixes) = ([0usize; 3], [0usize; 3], [0usize; 3]);
    let (mut slips, mut walls) = ([(0usize, 0usize); 3], [0usize; 3]);
    let (mut wins, mut both, mut optimal) = ([0usize; 2], 0usize, 0usize);
    let (mut releases, mut misses) = ([0usize; 3], 0usize);
    for s in 0..SEEDS {
        let seed = SEED + s;
        let (runs, receipt, fibre, ms) = passages(seed, TUBE_HORIZON, BASIN_HORIZON, PRICE);
        let [m, p, b] = &runs;
        println!();
        println!("seed {seed}: the truth [{}] {}", m.index, m.runner.label());
        println!(
            "  capture tick: the machine {}, pure pursuit {}, constant bearing {}",
            capture_line(m),
            capture_line(p),
            capture_line(b)
        );
        let limit = m
            .captured
            .map_or(OPTIMUM_LIMIT, |tick| tick.min(OPTIMUM_LIMIT));
        let started = Instant::now();
        match least_capture(seed, limit) {
            Some(least) => {
                optimal += usize::from(m.captured == Some(least));
                println!(
                    "  the truth-only basin's least capture from the opening: {least} ({} ms)",
                    started.elapsed().as_millis()
                )
            }
            None => println!(
                "  the truth-only basin's least capture from the opening: none within {limit} ({} ms)",
                started.elapsed().as_millis()
            ),
        }
        let first = runs.iter().map(ActionPassage::ticks).min().expect("three");
        for (i, passage) in runs.iter().enumerate() {
            sums[i] += passage.ticks();
            let (kernel, prefix) = (passage.kernel_sum(usize::MAX), passage.kernel_sum(first));
            kernels[i] += kernel;
            prefixes[i] += prefix;
            slips[i].0 += passage.slips;
            slips[i].1 += passage.slip_ticks;
            walls[i] += passage.walls;
            println!(
                "  {}: tube sum {kernel} over {} ticks, {prefix} over the first {first}; slips {} onsets, {} slipping ticks; wall meetings {}",
                names[i],
                passage.tubes.len(),
                passage.slips,
                passage.slip_ticks,
                passage.walls
            );
            if trace {
                let sizes: Vec<String> = passage
                    .tubes
                    .iter()
                    .map(|tube| tube.size().to_string())
                    .collect();
                println!("    tube by tick: {}", sizes.join(" "));
            }
        }
        wins[0] += usize::from(m.ticks() < p.ticks());
        wins[1] += usize::from(m.ticks() < b.ticks());
        both += usize::from(m.ticks() < p.ticks() && m.ticks() < b.ticks());
        let counts = [
            receipt.count(Release::Certified),
            receipt.count(Release::Commit),
            receipt.count(Release::Probe),
        ];
        for (total, count) in releases.iter_mut().zip(counts) {
            *total += count;
        }
        misses += receipt.misses;
        println!(
            "  the machine: {} certified, {} commits, {} probes; its predicted consequence missed on {} ticks; the fibre at its last tick {}; read in {ms} ms",
            counts[0], counts[1], counts[2], receipt.misses, fibre
        );
    }
    println!();
    println!(
        "over {SEEDS} seeds: capture ticks in sum the machine {}, pure pursuit {}, constant bearing {} (an uncaptured passage counts its cap {ACTION_TICKS})",
        sums[0], sums[1], sums[2]
    );
    println!(
        "  the machine strictly fewer on {} seeds against pure pursuit, {} against constant bearing, {} against both; at the truth-only basin's least capture on {optimal}",
        wins[0], wins[1], both
    );
    println!(
        "  the cornering receipt (tube sums at horizon {RECEIPT_HORIZON}): over each passage {} / {} / {}; over the ticks before the first capture {} / {} / {}",
        kernels[0], kernels[1], kernels[2], prefixes[0], prefixes[1], prefixes[2]
    );
    println!(
        "  the runner's slips (onsets, slipping ticks) {:?} / {:?} / {:?}; wall meetings {} / {} / {}",
        slips[0], slips[1], slips[2], walls[0], walls[1], walls[2]
    );
    println!(
        "  the machine's releases: {} certified, {} commits, {} probes; predicted consequence missed on {misses} ticks",
        releases[0], releases[1], releases[2]
    );
    let fewer_in_sum = sums[0] < sums[1] && sums[0] < sums[2];
    let verdict = |passed: bool| if passed { "passed" } else { "not passed" };
    println!(
        "  F6's action acceptance, fewer ticks than both controls in sum and on more than half of the seeds, each seed against both at once: {}",
        verdict(fewer_in_sum && 2 * both > SEEDS as usize)
    );
    println!(
        "  read against each control separately: {}",
        verdict(fewer_in_sum && 2 * wins[0] > SEEDS as usize && 2 * wins[1] > SEEDS as usize)
    );
}

fn reception() {
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

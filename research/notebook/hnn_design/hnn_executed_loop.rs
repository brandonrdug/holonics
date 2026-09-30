//! **The executed comparison's loop** (THE_REBUILD U6; the
//! [diagnosis record](../../records/2026-09-30_THE_LEARNING_FAILURE_DIAGNOSED_THE_TRAINED_COMPARISON_IS_NOT_THE_ONE_THE_RELEASE_EXECUTES.md)
//! §5; #73, #148, #63): `hnn::executed` read on the order-2 terrain at `E` alone.
//!
//! ```sh
//! cargo run --release -p holonics --example hnn_prediction -- executed move <seed> <requests>
//! cargo run --release -p holonics --example hnn_prediction -- executed train <arm> <terrain> <seed> <batch> <moves> <deadline ms> <out>
//! cargo run --release -p holonics --example hnn_prediction -- executed evaluate <terrain> <seed> <count> <out> opening <label=E>…
//! cargo run --release -p holonics --example hnn_prediction -- executed spread <terrain> <seed> <count> opening <label=E>…
//! cargo run --release -p holonics --example hnn_prediction -- executed counts <terrain> <training seed> <count> <validation seed> <count> <out>
//! ```
//!
//! - **The two counts** (U6 step 1, loop 1a; the
//!   [pin](../../records/2026-09-30_THE_TWO_COUNTS_PINNED_BEFORE_ITS_RUNS.md)): `executed counts`
//!   reads the declared reference family (lag `ℓ ∈ [1, 40]`, a map of `ℤ/4`; the line in the
//!   hierarchical family too) along the machine's own training passage, its survivors at every
//!   observation, `n*_terrain` at the stopping object and its certificate; read-only
//!   instrumentation, never passed to the machine. `executed train` prints D1 (the step's descent)
//!   and D2 (the comparison's operating point) on every move and writes the constitution after
//!   moves 1, 2, 4, 8 and 16 (`<out>.m<k>`); `executed evaluate` reads constant and nonconstant
//!   requests apart with the success rule (every nonconstant section whole).
//!
//! - **`executed train`, `executed evaluate`** (Stage 2, the
//!   [pin](../../records/2026-09-30_THE_EXECUTED_COMPARISONS_BOUNDED_TEST_PINNED_BEFORE_ITS_RUNS.md)):
//!   one arm (the executed comparison, `executed-open` or `executed-partition`) trained from the
//!   declared opening by the one ladder, its `E` written; every constitution's confirmation from the
//!   open section, its counts and every section. (Stage 2's `face` arm, the bank's face as the
//!   comparison, was retired on September 30 with batch N2; its source is at `7ca300bb`.)
//! - **`executed spread`** (a diagnostic after Stage 2, never a pinned run): at the open section, the
//!   target's and the termination's ranks among each station's candidates, the station terms and the
//!   readings' spread.
//!
//! - **`executed move`** (Stage 1): one committed move of `E` on the release's own comparison, from
//!   the declared opening (`Constitution::initial`), on `requests` order-2 requests drawn at `seed`,
//!   each compared along the machine's own open-section trajectory. Printed whole: every request's
//!   release before and after (lock order, locks, their readings, holds and refusals), every
//!   refinement's class, threshold and order predicates, the proposal, every trial step with its
//!   guards, the adopted successor's carried step, and the requirements' receipts (the monodromy's
//!   variation forward and in reverse, the three routes of the covector's pairing, and the pairing
//!   against the exact change of the readings).

use super::*;
use holonics::hnn::executed::{
    BatchComparison, Context, ExecutedMove, Predicate, Request, SlopeSplit, executed_move,
    pairing_receipt,
};
use holonics::hnn::prediction::BankPlacement;
use holonics::hnn::ring::{MemberCovector, turn};
use num_bigint::{BigInt, BigUint};
use num_traits::One;
use std::collections::BTreeSet;

/// An enclosure read at the grain `1/g`: the cells `[⌊g·lower⌋/g, (⌊g·upper⌋ + 1)/g)` it lies in.
pub(super) fn cell(interval: &ExactInterval, grain: i64) -> String {
    let g = Rat::from_integer(grain.into());
    let low = (&interval.lower * &g).floor().to_integer();
    let high = (&interval.upper * &g).floor().to_integer() + BigInt::from(1);
    format!("[{low}/{grain}, {high}/{grain})")
}

fn predicate(p: Predicate) -> &'static str {
    match p {
        Predicate::Holds => "holds",
        Predicate::Fails => "fails",
        Predicate::Undecided => "undecided",
    }
}

/// Every request's release and predicates, whole.
pub(super) fn print_batch(label: &str, batch: &BatchComparison, targets: &[Vec<usize>]) {
    println!(
        "  {label}: F ∈ {} nats over {} readings; class and threshold hold at {} of {} compared stations",
        cell(&batch.value, 1 << 16),
        batch.readings,
        batch.holding().0,
        batch.holding().1
    );
    let (whole, right, released) = batch.sections(targets);
    println!(
        "  {label}: sections released {released} of {}, whole sections equal to their targets {whole}, stations right {right}",
        targets.len()
    );
    for (index, (request, target)) in batch.requests.iter().zip(targets).enumerate() {
        let Some(generation) = &request.generation else {
            continue;
        };
        println!(
            "    request {index}: target {target:?}; {} {:?}; lock order {:?}; refused lock {:?}; refinements {}, readings {}, members certified {} of {}, ticks closed {} of {}",
            if generation.release.released() { "released" } else { "held" },
            generation.release.classes,
            generation.locks,
            generation.uncertified,
            generation.refinements,
            generation.readings,
            generation.certified,
            generation.members,
            generation.ticks_closed,
            generation.ticks
        );
        for (station, class, growth, runner) in &generation.decisions {
            println!(
                "      lock station {station} class {class} ({}): joint [{}, {}], runner-up [{}, {}]",
                if *class == target[*station] { "right" } else { "wrong" },
                growth.lower,
                growth.upper,
                runner.lower,
                runner.upper
            );
        }
        for order in &request.orders {
            let stations: Vec<String> = request
                .stations
                .iter()
                .filter(|s| s.context == order.context)
                .map(|s| {
                    format!(
                        "{}:{}→{} class {} threshold {} f ∈ {}",
                        s.station,
                        s.top,
                        s.target,
                        predicate(s.class),
                        predicate(s.threshold),
                        cell(&s.value, 1 << 8)
                    )
                })
                .collect();
            println!(
                "      refinement {}: eligible {:?}; locked {:?}; order {}; stations {}",
                order.context,
                order
                    .eligible
                    .iter()
                    .map(|(s, top, gap, right)| format!("{s}:{top} gap {gap} {}", if *right { "right" } else { "wrong" }))
                    .collect::<Vec<_>>(),
                order.locked,
                match order.safe {
                    Some(true) => "safe",
                    Some(false) => "unsafe",
                    None => "held",
                },
                stations.join("; ")
            );
        }
    }
}

/// **A known-truth terrain's pairs** (only the terrain computes truth): `order2`, `x_t = x_(t−2) + 1
/// (mod 4)` after 40 drawn cells; `alternation`, two drawn classes alternating, `x_t = x_(t−2)`;
/// `line`, a drawn start and step, `x_t = x_0 + s t (mod 4)`.
pub(super) fn terrain_pairs(
    terrain: &str,
    declared: &Declared,
    seed: u64,
    count: usize,
) -> Vec<(Vec<usize>, Vec<usize>)> {
    let symbols = declared.alphabet - 1;
    let (n, m) = (declared.request, declared.stations);
    let mut draw = Draw::new(seed);
    match terrain {
        "order2" => order_pairs(declared, seed, count),
        "alternation" => (0..count)
            .map(|_| {
                let (a, b) = (draw.below(symbols), draw.below(symbols));
                let mut passage: Vec<usize> =
                    (0..n + m).map(|t| if t % 2 == 0 { a } else { b }).collect();
                let target = passage.split_off(n);
                (passage, target)
            })
            .collect(),
        "line" => (0..count)
            .map(|_| {
                let (x0, s) = (draw.below(symbols), draw.below(symbols));
                let mut passage: Vec<usize> = (0..n + m).map(|t| (x0 + s * t) % symbols).collect();
                let target = passage.split_off(n);
                (passage, target)
            })
            .collect(),
        _ => panic!("a terrain: order2 | alternation | line"),
    }
}

/// The source port as rows of rationals (`E rows cols`, then its realified rows).
fn write_port(theta: &Constitution, ring: usize) -> String {
    let port = theta.source_port(ring).expect("E");
    let mut s = format!("E {} {}\n", port.rows(), port.columns());
    for i in 0..port.rows() {
        let row: Vec<String> = (0..port.columns())
            .map(|j| port.get(i, j).expect("in range").to_string())
            .collect();
        s.push_str(&row.join(" "));
        s.push('\n');
    }
    s.push_str(&format!("rho {}\n", theta.transport(ring)));
    s
}

/// A trained constitution read back from [`write_port`]'s text: the source port `E` and, when the
/// file carries one, the source navigator's transport modulus `ρ` (the passage law of
/// September 30); the declared opening elsewhere.
pub(super) fn trained(opening: &Constitution, ring: usize, path: &str) -> Constitution {
    let theta = opening
        .clone()
        .with_ports(ring, None, Some(read_port(path)), None)
        .expect("the trained E");
    match read_modulus(path) {
        Some(modulus) => theta.with_transport(ring, modulus).expect("the trained ρ"),
        None => theta,
    }
}

/// The transport modulus line `rho <ρ>` of a written port, if any.
fn read_modulus(path: &str) -> Option<Rat> {
    #[allow(clippy::disallowed_methods)]
    let text = std::fs::read_to_string(path).expect("read the port");
    text.lines()
        .find_map(|line| line.strip_prefix("rho "))
        .map(|value| value.trim().parse::<Rat>().expect("a rational ρ"))
}

/// A source port read back from [`write_port`]'s text.
fn read_port(path: &str) -> ExactRatMatrix {
    #[allow(clippy::disallowed_methods)]
    let text = std::fs::read_to_string(path).expect("read the port");
    let mut lines = text.lines();
    let head: Vec<usize> = lines
        .next()
        .expect("E")
        .split_whitespace()
        .skip(1)
        .map(|x| x.parse().expect("a shape"))
        .collect();
    let rows: Vec<Vec<Rat>> = (0..head[0])
        .map(|_| {
            lines
                .next()
                .expect("a row")
                .split_whitespace()
                .map(|x| x.parse::<Rat>().expect("a rational"))
                .collect()
        })
        .collect();
    ExactRatMatrix::new(rows).expect("E")
}

/// **The modulus's slope split by term kind**, printed (`hnn::executed::SlopeSplit`): the terms led
/// by the threshold and by a class rival with their `Σ (f)_+`, `γ_ρ` of the leading contributions
/// by kind, and every term's target part and class rival part read alone (the class branch at every
/// term is their sum).
pub(super) fn split_line(split: &SlopeSplit) -> String {
    let point = |x: &Rat| cell(&ExactInterval::point(x.clone()), 1 << 12);
    format!(
        "; split: threshold-led {} terms (Σ (f)_+ {}, γ {}), class-led {} terms (Σ (f)_+ {}, γ {}); every term read alone: the target's part {}, the class rival's part {}, the class branch {}",
        split.threshold_led,
        cell(&split.threshold_value, 1 << 12),
        point(&split.led_threshold),
        split.class_led,
        cell(&split.class_value, 1 << 12),
        point(&split.led_class),
        point(&split.target),
        point(&split.rival),
        point(&(&split.target + &split.rival))
    )
}

/// **The modulus's slope at constitutions** (`executed slopes <terrain> <seed> <count> <label=E>…`,
/// a diagnostic, never a pinned run; `opening` the declared opening, a written port with its `ρ`
/// otherwise, and `label=E@ρ` read at the modulus `ρ`, `label=@ρ` the opening at `ρ`): the batch compared along the machine's
/// own trajectory, its whole sections, and `γ_ρ` split by term kind, no move made.
pub(super) fn slopes(terrain: &str, seed: u64, count: usize, arms: &[String]) {
    use holonics::hnn::executed::modulus_slopes;
    let clock = Instant::now();
    let declared = order_declared();
    let engine = Engine::new(declared);
    let bank = bank_of(declared.period, &bank_strength());
    let ring = engine.refinement.ring();
    let pairs = terrain_pairs(terrain, &declared, seed, count);
    let requests: Vec<Request> = pairs
        .iter()
        .map(|(request, target)| {
            let (current, moment) = ingest(&engine.field, request);
            Request {
                current,
                moment,
                targets: target.clone(),
                context: Context::Open,
            }
        })
        .collect();
    let targets: Vec<Vec<usize>> = pairs.iter().map(|(_, t)| t.clone()).collect();
    println!("executed slopes: {count} {terrain} requests at seed {seed}, along the machine's own trajectory");
    for arm in arms {
        let started = Instant::now();
        let (label, path) = arm.split_once('=').unwrap_or((arm.as_str(), ""));
        let (path, modulus) = match path.split_once('@') {
            Some((path, modulus)) => (path, Some(modulus.parse::<Rat>().expect("a rational ρ"))),
            None => (path, None),
        };
        let mut theta = match (path.is_empty(), &modulus) {
            (true, None) => founded_opening(&engine),
            (true, Some(_)) => engine.theta.clone(),
            (false, _) => trained(&engine.theta, ring, path),
        };
        if let Some(modulus) = modulus {
            theta = theta.with_transport(ring, modulus).expect("a passive modulus on the lattice");
        }
        let (batch, split) =
            modulus_slopes(&engine.field, &theta, &requests, &engine.refinement, &bank, BANK_GRAIN)
                .expect("the slopes");
        let (whole, right, released) = batch.sections(&targets);
        let gamma = &split.led_threshold + &split.led_class;
        println!(
            "  {label} (ρ = {}): F ∈ {}; released {released}, whole {whole}, stations right {right}; γ_ρ {}{}; {} ms",
            theta.transport(ring),
            cell(&batch.value, 1 << 12),
            cell(&ExactInterval::point(gamma), 1 << 12),
            split_line(&split),
            started.elapsed().as_millis()
        );
    }
    println!("executed slopes: {} ms; resident {}", clock.elapsed().as_millis(), resident());
}

/// **The executed comparison's declared opening** (`hnn::executed`, "The committed move"): the
/// declared constitution with the source ring's transport founded off the lossless boundary
/// (`Constitution::founded_transport`).
pub(super) fn founded_opening(engine: &Engine) -> Constitution {
    engine
        .theta
        .clone()
        .founded_transport(&engine.field, engine.refinement.ring())
        .expect("the founded transport")
}

/// The partitions' seed of Stage 2's partition arms (the readout's `mask` law), pinned.
const STAGE_TWO_MASK_SEED: u64 = 2_026_093_004;

/// **Stage 2: one arm's training** (`executed train <arm> <terrain> <seed> <batch> <moves>
/// <deadline ms> <out>`). The arm is the executed comparison (`executed`) crossed with the
/// contexts (`open`: the machine's own trajectory; `partition`: the readout's partitions at
/// [`STAGE_TWO_MASK_SEED`]). Every arm starts from the declared opening, reads the same requests in
/// the same batches, and moves by the one certified step's ladder; the moves are the work bound,
/// the deadline a guard (reaching it is reported incomplete). The trained `E` is written to `out`.
/// Each move also prints the port's first-order slope and the modulus's slope `γ_ρ` (added after
/// the station-framed placement's pinned runs, to read why the modulus stays at one).
#[allow(clippy::too_many_arguments)]
pub(super) fn train(
    arm: &str,
    terrain: &str,
    seed: u64,
    batch: usize,
    moves: usize,
    deadline: u128,
    out: &str,
) {
    use holonics::hnn::prediction::mask;
    let clock = Instant::now();
    let declared = order_declared();
    let engine = Engine::new(declared);
    let bank = bank_of(declared.period, &bank_strength());
    // An arm may carry its opening's transport modulus (`executed-open@ρ`, a development read).
    let (arm_name, opening_modulus) = match arm.split_once('@') {
        Some((name, modulus)) => (name, Some(modulus.parse::<Rat>().expect("a rational ρ"))),
        None => (arm, None),
    };
    let (comparison, contexts) =
        arm_name.split_once('-').expect("an arm: executed-open | executed-partition");
    assert_eq!(comparison, "executed", "the comparison: executed");
    let pairs = terrain_pairs(terrain, &declared, seed, batch * moves);
    let mut masks = Draw::new(STAGE_TWO_MASK_SEED);
    let requests: Vec<Request> = pairs
        .iter()
        .map(|(request, target)| {
            let (current, moment) = ingest(&engine.field, request);
            let context = match contexts {
                "open" => Context::Open,
                "partition" => Context::Partition(mask(&mut masks, declared.stations)),
                _ => panic!("contexts: open | partition"),
            };
            Request {
                current,
                moment,
                targets: target.clone(),
                context,
            }
        })
        .collect();
    let mut theta = match &opening_modulus {
        Some(modulus) => engine
            .theta
            .clone()
            .with_transport(engine.refinement.ring(), modulus.clone())
            .expect("a passive modulus on the lattice"),
        None => founded_opening(&engine),
    };
    println!(
        "executed train: arm {arm} on {terrain} at seed {seed}: {moves} moves of {batch} requests; the declared opening, its transport modulus {}; the bank p = {}, grain 2^(-{BANK_GRAIN})",
        theta.transport(engine.refinement.ring()),
        bank_strength()
    );
    // The two counts' instrumentation (the pin §5), read from the terrain's pairs alone and only
    // printed: the ideal listener's bits on each move's batch, and which requests are constant.
    let information = ideal_information(terrain, &pairs, batch);
    let constant: Vec<bool> = pairs.iter().map(|(request, _)| constant_request(request)).collect();
    let (mut adopted, mut refused, mut readings) = (0usize, 0usize, 0usize);
    let mut complete = true;
    for (index, chunk) in requests.chunks(batch).enumerate() {
        if clock.elapsed().as_millis() > deadline {
            complete = false;
            println!("  deadline reached before move {index}: incomplete");
            break;
        }
        let started = Instant::now();
        let moved = executed_move(&engine.field, &theta, chunk, &engine.refinement, &bank, BANK_GRAIN)
            .expect("the move");
        readings += moved.before.readings;
        // The two slopes the move reads (a diagnostic added after the station-framed placement's
        // pinned runs): the port's unit move's first order, and the modulus's `γ_ρ` (its sign
        // decides whether the modulus may leave one: none upward from `ρ = 1`).
        let slopes = format!(
            "; the port's first-order slope {}; the modulus's slope γ_ρ {}{}",
            moved.slope.as_ref().map_or_else(|| "none".to_string(), |s| cell(s, 1 << 12)),
            moved
                .modulus_slope
                .as_ref()
                .map_or_else(|| "none".to_string(), |g| cell(&ExactInterval::point(g.clone()), 1 << 12)),
            moved.split.as_ref().map_or_else(String::new, split_line)
        ) + &format!(
            "; the modulus's curvature G_ρ {}, its least-squares unit move {}",
            moved
                .modulus_curvature
                .as_ref()
                .map_or_else(|| "none".to_string(), |g| cell(&ExactInterval::point(g.clone()), 1 << 12)),
            moved
                .modulus_unit
                .as_ref()
                .map_or_else(|| "none".to_string(), |u| cell(&ExactInterval::point(u.clone()), 1 << 16))
        );
        let sections = if contexts == "open" {
            let targets: Vec<Vec<usize>> = chunk.iter().map(|r| r.targets.clone()).collect();
            let (whole, right, released) = moved.before.sections(&targets);
            format!("; batch released {released}, whole {whole}, stations right {right}")
        } else {
            String::new()
        };
        // D1 and D2 (the pin §5), read from the move's receipt at `θ` before it is replaced.
        let targets: Vec<Vec<usize>> = chunk.iter().map(|r| r.targets.clone()).collect();
        let ring = engine.refinement.ring();
        let first = index * batch;
        print_d1(index, &moved, &theta, ring, &targets, information.get(index).map_or("", String::as_str));
        let carried = moved
            .adopted
            .as_ref()
            .and_then(|_| moved.trials.last())
            .or_else(|| moved.trials.iter().rev().find(|t| t.terms.is_some()));
        print_d2(
            index,
            &moved,
            &constant[first..first + chunk.len()],
            carried.and_then(|t| t.terms.as_ref()),
        );
        match &moved.adopted {
            Some((successor, step)) => {
                adopted += 1;
                let last = moved.trials.last().expect("the adopted trial");
                println!(
                    "  move {index}: adopted at step {} (trial {} of the ladder); value {} → {}; E's largest entry {}; transport modulus {} → {}{sections}; {} ms",
                    step.step,
                    moved.trials.len(),
                    cell(&moved.before.value, 1 << 12),
                    last.value.as_ref().map_or_else(String::new, |v| cell(v, 1 << 12)),
                    step.largest,
                    theta.transport(engine.refinement.ring()),
                    successor.transport(engine.refinement.ring()),
                    started.elapsed().as_millis()
                );
                println!("    move {index}{slopes}");
                theta = successor.clone();
                // The adopted constitution written at every move, so a run stopped by its process
                // guard leaves its last certified successor (a checkpoint, not a law).
                #[allow(clippy::disallowed_methods)]
                std::fs::write(out, write_port(&theta, engine.refinement.ring())).expect("write E");
            }
            None => {
                refused += 1;
                println!(
                    "  move {index}: refused {:?} after {} trials; value {}{sections}; {} ms",
                    moved.refusal,
                    moved.trials.len(),
                    cell(&moved.before.value, 1 << 12),
                    started.elapsed().as_millis()
                );
                println!("    move {index}{slopes}");
            }
        }
        // The checkpoints (the pin §4): the constitution after moves 1, 2, 4, 8 and 16.
        if CHECKPOINTS.contains(&(index + 1)) {
            let path = format!("{out}.m{}", index + 1);
            #[allow(clippy::disallowed_methods)]
            std::fs::write(&path, write_port(&theta, engine.refinement.ring())).expect("write E");
            println!("  checkpoint after move {}: {path}", index + 1);
        }
    }
    #[allow(clippy::disallowed_methods)]
    std::fs::write(out, write_port(&theta, engine.refinement.ring())).expect("write E");
    println!(
        "executed train: arm {arm}: {adopted} moves adopted, {refused} refused, {readings} readings at E; {}; {} ms; resident {}",
        if complete { "complete" } else { "incomplete (deadline)" },
        clock.elapsed().as_millis(),
        resident()
    );
}

/// **Stage 2's confirmation** (`executed evaluate <terrain> <seed> <count> <out> <label=E>…`, a
/// label `opening` reading the declared opening): every constitution generates every confirmation
/// request by `generate_by_bank` from the open section; the complete sections are written to `out`
/// and the counts printed: released and held, whole sections equal to their targets, stations
/// right by station, sections reaching the termination, incorrect releases, the first lock's
/// station and correctness, and the refused certificates.
pub(super) fn evaluate(terrain: &str, seed: u64, count: usize, out: &str, arms: &[String]) {
    use rayon::prelude::*;
    use std::fmt::Write as _;
    let clock = Instant::now();
    let declared = order_declared();
    let engine = Engine::new(declared);
    let bank = bank_of(declared.period, &bank_strength());
    let ring = engine.refinement.ring();
    let pairs = terrain_pairs(terrain, &declared, seed, count);
    let mut listing = String::new();
    for arm in arms {
        let (label, path) = arm.split_once('=').unwrap_or((arm.as_str(), ""));
        let theta = match (label, path.is_empty()) {
            ("lossless", true) => engine.theta.clone(),
            (_, true) => founded_opening(&engine),
            (_, false) => trained(&engine.theta, ring, path),
        };
        // The constitution's own clock: its requests' generation (run in parallel on the host's
        // cores) and their tally, read before the listing is written.
        let started = Instant::now();
        let generated: Vec<_> = pairs
            .par_iter()
            .map(|(request, _)| {
                let (current, moment) = ingest(&engine.field, request);
                generate_by_bank(
                    &engine.field,
                    &theta,
                    &current,
                    &moment,
                    &engine.refinement,
                    &bank,
                    BANK_GRAIN,
                )
            })
            .collect();
        let (mut released, mut held, mut whole, mut incorrect, mut terminated) = (0, 0, 0, 0, 0);
        let (mut refused, mut uncertified) = (0, 0);
        let mut by_station = vec![0usize; declared.stations];
        let (mut first_request, mut first_right) = (0, 0);
        // The two counts' split (the pin §4): nonconstant and constant requests apart, and the
        // success rule, every nonconstant request's section released whole.
        let (mut nonconstant, mut whole_nonconstant, mut whole_constant) = (0, 0, 0);
        writeln!(listing, "== {label} on {terrain}, seed {seed}").unwrap();
        for ((request, target), generation) in pairs.iter().zip(&generated) {
            let is_constant = constant_request(request);
            nonconstant += usize::from(!is_constant);
            let Ok(generation) = generation else {
                refused += 1;
                writeln!(listing, "{request:?} → refused").unwrap();
                continue;
            };
            let classes = &generation.release.classes;
            uncertified += usize::from(generation.uncertified.is_some());
            let right: Vec<bool> = classes.iter().zip(target).map(|(a, b)| a == b).collect();
            for (j, r) in right.iter().enumerate() {
                by_station[j] += usize::from(*r);
            }
            terminated += usize::from(generation.release.terminated.is_some());
            if let Some(first) = generation.locks.first().and_then(|lock| lock.first()) {
                first_request += usize::from(*first < 2);
                first_right += usize::from(classes[*first] == target[*first]);
            }
            if generation.release.released() {
                released += 1;
                if right.iter().all(|r| *r) {
                    whole += 1;
                    if is_constant {
                        whole_constant += 1;
                    } else {
                        whole_nonconstant += 1;
                    }
                } else {
                    incorrect += 1;
                }
            } else {
                held += 1;
            }
            writeln!(
                listing,
                "{} | target {:?} | {} {:?} | locks {:?}{}",
                request.iter().map(ToString::to_string).collect::<String>(),
                target,
                if generation.release.released() { "released" } else { "held" },
                classes,
                generation.locks,
                if is_constant { " | constant request" } else { "" }
            )
            .unwrap();
        }
        println!(
            "  {label} (transport modulus {}): released {released}, held {held}, refused {refused}, refused certificates {uncertified}; whole sections {whole} of {count} (nonconstant {whole_nonconstant} of {nonconstant}, constant {whole_constant} of {}); the success rule (every nonconstant section whole): {}; incorrect releases {incorrect}; reaching the termination {terminated}; stations right {} by station {by_station:?}; first lock at a request-reading station (0 or 1) {first_request}, first lock right {first_right}; {} ms",
            theta.transport(ring),
            count - nonconstant,
            if whole_nonconstant == nonconstant { "holds" } else { "does not hold" },
            by_station.iter().sum::<usize>(),
            started.elapsed().as_millis()
        );
        // Written after each constitution, so a run stopped by its guard keeps what it read.
        #[allow(clippy::disallowed_methods)]
        std::fs::write(out, &listing).expect("write the sections");
    }
    #[allow(clippy::disallowed_methods)]
    std::fs::write(out, listing).expect("write the sections");
    println!(
        "executed evaluate: {} ms; resident {}",
        clock.elapsed().as_millis(),
        resident()
    );
}

/// **The first refinement's spread** (`executed spread <terrain> <seed> <count> <label=E>…`, a
/// diagnostic after Stage 2, not a pinned run): at the open section of each request, every
/// station's five candidates read exactly; per constitution, the target's rank among them (by the
/// lower end, 0 the top), the station's term `f = max(max ln(a_x/a_t), −ln a_t)` and the spread
/// `ln(a_top/a_bottom)`, each summed at the grain `2^(−8)`.
pub(super) fn spread(terrain: &str, seed: u64, count: usize, arms: &[String]) {
    use rayon::prelude::*;
    let declared = order_declared();
    let engine = Engine::new(declared);
    let bank = bank_of(declared.period, &bank_strength());
    let ring = engine.refinement.ring();
    let pairs = terrain_pairs(terrain, &declared, seed, count);
    for arm in arms {
        let (label, path) = arm.split_once('=').unwrap_or((arm.as_str(), ""));
        let theta = if path.is_empty() {
            engine.theta.clone()
        } else {
            trained(&engine.theta, ring, path)
        };
        let read: Vec<(Vec<usize>, Rat, Rat)> = pairs
            .par_iter()
            .map(|(request, target)| {
                let (current, moment) = ingest(&engine.field, request);
                let placement = BankPlacement::of(
                    &engine.field,
                    &theta,
                    &current,
                    &moment,
                    &engine.refinement,
                )
                .expect("the placement");
                let mut ranks = vec![0usize; 2 * declared.alphabet];
                let (mut terms, mut spreads) = (Rat::zero(), Rat::zero());
                for (station, &t) in target.iter().enumerate() {
                    let joints: Vec<holonics::hnn::ring::Growth> = (0..declared.alphabet)
                        .map(|class| {
                            let mut cells = vec![None; declared.stations];
                            cells[station] = Some(class);
                            bank.read_turn(&turn(&placement.storage(station, &cells)), BANK_GRAIN)
                                .expect("a reading")
                                .joint
                        })
                        .collect();
                    let rank = joints
                        .iter()
                        .filter(|g| g.lower > joints[t].lower)
                        .count();
                    ranks[rank] += 1;
                    // The termination's own rank, beside the target's (the last class).
                    let end = declared.alphabet - 1;
                    let end_rank = joints
                        .iter()
                        .filter(|g| g.lower > joints[end].lower)
                        .count();
                    ranks[declared.alphabet + end_rank] += 1;
                    let ln = |x: &Rat| {
                        holonics::ratio::algebraic::ln_enclosure(x).expect("a logarithm").lower
                    };
                    let lt = ln(&joints[t].lower);
                    let top = joints.iter().map(|g| ln(&g.lower)).max().expect("a class");
                    let bottom = joints.iter().map(|g| ln(&g.lower)).min().expect("a class");
                    let f = (top.clone() - &lt).max(-lt);
                    terms += f.max(Rat::zero());
                    spreads += top - bottom;
                }
                (ranks, terms, spreads)
            })
            .collect();
        let mut ranks = vec![0usize; 2 * declared.alphabet];
        let (mut terms, mut spreads) = (Rat::zero(), Rat::zero());
        for (r, t, s) in read {
            for (a, b) in ranks.iter_mut().zip(r) {
                *a += b;
            }
            terms += t;
            spreads += s;
        }
        let point = |x: &Rat| cell(&ExactInterval::point(x.clone()), 1 << 8);
        println!(
            "  {label}: the target's rank at the open section (0 the top) {:?}, the termination's {:?}; Σ (f)_+ at the lower ends {}; Σ ln(a_top/a_bottom) {}",
            &ranks[..declared.alphabet],
            &ranks[declared.alphabet..],
            point(&terms),
            point(&spreads)
        );
    }
}

/// The order-2 declaration, its bank and a batch of requests compared along the machine's own
/// trajectory.
pub(super) fn order_batch(
    seed: u64,
    count: usize,
) -> (Engine, ReceivingBank, Vec<Request>, Vec<Vec<usize>>) {
    let declared = order_declared();
    let engine = Engine::new(declared);
    let bank = bank_of(declared.period, &bank_strength());
    let pairs = order_pairs(&declared, seed, count);
    let requests = pairs
        .iter()
        .map(|(request, target)| {
            let (current, moment) = ingest(&engine.field, request);
            Request {
                current,
                moment,
                targets: target.clone(),
                context: Context::Open,
            }
        })
        .collect();
    let targets = pairs.into_iter().map(|(_, target)| target).collect();
    (engine, bank, requests, targets)
}

/// **Stage 1: one committed move with its complete receipt** (module header).
pub(super) fn stage_one(seed: u64, count: usize) {
    let clock = Instant::now();
    let (engine, bank, requests, targets) = order_batch(seed, count);
    println!(
        "executed move: {count} order-2 requests at seed {seed}, compared along the machine's own open-section trajectory; E at the declared opening; the bank p = {}, grain 2^(-{BANK_GRAIN})",
        bank_strength()
    );
    let moved: ExecutedMove = executed_move(
        &engine.field,
        &engine.theta,
        &requests,
        &engine.refinement,
        &bank,
        BANK_GRAIN,
    )
    .expect("the executed move");
    println!("  read and proposed in {} ms", clock.elapsed().as_millis());
    print_batch("before", &moved.before, &targets);
    println!(
        "  proposal: {} storage contributions, {} returns at E, {} terms positive or undecided, {} leading branches unresolved {:?}, {} terms with an unresolved active branch",
        moved.contributions,
        moved.returns,
        moved.terms,
        moved.unresolved.len(),
        moved.unresolved,
        moved.unresolved_branches
    );
    if let Some(slope) = &moved.slope {
        println!(
            "  the unit step's first-order bound Σ sup_α Df_α ∈ {} nats",
            cell(slope, 1 << 16)
        );
    }
    for trial in &moved.trials {
        println!(
            "  trial step {}: largest entry move {}, successor's largest entry {}, first-order bound {}, F after {}, refusal {:?}",
            trial.step,
            trial.moved,
            trial.largest,
            trial
                .first_order
                .as_ref()
                .map_or_else(|| "not read".to_string(), |b| cell(b, 1 << 16)),
            trial
                .value
                .as_ref()
                .map_or_else(|| "not read".to_string(), |v| cell(v, 1 << 16)),
            trial.refusal.as_ref().map(|r| match r {
                holonics::hnn::executed::TrialRefusal::NotBelow(v) =>
                    format!("NotBelow(F ∈ {})", cell(v, 1 << 16)),
                holonics::hnn::executed::TrialRefusal::FirstOrder(v) =>
                    format!("FirstOrder({})", cell(v, 1 << 16)),
                other => format!("{other:?}"),
            })
        );
    }
    println!("  refusal of the move: {:?}", moved.refusal);
    let Some((successor, step)) = &moved.adopted else {
        println!("executed move: no step adopted; {} ms; resident {}", clock.elapsed().as_millis(), resident());
        return;
    };
    let after = moved
        .trials
        .last()
        .and_then(|t| t.after.clone())
        .expect("the adopted trial's comparison");
    println!(
        "  adopted: step {}, alignment {}, entries stepped {}, residuals released {}, storage growth {}, E's largest entry {}, exact bits {}",
        step.step,
        step.alignment,
        step.stepped,
        step.released.len(),
        step.storage_growth,
        step.largest,
        step.bits
    );
    println!(
        "  the certificate: F(E′)⁺ < F(E)⁻, {} < {}: {}",
        cell(&ExactInterval::point(after.value.upper.clone()), 1 << 16),
        cell(&ExactInterval::point(moved.before.value.lower.clone()), 1 << 16),
        after.value.upper < moved.before.value.lower
    );
    print_batch("after", &after, &targets);
    // Requirement 3: the covector paired with the carried move against the exact change.
    let pairing = pairing_receipt(
        &engine.field,
        &engine.theta,
        successor,
        &requests,
        &engine.refinement,
        &bank,
        BANK_GRAIN,
        4,
    )
    .expect("the pairing receipt");
    for reading in &pairing {
        println!(
            "  pairing: request {} section {:?} member {}: Δ ln ρ exact ∈ {}, the covector on the carried move ∈ {}",
            reading.request,
            reading.cells,
            reading.member,
            cell(&reading.actual, 1 << 20),
            cell(&reading.predicted, 1 << 20)
        );
    }
    let ring = engine.refinement.ring();
    let delta = successor
        .source_port(ring)
        .expect("E")
        .subtract(engine.theta.source_port(ring).expect("E"))
        .expect("the move");
    // Requirement 3 at a small step: the same direction at 2^(−8) of the carried move (a chart of
    // the source port for the check, never adopted), where the second order is 2^8 times smaller
    // against the first.
    let small = engine
        .theta
        .clone()
        .with_ports(
            ring,
            None,
            Some(
                engine
                    .theta
                    .source_port(ring)
                    .expect("E")
                    .add(&delta.scaled(&rat(1, 256)))
                    .expect("the small move"),
            ),
            None,
        )
        .expect("the small move as a port");
    let small_pairing = pairing_receipt(
        &engine.field,
        &engine.theta,
        &small,
        &requests,
        &engine.refinement,
        &bank,
        BANK_GRAIN,
        4,
    )
    .expect("the small step's pairing");
    for reading in &small_pairing {
        println!(
            "  pairing at 2^(-8) of the move: request {} section {:?} member {}: Δ ln ρ exact ∈ {}, the covector ∈ {}",
            reading.request,
            reading.cells,
            reading.member,
            cell(&reading.actual, 1 << 28),
            cell(&reading.predicted, 1 << 28)
        );
    }
    // Requirement 1: on the same candidates, the monodromy's variation along the carried storage
    // move, forward and in reverse, and the covector's three routes.
    let moved_theta = engine
        .theta
        .clone()
        .with_ports(ring, None, Some(delta), None)
        .expect("the move as a port");
    for reading in pairing.iter().take(4) {
        let request = &requests[reading.request];
        let at = BankPlacement::of(
            &engine.field,
            &engine.theta,
            &request.current,
            &request.moment,
            &engine.refinement,
        )
        .expect("the placement");
        let along = BankPlacement::of(
            &engine.field,
            &moved_theta,
            &request.current,
            &request.moment,
            &engine.refinement,
        )
        .expect("the move's placement");
        let amplitudes = turn(&at.storage(reading.station, &reading.cells));
        // The request's own storage moves with E too: the move's placement is the whole storage
        // move (base and section), linear in E.
        let direction = turn(&along.storage(reading.station, &reading.cells));
        let variation = bank
            .turn_variation(reading.member, &amplitudes, &direction)
            .expect("the variation");
        let routes = bank
            .directional_routes(reading.member, &amplitudes, &direction, BANK_GRAIN)
            .expect("the routes");
        println!(
            "  variation: request {} member {}: forward = reverse exactly: {}; routes {}",
            reading.request,
            reading.member,
            variation.forward == variation.reverse,
            match routes {
                Some(r) => format!(
                    "covector {}, eigen {}, trace {}; agree {}",
                    cell(&r.covector, 1 << 20),
                    cell(&r.eigen, 1 << 20),
                    cell(&r.trace, 1 << 20),
                    r.agree()
                ),
                None => "unresolved".to_string(),
            }
        );
    }
    let _ = MemberCovector::member;
    println!(
        "executed move: {} ms in all; resident {}",
        clock.elapsed().as_millis(),
        resident()
    );
}

// -------------------------------------------------------------------------------------------
// The two counts (THE_REBUILD U6, step 1, loop 1a; the
// [pin](../../records/2026-09-30_THE_TWO_COUNTS_PINNED_BEFORE_ITS_RUNS.md)). Read-only
// instrumentation: the declared reference family is computed from the terrain's pairs alone and is
// printed; nothing of it (keys, survivors, lags, continuations) reaches the machine.

/// [definition; the pin §1] **The declared reference family's lags** `ℓ ∈ [1, LAGS]` over the
/// terrain's residue ring `ℤ/RESIDUES` (the alphabet less the termination).
const LAGS: usize = 40;
const RESIDUES: usize = 4;
/// [definition; the pin §4] **The checkpoints**: the constitution written after these many moves.
const CHECKPOINTS: [usize; 5] = [1, 2, 4, 8, 16];

/// **An observation's argument** under lag `ℓ` (the pin §1, the emitter): station `j`'s cell
/// `x_(n + j − ℓ)`, read from the request (the initial history) or from the same request's earlier
/// stations; never across a request boundary.
fn argument(request: &[usize], section: &[usize], station: usize, lag: usize) -> usize {
    let at = request.len() + station - lag;
    if at < request.len() {
        request[at]
    } else {
        section[at - request.len()]
    }
}

/// [definition; the pin §1] **A constant request**: its 40 cells one class, so every lag reads its
/// one symbol and it separates no lag.
fn constant_request(request: &[usize]) -> bool {
    request.iter().all(|&x| x == request[0])
}

/// An observation count in both units (the pin §4): `q` requests plus `j` stations.
fn both_units(observations: usize, stations: usize) -> String {
    format!(
        "{observations} observations ({} requests plus {} stations)",
        observations / stations,
        observations % stations
    )
}

/// [definition; the pin §1] **One lag's fibre in the global family**: whether it lives, and its
/// map's value at each residue (`None` unobserved: every value survives there).
#[derive(Clone, Debug, PartialEq, Eq)]
struct LagFibre {
    alive: bool,
    map: [Option<usize>; RESIDUES],
}

/// [definition; the pin §1] **One lag's fibre in the hierarchical family `H`**: whether it lives,
/// the finished requests' translation counts multiplied, and the current request's consistent
/// translations (reset to all of `ℤ/4` at each request boundary: the translation never carries
/// across requests, the lag and its death do).
#[derive(Clone, Debug)]
struct TranslationFibre {
    alive: bool,
    past: BigUint,
    current: [bool; RESIDUES],
}

/// [definition; the pin §1] **A declared reference family's survivors**, read along a passage in
/// its order: the global family (one key for every request) or `H` (a global lag, a per-request
/// translation, over a passage of `requests` requests, `begun` of them begun).
#[derive(Clone, Debug)]
enum ReferenceFamily {
    Global(Vec<LagFibre>),
    Hierarchical {
        lags: Vec<TranslationFibre>,
        requests: usize,
        begun: usize,
    },
}

impl ReferenceFamily {
    fn global() -> Self {
        Self::Global(vec![
            LagFibre {
                alive: true,
                map: [None; RESIDUES],
            };
            LAGS
        ])
    }

    fn hierarchical(requests: usize) -> Self {
        Self::Hierarchical {
            lags: vec![
                TranslationFibre {
                    alive: true,
                    past: BigUint::from(1u32),
                    current: [true; RESIDUES],
                };
                LAGS
            ],
            requests,
            begun: 0,
        }
    }

    fn name(&self) -> &'static str {
        match self {
            Self::Global(_) => "the global family",
            Self::Hierarchical { .. } => "the hierarchical family H",
        }
    }

    /// The family's size under its prior: `40 · 4⁴` keys, or `40 · 4^R` for `H`.
    fn size(&self) -> BigUint {
        let four = BigUint::from(RESIDUES as u32);
        match self {
            Self::Global(_) => BigUint::from(LAGS as u32) * four.pow(RESIDUES as u32),
            Self::Hierarchical { requests, .. } => {
                BigUint::from(LAGS as u32) * four.pow(*requests as u32)
            }
        }
    }

    /// **The survivors' count** `#S_k` (the pin §1): `Σ_(ℓ alive) 4^(u_ℓ)`, or for `H`
    /// `Σ_(ℓ alive) Π_r #C_(ℓ,r)`, every unbegun request with its four translations.
    fn count(&self) -> BigUint {
        let four = BigUint::from(RESIDUES as u32);
        match self {
            Self::Global(lags) => lags
                .iter()
                .filter(|lag| lag.alive)
                .map(|lag| four.pow(lag.map.iter().filter(|v| v.is_none()).count() as u32))
                .sum(),
            Self::Hierarchical {
                lags,
                requests,
                begun,
            } => lags
                .iter()
                .filter(|lag| lag.alive)
                .map(|lag| {
                    if *begun == 0 {
                        four.pow(*requests as u32)
                    } else {
                        let current =
                            BigUint::from(lag.current.iter().filter(|c| **c).count() as u32);
                        &lag.past * current * four.pow((*requests - *begun) as u32)
                    }
                })
                .sum(),
        }
    }

    /// **A request boundary**: `H`'s translation fibre resets to all of `ℤ/4`, the finished
    /// request's count joining the product (the pin §1, the reset convention).
    fn begin(&mut self) {
        if let Self::Hierarchical { lags, begun, .. } = self {
            if *begun > 0 {
                for lag in lags.iter_mut().filter(|lag| lag.alive) {
                    let kept = lag.current.iter().filter(|c| **c).count();
                    lag.past *= BigUint::from(kept as u32);
                }
            }
            for lag in lags.iter_mut() {
                lag.current = [true; RESIDUES];
            }
            *begun += 1;
        }
    }

    /// **One observation**: station `j` of a request, its true value `section[j]` against every
    /// alive key's emission (the pin §1).
    fn observe(&mut self, request: &[usize], section: &[usize], station: usize) {
        let value = section[station];
        match self {
            Self::Global(lags) => {
                for (index, lag) in lags.iter_mut().enumerate().filter(|(_, lag)| lag.alive) {
                    let a = argument(request, section, station, index + 1);
                    match lag.map[a] {
                        None => lag.map[a] = Some(value),
                        Some(v) if v != value => lag.alive = false,
                        Some(_) => {}
                    }
                }
            }
            Self::Hierarchical { lags, .. } => {
                for (index, lag) in lags.iter_mut().enumerate().filter(|(_, lag)| lag.alive) {
                    let a = argument(request, section, station, index + 1);
                    let c = (value + RESIDUES - a) % RESIDUES;
                    for (t, kept) in lag.current.iter_mut().enumerate() {
                        *kept &= t == c;
                    }
                    if lag.current.iter().all(|kept| !kept) {
                        lag.alive = false;
                    }
                }
            }
        }
    }

    /// The alive lags.
    fn alive(&self) -> Vec<usize> {
        match self {
            Self::Global(lags) => (1..=LAGS).filter(|l| lags[l - 1].alive).collect(),
            Self::Hierarchical { lags, .. } => (1..=LAGS).filter(|l| lags[l - 1].alive).collect(),
        }
    }

    /// **The continuations the survivors emit on a fresh request** (the pin §4): each key run
    /// freely over the request's `stations` (its own emissions its later arguments; an unobserved
    /// argument emits every value; `H`'s fresh translation every value), stopping once `bound`
    /// distinct continuations are found. With `given`, `H` reads the request's own first station
    /// (its translation's one reading) and every continuation starts with it.
    fn continuations(
        &self,
        request: &[usize],
        stations: usize,
        bound: usize,
        given: Option<usize>,
    ) -> BTreeSet<Vec<usize>> {
        fn emit(
            request: &[usize],
            lag: usize,
            map: [Option<usize>; RESIDUES],
            section: &mut Vec<usize>,
            stations: usize,
            out: &mut BTreeSet<Vec<usize>>,
            bound: usize,
        ) {
            if out.len() >= bound {
                return;
            }
            if section.len() == stations {
                out.insert(section.clone());
                return;
            }
            let a = argument(request, section, section.len(), lag);
            let values: Vec<usize> = match map[a] {
                Some(y) => vec![y],
                None => (0..RESIDUES).collect(),
            };
            for y in values {
                let mut next = map;
                next[a] = Some(y);
                section.push(y);
                emit(request, lag, next, section, stations, out, bound);
                section.pop();
            }
        }
        let mut out = BTreeSet::new();
        for lag in self.alive() {
            match self {
                Self::Global(lags) => emit(
                    request,
                    lag,
                    lags[lag - 1].map,
                    &mut Vec::new(),
                    stations,
                    &mut out,
                    bound,
                ),
                Self::Hierarchical { .. } => {
                    let translations: Vec<usize> = match given {
                        Some(first) => {
                            vec![(first + RESIDUES - argument(request, &[], 0, lag)) % RESIDUES]
                        }
                        None => (0..RESIDUES).collect(),
                    };
                    for c in translations {
                        let map: [Option<usize>; RESIDUES] =
                            std::array::from_fn(|a| Some((a + c) % RESIDUES));
                        emit(request, lag, map, &mut Vec::new(), stations, &mut out, bound);
                    }
                }
            }
            if out.len() >= bound {
                break;
            }
        }
        out
    }

    /// The survivor list, the certificate (the pin §4): every alive lag with its map (`·` an
    /// unobserved argument, its fibre all of `ℤ/4`), or for `H` the lag and its current
    /// translations; a key is marked an alias when it is not the terrain's generating key.
    fn certificate(&self, generating: Option<(usize, [usize; RESIDUES])>) -> String {
        match self {
            Self::Global(lags) => self
                .alive()
                .iter()
                .map(|&l| {
                    let map = lags[l - 1].map;
                    let shown: Vec<String> = map
                        .iter()
                        .map(|v| v.map_or_else(|| "·".to_string(), |y| y.to_string()))
                        .collect();
                    let alias = match generating {
                        Some((lag, f))
                            if lag == l && map.iter().zip(f).all(|(v, y)| *v == Some(y)) =>
                        {
                            ""
                        }
                        _ => " alias",
                    };
                    format!("ℓ {l} f [{}]{alias}", shown.join(" "))
                })
                .collect::<Vec<_>>()
                .join("; "),
            Self::Hierarchical { lags, .. } => self
                .alive()
                .iter()
                .map(|&l| {
                    let kept: Vec<usize> =
                        (0..RESIDUES).filter(|&c| lags[l - 1].current[c]).collect();
                    format!("ℓ {l} (current translations {kept:?})")
                })
                .collect::<Vec<_>>()
                .join("; "),
        }
    }

    /// Every alive lag's unobserved arguments (the global family).
    fn unobserved(&self) -> String {
        match self {
            Self::Global(lags) => self
                .alive()
                .iter()
                .filter_map(|&l| {
                    let free: Vec<usize> =
                        (0..RESIDUES).filter(|&a| lags[l - 1].map[a].is_none()).collect();
                    (!free.is_empty()).then(|| format!("ℓ {l}: {free:?}"))
                })
                .collect::<Vec<_>>()
                .join("; "),
            Self::Hierarchical { .. } => String::new(),
        }
    }
}

/// The terrain's generating key in the global family, where it is one (the pin §2): order-2
/// `(2, a ↦ a + 1)`, the alternation `(2, id)`; the line's law is no global key.
fn generating_key(terrain: &str) -> Option<(usize, [usize; RESIDUES])> {
    match terrain {
        "order2" => Some((2, [1, 2, 3, 0])),
        "alternation" => Some((2, [0, 1, 2, 3])),
        _ => None,
    }
}

/// `log₂` of an exact ratio of counts, enclosed on the declared grid.
fn bits(ratio: &Rat) -> ExactInterval {
    holonics::ratio::algebraic::log2_enclosure(ratio).expect("a positive ratio")
}

/// A ratio of two counts, exact.
fn count_ratio(numerator: &BigUint, denominator: &BigUint) -> Rat {
    Rat::new(BigInt::from(numerator.clone()), BigInt::from(denominator.clone()))
}

/// [definition; the pin §1, §4] **A family's reading along a passage**: the survivors' count
/// before every observation and after the last (`counts[k] = #S_k`), and the family after the
/// passage.
struct PassageReading {
    counts: Vec<BigUint>,
    family: ReferenceFamily,
}

/// Read a family along the passage, observation by observation, in the passage's order; `at`
/// sees the family after each observation `k` (its count `counts[k]` already pushed).
fn read_passage(
    mut family: ReferenceFamily,
    pairs: &[(Vec<usize>, Vec<usize>)],
    mut at: impl FnMut(usize, &ReferenceFamily, &[BigUint]),
) -> PassageReading {
    let mut counts = vec![family.count()];
    for (request, section) in pairs {
        family.begin();
        for station in 0..section.len() {
            family.observe(request, section, station);
            counts.push(family.count());
            at(counts.len() - 1, &family, &counts);
        }
    }
    PassageReading { counts, family }
}

/// **The ideal listener's information on each batch of the passage** (D1; the pin §5): each
/// move's exact ratio `#S_(64m)/#S_(64(m+1))` and its `log₂` enclosed, in bits.
fn batch_information(counts: &[BigUint], per_batch: usize) -> Vec<(Rat, ExactInterval)> {
    (0..(counts.len() - 1) / per_batch)
        .map(|m| {
            let ratio = count_ratio(&counts[m * per_batch], &counts[(m + 1) * per_batch]);
            let b = bits(&ratio);
            (ratio, b)
        })
        .collect()
}

/// **The ideal listener's information on each move's batch** (D1; the pin §5), from the terrain's
/// pairs alone, per family, printed beside each move and never passed to it.
fn ideal_information(terrain: &str, pairs: &[(Vec<usize>, Vec<usize>)], batch: usize) -> Vec<String> {
    let stations = pairs.first().map_or(0, |(_, s)| s.len());
    let per: Vec<(String, Vec<(Rat, ExactInterval)>)> = families_of(terrain, pairs.len())
        .into_iter()
        .map(|family| {
            let name = family.name();
            let reading = read_passage(family, pairs, |_, _, _| {});
            (name.to_string(), batch_information(&reading.counts, batch * stations))
        })
        .collect();
    (0..pairs.len() / batch)
        .map(|m| {
            per.iter()
                .map(|(name, info)| {
                    format!("{name}: ratio {}, {} bits", info[m].0, cell(&info[m].1, 1 << 8))
                })
                .collect::<Vec<_>>()
                .join("; ")
        })
        .collect()
}

/// [definition; the pin §5] **One stratum of D2's readings**: the station comparisons of one
/// decision kind and request kind, their class gaps and threshold margins (sign counts, sums,
/// extremes; exact enclosures), the gaps' magnitudes summed, and their terms' derivatives along
/// the carried move (exactly zero, below the term's grain, descending, rising, straddling; their
/// sum).
#[derive(Default)]
struct Stratum {
    count: usize,
    gap: [usize; 3],
    margin: [usize; 3],
    gap_sum: (Rat, Rat),
    margin_sum: (Rat, Rat),
    magnitude: (Rat, Rat),
    gap_least: Option<Rat>,
    gap_most: Option<Rat>,
    margin_least: Option<Rat>,
    margin_most: Option<Rat>,
    terms: usize,
    derivative: [usize; 5],
    derivative_sum: (Rat, Rat),
}

/// An enclosure's sign: 0 certainly positive, 1 certainly negative, 2 straddling zero.
fn sign_of(lower: &Rat, upper: &Rat) -> usize {
    if lower.is_positive() {
        0
    } else if upper.is_negative() {
        1
    } else {
        2
    }
}

impl Stratum {
    fn station(&mut self, gap: &ExactInterval, margin: &ExactInterval) {
        self.count += 1;
        self.gap[sign_of(&gap.lower, &gap.upper)] += 1;
        self.margin[sign_of(&margin.lower, &margin.upper)] += 1;
        self.gap_sum.0 += &gap.lower;
        self.gap_sum.1 += &gap.upper;
        self.margin_sum.0 += &margin.lower;
        self.margin_sum.1 += &margin.upper;
        // |γ| ∈ [dist(0, γ), max(|γ⁻|, |γ⁺|)].
        let far = gap.lower.abs().max(gap.upper.abs());
        let near = if sign_of(&gap.lower, &gap.upper) == 2 {
            Rat::zero()
        } else {
            gap.lower.abs().min(gap.upper.abs())
        };
        self.magnitude.0 += near;
        self.magnitude.1 += far;
        let least = |x: &mut Option<Rat>, v: &Rat| {
            if x.as_ref().is_none_or(|y| v < y) {
                *x = Some(v.clone());
            }
        };
        let most = |x: &mut Option<Rat>, v: &Rat| {
            if x.as_ref().is_none_or(|y| v > y) {
                *x = Some(v.clone());
            }
        };
        least(&mut self.gap_least, &gap.lower);
        most(&mut self.gap_most, &gap.upper);
        least(&mut self.margin_least, &margin.lower);
        most(&mut self.margin_most, &margin.upper);
    }

    /// A term's derivative along the carried move, against its term's grain (the width of its own
    /// enclosure): 0 exactly zero, 1 below the grain, 2 descending, 3 rising, 4 straddling.
    fn derivative(&mut self, d: &ExactInterval, grain: &Rat) {
        self.terms += 1;
        let kind = if d.lower.is_zero() && d.upper.is_zero() {
            0
        } else if d.lower.abs().max(d.upper.abs()) < *grain {
            1
        } else {
            match sign_of(&d.lower, &d.upper) {
                1 => 2,
                0 => 3,
                _ => 4,
            }
        };
        self.derivative[kind] += 1;
        self.derivative_sum.0 += &d.lower;
        self.derivative_sum.1 += &d.upper;
    }

    fn line(&self) -> String {
        let pair = |p: &(Rat, Rat)| cell(&ExactInterval { lower: p.0.clone(), upper: p.1.clone() }, 1 << 8);
        let point = |x: &Option<Rat>| {
            x.as_ref()
                .map_or_else(|| "-".to_string(), |v| cell(&ExactInterval::point(v.clone()), 1 << 8))
        };
        let mean = |p: &(Rat, Rat)| {
            if self.count == 0 {
                "-".to_string()
            } else {
                let n = Rat::from_integer(BigInt::from(self.count));
                cell(
                    &ExactInterval {
                        lower: &p.0 / &n,
                        upper: &p.1 / &n,
                    },
                    1 << 8,
                )
            }
        };
        format!(
            "stations {}; class gap (+, −, straddling) {:?}, Σ ∈ {}, least {}, most {}, Σ|γ| ∈ {}, mean |γ| ∈ {}; threshold margin (+, −, straddling) {:?}, Σ ∈ {}, least {}, most {}; terms of F's support {}, their derivative along the carried move (exactly zero, below its term's grain, descending, rising, straddling) {:?}, Σ ∈ {} nats",
            self.count,
            self.gap,
            pair(&self.gap_sum),
            point(&self.gap_least),
            point(&self.gap_most),
            pair(&self.magnitude),
            mean(&self.magnitude),
            self.margin,
            pair(&self.margin_sum),
            point(&self.margin_least),
            point(&self.margin_most),
            self.terms,
            self.derivative,
            pair(&self.derivative_sum)
        )
    }
}

/// `ln` of a growth's enclosure (both ends positive: the comparison's own terms read them).
fn ln_growth(growth: &holonics::hnn::ring::Growth) -> ExactInterval {
    let ln = |x: &Rat| holonics::ratio::algebraic::ln_enclosure(x).expect("a positive growth");
    ExactInterval {
        lower: ln(&growth.lower).lower,
        upper: ln(&growth.upper).upper,
    }
}

/// [definition; the pin §5] **D2, the comparison's operating point**, printed for one move: every
/// station comparison of the batch at `θ` (every refinement, and the open section apart), its
/// class gap `ln a_t − ln a_r` and threshold margin `ln a_t` as exact enclosures, stratified by
/// decision (right; wrong and eligible, a confident wrong decision the release would lock; wrong
/// and not eligible) and by request (constant or not), with each term of `F`'s support's
/// derivative along the carried move (`terms`, aligned with the move's `sites`).
fn print_d2(
    index: usize,
    moved: &ExecutedMove,
    constant: &[bool],
    terms: Option<&Vec<Option<ExactInterval>>>,
) {
    use holonics::hnn::executed::StationComparison;
    let kinds = ["right", "wrong, eligible (confident)", "wrong, not eligible"];
    // strata[open][decision][constant]
    let mut strata: Vec<Vec<Vec<Stratum>>> = (0..2)
        .map(|_| (0..3).map(|_| (0..2).map(|_| Stratum::default()).collect()).collect())
        .collect();
    let mut decision_of: BTreeMap<(usize, usize, usize), (usize, &StationComparison)> =
        BTreeMap::new();
    for (r, request) in moved.before.requests.iter().enumerate() {
        for s in &request.stations {
            let eligible = request
                .orders
                .iter()
                .find(|o| o.context == s.context)
                .is_some_and(|o| o.eligible.iter().any(|(station, _, _, _)| *station == s.station));
            let decision = if s.top == s.target {
                0
            } else if eligible {
                1
            } else {
                2
            };
            let t = ln_growth(&s.target_growth);
            let x = ln_growth(&s.rival_growth);
            let gap = ExactInterval {
                lower: &t.lower - &x.upper,
                upper: &t.upper - &x.lower,
            };
            let c = usize::from(constant[r]);
            strata[0][decision][c].station(&gap, &t);
            if s.context == 0 {
                strata[1][decision][c].station(&gap, &t);
            }
            decision_of.insert((r, s.context, s.station), (decision, s));
        }
    }
    if let Some(terms) = terms {
        for (site, term) in moved.sites.iter().zip(terms) {
            let Some(d) = term else { continue };
            let Some((decision, s)) = decision_of.get(&(site.request, site.context, site.station))
            else {
                continue;
            };
            let grain = &s.value.upper - &s.value.lower;
            let c = usize::from(constant[site.request]);
            strata[0][*decision][c].derivative(d, &grain);
            if site.context == 0 {
                strata[1][*decision][c].derivative(d, &grain);
            }
        }
    }
    for (open, scope) in ["every refinement", "the open section"].iter().enumerate() {
        for (decision, kind) in kinds.iter().enumerate() {
            for (c, request) in ["nonconstant", "constant"].iter().enumerate() {
                let stratum = &strata[open][decision][c];
                if stratum.count == 0 {
                    continue;
                }
                println!("    D2 move {index}, {scope}, {kind}, {request} requests: {}", stratum.line());
            }
        }
    }
}

/// [definition; the pin §5] **D1, the step's descent**, printed for one move: `F` at `θ` and its
/// grain; the unit slope, the modulus's share and the ladder's start (the first-order zero against
/// the entry scale, which binds); every trial; at the carried move (the adopted trial, else the last
/// trial whose first order was read) the step's norm, the lattice, passive and entry bounds, the
/// predicted descents (the certificate and the leading branches) against the measured, whether the
/// trajectory changed, the decisions moved at the open section, and the ideal listener's bits on
/// the batch.
fn print_d1(
    index: usize,
    moved: &ExecutedMove,
    theta: &Constitution,
    ring: usize,
    targets: &[Vec<usize>],
    information: &str,
) {
    use holonics::hnn::constitution::Locus;
    let before = &moved.before.value;
    let grain = &before.upper - &before.lower;
    let two = Rat::from_integer(BigInt::from(2));
    let point = |x: &Rat, g: i64| cell(&ExactInterval::point(x.clone()), g);
    let negated = |x: &ExactInterval| ExactInterval {
        lower: -x.upper.clone(),
        upper: -x.lower.clone(),
    };
    let mut line = format!(
        "    D1 move {index}: F(θ) ∈ {}, its grain (enclosure width) ∈ {} nats",
        cell(before, 1 << 12),
        point(&grain, 1 << 16)
    );
    let (Some(slope), Some(gamma), Some(unit), Some(largest)) = (
        &moved.slope,
        &moved.modulus_slope,
        &moved.modulus_unit,
        &moved.unit_largest,
    ) else {
        println!(
            "{line}; no descent proposed: {:?} (the unit slope {}); zero prediction",
            moved.refusal,
            moved.slope.as_ref().map_or_else(|| "not read".to_string(), |s| cell(s, 1 << 12))
        );
        println!("    D1 move {index}: the ideal listener on this batch: {information}");
        return;
    };
    let share = gamma * unit;
    let joint_upper = &slope.upper + &share;
    let zero = if joint_upper.is_negative() {
        Some(&before.lower / -joint_upper.clone())
    } else {
        None
    };
    let scale = Rat::new(BigInt::from(1), BigInt::from(2)) / largest;
    let binds = match &zero {
        Some(z) if *z <= scale => "the first-order zero",
        Some(_) => "the entry scale",
        None => "none (the joint slope is not negative)",
    };
    line += &format!(
        "; the unit slope ∈ {}, the modulus's share γ_ρΔρ {}, the first-order zero F⁻/(−slope⁺) {}, the entry scale ½/u {} (u = {largest}), binding: {binds}",
        cell(slope, 1 << 12),
        point(&share, 1 << 12),
        zero.as_ref().map_or_else(|| "none".to_string(), |z| point(z, 1 << 16)),
        point(&scale, 1 << 16)
    );
    println!("{line}");
    let trials: Vec<String> = moved
        .trials
        .iter()
        .map(|t| {
            format!(
                "η {} {}",
                t.step,
                match &t.refusal {
                    None => "adopted".to_string(),
                    Some(holonics::hnn::executed::TrialRefusal::NotBelow(v)) =>
                        format!("refused NotBelow(F ∈ {})", cell(v, 1 << 12)),
                    Some(holonics::hnn::executed::TrialRefusal::FirstOrder(v)) =>
                        format!("refused FirstOrder({})", cell(v, 1 << 12)),
                    Some(other) => format!("refused {other:?}"),
                }
            )
        })
        .collect();
    let entry_refusals = moved
        .trials
        .iter()
        .filter(|t| matches!(t.refusal, Some(holonics::hnn::executed::TrialRefusal::EntryBound(_))))
        .count();
    println!(
        "    D1 move {index}: the ladder: {} trials, {} halvings before {}; {}; trials refused by the entry bound {entry_refusals}",
        moved.trials.len(),
        moved.trials.len().saturating_sub(1),
        if moved.adopted.is_some() { "adoption" } else { "refusal" },
        trials.join(", ")
    );
    let Some(trial) = moved
        .adopted
        .as_ref()
        .and_then(|_| moved.trials.last())
        .or_else(|| moved.trials.iter().rev().find(|t| t.first_order.is_some()))
    else {
        println!("    D1 move {index}: no carried move read its first order: zero prediction");
        println!("    D1 move {index}: the ideal listener on this batch: {information}");
        return;
    };
    let lattice = theta.lattice(Locus::SourcePort(ring)).expect("the lattice").unit();
    let modulus = theta.transport(ring);
    let target = &modulus + &trial.step * unit;
    let passive = if target > Rat::one() {
        "at one"
    } else if target < &modulus / &two {
        "at ρ/2"
    } else {
        "not active"
    };
    let carried = trial.modulus.clone().unwrap_or_else(|| modulus.clone());
    let clipped = target.clone().max(&modulus / &two).min(Rat::one());
    let (squares, stepped, released) = match &trial.source {
        Some(source) => {
            let port = theta.source_port(ring).expect("E");
            let successor = moved.adopted.as_ref().map(|(s, _)| s);
            let squares = successor.map(|s| {
                s.source_port(ring)
                    .expect("E")
                    .subtract(port)
                    .expect("the move")
                    .entries()
                    .iter()
                    .map(|x| x * x)
                    .sum::<Rat>()
            });
            (squares, source.stepped, source.released.len())
        }
        None => (None, 0, 0),
    };
    println!(
        "    D1 move {index}: the carried move at η {} ({}): ‖ΔE‖_∞ {}, Σ ΔE² {}, entries whose lattice coordinate moved {stepped}, residuals released {released}, E's lattice unit {lattice}; ρ {modulus} → {carried} (Δρ {}), its target ρ + ηΔρ {} (passive bound {passive}; the lattice's rounding {}); E's largest entry {} against the entry bound 8",
        trial.step,
        if moved.adopted.is_some() { "adopted" } else { "refused" },
        trial.moved,
        squares.map_or_else(|| "not adopted".to_string(), |s| s.to_string()),
        &carried - &modulus,
        point(&target, 1 << 21),
        point(&(&carried - &clipped), 1 << 30),
        trial.largest
    );
    let Some(bound) = &trial.first_order else {
        return;
    };
    let certificate = negated(bound);
    let leading = trial.leading.as_ref().map(&negated);
    let measured = trial.value.as_ref().map(|after| ExactInterval {
        lower: &before.lower - &after.upper,
        upper: &before.upper - &after.lower,
    });
    let kind = if !certificate.upper.is_positive() {
        "zero (not positive)"
    } else if certificate.upper < grain {
        "below the grain"
    } else {
        "above the grain"
    };
    let eighth = |m: &ExactInterval| {
        let bar = &certificate.upper / Rat::from_integer(BigInt::from(8));
        if m.lower >= bar {
            "holds"
        } else if m.upper < &certificate.lower / Rat::from_integer(BigInt::from(8)) {
            "fails"
        } else {
            "undecided"
        }
    };
    let agree = match (&leading, &measured) {
        (Some(l), Some(m)) => {
            let (a, b) = (sign_of(&l.lower, &l.upper), sign_of(&m.lower, &m.upper));
            if a == 2 || b == 2 {
                "undecided"
            } else if a == b {
                "agree"
            } else {
                "opposite"
            }
        }
        _ => "not read",
    };
    println!(
        "    D1 move {index}: predicted descent, the certificate −Σ sup Df ∈ {} (exact enclosure; approximate as a prediction), the leading branches −Σ sign⟨ĝ, Δz⟩ ∈ {}; measured C(θ) − C(θ+δ) ∈ {} (exact); the prediction {kind}; measured at least 1/8 of the certificate: {}; the leading branches' sign and the measured's: {agree}",
        cell(&certificate, 1 << 12),
        leading.as_ref().map_or_else(|| "not read".to_string(), |l| cell(l, 1 << 12)),
        measured.as_ref().map_or_else(|| "not read".to_string(), |m| cell(m, 1 << 12)),
        measured.as_ref().map_or("not read", eighth)
    );
    if let Some(after) = &trial.after {
        let changed = moved
            .before
            .requests
            .iter()
            .zip(&after.requests)
            .filter(|(a, b)| {
                a.generation.as_ref().map(|g| &g.locks) != b.generation.as_ref().map(|g| &g.locks)
            })
            .count();
        // [wrong→right, right→wrong, wrong→another wrong, right kept, wrong kept]
        let mut moves = [0usize; 5];
        for (a, b) in moved.before.requests.iter().zip(&after.requests) {
            let open = |r: &holonics::hnn::executed::RequestComparison| -> BTreeMap<usize, (usize, usize)> {
                r.stations
                    .iter()
                    .filter(|s| s.context == 0)
                    .map(|s| (s.station, (s.top, s.target)))
                    .collect()
            };
            let (x, y) = (open(a), open(b));
            for (station, (top, target)) in &x {
                let Some((next, _)) = y.get(station) else { continue };
                let kind = match (top == target, next == target) {
                    (false, true) => 0,
                    (true, false) => 1,
                    (false, false) if next != top => 2,
                    (true, true) => 3,
                    (false, false) => 4,
                };
                moves[kind] += 1;
            }
        }
        let (whole, right, released) = after.sections(targets);
        println!(
            "    D1 move {index}: the successor's trajectory changed in {changed} of {} requests; at the open section, wrong→right {}, right→wrong {}, wrong→another wrong {}, right kept {}, wrong kept {}; the successor's batch: released {released}, whole {whole}, stations right {right}",
            moved.before.requests.len(),
            moves[0],
            moves[1],
            moves[2],
            moves[3],
            moves[4]
        );
    }
    println!("    D1 move {index}: the ideal listener on this batch: {information}");
}

/// The families the pin reads on a terrain (§1): the global family, and on the line `H` too.
fn families_of(terrain: &str, requests: usize) -> Vec<ReferenceFamily> {
    if terrain == "line" {
        vec![ReferenceFamily::global(), ReferenceFamily::hierarchical(requests)]
    } else {
        vec![ReferenceFamily::global()]
    }
}

/// **The terrain's counts** (`executed counts <terrain> <training seed> <requests> <validation
/// seed> <validation count> <out>`; the pin §1, §2, §4): the declared reference family read along
/// the machine's own training passage (the training requests in their order, station by station),
/// every observation's survivors and ratio written to `out`; `n*_terrain` at the stopping object
/// (the nonconstant validation requests, and all of them), the syntactic class, the certificate,
/// the unobserved arguments and lag aliases, the constant requests' bits apart, each batch's
/// information, and the training/validation content overlap. The line is read in `H` too.
pub(super) fn counts(
    terrain: &str,
    seed: u64,
    count: usize,
    validation_seed: u64,
    validation_count: usize,
    out: &str,
) {
    use std::fmt::Write as _;
    let clock = Instant::now();
    let declared = order_declared();
    let stations = declared.stations;
    let pairs = terrain_pairs(terrain, &declared, seed, count);
    let validation = terrain_pairs(terrain, &declared, validation_seed, validation_count);
    let batch = 8;
    let constant: Vec<usize> =
        (0..pairs.len()).filter(|&r| constant_request(&pairs[r].0)).collect();
    let validation_constant = validation.iter().filter(|(r, _)| constant_request(r)).count();
    let shared = validation
        .iter()
        .filter(|(v, _)| pairs.iter().any(|(t, _)| t == v))
        .count();
    let distinct_training: BTreeSet<&Vec<usize>> = pairs.iter().map(|(r, _)| r).collect();
    let distinct_validation: BTreeSet<&Vec<usize>> = validation.iter().map(|(r, _)| r).collect();
    println!(
        "executed counts: {terrain}, the training passage at seed {seed} ({count} requests, {} observations), validation at seed {validation_seed} ({validation_count} requests); the family: lag in [1, {LAGS}], a map of Z/{RESIDUES}",
        count * stations
    );
    println!(
        "  constant requests: training {} of {count} (requests {constant:?}), validation {validation_constant} of {validation_count}; distinct requests: training {}, validation {}; validation requests whose 40 cells equal a training request's: {shared} of {validation_count}",
        constant.len(),
        distinct_training.len(),
        distinct_validation.len()
    );
    let mut listing = String::new();
    for family in families_of(terrain, count) {
        let name = family.name();
        let size = family.size();
        let hierarchical = matches!(family, ReferenceFamily::Hierarchical { .. });
        // The stopping object, read where the survivors change (they only shrink, so the
        // continuations only shrink: the first count at which it holds is n*).
        let unique = |f: &ReferenceFamily, v: &(Vec<usize>, Vec<usize>), given: bool| {
            f.continuations(&v.0, stations, 2, given.then(|| v.1[0])).len() == 1
        };
        let holds = |f: &ReferenceFamily, all: bool, given: bool| {
            validation
                .iter()
                .filter(|v| all || !constant_request(&v.0))
                .all(|v| unique(f, v, given))
        };
        let (mut star, mut star_all, mut star_given) = (None, None, None);
        let mut star_family = None;
        let mut last_change = 0;
        if hierarchical && holds(&family, false, true) {
            star_given = Some(0);
        }
        let reading = read_passage(family, &pairs, |k, f, counts| {
            if counts[k] != counts[k - 1] {
                last_change = k;
                if star.is_none() && holds(f, false, false) {
                    star = Some(k);
                    star_family = Some(f.clone());
                }
                if star_all.is_none() && holds(f, true, false) {
                    star_all = Some(k);
                }
                if hierarchical && star_given.is_none() && holds(f, false, true) {
                    star_given = Some(k);
                }
            }
        });
        let counts = &reading.counts;
        writeln!(
            listing,
            "== {name} on {terrain}, seed {seed}: observation, request, station, value, #S, ratio #S_(k-1)/#S_k, its bits (2^-8 cells), the code log2(|K|/#S) (2^-8 cells)"
        )
        .unwrap();
        writeln!(listing, "0 - - - {} - - [0/256, 0/256]", counts[0]).unwrap();
        let mut constant_ratio = Rat::one();
        let mut nonconstant_ratio = Rat::one();
        for k in 1..counts.len() {
            let request = (k - 1) / stations;
            let station = (k - 1) % stations;
            let ratio = count_ratio(&counts[k - 1], &counts[k]);
            if constant.contains(&request) {
                constant_ratio *= &ratio;
            } else {
                nonconstant_ratio *= &ratio;
            }
            let code = count_ratio(&size, &counts[k]);
            writeln!(
                listing,
                "{k} {request} {station} {} {} {} {} {}",
                pairs[request].1[station],
                counts[k],
                ratio,
                cell(&bits(&ratio), 1 << 8),
                cell(&bits(&code), 1 << 8)
            )
            .unwrap();
        }
        let end = counts.last().expect("a count");
        println!(
            "  {name}: |K| = {size}; after the passage #S = {end}, the code log2(|K|/#S) ∈ {} bits; the alphabet's lower bound clog4 10240 = 7 observations",
            cell(&bits(&count_ratio(&size, end)), 1 << 8)
        );
        // The head of the ideal listener's curve (every observation in the receipts).
        let head = star
            .unwrap_or(0)
            .max(last_change.min(4 * stations))
            .min(counts.len() - 1);
        let curve: Vec<String> = (1..=head)
            .map(|k| format!("{k}:{}", count_ratio(&counts[k - 1], &counts[k])))
            .collect();
        println!(
            "  {name}: the curve's head, observation:ratio #S_(k-1)/#S_k, through observation {head}: {}",
            curve.join(" ")
        );
        println!(
            "  {name}: #S at the request boundaries 0 to 8: {}",
            (0..=8usize.min(count))
                .map(|r| counts[r * stations].to_string())
                .collect::<Vec<_>>()
                .join(" ")
        );
        match (star, &star_family) {
            (Some(k), Some(f)) => println!(
                "  {name}: n*_terrain (every nonconstant validation request's continuation unique) at {}; #S = {}; the code ∈ {} bits; survivors: {}; unobserved arguments: {}",
                both_units(k, stations),
                counts[k],
                cell(&bits(&count_ratio(&size, &counts[k])), 1 << 8),
                f.certificate(generating_key(terrain)),
                f.unobserved()
            ),
            _ => println!(
                "  {name}: n*_terrain not reached in the passage's {}: the stopping object does not hold",
                both_units(counts.len() - 1, stations)
            ),
        }
        match star_all {
            Some(k) => println!(
                "  {name}: with the constant validation requests included, the stopping object at {}",
                both_units(k, stations)
            ),
            None => println!(
                "  {name}: with the constant validation requests included, not reached"
            ),
        }
        if hierarchical {
            match star_given {
                Some(k) => println!(
                    "  {name}: given each validation request's own first station (its translation's reading), stations 1 to 7 unique at {}",
                    both_units(k, stations)
                ),
                None => println!(
                    "  {name}: given each validation request's own first station, not unique in the passage"
                ),
            }
        }
        println!(
            "  {name}: the syntactic class: the survivors last changed at {}; {end} survivors at the passage's end ({}); alive lags {:?}; survivors: {}; unobserved arguments: {}",
            both_units(last_change, stations),
            if *end == BigUint::from(1u32) { "one key" } else { "not one key" },
            reading.family.alive(),
            reading.family.certificate(generating_key(terrain)),
            reading.family.unobserved()
        );
        let final_distinct: Vec<usize> = validation
            .iter()
            .map(|v| reading.family.continuations(&v.0, stations, 1 << 12, None).len())
            .collect();
        let unique_nonconstant = validation
            .iter()
            .zip(&final_distinct)
            .filter(|(v, n)| !constant_request(&v.0) && **n == 1)
            .count();
        let unique_constant = validation
            .iter()
            .zip(&final_distinct)
            .filter(|(v, n)| constant_request(&v.0) && **n == 1)
            .count();
        println!(
            "  {name}: at the passage's end, validation requests with one admitted continuation: nonconstant {unique_nonconstant} of {}, constant {unique_constant} of {validation_constant}; distinct continuations per validation request (at most 4096 counted) {final_distinct:?}",
            validation_count - validation_constant
        );
        println!(
            "  {name}: the bits the constant training requests' observations carry: log2({constant_ratio}) ∈ {}; the nonconstant requests': log2({nonconstant_ratio}) ∈ {}",
            cell(&bits(&constant_ratio), 1 << 8),
            cell(&bits(&nonconstant_ratio), 1 << 8)
        );
        let per_batch = batch_information(counts, batch * stations);
        println!(
            "  {name}: each move's batch (8 requests, 64 observations), the ideal listener's ratio and bits: {}",
            per_batch
                .iter()
                .enumerate()
                .map(|(m, (ratio, b))| format!("move {m}: {ratio}, {}", cell(b, 1 << 8)))
                .collect::<Vec<_>>()
                .join("; ")
        );
    }
    #[allow(clippy::disallowed_methods)]
    std::fs::write(out, listing).expect("write the curve");
    println!(
        "executed counts: {} ms; resident {}",
        clock.elapsed().as_millis(),
        resident()
    );
}

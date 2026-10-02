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
//! cargo run --release -p holonics --example hnn_prediction -- executed witness <terrain> <seed> <count> <moves> <deadline ms> <out>
//! cargo run --release -p holonics --example hnn_prediction -- executed causal <terrain> <seed> <count> <label[=E]>…
//! cargo run --release -p holonics --example hnn_prediction -- executed segment <terrain> <seed> <count> <label=source>…
//! cargo run --release -p holonics --example hnn_prediction -- executed instants <terrain> <seed> <count> <label=source>…
//! cargo run --release -p holonics --example hnn_prediction -- executed direction <terrain> <seed> <count> <arm> <from> <toward> <out> <η>…
//! cargo run --release -p holonics --example hnn_prediction -- executed rho-slopes <terrain> <seed> <count> <arm> <label=source>…
//! cargo run --release -p holonics --example hnn_prediction -- executed witness-plane <terrain> <seed> <count> <arm> <toward> <out> <label=source>…
//! cargo run --release -p holonics --example hnn_prediction -- executed move-once <terrain> <seed> <count> <out> <label=state> <arm> <metric>…
//! cargo run --release -p holonics --example hnn_prediction -- executed margins <terrain> <seed> <count> <before state> <after state>
//! cargo run --release -p holonics --example hnn_prediction -- executed agreement <terrain> <seed> <count> <arm,arm,…> <label=source>…
//! cargo run --release -p holonics --example hnn_prediction -- executed span <terrain> <seed> <count> <arm> <toward> <label=source>…
//! cargo run --release -p holonics --example hnn_prediction -- executed route-plane <terrain> <seed> <count> <arm> <both|route|port> <toward> <label=state>…
//! ```
//!
//! - **Step 1b** (the
//!   [pin](../../records/2026-09-30_STEP_1B_THE_CANDIDATE_COMPARISON_PINNED_BEFORE_ITS_RUNS.md) §13):
//!   `executed train`'s arms are `<composition>-<reading>` (`lock-dec` the candidate, `lock-all`,
//!   `hinge-dec`, `hinge-all` 1a's law, `lock-tf` the teacher-forced diagnostic; `@ρ` or
//!   `~<checkpoint>` an opening), every arm on the same epochs under the same guards; each move
//!   prints D1 and D2 with the fixed mask's descent account beside the successor's own release, the
//!   terms' counts, the persistence reads, I4 at the release's locks and I7's ranks; checkpoints
//!   carry the complete continuing state (`Constitution::continuing_state`), and a remount of `E`
//!   and `ρ` alone is labelled partial. `executed witness` is gate A's constrained feasibility
//!   witness; `executed causal` is the causal reading (I6).
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
use holonics::hnn::constitution::ContinuingState;
use holonics::hnn::executed::{
    BatchComparison, Comparison, Composition, Context, Excess, ExecutedMove, Predicate, Reading,
    Request, SlopeSplit, compare, executed_move, pairing_receipt,
};
use holonics::hnn::prediction::BankPlacement;
use holonics::hnn::ring::{MemberCovector, turn};
use num_bigint::{BigInt, BigUint};
use num_traits::One;
use std::collections::BTreeSet;

/// [definition; agent-inferred, step 1b's pin §13.8] **An arm's declared comparison** by name:
/// `<composition>-<reading>`, the composition `hinge` (1a's `F`) or `lock` (the lock face `L`), the
/// reading `all` (every refinement), `dec` (the decisions), `tf` (teacher-forced left to right) or
/// `partition` (Stage 2's partitions, read with the hinge or the face at their one refinement).
/// Gate B's arms: `lock-dec` (the candidate), `lock-all`, `hinge-dec`, `hinge-all` (1a's law) and
/// `lock-tf` (the diagnostic), each from the same opening on the same epochs.
pub(super) fn arm_comparison(arm: &str) -> (Comparison, bool) {
    let (composition, reading) = arm
        .split_once('-')
        .expect("an arm: <hinge|lock>-<all|dec|tf|partition>");
    let composition = match composition {
        "hinge" => Composition::Hinge,
        "lock" => Composition::LockFace,
        "order" => Composition::LockOrder,
        _ => panic!("a composition: hinge | lock | order"),
    };
    let (reading, partition) = match reading {
        "all" => (Reading::Every, false),
        "dec" => (Reading::Decisions, false),
        "tf" => (Reading::TeacherForced, false),
        "forced" => (Reading::Forced, false),
        "fdec" => (Reading::ForcedDecisions, false),
        "partition" => (Reading::Every, true),
        _ => panic!("a reading: all | dec | tf | forced | fdec | partition"),
    };
    (
        Comparison {
            composition,
            reading,
        },
        partition,
    )
}

/// The composition's symbol in the receipts: `F` the hinge, `L` the lock face.
fn symbol(comparison: &Comparison) -> &'static str {
    match comparison.composition {
        Composition::Hinge => "F",
        Composition::LockFace => "L",
        Composition::LockOrder => "L+O",
    }
}

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
        "  {label}: {} ∈ {} nats over {} readings; class and threshold hold at {} of {} compared stations",
        symbol(&batch.comparison),
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
                .filter(|s| s.context == Some(order.context))
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

/// [definition; agent-inferred, step 1b's pin §13.6] **A checkpoint: the complete continuing state**
/// (`Constitution::continuing_state`): `E rows cols`, its rows and `rho ρ` first (the form a partial
/// remount reads), then the normal law's carried Gram and chart, its carried remainders, the
/// locus's clock, the commit and the storage product.
pub(super) fn write_state(theta: &Constitution, ring: usize) -> String {
    theta
        .continuing_state(ring)
        .expect("the executed move moves the source port alone")
        .to_text()
}

/// **A partial remount**: a written constitution read back as its source port `E` and, when the
/// file carries one, the source navigator's transport modulus `ρ` (the passage law of
/// September 30), on the declared opening; the normal law rebuilt from its prior (its carried Gram,
/// chart, remainders and clock lost). Exact for every reading of the release (which reads `E` and
/// `ρ` alone), partial for a continuing deposit: labelled so on stderr wherever one is read (stdout
/// is left to the readings, so the baseline's replay listing is unchanged).
pub(super) fn trained(opening: &Constitution, ring: usize, path: &str) -> Constitution {
    eprintln!(
        "remount {path}: partial (E and rho alone; the normal law's Gram, chart, remainders and clock are the prior's)"
    );
    let theta = opening
        .clone()
        .with_ports(ring, None, Some(read_port(path)), None)
        .expect("the trained E");
    match read_modulus(path) {
        Some(modulus) => theta.with_transport(ring, modulus).expect("the trained ρ"),
        None => theta,
    }
}

/// **A full remount**: a checkpoint's complete continuing state restored onto the declared opening
/// (`Constitution::continued`); refused where the file holds `E` and `ρ` alone.
pub(super) fn remounted(opening: &Constitution, path: &str) -> Constitution {
    #[allow(clippy::disallowed_methods)]
    let text = std::fs::read_to_string(path).expect("read the checkpoint");
    let state = ContinuingState::from_text(&text).expect("a complete continuing state");
    opening.clone().continued(&state).expect("the checkpoint continues the declared opening")
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
/// by the threshold and by a class rival with their terms' sum (the hinge's `Σ (f)_+`; every
/// lock-face term counted class-led with its `ℓ`), `γ_ρ` of the leading contributions by kind, and
/// every term's target part and rival part read alone (their sum is the slope).
pub(super) fn split_line(split: &SlopeSplit) -> String {
    let point = |x: &Rat| cell(&ExactInterval::point(x.clone()), 1 << 12);
    format!(
        "; split: threshold-led {} terms (their terms Σ {}, γ {}), class-led {} terms (their terms Σ {}, γ {}); every term read alone: the target's part {}, the class rival's part {}, the class branch {}",
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
        // 1a's comparison, the hinge at every refinement (the diagnostic's own).
        let (batch, split) = modulus_slopes(
            &engine.field,
            &theta,
            &requests,
            &engine.refinement,
            &bank,
            BANK_GRAIN,
            Comparison::HINGE_EVERY,
        )
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

/// **One arm's training** (`executed train <arm> <terrain> <seed> <batch> <moves> <deadline ms>
/// <out>`; Stage 2, and step 1b's gate-B arms). The arm is `<composition>-<reading>`
/// ([`arm_comparison`]) with its opening: `<arm>@ρ` the declared opening at the modulus `ρ` (a
/// development read), `<arm>~<checkpoint>` a complete continuing state restored onto the declared
/// opening (a full remount), the founded opening otherwise. Every arm reads the same requests in the
/// same epochs under the same ladder depth and guards (matched observation and move budgets; each
/// move's readings, its trials' and its wall time printed, so any extra computation is read). The
/// moves are the work bound, the deadline a guard (reaching it is reported incomplete). The complete
/// continuing state is written to `out` after every adopted move, and at the checkpoints after moves
/// 1, 2, 4, 8 and 16 (`<out>.m<k>`).
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
    let ring = engine.refinement.ring();
    let (arm_name, opening) = match (arm.split_once('~'), arm.split_once('@')) {
        (Some((name, path)), _) => (name, Some(Err(path))),
        (None, Some((name, modulus))) => {
            (name, Some(Ok(modulus.parse::<Rat>().expect("a rational ρ"))))
        }
        (None, None) => (arm, None),
    };
    let (comparison, partition) = arm_comparison(arm_name);
    let pairs = terrain_pairs(terrain, &declared, seed, batch * moves);
    let mut masks = Draw::new(STAGE_TWO_MASK_SEED);
    let requests: Vec<Request> = pairs
        .iter()
        .map(|(request, target)| {
            let (current, moment) = ingest(&engine.field, request);
            let context = if partition {
                Context::Partition(mask(&mut masks, declared.stations))
            } else {
                Context::Open
            };
            Request {
                current,
                moment,
                targets: target.clone(),
                context,
            }
        })
        .collect();
    let mut theta = match &opening {
        Some(Ok(modulus)) => engine
            .theta
            .clone()
            .with_transport(ring, modulus.clone())
            .expect("a passive modulus on the lattice"),
        Some(Err(path)) => remounted(&engine.theta, path),
        None => founded_opening(&engine),
    };
    println!(
        "executed train: arm {arm} ({:?} read at {:?}{}) on {terrain} at seed {seed}: {moves} moves of {batch} requests; the opening's transport modulus {}, its source clock {}; the bank p = {}, grain 2^(-{BANK_GRAIN})",
        comparison.composition,
        comparison.reading,
        if partition { ", on partitions" } else { "" },
        theta.transport(ring),
        theta.clock(holonics::hnn::constitution::Locus::SourcePort(ring)),
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
        let moved = executed_move(
            &engine.field,
            &theta,
            chunk,
            &engine.refinement,
            &bank,
            BANK_GRAIN,
            comparison,
        )
        .expect("the move");
        let trial_readings: usize = moved.trials.iter().map(|t| t.readings).sum();
        readings += moved.before.readings + trial_readings;
        // The slopes the move reads: the joint unit move's first order (the guard), the port's part
        // alone (a receipt), the excess's piecewise derivative (the ladder's start), and the
        // modulus's `γ_ρ` (none upward from `ρ = 1`).
        let point = |x: &Option<Rat>, g: i64| {
            x.as_ref()
                .map_or_else(|| "none".to_string(), |v| cell(&ExactInterval::point(v.clone()), g))
        };
        let interval = |x: &Option<ExactInterval>| {
            x.as_ref().map_or_else(|| "none".to_string(), |v| cell(v, 1 << 12))
        };
        let slopes = format!(
            "; the joint unit slope {}, the port's alone {}, the excess's {}; the modulus's slope γ_ρ {}{}; the modulus's curvature G_ρ {}, its least-squares unit move {}",
            interval(&moved.slope),
            interval(&moved.port_slope),
            interval(&moved.excess_slope),
            point(&moved.modulus_slope, 1 << 12),
            moved.split.as_ref().map_or_else(String::new, split_line),
            point(&moved.modulus_curvature, 1 << 12),
            point(&moved.modulus_unit, 1 << 16)
        );
        let sections = if partition {
            String::new()
        } else {
            let targets: Vec<Vec<usize>> = chunk.iter().map(|r| r.targets.clone()).collect();
            let (whole, right, released) = moved.before.sections(&targets);
            format!("; batch released {released}, whole {whole}, stations right {right}")
        };
        // D1 and D2 (the pin §5; step 1b's §9), read from the move's receipt at `θ`.
        let targets: Vec<Vec<usize>> = chunk.iter().map(|r| r.targets.clone()).collect();
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
        print_ranks(index, &moved.before, declared.alphabet);
        match &moved.adopted {
            Some((successor, step)) => {
                adopted += 1;
                let last = moved.trials.last().expect("the adopted trial");
                println!(
                    "  move {index}: adopted at step {} (trial {} of the ladder); {} {} → {} on the fixed mask (the successor's own release {}); E's largest entry {}; transport modulus {} → {}{sections}; readings at θ {}, in the trials {trial_readings}; {} ms",
                    step.step,
                    moved.trials.len(),
                    symbol(&comparison),
                    cell(&moved.before.value, 1 << 12),
                    last.value.as_ref().map_or_else(String::new, |v| cell(v, 1 << 12)),
                    last.after.as_ref().map_or_else(String::new, |a| cell(&a.value, 1 << 12)),
                    step.largest,
                    theta.transport(ring),
                    successor.transport(ring),
                    moved.before.readings,
                    started.elapsed().as_millis()
                );
                println!("    move {index}{slopes}");
                theta = successor.clone();
                // The adopted constitution's complete continuing state written at every move, so
                // a run stopped by its process guard leaves its last certified successor.
                #[allow(clippy::disallowed_methods)]
                std::fs::write(out, write_state(&theta, ring)).expect("write the state");
            }
            None => {
                refused += 1;
                println!(
                    "  move {index}: refused {:?} after {} trials; {} {}{sections}; readings at θ {}, in the trials {trial_readings}; {} ms",
                    moved.refusal,
                    moved.trials.len(),
                    symbol(&comparison),
                    cell(&moved.before.value, 1 << 12),
                    moved.before.readings,
                    started.elapsed().as_millis()
                );
                println!("    move {index}{slopes}");
            }
        }
        // The checkpoints (the pin §4): the constitution after moves 1, 2, 4, 8 and 16.
        if CHECKPOINTS.contains(&(index + 1)) {
            let path = format!("{out}.m{}", index + 1);
            #[allow(clippy::disallowed_methods)]
            std::fs::write(&path, write_state(&theta, ring)).expect("write the state");
            println!("  checkpoint after move {} (the complete continuing state): {path}", index + 1);
        }
    }
    #[allow(clippy::disallowed_methods)]
    std::fs::write(out, write_state(&theta, ring)).expect("write the state");
    println!(
        "executed train: arm {arm}: {adopted} moves adopted, {refused} refused, {readings} readings (at θ and in the trials); {}; {} ms; resident {}",
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

/// A written constitution remounted onto the declared opening: whole where the file holds a complete
/// continuing state, else partial (`E` and `ρ` alone, labelled on stderr by [`trained`]).
pub(super) fn remount(opening: &Constitution, ring: usize, path: &str) -> Constitution {
    #[allow(clippy::disallowed_methods)]
    let text = std::fs::read_to_string(path).expect("read the constitution");
    match ContinuingState::from_text(&text) {
        Ok(state) => opening
            .clone()
            .continued(&state)
            .expect("the checkpoint continues the declared opening"),
        Err(_) => trained(opening, ring, path),
    }
}

/// The requests of a known-truth terrain, each ingested, compared along the machine's own release.
pub(super) fn open_requests(engine: &Engine, pairs: &[(Vec<usize>, Vec<usize>)]) -> Vec<Request> {
    pairs
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
        .collect()
}

/// The decision terms in the lock face's solved level (the strict rational test), of those read.
pub(super) fn solved_terms(batch: &BatchComparison) -> (usize, usize) {
    let terms = batch.requests.iter().flat_map(|r| &r.terms);
    let (mut solved, mut all) = (0, 0);
    for term in terms {
        all += 1;
        solved += usize::from(term.comparison.solved == Predicate::Holds);
    }
    (solved, all)
}

/// Every decision term of a batch, whole: its request, station, decision refinement, target and top,
/// the lock face `ℓ` enclosed, its solved test, `θ_t`, and the target's and leading rival's joint
/// enclosures; with each request's release.
pub(super) fn print_terms(label: &str, batch: &BatchComparison, targets: &[Vec<usize>]) {
    for (index, (request, target)) in batch.requests.iter().zip(targets).enumerate() {
        let released = request.generation.as_ref().map_or_else(
            || "not released".to_string(),
            |g| {
                format!(
                    "{} {:?}, locks {:?}",
                    if g.release.released() { "released" } else { "held" },
                    g.release.classes,
                    g.locks
                )
            },
        );
        println!("    {label} request {index}: target {target:?}; {released}; r* {:?}", request.consistent);
        for term in &request.terms {
            let s = &term.comparison;
            println!(
                "      station {} at refinement {:?}: target {}, top {}, ℓ ∈ {} nats, solved {:?} ({:?}), θ_t ∈ {}, target [{}, {}], leading rival [{}, {}]",
                s.station,
                term.site.context,
                s.target,
                s.top,
                cell(&s.lock, 1 << 16),
                s.solved,
                term.kind,
                cell(&s.share, 1 << 16),
                s.target_growth.lower,
                s.target_growth.upper,
                s.rival_growth.lower,
                s.rival_growth.upper
            );
        }
    }
}

/// **A move's line in gate A's witness format** (`executed witness`, exactly): its adoption or
/// refusal, the ladder's start, every trial's step and refusal, the owner's persistence reads at the
/// incumbent, and the move's wall time. Loop 1c's `executed resume-coupling` prints its move through
/// this one formatter, so its identity check reads the same text gate A printed.
pub(super) fn move_line(index: usize, moved: &ExecutedMove, ms: u128) -> String {
    format!(
        "    move {index}: {}; the ladder's start {:?}; trials {}; persistence {:?}; {ms} ms",
        match &moved.adopted {
            Some((_, step)) => format!("adopted at step {}", step.step),
            None => format!("refused {:?}", moved.refusal),
        },
        moved.start,
        moved
            .trials
            .iter()
            .map(|t| format!("η {} {:?}", t.step, t.refusal.as_ref().map(|_| "refused")))
            .collect::<Vec<_>>()
            .join(", "),
        moved.persistence,
    )
}

/// **A move's trials whole** (the native direction record's guard): each trial's step, its carried
/// modulus, the fixed mask's composition, the own release's executed composition, and its refusal by
/// kind, so a step refused past the trajectory cell (`OwnNotBelow`) is read apart from one refused on
/// the mask (`NotBelow`).
pub(super) fn trial_line(moved: &ExecutedMove) -> String {
    let trials: Vec<String> = moved
        .trials
        .iter()
        .map(|t| {
            format!(
                "η {} ρ {} mask {} own {} {}",
                t.step,
                t.modulus.as_ref().map_or_else(|| "unmoved".to_string(), ToString::to_string),
                t.value.as_ref().map_or_else(|| "not read".to_string(), |v| cell(v, 1 << 12)),
                t.after
                    .as_ref()
                    .map_or_else(|| "not read".to_string(), |a| cell(&a.value, 1 << 12)),
                match &t.refusal {
                    None => "adopted".to_string(),
                    Some(holonics::hnn::executed::TrialRefusal::NotBelow(_)) => "NotBelow".to_string(),
                    Some(holonics::hnn::executed::TrialRefusal::OwnNotBelow(_)) => "OwnNotBelow".to_string(),
                    Some(holonics::hnn::executed::TrialRefusal::FirstOrder(_)) => "FirstOrder".to_string(),
                    Some(other) => format!("{other:?}"),
                }
            )
        })
        .collect();
    format!(
        "      trials: {}; γ_ρ {}",
        trials.join("; "),
        moved
            .modulus_slope
            .as_ref()
            .map_or_else(|| "not read".to_string(), |g| cell(&ExactInterval::point(g.clone()), 1 << 12))
    )
}

/// [definition; agent-inferred, step 1b's gate A: the pin §13.3 and its gate-A addendum] **The
/// constrained feasibility witness** (`executed witness <terrain> <seed> <count> <moves> <deadline
/// ms> <out>`). From the founded opening, the candidate's own certified move (the lock face at the
/// decisions, every commit guard) is iterated on one declared development batch, every epoch the
/// same `count` requests, read from the open section by the release's actual executed contexts.
/// It stops at a witness (the strict solved test `1 + Σ_(x≠t) U_x < L_t` at every station's
/// decision term of every request), at a refused move (the batch is fixed, so a refused move leaves
/// the constitution and the next move's reading unchanged: it would repeat exactly), when the moves
/// are spent, or at the deadline (checked before each move). Every constitution read prints its
/// solved stations, whole sections, `L`, `X` and the source port's largest entry and modulus; the
/// best (the most stations solved, the earliest among equals) is written to `out` as its complete
/// continuing state, and printed whole. The procedure and its budget are pinned in the pin's gate-A
/// addendum before the run; the budget is never raised.
pub(super) fn witness(
    terrain: &str,
    seed: u64,
    count: usize,
    moves: usize,
    deadline: u128,
    out: &str,
    states: Option<&str>,
) {
    let clock = Instant::now();
    let declared = order_declared();
    let engine = Engine::new(declared);
    let bank = bank_of(declared.period, &bank_strength());
    let ring = engine.refinement.ring();
    let pairs = terrain_pairs(terrain, &declared, seed, count);
    let requests = open_requests(&engine, &pairs);
    let targets: Vec<Vec<usize>> = pairs.iter().map(|(_, t)| t.clone()).collect();
    let comparison = Comparison::LOCK_DECISIONS;
    let mut theta = founded_opening(&engine);
    println!(
        "executed witness: {count} {terrain} requests at development seed {seed}; the candidate's move (the lock face at the decisions) iterated on them from the founded opening (ρ = {}), at most {moves} moves, deadline {deadline} ms; the bank p = {}, grain 2^(-{BANK_GRAIN})",
        theta.transport(ring),
        bank_strength()
    );
    let largest = |theta: &Constitution| {
        theta
            .source_port(ring)
            .expect("E")
            .entries()
            .iter()
            .map(|x| x.abs())
            .max()
            .unwrap_or_else(Rat::zero)
    };
    let report = |label: &str, theta: &Constitution, batch: &BatchComparison, ms: u128| {
        let (solved, all) = solved_terms(batch);
        let (whole, right, released) = batch.sections(&targets);
        println!(
            "  {label}: solved {solved} of {all} decision terms; whole sections {whole} of {count} (released {released}, stations right {right}); L ∈ {} nats, X ∈ {} nats; E's largest entry {}, ρ {}; the terms {:?}; {ms} ms",
            cell(&batch.value, 1 << 12),
            cell(&batch.excess, 1 << 12),
            largest(theta),
            theta.transport(ring),
            batch.counts(declared.stations)
        );
        (solved, all)
    };
    // Loop 1c's replay (its pin §1.1): with a states directory, every constitution read is written
    // as its complete continuing state, `c<k>.state`; nothing else of the procedure changes.
    let keep_state = |index: usize, theta: &Constitution| {
        if let Some(dir) = states {
            #[allow(clippy::disallowed_methods)]
            std::fs::write(format!("{dir}/c{index}.state"), write_state(theta, ring))
                .expect("write a constitution's state");
        }
    };
    let mut best: Option<(usize, String, Constitution, BatchComparison)> = None;
    let mut keep = |solved: usize, label: String, theta: &Constitution, batch: &BatchComparison| {
        if best.as_ref().is_none_or(|(s, ..)| solved > *s) {
            best = Some((solved, label, theta.clone(), batch.clone()));
        }
    };
    let mut found = false;
    let mut stop = "the moves are spent".to_string();
    let mut incomplete = false;
    for index in 0..moves {
        if clock.elapsed().as_millis() > deadline {
            stop = format!("the deadline, before move {index} (incomplete)");
            incomplete = true;
            break;
        }
        let started = Instant::now();
        let moved = executed_move(
            &engine.field,
            &theta,
            &requests,
            &engine.refinement,
            &bank,
            BANK_GRAIN,
            comparison,
        )
        .expect("the move");
        let label = format!("constitution {index} (before move {index})");
        let (solved, all) = report(&label, &theta, &moved.before, started.elapsed().as_millis());
        keep_state(index, &theta);
        keep(solved, label, &theta, &moved.before);
        if solved == all {
            found = true;
            stop = format!("a witness at constitution {index}");
            break;
        }
        println!("{}", move_line(index, &moved, started.elapsed().as_millis()));
        println!("{}", trial_line(&moved));
        match moved.adopted {
            Some((successor, _)) => theta = successor,
            None => {
                stop = format!("move {index} refused, {:?} (the batch is fixed: the next move would repeat it)", moved.refusal);
                break;
            }
        }
        if index + 1 == moves {
            let started = Instant::now();
            let last = compare(
                &engine.field,
                &theta,
                &requests,
                &engine.refinement,
                &bank,
                BANK_GRAIN,
                comparison,
            )
            .expect("the last constitution's reading");
            let label = format!("constitution {} (after the last move)", index + 1);
            let (solved, all) = report(&label, &theta, &last, started.elapsed().as_millis());
            keep_state(index + 1, &theta);
            keep(solved, label, &theta, &last);
            if solved == all {
                found = true;
                stop = format!("a witness at constitution {}", index + 1);
            }
        }
    }
    let (solved, label, theta_best, batch) = best.expect("at least one constitution read");
    #[allow(clippy::disallowed_methods)]
    std::fs::write(out, write_state(&theta_best, ring)).expect("write the state");
    let all = solved_terms(&batch).1;
    if found {
        println!("executed witness: FOUND at {label}: the strict solved test holds at all {all} decision terms; written to {out}");
    } else {
        println!(
            "executed witness: no witness found within this procedure and budget (stopped at {stop}); the best: {solved} of {all} decision terms solved, at {label}; written to {out}"
        );
    }
    print_terms(&label, &batch, &targets);
    println!(
        "executed witness: stopped at {stop}; {} ms; resident {}",
        clock.elapsed().as_millis(),
        resident()
    );
    // Loop 1c's launcher (Astra's review of `722c3334`): a procedure stopped by its own deadline is
    // incomplete and exits so, never read as success; its listing is unchanged.
    if incomplete {
        std::process::exit(super::loop_1c::INCOMPLETE);
    }
}

/// [definition; step 1b's pin §8 I6] **The causal reading** (`executed causal <terrain> <seed>
/// <count> <label[=E]>…`, `lossless` the declared opening, `opening` the founded one, a written
/// constitution remounted otherwise): per constitution, each request's stations read at the
/// teacher-forced section (every earlier station at its target, the rest open), the five candidates
/// by the joint growth: the stations whose class predicate holds, whose threshold holds, in the lock
/// face's solved level, and the target's rank among the five (0 the top), by station; beside them,
/// the release's first lock's station and whether it is right.
pub(super) fn causal(terrain: &str, seed: u64, count: usize, arms: &[String]) {
    let clock = Instant::now();
    let declared = order_declared();
    let engine = Engine::new(declared);
    let bank = bank_of(declared.period, &bank_strength());
    let ring = engine.refinement.ring();
    let pairs = terrain_pairs(terrain, &declared, seed, count);
    let requests = open_requests(&engine, &pairs);
    let comparison = Comparison {
        composition: Composition::LockFace,
        reading: Reading::TeacherForced,
    };
    println!("executed causal: {count} {terrain} requests at seed {seed}, each station read with the earlier stations at their targets");
    for arm in arms {
        let started = Instant::now();
        let (label, path) = arm.split_once('=').unwrap_or((arm.as_str(), ""));
        let theta = match (label, path.is_empty()) {
            ("lossless", true) => engine.theta.clone(),
            (_, true) => founded_opening(&engine),
            (_, false) => remount(&engine.theta, ring, path),
        };
        let batch = compare(
            &engine.field,
            &theta,
            &requests,
            &engine.refinement,
            &bank,
            BANK_GRAIN,
            comparison,
        )
        .expect("the causal reading");
        let stations = declared.stations;
        let (mut class, mut threshold, mut solved) = (vec![0usize; stations], vec![0usize; stations], vec![0usize; stations]);
        let mut ranks = vec![0usize; declared.alphabet];
        let (mut first, mut first_right) = (BTreeMap::<usize, usize>::new(), 0usize);
        for (request, (_, target)) in batch.requests.iter().zip(&pairs) {
            for term in &request.terms {
                let s = &term.comparison;
                class[s.station] += usize::from(s.class == Predicate::Holds);
                threshold[s.station] += usize::from(s.threshold == Predicate::Holds);
                solved[s.station] += usize::from(term.kind == Excess::Solved);
                ranks[s.rank.min(declared.alphabet - 1)] += 1;
            }
            if let Some(generation) = &request.generation
                && let Some((station, class, ..)) = generation.decisions.first()
            {
                *first.entry(*station).or_default() += 1;
                first_right += usize::from(*class == target[*station]);
            }
        }
        println!(
            "  {label} (ρ = {}): class holds {} by station {class:?}; threshold holds {} by station {threshold:?}; solved {} by station {solved:?}; the target's rank among the five (0 the top) {ranks:?}; the first lock's station {first:?}, right {first_right}; {} ms",
            theta.transport(ring),
            class.iter().sum::<usize>(),
            threshold.iter().sum::<usize>(),
            solved.iter().sum::<usize>(),
            started.elapsed().as_millis()
        );
    }
    println!("executed causal: {} ms; resident {}", clock.elapsed().as_millis(), resident());
}

/// A constitution by its source ([`segment`]): `opening` the founded opening, `lossless` the declared
/// opening, `<source>@<ρ>` the source's `E` at the modulus `ρ`, `<A>+<B>:<s>` the chord
/// `(1 − s)Θ_A + sΘ_B` in `E` and `ρ` (each entry exact; `ρ` must lie on the source port's lattice),
/// a written constitution otherwise ([`remount`]).
fn segment_source(engine: &Engine, ring: usize, spec: &str) -> Constitution {
    if let Some((ends, s)) = spec.rsplit_once(':')
        && let Some((a, b)) = ends.split_once('+')
    {
        let s = s.parse::<Rat>().expect("a rational s");
        let (a, b) = (segment_source(engine, ring, a), segment_source(engine, ring, b));
        let (ea, eb) = (a.source_port(ring).expect("E"), b.source_port(ring).expect("E"));
        let columns = ea.columns();
        let mixed: Vec<Rat> = ea
            .entries()
            .iter()
            .zip(eb.entries())
            .map(|(x, y)| x + &(&s * &(y - x)))
            .collect();
        let rows = mixed.chunks(columns).map(<[Rat]>::to_vec).collect();
        let (ra, rb) = (a.transport(ring), b.transport(ring));
        let modulus = &ra + &(&s * &(&rb - &ra));
        return engine
            .theta
            .clone()
            .with_ports(ring, None, Some(ExactRatMatrix::new(rows).expect("E")), None)
            .expect("the chord's E")
            .with_transport(ring, modulus)
            .expect("the chord's ρ on the lattice");
    }
    if let Some((source, modulus)) = spec.rsplit_once('@') {
        let modulus = modulus.parse::<Rat>().expect("a rational ρ");
        return segment_source(engine, ring, source)
            .with_transport(ring, modulus)
            .expect("a passive modulus on the lattice");
    }
    match spec {
        "opening" => founded_opening(engine),
        "lossless" => engine.theta.clone(),
        path => remount(&engine.theta, ring, path),
    }
}

/// The Frobenius pairing of two matrices of one shape, exactly.
fn frobenius(a: &ExactRatMatrix, b: &ExactRatMatrix) -> Rat {
    a.entries().iter().zip(b.entries()).map(|(x, y)| x * y).sum()
}

/// [definition; agent-inferred, October 1; the
/// [pin](../../records/2026-10-01_THE_NATIVE_DIRECTION_PINNED_BEFORE_ITS_RUN.md)] **The native
/// direction** (`executed direction <terrain> <seed> <count> <arm> <from> <toward> <out> <η>…`,
/// sources as [`segment_source`]): read-only. At `from`, the committed move's unit step as
/// `executed_move` forms it (`hnn::executed::unit_direction`): `ΔE` through the normal law's chart,
/// the plain pullback `G` of the same returns, and `Δρ`. Each is paired with `E_toward − E_from`
/// (the pairing's sign and its squared cosine, exactly). Then for each `η`, the constitution
/// `(E + ηΔE, ρ + ηΔρ)` (`ρ` floored onto the source port's lattice) is read by the arm's comparison
/// and written to `<out>/eta-<k>.txt` (`E` and `ρ`, a partial remount's form). No move is made.
#[allow(clippy::too_many_arguments)]
pub(super) fn direction(
    terrain: &str,
    seed: u64,
    count: usize,
    arm: &str,
    from: &str,
    toward: &str,
    out: &str,
    steps: &[String],
) {
    use holonics::hnn::executed::unit_direction;
    let clock = Instant::now();
    let declared = order_declared();
    let engine = Engine::new(declared);
    let bank = bank_of(declared.period, &bank_strength());
    let ring = engine.refinement.ring();
    let pairs = terrain_pairs(terrain, &declared, seed, count);
    let requests = open_requests(&engine, &pairs);
    let targets: Vec<Vec<usize>> = pairs.iter().map(|(_, t)| t.clone()).collect();
    let (comparison, partition) = arm_comparison(arm);
    assert!(!partition, "the direction is read on the open section");
    println!(
        "executed direction: {count} {terrain} requests at development seed {seed}, the arm {arm}, from {from} toward {toward}; the bank p = {}, grain 2^(-{BANK_GRAIN})",
        bank_strength()
    );
    let theta = segment_source(&engine, ring, from);
    let goal = segment_source(&engine, ring, toward);
    let started = Instant::now();
    let reading = unit_direction(
        &engine.field,
        &theta,
        &requests,
        &engine.refinement,
        &bank,
        BANK_GRAIN,
        comparison,
    )
    .expect("the unit direction");
    let e = theta.source_port(ring).expect("E").clone();
    let route = goal.source_port(ring).expect("E").subtract(&e).expect("one shape");
    let route_rho = goal.transport(ring) - theta.transport(ring);
    let route_norm = frobenius(&route, &route);
    let point = |x: &Rat, grain: i64| cell(&ExactInterval::point(x.clone()), grain);
    let align = |m: &ExactRatMatrix| {
        let pairing = frobenius(m, &route);
        let norm = frobenius(m, m);
        let cosine = if norm.is_zero() || route_norm.is_zero() {
            "none".to_string()
        } else {
            point(&(&pairing * &pairing / (&norm * &route_norm)), 1 << 12)
        };
        let sign = if pairing.is_positive() {
            "positive"
        } else if pairing.is_zero() {
            "zero"
        } else {
            "negative"
        };
        format!("pairing with the route {sign}, squared cosine {cosine}, largest entry {}", largest_of(m))
    };
    let (solved, all) = solved_terms(&reading.before);
    let (whole, right, released) = reading.before.sections(&targets);
    let (Some(unit), Some(pullback), Some(modulus)) =
        (&reading.unit_move, &reading.pullback, &reading.modulus_unit)
    else {
        println!(
            "  from: refused before the step, {:?}; {} ms",
            reading.refusal,
            started.elapsed().as_millis()
        );
        return;
    };
    println!(
        "  from ({from}): ρ {}; {} ∈ {} nats; solved {solved} of {all}; whole {whole} (released {released}, stations right {right}); the route's ρ change {}; ΔE (through the chart): {}; G (the plain pullback): {}; Δρ ∈ {} (γ_ρ ∈ {}); {} ms",
        theta.transport(ring),
        symbol(&comparison),
        cell(&reading.before.value, 1 << 12),
        route_rho,
        align(unit),
        align(pullback),
        point(modulus, 1 << 21),
        point(reading.modulus_slope.as_ref().expect("γ_ρ"), 1 << 12),
        started.elapsed().as_millis()
    );
    let lattice = Rat::new(BigInt::one(), BigInt::from(1u64 << 21));
    for (k, step) in steps.iter().enumerate() {
        let started = Instant::now();
        let eta = step.parse::<Rat>().expect("a rational step");
        let moved: Vec<Rat> = e
            .entries()
            .iter()
            .zip(unit.entries())
            .map(|(x, d)| x + &(&eta * d))
            .collect();
        let rows: Vec<Vec<Rat>> = moved.chunks(e.columns()).map(<[Rat]>::to_vec).collect();
        let raw = theta.transport(ring) + &eta * modulus;
        let modulus_eta = (&raw / &lattice).floor() * &lattice;
        let successor = engine
            .theta
            .clone()
            .with_ports(ring, None, Some(ExactRatMatrix::new(rows.clone()).expect("E")), None)
            .expect("the successor's E")
            .with_transport(ring, modulus_eta.clone())
            .expect("a passive modulus on the lattice");
        let mut text = format!("E {} {}\n", rows.len(), e.columns());
        for row in &rows {
            text.push_str(&row.iter().map(ToString::to_string).collect::<Vec<_>>().join(" "));
            text.push('\n');
        }
        text.push_str(&format!("rho {modulus_eta}\n"));
        #[allow(clippy::disallowed_methods)]
        std::fs::write(format!("{out}/eta-{k}.txt"), text).expect("write the successor");
        let batch = compare(
            &engine.field,
            &successor,
            &requests,
            &engine.refinement,
            &bank,
            BANK_GRAIN,
            comparison,
        )
        .expect("the successor's reading");
        let (solved, all) = solved_terms(&batch);
        let (whole, right, released) = batch.sections(&targets);
        let first: Vec<String> = batch
            .requests
            .iter()
            .zip(&targets)
            .filter_map(|(r, t)| {
                r.generation.as_ref().and_then(|g| {
                    g.decisions.first().map(|(s, c, ..)| {
                        format!("{s}{}", if *c == t[*s] { "+" } else { "-" })
                    })
                })
            })
            .collect();
        println!(
            "  η {eta} (eta-{k}): ρ {modulus_eta}; {} ∈ {} nats; solved {solved} of {all}; whole {whole} (released {released}, stations right {right}); first locks {}; the terms {:?}; {} ms",
            symbol(&comparison),
            cell(&batch.value, 1 << 12),
            first.join(" "),
            batch.counts(declared.stations),
            started.elapsed().as_millis()
        );
    }
    println!("executed direction: {} ms; resident {}", clock.elapsed().as_millis(), resident());
}

/// [measured-diagnostic; agent-inferred, October 1; the
/// [one-move pin](../../records/2026-10-01_ONE_GUARDED_MOVE_FROM_THE_STUCK_STATE_PINNED_BEFORE_ITS_RUN.md)]
/// **One committed move from a state under each declared metric** (`executed move-once <terrain>
/// <seed> <count> <out> <label=state> <arm> <metric>…`, the arm as [`arm_comparison`], `metric`
/// `coordinate`, `witness`, `kinetic` or `kinetic-modulus`, the state
/// a complete continuing state, restored with no `E`/`ρ` fallback ([`remounted`])): the candidate
/// arm's real proposal, guards, ladder and state carry (`hnn::executed::executed_move_in`), every
/// metric from the same restored state. The metrics are attempted in order and the first adopted
/// move ends the run (Astra's attribution: the control first; the witness only if it refuses). Each
/// prints the incumbent's reading, the move's line with every trial, the witness's form where read,
/// and the adopted successor's own release (its trial's reading), written to
/// `<out>/<label>-<metric>.state`.
pub(super) fn move_once(terrain: &str, seed: u64, count: usize, out: &str, source: &str, arm: &str, metrics: &[String]) {
    use holonics::hnn::executed::{MoveMetric, executed_move_in};
    let clock = Instant::now();
    let declared = order_declared();
    let engine = Engine::new(declared);
    let bank = bank_of(declared.period, &bank_strength());
    let ring = engine.refinement.ring();
    let pairs = terrain_pairs(terrain, &declared, seed, count);
    let requests = open_requests(&engine, &pairs);
    let targets: Vec<Vec<usize>> = pairs.iter().map(|(_, t)| t.clone()).collect();
    let (comparison, partition) = arm_comparison(arm);
    assert!(!partition, "one move reads the open section");
    let (label, spec) = source.split_once('=').expect("<label>=<source>");
    let theta = remounted(&engine.theta, spec);
    println!(
        "executed move-once: {count} {terrain} requests at development seed {seed}, the candidate arm, from {label} (ρ {}); the bank p = {}, grain 2^(-{BANK_GRAIN})",
        theta.transport(ring),
        bank_strength()
    );
    let report = |what: &str, batch: &BatchComparison, rho: &Rat, ms: u128| {
        let (solved, all) = solved_terms(batch);
        let (whole, right, released) = batch.sections(&targets);
        println!(
            "  {what}: ρ {rho}; L ∈ {} nats, X ∈ {} nats; solved {solved} of {all}; whole {whole} (released {released}, stations right {right}); {ms} ms",
            cell(&batch.value, 1 << 12),
            cell(&batch.excess, 1 << 12),
        );
    };
    for name in metrics {
        let metric = match name.as_str() {
            "coordinate" => MoveMetric::Coordinate,
            "witness" => MoveMetric::Witness,
            "kinetic" => MoveMetric::Kinetic,
            "kinetic-modulus" => MoveMetric::KineticModulus,
            other => panic!("a metric, coordinate, witness, kinetic or kinetic-modulus: {other}"),
        };
        let started = Instant::now();
        let moved = executed_move_in(
            &engine.field,
            &theta,
            &requests,
            &engine.refinement,
            &bank,
            BANK_GRAIN,
            comparison,
            metric,
        )
        .expect("the move");
        report(
            &format!("{label} {name}: the incumbent"),
            &moved.before,
            &theta.transport(ring),
            started.elapsed().as_millis(),
        );
        print_orders("the incumbent", &moved.before);
        if let Some(w) = &moved.witness {
            println!(
                "    the witness: G_EE {}, G_Eρ {}, G_ρρ {}; g_E {}, g_ρ {}; step {:?} (24 bits)",
                at_bits(w.form.at(0, 0)),
                at_bits(w.form.at(0, 1)),
                at_bits(w.form.at(1, 1)),
                at_bits(&w.gradient[0]),
                at_bits(&w.gradient[1]),
                w.step().map(|v| (at_bits(&v[0]), at_bits(&v[1]))),
            );
        }
        if let Some(k) = &moved.kinetic {
            println!(
                "    the receiver's solve: {} readings, {} iterations, stop {:?}, residual energy {}, model change {} (24 bits)",
                k.readings,
                k.residuals.len(),
                k.stop,
                k.residuals.last().map_or_else(|| "none".to_string(), |r| at_bits(r).to_string()),
                at_bits(&k.predicted),
            );
            if let Some((own, supplied)) = &k.modulus_drive {
                println!(
                    "    the joined direction: Δρ {:?}, own {}, supplied {} (24 bits)",
                    k.modulus.as_ref().map(at_bits),
                    at_bits(own),
                    at_bits(supplied)
                );
            }
        }
        if let Some(held) = &moved.modulus_held {
            if let Some((own, supplied)) = &held.modulus_drive {
                println!(
                    "    the bound held an upward ask: Δρ {:?}, own {}, supplied {} (24 bits)",
                    held.modulus.as_ref().map(at_bits),
                    at_bits(own),
                    at_bits(supplied)
                );
            }
        }
        println!(
            "    γ_ρ {:?}, Δρ per unit of E's step {:?} (24 bits)",
            moved.modulus_slope.as_ref().map(at_bits),
            moved.modulus_unit.as_ref().map(at_bits)
        );
        println!("{}", move_line(0, &moved, started.elapsed().as_millis()));
        println!("{}", trial_line(&moved));
        if std::env::var("DECISION_DIFF").is_ok() {
            decision_diff(&moved.before, moved.trials.last().and_then(|t| t.after.as_ref()));
        }
        match &moved.adopted {
            Some((successor, _)) => {
                let own = moved.trials.last().and_then(|t| t.after.as_ref()).expect("the adopted trial's own release");
                report(
                    &format!("{label} {name}: the adopted successor's own release"),
                    own,
                    &successor.transport(ring),
                    started.elapsed().as_millis(),
                );
                print_orders("the successor", own);
                #[allow(clippy::disallowed_methods)]
                std::fs::write(format!("{out}/{label}-{name}.state"), write_state(successor, ring))
                    .expect("write the successor's state");
                println!("  {label}: {name} adopted; the later metrics are not attempted");
                break;
            }
            None => println!(
                "  {label} {name}: refused, {:?}; {} ms",
                moved.refusal,
                started.elapsed().as_millis()
            ),
        }
    }
    println!("executed move-once: {} ms; resident {}", clock.elapsed().as_millis(), resident());
}

/// [measured-diagnostic; agent-inferred, October 1; the
/// [margins record](../../records/2026-10-01_THE_DECISION_MARGINS_THROUGH_THE_ACCEPTED_MOVE.md)]
/// **An accepted move read decision by decision** (`executed margins <terrain> <seed> <count>
/// <before state> <after state>`, complete continuing states restored with no fallback):
/// `hnn::executed::move_margins` on the candidate arm. Per incumbent decision term: its site, target,
/// and at `before` and at `after` on the same fixed section, the lock face `ℓ`, its solved predicate,
/// the top class, the target's and the leading rival's growth enclosures (the ordering margin) and
/// the first-order bound on the exact storage move; then each request's released section before and
/// after against its targets. Every term is printed, none selected after the outcome.
/// [measured-diagnostic; October 2] **The own release decision by decision, the incumbent against
/// the smallest trial** (`DECISION_DIFF`): per request and per decision term, the section the term is
/// read at, the top class and the lock face `ℓ` (lower ends, `/4096` nats), and whether the term's
/// section or its top moved: a flipped decision upstream changes the section, a flip at the term
/// changes its top.
fn decision_diff(before: &BatchComparison, after: Option<&BatchComparison>) {
    let Some(after) = after else {
        println!("    decision diff: the smallest trial has no own release");
        return;
    };
    let low = |x: &holonics::ratio::algebraic::ExactInterval| (&x.lower * Rat::from_integer(4096.into())).floor();
    for (r, (b, a)) in before.requests.iter().zip(&after.requests).enumerate() {
        let sb = b.generation.as_ref().map(|g| format!("{:?}", g.release.emitted));
        let sa = a.generation.as_ref().map(|g| format!("{:?}", g.release.emitted));
        println!(
            "    request {r}: L {} -> {} (/4096); section {} -> {}",
            low(&b.value),
            low(&a.value),
            sb.unwrap_or_default(),
            sa.unwrap_or_default()
        );
        for tb in &b.terms {
            let ta = a.terms.iter().find(|t| t.site.station == tb.site.station);
            match ta {
                Some(ta) => {
                    let moved_section = ta.site.cells != tb.site.cells;
                    let moved_top = ta.comparison.top != tb.comparison.top;
                    println!(
                        "      station {}: target {}, top {} -> {}, ℓ {} -> {}{}{}",
                        tb.site.station,
                        tb.comparison.target,
                        tb.comparison.top,
                        ta.comparison.top,
                        low(&tb.value),
                        low(&ta.value),
                        if moved_section { ", section moved" } else { "" },
                        if moved_top { ", top flipped" } else { "" },
                    );
                }
                None => println!("      station {}: absent after", tb.site.station),
            }
        }
    }
}

pub(super) fn margins(terrain: &str, seed: u64, count: usize, before: &str, after: &str) {
    use holonics::hnn::executed::move_margins;
    let clock = Instant::now();
    let declared = order_declared();
    let engine = Engine::new(declared);
    let bank = bank_of(declared.period, &bank_strength());
    let pairs = terrain_pairs(terrain, &declared, seed, count);
    let requests = open_requests(&engine, &pairs);
    let targets: Vec<Vec<usize>> = pairs.iter().map(|(_, t)| t.clone()).collect();
    let comparison = Comparison::LOCK_DECISIONS;
    let (theta, successor) = (remounted(&engine.theta, before), remounted(&engine.theta, after));
    println!(
        "executed margins: {count} {terrain} requests at development seed {seed}, the candidate arm; from {before} to {after}; the bank p = {}, grain 2^(-{BANK_GRAIN})",
        bank_strength()
    );
    let read = move_margins(
        &engine.field,
        &theta,
        &successor,
        &requests,
        &engine.refinement,
        &bank,
        BANK_GRAIN,
        comparison,
    )
    .expect("the margins");
    let first: BTreeMap<(usize, usize), &Option<ExactInterval>> = read
        .sites
        .iter()
        .zip(&read.first_order)
        .map(|(site, bound)| ((site.request, site.station), bound))
        .collect();
    let growth = |g: &holonics::hnn::ring::Growth| format!("[{}, {}]", at_bits(&g.lower), at_bits(&g.upper));
    for (index, (request, mask)) in read.before.requests.iter().zip(&read.mask).enumerate() {
        for (b, a) in request.terms.iter().zip(mask) {
            let (sb, sa) = (&b.comparison, &a.comparison);
            println!(
                "    request {index} station {} (refinement {:?}, {} placed): target {}; before ℓ ∈ {} {:?} top {} target {} rival {}; after ℓ ∈ {} {:?} top {} target {} rival {}; first order {}",
                sb.station,
                b.site.context,
                b.site.cells.iter().filter(|c| c.is_some()).count(),
                sb.target,
                cell(&sb.lock, 1 << 16),
                sb.solved,
                sb.top,
                growth(&sb.target_growth),
                growth(&sb.rival_growth),
                cell(&sa.lock, 1 << 16),
                sa.solved,
                sa.top,
                growth(&sa.target_growth),
                growth(&sa.rival_growth),
                first
                    .get(&(index, sb.station))
                    .and_then(|b| b.as_ref())
                    .map_or_else(|| "none".to_string(), |b| cell(b, 1 << 16)),
            );
        }
    }
    let section = |batch: &BatchComparison, index: usize| {
        batch.requests[index]
            .generation
            .as_ref()
            .map_or_else(|| "not released".to_string(), |g| format!("{:?}, locks {:?}", g.release.classes, g.locks))
    };
    for (index, target) in targets.iter().enumerate() {
        println!(
            "    request {index}: target {target:?}; before {}; after {}",
            section(&read.before, index),
            section(&read.after, index)
        );
        // The release's order at its first refinement: every eligible station (its top flipped and
        // locked), its top, its gap and whether its top is its target; the stations it locked.
        for (what, batch) in [("before", &read.before), ("after", &read.after)] {
            if let Some(order) = batch.requests[index].orders.first() {
                let eligible: Vec<String> = order
                    .eligible
                    .iter()
                    .map(|(s, top, gap, right)| {
                        format!("{s}:{top}{} gap {}", if *right { "+" } else { "-" }, at_bits(gap))
                    })
                    .collect();
                println!(
                    "      {what} order at refinement {}: eligible [{}]; locked {:?}",
                    order.context,
                    eligible.join(", "),
                    order.locked
                );
            }
        }
    }
    for (what, batch) in [("before", &read.before), ("after", &read.after)] {
        let (solved, all) = solved_terms(batch);
        let (whole, right, released) = batch.sections(&targets);
        println!(
            "  {what}: L ∈ {} nats; solved {solved} of {all}; whole {whole} (released {released}, stations right {right}); {} ms",
            cell(&batch.value, 1 << 12),
            clock.elapsed().as_millis()
        );
    }
    println!("executed margins: {} ms; resident {}", clock.elapsed().as_millis(), resident());
}

/// [measured-diagnostic; agent-inferred, October 1; the
/// [ρ stiffness record](../../records/2026-10-01_THE_STIFFNESS_IN_RHO.md)]
/// **The witness's plane along the port's unit move and along the route** (`executed route-plane
/// <terrain> <seed> <count> <arm> <both|route|port> <toward> <label=state>…`, states restored
/// whole): at each state the
/// witness's form, its step `(α, β)` and `β` over the chord to `toward`'s `ρ`, on the plane of the
/// port's unit move `ΔE` (the move's own) and on the plane of the route `E_toward − E`
/// (`hnn::executed::witness_plane_along`). No move is made.
pub(super) fn route_plane(
    terrain: &str,
    seed: u64,
    count: usize,
    arm: &str,
    planes: &str,
    toward: &str,
    sources: &[String],
) {
    use holonics::hnn::executed::witness_plane_along;
    let clock = Instant::now();
    let declared = order_declared();
    let engine = Engine::new(declared);
    let bank = bank_of(declared.period, &bank_strength());
    let ring = engine.refinement.ring();
    let pairs = terrain_pairs(terrain, &declared, seed, count);
    let requests = open_requests(&engine, &pairs);
    let (comparison, partition) = arm_comparison(arm);
    assert!(!partition, "the plane is read on the open section");
    let goal = segment_source(&engine, ring, toward);
    println!(
        "executed route-plane: {count} {terrain} requests at development seed {seed}, the arm {arm}, toward {toward} (ρ {}); the bank p = {}, grain 2^(-{BANK_GRAIN})",
        goal.transport(ring),
        bank_strength()
    );
    for source in sources {
        let (label, spec) = source.split_once('=').expect("<label>=<state>");
        let theta = remounted(&engine.theta, spec);
        let chord = goal.transport(ring) - theta.transport(ring);
        let both = [("the port's unit move", None), ("the route", Some(&goal))];
        let chosen: Vec<_> = both
            .into_iter()
            .filter(|(_, along)| planes == "both" || (planes == "route") == along.is_some())
            .collect();
        for (plane, along) in chosen {
            let started = Instant::now();
            let reading = witness_plane_along(
                &engine.field,
                &theta,
                along,
                &requests,
                &engine.refinement,
                &bank,
                BANK_GRAIN,
                comparison,
            )
            .expect("the plane");
            let line = match &reading.witness {
                None => format!("no witness's form ({:?})", reading.refusal),
                Some(w) => {
                    let step = w.step();
                    format!(
                        "G_EE {}, G_Eρ {}, G_ρρ {}; g_E {}, g_ρ {}; step {:?}; β over the chord {}; decoupled β₀ over the chord {}",
                        at_bits(w.form.at(0, 0)),
                        at_bits(w.form.at(0, 1)),
                        at_bits(w.form.at(1, 1)),
                        at_bits(&w.gradient[0]),
                        at_bits(&w.gradient[1]),
                        step.as_ref().map(|v| (at_bits(&v[0]), at_bits(&v[1]))),
                        step.as_ref().map_or_else(|| "none".to_string(), |v| at_bits(&(&v[1] / &chord)).to_string()),
                        w.decoupled()[1].as_ref().map_or_else(|| "none".to_string(), |b| at_bits(&(b / &chord)).to_string()),
                    )
                }
            };
            println!(
                "  {label}, {plane}: ρ {}, chord {chord}; {} ∈ {} nats; {line}; {} ms",
                theta.transport(ring),
                symbol(&comparison),
                cell(&reading.before.value, 1 << 12),
                started.elapsed().as_millis()
            );
        }
    }
    println!("executed route-plane: {} ms; resident {}", clock.elapsed().as_millis(), resident());
}

/// [measured-diagnostic; agent-inferred, October 1; the
/// [witness's span record](../../records/2026-10-01_THE_WITNESSS_DIRECTION_IN_THE_SPAN_OF_THE_RETURNS.md)]
/// **The witness's direction in the span of the returns** (`executed span <terrain> <seed> <count>
/// <arm> <toward> <label=source>…`, sources as [`segment_source`]): read-only. At each source,
/// `hnn::executed::witness_span`: the number of returns, the witness's step's `E` move and `ρ` move,
/// and each `E` move's squared cosine with the route `E_toward − E` (the witness's and the port's
/// unit move), `ρ`'s move over the chord, and the Gauss–Newton model's change.
pub(super) fn span(terrain: &str, seed: u64, count: usize, arm: &str, toward: &str, sources: &[String]) {
    use holonics::hnn::executed::witness_span;
    use holonics::ratio::linear::inertia::inertia;
    let clock = Instant::now();
    let declared = order_declared();
    let engine = Engine::new(declared);
    let bank = bank_of(declared.period, &bank_strength());
    let ring = engine.refinement.ring();
    let pairs = terrain_pairs(terrain, &declared, seed, count);
    let requests = open_requests(&engine, &pairs);
    let targets: Vec<Vec<usize>> = pairs.iter().map(|(_, t)| t.clone()).collect();
    let (comparison, partition) = arm_comparison(arm);
    assert!(!partition, "the span is read on the open section");
    let goal = segment_source(&engine, ring, toward);
    println!(
        "executed span: {count} {terrain} requests at development seed {seed}, the arm {arm}, toward {toward}; the bank p = {}, grain 2^(-{BANK_GRAIN})",
        bank_strength()
    );
    for source in sources {
        let started = Instant::now();
        let (label, spec) = source.split_once('=').expect("<label>=<source>");
        let theta = segment_source(&engine, ring, spec);
        let e = theta.source_port(ring).expect("E").clone();
        let route = goal.source_port(ring).expect("E").subtract(&e).expect("one shape");
        let chord = goal.transport(ring) - theta.transport(ring);
        let reading = witness_span(
            &engine.field,
            &theta,
            &requests,
            &engine.refinement,
            &bank,
            BANK_GRAIN,
            comparison,
        )
        .expect("the span");
        let cosine = |m: &ExactRatMatrix| {
            let (p, n, r) = (frobenius(m, &route), frobenius(m, m), frobenius(&route, &route));
            if n.is_zero() || r.is_zero() {
                "none".to_string()
            } else {
                format!(
                    "{} {}",
                    if p.is_positive() { "+" } else { "-" },
                    at_bits(&(&p * &p / (&n * &r)))
                )
            }
        };
        let inertia_line = reading
            .witness
            .as_ref()
            .map(|w| format!("{:?}", inertia(&w.form)))
            .unwrap_or_else(|| "none".to_string());
        println!(
            "  {label}: ρ {}; {} ∈ {} nats; {} returns; the witness's form inertia {}; the port's unit move: squared cosine with the route {}; the witness's E move: {}; its ρ move over the chord {}; the model's change {}; {} ms",
            theta.transport(ring),
            symbol(&comparison),
            cell(&reading.before.value, 1 << 12),
            reading.returns,
            inertia_line,
            reading.unit_move.as_ref().map_or_else(|| "none".to_string(), cosine),
            reading.witness_move.as_ref().map_or_else(|| format!("none ({:?})", reading.refusal), cosine),
            reading.modulus_move.as_ref().map_or_else(|| "none".to_string(), |b| at_bits(&(b / &chord)).to_string()),
            reading.witness.as_ref().and_then(|w| w.predicted()).map_or_else(|| "none".to_string(), |p| at_bits(&p).to_string()),
            started.elapsed().as_millis()
        );
        // The span's step taken whole, by half and by a quarter (E carried onto the source port's
        // lattice, nearest; ρ floored onto it), each read by the arm's comparison.
        let (Some(moved), Some(rho_move)) = (&reading.witness_move, &reading.modulus_move) else {
            continue;
        };
        let lattice = engine
            .theta
            .lattice(holonics::hnn::constitution::Locus::SourcePort(ring))
            .expect("the source port's lattice")
            .unit();
        let half = Rat::new(BigInt::one(), BigInt::from(2));
        for fraction in [Rat::one(), half.clone(), Rat::new(BigInt::one(), BigInt::from(4))] {
            let started = Instant::now();
            let rows: Vec<Vec<Rat>> = e
                .to_rows()
                .iter()
                .zip(moved.to_rows())
                .map(|(a, d)| {
                    a.iter()
                        .zip(&d)
                        .map(|(x, y)| ((x + &(&fraction * y)) / &lattice + &half).floor() * &lattice)
                        .collect()
                })
                .collect();
            let modulus = ((theta.transport(ring) + &fraction * rho_move) / &lattice).floor() * &lattice;
            let modulus = modulus.max(lattice.clone()).min(Rat::one());
            let successor = engine
                .theta
                .clone()
                .with_ports(ring, None, Some(ExactRatMatrix::new(rows).expect("E")), None)
                .expect("the successor's E")
                .with_transport(ring, modulus.clone())
                .expect("a passive modulus on the lattice");
            let batch = compare(
                &engine.field,
                &successor,
                &requests,
                &engine.refinement,
                &bank,
                BANK_GRAIN,
                comparison,
            )
            .expect("the successor's reading");
            let (solved, all) = solved_terms(&batch);
            let (whole, right, released) = batch.sections(&targets);
            println!(
                "  {label} span step × {fraction}: ρ {modulus}; {} ∈ {} nats; solved {solved} of {all}; whole {whole} (released {released}, stations right {right}); {} ms",
                symbol(&comparison),
                cell(&batch.value, 1 << 12),
                started.elapsed().as_millis()
            );
        }
    }
    println!("executed span: {} ms; resident {}", clock.elapsed().as_millis(), resident());
}

/// [measured-diagnostic; agent-inferred, October 1; the
/// [agreement record](../../records/2026-10-01_THE_COMPARISONS_AGREEMENT_WITH_THE_DECISIONS.md)]
/// **Each constitution under several declared comparisons** (`executed agreement <terrain> <seed>
/// <count> <arm,arm,…> <label=source>…`, sources as [`segment_source`]): read-only. One line per
/// constitution and arm: the composition's value, solved terms, whole sections and stations right
/// (the release is the same under every arm; only the terms read differ).
pub(super) fn agreement(terrain: &str, seed: u64, count: usize, arms: &str, sources: &[String]) {
    let clock = Instant::now();
    let declared = order_declared();
    let engine = Engine::new(declared);
    let bank = bank_of(declared.period, &bank_strength());
    let ring = engine.refinement.ring();
    let pairs = terrain_pairs(terrain, &declared, seed, count);
    let requests = open_requests(&engine, &pairs);
    let targets: Vec<Vec<usize>> = pairs.iter().map(|(_, t)| t.clone()).collect();
    println!(
        "executed agreement: {count} {terrain} requests at development seed {seed}, the arms {arms}; the bank p = {}, grain 2^(-{BANK_GRAIN})",
        bank_strength()
    );
    for source in sources {
        let (label, spec) = source.split_once('=').expect("<label>=<source>");
        let theta = segment_source(&engine, ring, spec);
        for arm in arms.split(',') {
            let started = Instant::now();
            let (comparison, partition) = arm_comparison(arm);
            assert!(!partition, "the open section");
            let batch = compare(
                &engine.field,
                &theta,
                &requests,
                &engine.refinement,
                &bank,
                BANK_GRAIN,
                comparison,
            )
            .expect("the reading");
            let (solved, all) = solved_terms(&batch);
            let (whole, right, released) = batch.sections(&targets);
            println!(
                "  {label} {arm}: ρ {}; value ∈ {} nats; solved {solved} of {all}; whole {whole} (released {released}, stations right {right}); {} ms",
                theta.transport(ring),
                cell(&batch.value, 1 << 12),
                started.elapsed().as_millis()
            );
        }
    }
    println!("executed agreement: {} ms; resident {}", clock.elapsed().as_millis(), resident());
}

/// Every request's order term ([`holonics::hnn::executed::OrderTerm`]), where read: its sheets
/// (station, top, gap; the right one first), `ℓ_o` and whether it is solved.
fn print_orders(what: &str, batch: &BatchComparison) {
    for (index, request) in batch.requests.iter().enumerate() {
        for order in &request.order_terms {
            let sheets: Vec<String> = order
                .sheets
                .iter()
                .map(|s| format!("{}:{} gap {}", s.station, s.top, at_bits(&s.gap)))
                .collect();
            println!(
                "      {what} request {index} order at refinement {}: [{}]; ℓ_o ∈ {} nats, {:?}",
                order.context,
                sheets.join(", "),
                cell(&order.value, 1 << 16),
                order.solved
            );
        }
    }
}

/// A rational read at 24 significant bits toward zero (`m/2^k`, exact as printed).
fn at_bits(x: &Rat) -> Rat {
    use holonics::holon::deposition::significant;
    if x.is_zero() {
        x.clone()
    } else if x.is_negative() {
        -significant(&-x.clone(), 24, false)
    } else {
        significant(x, 24, false)
    }
}

/// [measured-diagnostic; agent-inferred, October 1; the
/// [witness's metric record](../../records/2026-10-01_THE_MOVES_METRIC_IS_ITS_WITNESSS_THE_LOCKS_FISHER_FORM_ON_THE_MOVES_PLANE.md)]
/// **The move's plane read by its witness** (`executed witness-plane <terrain> <seed> <count> <arm>
/// <toward> <out> <label=source>…`, sources as [`segment_source`]): read-only. At each source, the
/// committed move's unit step `ΔE` and its coordinate control `Δρ_c = −γ_ρ/G_ρ` as `executed_move`
/// forms them, and the witness's form on the plane of `ΔE` and `ρ`
/// (`hnn::executed::witness_plane`): its step `(α, β)`, the steps with the cross term dropped, and
/// the second-order model's change, beside `toward`'s `ρ` less the source's. Then two successors
/// share the witness's `E + αΔE`, carried onto the source port's lattice entry by entry (nearest),
/// as the machine's own move carries it (off the lattice, `α`'s bits multiply every storage's and a
/// read passed its bound: the record §3): the witness's `ρ + β` and the control's `ρ + αΔρ_c`
/// (each floored onto the lattice and held in `[unit, 1]`), each read by the arm's
/// comparison and written to `<out>/<label>-{witness,control}.txt`. No move is made.
#[allow(clippy::too_many_arguments)]
pub(super) fn witness_plane(
    terrain: &str,
    seed: u64,
    count: usize,
    arm: &str,
    toward: &str,
    out: &str,
    sources: &[String],
) {
    let clock = Instant::now();
    let declared = order_declared();
    let engine = Engine::new(declared);
    let bank = bank_of(declared.period, &bank_strength());
    let ring = engine.refinement.ring();
    let pairs = terrain_pairs(terrain, &declared, seed, count);
    let requests = open_requests(&engine, &pairs);
    let targets: Vec<Vec<usize>> = pairs.iter().map(|(_, t)| t.clone()).collect();
    let (comparison, partition) = arm_comparison(arm);
    assert!(!partition, "the plane is read on the open section");
    println!(
        "executed witness-plane: {count} {terrain} requests at development seed {seed}, the arm {arm}, toward {toward}; the bank p = {}, grain 2^(-{BANK_GRAIN})",
        bank_strength()
    );
    let goal = segment_source(&engine, ring, toward).transport(ring);
    let lattice = engine
        .theta
        .lattice(holonics::hnn::constitution::Locus::SourcePort(ring))
        .expect("the source port's lattice")
        .unit();
    let half = Rat::new(BigInt::one(), BigInt::from(2));
    let on_lattice = |x: Rat| {
        ((&x / &lattice).floor() * &lattice)
            .max(lattice.clone())
            .min(Rat::one())
    };
    let first_locks = |batch: &BatchComparison| -> String {
        batch
            .requests
            .iter()
            .zip(&targets)
            .filter_map(|(r, t)| {
                r.generation.as_ref().and_then(|g| {
                    g.decisions
                        .first()
                        .map(|(s, c, ..)| format!("{s}{}", if *c == t[*s] { "+" } else { "-" }))
                })
            })
            .collect::<Vec<_>>()
            .join(" ")
    };
    for source in sources {
        let started = Instant::now();
        let (label, spec) = source.split_once('=').expect("<label>=<source>");
        let theta = segment_source(&engine, ring, spec);
        let rho = theta.transport(ring);
        let reading = holonics::hnn::executed::witness_plane(
            &engine.field,
            &theta,
            &requests,
            &engine.refinement,
            &bank,
            BANK_GRAIN,
            comparison,
        )
        .expect("the plane");
        let (solved, all) = solved_terms(&reading.before);
        let (whole, right, released) = reading.before.sections(&targets);
        println!(
            "  {label}: ρ {rho}; {} ∈ {} nats; solved {solved} of {all}; whole {whole} (released {released}, stations right {right}); toward's ρ less this ρ: {}; {} ms",
            symbol(&comparison),
            cell(&reading.before.value, 1 << 12),
            &goal - &rho,
            started.elapsed().as_millis()
        );
        let (Some(unit), Some(witness), Some(control)) =
            (&reading.unit_move, &reading.witness, &reading.modulus_unit)
        else {
            println!(
                "    refused before the plane, {:?}; {} ms",
                reading.refusal,
                started.elapsed().as_millis()
            );
            continue;
        };
        let gamma = reading.modulus_slope.clone().expect("γ_ρ");
        let curvature = reading.modulus_curvature.clone().expect("G_ρ");
        let (ee, er, rr) = (witness.form.at(0, 0), witness.form.at(0, 1), witness.form.at(1, 1));
        let (ge, gr) = (&witness.gradient[0], &witness.gradient[1]);
        let decoupled = witness.decoupled();
        println!(
            "    the coordinate control: γ_ρ {}, G_ρ {}, Δρ_c {} (24 bits); ΔE's largest entry {}",
            at_bits(&gamma),
            at_bits(&curvature),
            at_bits(control),
            largest_of(unit)
        );
        println!(
            "    the witness ({} lock terms): G_EE {}, G_Eρ {}, G_ρρ {}, det {}; g_E {}, g_ρ {} (24 bits); decoupled α₀ {:?}, β₀ {:?}",
            reading.terms,
            at_bits(ee),
            at_bits(er),
            at_bits(rr),
            at_bits(&witness.determinant()),
            at_bits(ge),
            at_bits(gr),
            decoupled[0].as_ref().map(at_bits),
            decoupled[1].as_ref().map(at_bits),
        );
        let Some([alpha, beta]) = witness.step().and_then(|v| <[Rat; 2]>::try_from(v).ok()) else {
            println!("    the plane is degenerate to the witness; {} ms", started.elapsed().as_millis());
            continue;
        };
        let route = &goal - &rho;
        let ratio = |x: &Rat| {
            if route.is_zero() {
                "none".to_string()
            } else {
                at_bits(&(x / &route)).to_string()
            }
        };
        let control_move = &alpha * control;
        println!(
            "    the witness's step: α {}, β {} (24 bits); the model's change {}; β over toward's ρ change {}; the control's αΔρ_c over it {}",
            at_bits(&alpha),
            at_bits(&beta),
            at_bits(&witness.predicted().expect("a step")),
            ratio(&beta),
            ratio(&control_move),
        );
        let e = theta.source_port(ring).expect("E").clone();
        let moved: Vec<Rat> = e
            .entries()
            .iter()
            .zip(unit.entries())
            .map(|(x, d)| ((x + &(&alpha * d)) / &lattice + &half).floor() * &lattice)
            .collect();
        let rows: Vec<Vec<Rat>> = moved.chunks(e.columns()).map(<[Rat]>::to_vec).collect();
        let largest = moved.iter().map(|x| x.abs()).max().unwrap_or_else(Rat::zero);
        for (kind, modulus) in [
            ("witness", on_lattice(&rho + &beta)),
            ("control", on_lattice(&rho + &control_move)),
        ] {
            let started = Instant::now();
            let successor = engine
                .theta
                .clone()
                .with_ports(ring, None, Some(ExactRatMatrix::new(rows.clone()).expect("E")), None)
                .expect("the successor's E")
                .with_transport(ring, modulus.clone())
                .expect("a passive modulus on the lattice");
            let mut text = format!("E {} {}\n", rows.len(), e.columns());
            for row in &rows {
                text.push_str(&row.iter().map(ToString::to_string).collect::<Vec<_>>().join(" "));
                text.push('\n');
            }
            text.push_str(&format!("rho {modulus}\n"));
            #[allow(clippy::disallowed_methods)]
            std::fs::write(format!("{out}/{label}-{kind}.txt"), text).expect("write the successor");
            let batch = compare(
                &engine.field,
                &successor,
                &requests,
                &engine.refinement,
                &bank,
                BANK_GRAIN,
                comparison,
            )
            .expect("the successor's reading");
            let (solved, all) = solved_terms(&batch);
            let (whole, right, released) = batch.sections(&targets);
            println!(
                "  {label} {kind}: ρ {modulus}; E's largest entry {}; {} ∈ {} nats; solved {solved} of {all}; whole {whole} (released {released}, stations right {right}); first locks {}; {} ms",
                at_bits(&largest),
                symbol(&comparison),
                cell(&batch.value, 1 << 12),
                first_locks(&batch),
                started.elapsed().as_millis()
            );
        }
    }
    println!("executed witness-plane: {} ms; resident {}", clock.elapsed().as_millis(), resident());
}

/// The largest entry's magnitude of a matrix.
fn largest_of(m: &ExactRatMatrix) -> Rat {
    m.entries().iter().map(|x| x.abs()).max().unwrap_or_else(Rat::zero)
}

/// [definition; agent-inferred, October 1; the
/// [pin](../../records/2026-10-01_THE_MODULUS_SLOPE_PINNED_BEFORE_ITS_RUN.md)] **The modulus's slope
/// at constitutions** (`executed rho-slopes <terrain> <seed> <count> <arm> <label=source>…`, the arm
/// as [`arm_comparison`], sources as [`segment_source`]): read-only. Per constitution, the arm's
/// comparison on the declared requests, the proposal formed as `executed_move` forms it, and its
/// modulus part (`hnn::executed::modulus_slopes`): `γ_ρ` (the composition's first-order slope in
/// `ρ`) with its target and rival parts, the storage curvature `G_ρ` and the least-squares unit
/// move `−γ_ρ/G_ρ`, beside the comparison's value and the release's counts. No move is made.
pub(super) fn rho_slopes(terrain: &str, seed: u64, count: usize, arm: &str, sources: &[String]) {
    use holonics::hnn::executed::modulus_slopes;
    let clock = Instant::now();
    let declared = order_declared();
    let engine = Engine::new(declared);
    let bank = bank_of(declared.period, &bank_strength());
    let ring = engine.refinement.ring();
    let pairs = terrain_pairs(terrain, &declared, seed, count);
    let requests = open_requests(&engine, &pairs);
    let targets: Vec<Vec<usize>> = pairs.iter().map(|(_, t)| t.clone()).collect();
    let (comparison, partition) = arm_comparison(arm);
    assert!(!partition, "the modulus's slope is read on the open section");
    println!(
        "executed rho-slopes: {count} {terrain} requests at development seed {seed}, the arm {arm}; the bank p = {}, grain 2^(-{BANK_GRAIN})",
        bank_strength()
    );
    let point = |x: &Rat, grain: i64| cell(&ExactInterval::point(x.clone()), grain);
    for source in sources {
        let started = Instant::now();
        let (label, spec) = source.split_once('=').expect("<label>=<source>");
        let theta = segment_source(&engine, ring, spec);
        let (batch, split) = modulus_slopes(
            &engine.field,
            &theta,
            &requests,
            &engine.refinement,
            &bank,
            BANK_GRAIN,
            comparison,
        )
        .expect("the modulus's slope");
        let slope = &split.led_threshold + &split.led_class;
        let unit = if split.curvature.is_zero() {
            "none (G_ρ = 0)".to_string()
        } else {
            point(&(-(&slope / &split.curvature)), 1 << 21)
        };
        let (solved, all) = solved_terms(&batch);
        let (whole, right, released) = batch.sections(&targets);
        println!(
            "  {label}: ρ {}; {} ∈ {} nats; solved {solved} of {all}; whole {whole} of {count} (released {released}, stations right {right}); γ_ρ ∈ {} (target part {}, rival part {}); G_ρ ∈ {}; the least-squares unit move −γ_ρ/G_ρ ∈ {unit}; terms led by the threshold {}, by a class {}; {} ms",
            theta.transport(ring),
            symbol(&comparison),
            cell(&batch.value, 1 << 12),
            point(&slope, 1 << 12),
            point(&split.target, 1 << 12),
            point(&split.rival, 1 << 12),
            point(&split.curvature, 1 << 12),
            split.threshold_led,
            split.class_led,
            started.elapsed().as_millis()
        );
    }
    println!("executed rho-slopes: {} ms; resident {}", clock.elapsed().as_millis(), resident());
}

/// [definition; agent-inferred, October 1; the
/// [pin](../../records/2026-10-01_THE_SEGMENT_PROBE_PINNED_BEFORE_ITS_RUN.md)] **The segment probe**
/// (`executed segment <terrain> <seed> <count> [arm=<arm>] <label=source>…`, sources as
/// [`segment_source`]):
/// read-only. Each constitution is read on the declared requests by gate A's comparison (the lock
/// face at the decisions, `Comparison::LOCK_DECISIONS`, as `executed witness` reads its
/// constitutions) and reported in the witness's line, beside the stations right by station, the
/// class and threshold predicates at the decision terms, the first lock's station and whether it is
/// right, and every request's release and terms whole. No move and no update; nothing is written but
/// the listing.
pub(super) fn segment(terrain: &str, seed: u64, count: usize, arms: &[String]) {
    let clock = Instant::now();
    let declared = order_declared();
    let engine = Engine::new(declared);
    let bank = bank_of(declared.period, &bank_strength());
    let ring = engine.refinement.ring();
    let pairs = terrain_pairs(terrain, &declared, seed, count);
    let requests = open_requests(&engine, &pairs);
    let targets: Vec<Vec<usize>> = pairs.iter().map(|(_, t)| t.clone()).collect();
    // A first argument `arm=<arm>` declares the comparison (as [`arm_comparison`]); gate A's
    // otherwise.
    let (comparison, arms) = match arms.first().and_then(|a| a.strip_prefix("arm=")) {
        Some(arm) => (arm_comparison(arm).0, &arms[1..]),
        None => (Comparison::LOCK_DECISIONS, arms),
    };
    println!(
        "executed segment: {count} {terrain} requests at development seed {seed}, each constitution read by {:?}; the bank p = {}, grain 2^(-{BANK_GRAIN})",
        comparison,
        bank_strength()
    );
    for arm in arms {
        let started = Instant::now();
        let (label, spec) = arm.split_once('=').expect("<label>=<source>");
        let theta = segment_source(&engine, ring, spec);
        let batch = compare(
            &engine.field,
            &theta,
            &requests,
            &engine.refinement,
            &bank,
            BANK_GRAIN,
            comparison,
        )
        .expect("the segment's reading");
        let (solved, all) = solved_terms(&batch);
        let (whole, right, released) = batch.sections(&targets);
        let largest = theta
            .source_port(ring)
            .expect("E")
            .entries()
            .iter()
            .map(|x| x.abs())
            .max()
            .unwrap_or_else(Rat::zero);
        let mut by_station = vec![0usize; declared.stations];
        let (mut first, mut first_right) = (BTreeMap::<usize, usize>::new(), 0usize);
        for (request, target) in batch.requests.iter().zip(&targets) {
            if let Some(generation) = &request.generation {
                if generation.release.released() {
                    for (station, (a, b)) in generation.release.classes.iter().zip(target).enumerate() {
                        by_station[station] += usize::from(a == b);
                    }
                }
                if let Some((station, class, ..)) = generation.decisions.first() {
                    *first.entry(*station).or_default() += 1;
                    first_right += usize::from(*class == target[*station]);
                }
            }
        }
        let terms = batch.requests.iter().flat_map(|r| &r.terms);
        let (mut class, mut threshold) = (0usize, 0usize);
        for term in terms {
            class += usize::from(term.comparison.class == Predicate::Holds);
            threshold += usize::from(term.comparison.threshold == Predicate::Holds);
        }
        println!(
            "  {label} ({spec}): solved {solved} of {all} decision terms; class holds {class}, threshold holds {threshold}; whole sections {whole} of {count} (released {released}, stations right {right} by station {by_station:?}); first lock's station {first:?}, right {first_right}; L ∈ {} nats, X ∈ {} nats; E's largest entry {largest}, ρ {}; the terms {:?}; {} ms",
            cell(&batch.value, 1 << 12),
            cell(&batch.excess, 1 << 12),
            theta.transport(ring),
            batch.counts(declared.stations),
            started.elapsed().as_millis()
        );
        print_terms(label, &batch, &targets);
    }
    println!("executed segment: {} ms; resident {}", clock.elapsed().as_millis(), resident());
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
    // Stage 1's comparison: 1a's hinge at every refinement.
    let comparison = Comparison::HINGE_EVERY;
    let moved: ExecutedMove = executed_move(
        &engine.field,
        &engine.theta,
        &requests,
        &engine.refinement,
        &bank,
        BANK_GRAIN,
        comparison,
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
    let masked = moved
        .trials
        .last()
        .and_then(|t| t.value.clone())
        .expect("the adopted trial's fixed-mask value");
    println!(
        "  the certificate on the fixed mask: F(E′)⁺ < F(E)⁻, {} < {}: {}",
        cell(&ExactInterval::point(masked.upper.clone()), 1 << 16),
        cell(&ExactInterval::point(moved.before.value.lower.clone()), 1 << 16),
        masked.upper < moved.before.value.lower
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
        comparison,
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
        comparison,
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

/// [definition; the pin §5; step 1b's pin §8 I5] **One stratum of D2's readings**: the station
/// comparisons of one decision kind and request kind, their class gaps and threshold margins (sign
/// counts, sums, extremes; exact enclosures), the gaps' magnitudes summed, the stations in the lock
/// face's solved level (the rational test) and the target's share `θ_t` summed, and their terms'
/// derivatives along the carried move (exactly zero, below the term's grain, descending, rising,
/// straddling; their sum).
#[derive(Default)]
struct Stratum {
    count: usize,
    solved: usize,
    share_sum: (Rat, Rat),
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
    fn station(
        &mut self,
        gap: &ExactInterval,
        margin: &ExactInterval,
        s: &holonics::hnn::executed::StationComparison,
    ) {
        self.count += 1;
        self.solved += usize::from(s.solved == Predicate::Holds);
        self.share_sum.0 += &s.share.lower;
        self.share_sum.1 += &s.share.upper;
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
            "stations {}, in the lock face's solved level {}, mean θ_t ∈ {}; class gap (+, −, straddling) {:?}, Σ ∈ {}, least {}, most {}, Σ|γ| ∈ {}, mean |γ| ∈ {}; threshold margin (+, −, straddling) {:?}, Σ ∈ {}, least {}, most {}; terms of the composition's support {}, their derivative along the carried move (exactly zero, below its term's grain, descending, rising, straddling) {:?}, Σ ∈ {} nats",
            self.count,
            self.solved,
            mean(&self.share_sum),
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

/// [definition; the pin §5; step 1b's pin §9] **D2, the comparison's operating point**, printed
/// for one move: every station comparison of the batch at `θ` (every refinement, the open section
/// apart) and the declared reading's terms, their class gap `ln a_t − ln a_r` and threshold margin
/// `ln a_t` as exact enclosures, the lock face's solved level and `θ_t`, stratified by decision
/// (right; wrong and eligible, a confident wrong decision the release would lock; wrong and not
/// eligible, or read at a section the release did not execute) and by request (constant or not),
/// with each term of the composition's support's derivative along the carried move (`terms`,
/// aligned with the move's `sites`).
fn print_d2(
    index: usize,
    moved: &ExecutedMove,
    constant: &[bool],
    terms: Option<&Vec<Option<ExactInterval>>>,
) {
    use holonics::hnn::executed::{RequestComparison, StationComparison};
    let kinds = ["right", "wrong, eligible (confident)", "wrong, not eligible"];
    let scopes = ["every refinement", "the open section", "the declared reading's terms"];
    // strata[scope][decision][constant]
    let mut strata: Vec<Vec<Vec<Stratum>>> = (0..3)
        .map(|_| (0..3).map(|_| (0..2).map(|_| Stratum::default()).collect()).collect())
        .collect();
    let decision = |request: &RequestComparison, s: &StationComparison| {
        let eligible = s.context.is_some_and(|k| {
            request
                .orders
                .iter()
                .find(|o| o.context == k)
                .is_some_and(|o| o.eligible.iter().any(|(station, _, _, _)| *station == s.station))
        });
        if s.top == s.target {
            0
        } else if eligible {
            1
        } else {
            2
        }
    };
    let read = |s: &StationComparison| {
        let t = ln_growth(&s.target_growth);
        let x = ln_growth(&s.rival_growth);
        (
            ExactInterval {
                lower: &t.lower - &x.upper,
                upper: &t.upper - &x.lower,
            },
            t,
        )
    };
    for (r, request) in moved.before.requests.iter().enumerate() {
        let c = usize::from(constant[r]);
        for s in &request.stations {
            let (gap, margin) = read(s);
            let d = decision(request, s);
            strata[0][d][c].station(&gap, &margin, s);
            if s.context == Some(0) {
                strata[1][d][c].station(&gap, &margin, s);
            }
        }
        for term in &request.terms {
            let (gap, margin) = read(&term.comparison);
            strata[2][decision(request, &term.comparison)][c].station(
                &gap,
                &margin,
                &term.comparison,
            );
        }
    }
    if let Some(terms) = terms {
        for (site, bound) in moved.sites.iter().zip(terms) {
            let Some(d) = bound else { continue };
            let request = &moved.before.requests[site.request];
            let Some(term) = request.terms.iter().find(|t| &t.site == site) else {
                continue;
            };
            let grain = &term.value.upper - &term.value.lower;
            let c = usize::from(constant[site.request]);
            let k = decision(request, &term.comparison);
            strata[2][k][c].derivative(d, &grain);
            if site.context.is_some() {
                strata[0][k][c].derivative(d, &grain);
            }
            if site.context == Some(0) {
                strata[1][k][c].derivative(d, &grain);
            }
        }
    }
    for (scope_index, scope) in scopes.iter().enumerate() {
        for (decision, kind) in kinds.iter().enumerate() {
            for (c, request) in ["nonconstant", "constant"].iter().enumerate() {
                let stratum = &strata[scope_index][decision][c];
                if stratum.count == 0 {
                    continue;
                }
                println!("    D2 move {index}, {scope}, {kind}, {request} requests: {}", stratum.line());
            }
        }
    }
}

/// [definition; step 1b's pin §8 I7] **The relation that needs no request**, per move at the
/// epoch's open section: the target's rank among the four symbols (the termination left out, 0 the
/// top) and the termination's rank among the five, as histograms over the stations.
fn print_ranks(index: usize, batch: &BatchComparison, alphabet: usize) {
    let mut symbols = vec![0usize; alphabet];
    let mut termination = vec![0usize; alphabet + 1];
    for request in &batch.requests {
        for s in request.stations.iter().filter(|s| s.context == Some(0)) {
            if let Some(rank) = s.symbol_rank {
                symbols[rank] += 1;
            }
            termination[s.termination_rank.min(alphabet)] += 1;
        }
    }
    println!(
        "    I7 move {index}: at the open section, the target's rank among the four symbols (0 the top) {:?}; the termination's rank among the five {:?}",
        &symbols[..alphabet - 1],
        &termination[..alphabet]
    );
}

/// Each station's decision in a release: `Some(right)` where it locked, `None` where it was held.
fn decisions_of(batch: &BatchComparison, targets: &[Vec<usize>]) -> Vec<Vec<Option<bool>>> {
    batch
        .requests
        .iter()
        .zip(targets)
        .map(|(request, target)| {
            let mut out = vec![None; target.len()];
            if let Some(generation) = &request.generation {
                for (station, class, ..) in &generation.decisions {
                    out[*station] = Some(*class == target[*station]);
                }
            }
            out
        })
        .collect()
}

/// [definition; the pin §5; step 1b's pin §9, §13.1] **D1, the step's descent**, printed for one
/// move: the composition `C` at `θ`, its grain and its excess `X` over the solved level, the terms'
/// counts, the unresolved members and the persistence reads; the joint unit slope, the port's part
/// alone, the excess's piecewise derivative, the modulus's share and the ladder's start with the
/// bound that set it; every trial with its readings; at the carried move (the adopted trial, else the
/// last trial whose first order was read) the step's norm, the lattice, passive and entry bounds, the
/// predicted descents (the certificate and the leading contributions) against the measured on the
/// fixed mask, the successor's own release's composition and the context change (own less mask),
/// the decisions moved at the open section and at the release's locks (I4), the successor's terms'
/// counts, and the ideal listener's bits on the batch.
fn print_d1(
    index: usize,
    moved: &ExecutedMove,
    theta: &Constitution,
    ring: usize,
    targets: &[Vec<usize>],
    information: &str,
) {
    use holonics::hnn::constitution::Locus;
    let c = symbol(&moved.comparison);
    let before = &moved.before.value;
    let grain = &before.upper - &before.lower;
    let two = Rat::from_integer(BigInt::from(2));
    let point = |x: &Rat, g: i64| cell(&ExactInterval::point(x.clone()), g);
    let negated = |x: &ExactInterval| ExactInterval {
        lower: -x.upper.clone(),
        upper: -x.lower.clone(),
    };
    let stations = targets.first().map_or(0, Vec::len);
    println!(
        "    D1 move {index}: {c}(θ) ∈ {}, its grain (enclosure width) ∈ {} nats; the excess X(θ) ∈ {} nats; the terms {:?}; unresolved: {} leading members {:?}, {} terms reading an unresolved active member; persistence {:?}",
        cell(before, 1 << 12),
        point(&grain, 1 << 16),
        cell(&moved.before.excess, 1 << 12),
        moved.before.counts(stations),
        moved.unresolved.len(),
        moved.unresolved,
        moved.unresolved_branches,
        moved.persistence
    );
    let (Some(slope), Some(unit), Some(largest)) =
        (&moved.slope, &moved.modulus_unit, &moved.unit_largest)
    else {
        println!(
            "    D1 move {index}: no descent proposed: {:?} (the joint unit slope {}); zero prediction",
            moved.refusal,
            moved.slope.as_ref().map_or_else(|| "not read".to_string(), |s| cell(s, 1 << 12))
        );
        println!("    D1 move {index}: the ideal listener on this batch: {information}");
        return;
    };
    let share = moved
        .modulus_slope
        .as_ref()
        .map_or_else(Rat::zero, |gamma| gamma * unit);
    println!(
        "    D1 move {index}: the joint unit slope ∈ {} (the port's alone {}, the modulus's leading share γ_ρΔρ {}), the excess's piecewise derivative s_X ∈ {}; the ladder's start {} ({:?}; the entry scale ½/u {}, u = {largest})",
        cell(slope, 1 << 12),
        moved.port_slope.as_ref().map_or_else(|| "not read".to_string(), |s| cell(s, 1 << 12)),
        point(&share, 1 << 12),
        moved.excess_slope.as_ref().map_or_else(|| "not read".to_string(), |s| cell(s, 1 << 12)),
        moved.start.as_ref().map_or_else(|| "none".to_string(), |(s, _)| s.to_string()),
        moved.start.as_ref().map(|(_, kind)| *kind),
        point(&(Rat::new(BigInt::from(1), BigInt::from(2)) / largest), 1 << 16)
    );
    let trials: Vec<String> = moved
        .trials
        .iter()
        .map(|t| {
            format!(
                "η {} {} (readings {})",
                t.step,
                match &t.refusal {
                    None => "adopted".to_string(),
                    Some(holonics::hnn::executed::TrialRefusal::NotBelow(v)) =>
                        format!("refused NotBelow({c}_mask ∈ {})", cell(v, 1 << 12)),
                    Some(holonics::hnn::executed::TrialRefusal::OwnNotBelow(v)) =>
                        format!("refused OwnNotBelow({c}_own ∈ {})", cell(v, 1 << 12)),
                    Some(holonics::hnn::executed::TrialRefusal::FirstOrder(v)) =>
                        format!("refused FirstOrder({})", cell(v, 1 << 12)),
                    Some(other) => format!("refused {other:?}"),
                },
                t.readings
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
        "    D1 move {index}: predicted descent, the certificate −Σ bound ∈ {} (exact enclosure; approximate as a prediction), the leading contributions −Σ c⟨ĝ, Δz⟩ ∈ {}; measured on the fixed mask {c}(θ) − {c}_mask(θ+δ) ∈ {} (exact); the prediction {kind}; the leading contributions' sign and the measured's: {agree}; the successor's own release {c}_own(θ+δ) ∈ {}, the context change {c}_own − {c}_mask ∈ {} (the own release's composition is a declared score: its change is never decision progress)",
        cell(&certificate, 1 << 12),
        leading.as_ref().map_or_else(|| "not read".to_string(), |l| cell(l, 1 << 12)),
        measured.as_ref().map_or_else(|| "not read".to_string(), |m| cell(m, 1 << 12)),
        trial.after.as_ref().map_or_else(|| "not read".to_string(), |a| cell(&a.value, 1 << 12)),
        trial.change.as_ref().map_or_else(|| "not read".to_string(), |d| cell(d, 1 << 12))
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
                    .filter(|s| s.context == Some(0))
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
        // I4 at the release's locks: [wrong→right, right→wrong, held→right, held→wrong,
        // right→held, wrong→held].
        let mut locks = [0usize; 6];
        for (a, b) in decisions_of(&moved.before, targets)
            .iter()
            .zip(&decisions_of(after, targets))
        {
            for (x, y) in a.iter().zip(b) {
                let kind = match (x, y) {
                    (Some(false), Some(true)) => 0,
                    (Some(true), Some(false)) => 1,
                    (None, Some(true)) => 2,
                    (None, Some(false)) => 3,
                    (Some(true), None) => 4,
                    (Some(false), None) => 5,
                    _ => continue,
                };
                locks[kind] += 1;
            }
        }
        let (whole, right, released) = after.sections(targets);
        println!(
            "    D1 move {index}: the successor's trajectory changed in {changed} of {} requests; at the open section, wrong→right {}, right→wrong {}, wrong→another wrong {}, right kept {}, wrong kept {}; at the release's locks (I4), wrong→right {}, right→wrong {}, held→right {}, held→wrong {}, right→held {}, wrong→held {}; the successor's batch: released {released}, whole {whole}, stations right {right}; its terms {:?}",
            moved.before.requests.len(),
            moves[0],
            moves[1],
            moves[2],
            moves[3],
            moves[4],
            locks[0],
            locks[1],
            locks[2],
            locks[3],
            locks[4],
            locks[5],
            after.counts(stations)
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

/// [measured-diagnostic; agent-inferred, October 2; the
/// [representation record](../../records/2026-10-02_THE_REPRESENTATION_THE_REFITS_E_MAKES_RHO_A_MONOTONE_PATH_TO_THE_DECISIONS.md)]
/// **The receiver's minimum-energy move read against a declared `E` leg** (`executed kinetic
/// <terrain> <seed> <count> <arm> <toward> <label=source>…`): `hnn::executed::kinetic_reading` at
/// each source, toward the `E` of `toward` at the source's own `ρ`. Prints the returns, the reading
/// coordinates, the normal law's unit move's signed squared cosine with the leg, then the solve's
/// iterates at `k = 1, 2, 4, …` and the last: the signed squared cosine and the residual energy, the
/// stop, the model change and `v`'s largest entry. Nothing is moved.
pub(super) fn kinetic(terrain: &str, seed: u64, count: usize, arm: &str, toward: &str, sources: &[String]) {
    use holonics::hnn::executed::kinetic_reading;
    let clock = Instant::now();
    let declared = order_declared();
    let engine = Engine::new(declared);
    let bank = bank_of(declared.period, &bank_strength());
    let ring = engine.refinement.ring();
    let pairs = terrain_pairs(terrain, &declared, seed, count);
    let requests = open_requests(&engine, &pairs);
    let (comparison, partition) = arm_comparison(arm);
    assert!(!partition, "the solve is read on the open section");
    let goal = segment_source(&engine, ring, toward);
    println!(
        "executed kinetic: {count} {terrain} requests at development seed {seed}, the arm {arm}, toward {toward}; the bank p = {}, grain 2^(-{BANK_GRAIN})",
        bank_strength()
    );
    for source in sources {
        let started = Instant::now();
        let (label, spec) = source.split_once('=').expect("<label>=<source>");
        let theta = segment_source(&engine, ring, spec);
        let leg = theta
            .clone()
            .with_ports(ring, None, Some(goal.source_port(ring).expect("E").clone()), None)
            .expect("the leg's end");
        let reading = kinetic_reading(
            &engine.field,
            &theta,
            Some(&leg),
            &requests,
            &engine.refinement,
            &bank,
            BANK_GRAIN,
            comparison,
            false,
        )
        .expect("the kinetic reading");
        println!(
            "  {label}: ρ {}; {} ∈ {} nats; {} returns; the normal law's unit move against the leg {}; {} ms",
            theta.transport(ring),
            symbol(&comparison),
            cell(&reading.before.value, 1 << 12),
            reading.returns,
            reading.unit_cosine.as_ref().map_or_else(|| format!("none ({:?})", reading.refusal), |c| at_bits(c).to_string()),
            started.elapsed().as_millis()
        );
        let Some(solve) = &reading.solve else {
            println!("  {label}: no solve ({:?})", reading.refusal);
            continue;
        };
        let last = solve.residuals.len();
        let mut k = 1;
        while k <= last {
            println!(
                "    iterate {k}: against the leg {}, residual energy {}",
                solve.cosines.get(k - 1).map_or_else(|| "none".to_string(), |c| at_bits(c).to_string()),
                at_bits(&solve.residuals[k - 1]),
            );
            k = if k * 2 > last && k < last { last } else { k * 2 };
        }
        println!(
            "    {} readings; stop {:?} after {last}; the model's change {}; v's largest entry {} (24 bits); {} ms",
            solve.readings,
            solve.stop,
            at_bits(&solve.predicted),
            at_bits(&largest_of(&solve.moved)),
            started.elapsed().as_millis()
        );
    }
    println!("executed kinetic: {} ms; resident {}", clock.elapsed().as_millis(), resident());
}

/// [measured-diagnostic; agent-inferred, October 2; the
/// [transport modulus record](../../records/2026-10-02_THE_TRANSPORT_MODULUS_JOINS_THE_RECEIVERS_MINIMUM_ENERGY_MOVE.md)
/// §4c] **The joined move's direction at each source, read and not taken** (`executed joined
/// <terrain> <seed> <count> <arm> <label=source>…`): `hnn::executed::kinetic_reading` with the joined
/// solve. Prints the source's `ρ` and the founding's `ρ₀`, the comparison, the solve's `Δρ` before any
/// bound, and its two drives: the readings' own ask along `ρ` and what `E`'s move already supplies
/// (`Δρ = (own − supplied)/s`). Nothing is moved.
pub(super) fn joined(terrain: &str, seed: u64, count: usize, arm: &str, sources: &[String]) {
    use holonics::hnn::executed::kinetic_reading;
    let clock = Instant::now();
    let declared = order_declared();
    let engine = Engine::new(declared);
    let bank = bank_of(declared.period, &bank_strength());
    let ring = engine.refinement.ring();
    let pairs = terrain_pairs(terrain, &declared, seed, count);
    let requests = open_requests(&engine, &pairs);
    let (comparison, partition) = arm_comparison(arm);
    assert!(!partition, "the solve is read on the open section");
    println!(
        "executed joined: {count} {terrain} requests at development seed {seed}, the arm {arm}; the bank p = {}, grain 2^(-{BANK_GRAIN})",
        bank_strength()
    );
    for source in sources {
        let started = Instant::now();
        let (label, spec) = source.split_once('=').expect("<label>=<source>");
        let theta = segment_source(&engine, ring, spec);
        let founding = theta.founding_transport(&engine.field, ring).expect("the founding");
        let reading = kinetic_reading(
            &engine.field,
            &theta,
            None,
            &requests,
            &engine.refinement,
            &bank,
            BANK_GRAIN,
            comparison,
            true,
        )
        .expect("the joined reading");
        println!(
            "  {label}: ρ {}, ρ₀ {founding}; {} ∈ {} nats; {} returns; {} ms",
            theta.transport(ring),
            symbol(&comparison),
            cell(&reading.before.value, 1 << 12),
            reading.returns,
            started.elapsed().as_millis()
        );
        let Some(solve) = &reading.solve else {
            println!("  {label}: no solve ({:?})", reading.refusal);
            continue;
        };
        match &solve.modulus_drive {
            Some((own, supplied)) => println!(
                "    Δρ {:?}; own {}, supplied {}, own − supplied {} (24 bits); stop {:?} after {}; {} ms",
                solve.modulus.as_ref().map(at_bits),
                at_bits(own),
                at_bits(supplied),
                at_bits(&(own - supplied)),
                solve.stop,
                solve.residuals.len(),
                started.elapsed().as_millis()
            ),
            None => println!("    no modulus drive; stop {:?}; {} ms", solve.stop, started.elapsed().as_millis()),
        }
    }
    println!("executed joined: {} ms; resident {}", clock.elapsed().as_millis(), resident());
}

/// [measured-diagnostic; agent-inferred, October 2; the
/// [turn-clock record](../../records/2026-10-02_THE_COMMITMENT_IS_READ_ON_THE_TURN_CLOCK_ITS_ORDER_IS_RESOLVED_TO_ONE_TURN_AND_A_CROSSING_JUMPS_ONLY_AT_A_WHOLE_TURN.md)
/// §4, §9; read-only, never a law] **The whole-turn commitment turns beside the gap order**
/// (`executed instants`). Each request's release runs under its own law (`LockOrder::Gap`), its
/// refinements kept. At every refinement, each eligible station's commitment turn is read from its
/// candidates' joint growths: the least whole `n` at which the commitment residual
/// `R(n) = a_top^(−n) + Σ_y (a_y/a_top)^n` places the top within the grain, `(1 + R(n))^16 ≤ 2`
/// (`τ = 1/16` bit; Lean `HNN/OrderTemperature.commit_turn_iff`). The turn is enclosed: `[n_lo, n_hi]`
/// from the readings' two ends, each power carried by squaring with every product rounded outward on
/// `2^(−64)ℤ`, so the enclosure is sound. A refinement is read against the whole-turn law: the
/// eligible stations of least turn commit together.
pub(super) fn instants(terrain: &str, seed: u64, count: usize, sources: &[String]) {
    use holonics::hnn::prediction::bank_release;
    use holonics::hnn::ring::Growth;
    use rayon::prelude::*;
    let declared = order_declared();
    let engine = Engine::new(declared);
    let bank = bank_of(declared.period, &bank_strength());
    let ring = engine.refinement.ring();
    let alphabet = engine.field.alphabet();
    let pairs = terrain_pairs(terrain, &declared, seed, count);
    let scale = BigInt::one() << 64u32;
    // x rounded on 2^(−64)ℤ, up or down.
    let round = |x: &Rat, up: bool| -> Rat {
        let scaled = x * Rat::from_integer(scale.clone());
        let n = if up { scaled.ceil() } else { scaled.floor() }.to_integer();
        Rat::new(n, scale.clone())
    };
    // x^n for 0 ≤ x, carried by squaring with every product rounded the same way.
    let power = |x: &Rat, n: u64, up: bool| -> Rat {
        let (mut base, mut exp, mut acc) = (round(x, up), n, Rat::one());
        while exp > 0 {
            if exp & 1 == 1 {
                acc = round(&(&acc * &base), up);
            }
            base = round(&(&base * &base), up);
            exp >>= 1;
        }
        acc
    };
    // The residual's test at a whole turn, read at one end of the enclosures.
    let commits = |inverse_top: &Rat, ratios: &[Rat], n: u64, up: bool| -> bool {
        let mut residual = power(inverse_top, n, up);
        for r in ratios {
            residual += power(r, n, up);
        }
        let one_plus = Rat::one() + residual;
        let mut sixteenth = one_plus.clone();
        for _ in 0..4 {
            sixteenth = &sixteenth * &sixteenth;
        }
        sixteenth <= Rat::from_integer(BigInt::from(2))
    };
    // The least whole turn at which the test holds: doubling, then bisection.
    let least = |inverse_top: &Rat, ratios: &[Rat], up: bool| -> u64 {
        let mut high = 1u64;
        while !commits(inverse_top, ratios, high, up) {
            high = high.checked_mul(2).expect("a commitment turn below 2^64");
        }
        let mut low = high / 2;
        while low + 1 < high {
            let middle = low + (high - low) / 2;
            if commits(inverse_top, ratios, middle, up) {
                high = middle;
            } else {
                low = middle;
            }
        }
        high
    };
    // A station's turn enclosure [n_lo, n_hi] from its candidates' joints and its top.
    let turns = |joints: &[&Growth], top: usize| -> (u64, u64) {
        let top_growth = joints[top];
        let at = |a_top: &Rat, rival: &dyn Fn(&Growth) -> Rat, up: bool| -> u64 {
            let inverse = Rat::one() / a_top;
            let ratios: Vec<Rat> = (0..joints.len())
                .filter(|&y| y != top)
                .map(|y| rival(joints[y]) / a_top)
                .collect();
            least(&inverse, &ratios, up)
        };
        let n_hi = at(&top_growth.lower, &|g: &Growth| g.upper.clone(), true);
        let n_lo = at(&top_growth.upper, &|g: &Growth| g.lower.clone(), false);
        (n_lo, n_hi)
    };
    for source in sources {
        let (label, spec) = source.split_once('=').unwrap_or((source.as_str(), "opening"));
        let theta = segment_source(&engine, ring, spec);
        let started = Instant::now();
        let per_request: Vec<(Vec<String>, [usize; 6], Vec<u64>)> = pairs
            .par_iter()
            .enumerate()
            .map(|(index, (request, _))| {
                let unit = Instant::now();
                let (current, moment) = ingest(&engine.field, request);
                let placement =
                    BankPlacement::of(&engine.field, &theta, &current, &moment, &engine.refinement)
                        .expect("the placement");
                let (_, refinements) = bank_release(
                    &placement,
                    &engine.refinement,
                    alphabet,
                    &bank,
                    BANK_GRAIN,
                    |amplitudes| bank.read_turn(amplitudes, BANK_GRAIN),
                    true,
                )
                .expect("the release");
                // [refinements, agree, coarser (whole-turn locks more together), inverted
                // (gap locks a station of later turn), enclosure open (n_lo < n_hi somewhere),
                // single-station gap locks]
                let mut tally = [0usize; 6];
                let mut lines = Vec::new();
                let mut locked_turns = Vec::new();
                for (k, refinement) in refinements.iter().enumerate() {
                    if refinement.eligible.is_empty() {
                        continue;
                    }
                    tally[0] += 1;
                    let mut read: Vec<(usize, Rat, (u64, u64))> = Vec::new();
                    for (station, top, gap) in &refinement.eligible {
                        let first = refinement
                            .open
                            .iter()
                            .position(|&(s, _)| s == *station)
                            .expect("an open station");
                        let joints: Vec<&Growth> = (0..alphabet)
                            .map(|class| &refinement.read[first + class].joint)
                            .collect();
                        read.push((*station, gap.clone(), turns(&joints, *top)));
                    }
                    let open = read.iter().any(|(_, _, (lo, hi))| lo < hi);
                    tally[4] += usize::from(open);
                    let least_hi = read.iter().map(|(_, _, (_, hi))| *hi).min().expect("eligible");
                    let least_lo = read.iter().map(|(_, _, (lo, _))| *lo).min().expect("eligible");
                    // The whole-turn law's first set, where the enclosures decide it.
                    let first_set: Vec<usize> = read
                        .iter()
                        .filter(|(_, _, (_, hi))| *hi == least_hi)
                        .map(|(s, _, _)| *s)
                        .collect();
                    let locked: Vec<usize> = refinement.locked.clone();
                    tally[5] += usize::from(locked.len() == 1);
                    for (s, _, (_, hi)) in &read {
                        if locked.contains(s) {
                            locked_turns.push(*hi);
                        }
                    }
                    let inverted = read
                        .iter()
                        .any(|(s, _, (lo, _))| locked.contains(s) && *lo > least_hi);
                    if inverted {
                        tally[3] += 1;
                    } else if !open && locked.iter().all(|s| first_set.contains(s)) {
                        if locked.len() == first_set.len() {
                            tally[1] += 1;
                        } else {
                            tally[2] += 1;
                        }
                    }
                    let listing: Vec<String> = read
                        .iter()
                        .map(|(s, gap, (lo, hi))| {
                            let turn = if lo == hi { format!("{hi}") } else { format!("[{lo},{hi}]") };
                            let mark = if locked.contains(s) { "*" } else { "" };
                            format!("{s}{mark}:gap {} turn {turn}", cell(&ExactInterval::point(gap.clone()), 1 << 12))
                        })
                        .collect();
                    lines.push(format!(
                        "    request {index} refinement {k}: least turn {least_lo}..{least_hi}; {}",
                        listing.join(", ")
                    ));
                }
                lines.push(format!(
                    "    request {index}: {} refinements read, {} ms",
                    tally[0],
                    unit.elapsed().as_millis()
                ));
                (lines, tally, locked_turns)
            })
            .collect();
        let mut total = [0usize; 6];
        let mut histogram: BTreeMap<u64, usize> = BTreeMap::new();
        println!("{label} ({spec}):");
        for (lines, tally, locked_turns) in &per_request {
            for line in lines {
                println!("{line}");
            }
            for (t, x) in total.iter_mut().zip(tally) {
                *t += x;
            }
            for n in locked_turns {
                *histogram.entry(*n).or_insert(0) += 1;
            }
        }
        println!(
            "  {label}: {} refinements with an eligible station; the gap order's locks are the whole-turn law's first set at {}, a strict part of it at {}, a later turn at {}; enclosures left a turn open at {}; single-station gap locks {}",
            total[0], total[1], total[2], total[3], total[4], total[5]
        );
        println!("  {label}: commitment turns (n_hi) of the gap order's locks: {histogram:?}");
        println!("  {label}: wall time {} ms", started.elapsed().as_millis());
    }
}

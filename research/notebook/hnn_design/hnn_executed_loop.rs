//! **The executed comparison's loop** (THE_REBUILD U6; the
//! [diagnosis record](../../records/2026-09-30_THE_LEARNING_FAILURE_DIAGNOSED_THE_TRAINED_COMPARISON_IS_NOT_THE_ONE_THE_RELEASE_EXECUTES.md)
//! §5; #73, #148, #63): `hnn::executed` read on the order-2 terrain at `E` alone.
//!
//! ```sh
//! cargo run --release -p holonics --example hnn_prediction -- executed move <seed> <requests>
//! cargo run --release -p holonics --example hnn_prediction -- executed train <arm> <terrain> <seed> <batch> <moves> <deadline ms> <out>
//! cargo run --release -p holonics --example hnn_prediction -- executed evaluate <terrain> <seed> <count> <out> opening <label=E>…
//! cargo run --release -p holonics --example hnn_prediction -- executed spread <terrain> <seed> <count> opening <label=E>…
//! ```
//!
//! - **`executed train`, `executed evaluate`** (Stage 2, the
//!   [pin](../../records/2026-09-30_THE_EXECUTED_COMPARISONS_BOUNDED_TEST_PINNED_BEFORE_ITS_RUNS.md)):
//!   one arm (`executed` or `face` × `open` or `partition`) trained from the declared opening by the
//!   one ladder, its `E` written; every constitution's confirmation from the open section, its counts
//!   and every section.
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
    BatchComparison, Context, ExecutedMove, Predicate, Request, executed_move, pairing_receipt,
};
use holonics::hnn::prediction::BankPlacement;
use holonics::hnn::ring::{MemberCovector, turn};
use num_bigint::BigInt;

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

/// The partitions' seed of Stage 2's partition arms (the readout's `mask` law), pinned.
const STAGE_TWO_MASK_SEED: u64 = 2_026_093_004;

/// **Stage 2: one arm's training** (`executed train <arm> <terrain> <seed> <batch> <moves>
/// <deadline ms> <out>`). The arm is the declared comparison (`executed` or `face`) crossed with the
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
    use holonics::hnn::executed::face_move;
    use holonics::hnn::prediction::mask;
    let clock = Instant::now();
    let declared = order_declared(false);
    let engine = Engine::new(declared);
    let bank = bank_of(declared.period, &bank_strength());
    let (comparison, contexts) = arm.split_once('-').expect("an arm: executed|face - open|partition");
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
    println!(
        "executed train: arm {arm} on {terrain} at seed {seed}: {moves} moves of {batch} requests; the declared opening; the bank p = {}, grain 2^(-{BANK_GRAIN})",
        bank_strength()
    );
    let mut theta = engine.theta.clone();
    let (mut adopted, mut refused, mut readings) = (0usize, 0usize, 0usize);
    let mut complete = true;
    for (index, chunk) in requests.chunks(batch).enumerate() {
        if clock.elapsed().as_millis() > deadline {
            complete = false;
            println!("  deadline reached before move {index}: incomplete");
            break;
        }
        let started = Instant::now();
        let moved = match comparison {
            "executed" => executed_move(&engine.field, &theta, chunk, &engine.refinement, &bank, BANK_GRAIN),
            "face" => face_move(&engine.field, &theta, chunk, &engine.refinement, &bank, BANK_GRAIN),
            _ => panic!("a comparison: executed | face"),
        }
        .expect("the move");
        readings += moved.before.readings;
        // The two slopes the move reads (a diagnostic added after the station-framed placement's
        // pinned runs): the port's unit move's first order, and the modulus's `γ_ρ` (its sign
        // decides whether the modulus may leave one: none upward from `ρ = 1`).
        let slopes = format!(
            "; the port's first-order slope {}; the modulus's slope γ_ρ {}",
            moved.slope.as_ref().map_or_else(|| "none".to_string(), |s| cell(s, 1 << 12)),
            moved
                .modulus_slope
                .as_ref()
                .map_or_else(|| "none".to_string(), |g| cell(&ExactInterval::point(g.clone()), 1 << 12))
        );
        let sections = if contexts == "open" {
            let targets: Vec<Vec<usize>> = chunk.iter().map(|r| r.targets.clone()).collect();
            let (whole, right, released) = moved.before.sections(&targets);
            format!("; batch released {released}, whole {whole}, stations right {right}")
        } else {
            String::new()
        };
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
    let declared = order_declared(false);
    let engine = Engine::new(declared);
    let bank = bank_of(declared.period, &bank_strength());
    let ring = engine.refinement.ring();
    let pairs = terrain_pairs(terrain, &declared, seed, count);
    let mut listing = String::new();
    for arm in arms {
        let (label, path) = arm.split_once('=').unwrap_or((arm.as_str(), ""));
        let theta = if path.is_empty() {
            engine.theta.clone()
        } else {
            trained(&engine.theta, ring, path)
        };
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
        writeln!(listing, "== {label} on {terrain}, seed {seed}").unwrap();
        for ((request, target), generation) in pairs.iter().zip(&generated) {
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
                } else {
                    incorrect += 1;
                }
            } else {
                held += 1;
            }
            writeln!(
                listing,
                "{} | target {:?} | {} {:?} | locks {:?}",
                request.iter().map(ToString::to_string).collect::<String>(),
                target,
                if generation.release.released() { "released" } else { "held" },
                classes,
                generation.locks
            )
            .unwrap();
        }
        println!(
            "  {label}: released {released}, held {held}, refused {refused}, refused certificates {uncertified}; whole sections {whole} of {count}; incorrect releases {incorrect}; reaching the termination {terminated}; stations right {} by station {by_station:?}; first lock at a request-reading station (0 or 1) {first_request}, first lock right {first_right}",
            by_station.iter().sum::<usize>()
        );
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
    let declared = order_declared(false);
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
    let declared = order_declared(false);
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

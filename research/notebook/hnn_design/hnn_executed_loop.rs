//! **The executed comparison's loop** (THE_REBUILD U6; the
//! [diagnosis record](../../records/2026-09-30_THE_LEARNING_FAILURE_DIAGNOSED_THE_TRAINED_COMPARISON_IS_NOT_THE_ONE_THE_RELEASE_EXECUTES.md)
//! §5; #73, #148, #63): `hnn::executed` read on the order-2 terrain at `E` alone.
//!
//! ```sh
//! cargo run --release -p holonics --example hnn_prediction -- executed move <seed> <requests>
//! ```
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
                .after
                .as_ref()
                .map_or_else(|| "not read".to_string(), |a| cell(&a.value, 1 << 16)),
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
        let amplitudes = turn(&at.storage(&reading.cells));
        // The request's own storage moves with E too: the move's placement is the whole storage
        // move (base and section), linear in E.
        let direction = turn(&along.storage(&reading.cells));
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

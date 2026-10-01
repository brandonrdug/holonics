//! **Loop 1c's modes** (THE_REBUILD U6, step 1, loop 1c; the
//! [pin](../../records/2026-10-01_LOOP_1C_PERSISTENCE_REPRESENTATION_AND_REACH_PINNED_BEFORE_ITS_RUNS.md);
//! #73, #148, #63). Measurement only: every intervention is a diagnostic, never a law, and the
//! original native continuation (gate A's procedure, `executed witness`) is the baseline.
//!
//! ```sh
//! cargo run --release -p holonics --example hnn_prediction -- executed replay <terrain> <seed> <count> <label=state>…
//! cargo run --release -p holonics --example hnn_prediction -- executed coupling <terrain> <seed> <count> <deadline ms> <label=state|label=opening>…
//! cargo run --release -p holonics --example hnn_prediction -- executed represent <terrain> <seed> <count> <iterates> <deadline ms> <out> [<held-out seed>]
//! ```
//!
//! - **`executed replay`** (the pin §1.1): each complete continuing state restored onto the
//!   declared opening (a full remount; a partial file is refused), written back and compared with
//!   its file, and read by the lock face at the decisions, printed in gate A's witness format (the
//!   summary line and every decision term whole) so a listing diffs against gate A's receipt.
//! - **`executed coupling`** (the pin §2): per constitution, every request's release under the
//!   release's own order and the two declared diagnostic orders (`LockOrder`), every station read
//!   at its lock (solved at a refinement), at the actual release with every other lock placed
//!   (solved at the release), the decision term `d(j)` (gate A's count), the paired landing
//!   factorial (normalization × entry, `BankPlacement::storage_over`), and, for every native event
//!   (solved at its lock, not at the release), the lattice of its later locks, the singletons'
//!   factorial and the later locks entered at their targets; then every earlier constitution's
//!   solved station re-read in its own fixed context (retained after later releases).
//! - **`executed represent`** (the pin §3): the exterior fit, a search other than the candidate's
//!   own move. At each iterate every decision term's lock face and gradient
//!   (`executed::site_gradients`); the Gauss–Newton step of least norm placing every term above
//!   the level `(15/16) ln 2` at it, on the dyadic faces; projected onto the source port's lattice and
//!   the entry box, and certified exactly through the actual release (`executed::frozen_reread`:
//!   the own release, and the iterate's frozen decision sites beside it). Every certified
//!   admissible trial is read for the witness and the best; a trial is adopted when its own
//!   release's excess falls by disjoint enclosures. A representation diagnostic, never a learning
//!   result.
//!
//! Every unit prints one line with its elapsed milliseconds; the deadline is checked before each
//! unit, and a run past it stops, reported incomplete.

use super::executed_loop::{
    cell, founded_opening, open_requests, print_terms, remount, remounted, solved_terms,
    terrain_pairs, write_state,
};
use super::*;
use holonics::hnn::HnnError;
use holonics::hnn::constitution::{ContinuingState, Locus};
use holonics::hnn::executed::{
    BatchComparison, Comparison, LockFace, Predicate, Reading, Request, TermSite, compare,
    entry_bound, frozen_reread, lock_face, site_gradients, sites_of,
};
use holonics::hnn::prediction::{BankGeneration, BankPlacement, BankRefinement, LockOrder, bank_release_ordered};
use holonics::hnn::ring::{Growth, TurnReading, turn};
use holonics::holon::deposition::significant;
use holonics::ratio::algebraic::ln_enclosure;
use num_bigint::BigInt;
use num_traits::One;
use rayon::prelude::*;
use std::sync::atomic::{AtomicUsize, Ordering};

/// Readings made by this process (each a bank's turn read), for the per-reading cost.
static READINGS: AtomicUsize = AtomicUsize::new(0);

/// The orders read: the release's own, then the two diagnostics.
const ORDERS: [LockOrder; 3] = [LockOrder::Gap, LockOrder::Ascending, LockOrder::Descending];

fn order_name(order: LockOrder) -> &'static str {
    match order {
        LockOrder::Gap => "gap (native)",
        LockOrder::Ascending => "ascending",
        LockOrder::Descending => "descending",
    }
}

fn mark(p: Predicate) -> &'static str {
    match p {
        Predicate::Holds => "H",
        Predicate::Fails => "F",
        Predicate::Undecided => "U",
    }
}

/// gate A's summary line of a constitution's reading (`executed witness`'s format, exactly).
fn summary(label: &str, theta: &Constitution, batch: &BatchComparison, targets: &[Vec<usize>], stations: usize, ms: u128) -> (usize, usize) {
    let ring = 0;
    let (solved, all) = solved_terms(batch);
    let (whole, right, released) = batch.sections(targets);
    let largest = theta
        .source_port(ring)
        .expect("E")
        .entries()
        .iter()
        .map(|x| x.abs())
        .max()
        .unwrap_or_else(Rat::zero);
    println!(
        "  {label}: solved {solved} of {all} decision terms; whole sections {whole} of {} (released {released}, stations right {right}); L ∈ {} nats, X ∈ {} nats; E's largest entry {}, ρ {}; the terms {:?}; {ms} ms",
        targets.len(),
        cell(&batch.value, 1 << 12),
        cell(&batch.excess, 1 << 12),
        largest,
        theta.transport(ring),
        batch.counts(stations)
    );
    (solved, all)
}

// -------------------------------------------------------------------------------------------
// the replay

/// **The exact replay of written states** (module header).
pub(super) fn replay(terrain: &str, seed: u64, count: usize, states: &[String]) {
    let clock = Instant::now();
    let declared = order_declared();
    let engine = Engine::new(declared);
    let bank = bank_of(declared.period, &bank_strength());
    let ring = engine.refinement.ring();
    let pairs = terrain_pairs(terrain, &declared, seed, count);
    let requests = open_requests(&engine, &pairs);
    let targets: Vec<Vec<usize>> = pairs.iter().map(|(_, t)| t.clone()).collect();
    println!(
        "executed replay: {count} {terrain} requests at seed {seed}; each complete continuing state restored onto the declared opening, written back, and read by the lock face at the decisions"
    );
    for arm in states {
        let started = Instant::now();
        let (label, path) = arm.split_once('=').expect("<label>=<state>");
        #[allow(clippy::disallowed_methods)]
        let text = std::fs::read_to_string(path).expect("read the state");
        // A complete continuing state is restored whole; a file of `E` and `ρ` alone (the exterior
        // fit's witness, a representation diagnostic) is a partial remount, labelled on stderr.
        let complete = ContinuingState::from_text(&text).is_ok();
        let theta = if complete {
            remounted(&engine.theta, path)
        } else {
            remount(&engine.theta, ring, path)
        };
        let back = if complete { write_state(&theta, ring) } else { String::new() };
        let batch = compare(
            &engine.field,
            &theta,
            &requests,
            &engine.refinement,
            &bank,
            BANK_GRAIN,
            Comparison::LOCK_DECISIONS,
        )
        .expect("the restored constitution's reading");
        summary(label, &theta, &batch, &targets, declared.stations, started.elapsed().as_millis());
        print_terms(label, &batch, &targets);
        if complete {
            eprintln!(
                "replay {label}: the restored state written back is {} its file",
                if back == text { "identical to" } else { "NOT identical to" }
            );
        }
    }
    println!("executed replay: {} ms; resident {}", clock.elapsed().as_millis(), resident());
}

// -------------------------------------------------------------------------------------------
// persistence and coupling

/// A lock face read at a section with its station open, or the typed refusal of the reading.
#[derive(Clone, Debug)]
enum Face {
    Read(LockFace),
    Refused(String),
}

impl Face {
    fn of(joints: Vec<Growth>, target: usize) -> Self {
        match lock_face(&joints, target) {
            Ok(face) => Face::Read(face),
            Err(error) => Face::Refused(error.to_string()),
        }
    }

    fn solved(&self) -> Option<Predicate> {
        match self {
            Face::Read(face) => Some(face.solved),
            Face::Refused(_) => None,
        }
    }

    fn holds(&self) -> bool {
        self.solved() == Some(Predicate::Holds)
    }

    fn lock(&self) -> Option<&ExactInterval> {
        match self {
            Face::Read(face) => Some(&face.value),
            Face::Refused(_) => None,
        }
    }

    fn show(&self) -> String {
        match self {
            Face::Read(face) => format!("{} ℓ {}", mark(face.solved), cell(&face.value, 1 << 16)),
            Face::Refused(why) => format!("refused ({why})"),
        }
    }
}

/// **A station's lock face at a section** read afresh: its candidates' storages with `data`
/// entering over the mass of `mass` (`BankPlacement::storage_over`; `data = mass` the release's own
/// storage), each candidate at the station, the five read in parallel.
fn read_face(
    placement: &BankPlacement,
    bank: &ReceivingBank,
    alphabet: usize,
    station: usize,
    data: &[Option<usize>],
    mass: &[Option<usize>],
    target: usize,
) -> Face {
    let joints: Result<Vec<Growth>, HnnError> = (0..alphabet)
        .into_par_iter()
        .map(|class| {
            let mut d = data.to_vec();
            d[station] = Some(class);
            let mut m = mass.to_vec();
            m[station] = Some(class);
            READINGS.fetch_add(1, Ordering::Relaxed);
            Ok(bank
                .read_turn(&turn(&placement.storage_over(station, &d, &m)), BANK_GRAIN)?
                .joint)
        })
        .collect();
    match joints {
        Ok(joints) => Face::of(joints, target),
        Err(error) => Face::Refused(error.to_string()),
    }
}

/// A refinement's kept readings of an open station, as its lock face.
fn kept_face(refinement: &BankRefinement<TurnReading>, alphabet: usize, station: usize, target: usize) -> Face {
    let at = refinement
        .open
        .iter()
        .position(|&(s, class)| s == station && class == 0)
        .expect("an open station");
    Face::of(
        refinement.read[at..at + alphabet].iter().map(|r| r.joint.clone()).collect(),
        target,
    )
}

/// One station's persistence under one order (the pin §2.2): its lock (the refinement and class),
/// the section it was decided at (its lock's, or the last refinement's when never locked), the
/// release's section with it open, and its lock face at each; with the landing's factorial (the
/// normalization alone and the entry alone) when a later lock landed.
#[derive(Clone, Debug)]
struct Station {
    lock: Option<(usize, usize)>,
    /// The stations locked together with it (the same refinement), and those locked at later
    /// refinements (the owner's `Persistence` re-reads a solved lock only when this is not empty).
    co: Vec<usize>,
    later: Vec<usize>,
    decision: Vec<Option<usize>>,
    released: Vec<Option<usize>>,
    at_lock: Face,
    at_release: Face,
    normalization: Option<Face>,
    entry: Option<Face>,
}

/// One request's release under one order and its stations.
struct Ordered {
    generation: BankGeneration,
    refinements: Vec<BankRefinement<TurnReading>>,
    stations: Vec<Station>,
}

/// The release under `order` and every station's persistence and landing factorial; a release a
/// reading refuses (an inadmissible crossing under a diagnostic order) is returned as its refusal.
#[allow(clippy::too_many_arguments)]
fn ordered_release(
    placement: &BankPlacement,
    engine: &Engine,
    bank: &ReceivingBank,
    targets: &[usize],
    order: LockOrder,
) -> Result<Ordered, String> {
    let alphabet = engine.field.alphabet();
    let stations = engine.refinement.stations();
    let (generation, refinements) = bank_release_ordered(
        placement,
        &engine.refinement,
        alphabet,
        bank,
        BANK_GRAIN,
        |amplitudes| {
            READINGS.fetch_add(1, Ordering::Relaxed);
            bank.read_turn(amplitudes, BANK_GRAIN)
        },
        true,
        order,
    )
    .map_err(|error| error.to_string())?;
    let mut section: Vec<Option<usize>> = vec![None; stations];
    for (station, class, ..) in &generation.decisions {
        section[*station] = Some(*class);
    }
    let rows: Vec<Station> = (0..stations)
        .into_par_iter()
        .map(|j| {
            let locked_at = refinements.iter().position(|r| r.locked.contains(&j));
            let k = locked_at.unwrap_or(refinements.len() - 1);
            let decision = refinements[k].placed.clone();
            let (co, later): (Vec<usize>, Vec<usize>) = match locked_at {
                Some(k) => (
                    refinements[k].locked.iter().copied().filter(|&s| s != j).collect(),
                    refinements[k + 1..].iter().flat_map(|r| r.locked.iter().copied()).collect(),
                ),
                None => (Vec::new(), Vec::new()),
            };
            let mut released = section.clone();
            released[j] = None;
            let at_lock = kept_face(&refinements[k], alphabet, j, targets[j]);
            let landed = released != decision;
            let at_release = if landed {
                read_face(placement, bank, alphabet, j, &released, &released, targets[j])
            } else {
                at_lock.clone()
            };
            let (normalization, entry) = if landed && locked_at.is_some() {
                (
                    Some(read_face(placement, bank, alphabet, j, &decision, &released, targets[j])),
                    Some(read_face(placement, bank, alphabet, j, &released, &decision, targets[j])),
                )
            } else {
                (None, None)
            };
            Station {
                lock: locked_at.map(|k| (k, section[j].expect("a locked station's class"))),
                co,
                later,
                decision,
                released,
                at_lock,
                at_release,
                normalization,
                entry,
            }
        })
        .collect();
    Ok(Ordered {
        generation,
        refinements,
        stations: rows,
    })
}

/// `a − b` enclosed.
fn minus(a: &ExactInterval, b: &ExactInterval) -> ExactInterval {
    ExactInterval {
        lower: &a.lower - &b.upper,
        upper: &a.upper - &b.lower,
    }
}

/// `a + b` enclosed.
fn plus(a: &ExactInterval, b: &ExactInterval) -> ExactInterval {
    ExactInterval {
        lower: &a.lower + &b.lower,
        upper: &a.upper + &b.upper,
    }
}

/// The landing factorial's contrasts on `ℓ` (the pin §2.3): the normalization first then the entry,
/// the entry first then the normalization, and the interaction, each enclosed.
fn contrasts(row: &Station) -> Option<String> {
    let (l00, l11) = (row.at_lock.lock()?, row.at_release.lock()?);
    let l10 = row.normalization.as_ref()?.lock()?;
    let l01 = row.entry.as_ref()?.lock()?;
    let interaction = plus(&minus(l11, l10), &minus(l00, l01));
    Some(format!(
        "N then D: {} then {}; D then N: {} then {}; interaction {}",
        cell(&minus(l10, l00), 1 << 16),
        cell(&minus(l11, l10), 1 << 16),
        cell(&minus(l01, l00), 1 << 16),
        cell(&minus(l11, l01), 1 << 16),
        cell(&interaction, 1 << 16)
    ))
}

/// The cells of a section with the subset `bits` of `later` placed at their classes in `released`.
fn with_subset(
    decision: &[Option<usize>],
    released: &[Option<usize>],
    later: &[usize],
    bits: usize,
) -> Vec<Option<usize>> {
    let mut cells = decision.to_vec();
    for (index, &station) in later.iter().enumerate() {
        if bits & (1 << index) != 0 {
            cells[station] = released[station];
        }
    }
    cells
}

/// A fixed context of an earlier constitution's solved station, re-read at later constitutions.
struct Item {
    constitution: usize,
    request: usize,
    station: usize,
    kind: &'static str,
    cells: Vec<Option<usize>>,
}

/// **Persistence and coupling** (module header; the pin §2).
pub(super) fn coupling(terrain: &str, seed: u64, count: usize, deadline: u128, arms: &[String]) {
    let clock = Instant::now();
    let declared = order_declared();
    let engine = Engine::new(declared);
    let bank = bank_of(declared.period, &bank_strength());
    let ring = engine.refinement.ring();
    let alphabet = engine.field.alphabet();
    let stations = declared.stations;
    let pairs = terrain_pairs(terrain, &declared, seed, count);
    let requests = open_requests(&engine, &pairs);
    let targets: Vec<Vec<usize>> = pairs.iter().map(|(_, t)| t.clone()).collect();
    println!(
        "executed coupling: {count} {terrain} requests at seed {seed}; at each constitution the release under the orders {:?}, every station at its lock, at the release and at its decision term, the landing factorial, the native events' lattices, and the earlier constitutions' solved stations re-read in their fixed contexts; deadline {deadline} ms; {} threads",
        ORDERS.map(order_name),
        rayon::current_num_threads()
    );
    let mut items: Vec<Item> = Vec::new();
    let mut previous: Option<(usize, Vec<Vec<(bool, bool)>>)> = None;
    for (index, arm) in arms.iter().enumerate() {
        if clock.elapsed().as_millis() > deadline {
            println!("executed coupling: the deadline, before constitution {index} (incomplete)");
            break;
        }
        let started = Instant::now();
        let start_readings = READINGS.load(Ordering::Relaxed);
        let (label, path) = arm.split_once('=').unwrap_or((arm.as_str(), ""));
        let theta = if path.is_empty() || path == "opening" {
            founded_opening(&engine)
        } else {
            // A complete continuing state restored whole, and written back against its file (the
            // replay's item 3); a file of `E` and `ρ` alone (a representation witness) is a partial
            // remount, labelled so.
            #[allow(clippy::disallowed_methods)]
            let text = std::fs::read_to_string(path).expect("read the state");
            if ContinuingState::from_text(&text).is_ok() {
                let theta = remounted(&engine.theta, path);
                println!(
                    "constitution {label}: the restored state written back is {} its file",
                    if write_state(&theta, ring) == text { "identical to" } else { "NOT identical to" }
                );
                theta
            } else {
                println!("constitution {label}: E and ρ alone, a partial remount (a representation diagnostic)");
                remount(&engine.theta, ring, path)
            }
        };
        let placements: Vec<BankPlacement> = requests
            .par_iter()
            .map(|r| {
                BankPlacement::of(&engine.field, &theta, &r.current, &r.moment, &engine.refinement)
                    .expect("a placement")
            })
            .collect();
        // The three orders' releases and every station's persistence and landing factorial.
        let releases: Vec<Vec<Result<Ordered, String>>> = placements
            .par_iter()
            .zip(&targets)
            .map(|(placement, targets)| {
                // The three orders' releases are co-present regions: shared immutable input (the
                // placement), one output each.
                ORDERS
                    .par_iter()
                    .map(|&order| ordered_release(placement, &engine, &bank, targets, order))
                    .collect()
            })
            .collect();
        let natives: Vec<&Ordered> = releases
            .iter()
            .map(|o| o[0].as_ref().expect("the native release reads as the continuation read it"))
            .collect();
        let released_ms = started.elapsed().as_millis();
        println!(
            "constitution {label} (ρ = {}): the releases and the stations read; {} readings; {released_ms} ms",
            theta.transport(ring),
            READINGS.load(Ordering::Relaxed) - start_readings
        );
        // The decision terms (gate A's count) on the native order.
        let mut decision_solved = 0;
        let mut decision_all = 0;
        let mut decided: Vec<Vec<Option<Predicate>>> = Vec::new();
        for (q, (request, native)) in requests.iter().zip(&natives).enumerate() {
            let (sites, _) = sites_of(q, request, &native.refinements, Reading::Decisions, stations, alphabet);
            let mut row = vec![None; stations];
            for site in &sites {
                let k = site.context.expect("an executed refinement");
                let face = kept_face(&native.refinements[k], alphabet, site.station, targets[q][site.station]);
                decision_all += 1;
                decision_solved += usize::from(face.holds());
                row[site.station] = face.solved();
            }
            decided.push(row);
        }
        println!("  decision terms (gate A's count, native order): solved {decision_solved} of {decision_all}");
        // Each order's counts and every station whole.
        for (o, &order) in ORDERS.iter().enumerate() {
            let (mut locked, mut held, mut at_lock, mut stay, mut fall, mut undecided, mut landed) = (0, 0, 0, 0, 0, 0, 0);
            let (mut whole, mut right, mut released, mut refused) = (0, 0, 0, 0);
            for (q, ordered) in releases.iter().enumerate() {
                let Ok(r) = &ordered[o] else {
                    refused += 1;
                    continue;
                };
                if r.generation.release.released() {
                    released += 1;
                    let hits = r.generation.release.classes.iter().zip(&targets[q]).filter(|(a, b)| a == b).count();
                    right += hits;
                    whole += usize::from(hits == stations);
                }
                for s in &r.stations {
                    if s.lock.is_some() {
                        locked += 1;
                    } else {
                        held += 1;
                    }
                    if s.lock.is_some() && s.at_lock.holds() {
                        at_lock += 1;
                        if !s.later.is_empty() {
                            landed += 1;
                            match s.at_release.solved() {
                                Some(Predicate::Holds) => stay += 1,
                                Some(Predicate::Undecided) => undecided += 1,
                                _ => fall += 1,
                            }
                        }
                    }
                }
            }
            println!(
                "  order {}: locked {locked}, never locked {held}; solved at the lock {at_lock}, of them with a later lock {landed}: at the release solved {stay}, not solved {fall}, undecided {undecided}; released {released} of {count}, whole {whole}, stations right {right}; releases refused {refused}",
                order_name(order)
            );
            println!(
                "  order {}: Persistence {{ locks: {locked}, solved: {at_lock}, reread: {landed}, stay: {stay}, fall: {} }}",
                order_name(order),
                fall + undecided
            );
            for (q, ordered) in releases.iter().enumerate() {
                let r = match &ordered[o] {
                    Ok(r) => r,
                    Err(why) => {
                        println!("    request {q}: target {:?}; the release refused ({why})", targets[q]);
                        continue;
                    }
                };
                println!(
                    "    request {q}: target {:?}; {} {:?}, locks {:?}",
                    targets[q],
                    if r.generation.release.released() { "released" } else { "held" },
                    r.generation.release.classes,
                    r.generation.locks
                );
                for (j, s) in r.stations.iter().enumerate() {
                    let pattern = match (&s.normalization, &s.entry) {
                        (Some(n), Some(e)) => format!(
                            "; factorial (N0D0, N1D0, N0D1, N1D1) ({}, {}, {}, {}): N1D0 {}, N0D1 {}; {}",
                            s.at_lock.solved().map_or("R", mark),
                            n.solved().map_or("R", mark),
                            e.solved().map_or("R", mark),
                            s.at_release.solved().map_or("R", mark),
                            n.show(),
                            e.show(),
                            contrasts(s).unwrap_or_else(|| "contrasts refused".to_string())
                        ),
                        _ => String::new(),
                    };
                    let decision = if o == 0 {
                        format!(", decision term {}", decided[q][j].map_or("—", mark))
                    } else {
                        String::new()
                    };
                    println!(
                        "      station {j}: {}; at the lock {}; at the release {}{decision}{pattern}",
                        s.lock.map_or_else(|| "never locked".to_string(), |(k, class)| format!("locked {class} at refinement {k}")),
                        s.at_lock.show(),
                        s.at_release.show()
                    );
                }
            }
        }
        let stations_ms = started.elapsed().as_millis();
        // The native events: solved at the lock, not at the release.
        let lattice_started = Instant::now();
        let lattice_readings = READINGS.load(Ordering::Relaxed);
        let mut events = 0;
        for (q, native) in natives.iter().enumerate() {
            for (j, s) in native.stations.iter().enumerate() {
                if s.lock.is_none() || !s.at_lock.holds() || s.at_release.holds() || s.later.is_empty() {
                    continue;
                }
                events += 1;
                // Every landing after the decision's section: the co-locked stations and the later locks.
                let mut later: Vec<usize> = s.co.iter().chain(&s.later).copied().collect();
                later.sort_unstable();
                let subsets = 1usize << later.len();
                let faces: Vec<Face> = (0..subsets)
                    .into_par_iter()
                    .map(|bits| {
                        if bits == 0 {
                            s.at_lock.clone()
                        } else if bits == subsets - 1 {
                            s.at_release.clone()
                        } else {
                            let cells = with_subset(&s.decision, &s.released, &later, bits);
                            read_face(&placements[q], &bank, alphabet, j, &cells, &cells, targets[q][j])
                        }
                    })
                    .collect();
                println!(
                    "  event: request {q} station {j} (target {}), locked at refinement {} with {:?}, landings {:?} at classes {:?}",
                    targets[q][j],
                    s.lock.expect("locked").0,
                    s.co,
                    later,
                    later.iter().map(|&i| s.released[i].expect("placed")).collect::<Vec<_>>()
                );
                for (bits, face) in faces.iter().enumerate() {
                    let placed: Vec<usize> = later.iter().enumerate().filter(|(b, _)| bits & (1 << b) != 0).map(|(_, &i)| i).collect();
                    println!("    later locks placed {placed:?}: {}", face.show());
                }
                // The minimal undoing sets: not solved there, solved at every proper subset.
                let solved = |bits: usize| faces[bits].holds();
                let minimal: Vec<Vec<usize>> = (1..subsets)
                    .filter(|&bits| !solved(bits) && (0..subsets).filter(|&sub| sub & bits == sub && sub != bits).all(solved))
                    .map(|bits| later.iter().enumerate().filter(|(b, _)| bits & (1 << b) != 0).map(|(_, &i)| i).collect())
                    .collect();
                let monotone = (0..subsets).all(|bits| solved(bits) || (0..subsets).filter(|&sup| sup & bits == bits).all(|sup| !solved(sup)));
                println!("    minimal undoing sets {minimal:?}; undoing is upward closed: {monotone}");
                // The Möbius interactions of ℓ over the lattice (order two and more), certainly nonzero.
                let mut certain = Vec::new();
                let mut straddling = 0;
                for bits in 1..subsets {
                    if bits.count_ones() < 2 {
                        continue;
                    }
                    let mut sum = ExactInterval::point(Rat::zero());
                    let mut known = true;
                    for sub in 0..subsets {
                        if sub & bits != sub {
                            continue;
                        }
                        let Some(l) = faces[sub].lock() else {
                            known = false;
                            break;
                        };
                        sum = if (bits.count_ones() - sub.count_ones()) % 2 == 0 { plus(&sum, l) } else { minus(&sum, l) };
                    }
                    if !known {
                        continue;
                    }
                    if sum.lower.is_positive() || sum.upper.is_negative() {
                        let placed: Vec<usize> = later.iter().enumerate().filter(|(b, _)| bits & (1 << b) != 0).map(|(_, &i)| i).collect();
                        certain.push(format!("{placed:?} {}", cell(&sum, 1 << 16)));
                    } else {
                        straddling += 1;
                    }
                }
                println!("    interactions of order ≥ 2 certainly nonzero: {}; straddling zero: {straddling}", certain.join(", "));
                // Each later lock alone: its normalization and its entry apart; and the later locks entered
                // at their targets (the terrain's, read only here).
                for &k in &later {
                    let mut landed = s.decision.clone();
                    landed[k] = s.released[k];
                    let n = read_face(&placements[q], &bank, alphabet, j, &s.decision, &landed, targets[q][j]);
                    let e = read_face(&placements[q], &bank, alphabet, j, &landed, &s.decision, targets[q][j]);
                    println!("    later lock {k} alone: normalization {}; entry {}", n.show(), e.show());
                }
                let mut at_targets = s.decision.clone();
                for &k in &later {
                    at_targets[k] = Some(targets[q][k]);
                }
                let t = read_face(&placements[q], &bank, alphabet, j, &at_targets, &at_targets, targets[q][j]);
                println!("    the later stations entered at their targets: {}", t.show());
            }
        }
        println!(
            "  events {events}; {} readings; {} ms",
            READINGS.load(Ordering::Relaxed) - lattice_readings,
            lattice_started.elapsed().as_millis()
        );
        // Retention: every earlier constitution's solved station re-read in its fixed context.
        let retention_started = Instant::now();
        let retention_readings = READINGS.load(Ordering::Relaxed);
        let reread: Vec<Option<Predicate>> = items
            .par_iter()
            .map(|item| {
                read_face(&placements[item.request], &bank, alphabet, item.station, &item.cells, &item.cells, targets[item.request][item.station]).solved()
            })
            .collect();
        let mut by: BTreeMap<(usize, &'static str), [usize; 4]> = BTreeMap::new();
        for (item, predicate) in items.iter().zip(&reread) {
            let slot = by.entry((item.constitution, item.kind)).or_default();
            slot[0] += 1;
            match predicate {
                Some(Predicate::Holds) => slot[1] += 1,
                Some(Predicate::Fails) => slot[2] += 1,
                Some(Predicate::Undecided) => slot[3] += 1,
                None => {}
            }
        }
        for ((from, kind), [all, holds, fails, undecided]) in &by {
            println!("  retained from constitution {from} ({kind} context): {all} re-read, solved {holds}, failing {fails}, undecided {undecided}");
        }
        // Own-context retention: solved at the previous constitution's own contexts and at this one's.
        let own: Vec<Vec<(bool, bool)>> = natives
            .iter()
            .map(|o| o.stations.iter().map(|s| (s.lock.is_some() && s.at_lock.holds(), s.at_release.holds() && s.lock.is_some())).collect())
            .collect();
        if let Some((from, before)) = &previous {
            let (mut lock_kept, mut lock_had, mut release_kept, mut release_had) = (0, 0, 0, 0);
            for (b, a) in before.iter().flatten().zip(own.iter().flatten()) {
                lock_had += usize::from(b.0);
                lock_kept += usize::from(b.0 && a.0);
                release_had += usize::from(b.1);
                release_kept += usize::from(b.1 && a.1);
            }
            println!("  own contexts from constitution {from}: solved at the lock {lock_had}, still at its own lock {lock_kept}; solved at the release {release_had}, still at its own release {release_kept}");
        }
        previous = Some((index, own));
        for (q, native) in natives.iter().enumerate() {
            for (j, s) in native.stations.iter().enumerate() {
                if s.lock.is_none() {
                    continue;
                }
                if s.at_lock.holds() {
                    items.push(Item { constitution: index, request: q, station: j, kind: "lock", cells: s.decision.clone() });
                }
                if s.at_release.holds() {
                    items.push(Item { constitution: index, request: q, station: j, kind: "release", cells: s.released.clone() });
                }
            }
        }
        println!(
            "  retention: {} readings; {} ms",
            READINGS.load(Ordering::Relaxed) - retention_readings,
            retention_started.elapsed().as_millis()
        );
        let readings = READINGS.load(Ordering::Relaxed) - start_readings;
        println!(
            "constitution {label}: {readings} readings; the releases {released_ms} ms, through the stations {stations_ms} ms, in all {} ms",
            started.elapsed().as_millis()
        );
    }
    println!(
        "executed coupling: {} readings; {} ms; resident {}",
        READINGS.load(Ordering::Relaxed),
        clock.elapsed().as_millis(),
        resident()
    );
}

// -------------------------------------------------------------------------------------------
// representation: the exterior fit

/// A rational's dyadic face at 64 significant bits toward zero.
fn face64(x: &Rat) -> Rat {
    if x.is_negative() {
        -significant(&-x.clone(), 64, false)
    } else if x.is_zero() {
        Rat::zero()
    } else {
        significant(x, 64, false)
    }
}

/// The nearest point of the lattice of unit `u` (ties up).
fn on_lattice(x: &Rat, unit: &Rat) -> Rat {
    ((x / unit) + Rat::new(BigInt::one(), BigInt::from(2))).floor() * unit
}

/// The largest power of two at or below `x > 0`.
fn power_below(x: &Rat) -> Rat {
    let mut p = Rat::one();
    let two = Rat::from_integer(2.into());
    while &p * &two <= *x {
        p *= &two;
    }
    while p > *x {
        p /= &two;
    }
    p
}

/// **The representation search** (module header; the pin §3).
#[allow(clippy::too_many_arguments)]
pub(super) fn represent(
    terrain: &str,
    seed: u64,
    count: usize,
    iterates: usize,
    deadline: u128,
    out: &str,
    held_out: Option<u64>,
) {
    let clock = Instant::now();
    let declared = order_declared();
    let engine = Engine::new(declared);
    let bank = bank_of(declared.period, &bank_strength());
    let ring = engine.refinement.ring();
    let pairs = terrain_pairs(terrain, &declared, seed, count);
    let requests: Vec<Request> = open_requests(&engine, &pairs);
    let targets: Vec<Vec<usize>> = pairs.iter().map(|(_, t)| t.clone()).collect();
    let opening = founded_opening(&engine);
    let unit = opening.lattice(Locus::SourcePort(ring)).expect("the port's lattice").unit();
    let bound = entry_bound();
    let ln2 = ln_enclosure(&Rat::from_integer(2.into())).expect("ln 2");
    let level = &ln2.lower * Rat::new(BigInt::from(15), BigInt::from(16));
    println!(
        "executed represent: {count} {terrain} requests at development seed {seed}; the exterior fit (least-norm Gauss–Newton on the lock faces above (15/16) ln 2, projected onto the lattice 2^(-{}) and the entry box ±{bound}, certified through the actual release) from the founded opening (ρ = {}), at most {iterates} iterates, the ladder at most {} trials, deadline {deadline} ms; {} threads",
        opening.lattice(Locus::SourcePort(ring)).expect("lattice").exponent(),
        opening.transport(ring),
        holonics::hnn::executed::LADDER_DEPTH,
        rayon::current_num_threads()
    );
    let mut theta = opening.clone();
    let mut best: Option<(usize, String, Constitution, BatchComparison)> = None;
    let mut best_frozen: Option<(usize, String)> = None;
    let mut stop = "the iterates are spent".to_string();
    let mut found = false;
    for index in 0..iterates {
        if clock.elapsed().as_millis() > deadline {
            stop = format!("the deadline, before iterate {index} (incomplete)");
            break;
        }
        let started = Instant::now();
        let (batch, gradients) = site_gradients(&engine.field, &theta, &requests, &engine.refinement, &bank, BANK_GRAIN)
            .expect("the iterate's readings");
        let read_ms = started.elapsed().as_millis();
        let label = format!("iterate {index}");
        let (solved, all) = summary(&label, &theta, &batch, &targets, declared.stations, read_ms);
        if best.as_ref().is_none_or(|(s, ..)| solved > *s) {
            best = Some((solved, label.clone(), theta.clone(), batch.clone()));
        }
        if solved == all {
            found = true;
            stop = format!("a witness at iterate {index}");
            break;
        }
        // The active terms: not certainly below the level; their rows, at the dyadic faces.
        let solve_started = Instant::now();
        let mut rows: Vec<Vec<Rat>> = Vec::new();
        let mut residuals: Vec<Rat> = Vec::new();
        let mut omitted = 0;
        for g in &gradients {
            if g.lock.upper <= level {
                continue;
            }
            let Some((port, modulus)) = &g.gradient else {
                omitted += 1;
                continue;
            };
            let mut row: Vec<Rat> = port.entries().iter().map(face64).collect();
            row.push(face64(modulus));
            rows.push(row);
            residuals.push(face64(&(&g.lock.upper - &level)));
        }
        if rows.is_empty() {
            stop = format!("iterate {index}: no active term has a resolved gradient ({omitted} omitted)");
            break;
        }
        let n = rows.len();
        let gram: Vec<Vec<Rat>> = (0..n)
            .into_par_iter()
            .map(|a| (0..n).map(|b| rows[a].iter().zip(&rows[b]).map(|(x, y)| x * y).sum()).collect())
            .collect();
        let gram = ExactRatMatrix::new(gram).expect("the Gram");
        let (inverse, regularized) = match gram.inverse() {
            Ok(inverse) => (inverse, None),
            Err(_) => {
                let trace: Rat = (0..n).map(|a| gram.get(a, a).expect("diagonal").clone()).sum();
                let mu = trace / Rat::from_integer(BigInt::from(n as u64)) / Rat::from_integer(BigInt::from(1u64 << 16));
                let shifted = gram
                    .add(&ExactRatMatrix::identity(n).expect("I").scaled(&mu))
                    .expect("shifted");
                (shifted.inverse().expect("the shifted Gram"), Some(mu))
            }
        };
        let y = inverse.apply(&residuals).expect("y");
        let width = rows[0].len();
        let direction: Vec<Rat> = (0..width)
            .into_par_iter()
            .map(|c| -rows.iter().zip(&y).map(|(row, w)| &row[c] * w).sum::<Rat>())
            .collect();
        let largest = direction[..width - 1].iter().map(|x| x.abs()).max().unwrap_or_else(Rat::zero);
        println!(
            "    iterate {index}: {n} active terms ({omitted} omitted, unresolved), the Gram {}; the step's largest entry change {}, its modulus change {}; {} ms",
            match &regularized {
                None => "invertible".to_string(),
                Some(mu) => format!("singular, shifted by μ = {}", cell(&ExactInterval::point(mu.clone()), 1 << 16)),
            },
            cell(&ExactInterval::point(largest.clone()), 1 << 16),
            cell(&ExactInterval::point(direction[width - 1].clone()), 1 << 16),
            solve_started.elapsed().as_millis()
        );
        // The ladder: from the largest power of two keeping the step's entry change within the
        // entry bound (at most one), halving, each trial projected and certified.
        let port = theta.source_port(ring).expect("E").clone();
        let (rows_e, columns) = (port.rows(), port.columns());
        let sites: Vec<Vec<TermSite>> = batch.requests.iter().map(|r| r.terms.iter().map(|t| t.site.clone()).collect()).collect();
        let mut step = if largest.is_positive() { power_below(&(&bound / &largest)).min(Rat::one()) } else { Rat::one() };
        let mut adopted = None;
        for trial in 0..holonics::hnn::executed::LADDER_DEPTH {
            let trial_started = Instant::now();
            let moved: Vec<Vec<Rat>> = (0..rows_e)
                .map(|r| {
                    (0..columns)
                        .map(|c| {
                            let x = port.get(r, c).expect("entry") + &step * &direction[r * columns + c];
                            on_lattice(&x, &unit).max(-bound.clone()).min(bound.clone())
                        })
                        .collect()
                })
                .collect();
            let modulus = on_lattice(&(theta.transport(ring) + &step * &direction[width - 1]), &unit)
                .max(unit.clone())
                .min(Rat::one());
            let moved = ExactRatMatrix::new(moved).expect("E′");
            if moved == port && modulus == theta.transport(ring) {
                println!("      trial {trial}: η {step}: below the lattice");
                break;
            }
            let successor = opening
                .clone()
                .with_ports(ring, None, Some(moved), None)
                .expect("E′ on the opening")
                .with_transport(ring, modulus)
                .expect("ρ′ passive on the lattice");
            let bits = successor.exact_bits();
            let read = frozen_reread(
                &engine.field,
                &successor,
                &requests,
                &engine.refinement,
                &bank,
                BANK_GRAIN,
                Comparison::LOCK_DECISIONS,
                &sites,
            );
            let (own, frozen, made) = match read {
                Ok(read) => read,
                Err(error) => {
                    println!("      trial {trial}: η {step}: refused ({error}); {} ms", trial_started.elapsed().as_millis());
                    step /= Rat::from_integer(2.into());
                    continue;
                }
            };
            let uncertified = own.requests.iter().any(|r| r.generation.as_ref().is_some_and(|g| g.uncertified.is_some()));
            let (s, _) = solved_terms(&own);
            let f = frozen.iter().flatten().filter(|t| t.comparison.solved == Predicate::Holds).count();
            let (whole, right, released) = own.sections(&targets);
            let over = bits > successor.budget();
            // Every certified, admissible trial is read for the witness and the best; the
            // adoption reads the own release's excess strictly lower by disjoint enclosures.
            let admissible = !uncertified && !over;
            let witness = admissible && s == all;
            let better = admissible && own.excess.upper < batch.excess.lower;
            println!(
                "      trial {trial}: η {step}: own solved {s} of {all}, frozen sites solved {f} of {all} ({made} frozen readings made); X ∈ {} nats; released {released}, whole {whole}, stations right {right}; exact bits {bits}{}{}; {}; {} ms",
                cell(&own.excess, 1 << 12),
                if uncertified { "; a lock's certificate refused" } else { "" },
                if over { "; past the budget" } else { "" },
                if witness { "a witness" } else if better { "adopted" } else { "not adopted" },
                trial_started.elapsed().as_millis()
            );
            if best_frozen.as_ref().is_none_or(|(b, _)| f > *b) {
                best_frozen = Some((f, format!("iterate {index}, trial {trial}")));
            }
            if admissible && best.as_ref().is_none_or(|(b, ..)| s > *b) {
                best = Some((s, format!("iterate {index}, trial {trial}"), successor.clone(), own.clone()));
            }
            if witness {
                found = true;
                stop = format!("a witness at iterate {index}, trial {trial}");
            }
            if witness || better {
                adopted = Some(successor);
                break;
            }
            step /= Rat::from_integer(2.into());
        }
        match adopted {
            Some(_) if found => break,
            Some(successor) => theta = successor,
            None => {
                stop = format!("iterate {index}: no trial adopted (the set is fixed: the next iterate would repeat it)");
                break;
            }
        }
        println!("    iterate {index}: {} ms", started.elapsed().as_millis());
        if index + 1 == iterates {
            let last = compare(&engine.field, &theta, &requests, &engine.refinement, &bank, BANK_GRAIN, Comparison::LOCK_DECISIONS)
                .expect("the last iterate's reading");
            let label = format!("iterate {} (after the last step)", index + 1);
            let (solved, all) = summary(&label, &theta, &last, &targets, declared.stations, 0);
            if best.as_ref().is_none_or(|(s, ..)| solved > *s) {
                best = Some((solved, label, theta.clone(), last.clone()));
            }
            if solved == all {
                found = true;
                stop = "a witness after the last step".to_string();
            }
        }
    }
    let (solved, label, theta_best, batch) = best.expect("an iterate read");
    let port = theta_best.source_port(ring).expect("E");
    let mut text = format!("E {} {}\n", port.rows(), port.columns());
    for r in 0..port.rows() {
        text += &(0..port.columns()).map(|c| port.get(r, c).expect("entry").to_string()).collect::<Vec<_>>().join(" ");
        text.push('\n');
    }
    text += &format!("rho {}\n", theta_best.transport(ring));
    #[allow(clippy::disallowed_methods)]
    std::fs::write(out, text).expect("write the best");
    let all = solved_terms(&batch).1;
    match (found, &best_frozen) {
        (true, _) => println!("executed represent: a witness FOUND at {label}: the strict test holds at all {all} decision terms of its own release; E and ρ written to {out} (a representation diagnostic, not a learning result)"),
        (false, Some((f, at))) if *f == all => println!("executed represent: a frozen-context witness only, at {at} (every frozen site solved, its own release not): narrower scope; no witness found within this procedure and budget (stopped at {stop}); the best own: {solved} of {all}, at {label}; written to {out}"),
        _ => println!("executed represent: no witness found within this procedure and budget (stopped at {stop}); the best own: {solved} of {all}, at {label}; the best frozen: {:?}; written to {out}", best_frozen),
    }
    print_terms(&label, &batch, &targets);
    if found && let Some(held) = held_out {
        let pairs = terrain_pairs(terrain, &declared, held, count);
        let fresh = open_requests(&engine, &pairs);
        let fresh_targets: Vec<Vec<usize>> = pairs.iter().map(|(_, t)| t.clone()).collect();
        let read = compare(&engine.field, &theta_best, &fresh, &engine.refinement, &bank, BANK_GRAIN, Comparison::LOCK_DECISIONS)
            .expect("the held-out reading");
        summary(&format!("the witness on the held-out development seed {held} (its scope, read once)"), &theta_best, &read, &fresh_targets, declared.stations, 0);
    }
    println!("executed represent: stopped at {stop}; {} ms; resident {}", clock.elapsed().as_millis(), resident());
}

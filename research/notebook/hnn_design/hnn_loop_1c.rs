//! **Loop 1c's modes** (THE_REBUILD U6, step 1, loop 1c; the
//! [pin](../../records/2026-10-01_LOOP_1C_PERSISTENCE_REPRESENTATION_AND_REACH_PINNED_BEFORE_ITS_RUNS.md);
//! #73, #148, #63). Measurement only: every intervention is a diagnostic, never a law, and the
//! original native continuation (gate A's procedure, `executed witness`) is the baseline.
//!
//! ```sh
//! cargo run --release -p holonics --example hnn_prediction -- executed restore <label=state>…
//! cargo run --release -p holonics --example hnn_prediction -- executed replay <terrain> <seed> <count> <label=state|label=partial:file>…
//! cargo run --release -p holonics --example hnn_prediction -- executed coupling <terrain> <seed> <count> <deadline ms> <label=state|label=partial:file|label=opening>…
//! cargo run --release -p holonics --example hnn_prediction -- executed represent <terrain> <seed> <count> <iterates> <deadline ms> <out> [<held-out seed>]
//! ```
//!
//! **Fail-closed** (Astra's review of `722c3334`). Every arm is declared (`label=<state>`, a
//! complete continuing state restored whole; `label=partial:<file>`, a file of `E` and `ρ` alone,
//! the representation's witness, admitted only within its bounds; `label=opening`), and every arm
//! is restored before any is read: a complete state that does not parse, does not continue the
//! declared opening or does not write back to its own text refuses the run, never falling back to
//! a partial remount. A run stopped by its own deadline or past a pinned bound exits [`INCOMPLETE`],
//! a refused input [`REFUSED`], so the launcher (`loop_1c_runs.sh`) never reads either as success.
//!
//! - **`executed restore`** (the launcher's `check-replay`): each complete continuing state restored
//!   whole and written back against its file, no reading made.
//! - **`executed replay`** (the pin §1.1): each complete continuing state restored onto the
//!   declared opening (a full remount), written back and compared with its file, and read by the
//!   lock face at the decisions, printed in gate A's witness format (the summary line and every
//!   decision term whole) so a listing diffs against gate A's receipt; a declared partial arm (the
//!   witness's `E` and `ρ`, §9 falsifier 5) is read the same way and its admissibility printed or
//!   refused.
//! - **`executed coupling`** (the pin §2): per constitution, every request's release under the
//!   release's own order and the two declared diagnostic orders (`LockOrder`), every station read
//!   at its lock (solved at a refinement), at the actual release with every other lock placed
//!   (solved at the release), the decision term `d(j)` (gate A's count), the paired landing
//!   factorial (normalization × entry, `BankPlacement::storage_over`), and, for every native event
//!   (solved at its lock, not at the release), the lattice of its later locks, the singletons'
//!   factorial and the later locks entered at their targets; then every earlier constitution's
//!   solved station re-read in its own fixed context (retained after later releases). The events
//!   are admitted within the pinned bound ([`EVENT_BOUND`] events of at most [`LANDING_BOUND`]
//!   landings, the pin §6.2) before any is read; past it the constitution is refused incomplete.
//! - **`executed represent`** (the pin §3): the exterior fit, a search other than the candidate's
//!   own move. At each iterate every decision term's lock face and gradient
//!   (`executed::site_gradients`); the Gauss–Newton step of least norm placing every term above
//!   the level `(15/16) ln 2` at it, on the dyadic faces; projected onto the source port's lattice and
//!   the entry box, and certified exactly through the actual release (`executed::frozen_reread`:
//!   the own release, and the iterate's frozen decision sites beside it). Every certified
//!   admissible trial is read for the witness and the best; a trial is adopted when its own
//!   release's excess falls by disjoint enclosures. Every label (the witness, the frozen-context
//!   witness, the best) is granted only to an admissible reading, one guard for all ([`bounds`],
//!   [`certification`]). A representation diagnostic, never a learning result.
//!
//! Every unit prints one line with its elapsed milliseconds; the deadline is checked before each
//! unit, and a run past it stops, reported incomplete.

use super::executed_loop::{
    cell, founded_opening, open_requests, print_terms, solved_terms, terrain_pairs, write_state,
};
use super::*;
use holonics::hnn::HnnError;
use holonics::hnn::constitution::{ContinuingState, Locus};
use holonics::hnn::executed::{
    BatchComparison, Comparison, LockFace, Predicate, Reading, Request, TermSite, compare,
    entry_bound, frozen_reread, lock_face, site_gradients, sites_of,
};
use std::fmt;
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
// fail-closed: the exit statuses, the declared arms and the one admissibility guard

/// The exit status of a run stopped incomplete: its own deadline reached, or a pinned bound passed
/// before a unit was read (the pin §6.2, §6.4). Never a valid result, and never truncated into one.
pub(super) const INCOMPLETE: i32 = 3;
/// The exit status of a refused input: a checkpoint that does not restore whole or does not write
/// back to its own text, a witness file outside the representation's bounds (the pin §3.1), or a
/// reading the release refuses.
pub(super) const REFUSED: i32 = 4;

/// Stops the process with `status`, its reason on both streams (the listing and the launcher's log).
pub(super) fn stop(status: i32, reason: &str) -> ! {
    println!("{reason}");
    eprintln!("{reason}");
    std::process::exit(status)
}

/// **A declared arm's source** (module header): the founded opening, a complete continuing state
/// restored whole, or a file of `E` and `ρ` alone declared partial.
#[derive(Clone, Debug, PartialEq, Eq)]
enum Source {
    Opening,
    Complete(String),
    Partial(String),
}

/// `<label>=<source>`: `opening`, `partial:<file>`, or a complete continuing state's file. Nothing
/// is inferred from a file's contents: a complete state that fails to parse is refused, never read
/// as a partial remount.
fn arm(text: &str) -> Result<(String, Source), String> {
    let (label, source) = text
        .split_once('=')
        .ok_or_else(|| format!("the arm {text:?} is not <label>=<source>"))?;
    let source = match source {
        "opening" => Source::Opening,
        _ => match source.strip_prefix("partial:") {
            Some(path) => Source::Partial(path.to_string()),
            None => Source::Complete(source.to_string()),
        },
    };
    Ok((label.to_string(), source))
}

/// **A complete continuing state restored whole** onto the declared opening
/// (`Constitution::continued`) and written back: refused where the text is not a complete state,
/// where the state does not continue the declared opening, and where its write-back differs from
/// the text by a byte (the replay's item 3: a mismatch fails, it does not warn).
fn restore_whole(engine: &Engine, ring: usize, text: &str) -> Result<Constitution, String> {
    let state = ContinuingState::from_text(text)
        .map_err(|error| format!("not a complete continuing state ({error})"))?;
    let theta = engine
        .theta
        .clone()
        .continued(&state)
        .map_err(|error| format!("it does not continue the declared opening ({error})"))?;
    if write_state(&theta, ring) != text {
        return Err("the restored state written back differs from its file".to_string());
    }
    Ok(theta)
}

/// **A witness's `E` and `ρ` remounted** on the founded opening as the search built its trials
/// (`with_ports`, then `with_transport`, which refuses a modulus outside `(0, 1]` or off the
/// lattice): the file exactly `E rows cols`, its rows and `rho ρ`, nothing after them; refused off
/// that form and outside the representation's material bounds ([`bounds`]).
fn remount_partial(engine: &Engine, ring: usize, text: &str) -> Result<Constitution, String> {
    let mut lines = text.lines();
    let head: Vec<&str> = lines.next().unwrap_or("").split_whitespace().collect();
    let [ "E", rows, columns ] = head.as_slice() else {
        return Err("the first line is not `E rows columns`".to_string());
    };
    let (rows, columns): (usize, usize) = match (rows.parse(), columns.parse()) {
        (Ok(r), Ok(c)) => (r, c),
        _ => return Err("the port's shape does not parse".to_string()),
    };
    let mut port = Vec::with_capacity(rows);
    for row in 0..rows {
        let entries: Result<Vec<Rat>, _> = lines
            .next()
            .ok_or_else(|| format!("row {row} is missing"))?
            .split_whitespace()
            .map(str::parse::<Rat>)
            .collect();
        let entries = entries.map_err(|_| format!("row {row} does not parse"))?;
        if entries.len() != columns {
            return Err(format!("row {row} has {} entries, not {columns}", entries.len()));
        }
        port.push(entries);
    }
    let modulus: Rat = lines
        .next()
        .and_then(|line| line.strip_prefix("rho "))
        .and_then(|value| value.trim().parse().ok())
        .ok_or_else(|| "the line after the rows is not `rho ρ`".to_string())?;
    if lines.any(|line| !line.trim().is_empty()) {
        return Err("lines follow `rho`: not a file of E and ρ alone (a complete state is declared without `partial:`)".to_string());
    }
    let port = ExactRatMatrix::new(port).map_err(|error| format!("E: {error}"))?;
    let theta = founded_opening(engine)
        .with_ports(ring, None, Some(port), None)
        .map_err(|error| format!("E on the opening: {error}"))?
        .with_transport(ring, modulus)
        .map_err(|error| format!("ρ: {error}"))?;
    bounds(&theta, &founded_opening(engine), ring).map_err(|why| why.to_string())?;
    Ok(theta)
}

/// Every arm restored before any is read; the first refused arm stops the run ([`REFUSED`]).
fn restore_arms(mode: &str, engine: &Engine, ring: usize, arms: &[String]) -> Vec<(String, Source, Constitution)> {
    arms.iter()
        .map(|text| {
            let (label, source) = arm(text).unwrap_or_else(|why| stop(REFUSED, &format!("executed {mode}: refused: {why}")));
            let read = |path: &str| {
                #[allow(clippy::disallowed_methods)]
                std::fs::read_to_string(path)
                    .unwrap_or_else(|error| stop(REFUSED, &format!("executed {mode}: {label} ({path}) refused: unreadable ({error})")))
            };
            let theta = match &source {
                Source::Opening => founded_opening(engine),
                Source::Complete(path) => restore_whole(engine, ring, &read(path)).unwrap_or_else(|why| {
                    stop(REFUSED, &format!("executed {mode}: {label} ({path}) refused: {why}; a complete state is never read as a partial remount"))
                }),
                Source::Partial(path) => remount_partial(engine, ring, &read(path))
                    .unwrap_or_else(|why| stop(REFUSED, &format!("executed {mode}: {label} ({path}), declared partial, refused: {why}"))),
            };
            (label, source, theta)
        })
        .collect()
}

/// Why a reading is refused every label of the representation search (the pin §3.1).
#[derive(Clone, Debug, PartialEq, Eq)]
enum Inadmissible {
    Shape { expected: (usize, usize), found: (usize, usize) },
    EntryBound(Rat),
    OffLattice(Rat),
    Modulus(Rat),
    Budget { bits: u64, budget: u64 },
    Unreleased { request: usize },
    Uncertified { request: usize, station: usize, class: usize },
}

impl fmt::Display for Inadmissible {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Inadmissible::Shape { expected, found } => write!(f, "inadmissible: E is {found:?}, not the declared port's {expected:?}"),
            Inadmissible::EntryBound(x) => write!(f, "inadmissible: the entry {x} lies outside the entry box ±{}", entry_bound()),
            Inadmissible::OffLattice(x) => write!(f, "inadmissible: {x} lies off the source port's lattice"),
            Inadmissible::Modulus(x) => write!(f, "inadmissible: ρ {x} is not passive on the lattice"),
            Inadmissible::Budget { bits, budget } => write!(f, "inadmissible: exact bits {bits} past the budget {budget}"),
            Inadmissible::Unreleased { request } => write!(f, "inadmissible: request {request} has no release"),
            Inadmissible::Uncertified { request, station, class } => {
                write!(f, "inadmissible: request {request}'s lock of station {station} at class {class} has its Floquet certificate refused")
            }
        }
    }
}

/// **The representation's material bounds** (the pin §3.1): `E` of the declared port's shape, every
/// entry on the source port's lattice and in the entry box `[−2³, 2³]`; `ρ` on the lattice in
/// `(0, 1]`; the constitution's exact bits within its budget. Read on the constitution itself, so
/// a label never rests on how the search happened to project it.
fn bounds(theta: &Constitution, opening: &Constitution, ring: usize) -> Result<(), Inadmissible> {
    let lattice = opening.lattice(Locus::SourcePort(ring)).expect("the port's lattice");
    let declared = opening.source_port(ring).expect("the declared E");
    let port = theta.source_port(ring).expect("E");
    let (expected, found) = ((declared.rows(), declared.columns()), (port.rows(), port.columns()));
    if expected != found {
        return Err(Inadmissible::Shape { expected, found });
    }
    let bound = entry_bound();
    for x in port.entries() {
        if x.abs() > bound {
            return Err(Inadmissible::EntryBound(x.clone()));
        }
        if !lattice.contains(x) {
            return Err(Inadmissible::OffLattice(x.clone()));
        }
    }
    let modulus = theta.transport(ring);
    if !modulus.is_positive() || modulus > Rat::one() || !lattice.contains(&modulus) {
        return Err(Inadmissible::Modulus(modulus));
    }
    let (bits, budget) = (theta.exact_bits(), theta.budget());
    if bits > budget {
        return Err(Inadmissible::Budget { bits, budget });
    }
    Ok(())
}

/// **The reading's exact certification** (the pin §3.1): every request released by the actual
/// release (an inadmissible crossing refuses the reading before this guard is read) with every
/// lock's Floquet certificate certified.
fn certification(reading: &BatchComparison) -> Result<(), Inadmissible> {
    certification_of(reading.requests.iter().map(|r| r.generation.as_ref().map(|g| g.uncertified)))
}

/// [`certification`] on each request's release: absent, or the lock whose certificate was refused.
fn certification_of(releases: impl IntoIterator<Item = Option<Option<(usize, usize)>>>) -> Result<(), Inadmissible> {
    for (request, release) in releases.into_iter().enumerate() {
        match release {
            None => return Err(Inadmissible::Unreleased { request }),
            Some(Some((station, class))) => return Err(Inadmissible::Uncertified { request, station, class }),
            Some(None) => {}
        }
    }
    Ok(())
}

/// The search's verdict (the pin §3.3).
#[derive(Clone, Debug, PartialEq, Eq)]
enum Verdict {
    Witness(String),
    FrozenOnly(String),
    None,
}

/// **The search's labels** (the pin §3.3), each granted only to an admissible reading
/// ([`bounds`] and [`certification`]): the all-64 witness and the frozen-context witness under one
/// guard (Astra's review of `722c3334`: the frozen label had none).
#[derive(Default)]
struct Labels {
    witness: Option<String>,
    frozen: Option<(usize, String)>,
}

impl Labels {
    /// A reading at `at`: its own release's solved terms and, for a trial, its frozen sites solved.
    fn read(&mut self, at: &str, admissible: &Result<(), Inadmissible>, own: usize, frozen: Option<usize>, all: usize) {
        if admissible.is_err() {
            return;
        }
        if own == all && self.witness.is_none() {
            self.witness = Some(at.to_string());
        }
        if let Some(f) = frozen
            && self.frozen.as_ref().is_none_or(|(best, _)| f > *best)
        {
            self.frozen = Some((f, at.to_string()));
        }
    }

    fn verdict(&self, all: usize) -> Verdict {
        match (&self.witness, &self.frozen) {
            (Some(at), _) => Verdict::Witness(at.clone()),
            (None, Some((f, at))) if *f == all => Verdict::FrozenOnly(at.clone()),
            _ => Verdict::None,
        }
    }
}

// -------------------------------------------------------------------------------------------
// the restore check and the replay

/// **The restore check** (module header; the launcher's `check-replay`): each complete continuing
/// state restored whole onto the declared opening and written back against its file, no reading
/// made. A partial or opening arm is refused here: this check reads complete states only.
pub(super) fn restore(arms: &[String]) {
    let clock = Instant::now();
    let engine = Engine::new(order_declared());
    let ring = engine.refinement.ring();
    for text in arms {
        if !matches!(arm(text), Ok((_, Source::Complete(_)))) {
            stop(REFUSED, &format!("executed restore: refused: {text:?} is not <label>=<complete state>"));
        }
    }
    for (label, source, _) in restore_arms("restore", &engine, ring, arms) {
        let Source::Complete(path) = source else { unreachable!("checked above") };
        println!("restore {label}: {path} restored whole onto the declared opening; written back identical to its file");
    }
    println!("executed restore: {} states; {} ms", arms.len(), clock.elapsed().as_millis());
}

/// **The exact replay of written states** (module header).
pub(super) fn replay(terrain: &str, seed: u64, count: usize, arms: &[String]) {
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
    let opening = founded_opening(&engine);
    for (label, source, theta) in restore_arms("replay", &engine, ring, arms) {
        let started = Instant::now();
        let batch = compare(
            &engine.field,
            &theta,
            &requests,
            &engine.refinement,
            &bank,
            BANK_GRAIN,
            Comparison::LOCK_DECISIONS,
        )
        .unwrap_or_else(|error| stop(REFUSED, &format!("executed replay: {label}: the reading refused ({error})")));
        let (solved, all) = summary(&label, &theta, &batch, &targets, declared.stations, started.elapsed().as_millis());
        print_terms(&label, &batch, &targets);
        match source {
            Source::Complete(_) => eprintln!("replay {label}: the restored state written back is identical to its file"),
            Source::Partial(_) => {
                // §9 falsifier 5: a witness read afresh must be admissible, certified exactly.
                match bounds(&theta, &opening, ring).and_then(|()| certification(&batch)) {
                    Ok(()) => println!(
                        "  {label}: admissible as a representation (the pin §3.1): E on the lattice within ±{}, ρ {} passive on the lattice, exact bits {} within the budget {}, every request released with every lock certified; solved {solved} of {all}",
                        entry_bound(),
                        theta.transport(ring),
                        theta.exact_bits(),
                        theta.budget()
                    ),
                    Err(why) => stop(REFUSED, &format!("executed replay: {label}, declared partial, refused: {why}")),
                }
            }
            Source::Opening => {}
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

/// [definition; the pin §6.2] **The coupling's event bound**: at most 6 native events a constitution
/// (gate A's persistence tuples have at most 6 falls at any constitution 0–15, and constitution 16
/// is held to the same bound), each of at most 7 landings. The projection of `exp-coupling` (its
/// unit upper `⌈95,349 · 7,200/6,840 + (17,667/2,865) · (4,290 + 640k)⌉` ms) holds only within it.
const EVENT_BOUND: usize = 6;
const LANDING_BOUND: usize = 7;

/// A native event (the pin §2.3): a station solved at its lock and not at the release, with a later
/// lock; its landings the co-locked stations and the later locks, ascending.
#[derive(Clone, Debug, PartialEq, Eq)]
struct Event {
    request: usize,
    station: usize,
    landings: Vec<usize>,
}

/// A constitution's events past the pinned bound.
#[derive(Clone, Debug, PartialEq, Eq)]
enum EventOverflow {
    Events(usize),
    Landings { request: usize, station: usize, landings: usize },
}

impl fmt::Display for EventOverflow {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            EventOverflow::Events(n) => write!(f, "{n} native events, past the pinned bound of {EVENT_BOUND}"),
            EventOverflow::Landings { request, station, landings } => write!(
                f,
                "the event at request {request} station {station} has {landings} landings, past the pinned bound of {LANDING_BOUND}"
            ),
        }
    }
}

/// **The native events of a constitution, admitted before any is read**: every request's stations
/// on the native order, counted whole first; past [`EVENT_BOUND`] events, or an event past
/// [`LANDING_BOUND`] landings, the constitution is refused (the caller stops the run incomplete),
/// never truncated to the first six.
fn native_events<'a>(natives: impl IntoIterator<Item = &'a [Station]>) -> Result<Vec<Event>, EventOverflow> {
    let mut events = Vec::new();
    for (request, stations) in natives.into_iter().enumerate() {
        for (station, s) in stations.iter().enumerate() {
            if s.lock.is_none() || !s.at_lock.holds() || s.at_release.holds() || s.later.is_empty() {
                continue;
            }
            let mut landings: Vec<usize> = s.co.iter().chain(&s.later).copied().collect();
            landings.sort_unstable();
            events.push(Event { request, station, landings });
        }
    }
    if events.len() > EVENT_BOUND {
        return Err(EventOverflow::Events(events.len()));
    }
    if let Some(e) = events.iter().find(|e| e.landings.len() > LANDING_BOUND) {
        return Err(EventOverflow::Landings { request: e.request, station: e.station, landings: e.landings.len() });
    }
    Ok(events)
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
    // Every arm restored before any constitution is read (the replay's item 3): a complete state
    // whole and written back against its file, a declared partial within the representation's
    // bounds; the first refused arm stops the run before any reading.
    let restored = restore_arms("coupling", &engine, ring, arms);
    for (index, (label, source, theta)) in restored.into_iter().enumerate() {
        if clock.elapsed().as_millis() > deadline {
            println!("executed coupling: the deadline, before constitution {index} (incomplete)");
            println!(
                "executed coupling: {} readings; {} ms; resident {}",
                READINGS.load(Ordering::Relaxed),
                clock.elapsed().as_millis(),
                resident()
            );
            stop(INCOMPLETE, &format!("executed coupling: stopped incomplete at its deadline {deadline} ms, before constitution {index}"));
        }
        let started = Instant::now();
        let start_readings = READINGS.load(Ordering::Relaxed);
        match source {
            Source::Complete(_) => println!("constitution {label}: the restored state written back is identical to its file"),
            Source::Partial(_) => println!(
                "constitution {label}: E and ρ alone, a declared partial remount within the representation's bounds (a representation diagnostic)"
            ),
            Source::Opening => {}
        }
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
        // The native events: solved at the lock, not at the release; admitted within the pinned
        // bound before any is read, or the constitution is refused incomplete (never truncated).
        let lattice_started = Instant::now();
        let lattice_readings = READINGS.load(Ordering::Relaxed);
        let admitted = native_events(natives.iter().map(|native| native.stations.as_slice()))
            .unwrap_or_else(|overflow| {
                stop(
                    INCOMPLETE,
                    &format!(
                        "executed coupling: constitution {label}: {overflow}; refused as incomplete before any of its events is read (the pin §6.2's projection holds only within the bound); {} ms",
                        clock.elapsed().as_millis()
                    ),
                )
            });
        let events = admitted.len();
        for Event { request: q, station: j, landings: later } in admitted {
            {
                let s = &natives[q].stations[j];
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
    // The witness's criterion is every declared decision term (a station of a request), never
    // only those a reading happened to make.
    let declared_all = declared.stations * count;
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
    // Every label is granted only to an admissible reading (`bounds` and `certification`); the
    // best is the most solved of them, the earliest among equals.
    let mut best: Option<(usize, String, Constitution, BatchComparison)> = None;
    let mut labels = Labels::default();
    let mut stopped = "the iterates are spent".to_string();
    let mut incomplete = false;
    for index in 0..iterates {
        if clock.elapsed().as_millis() > deadline {
            stopped = format!("the deadline, before iterate {index} (incomplete)");
            incomplete = true;
            break;
        }
        let started = Instant::now();
        let (batch, gradients) = site_gradients(&engine.field, &theta, &requests, &engine.refinement, &bank, BANK_GRAIN)
            .expect("the iterate's readings");
        let read_ms = started.elapsed().as_millis();
        let label = format!("iterate {index}");
        let (solved, all) = summary(&label, &theta, &batch, &targets, declared.stations, read_ms);
        let admissible = bounds(&theta, &opening, ring).and_then(|()| certification(&batch));
        if let Err(why) = &admissible {
            println!("    {label}: {why}; no label is granted to it");
        }
        if admissible.is_ok() && best.as_ref().is_none_or(|(s, ..)| solved > *s) {
            best = Some((solved, label.clone(), theta.clone(), batch.clone()));
        }
        labels.read(&label, &admissible, solved, None, declared_all);
        if labels.witness.is_some() {
            stopped = format!("a witness at iterate {index}");
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
            stopped = format!("iterate {index}: no active term has a resolved gradient ({omitted} omitted)");
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
            let (s, _) = solved_terms(&own);
            let f = frozen.iter().flatten().filter(|t| t.comparison.solved == Predicate::Holds).count();
            let (whole, right, released) = own.sections(&targets);
            // Every trial is read for the labels under the one guard ([`bounds`] on the successor
            // itself and [`certification`] of its own release); the adoption reads the own
            // release's excess strictly lower by disjoint enclosures, admissible trials only.
            let admissible = bounds(&successor, &opening, ring).and_then(|()| certification(&own));
            let at = format!("iterate {index}, trial {trial}");
            labels.read(&at, &admissible, s, Some(f), declared_all);
            let witness = admissible.is_ok() && s == declared_all;
            let better = admissible.is_ok() && own.excess.upper < batch.excess.lower;
            println!(
                "      trial {trial}: η {step}: own solved {s} of {all}, frozen sites solved {f} of {all} ({made} frozen readings made); X ∈ {} nats; released {released}, whole {whole}, stations right {right}; exact bits {bits}{}; {}; {} ms",
                cell(&own.excess, 1 << 12),
                match &admissible {
                    Ok(()) => String::new(),
                    Err(why) => format!("; {why}"),
                },
                if witness { "a witness" } else if better { "adopted" } else { "not adopted" },
                trial_started.elapsed().as_millis()
            );
            if admissible.is_ok() && best.as_ref().is_none_or(|(b, ..)| s > *b) {
                best = Some((s, at, successor.clone(), own.clone()));
            }
            if witness {
                stopped = format!("a witness at iterate {index}, trial {trial}");
            }
            if witness || better {
                adopted = Some(successor);
                break;
            }
            step /= Rat::from_integer(2.into());
        }
        match adopted {
            Some(_) if labels.witness.is_some() => break,
            Some(successor) => theta = successor,
            None => {
                stopped = format!("iterate {index}: no trial adopted (the set is fixed: the next iterate would repeat it)");
                break;
            }
        }
        println!("    iterate {index}: {} ms", started.elapsed().as_millis());
        if index + 1 == iterates {
            let last = compare(&engine.field, &theta, &requests, &engine.refinement, &bank, BANK_GRAIN, Comparison::LOCK_DECISIONS)
                .expect("the last iterate's reading");
            let label = format!("iterate {} (after the last step)", index + 1);
            let (solved, _) = summary(&label, &theta, &last, &targets, declared.stations, 0);
            let admissible = bounds(&theta, &opening, ring).and_then(|()| certification(&last));
            if let Err(why) = &admissible {
                println!("    {label}: {why}; no label is granted to it");
            }
            if admissible.is_ok() && best.as_ref().is_none_or(|(s, ..)| solved > *s) {
                best = Some((solved, label.clone(), theta.clone(), last.clone()));
            }
            labels.read(&label, &admissible, solved, None, declared_all);
            if labels.witness.is_some() {
                stopped = "a witness after the last step".to_string();
            }
        }
    }
    let all = declared_all;
    let verdict = labels.verdict(all);
    let Some((solved, label, theta_best, batch)) = best else {
        println!("executed represent: no witness found within this procedure and budget (stopped at {stopped}); no admissible reading, so nothing is written to {out}");
        println!("executed represent: stopped at {stopped}; {} ms; resident {}", clock.elapsed().as_millis(), resident());
        if incomplete {
            stop(INCOMPLETE, &format!("executed represent: stopped incomplete at its deadline {deadline} ms"));
        }
        return;
    };
    let port = theta_best.source_port(ring).expect("E");
    let mut text = format!("E {} {}\n", port.rows(), port.columns());
    for r in 0..port.rows() {
        text += &(0..port.columns()).map(|c| port.get(r, c).expect("entry").to_string()).collect::<Vec<_>>().join(" ");
        text.push('\n');
    }
    text += &format!("rho {}\n", theta_best.transport(ring));
    #[allow(clippy::disallowed_methods)]
    std::fs::write(out, text).expect("write the best");
    match &verdict {
        Verdict::Witness(_) => println!("executed represent: a witness FOUND at {label}: the strict test holds at all {all} decision terms of its own release; E and ρ written to {out} (a representation diagnostic, not a learning result)"),
        Verdict::FrozenOnly(at) => println!("executed represent: a frozen-context witness only, at {at} (every frozen site solved, its own release not; admissible and certified): narrower scope; no witness found within this procedure and budget (stopped at {stopped}); the best own: {solved} of {all}, at {label}; written to {out}"),
        Verdict::None => println!("executed represent: no witness found within this procedure and budget (stopped at {stopped}); the best own: {solved} of {all}, at {label}; the best frozen (admissible trials): {:?}; written to {out}", labels.frozen),
    }
    print_terms(&label, &batch, &targets);
    if matches!(verdict, Verdict::Witness(_)) && let Some(held) = held_out {
        let pairs = terrain_pairs(terrain, &declared, held, count);
        let fresh = open_requests(&engine, &pairs);
        let fresh_targets: Vec<Vec<usize>> = pairs.iter().map(|(_, t)| t.clone()).collect();
        let read = compare(&engine.field, &theta_best, &fresh, &engine.refinement, &bank, BANK_GRAIN, Comparison::LOCK_DECISIONS)
            .expect("the held-out reading");
        summary(&format!("the witness on the held-out development seed {held} (its scope, read once)"), &theta_best, &read, &fresh_targets, declared.stations, 0);
    }
    println!("executed represent: stopped at {stopped}; {} ms; resident {}", clock.elapsed().as_millis(), resident());
    if incomplete {
        stop(INCOMPLETE, &format!("executed represent: stopped incomplete at its deadline {deadline} ms"));
    }
}

// -------------------------------------------------------------------------------------------
// the fail-closed repairs' negative tests (Astra's review of `722c3334`), each with its positive
// control: `cargo test -p holonics --example hnn_prediction`

#[cfg(test)]
mod tests {
    use super::*;

    /// Gate A's saved complete continuing state (constitution 1 of its native continuation).
    fn gate_a_state() -> String {
        let path = concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/../../research/records/2026-09-30_STEP_1B_GATE_A_receipts/witness_best.state"
        );
        #[allow(clippy::disallowed_methods)]
        std::fs::read_to_string(path).expect("gate A's saved state")
    }

    fn face(solved: Predicate) -> Face {
        let zero = ExactInterval::point(Rat::zero());
        Face::Read(LockFace { value: zero.clone(), solved, above: false, shares: Vec::new(), excess: zero })
    }

    /// A locked station solved at its lock; an event when the release's re-read does not hold.
    fn station(event: bool, later: Vec<usize>) -> Station {
        Station {
            lock: Some((0, 1)),
            co: Vec::new(),
            later,
            decision: Vec::new(),
            released: Vec::new(),
            at_lock: face(Predicate::Holds),
            at_release: face(if event { Predicate::Fails } else { Predicate::Holds }),
            normalization: None,
            entry: None,
        }
    }

    /// Eight requests whose stations hold `events` native events between them, one a request.
    fn requests_with(events: usize) -> Vec<Vec<Station>> {
        (0..8)
            .map(|q| (0..8).map(|j| station(j == 0 && q < events, vec![1, 2])).collect())
            .collect()
    }

    #[test]
    fn a_seventh_coupling_event_refuses_the_constitution_as_incomplete() {
        // Six events (the pinned bound) are admitted whole.
        let six = requests_with(6);
        let admitted = native_events(six.iter().map(Vec::as_slice)).expect("six events within the bound");
        assert_eq!(admitted.len(), EVENT_BOUND);
        assert_eq!(admitted[0], Event { request: 0, station: 0, landings: vec![1, 2] });
        // A seventh is refused before any is read: never truncated to the first six.
        let seven = requests_with(7);
        assert_eq!(native_events(seven.iter().map(Vec::as_slice)), Err(EventOverflow::Events(7)));
        // An event past seven landings is refused too (the bound is events of at most 7 landings).
        let mut wide = requests_with(1);
        wide[0][0] = station(true, (1..9).collect());
        assert_eq!(
            native_events(wide.iter().map(Vec::as_slice)),
            Err(EventOverflow::Landings { request: 0, station: 0, landings: 8 })
        );
        // An undecided re-read at the release is an event as a failing one is.
        let mut undecided = requests_with(6);
        undecided[7][3].at_release = face(Predicate::Undecided);
        assert_eq!(native_events(undecided.iter().map(Vec::as_slice)), Err(EventOverflow::Events(7)));
    }

    #[test]
    fn a_malformed_full_checkpoint_is_refused_never_remounted_partially() {
        let engine = Engine::new(order_declared());
        let ring = engine.refinement.ring();
        let text = gate_a_state();
        // Positive control: the saved state restores whole and writes back to its own text.
        assert!(restore_whole(&engine, ring, &text).is_ok());
        // Truncated after `rho`: E and ρ intact, the rest of the state gone.
        let rho = text.lines().position(|line| line.starts_with("rho ")).expect("rho");
        let truncated: String = text.lines().take(rho + 1).map(|line| format!("{line}\n")).collect();
        let refused = restore_whole(&engine, ring, &truncated).expect_err("a truncated state is refused");
        assert!(refused.contains("not a complete continuing state"), "{refused}");
        // The hazard repaired: the same text read as E and ρ alone would remount (the earlier
        // harness's silent fallback); it does so now only when declared `partial:`.
        assert!(remount_partial(&engine, ring, &truncated).is_ok());
        assert_eq!(arm("3=c3.state"), Ok(("3".to_string(), Source::Complete("c3.state".to_string()))));
        assert_eq!(arm("w=partial:best.txt"), Ok(("w".to_string(), Source::Partial("best.txt".to_string()))));
        // A complete state is never read as a partial: `partial:` refuses lines after `rho`.
        assert!(remount_partial(&engine, ring, &text).is_err());
        // A value off its written form after `rho` (the clock `01`): parses to the same state, but
        // does not write back to its own text.
        let edited = text.replace("\nclock ", "\nclock 0");
        assert_ne!(edited, text);
        assert!(ContinuingState::from_text(&edited).is_ok());
        let refused = restore_whole(&engine, ring, &edited).expect_err("a state off its written form is refused");
        assert!(refused.contains("written back differs"), "{refused}");
        // A broken line after `rho` (the Gram's head): the state does not parse.
        let broken = text.replace("\ngram 5\n", "\ngram five\n");
        assert_ne!(broken, text);
        assert!(restore_whole(&engine, ring, &broken).is_err());
        // A trailing line after `end`: parses, but its write-back differs by those bytes.
        let trailing = format!("{text}extra\n");
        let refused = restore_whole(&engine, ring, &trailing).expect_err("a trailing line is refused");
        assert!(refused.contains("written back differs"), "{refused}");
    }

    #[test]
    fn an_inadmissible_frozen_context_witness_is_refused_the_label() {
        let engine = Engine::new(order_declared());
        let ring = engine.refinement.ring();
        let opening = founded_opening(&engine);
        let all = 64;
        let certified = || certification_of(vec![Some(None); 8]);
        // Positive control: an admissible trial solving every frozen site, not its own release,
        // is the frozen-context witness.
        let admissible = bounds(&opening, &opening, ring).and_then(|()| certified());
        assert_eq!(admissible, Ok(()));
        let mut labels = Labels::default();
        labels.read("admissible", &admissible, 10, Some(all), all);
        assert_eq!(labels.verdict(all), Verdict::FrozenOnly("admissible".to_string()));
        // The same reading at constitutions outside the bounds, or uncertified, is refused it.
        let port = opening.source_port(ring).expect("E").clone();
        let entry = |r: usize, c: usize, value: &Rat| if (r, c) == (0, 0) { value.clone() } else { port.get(r, c).expect("entry").clone() };
        let with_entry = |value: Rat| {
            let rows: Vec<Vec<Rat>> = (0..port.rows()).map(|r| (0..port.columns()).map(|c| entry(r, c, &value)).collect()).collect();
            opening.clone().with_ports(ring, None, Some(ExactRatMatrix::new(rows).expect("E")), None).expect("E on the opening")
        };
        let past = with_entry(Rat::from_integer(9.into()));
        let off = with_entry(Rat::new(BigInt::one(), BigInt::one() << 40usize));
        let refusals = [
            bounds(&past, &opening, ring),
            bounds(&off, &opening, ring),
            bounds(&opening, &opening, ring).and_then(|()| certification_of(vec![Some(None), Some(Some((3, 1)))])),
            bounds(&opening, &opening, ring).and_then(|()| certification_of(vec![Some(None), None])),
        ];
        assert!(matches!(refusals[0], Err(Inadmissible::EntryBound(_))));
        assert!(matches!(refusals[1], Err(Inadmissible::OffLattice(_))));
        assert_eq!(refusals[2], Err(Inadmissible::Uncertified { request: 1, station: 3, class: 1 }));
        assert_eq!(refusals[3], Err(Inadmissible::Unreleased { request: 1 }));
        for refused in &refusals {
            let mut labels = Labels::default();
            labels.read("inadmissible", refused, 10, Some(all), all);
            assert_eq!(labels.verdict(all), Verdict::None, "{refused:?}");
            // The all-64 witness is held to the same guard.
            labels.read("inadmissible", refused, all, Some(all), all);
            assert_eq!(labels.verdict(all), Verdict::None, "{refused:?}");
        }
        // A file of E and ρ past the entry bound is refused as a declared partial too.
        let mut text = format!("E {} {}\n", port.rows(), port.columns());
        let nine = Rat::from_integer(9.into());
        for r in 0..port.rows() {
            let row: Vec<String> = (0..port.columns()).map(|c| entry(r, c, &nine).to_string()).collect();
            text += &(row.join(" ") + "\n");
        }
        text += &format!("rho {}\n", opening.transport(ring));
        let refused = remount_partial(&engine, ring, &text).expect_err("past the entry bound");
        assert!(refused.contains("entry box"), "{refused}");
    }
}

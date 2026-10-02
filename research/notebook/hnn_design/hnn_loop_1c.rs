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
//! cargo run --release -p holonics --example hnn_prediction -- executed resume-coupling <terrain> <seed> <count> <c1 state> <gate A receipt> <move bound ms> <capture dir>
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
//! - **`executed resume-coupling`** (the c2 diagnostic; the primary's brief, narrowed by Astra's
//!   review of the c2 consumer): gate A's saved constitution 1 restored whole (refused, exit
//!   [`REFUSED`], never remounted partially), and one native update through the owner
//!   (`hnn::executed::executed_move`, the lock face at the decisions, every commit guard) on the
//!   batch gate A's move 1 read; past its bound the move stops the run then, incomplete ([`Watch`]).
//!   Nothing after the move is re-released: the move's own reading of its adopted successor (the
//!   trial's release) supplies constitution 2's summary, every lock's context at its own lock with
//!   its lock face, and the terminal assignment ([`locks_of`]). Constitution 2's complete state and
//!   those contexts are written ([`capture`]) before any diagnostic read. Then, each gated by the one
//!   before ([`resumed`]): the move's lines and constitution 2's reading equal gate A's receipt, and
//!   the persistence reads' locks, solved and re-reads (no reading); the re-reads, lost and
//!   retained, admitted within [`REREAD_BOUND`]; each re-read at the release (`N1D1`), whose stay
//!   and fall must be gate A's (else exit [`MISMATCH`], nothing further read); then its
//!   normalization alone and entry alone (`N1D0`, `N0D1`), with the contrasts in both orders and the
//!   interaction. The native order only; Fails, Undecided and refusals apart everywhere.
//!
//! Every unit prints one line with its elapsed milliseconds; the deadline is checked before each
//! unit, and a run past it stops, reported incomplete.

use super::executed_loop::{
    cell, founded_opening, move_line, open_requests, print_terms, solved_terms, terrain_pairs,
    write_state,
};
use super::*;
use holonics::hnn::HnnError;
use holonics::hnn::constitution::{ContinuingState, Locus};
use holonics::hnn::executed::{
    BatchComparison, Comparison, LockFace, Predicate, Reading, Request, RequestComparison, TermSite,
    compare, entry_bound, executed_move, frozen_reread, lock_face, site_gradients, sites_of,
};
use std::fmt;
use std::sync::{OnceLock, mpsc};
use std::time::Duration;
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
    let (line, solved, all) = summary_line(label, theta, batch, targets, stations, ms);
    println!("{line}");
    (solved, all)
}

/// [`summary`]'s line, with the solved decision terms and those read.
fn summary_line(label: &str, theta: &Constitution, batch: &BatchComparison, targets: &[Vec<usize>], stations: usize, ms: u128) -> (String, usize, usize) {
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
    let line = format!(
        "  {label}: solved {solved} of {all} decision terms; whole sections {whole} of {} (released {released}, stations right {right}); L ∈ {} nats, X ∈ {} nats; E's largest entry {}, ρ {}; the terms {:?}; {ms} ms",
        targets.len(),
        cell(&batch.value, 1 << 12),
        cell(&batch.excess, 1 << 12),
        largest,
        theta.transport(ring),
        batch.counts(stations)
    );
    (line, solved, all)
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

/// A lock face read at a section with its station open, or the typed refusal of the reading; or
/// one the release already read and kept (`Kept`: its `ℓ` enclosure and solved predicate, from the
/// owner's receipt of the refinement that locked the station, reused rather than read again).
#[derive(Clone, Debug)]
enum Face {
    Read(LockFace),
    Kept { value: ExactInterval, solved: Predicate },
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
            Face::Kept { solved, .. } => Some(*solved),
            Face::Refused(_) => None,
        }
    }

    fn holds(&self) -> bool {
        self.solved() == Some(Predicate::Holds)
    }

    fn lock(&self) -> Option<&ExactInterval> {
        match self {
            Face::Read(face) => Some(&face.value),
            Face::Kept { value, .. } => Some(value),
            Face::Refused(_) => None,
        }
    }

    fn show(&self) -> String {
        match self {
            Face::Read(face) => format!("{} ℓ {}", mark(face.solved), cell(&face.value, 1 << 16)),
            Face::Kept { value, solved } => format!("{} ℓ {}", mark(*solved), cell(value, 1 << 16)),
            Face::Refused(why) => format!("refused ({why})"),
        }
    }

    /// The face's mark: `H`, `F`, `U`, or `R` (refused); Fails and Undecided never pooled.
    fn mark(&self) -> &'static str {
        self.solved().map_or("R", mark)
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
    contrasts_of(&row.at_lock, row.normalization.as_ref()?, row.entry.as_ref()?, &row.at_release)
}

/// [`contrasts`] on the four cells `N0D0, N1D0, N0D1, N1D1`.
fn contrasts_of(n0d0: &Face, n1d0: &Face, n0d1: &Face, n1d1: &Face) -> Option<String> {
    let (l00, l11) = (n0d0.lock()?, n1d1.lock()?);
    let l10 = n1d0.lock()?;
    let l01 = n0d1.lock()?;
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

/// [definition; agent-inferred, October 2] **The exterior fit's step sizes**: at most 8 a trial,
/// halving from its first. A declared bound on an exterior search's work, recorded with its runs
/// (`hnn_loop_1c`'s receipts); it is not the machine's move, whose halvings end at the lattice's
/// resolution (`hnn::executed`).
const REFIT_HALVINGS: usize = 8;

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
        REFIT_HALVINGS,
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
        for trial in 0..REFIT_HALVINGS {
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
// the c2 diagnostic: one native update resumed from gate A's saved constitution 1, then the native
// release's re-reads at constitution 2 (narrowed by Astra's review of the c2 consumer)

/// The exit status of an identity mismatch: the resumed move's lines, its successor's reading or the
/// persistence reads at the successor differ from gate A's receipt. Every read after it is withheld.
pub(super) const MISMATCH: i32 = 5;

/// [definition; the primary's c2 brief and Astra's review of the c2 consumer] **The re-reads
/// admitted at constitution 2**: gate A's persistence reads there (its move 2 line) re-read 7 solved
/// locks with a later lock, 4 staying solved and 3 not. Every re-read, lost and retained alike, is
/// counted before any is read; past the bound the run is refused incomplete, never truncated.
const REREAD_BOUND: usize = 7;

/// The receipt's lines the identity reads: constitution 1's summary and move 1's line (the move's
/// own printed lines), constitution 2's summary, and move 2's line, whose persistence reads are the
/// owner's at constitution 2.
const RECEIPT_C1: &str = "  constitution 1 (before move 1): ";
const RECEIPT_MOVE_1: &str = "    move 1: ";
const RECEIPT_C2: &str = "  constitution 2 (before move 2): ";
const RECEIPT_MOVE_2: &str = "    move 2: ";

/// The owner's persistence fields gate A printed (`hnn::executed::Persistence` before the split of
/// Astra's review of October 1, which is compared wherever a receipt carries it).
const TUPLE: [&str; 5] = ["locks", "solved", "reread", "stay", "fall"];

/// **A unit's early stop** (CLAUDE.md, "Stop early on evidence"): a guard thread that calls
/// `expired` when the unit has not ended within its bound, so a unit past its projection's upper
/// bound stops the run then, not at the outer guard; ended in time, it calls nothing.
struct Watch {
    ended: Option<mpsc::Sender<()>>,
    guard: Option<std::thread::JoinHandle<()>>,
}

impl Watch {
    fn start(bound: Duration, expired: impl FnOnce() + Send + 'static) -> Self {
        let (ended, waiting) = mpsc::channel::<()>();
        let guard = std::thread::spawn(move || {
            if matches!(waiting.recv_timeout(bound), Err(mpsc::RecvTimeoutError::Timeout)) {
                expired();
            }
        });
        Watch { ended: Some(ended), guard: Some(guard) }
    }

    /// The unit ended: the guard returns without calling `expired`, unless the bound had passed.
    fn end(mut self) {
        drop(self.ended.take());
        if let Some(guard) = self.guard.take() {
            let _ = guard.join();
        }
    }
}

/// A printed line as the identity compares it: the wall time `; <n> ms` at its end removed, and the
/// persistence split `, reversed: <n>, uncertified: <n>` (which gate A's receipt predates) removed
/// wherever printed. Nothing else is masked.
fn masked(line: &str) -> String {
    let mut text = line.to_string();
    let mut from = 0;
    while let Some(found) = text[from..].find(", reversed: ") {
        let at = from + found;
        let after = at + ", reversed: ".len();
        let digits = text[after..].chars().take_while(char::is_ascii_digit).count();
        let tail = after + digits;
        let Some(rest) = text[tail..].strip_prefix(", uncertified: ") else {
            from = after;
            continue;
        };
        let more = rest.chars().take_while(char::is_ascii_digit).count();
        if digits == 0 || more == 0 {
            from = after;
            continue;
        }
        let end = tail + ", uncertified: ".len() + more;
        text.replace_range(at..end, "");
        from = at;
    }
    if let Some(at) = text.rfind("; ")
        && let Some(n) = text[at + 2..].strip_suffix(" ms")
        && !n.is_empty()
        && n.chars().all(|c| c.is_ascii_digit())
    {
        text.truncate(at);
    }
    text
}

/// A printed `Persistence { … }`'s fields by name.
fn persistence_fields(line: &str) -> Option<BTreeMap<String, usize>> {
    let body = line.split_once("Persistence { ")?.1.split_once(" }")?.0;
    body.split(", ")
        .map(|field| {
            let (name, value) = field.split_once(": ")?;
            Some((name.to_string(), value.parse().ok()?))
        })
        .collect()
}

/// **Gate A's receipt of move 1 and of constitution 2** (`witness.txt`), read before the move: the
/// move's two printed lines, constitution 2's summary line, and the owner's persistence reads at
/// constitution 2 (move 2's line), by field. Each line found exactly once, or refused.
#[derive(Clone, Debug, PartialEq, Eq)]
struct Receipt {
    moved: [String; 2],
    successor: String,
    persistence: BTreeMap<String, usize>,
}

impl Receipt {
    fn read(text: &str) -> Result<Self, String> {
        let line = |prefix: &str| -> Result<String, String> {
            let mut found = text.lines().filter(|line| line.starts_with(prefix));
            let first = found
                .next()
                .ok_or_else(|| format!("gate A's receipt has no line `{}…`", prefix.trim_start()))?;
            if found.next().is_some() {
                return Err(format!("gate A's receipt has more than one line `{}…`", prefix.trim_start()));
            }
            Ok(first.to_string())
        };
        let moved = [line(RECEIPT_C1)?, line(RECEIPT_MOVE_1)?];
        let successor = line(RECEIPT_C2)?;
        let persistence = persistence_fields(&line(RECEIPT_MOVE_2)?)
            .ok_or_else(|| "gate A's move 2 line: its persistence reads do not parse".to_string())?;
        if let Some(field) = TUPLE.iter().find(|field| !persistence.contains_key(**field)) {
            return Err(format!("gate A's move 2 line: its persistence reads have no `{field}`"));
        }
        Ok(Self { moved, successor, persistence })
    }
}

/// **The resumed read's inputs, each refused before the move**: gate A's receipt ([`Receipt::read`])
/// and gate A's saved constitution 1 restored whole ([`restore_whole`]: a state that does not parse,
/// does not continue the declared opening or does not write back to its own text is refused, never
/// remounted partially).
fn resume_inputs(engine: &Engine, ring: usize, state: &str, receipt: &str) -> Result<(Constitution, Receipt), String> {
    let receipt = Receipt::read(receipt)?;
    let theta = restore_whole(engine, ring, state)
        .map_err(|why| format!("constitution 1 refused: {why}; a complete state is never read as a partial remount"))?;
    Ok((theta, receipt))
}

/// **The persistence reads at constitution 2, every status apart** (the owner's
/// `hnn::executed::Persistence`, read by its rule): the native release's locks, those solved at their
/// own lock, those of them with a later lock (the re-reads), and of the re-reads at the release:
/// solved (`stay`), the strict test failing (`reversed`), undecided (`uncertified`), or the reading
/// refused (`refused`, which the owner's read never returns). `fall` is reversed and uncertified
/// together, as gate A printed it; nothing is pooled with a refusal.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
struct Tally {
    locks: usize,
    solved: usize,
    reread: usize,
    stay: usize,
    reversed: usize,
    uncertified: usize,
    refused: usize,
}

impl Tally {
    fn fall(&self) -> usize {
        self.reversed + self.uncertified
    }

    fn field(&self, name: &str) -> Option<usize> {
        Some(match name {
            "locks" => self.locks,
            "solved" => self.solved,
            "reread" => self.reread,
            "stay" => self.stay,
            "fall" => self.fall(),
            "reversed" => self.reversed,
            "uncertified" => self.uncertified,
            _ => return None,
        })
    }

    /// The receipt's fields among `names` that differ from this tally's (a field the receipt does
    /// not carry is not compared).
    fn differing(&self, receipt: &BTreeMap<String, usize>, names: &[&str]) -> Vec<String> {
        names
            .iter()
            .filter_map(|&name| {
                let want = *receipt.get(name)?;
                let found = self.field(name)?;
                (want != found).then(|| format!("{name} {found}, gate A's {want}"))
            })
            .collect()
    }
}

impl fmt::Display for Tally {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "Persistence {{ locks: {}, solved: {}, reread: {}, stay: {}, fall: {}, reversed: {}, uncertified: {} }}; refused {}",
            self.locks,
            self.solved,
            self.reread,
            self.stay,
            self.fall(),
            self.reversed,
            self.uncertified,
            self.refused
        )
    }
}

/// **One lock of the native release at constitution 2**, as the resumed move's own reading of its
/// adopted successor holds it (the trial's release, reused; no reading made): its request, station
/// and target; the refinement that locked it (`λ(j)`, its own lock's context) and its class; the
/// stations locked with it and at later refinements; the decision section `S_λ(j)` (the cells
/// placed when `λ(j)` was read) and the release section `S_rel(j)` (the terminal assignment), each
/// with the station open; and its lock face at its own lock, kept from the owner's receipt.
#[derive(Clone, Debug)]
struct Lock {
    request: usize,
    station: usize,
    target: usize,
    refinement: usize,
    class: usize,
    co: Vec<usize>,
    later: Vec<usize>,
    decision: Vec<Option<usize>>,
    released: Vec<Option<usize>>,
    at_lock: Face,
}

impl Lock {
    /// The owner's re-read: solved at its own lock, with a later lock in its section.
    fn reread(&self) -> bool {
        self.at_lock.holds() && !self.later.is_empty()
    }
}

/// **A request's locks from the move's own reading of the successor**, reused: the terminal
/// assignment from the release's decisions; each refinement's placed cells, every lock of an earlier
/// refinement (`bank_release`'s law), checked against every one of the owner's term sites, which
/// carry their refinement's placed cells; each lock's face at its own lock from the owner's receipt
/// of that refinement. Refused where the reading does not hold them.
fn locks_of(request: usize, compared: &RequestComparison, targets: &[usize], stations: usize) -> Result<Vec<Lock>, String> {
    let generation = compared
        .generation
        .as_ref()
        .ok_or_else(|| format!("request {request} has no release"))?;
    let mut section: Vec<Option<usize>> = vec![None; stations];
    for (station, class, ..) in &generation.decisions {
        section[*station] = Some(*class);
    }
    let placed = |k: usize| -> Vec<Option<usize>> {
        let mut cells = vec![None; stations];
        for order in compared.orders.iter().filter(|o| o.context < k) {
            for &s in &order.locked {
                cells[s] = section[s];
            }
        }
        cells
    };
    for term in &compared.terms {
        if let Some(k) = term.site.context
            && term.site.cells != placed(k)
        {
            return Err(format!(
                "request {request} station {}: the owner's site at refinement {k} holds {:?}, the locks before it {:?}",
                term.site.station,
                term.site.cells,
                placed(k)
            ));
        }
    }
    let mut locks = Vec::new();
    for order in &compared.orders {
        let k = order.context;
        for &j in &order.locked {
            let seen = compared
                .stations
                .iter()
                .find(|s| s.context == Some(k) && s.station == j)
                .ok_or_else(|| format!("request {request} station {j}: no reading at its own lock (refinement {k})"))?;
            let mut released = section.clone();
            released[j] = None;
            locks.push(Lock {
                request,
                station: j,
                target: targets[j],
                refinement: k,
                class: section[j].ok_or_else(|| format!("request {request} station {j}: locked with no decision"))?,
                co: order.locked.iter().copied().filter(|&s| s != j).collect(),
                later: compared
                    .orders
                    .iter()
                    .filter(|o| o.context > k)
                    .flat_map(|o| o.locked.iter().copied())
                    .collect(),
                decision: placed(k),
                released,
                at_lock: Face::Kept { value: seen.lock.clone(), solved: seen.solved },
            });
        }
    }
    Ok(locks)
}

/// **Every re-read admitted before any is read** (lost and retained alike; [`REREAD_BOUND`]): past
/// the bound, their count and nothing read (the caller stops incomplete), never the first seven.
fn admit(locks: &[Vec<Lock>], bound: usize) -> Result<Vec<Lock>, usize> {
    let rereads: Vec<Lock> = locks.iter().flatten().filter(|lock| lock.reread()).cloned().collect();
    if rereads.len() > bound { Err(rereads.len()) } else { Ok(rereads) }
}

/// **A re-read's paired factorial** at constitution 2 (the pin §2.3; the native order only): `N0D0`
/// the decision's own at its lock (kept), `N1D0` the normalization alone (the decision's data over
/// the release's mass), `N0D1` the entry alone (the release's data over the decision's mass), `N1D1`
/// the release's own (the owner's persistence re-read at the terminal assignment).
#[derive(Clone, Debug)]
struct Factorial {
    n0d0: Face,
    n1d0: Face,
    n0d1: Face,
    n1d1: Face,
}

impl Factorial {
    /// The four cells' marks, `N0D0 N1D0 N0D1 N1D1`, Fails and Undecided apart.
    fn pattern(&self) -> String {
        [&self.n0d0, &self.n1d0, &self.n0d1, &self.n1d1].map(Face::mark).concat()
    }
}

/// A stop of the resumed read: its exit status and its reason.
#[derive(Clone, Debug, PartialEq, Eq)]
struct Halt {
    status: i32,
    reason: String,
}

/// What the resumed move printed: constitution 1's summary and move 1's line, and constitution 2's
/// summary from the move's own reading of its adopted successor (`None` when it adopted none or its
/// adopted trial holds no reading).
struct Printed {
    moved: [String; 2],
    successor: Option<String>,
}

/// What the resumed read returns: the persistence reads at constitution 2 and every re-read with
/// its factorial.
struct Resumed {
    tally: Tally,
    rereads: Vec<(Lock, Factorial)>,
}

/// A station's lock face read at constitution 2: the lock (its request, station and target), the
/// data entering, the mass the span is read over.
type ReadFace<'a> = dyn Fn(&Lock, &[Option<usize>], &[Option<usize>]) -> Face + Sync + 'a;

/// **The c2 diagnostic after the move, each step gated by the one before** (module header). Every
/// fresh reading goes through `read`; steps 1–4 make none:
/// 1. the move's two lines equal gate A's (masked);
/// 2. constitution 2's reading, the move's own of its successor, equals gate A's;
/// 3. the persistence reads' locks, solved and re-reads, from the kept contexts, equal gate A's at
///    constitution 2;
/// 4. the re-reads, lost and retained, are admitted within [`REREAD_BOUND`] (else incomplete);
/// 5. each re-read is read at the release (`N1D1`, the owner's re-read), and its stay and fall must
///    equal gate A's with none refused (the only readings made before the whole identity holds);
/// 6. each re-read's normalization alone and entry alone are read (`N1D0`, `N0D1`).
fn resumed(
    receipt: &Receipt,
    printed: &Printed,
    locks: Option<&[Vec<Lock>]>,
    read: &ReadFace<'_>,
    log: &mut dyn FnMut(String),
) -> Result<Resumed, Halt> {
    let mismatch = |reason: String| Halt {
        status: MISMATCH,
        reason: format!("executed resume-coupling: identity: {reason}; stopped, nothing further read"),
    };
    for (found, want) in printed.moved.iter().zip(&receipt.moved) {
        if masked(found) != masked(want) {
            return Err(mismatch(format!("the move's line differs from gate A's (masked)\n  found: {found}\n  gate A: {want}")));
        }
    }
    log("identity: constitution 1's reading and move 1's line equal gate A's (wall times and the persistence split masked)".to_string());
    let Some(found) = &printed.successor else {
        return Err(mismatch(
            "the move adopted no successor, or holds no reading of it; gate A's move 1 adopted one and read it".to_string(),
        ));
    };
    if masked(found) != masked(&receipt.successor) {
        return Err(mismatch(format!(
            "constitution 2's reading differs from gate A's (masked)\n  found: {found}\n  gate A: {}",
            receipt.successor
        )));
    }
    log("identity: constitution 2's reading (the move's own reading of its successor, reused) equals gate A's (the wall time masked)".to_string());
    let Some(locks) = locks else {
        return Err(mismatch("the move's own reading of its successor holds no release".to_string()));
    };
    let mut tally = Tally::default();
    for lock in locks.iter().flatten() {
        tally.locks += 1;
        tally.solved += usize::from(lock.at_lock.holds());
        tally.reread += usize::from(lock.reread());
    }
    let differ = tally.differing(&receipt.persistence, &["locks", "solved", "reread"]);
    if !differ.is_empty() {
        return Err(mismatch(format!("the native release's locks at constitution 2 (kept, no reading): {}", differ.join("; "))));
    }
    let rereads = admit(locks, REREAD_BOUND).map_err(|count| Halt {
        status: INCOMPLETE,
        reason: format!(
            "executed resume-coupling: {count} re-reads at constitution 2, past the bound of {REREAD_BOUND}; refused as incomplete before any is read (never truncated)"
        ),
    })?;
    log(format!("re-reads at constitution 2: {} within the bound of {REREAD_BOUND}, every one admitted before any is read", rereads.len()));
    let started = Instant::now();
    let n1d1: Vec<Face> = rereads.par_iter().map(|lock| read(lock, &lock.released, &lock.released)).collect();
    for face in &n1d1 {
        match face.solved() {
            Some(Predicate::Holds) => tally.stay += 1,
            Some(Predicate::Fails) => tally.reversed += 1,
            Some(Predicate::Undecided) => tally.uncertified += 1,
            None => tally.refused += 1,
        }
    }
    log(format!("persistence at constitution 2: {tally}; the release re-reads {} ms", started.elapsed().as_millis()));
    let mut differ = tally.differing(&receipt.persistence, &["stay", "fall", "reversed", "uncertified"]);
    if tally.refused > 0 {
        differ.push(format!("refused {}, which the owner's persistence read never returns", tally.refused));
    }
    if !differ.is_empty() {
        return Err(mismatch(format!("the persistence reads at constitution 2: {}", differ.join("; "))));
    }
    log("identity: the persistence reads at constitution 2 equal gate A's (its move 2 line)".to_string());
    let started = Instant::now();
    let singles: Vec<(Face, Face)> = rereads
        .par_iter()
        .map(|lock| (read(lock, &lock.decision, &lock.released), read(lock, &lock.released, &lock.decision)))
        .collect();
    log(format!("the normalization and the entry alone: {} ms", started.elapsed().as_millis()));
    let rereads = rereads
        .into_iter()
        .zip(n1d1)
        .zip(singles)
        .map(|((lock, n1d1), (n1d0, n0d1))| {
            let factorial = Factorial { n0d0: lock.at_lock.clone(), n1d0, n0d1, n1d1 };
            (lock, factorial)
        })
        .collect();
    Ok(Resumed { tally, rereads })
}

/// **The capture, written before any diagnostic read** (Astra's review of the c2 consumer):
/// constitution 2's complete continuing state (`c2.state`), and the native release's contexts the
/// move read at it (`c2_contexts.txt`): every request's terminal assignment and every lock's
/// refinement, class, decision section and its lock face at its own lock, exactly (`ℓ`'s endpoints,
/// no cell). Unverified until the identity holds; the launcher stamps it only then.
fn capture(
    dir: &str,
    successor: &Constitution,
    ring: usize,
    reading: &BatchComparison,
    locks: &Result<Vec<Vec<Lock>>, String>,
    targets: &[Vec<usize>],
) -> std::io::Result<()> {
    let state = format!("{dir}/c2.state");
    let contexts = format!("{dir}/c2_contexts.txt");
    let mut text = String::from(
        "c2 contexts: the native release of constitution 2 as move 1 read its adopted successor (the trial's own release under the lock face at the decisions, reused); unverified until the identity checks of the run's listing pass\n",
    );
    for (q, request) in reading.requests.iter().enumerate() {
        let release = request.generation.as_ref().map_or_else(
            || "no release".to_string(),
            |g| {
                let mut terminal: Vec<Option<usize>> = vec![None; targets[q].len()];
                for (station, class, ..) in &g.decisions {
                    terminal[*station] = Some(*class);
                }
                format!(
                    "{} {:?}, locks {:?}; terminal assignment {terminal:?}",
                    if g.release.released() { "released" } else { "held" },
                    g.release.classes,
                    g.locks
                )
            },
        );
        text += &format!("request {q}: target {:?}; {release}; r* {:?}\n", targets[q], request.consistent);
        if let Ok(locks) = locks {
            for lock in &locks[q] {
                let face = match &lock.at_lock {
                    Face::Kept { value, solved } => format!("{} ℓ ∈ [{}, {}]", mark(*solved), value.lower, value.upper),
                    other => other.show(),
                };
                text += &format!(
                    "  station {}: locked {} at refinement {} with {:?}, later locks {:?}; decision section {:?}; at its own lock {face}\n",
                    lock.station, lock.class, lock.refinement, lock.co, lock.later, lock.decision
                );
            }
        }
    }
    if let Err(why) = locks {
        text += &format!("the locks refused: {why}\n");
    }
    #[allow(clippy::disallowed_methods)]
    std::fs::write(&state, write_state(successor, ring))?;
    #[allow(clippy::disallowed_methods)]
    std::fs::write(&contexts, text)?;
    println!("capture: constitution 2's complete continuing state written to {state}, its native release's contexts to {contexts}, before any diagnostic read");
    Ok(())
}

/// **The c2 diagnostic** (module header): `executed resume-coupling <terrain> <seed> <count> <c1
/// state> <gate A's receipt> <the move's bound ms> <capture dir>`.
#[allow(clippy::too_many_arguments)]
pub(super) fn resume_coupling(
    terrain: &str,
    seed: u64,
    count: usize,
    state: &str,
    receipt: &str,
    move_bound: u128,
    capture_dir: &str,
) {
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
        "executed resume-coupling: {count} {terrain} requests at development seed {seed}; gate A's constitution 1 restored whole, one native update taken (the lock face at the decisions, every commit guard) on the batch gate A's move 1 read; its lines and constitution 2's reading checked against gate A's receipt; constitution 2 and its native release's contexts captured before any diagnostic read; then every re-read at constitution 2 (lost and retained, at most {REREAD_BOUND}) at its own lock (kept) and at the release, with its normalization and its entry alone; the native order only; the move's bound {move_bound} ms; {} threads",
        rayon::current_num_threads()
    );
    let read_text = |what: &str, path: &str| -> String {
        #[allow(clippy::disallowed_methods)]
        std::fs::read_to_string(path)
            .unwrap_or_else(|error| stop(REFUSED, &format!("executed resume-coupling: {what} ({path}) refused: unreadable ({error})")))
    };
    let (theta, expected) = resume_inputs(&engine, ring, &read_text("constitution 1", state), &read_text("gate A's receipt", receipt))
        .unwrap_or_else(|why| stop(REFUSED, &format!("executed resume-coupling: refused before the move: {why}")));
    println!("constitution 1: {state} restored whole onto the declared opening; written back identical to its file");
    // The one native update, watched: past its bound the run stops then, incomplete.
    let started = Instant::now();
    let bound = Duration::from_millis(u64::try_from(move_bound).unwrap_or(u64::MAX));
    let watch = Watch::start(bound, move || {
        stop(
            INCOMPLETE,
            &format!("executed resume-coupling: the move passed its bound of {move_bound} ms before it ended; stopped incomplete, nothing after it read (the projection's error, reported as such); resident {}", resident()),
        )
    });
    let moved = executed_move(&engine.field, &theta, &requests, &engine.refinement, &bank, BANK_GRAIN, Comparison::LOCK_DECISIONS);
    watch.end();
    let move_ms = started.elapsed().as_millis();
    if move_ms > move_bound {
        stop(INCOMPLETE, &format!("executed resume-coupling: the move took {move_ms} ms, past its bound of {move_bound} ms; stopped incomplete, nothing after it read"));
    }
    let moved = moved.unwrap_or_else(|error| stop(REFUSED, &format!("executed resume-coupling: the move refused its reading ({error})")));
    let (c1_line, ..) = summary_line("constitution 1 (before move 1)", &theta, &moved.before, &targets, stations, move_ms);
    let move_1 = move_line(1, &moved, move_ms);
    println!("{c1_line}");
    println!("{move_1}");
    // The move's own reading of its adopted successor: the adopted trial's release, reused.
    let own = moved.adopted.as_ref().and_then(|(successor, _)| {
        moved
            .trials
            .iter()
            .rev()
            .find(|trial| trial.refusal.is_none())
            .and_then(|trial| trial.after.as_ref())
            .map(|reading| (successor, reading))
    });
    let c2_line = own.map(|(successor, reading)| summary_line("constitution 2 (before move 2)", successor, reading, &targets, stations, move_ms).0);
    if let Some(line) = &c2_line {
        println!("{line}");
        println!("    (constitution 2's reading is the move's own reading of its adopted successor, reused: no reading made)");
    }
    let locks: Option<Result<Vec<Vec<Lock>>, String>> = own.map(|(_, reading)| {
        reading
            .requests
            .iter()
            .enumerate()
            .map(|(q, request)| locks_of(q, request, &targets[q], stations))
            .collect()
    });
    // Capture first: nothing the diagnostic reads below can lose constitution 2 or its contexts.
    if let (Some((successor, reading)), Some(locks)) = (own, &locks) {
        capture(capture_dir, successor, ring, reading, locks, &targets)
            .unwrap_or_else(|error| stop(REFUSED, &format!("executed resume-coupling: the capture could not be written to {capture_dir} ({error})")));
    }
    let locks = match locks {
        Some(Err(why)) => stop(REFUSED, &format!("executed resume-coupling: the move's own reading of its successor refused as contexts: {why}")),
        Some(Ok(locks)) => Some(locks),
        None => None,
    };
    // Every fresh reading at constitution 2 through one function; each request's placement made
    // on its first reading, none before the move's lines, constitution 2's reading and the kept
    // part of the tuple hold.
    let successor = own.map(|(successor, _)| successor);
    let placements: Vec<OnceLock<Result<BankPlacement, String>>> = requests.iter().map(|_| OnceLock::new()).collect();
    let read = |lock: &Lock, data: &[Option<usize>], mass: &[Option<usize>]| -> Face {
        let Some(successor) = successor else {
            return Face::Refused("no successor".to_string());
        };
        let request = &requests[lock.request];
        let placement = placements[lock.request].get_or_init(|| {
            BankPlacement::of(&engine.field, successor, &request.current, &request.moment, &engine.refinement).map_err(|error| error.to_string())
        });
        match placement {
            Ok(placement) => read_face(placement, &bank, alphabet, lock.station, data, mass, lock.target),
            Err(why) => Face::Refused(format!("the placement at constitution 2 refused ({why})")),
        }
    };
    let reads_started = Instant::now();
    let start_readings = READINGS.load(Ordering::Relaxed);
    let printed = Printed { moved: [c1_line, move_1], successor: c2_line };
    let mut log = |line: String| println!("  {line}");
    let resumed = resumed(&expected, &printed, locks.as_deref(), &read, &mut log).unwrap_or_else(|halt| stop(halt.status, &halt.reason));
    let reads_ms = reads_started.elapsed().as_millis();
    // Every re-read whole: its lock, its status at the release, its four cells and the contrasts in
    // both orders with the interaction; nothing named a cause.
    let mut patterns: BTreeMap<(&'static str, String), usize> = BTreeMap::new();
    for (lock, factorial) in &resumed.rereads {
        let status = match factorial.n1d1.solved() {
            Some(Predicate::Holds) => "retained",
            Some(Predicate::Fails) => "lost, reversed",
            Some(Predicate::Undecided) => "lost, uncertified",
            None => "refused",
        };
        *patterns.entry((status, factorial.pattern())).or_default() += 1;
        println!(
            "  re-read: request {} station {} (target {}): locked {} at refinement {} with {:?}, later locks {:?} at classes {:?}; {status}; factorial (N0D0, N1D0, N0D1, N1D1) ({}, {}, {}, {}): N0D0 (kept) {}, N1D0 {}, N0D1 {}, N1D1 {}; {}",
            lock.request,
            lock.station,
            lock.target,
            lock.class,
            lock.refinement,
            lock.co,
            lock.later,
            lock.later.iter().map(|&k| lock.released[k]).collect::<Vec<_>>(),
            factorial.n0d0.mark(),
            factorial.n1d0.mark(),
            factorial.n0d1.mark(),
            factorial.n1d1.mark(),
            factorial.n0d0.show(),
            factorial.n1d0.show(),
            factorial.n0d1.show(),
            factorial.n1d1.show(),
            contrasts_of(&factorial.n0d0, &factorial.n1d0, &factorial.n0d1, &factorial.n1d1)
                .unwrap_or_else(|| "contrasts refused".to_string())
        );
    }
    let t = &resumed.tally;
    println!(
        "  re-reads {}: retained {}, lost {} (reversed {}, uncertified {}), refused {}",
        resumed.rereads.len(),
        t.stay,
        t.fall(),
        t.reversed,
        t.uncertified,
        t.refused
    );
    for ((status, pattern), n) in &patterns {
        println!("  pattern (N0D0 N1D0 N0D1 N1D1) {pattern}, {status}: {n}");
    }
    let made = READINGS.load(Ordering::Relaxed) - start_readings;
    println!(
        "executed resume-coupling: complete; the move {move_ms} ms of its bound {move_bound} ms; the reads at constitution 2 {reads_ms} ms; {made} turn readings made after the move, {} kept from the move's own reading (each re-read's lock face at its own lock: {} re-reads of {alphabet} candidates); {} ms; resident {}",
        resumed.rereads.len() * alphabet,
        resumed.rereads.len(),
        clock.elapsed().as_millis(),
        resident()
    );
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

    // ---------------------------------------------------------------------------------------
    // the c2 diagnostic (`executed resume-coupling`): synthetic locks and readings stand in for the
    // move and the turn readings, so nothing here takes the move or reads constitution 2; gate A's
    // receipt and saved state are read as files only.

    /// Gate A's printed receipt (`witness.txt`).
    fn gate_a_receipt() -> String {
        let path = concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/../../research/records/2026-09-30_STEP_1B_GATE_A_receipts/witness.txt"
        );
        #[allow(clippy::disallowed_methods)]
        std::fs::read_to_string(path).expect("gate A's receipt")
    }

    fn read_at(solved: Predicate, value: i64) -> Face {
        let zero = ExactInterval::point(Rat::zero());
        Face::Read(LockFace {
            value: ExactInterval::point(Rat::from_integer(value.into())),
            solved,
            above: false,
            shares: Vec::new(),
            excess: zero,
        })
    }

    /// 8 requests of 8 stations, one lock a refinement from station 7 down (gate A's constitution 1
    /// listing), so station `j` has later locks `j − 1 … 0`; solved at its own lock where `solved`.
    fn locks_with(solved: impl Fn(usize, usize) -> bool) -> Vec<Vec<Lock>> {
        (0..8)
            .map(|q| {
                (0..8)
                    .map(|j| {
                        let mut released = vec![Some(1); 8];
                        released[j] = None;
                        let at = if solved(q, j) { Predicate::Holds } else { Predicate::Fails };
                        Lock {
                            request: q,
                            station: j,
                            target: 1,
                            refinement: 7 - j,
                            class: 1,
                            co: Vec::new(),
                            later: (0..j).rev().collect(),
                            decision: (0..8).map(|s| (s > j).then_some(1)).collect(),
                            released,
                            at_lock: Face::Kept { value: ExactInterval::point(Rat::from_integer(1.into())), solved: at },
                        }
                    })
                    .collect()
            })
            .collect()
    }

    /// Gate A's constitution 2 in synthetic form: 64 locks, 7 solved at their own lock, each with
    /// later locks (requests 0–6, station 1).
    fn gate_a_locks() -> Vec<Vec<Lock>> {
        locks_with(|q, j| q < 7 && j == 1)
    }

    /// What the resumed move prints when it reproduces gate A: the receipt's lines with other wall
    /// times and the persistence split beside `fall`.
    fn reproduced(receipt: &Receipt) -> Printed {
        let retimed = |line: &str| format!("{}; 1 ms", masked(line));
        Printed {
            moved: [retimed(&receipt.moved[0]), retimed(&receipt.moved[1]).replace(" }; ", ", reversed: 0, uncertified: 0 }; ")],
            successor: Some(retimed(&receipt.successor)),
        }
    }

    /// Which cell a synthetic reading was asked for.
    #[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
    enum Cell {
        N1D0,
        N0D1,
        N1D1,
    }

    /// A synthetic reader: at the release (`N1D1`) requests 0–3 stay solved, 4 and 6 fail, 5 is
    /// undecided (gate A's `stay 4, fall 3`); the normalization alone fails for request 0 (a retained
    /// re-read the entry compensates) and the entry alone is undecided for request 4. Every call is
    /// logged by its request, station and cell.
    struct Reader {
        calls: std::sync::Mutex<Vec<(usize, usize, Cell)>>,
        refuse: Option<usize>,
    }

    impl Reader {
        fn new() -> Self {
            Reader { calls: std::sync::Mutex::new(Vec::new()), refuse: None }
        }

        fn read(&self, lock: &Lock, data: &[Option<usize>], mass: &[Option<usize>]) -> Face {
            let cell = match (data == lock.released.as_slice(), mass == lock.released.as_slice()) {
                (true, true) => Cell::N1D1,
                (false, true) if data == lock.decision.as_slice() => Cell::N1D0,
                (true, false) if mass == lock.decision.as_slice() => Cell::N0D1,
                _ => panic!("a reading at no declared cell"),
            };
            self.calls.lock().expect("calls").push((lock.request, lock.station, cell));
            let q = lock.request;
            match cell {
                Cell::N1D1 if self.refuse == Some(q) => Face::Refused("a synthetic refusal".to_string()),
                Cell::N1D1 if q < 4 => read_at(Predicate::Holds, 0),
                Cell::N1D1 if q == 5 => read_at(Predicate::Undecided, 2),
                Cell::N1D1 => read_at(Predicate::Fails, 3),
                Cell::N1D0 if q == 0 => read_at(Predicate::Fails, 4),
                Cell::N0D1 if q == 4 => read_at(Predicate::Undecided, 5),
                _ => read_at(Predicate::Holds, -1),
            }
        }

        fn calls(&self) -> Vec<(usize, usize, Cell)> {
            let mut calls = self.calls.lock().expect("calls").clone();
            calls.sort();
            calls
        }
    }

    fn resume_with(receipt: &Receipt, printed: &Printed, locks: Option<&[Vec<Lock>]>, reader: &Reader) -> Result<Resumed, Halt> {
        let read = |lock: &Lock, data: &[Option<usize>], mass: &[Option<usize>]| reader.read(lock, data, mass);
        resumed(receipt, printed, locks, &read, &mut |_| {})
    }

    #[test]
    fn a_malformed_c1_state_is_refused_before_the_move() {
        let engine = Engine::new(order_declared());
        let ring = engine.refinement.ring();
        let (state, receipt) = (gate_a_state(), gate_a_receipt());
        // Positive control: gate A's saved state restores whole, and its receipt reads constitution
        // 2's persistence reads `locks 64, solved 7, reread 7, stay 4, fall 3`.
        let (_, read) = resume_inputs(&engine, ring, &state, &receipt).expect("gate A's state and receipt");
        let tuple: Vec<usize> = TUPLE.iter().map(|field| read.persistence[*field]).collect();
        assert_eq!(tuple, vec![64, 7, 7, 4, 3]);
        assert!(read.moved[1].starts_with("    move 1: adopted at step 1/2; "));
        // Truncated after `rho` (E and ρ intact): refused, never remounted partially.
        let rho = state.lines().position(|line| line.starts_with("rho ")).expect("rho");
        let truncated: String = state.lines().take(rho + 1).map(|line| format!("{line}\n")).collect();
        let refused = resume_inputs(&engine, ring, &truncated, &receipt).expect_err("a truncated state");
        assert!(refused.contains("not a complete continuing state"), "{refused}");
        assert!(refused.contains("never read as a partial remount"), "{refused}");
        // Off its written form: parses, does not write back to its own text.
        let edited = state.replace("\nclock ", "\nclock 0");
        let refused = resume_inputs(&engine, ring, &edited, &receipt).expect_err("a state off its written form");
        assert!(refused.contains("written back differs"), "{refused}");
        // A receipt without move 2's line (constitution 2's persistence reads) is refused too.
        let without: String = receipt.lines().filter(|line| !line.starts_with(RECEIPT_MOVE_2)).map(|line| format!("{line}\n")).collect();
        let refused = resume_inputs(&engine, ring, &state, &without).expect_err("no move 2 line");
        assert!(refused.contains("no line `move 2: …`"), "{refused}");
    }

    #[test]
    fn an_identity_mismatch_stops_before_any_reading_of_constitution_2() {
        let receipt = Receipt::read(&gate_a_receipt()).expect("gate A's receipt");
        let locks = gate_a_locks();
        // The move's line perturbed (another step): stopped, nothing read.
        let mut printed = reproduced(&receipt);
        printed.moved[1] = printed.moved[1].replace("adopted at step 1/2", "adopted at step 1/4");
        let reader = Reader::new();
        let halt = resume_with(&receipt, &printed, Some(&locks), &reader).err().expect("a perturbed move line");
        assert_eq!(halt.status, MISMATCH);
        assert!(reader.calls().is_empty());
        // Constitution 1's reading perturbed, constitution 2's perturbed, or no successor: the same.
        for perturb in [0, 1, 2] {
            let mut printed = reproduced(&receipt);
            match perturb {
                0 => printed.moved[0] = printed.moved[0].replace("solved 7 of 64", "solved 8 of 64"),
                1 => printed.successor = printed.successor.map(|line| line.replace("solved 1 of 64", "solved 2 of 64")),
                _ => printed.successor = None,
            }
            let reader = Reader::new();
            let halt = resume_with(&receipt, &printed, Some(&locks), &reader).err().expect("a perturbed line");
            assert_eq!(halt.status, MISMATCH, "{perturb}");
            assert!(reader.calls().is_empty(), "{perturb}");
        }
        // The tuple perturbed in its kept part (gate A's re-reads 8): stopped before any reading.
        let printed = reproduced(&receipt);
        let mut tuple = receipt.clone();
        tuple.persistence.insert("reread".to_string(), 8);
        let reader = Reader::new();
        let halt = resume_with(&tuple, &printed, Some(&locks), &reader).err().expect("a perturbed reread");
        assert_eq!(halt.status, MISMATCH);
        assert!(halt.reason.contains("reread 7, gate A's 8"), "{}", halt.reason);
        assert!(reader.calls().is_empty());
        // The tuple perturbed in its read part (stay 5, fall 2): only the release re-reads are made,
        // the normalization and the entry are never read.
        let mut tuple = receipt.clone();
        tuple.persistence.insert("stay".to_string(), 5);
        tuple.persistence.insert("fall".to_string(), 2);
        let reader = Reader::new();
        let halt = resume_with(&tuple, &printed, Some(&locks), &reader).err().expect("a perturbed stay");
        assert_eq!(halt.status, MISMATCH);
        assert!(halt.reason.contains("stay 4, gate A's 5"), "{}", halt.reason);
        let calls = reader.calls();
        assert_eq!(calls.len(), 7);
        assert!(calls.iter().all(|&(_, _, cell)| cell == Cell::N1D1));
        // Positive control: the reproduced lines (other wall times, the split printed) pass.
        let reader = Reader::new();
        assert!(resume_with(&receipt, &printed, Some(&locks), &reader).is_ok());
    }

    #[test]
    fn more_than_seven_rereads_is_refused_as_incomplete() {
        let receipt = Receipt::read(&gate_a_receipt()).expect("gate A's receipt");
        let printed = reproduced(&receipt);
        // Eight re-reads, the receipt made to agree so the bound alone decides.
        let eight = locks_with(|q, j| j == 1 && q < 8);
        let mut agreeing = receipt.clone();
        agreeing.persistence.insert("solved".to_string(), 8);
        agreeing.persistence.insert("reread".to_string(), 8);
        assert_eq!(admit(&eight, REREAD_BOUND).err(), Some(8), "refused whole, never the first seven");
        let reader = Reader::new();
        let halt = resume_with(&agreeing, &printed, Some(&eight), &reader).err().expect("past the bound");
        assert_eq!(halt.status, INCOMPLETE);
        assert!(halt.reason.contains("8 re-reads at constitution 2, past the bound of 7"), "{}", halt.reason);
        assert!(reader.calls().is_empty(), "nothing read past the bound");
        // Positive control: seven, the lost and the retained alike, are admitted.
        let seven = admit(&gate_a_locks(), REREAD_BOUND).expect("seven within the bound");
        assert_eq!(seven.len(), REREAD_BOUND);
        // A solved lock with no later lock (station 0 locks last) is no re-read.
        let last = locks_with(|_, j| j == 0);
        assert_eq!(admit(&last, REREAD_BOUND).map(|r| r.len()), Ok(0));
    }

    #[test]
    fn the_factorial_is_read_for_lost_and_retained_rereads() {
        let receipt = Receipt::read(&gate_a_receipt()).expect("gate A's receipt");
        let locks = gate_a_locks();
        let reader = Reader::new();
        let read = resume_with(&receipt, &reproduced(&receipt), Some(&locks), &reader).ok().expect("gate A's c2 in synthetic form");
        assert_eq!(read.rereads.len(), 7);
        // Every re-read, retained (requests 0–3) and lost (4–6), read at the release and at its
        // normalization and its entry alone: three cells each, and nothing else read.
        let mut expected: Vec<(usize, usize, Cell)> = (0..7).flat_map(|q| [Cell::N1D0, Cell::N0D1, Cell::N1D1].map(|c| (q, 1, c))).collect();
        expected.sort();
        assert_eq!(reader.calls(), expected);
        for (lock, factorial) in &read.rereads {
            // N0D0 is the lock face the move kept, never read again.
            assert!(matches!(factorial.n0d0, Face::Kept { solved: Predicate::Holds, .. }), "{lock:?}");
            for cell in [&factorial.n1d0, &factorial.n0d1, &factorial.n1d1] {
                assert!(matches!(cell, Face::Read(_)), "{lock:?}");
            }
            assert!(contrasts_of(&factorial.n0d0, &factorial.n1d0, &factorial.n0d1, &factorial.n1d1).is_some_and(|c| c.contains("interaction")));
        }
        // The retained re-read whose normalization alone fails while the release holds (a
        // compensation control) keeps its whole pattern.
        let retained = read.rereads.iter().find(|(lock, _)| lock.request == 0).expect("request 0");
        assert_eq!(retained.1.pattern(), "HFHH");
        // The interaction enclosed exactly: ℓ₁₁ − ℓ₁₀ − ℓ₀₁ + ℓ₀₀ = 0 − 4 − (−1) + 1 = −2.
        let contrasts = contrasts_of(&retained.1.n0d0, &retained.1.n1d0, &retained.1.n0d1, &retained.1.n1d1).expect("contrasts");
        assert!(contrasts.ends_with("interaction [-131072/65536, -131071/65536)"), "{contrasts}");
    }

    #[test]
    fn fails_and_undecided_are_counted_apart() {
        let receipt = Receipt::read(&gate_a_receipt()).expect("gate A's receipt");
        let locks = gate_a_locks();
        let read = resume_with(&receipt, &reproduced(&receipt), Some(&locks), &Reader::new()).ok().expect("gate A's c2 in synthetic form");
        let t = read.tally;
        assert_eq!((t.locks, t.solved, t.reread, t.stay), (64, 7, 7, 4));
        assert_eq!((t.reversed, t.uncertified, t.refused, t.fall()), (2, 1, 0, 3));
        assert_eq!(
            t.to_string(),
            "Persistence { locks: 64, solved: 7, reread: 7, stay: 4, fall: 3, reversed: 2, uncertified: 1 }; refused 0"
        );
        // The lost re-reads keep their own marks: a failing and an undecided release are patterns apart.
        let pattern = |q: usize| read.rereads.iter().find(|(lock, _)| lock.request == q).expect("a re-read").1.pattern();
        assert_eq!(pattern(4), "HHUF");
        assert_eq!(pattern(5), "HHHU");
        assert_eq!(pattern(6), "HHHF");
        // A refused reading at the release is neither: counted refused, and refused by the identity
        // (the owner's read never returns one), before the normalization and the entry are read.
        let reader = Reader { refuse: Some(6), ..Reader::new() };
        let halt = resume_with(&receipt, &reproduced(&receipt), Some(&locks), &reader).err().expect("a refused re-read");
        assert_eq!(halt.status, MISMATCH);
        assert!(halt.reason.contains("fall 2, gate A's 3") && halt.reason.contains("refused 1"), "{}", halt.reason);
        assert!(reader.calls().iter().all(|&(_, _, cell)| cell == Cell::N1D1));
    }

    #[test]
    fn the_move_past_its_bound_stops_the_run() {
        // Past its bound the guard calls the stop (the harness's stops the process incomplete).
        let (fired, heard) = mpsc::channel();
        let watch = Watch::start(Duration::from_millis(10), move || fired.send(()).expect("heard"));
        assert!(heard.recv_timeout(Duration::from_secs(10)).is_ok());
        watch.end();
        // Positive control: a unit ended within its bound calls nothing.
        let (fired, heard) = mpsc::channel();
        Watch::start(Duration::from_secs(600), move || fired.send(()).expect("heard")).end();
        assert!(heard.try_recv().is_err());
    }
}

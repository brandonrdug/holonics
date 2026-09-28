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
//! cargo run --release -p holonics --example hnn_chase -- diagnose [seeds]   # U4: the failure located
//! cargo run --release -p holonics --example hnn_chase -- fresh    # U4: the fresh population
//! cargo run --release -p holonics --example hnn_chase -- moves [fresh]   # U4: the move sets
//! ```
//!
//! [definition; agent-inferred] **U4's next loop.** `diagnose` reads the machine's passage tick by
//! tick against the truth-only basin and prints every admitted move's readings at each tick whose
//! release raises the truth's least capture. `choose`'s fourth rung is the plan
//! (`robust,certified-expected,expected`), and each rung prints the bounds its machine released and
//! kept (capture by `t + B_t`, the chaser's pledge) and the pledges broken. `fresh` runs the pinned
//! fresh population against its
//! predeclared criteria ([`fresh`]). `moves` reads the truth-only least capture under each declared
//! variant of the chaser's move set ([`MOVE_SETS`], `pursuit::MoveSet`).
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
//!
//! [definition] **The uncertified releases, read through the one law** (THE_REBUILD U3, the second
//! loop): below each seed's machine line, every tick the one law did not release (`Released` at
//! tolerance zero is the certified capture) is printed with what the law returned, an offered
//! probe's class sizes against the commit's and their products `∏_c |c|^|c|` with their
//! factorization, and the cornering arm's cost comparison (the probe's concession in tube states
//! against the price `d·|Θ|`).
//!
//! [definition; agent-inferred] **The move reading** (THE_REBUILD U4; a reading of the receipt, not
//! a change of law): for each passage and in sum, each tick's move `(v, v′)` of the runner and of
//! the chaser counted by its kind (`geometry::motion`: rest, start, stop, free fall, turn, boost,
//! turn and boost), and each slip read as the demanded move outside the traction disk of the cell
//! the runner stands on (at the onset, the demanded move's kind) while the realized move is the held
//! one `(v, v)` at every slipping tick.

#[path = "exterior.rs"]
mod exterior;

use std::sync::Arc;
use std::time::Instant;

use holonics::compression::landmark::context::{
    Capacity, LandmarkDeclaration, LetterFamily, StopPrior,
};
use holonics::geometry::motion::{Move, MoveKind};
use holonics::holarchy::terrain::{
    ActionDeclaration, ActionPassage, ArenaDeclaration, Basin, BasinMemo, Candidate, CaptureReach,
    Chase, ChasePorts, ChaseView, Chaser, ConstantBearing, Evasion, ExpectedCapture, ExpectedMemo,
    Motion, MoveSet, Moves, PurePursuit, Pursuer, RunnerFamily, RunnerLaw, RunnerState, act_drawn,
    capture_ticks, classes, expected_ticks, viable_tube,
};
use holonics::ratio::algebraic::ExactInterval;
use holonics::ratio::surprisal::SymbolicSurprisal;
use holonics::ratio::{Rat, rat};
use holonics::receiver::population::{
    ChaseFamily, Family, MachineChaser, MachineDeclaration, MachineReceipt, MachineRelease, Plan,
    Population, PopulationError, Posterior, Release, TreeFamily, selected_fibre,
};
use holonics::receiver::release::ReleaseReturn;
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

/// [definition; agent-inferred, pinned before the run] **The fresh population** (U4's next loop):
/// the seeds `FRESH_SEED + s`, `s < FRESH_SEEDS`, a declared contiguous range disjoint from the
/// acceptance seeds (`SEED + s`) and the choosing seeds (`CHOOSING_SEED + s`), none read before this
/// pin and none selected by any property. `64 = 2⁶` seeds: the run was projected at about four
/// minutes against the ten-minute budget from the choosing sweep's work.
const FRESH_SEED: u64 = 20_261_101;
const FRESH_SEEDS: u64 = 64;

/// [definition; agent-inferred, chosen on the choosing seeds] **The candidate**: the pledged expected
/// plan (`receiver::population::chaser::Plan::Expected`, its release the machine's own continuation)
/// at the machine's pinned `n`, `m` and `d`. On the choosing seeds at `n = 2, m = 12, d = 0` the
/// robust plan summed 150 capture ticks, the certified-then-expected plan 148 and the pledged expected
/// plan 147, each keeping every bound it released; the least sum chooses.
const CANDIDATE_PLAN: Plan = Plan::Expected;

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
        evasions: vec![
            Evasion::Flee,
            Evasion::Circle { clockwise: false },
            Evasion::Circle { clockwise: true },
            Evasion::ZigZag { period: 2 },
            Evasion::ZigZag { period: 3 },
        ],
    }
}

fn pursuer() -> Pursuer {
    Pursuer {
        law: RunnerLaw {
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
        Some("diagnose") => diagnose(&mode[1..]),
        Some("fresh") => fresh(),
        Some("moves") => move_sets(&mode[1..]),
        _ => reception(),
    }
}

// -------------------------------------------------------------------------------------------
// U4's next loop: the measured failure located

/// [definition; agent-inferred] **The diagnosis's truth-only reading limit**: the truth's least
/// capture through each admitted move is read to at most this many ticks (above every least the
/// acceptance seeds read, `14`).
const DIAGNOSIS_LIMIT: usize = 24;

/// [definition; agent-inferred] **An admitted move's readings at a tick** (U4's next loop, the
/// diagnosis; readings of the machine's own laws, not a change of its rule): the machine's four
/// (the fibre's capture basin `b(u)` at its horizon `m`, the cornering `K(u)`, the nearness `N(u)`
/// and the information product `∏_c |c|^|c|`), the truth's own least capture through the move
/// (`1 +` the truth-only basin from the joint state after it), and the capture basin at `m` over
/// the leading class alone (the class the machine predicts) and over the truth's class alone.
struct MoveRow {
    next: Motion,
    truth: Option<usize>,
    fibre: Option<usize>,
    cornering: usize,
    nearness: i64,
    information: BigUint,
    lead: Option<usize>,
    own: Option<usize>,
    sum: ExpectedCapture,
}

/// [definition] **A tick's diagnosis**: the fibre's size and classes, the release, the chosen move's
/// row, the truth's least capture from the present joint state, and every admitted move's row.
struct TickRow {
    tick: usize,
    fibre: usize,
    classes: usize,
    release: Release,
    chosen: usize,
    now: Option<usize>,
    rows: Vec<MoveRow>,
}

impl TickRow {
    /// **A regret tick**: the chosen move's truth-only capture exceeds the present least.
    fn regret(&self) -> bool {
        match (self.now, self.rows[self.chosen].truth) {
            (Some(now), Some(via)) => via > now,
            (Some(_), None) => true,
            _ => false,
        }
    }
}

/// [definition; agent-inferred] **The traced machine**: the machine itself decides and receives;
/// beside it, each candidate's state is carried past the received cells (as the machine carries
/// them), and each tick's readings are taken on the machine's fibre before it releases. The
/// diagnosis checks that the machine's commit order on these readings returns the move the machine
/// released at every certified and committed tick.
struct Traced {
    inner: MachineChaser,
    truth: usize,
    candidates: Vec<Candidate>,
    ports: Option<Arc<ChasePorts>>,
    ticks: Vec<TickRow>,
}

impl Chaser for Traced {
    type Error = PopulationError;

    fn label(&self) -> String {
        self.inner.label()
    }

    fn open(&mut self, ports: &Arc<ChasePorts>, pursuer: &Pursuer) -> Result<(), PopulationError> {
        self.inner.open(ports, pursuer)?;
        self.candidates = Candidate::opening(&family(), &ports.arena, ports.opening.position)?;
        self.ports = Some(Arc::clone(ports));
        self.ticks.clear();
        Ok(())
    }

    fn decide(&mut self, view: &ChaseView<'_>) -> Result<Motion, PopulationError> {
        let indices = self.inner.fibre();
        let released = self.inner.decide(view)?;
        let release = self
            .inner
            .receipt()
            .releases
            .last()
            .expect("a release")
            .kind();
        let ports = Arc::clone(self.ports.as_ref().expect("opened"));
        let (arena, moves, pursuer) = (&ports.arena, &ports.moves, view.pursuer);
        let caps = pursuer.law.caps(arena.declaration())?;
        let disk = Moves::within(caps.top())?;
        let basin = Basin {
            arena,
            moves,
            pursuer,
            caps: &caps,
            disk: &disk,
        };
        let tick = view.tick as u64;
        let fibre: Vec<Candidate> = indices
            .iter()
            .map(|&i| self.candidates[i].clone())
            .collect();
        let plural = fibre.len() > 1;
        let parts = classes(arena, moves, &fibre, view.chaser.position, tick)?;
        let truth = [self.candidates[self.truth].clone()];
        let truth_parts = classes(arena, moves, &truth, view.chaser.position, tick)?;
        let lead = parts
            .iter()
            .max_by(|a, b| a.1.len().cmp(&b.1.len()).then(b.0.cmp(&a.0)))
            .map(|part| vec![part.clone()])
            .expect("a nonempty fibre");
        let own: Vec<_> = parts
            .iter()
            .filter(|(_, class)| class.iter().any(|c| c.index == self.truth))
            .cloned()
            .collect();
        let (mut memo, mut truth_memo) = (BasinMemo::default(), BasinMemo::default());
        let mut expected_memo = ExpectedMemo::default();
        let now =
            basin.capture_ticks(&mut truth_memo, view.chaser, tick, &truth, DIAGNOSIS_LIMIT)?;
        let admitted = view.admitted()?;
        let mut rows = Vec::with_capacity(admitted.len());
        for &next in &admitted {
            let fibre_b = capture_ticks(&basin, &mut memo, &parts, next, tick, BASIN_HORIZON - 1)?;
            let truth_b = capture_ticks(
                &basin,
                &mut truth_memo,
                &truth_parts,
                next,
                tick,
                DIAGNOSIS_LIMIT - 1,
            )?;
            let lead_b = capture_ticks(&basin, &mut memo, &lead, next, tick, BASIN_HORIZON - 1)?;
            let own_b = if own.is_empty() {
                None
            } else {
                capture_ticks(&basin, &mut memo, &own, next, tick, BASIN_HORIZON - 1)?
            };
            let sum = expected_ticks(
                &basin,
                &mut expected_memo,
                &parts,
                next,
                tick,
                BASIN_HORIZON - 1,
            )?;
            let reach = CaptureReach::of(arena, pursuer, &caps, &disk, next, TUBE_HORIZON)?;
            let (mut cornering, mut nearness, mut sizes) = (0usize, 0i64, Vec::new());
            for (_, class) in &parts {
                let motion = class[0].state.motion;
                let gap = [
                    motion.position[0] - next.position[0],
                    motion.position[1] - next.position[1],
                ];
                nearness += (gap[0] * gap[0] + gap[1] * gap[1]) * class.len() as i64;
                if !pursuer.captures(motion.position, next.position) {
                    for member in class {
                        cornering += viable_tube(
                            arena,
                            &member.law.caps,
                            motion,
                            member.state.held,
                            &reach,
                        )?
                        .size();
                    }
                }
                if plural {
                    for (_, split) in classes(arena, moves, class, next.position, tick + 1)? {
                        sizes.push(split.len());
                    }
                }
            }
            let information = sizes.iter().fold(BigUint::from(1u32), |product, &size| {
                product * BigUint::from(size).pow(size as u32)
            });
            rows.push(MoveRow {
                next,
                truth: truth_b,
                fibre: fibre_b,
                cornering,
                nearness,
                information,
                lead: lead_b,
                own: own_b,
                sum,
            });
        }
        let chosen = admitted
            .iter()
            .position(|&m| m == released)
            .expect("the machine releases an admitted move");
        if release != Release::Probe {
            let commit = (0..rows.len())
                .min_by_key(|&i| {
                    let r = &rows[i];
                    (r.fibre.is_none(), r.fibre, r.cornering, r.nearness)
                })
                .expect("a nonempty admitted set");
            assert_eq!(
                commit, chosen,
                "the diagnosis reads the machine's commit order"
            );
        }
        self.ticks.push(TickRow {
            tick: view.tick,
            fibre: fibre.len(),
            classes: parts.len(),
            release,
            chosen,
            now,
            rows,
        });
        Ok(released)
    }

    fn receive(&mut self, cell: usize) -> Result<(), PopulationError> {
        self.inner.receive(cell)?;
        let ports = self.ports.as_ref().expect("opened");
        self.candidates = self
            .candidates
            .iter()
            .map(|candidate| candidate.receive(&ports.arena, &ports.moves, cell))
            .collect::<Result<_, _>>()?;
        Ok(())
    }
}

/// A win, tie or loss of `a` against `b` in capture ticks (fewer wins): `0`, `1` or `2`.
fn outcome(a: usize, b: usize) -> usize {
    match a.cmp(&b) {
        std::cmp::Ordering::Less => 0,
        std::cmp::Ordering::Equal => 1,
        std::cmp::Ordering::Greater => 2,
    }
}

/// `w/t/l` of a count triple.
fn wtl(counts: &[usize; 3]) -> String {
    format!("{}/{}/{}", counts[0], counts[1], counts[2])
}

/// [definition; agent-inferred, pinned before the run] **The fresh population's run** (U4's next
/// loop; THE_REBUILD U4, "F6's action acceptance stays as written"). On each seed of the fresh
/// population ([`FRESH_SEED`]), four chasers from the reception's draw under the same traction
/// bound: the machine under its robust plan (the current rule), the candidate ([`CANDIDATE_PLAN`]),
/// pure pursuit and constant bearing; each capture tick counts the cap `2^9` when uncaptured. The
/// truth-only basin's least capture `L` is read to the least of the four captures, which bounds it
/// (each chaser's realized word is a strategy that knows nothing the truth-only basin lacks). The
/// criteria, declared before the run:
/// - **aggregate capture ticks**, `Σ T` for each chaser;
/// - **the sum of regrets** to the truth-only least, `Σ (T − L)`, for each chaser;
/// - **win/tie/loss** (strictly fewer ticks, equal, more) of each machine against pure pursuit,
///   against constant bearing, and against both at once (against the lesser of the two on the
///   seed), and of the candidate against the robust machine;
/// - **F6's action acceptance as written**, for each machine: strictly fewer ticks than both
///   controls in sum, and strictly fewer than both on more than half of the seeds;
/// - **the candidate against the current machine**: it improves on it exactly when its aggregate
///   capture ticks are strictly fewer and it wins more seeds against it than it loses.
///
/// Reported separately, as a conditional reading and never as the acceptance: the seeds whose
/// truth-only least lies strictly below both controls (a win beyond every control is admitted),
/// with each machine's win/tie/loss against both at once and its regret sum on them.
///
/// [measured; the pin amended before the rerun] **A refused draw.** The first run stopped at seed
/// `20261135`, the 35th: its draw opens the runner and the chaser within capture, which the terrain
/// refuses (`Chase::draw`, `pursuit::act`), and the pin had not declared the case. A draw the terrain
/// refuses is a seed with no chase: it is printed, read by no chaser and enters no sum, and "more
/// than half of the seeds" counts the chased seeds. The refusal reads the openings alone, the same
/// for every chaser, so it selects by no chaser's outcome. Nothing else changed.
fn fresh() {
    let declaration = declaration();
    let family = family();
    let action = ActionDeclaration {
        pursuer: pursuer(),
        ticks: ACTION_TICKS,
        horizon: RECEIPT_HORIZON,
    };
    println!(
        "hnn_chase fresh: the fresh population {FRESH_SEED} + s, s < {FRESH_SEEDS}; the machine n = {TUBE_HORIZON}, m = {BASIN_HORIZON}, d = {PRICE}, escape 2^(−{ESCAPE}); the candidate plan {}; passages of at most {ACTION_TICKS} = 2^9 ticks",
        CANDIDATE_PLAN.label()
    );
    let names = [
        "the machine (robust)",
        "the candidate",
        "pure pursuit",
        "constant bearing",
    ];
    let started = Instant::now();
    let (mut sums, mut regrets) = ([0usize; 4], [0usize; 4]);
    // Per machine (robust, candidate): against pursuit, bearing, both at once; win/tie/loss.
    let mut against = [[[0usize; 3]; 3]; 2];
    let mut head = [0usize; 3];
    let (mut admitting, mut conditional, mut conditional_regrets) =
        (0usize, [[0usize; 3]; 2], [0usize; 2]);
    let mut releases = [[0usize; 3]; 2];
    let mut refused = Vec::new();
    for s in 0..FRESH_SEEDS {
        let seed = FRESH_SEED + s;
        let (_, _, openings) = Chase::drawn(&declaration, &family, seed).expect("a draw");
        if action.pursuer.captures(openings[0], openings[1]) {
            println!(
                "seed {seed}: the draw opens within capture ({:?}, {:?}); the terrain refuses the chase, and no chaser reads it",
                openings[0], openings[1]
            );
            refused.push(seed);
            continue;
        }
        let mut robust = machine(TUBE_HORIZON, BASIN_HORIZON, PRICE, Plan::Robust);
        let r = act_drawn(&declaration, &family, &action, seed, &mut robust).expect("the machine");
        let mut candidate = machine(TUBE_HORIZON, BASIN_HORIZON, PRICE, CANDIDATE_PLAN);
        let e =
            act_drawn(&declaration, &family, &action, seed, &mut candidate).expect("the candidate");
        let p = act_drawn(&declaration, &family, &action, seed, &mut PurePursuit).expect("pursuit");
        let b =
            act_drawn(&declaration, &family, &action, seed, &mut ConstantBearing).expect("bearing");
        for (total, receipt) in releases
            .iter_mut()
            .zip([robust.receipt(), candidate.receipt()])
        {
            for (count, release) in
                total
                    .iter_mut()
                    .zip([Release::Certified, Release::Commit, Release::Probe])
            {
                *count += receipt.count(release);
            }
        }
        let ticks = [r.ticks(), e.ticks(), p.ticks(), b.ticks()];
        let limit = *ticks.iter().min().expect("four");
        let least = least_capture(seed, limit).expect("the least lies within every capture");
        for i in 0..4 {
            sums[i] += ticks[i];
            regrets[i] += ticks[i] - least;
        }
        let best_control = ticks[2].min(ticks[3]);
        let admits = least < best_control;
        admitting += usize::from(admits);
        for m in 0..2 {
            against[m][0][outcome(ticks[m], ticks[2])] += 1;
            against[m][1][outcome(ticks[m], ticks[3])] += 1;
            against[m][2][outcome(ticks[m], best_control)] += 1;
            if admits {
                conditional[m][outcome(ticks[m], best_control)] += 1;
                conditional_regrets[m] += ticks[m] - least;
            }
        }
        head[outcome(ticks[1], ticks[0])] += 1;
        println!(
            "seed {seed}: the truth [{}] {}; capture robust {}, candidate {}, pursuit {}, bearing {}; least {least}{}",
            r.index,
            r.runner.label(),
            capture_line(&r),
            capture_line(&e),
            capture_line(&p),
            capture_line(&b),
            if admits {
                "; admits a win beyond both controls"
            } else {
                ""
            }
        );
    }
    let chased = FRESH_SEEDS as usize - refused.len();
    println!();
    println!(
        "the terrain refuses {} of {FRESH_SEEDS} draws (openings within capture): {refused:?}",
        refused.len()
    );
    println!(
        "over the {chased} chased seeds ({} ms): capture ticks in sum {} {}, {} {}, {} {}, {} {} (an uncaptured passage counts its cap {ACTION_TICKS})",
        started.elapsed().as_millis(),
        names[0],
        sums[0],
        names[1],
        sums[1],
        names[2],
        sums[2],
        names[3],
        sums[3]
    );
    println!(
        "  the sum of regrets to the truth-only least: {} {}, {} {}, {} {}, {} {}",
        names[0], regrets[0], names[1], regrets[1], names[2], regrets[2], names[3], regrets[3]
    );
    for m in 0..2 {
        println!(
            "  {} win/tie/loss: against pure pursuit {}, against constant bearing {}, against both at once {}; releases certified/commit/probe {:?}",
            names[m],
            wtl(&against[m][0]),
            wtl(&against[m][1]),
            wtl(&against[m][2]),
            releases[m]
        );
    }
    println!(
        "  the candidate against the robust machine, win/tie/loss: {}",
        wtl(&head)
    );
    let verdict = |passed: bool| if passed { "passed" } else { "not passed" };
    for m in 0..2 {
        let passed = sums[m] < sums[2] && sums[m] < sums[3] && 2 * against[m][2][0] > chased;
        println!(
            "  F6's action acceptance as written, {}: {}",
            names[m],
            verdict(passed)
        );
    }
    println!(
        "  the candidate improves on the current machine (fewer ticks in sum, more seeds won than lost against it): {}",
        verdict(sums[1] < sums[0] && head[0] > head[2])
    );
    println!(
        "  conditional reading (not the acceptance): {admitting} seeds admit a win beyond both controls; on them win/tie/loss against both at once {} {}, {} {}; regret sums {} / {}",
        names[0],
        wtl(&conditional[0]),
        names[1],
        wtl(&conditional[1]),
        conditional_regrets[0],
        conditional_regrets[1]
    );
}

/// An optional tick count, `·` for none.
fn opt(value: Option<usize>) -> String {
    value.map_or("·".to_string(), |v| v.to_string())
}

/// **The diagnosis** (U4's next loop): on each named seed (the acceptance seeds by default), the
/// machine's passage read tick by tick against the truth-only basin; every tick whose release
/// raises the truth's least capture is printed with every admitted move's readings.
fn diagnose(args: &[String]) {
    let seeds: Vec<u64> = if args.is_empty() {
        (0..SEEDS).map(|s| SEED + s).collect()
    } else {
        args.iter().map(|a| a.parse().expect("a seed")).collect()
    };
    let declaration = declaration();
    let family = family();
    let action = ActionDeclaration {
        pursuer: pursuer(),
        ticks: ACTION_TICKS,
        horizon: RECEIPT_HORIZON,
    };
    println!(
        "hnn_chase diagnose: the machine n = {TUBE_HORIZON}, m = {BASIN_HORIZON}, d = {PRICE}; the truth-only basin read to {DIAGNOSIS_LIMIT} ticks; rows: position, velocity, the truth's capture through the move, b over the fibre, b over the leading class, b over the truth's class, K, N, ∏|c|^|c|"
    );
    for seed in seeds {
        let (index, _, _) = Chase::drawn(&declaration, &family, seed).expect("a draw");
        let mut traced = Traced {
            inner: machine(TUBE_HORIZON, BASIN_HORIZON, PRICE, Plan::Robust),
            truth: index,
            candidates: Vec::new(),
            ports: None,
            ticks: Vec::new(),
        };
        let started = Instant::now();
        let passage =
            act_drawn(&declaration, &family, &action, seed, &mut traced).expect("the machine");
        println!();
        println!(
            "seed {seed}: the truth [{index}] {}; the machine captures at {}; the truth-only least from the opening {} ({} ms)",
            passage.runner.label(),
            capture_line(&passage),
            opt(traced.ticks.first().and_then(|t| t.now)),
            started.elapsed().as_millis()
        );
        for row in &traced.ticks {
            let chosen = &row.rows[row.chosen];
            println!(
                "  t {:>2}: |Θ| {:>2} in {:>2} classes; {:?}; to {:?} v {:?}; the truth's least now {}, through the release {}{}",
                row.tick,
                row.fibre,
                row.classes,
                row.release,
                chosen.next.position,
                chosen.next.velocity,
                opt(row.now),
                opt(chosen.truth),
                if row.regret() { "  ← regret" } else { "" }
            );
            if row.regret() {
                for (i, r) in row.rows.iter().enumerate() {
                    println!(
                        "      {} {:?} v {:>7}: truth {:>2}, b {:>2}, lead {:>2}, own {:>2}, S {:?}, K {:>6}, N {:>5}, ∏ {}",
                        if i == row.chosen { "*" } else { " " },
                        r.next.position,
                        format!("{:?}", r.next.velocity),
                        opt(r.truth),
                        opt(r.fibre),
                        opt(r.lead),
                        opt(r.own),
                        (r.sum.uncaptured, r.sum.ticks),
                        r.cornering,
                        r.nearness,
                        r.information
                    );
                }
            }
        }
    }
}

/// The machine of a declaration under a plan.
fn machine(horizon: usize, basin: usize, price: u64, plan: Plan) -> MachineChaser {
    MachineChaser::planning(
        MachineDeclaration {
            family: family(),
            escape: ESCAPE,
            horizon,
            basin,
            price,
        },
        plan,
    )
    .expect("a declared machine")
}

/// A plan by its name: `robust`, `certified-expected` or `expected`.
fn plan_named(name: &str) -> Plan {
    match name {
        "robust" => Plan::Robust,
        "certified-expected" => Plan::CertifiedExpected,
        "expected" => Plan::Expected,
        other => panic!("no plan named {other}"),
    }
}

/// **One seed's three passages**: the machine at a tube horizon, basin horizon and price, pure
/// pursuit and constant bearing, the cornering receipt at its declared horizon; the machine's
/// receipt, its fibre's size at its last tick and its wall time.
fn passages(
    seed: u64,
    horizon: usize,
    basin: usize,
    price: u64,
    plan: Plan,
) -> ([ActionPassage; 3], MachineReceipt, usize, u128) {
    let declaration = declaration();
    let family = family();
    let action = ActionDeclaration {
        pursuer: pursuer(),
        ticks: ACTION_TICKS,
        horizon: RECEIPT_HORIZON,
    };
    let started = Instant::now();
    let mut chaser = machine(horizon, basin, price, plan);
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
    let plans: Vec<Plan> = args.get(3).map_or(vec![Plan::Robust], |a| {
        a.split(',').map(plan_named).collect()
    });
    println!(
        "hnn_chase choose: choosing seeds {CHOOSING_SEED} + s, s < {SEEDS}; passages of at most {ACTION_TICKS} = 2^9 ticks"
    );
    for &horizon in &horizons {
        for &basin in &basins {
            for &price in &prices {
                for &plan in &plans {
                    let started = Instant::now();
                    let (mut sums, mut wins) = ([0usize; 3], [0usize; 3]);
                    let (mut kept, mut broken) = ((0usize, 0usize), 0usize);
                    let mut line = Vec::new();
                    for s in 0..SEEDS {
                        let ([m, p, b], receipt, _, _) =
                            passages(CHOOSING_SEED + s, horizon, basin, price, plan);
                        let (k, r) = bounds_kept(&m, &receipt);
                        kept.0 += k;
                        kept.1 += r;
                        broken += receipt.broken;
                        for (sum, passage) in sums.iter_mut().zip([&m, &p, &b]) {
                            *sum += passage.ticks();
                        }
                        wins[0] += usize::from(m.ticks() < p.ticks());
                        wins[1] += usize::from(m.ticks() < b.ticks());
                        wins[2] += usize::from(m.ticks() < p.ticks() && m.ticks() < b.ticks());
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
                        "n = {horizon}, m = {basin}, d = {price}, plan {}: capture ticks in sum machine {}, pursuit {}, bearing {}; seeds won {} against pursuit, {} against bearing, {} against both, of {SEEDS}; released bounds kept {} of {}, pledges broken {broken}; {} ms",
                        plan.label(),
                        sums[0],
                        sums[1],
                        sums[2],
                        wins[0],
                        wins[1],
                        wins[2],
                        kept.0,
                        kept.1,
                        started.elapsed().as_millis()
                    );
                    println!("  machine/pursuit/bearing: {}", line.join("  "));
                }
            }
        }
    }
}

/// **The released bounds a passage kept** (`receiver::population::chaser`, the pledge): the ticks
/// the machine released whose bound its own passage kept, capture by `t + B_t`, and the ticks it
/// released.
fn bounds_kept(passage: &ActionPassage, receipt: &MachineReceipt) -> (usize, usize) {
    receipt
        .certified
        .iter()
        .enumerate()
        .filter_map(|(tick, bound)| bound.map(|b| tick + b))
        .fold((0, 0), |(kept, released), by| {
            (
                kept + usize::from(passage.captured.is_some_and(|at| at <= by)),
                released + 1,
            )
        })
}

/// **The truth-only capture basin's least capture** from the opening, within `limit` ticks: every
/// adaptive chaser strategy that knows the truth's law (`pursuit::Basin` on the truth alone).
fn least_capture(seed: u64, limit: usize) -> Option<usize> {
    let declaration = declaration();
    let family = family();
    let pursuer = pursuer();
    let (index, arena, openings) = Chase::drawn(&declaration, &family, seed).expect("a draw");
    let moves = family.moves(&declaration).expect("the alphabet");
    let caps = pursuer.law.caps(&declaration).expect("the caps");
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

/// [definition; agent-inferred] **The move sets read** (U4's next loop; `pursuit::MoveSet`): the
/// chaser's declared lattice; the half lattice held to the lattice's realized top speed `√2`; the
/// half lattice without pure boosts; the half lattice. The same traction disk, friction field and
/// capture throughout, and the same speed bound `3/2` except where the top is declared lower.
const MOVE_SETS: [MoveSet; 4] = [
    MoveSet::LATTICE,
    MoveSet {
        grain: 2,
        boosts: true,
        top: Some(2),
    },
    MoveSet {
        grain: 2,
        boosts: false,
        top: None,
    },
    MoveSet {
        grain: 2,
        boosts: true,
        top: None,
    },
];

/// [definition; agent-inferred] **The truth-only least capture as a function of the move set**
/// (U4's next loop, a reading, not a change of law): on each seed (the acceptance seeds by default,
/// or `fresh` for the fresh population), the truth-only least capture from the opening under each
/// declared move set (`pursuit::least_capture`), each finer set read to the lattice's least (a finer
/// grain's least is at most it); the lattice's reading is checked equal to the capture basin's on the
/// truth alone.
fn move_sets(args: &[String]) {
    let (first, count) = match args.first().map(String::as_str) {
        Some("fresh") => (FRESH_SEED, FRESH_SEEDS),
        _ => (SEED, SEEDS),
    };
    let declaration = declaration();
    let family = family();
    let pursuer = pursuer();
    let moves = family.moves(&declaration).expect("the alphabet");
    println!(
        "hnn_chase moves: seeds {first} + s, s < {count}; the truth-only least capture under the move sets {}",
        MOVE_SETS
            .iter()
            .map(MoveSet::label)
            .collect::<Vec<_>>()
            .join(", ")
    );
    let started = Instant::now();
    let (mut sums, mut read, mut refused) = ([0usize; 4], 0usize, 0usize);
    for s in 0..count {
        let seed = first + s;
        let (index, arena, openings) = Chase::drawn(&declaration, &family, seed).expect("a draw");
        if pursuer.captures(openings[0], openings[1]) {
            println!("seed {seed}: the draw opens within capture; no chase");
            refused += 1;
            continue;
        }
        let runner = family.candidate(index).expect("the truth");
        let mut least = [None; 4];
        let mut limit = ACTION_TICKS;
        for (i, set) in MOVE_SETS.iter().enumerate() {
            least[i] = pursuit_least(&arena, &moves, &runner, openings, &pursuer, *set, limit);
            if i == 0 {
                let basin = least_capture(seed, least[0].unwrap_or(OPTIMUM_LIMIT));
                assert_eq!(
                    least[0], basin,
                    "the lattice's reading is the capture basin's on the truth alone"
                );
                limit = least[0].expect("the lattice captures the truth");
            }
        }
        let values: Vec<usize> = least.iter().map(|l| l.expect("within")).collect();
        for (sum, value) in sums.iter_mut().zip(&values) {
            *sum += value;
        }
        read += 1;
        println!(
            "seed {seed}: the truth [{index}] {}; least capture {}",
            runner.label(),
            values
                .iter()
                .map(ToString::to_string)
                .collect::<Vec<_>>()
                .join(" / ")
        );
    }
    println!();
    println!(
        "over {read} seeds ({refused} refused draws; {} ms): least captures in sum {}",
        started.elapsed().as_millis(),
        sums.iter()
            .map(ToString::to_string)
            .collect::<Vec<_>>()
            .join(" / ")
    );
}

/// `pursuit::least_capture`, read.
fn pursuit_least(
    arena: &holonics::holarchy::terrain::Arena,
    moves: &Moves,
    runner: &holonics::holarchy::terrain::Runner,
    openings: [[i64; 2]; 2],
    pursuer: &Pursuer,
    set: MoveSet,
    limit: usize,
) -> Option<usize> {
    holonics::holarchy::terrain::least_capture(arena, moves, runner, openings, pursuer, set, limit)
        .expect("a declared move set")
}

/// [definition; agent-inferred] **A passage's move reading** (module header; a reading of the
/// receipt, not a law): per tick the runner's move `(v_t, v_(t+1))` from its opening at rest and the
/// chaser's from its port, each counted by kind (`geometry::motion::MoveKind`, in its declared
/// order); and each slip, at its onset the demanded move `(v, v + Δv)` (the runner's law re-read at
/// the tick, `Runner::demand`) against the traction disk of the cell it stands on, and at every
/// slipping tick the realized move against the held one `(v, v)`.
#[derive(Clone, Copy, Debug, Default)]
struct MoveReading {
    runner: [usize; 7],
    chaser: [usize; 7],
    onsets: usize,
    outside: usize,
    demanded: [usize; 7],
    slipping: usize,
    held: usize,
}

impl MoveReading {
    fn add(&mut self, other: &MoveReading) {
        let pairs = [
            (&mut self.runner, &other.runner),
            (&mut self.chaser, &other.chaser),
            (&mut self.demanded, &other.demanded),
        ];
        for (total, count) in pairs {
            for (t, c) in total.iter_mut().zip(count) {
                *t += c;
            }
        }
        self.onsets += other.onsets;
        self.outside += other.outside;
        self.slipping += other.slipping;
        self.held += other.held;
    }
}

/// A kind's place in `MoveKind::ALL`.
fn kind_index(kind: MoveKind) -> usize {
    MoveKind::ALL
        .iter()
        .position(|&k| k == kind)
        .expect("a declared kind")
}

/// Counts by kind, as `label n` in the declared order.
fn kinds_line(counts: &[usize; 7]) -> String {
    MoveKind::ALL
        .iter()
        .zip(counts)
        .map(|(kind, n)| format!("{} {n}", kind.label()))
        .collect::<Vec<_>>()
        .join(", ")
}

/// **A passage's move reading** (on [`MoveReading`]): the runner replayed from its opening through
/// its cells, which must return the passage's path at every tick.
fn move_reading(passage: &ActionPassage) -> MoveReading {
    let ports = &passage.ports;
    let (arena, moves, runner) = (&ports.arena, &ports.moves, &passage.runner);
    let caps = runner.law.caps(arena.declaration()).expect("the caps");
    let chaser = ports.chaser.motions();
    let mut state = RunnerState::opening(arena, ports.opening.position).expect("the opening");
    let mut reading = MoveReading::default();
    for (tick, &cell) in passage.cells.iter().enumerate() {
        let v = state.motion.velocity;
        let realized = Move::new(v, passage.path[tick].velocity);
        reading.runner[kind_index(realized.kind())] += 1;
        let chased = Move::new(chaser[tick].velocity, chaser[tick + 1].velocity);
        reading.chaser[kind_index(chased.kind())] += 1;
        if cell == moves.slip() {
            reading.slipping += 1;
            reading.held += usize::from(realized == Move::held(v));
            if state.held == 0 {
                reading.onsets += 1;
                let change = runner
                    .demand(
                        arena,
                        moves,
                        &caps,
                        &state,
                        chaser[tick].position,
                        tick as u64,
                    )
                    .expect("a slip onset has its demand");
                let demanded = Move::by_change(v, change);
                let class = arena.class(state.motion.position).expect("in the arena");
                reading.outside += usize::from(!demanded.within_cap(caps.classes[class]));
                reading.demanded[kind_index(demanded.kind())] += 1;
            }
        }
        state = runner
            .receive(arena, moves, &state, cell)
            .expect("the runner's cell");
        assert_eq!(state.motion, passage.path[tick], "the replay is the path");
    }
    reading
}

/// The move reading's lines.
fn move_lines(reading: &MoveReading, indent: &str) {
    println!(
        "{indent}the runner's moves: {}",
        kinds_line(&reading.runner)
    );
    println!(
        "{indent}the chaser's moves: {}",
        kinds_line(&reading.chaser)
    );
    println!(
        "{indent}slip onsets {}, the demanded move outside the traction disk on {} ({}); slipping ticks {}, the realized move the held one on {}",
        reading.onsets,
        reading.outside,
        kinds_line(&reading.demanded),
        reading.slipping,
        reading.held
    );
}

/// **The uncertified releases, read through the one law** (module header): one line for each tick
/// the law did not release.
fn uncertified(receipt: &MachineReceipt) -> Vec<String> {
    let probe_line = |law: &ReleaseReturn| match law {
        ReleaseReturn::Ask { probe } => format!(
            "the law asked {} (classes {:?}, ∏|c|^|c| = {}) against the commit (classes {:?}, {})",
            probe.observation,
            probe.partition.classes(),
            factored(&probe.partition.product()),
            probe.partition.against(),
            factored(&probe.partition.against_product())
        ),
        other => format!("the law returned {other:?}"),
    };
    receipt
        .releases
        .iter()
        .enumerate()
        .filter_map(|(tick, release)| {
            let fibre = receipt.fibre[tick];
            match release {
                MachineRelease::Law(law @ ReleaseReturn::Ask { .. }) => Some(format!(
                    "tick {tick}, fibre {fibre}: the probe, emitted: {}",
                    probe_line(law)
                )),
                MachineRelease::Law(_) => None,
                MachineRelease::Commit {
                    law: ReleaseReturn::Hold,
                    ..
                } => Some(format!(
                    "tick {tick}, fibre {fibre}: the cornering commit; the law held, no admitted motion separating the fibre more than the commit"
                )),
                MachineRelease::Commit { law, price } => Some(format!(
                    "tick {tick}, fibre {fibre}: the cornering commit; {}; its concession {} tube states exceeds the price d·|Θ| = {}",
                    probe_line(law),
                    price.map_or(0, |p| p.concession),
                    price.map_or(0, |p| p.bound)
                )),
            }
        })
        .collect()
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
        pursuer.law.speed,
        pursuer.law.traction,
        pursuer.capture,
    );
    let names = ["the machine", "pure pursuit", "constant bearing"];
    let (mut sums, mut kernels, mut prefixes) = ([0usize; 3], [0usize; 3], [0usize; 3]);
    let (mut slips, mut walls) = ([(0usize, 0usize); 3], [0usize; 3]);
    let (mut wins, mut both, mut optimal) = ([0usize; 2], 0usize, 0usize);
    let (mut releases, mut misses) = ([0usize; 3], 0usize);
    let mut readings = [MoveReading::default(); 3];
    for s in 0..SEEDS {
        let seed = SEED + s;
        let (runs, receipt, fibre, ms) =
            passages(seed, TUBE_HORIZON, BASIN_HORIZON, PRICE, Plan::Robust);
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
            let reading = move_reading(passage);
            move_lines(&reading, "    ");
            readings[i].add(&reading);
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
        for line in uncertified(&receipt) {
            println!("    {line}");
        }
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
    println!("  the move reading over {SEEDS} seeds (a reading, not a law):");
    for (name, reading) in names.iter().zip(&readings) {
        println!("  against {name}:");
        move_lines(reading, "    ");
    }
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
        pursuer.law.speed,
        pursuer.law.traction,
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

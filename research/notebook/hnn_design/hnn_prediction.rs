//! **`hnn_prediction`: step 1's harness, the executed comparison on known-truth terrain**
//! (THE_REBUILD U6, step 1; #73, #148, #63). Its modes are the `executed …` subcommands of
//! `hnn_executed_loop.rs` and, for loop 1c, `hnn_loop_1c.rs`, whose headers state each mode and its
//! pins; this file holds the
//! declaration they share and dispatches to them. Committed commands run once in release, never a
//! test.
//!
//! ```sh
//! cargo run --release -p holonics --example hnn_prediction -- executed move <seed> <requests>
//! cargo run --release -p holonics --example hnn_prediction -- executed train <arm> <terrain> <seed> <batch> <moves> <deadline ms> <out>
//! cargo run --release -p holonics --example hnn_prediction -- executed evaluate <terrain> <seed> <count> <out> <label[=E]>…
//! cargo run --release -p holonics --example hnn_prediction -- executed spread <terrain> <seed> <count> <label[=E]>…
//! cargo run --release -p holonics --example hnn_prediction -- executed slopes <terrain> <seed> <count> <label[=E]>…
//! cargo run --release -p holonics --example hnn_prediction -- executed counts <terrain> <training seed> <count> <validation seed> <count> <out>
//! cargo run --release -p holonics --example hnn_prediction -- executed witness <terrain> <seed> <count> <moves> <deadline ms> <out> [<states dir>]
//! cargo run --release -p holonics --example hnn_prediction -- executed replay <terrain> <seed> <count> <label=state>…
//! cargo run --release -p holonics --example hnn_prediction -- executed coupling <terrain> <seed> <count> <deadline ms> <label=state|label=opening>…
//! cargo run --release -p holonics --example hnn_prediction -- executed represent <terrain> <seed> <count> <iterates> <deadline ms> <out> [<held-out seed>]
//! cargo run --release -p holonics --example hnn_prediction -- executed resume-coupling <terrain> <seed> <count> <c1 state> <gate A receipt> <move bound ms> <capture dir>
//! cargo run --release -p holonics --example hnn_prediction -- executed causal <terrain> <seed> <count> <label[=E]>…
//! ```
//!
//! [definition; agent-inferred, the order pin and the bank pin] **The declaration**
//! ([`order_declared`]), fixed by the September 29 pins and read by every mode:
//! - **The field** ([`declare`]): three rings of one period `d = 60 = 2²·3·5` in a chain
//!   `0 — 1 — 2`, joined node to node on every node at admittance 2 and exponent 0 (`G_a = Y_a`).
//!   The period is the joint residue ring of the pairwise coprime factors `3, 4, 5`, so a datum's
//!   residue is its joint residue class, and it holds a request and its section (`n + m = 48`).
//!   Ring 0 is the source and the receiving ring (its lock every port, so it steps once a cell);
//!   rings 1 and 2 step only by carries. There is no pair offset, so no window on the source. The
//!   receiver's grain is `L_R = 16` and its aperture `K·w + 1`.
//! - **The refinement**: `K = 2` continuing words of `w = 1` tick over `m = 8` stations; the
//!   alphabet `|A| = 5`, four symbols and the termination; a request of `n = 40` cells.
//! - **The constitution**: `Constitution::initial(field, CAMPAIGN_ONE_BUDGET)`, the declared opening
//!   `E₀` with nothing authored for a terrain (`CAMPAIGN_ONE_BUDGET = 2³³`).
//! - **The receiving bank** ([`bank_of`]): the parametron record's receiving node, its members the
//!   pump steps whose order divides `d`, at the strength `p = 5/8`, its turn read at the relative
//!   grain `2^(−16)` ([`BANK_GRAIN`]).
//! - **The order-2 terrain** ([`order_pairs`]): a request of `n` cells drawn uniformly from 4
//!   symbols, its target the continuation `x_t = x_(t−2) + 1 (mod 4)` over the `m` stations. The
//!   loop's `terrain_pairs` adds the alternation and the line; only the terrain computes truth.
//!
//! The modes before the executed comparison (`copy`, `moire`, `divergence`, `order2`, `pumped`,
//! `text`, `probe`, `develop`: native generation, the order repair, the bank's generation and
//! learning path, the pumped receiving ring) and the executed loop's `face` arm were retired on
//! September 30 (THE_REBUILD U6, batch N2); their source is at commit `7ca300bb`.

#[path = "exterior.rs"]
mod exterior;
#[path = "hnn_executed_loop.rs"]
mod executed_loop;
#[path = "hnn_loop_1c.rs"]
mod loop_1c;

use std::collections::BTreeMap;
use std::time::Instant;

use holonics::compression::landmark::context::StopPrior;
use holonics::geometry::RatVec3;
use holonics::geometry::screw::ScrewGenerator;
use holonics::hnn::constitution::{CAMPAIGN_ONE_BUDGET, Constitution};
use holonics::hnn::field::{
    ConstitutionRead, ContactDeclaration, CribDeclaration, Current, Field, FieldDeclaration,
    ReceiverDeclaration, RingDeclaration,
};
use holonics::hnn::moment::SourceMoment;
use holonics::hnn::prediction::{Refinement, generate_by_bank};
use holonics::hnn::ring::{PumpDeclaration, PumpStep, ReceivingBank, ResonatorMaterial};
use holonics::holarchy::terrain::Draw;
use holonics::holon::parametron::Carrier;
use holonics::ratio::algebraic::ExactInterval;
use holonics::ratio::linear::ExactRatMatrix;
use holonics::ratio::{Rat, rat};
use num_traits::{Signed, Zero};

use exterior::resident_set;

/// The receiver's code tolerance: campaign 1's `1/16` bit, so `L_R = 16`.
const TOLERANCE: (i64, i64) = (1, 16);
/// The declared population, above the declared field's capacity `n*`.
const POPULATION: u64 = 1 << 16;

/// [definition] **The declaration** (module header).
#[derive(Clone, Copy, Debug)]
struct Declared {
    /// `d`: every ring's period.
    period: u64,
    /// `|A|`: the exterior chart, its last class the termination.
    alphabet: usize,
    /// `K` and `w`.
    words: usize,
    span: usize,
    /// `m`.
    stations: usize,
    /// The request's length `n`.
    request: usize,
}

/// **The field** (module header).
fn declare(declared: &Declared) -> Field {
    let d = declared.period;
    let axis = ScrewGenerator::new(RatVec3::from_i64(0, 0, 1), RatVec3::zero());
    let ring = |lock: Vec<u64>| RingDeclaration {
        period: d,
        screw: axis.clone(),
        placements: (0..d)
            .map(|node| FieldDeclaration::quarter_turn(node, d))
            .collect(),
        lock,
        reflector: (0..d).map(|port| ((d - port) % d) as usize).collect(),
        admittance: Rat::from_integer(2.into()),
        initial: 0,
    };
    let contact = |from: usize, to: usize| ContactDeclaration {
        from,
        to,
        channel: (0..d as usize).map(|node| (node, node)).collect(),
        admittance: Rat::from_integer(2.into()),
        exponent: Rat::from_integer(0.into()),
    };
    Field::declare(
        FieldDeclaration {
            rings: vec![ring((0..d).collect()), ring(Vec::new()), ring(Vec::new())],
            contacts: vec![contact(0, 1), contact(1, 2)],
            loops: Vec::new(),
            sources: vec![0],
            offsets: Vec::new(),
            alphabet: declared.alphabet,
            step: Rat::from_integer(1.into()),
            exponent_grain: 1,
            receivers: vec![ReceiverDeclaration {
                ring: 0,
                aperture: declared.words * declared.span + 1,
                tolerance: rat(TOLERANCE.0, TOLERANCE.1),
                depth: 1,
                prior: StopPrior::half(),
            }],
            crib: CribDeclaration {
                window: 16,
                offset: 1,
            },
            population: POPULATION,
            lattice: Default::default(),
        }
        .by_lattice_rule(),
    )
    .expect("the declared field")
}

/// **A request's moment**, ingested from rest (past any carry-out: the moment's own law continues).
fn ingest(field: &Field, request: &[usize]) -> (Current, SourceMoment) {
    let mut current = Current::at_rest(field);
    let mut moment = SourceMoment::open(field, &current);
    let mut fed = 0;
    while fed < request.len() {
        fed += moment
            .ingest(field, &mut current, &request[fed..])
            .expect("a request in the chart")
            .cells;
    }
    (current, moment)
}

/// [definition] **The engine**: the declared field, its refinement and the declared opening.
struct Engine {
    field: Field,
    refinement: Refinement,
    theta: Constitution,
}

impl Engine {
    fn new(declared: Declared) -> Self {
        let field = declare(&declared);
        let refinement = Refinement::declare(
            &field,
            0,
            declared.words,
            declared.span,
            declared.stations,
            declared.alphabet - 1,
        )
        .expect("the declared refinement");
        let theta =
            Constitution::initial(&field, CAMPAIGN_ONE_BUDGET).expect("the initial constitution");
        Self {
            field,
            refinement,
            theta,
        }
    }
}

/// [definition; agent-inferred, the bank pin] **The receiving bank**: the parametron record's
/// receiving node (`C = I`, `K = I`, no dissipation but its port `Y = 16`, `h = 1`), its members at
/// the axis `1` and the pump steps `i^j` whose order divides the receiving ring's period `d` (so the
/// turn is a cycle of every member's clock), each at the declared strength `p`.
fn bank_of(period: u64, strength: &Rat) -> ReceivingBank {
    let identity = ExactRatMatrix::identity(2).expect("identity");
    let material = ResonatorMaterial::new(
        identity.clone(),
        identity,
        ExactRatMatrix::zero(2, 2).expect("zero"),
        None,
    )
    .expect("the receiving node");
    let axis = Carrier::new(Rat::from_integer(1.into()), Rat::zero()).expect("the axis 1");
    let pumps = [
        PumpStep::Stand,
        PumpStep::Quarter,
        PumpStep::Half,
        PumpStep::ThreeQuarters,
    ]
    .into_iter()
    .filter(|step| period.is_multiple_of(step.order() as u64))
    .map(|step| PumpDeclaration::new(strength.clone(), axis.clone(), step).expect("a member"))
    .collect();
    ReceivingBank::new(
        material,
        pumps,
        Rat::from_integer(16.into()),
        Rat::from_integer(1.into()),
        BANK_DECISION_GRAIN,
    )
    .expect("the bank")
}

/// The grain of a bank member's own `Floquet::decide` (the parametron record's `2^(−6)`); the turn's
/// readings take the declared grain of the run.
const BANK_DECISION_GRAIN: u32 = 6;

/// [agent-inferred, the bank pin] **The bank's strength**: the parametron record's declared bank,
/// unchanged, `p = 5/8` (its lock window on unit cells; the development reads at `p = 5/8` and
/// `p = 1` read alike). **The turn's relative grain** `2^(−16)`: the least margin the development
/// read locked on was past `2^(−8)` of its growth, so every lock was decided far inside it.
fn bank_strength() -> Rat {
    rat(5, 8)
}
const BANK_GRAIN: u32 = 16;

/// The process's resident set now and at its peak, in bytes (exterior), or `unread`.
fn resident() -> String {
    resident_set().map_or_else(|| "unread".to_string(), |(now, peak)| format!("{now} now, {peak} peak"))
}

/// **The declaration** (module header; the order pin): the joint residue ring of period
/// `D = 3·4·5 = 60`, pairwise coprime factors, at least the request and its section (`n + m = 48`).
fn order_declared() -> Declared {
    Declared {
        period: 3 * 4 * 5,
        alphabet: 5,
        words: 2,
        span: 1,
        stations: 8,
        request: 40,
    }
}

/// **The order-2 terrain** (module header): a request of `n` cells drawn uniformly from 4 symbols,
/// its target the continuation `x_t = x_(t−2) + 1 (mod 4)` over `m` stations.
fn order_pairs(declared: &Declared, seed: u64, count: usize) -> Vec<(Vec<usize>, Vec<usize>)> {
    let symbols = declared.alphabet - 1;
    let mut draw = Draw::new(seed);
    (0..count)
        .map(|_| {
            let mut passage: Vec<usize> =
                (0..declared.request).map(|_| draw.below(symbols)).collect();
            for _ in 0..declared.stations {
                let next = (passage[passage.len() - 2] + 1) % symbols;
                passage.push(next);
            }
            let target = passage.split_off(declared.request);
            (passage, target)
        })
        .collect()
}

fn main() {
    let arguments: Vec<String> = std::env::args().collect();
    match (arguments.get(1).map(String::as_str), arguments.get(2).map(String::as_str)) {
        (Some("executed"), Some("move")) => executed_loop::stage_one(
            arguments[3].parse().expect("a seed"),
            arguments[4].parse().expect("a count"),
        ),
        (Some("executed"), Some("train")) => executed_loop::train(
            &arguments[3],
            &arguments[4],
            arguments[5].parse().expect("a seed"),
            arguments[6].parse().expect("a batch"),
            arguments[7].parse().expect("moves"),
            arguments[8].parse().expect("a deadline in ms"),
            &arguments[9],
        ),
        (Some("executed"), Some("spread")) => executed_loop::spread(
            &arguments[3],
            arguments[4].parse().expect("a seed"),
            arguments[5].parse().expect("a count"),
            &arguments[6..],
        ),
        (Some("executed"), Some("slopes")) => executed_loop::slopes(
            &arguments[3],
            arguments[4].parse().expect("a seed"),
            arguments[5].parse().expect("a count"),
            &arguments[6..],
        ),
        (Some("executed"), Some("evaluate")) => executed_loop::evaluate(
            &arguments[3],
            arguments[4].parse().expect("a seed"),
            arguments[5].parse().expect("a count"),
            &arguments[6],
            &arguments[7..],
        ),
        // Step 1b's gate A: the constrained feasibility witness (the pin
        // research/records/2026-09-30_STEP_1B_THE_CANDIDATE_COMPARISON_PINNED_BEFORE_ITS_RUNS.md
        // §13.3 and its gate-A addendum).
        // With a ninth argument, every constitution read is written as its complete continuing
        // state into that directory (loop 1c's replay, its pin §1.1).
        (Some("executed"), Some("witness")) => executed_loop::witness(
            &arguments[3],
            arguments[4].parse().expect("a seed"),
            arguments[5].parse().expect("a count"),
            arguments[6].parse().expect("moves"),
            arguments[7].parse().expect("a deadline in ms"),
            &arguments[8],
            arguments.get(9).map(String::as_str),
        ),
        // Loop 1c (the pin
        // research/records/2026-10-01_LOOP_1C_PERSISTENCE_REPRESENTATION_AND_REACH_PINNED_BEFORE_ITS_RUNS.md):
        // the exact replay of written states, persistence and coupling, and the representation
        // search; the restore check of complete states, no reading made (the launcher's
        // `check-replay`).
        (Some("executed"), Some("restore")) => loop_1c::restore(&arguments[3..]),
        (Some("executed"), Some("replay")) => loop_1c::replay(
            &arguments[3],
            arguments[4].parse().expect("a seed"),
            arguments[5].parse().expect("a count"),
            &arguments[6..],
        ),
        (Some("executed"), Some("coupling")) => loop_1c::coupling(
            &arguments[3],
            arguments[4].parse().expect("a seed"),
            arguments[5].parse().expect("a count"),
            arguments[6].parse().expect("a deadline in ms"),
            &arguments[7..],
        ),
        // Loop 1c's c2 diagnostic: gate A's saved constitution 1 resumed by one native update, its
        // identity checked against gate A's receipt, then the re-reads at constitution 2.
        (Some("executed"), Some("resume-coupling")) => loop_1c::resume_coupling(
            &arguments[3],
            arguments[4].parse().expect("a seed"),
            arguments[5].parse().expect("a count"),
            &arguments[6],
            &arguments[7],
            arguments[8].parse().expect("the move's bound in ms"),
            &arguments[9],
        ),
        (Some("executed"), Some("represent")) => loop_1c::represent(
            &arguments[3],
            arguments[4].parse().expect("a seed"),
            arguments[5].parse().expect("a count"),
            arguments[6].parse().expect("iterates"),
            arguments[7].parse().expect("a deadline in ms"),
            &arguments[8],
            arguments.get(9).map(|s| s.parse().expect("a held-out seed")),
        ),
        // Step 1b's causal reading (I6).
        // The segment probe (the pin
        // research/records/2026-10-01_THE_SEGMENT_PROBE_PINNED_BEFORE_ITS_RUN.md): read-only.
        (Some("executed"), Some("segment")) => executed_loop::segment(
            &arguments[3],
            arguments[4].parse().expect("a seed"),
            arguments[5].parse().expect("a count"),
            &arguments[6..],
        ),
        // The modulus's slope (the pin
        // research/records/2026-10-01_THE_MODULUS_SLOPE_PINNED_BEFORE_ITS_RUN.md): read-only.
        (Some("executed"), Some("rho-slopes")) => executed_loop::rho_slopes(
            &arguments[3],
            arguments[4].parse().expect("a seed"),
            arguments[5].parse().expect("a count"),
            &arguments[6],
            &arguments[7..],
        ),
        // The native direction (the pin
        // research/records/2026-10-01_THE_NATIVE_DIRECTION_PINNED_BEFORE_ITS_RUN.md): read-only.
        (Some("executed"), Some("direction")) => executed_loop::direction(
            &arguments[3],
            arguments[4].parse().expect("a seed"),
            arguments[5].parse().expect("a count"),
            &arguments[6],
            &arguments[7],
            &arguments[8],
            &arguments[9],
            &arguments[10..],
        ),
        // The move's plane read by its witness (the record
        // research/records/2026-10-01_THE_MOVES_METRIC_IS_ITS_WITNESSS_THE_LOCKS_FISHER_FORM_ON_THE_MOVES_PLANE.md):
        // read-only.
        (Some("executed"), Some("witness-plane")) => executed_loop::witness_plane(
            &arguments[3],
            arguments[4].parse().expect("a seed"),
            arguments[5].parse().expect("a count"),
            &arguments[6],
            &arguments[7],
            &arguments[8],
            &arguments[9..],
        ),
        // One committed move from a state under each declared metric (the pin
        // research/records/2026-10-01_ONE_GUARDED_MOVE_FROM_THE_STUCK_STATE_PINNED_BEFORE_ITS_RUN.md).
        (Some("executed"), Some("move-once")) => executed_loop::move_once(
            &arguments[3],
            arguments[4].parse().expect("a seed"),
            arguments[5].parse().expect("a count"),
            &arguments[6],
            &arguments[7],
            &arguments[8..],
        ),
        (Some("executed"), Some("causal")) => executed_loop::causal(
            &arguments[3],
            arguments[4].parse().expect("a seed"),
            arguments[5].parse().expect("a count"),
            &arguments[6..],
        ),
        // The two counts' terrain reading (the pin
        // research/records/2026-09-30_THE_TWO_COUNTS_PINNED_BEFORE_ITS_RUNS.md).
        (Some("executed"), Some("counts")) => executed_loop::counts(
            &arguments[3],
            arguments[4].parse().expect("a training seed"),
            arguments[5].parse().expect("a training count"),
            arguments[6].parse().expect("a validation seed"),
            arguments[7].parse().expect("a validation count"),
            &arguments[8],
        ),
        _ => panic!(
            "executed move <seed> <requests> | train <arm> <terrain> <seed> <batch> <moves> <deadline ms> <out> | evaluate <terrain> <seed> <count> <out> <label[=E]>… | spread <terrain> <seed> <count> <label[=E]>… | slopes <terrain> <seed> <count> <label[=E]>… | counts <terrain> <training seed> <count> <validation seed> <count> <out> | witness <terrain> <seed> <count> <moves> <deadline ms> <out> [<states dir>] | causal <terrain> <seed> <count> <label[=E]>… | restore <label=state>… | replay <terrain> <seed> <count> <label=state|label=partial:file>… | coupling <terrain> <seed> <count> <deadline ms> <label=state|label=partial:file|label=opening>… | represent <terrain> <seed> <count> <iterates> <deadline ms> <out> [<held-out seed>] | resume-coupling <terrain> <seed> <count> <c1 state> <gate A receipt> <move bound ms> <capture dir>"
        ),
    }
}

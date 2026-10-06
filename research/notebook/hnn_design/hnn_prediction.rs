//! **`hnn_prediction`: step 1's harness on known-truth terrain** (THE_REBUILD U6, step 1; #73, #148,
//! #63). Its modes are the `executed …` subcommands of `hnn_executed_loop.rs` (the release read on a
//! terrain and the terrain's own counts), of `hnn_keys_loop.rs` (lane B's key location and its
//! deposit, lane C's pair diagnostic and the text path), of `hnn_repair_loop.rs` (the first repair
//! terrain) and of `hnn_text_repair.rs` (text repair by local keys), whose headers state each mode
//! and its pins; this file holds the declaration they share and dispatches to them. Committed
//! commands run once in release, never a test.
//!
//! ```sh
//! cargo run --release -p holonics --example hnn_prediction -- executed evaluate <terrain> <seed> <count> <out> <label[=state]>…
//! cargo run --release -p holonics --example hnn_prediction -- executed counts <terrain> <training seed> <count> <validation seed> <count> <out>
//! cargo run --release -p holonics --example hnn_prediction -- executed keys <terrain> <training seed> <count> <out>
//! cargo run --release -p holonics --example hnn_prediction -- executed keys-probe <terrain> <training seed> <count> <scale> <out>
//! cargo run --release -p holonics --example hnn_prediction -- executed pair-members <terrain> <seed> <count> <state>
//! cargo run --release -p holonics --example hnn_prediction -- executed text <cut> <private out dir> <pin> <dev|run> [<state> [<from> <to>]]
//! cargo run --release -p holonics --example hnn_prediction -- executed text-repair <cut> <private out dir> <pin> <dev|run>
//! cargo run --release -p holonics --example hnn_prediction -- executed repair <terrain> <A|B> <seed> <count> <out>
//! cargo run --release -p holonics --example hnn_prediction -- executed physical-repair <A|B> <count> <aperture> <out> <pin> <terrain>=<seed>…
//! cargo run --release -p holonics --example hnn_prediction -- executed physical-receive <A|B|one> <count> <aperture> <out> <pin> <terrain>=<seed>…
//! cargo run --release -p holonics --example hnn_prediction -- executed physical-learn <measure|held> <teaching count> <probe count> <out> <pin> <terrain>=<teaching seed>:<probe seed>…
//! ```
//!
//! [definition; agent-inferred, the order pin and the bank pin] **The declaration**
//! ([`order_declared`]), fixed by the September 29 pins for the reference modes. The physical
//! acquisition consumer declares its shorter section in `hnn_physical_receive::learn`:
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
//! - **The order-2 terrain**: a request of `n` cells drawn uniformly from 4 symbols, its target the
//!   continuation `x_t = x_(t−2) + 1 (mod 4)` over the `m` stations; the alternation and the line
//!   beside it. The loop's `terrain_pairs` reads them from the library's generator
//!   (`holarchy::terrain::KnownTruth::cyclic`, moved October 5); only the terrain computes truth.
//!
//! The modes before the executed comparison (`copy`, `moire`, `divergence`, `order2`, `pumped`,
//! `text`, `probe`, `develop`: native generation, the order repair, the bank's generation and
//! learning path, the pumped receiving ring) and the executed loop's `face` arm were retired on
//! September 30 (THE_REBUILD U6, batch N2); their source is at commit `7ca300bb`. The certified
//! descent's modes and loop 1c's (`move`, `train`, `witness`, `coupling`, `represent`, `run`,
//! `kinetic`, `joined` and their read-only diagnostics) retired with `hnn::executed`'s comparison
//! and move on October 5 (the library spine's S2); their source is at commit `9078f103`.
//!
//! [definition; agent-inferred, October 5; THE_MACHINE guard 22] **A run's limits are its pin's.**
//! Every mode bounded in time names a committed pin (`exterior::Pin`) where it took a deadline or a
//! bound in milliseconds: the pin holds the deadline, the unit bound and the thread budget with
//! their projection, and is refused when missing, uncommitted, changed since its commit or
//! committed twice. `text` reads its unit bound there; `text` and `text-repair`, which have no
//! deadline check of their own, stop at the pinned deadline. Counts that declare the read stay its
//! arguments.

#[path = "exterior.rs"]
mod exterior;
#[path = "hnn_executed_loop.rs"]
mod executed_loop;
#[path = "hnn_keys_loop.rs"]
mod keys_loop;
#[path = "hnn_repair_loop.rs"]
mod repair_loop;
#[path = "hnn_physical_receive.rs"]
mod physical_receive;
#[path = "hnn_text_repair.rs"]
mod text_repair;
#[path = "hnn_transport_loop.rs"]
mod transport_loop;

use std::collections::BTreeMap;
use std::time::Instant;

use holonics::compression::landmark::context::StopPrior;
use holonics::geometry::RatVec3;
use holonics::geometry::screw::ScrewGenerator;
use holonics::hnn::Encoded;
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
use num_traits::Zero;

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
    declare_with_offsets(declared, Vec::new())
}

/// The same physical chain with an explicitly declared finite family of source pair contacts.
/// Offsets are geometry, never a located task map or an expected class.
fn declare_with_offsets(declared: &Declared, offsets: Vec<usize>) -> Field {
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
            offsets,
            alphabet: declared.alphabet,
            step: Rat::from_integer(1.into()),
            exponent_grain: 1,
            receivers: vec![ReceiverDeclaration {
                ring: 0,
                aperture: declared.words * declared.span + 1,
                tolerance: rat(TOLERANCE.0, TOLERANCE.1),
                depth: 1,
                prior: StopPrior::half(),
                mass: 1,
                base: holonics::compression::landmark::context::BaseMeasure::Even,
                receiving_prior: 0,
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

/// **A request's moment**, ingested from rest (past any carry-out: the moment's own law continues);
/// the request enters encoded (THE_MACHINE guard 9).
fn ingest(field: &Field, request: &Encoded) -> (Current, SourceMoment) {
    let mut current = Current::at_rest(field);
    let mut moment = SourceMoment::open(field, &current);
    let mut fed = 0;
    while fed < request.len() {
        fed += moment
            .ingest(
                field,
                &mut current,
                &request.part(fed..request.len()).expect("a part of the request"),
            )
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
/// unchanged, `p = 5/8` (its lock interval on unit cells; the development reads at `p = 5/8` and
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

/// **The run's pin** (module header, guard 22): read, launched from the process's clock (`arm` for
/// a mode with no deadline check of its own), and its thread budget installed as the host's pool
/// before any parallel read.
fn pinned(path: &str, command: &str, clock: Instant, arm: bool) -> exterior::Pin {
    let pin = exterior::Pin::read(path, command);
    pin.launch(clock, arm);
    rayon::ThreadPoolBuilder::new()
        .num_threads(pin.threads())
        .build_global()
        .expect("the pinned thread budget is the host's first pool");
    pin
}

fn main() {
    let clock = Instant::now();
    let arguments: Vec<String> = std::env::args().collect();
    match (arguments.get(1).map(String::as_str), arguments.get(2).map(String::as_str)) {
        (Some("executed"), Some("evaluate")) => executed_loop::evaluate(
            &arguments[3],
            arguments[4].parse().expect("a seed"),
            arguments[5].parse().expect("a count"),
            &arguments[6],
            &arguments[7..],
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
        // Lane B: the pair menu along the training passage and the located pair's deposit
        // (research/records/2026-10-05_LOCATED_KEYS_BECOME_THE_SOURCE_PORTS_PAIR_COMPONENT.md).
        (Some("executed"), Some("keys")) => keys_loop::keys(
            &arguments[3],
            arguments[4].parse().expect("a training seed"),
            arguments[5].parse().expect("a training count"),
            &arguments[6],
        ),
        // Lane C: the pair storage's members along the target's trajectory (a diagnostic,
        // research/records/2026-10-05_THE_RELEASE_READS_THE_LOCATED_PAIR_ON_EQUAL_MATERIAL.md).
        (Some("executed"), Some("pair-members")) => keys_loop::pair_members(
            &arguments[3],
            arguments[4].parse().expect("a seed"),
            arguments[5].parse().expect("a count"),
            &arguments[6],
        ),
        // [historical; retired October 5] Lane B's key location and lane C's release on a text cut
        // through the byte chart: its result is THE_MACHINE guard 9's refusal (`keys_loop::text`).
        (Some("executed"), Some("text")) => {
            pinned(&arguments[5], "executed text", clock, true);
            keys_loop::text(&arguments[3])
        }
        // The first repair terrain: the located pair restricts the erased cells from both sides
        // (research/records/2026-10-05_REPAIR_BY_REFLECTION_THE_LOCATED_PAIR_RESTRICTS_THE_ERASED_CELLS_FROM_BOTH_SIDES.md).
        (Some("executed"), Some("repair")) => repair_loop::repair(
            &arguments[3],
            &arguments[4],
            arguments[5].parse().expect("a seed"),
            arguments[6].parse().expect("a count"),
            &arguments[7],
        ),
        // The physical repair: the damaged section through the field's own motion
        // (research/records/2026-10-05_THE_PHYSICAL_REPAIR_RUNS_THE_DAMAGED_SECTION_THROUGH_THE_FIELD_AND_HOLDS_WHAT_NO_CERTIFIED_DOMAIN_DECIDES.md).
        (Some("executed"), Some("physical-repair")) => {
            pinned(&arguments[7], "executed physical-repair", clock, true);
            repair_loop::physical(
                &arguments[3],
                arguments[4].parse().expect("a count"),
                arguments[5].parse().expect("an aperture"),
                &arguments[6],
                &arguments[8..],
            )
        }
        // Continuing native reception; its own pin and whole-section observed partition.
        (Some("executed"), Some("physical-receive")) => {
            let pin = pinned(&arguments[7], "executed physical-receive", clock, true);
            physical_receive::run(
                &arguments[3],
                arguments[4].parse().expect("a count"),
                arguments[5].parse().expect("an aperture"),
                &arguments[6],
                &arguments[8..],
                &pin,
            )
        }
        (Some("executed"), Some("physical-learn")) => {
            let pin = pinned(&arguments[7], "executed physical-learn", clock, true);
            physical_receive::learn(
                &arguments[3],
                arguments[4].parse().expect("a teaching count"),
                arguments[5].parse().expect("a probe count"),
                &arguments[6],
                &arguments[8..],
                &pin,
            )
        }
        // Text repair by local keys glued on overlaps
        // (research/records/2026-10-05_TEXT_REPAIR_BY_LOCAL_KEYS_GLUED_ON_OVERLAPS.md).
        (Some("executed"), Some("text-repair")) => {
            pinned(&arguments[5], "executed text-repair", clock, true);
            text_repair::run(&arguments[3])
        }
        // The located transport: each occurrence steps the rings by its located advance
        // (research/records/2026-10-05_THE_LOCATED_TRANSPORT_EACH_OCCURRENCE_STEPS_THE_RINGS_BY_ITS_LOCATED_ADVANCE.md).
        (Some("executed"), Some("transport")) => transport_loop::transport(
            arguments[3].parse().expect("a seed"),
            arguments[4].parse().expect("a count of read keys"),
            arguments[5].parse().expect("a length"),
            &arguments[6],
            arguments.get(7).map(String::as_str) == Some("locate"),
        ),
        (Some("executed"), Some("keys-probe")) => keys_loop::keys_probe(
            &arguments[3],
            arguments[4].parse().expect("a training seed"),
            arguments[5].parse().expect("a training count"),
            &arguments[6],
            &arguments[7],
        ),
        _ => panic!(
            "executed evaluate <terrain> <seed> <count> <out> <label[=state]>… | counts <terrain> <training seed> <count> <validation seed> <count> <out> | keys <terrain> <training seed> <count> <out> | keys-probe <terrain> <training seed> <count> <scale> <out> | pair-members <terrain> <seed> <count> <state> | text <cut> <out dir> <pin> <dev|run> [<state> [<from> <to>]] | text-repair <cut> <out dir> <pin> <dev|run> | repair <terrain> <A|B> <seed> <count> <out> | physical-repair <A|B> <count> <aperture> <out> <pin> <terrain>=<seed>…"
        ),
    }
}

//! **The HNN's campaign-1 measurements in the exact host reference** (rebuild step 4, #73, campaign
//! 1; design "Step 4 design: the HNN law", (d) and (f)): the notebook's receipts, each a committed
//! command run once in release. Three modes:
//!
//! ```sh
//! cargo run --release -p holonics --example hnn_lattice_growth -- growth chain 128 declared
//! cargo run --release -p holonics --example hnn_lattice_growth -- growth campaign 40 declared
//! cargo run --release -p holonics --example hnn_lattice_growth -- equality chain 8 declared
//! cargo run --release -p holonics --example hnn_lattice_growth -- equality chain 32 declared
//! cargo run --release -p holonics --example hnn_lattice_growth -- equality chain 32 normal
//! cargo run --release -p holonics --example hnn_lattice_growth -- equality campaign 8 declared
//! cargo run --release -p holonics --example hnn_lattice_growth -- openness configurations
//! cargo run --release -p holonics --example hnn_lattice_growth -- openness uniform
//! cargo run --release -p holonics --example hnn_lattice_growth -- openness cut
//! ```
//!
//! [established-bounded; measured] **`growth`** runs campaign 1's exposure protocol (keys on each
//! aeon's crib, a refine and compare per receiving window, every return deposited, the aeon
//! boundary at the joint clock's carry-out) and prints the constitution's exact bits after each
//! deposit, split into the lattice entries, the carried remainders and the solved charts
//! (`hnn::CarrierBits`), with the widest carried remainder, the deposit's released residuals and
//! their bits (`DepositReading::{released, released_bits}`), the entries whose lattice coordinate
//! moved (`DepositReading::stepped`) and the wall time of each refine, compare and deposit, with the
//! projected wall time of the field's whole exposure (`⌈n*/A⌉` windows at the measured means). An
//! optional fifth argument is the number of aeons (default 6) at whose boundary the admitted
//! reading is also read at the carried trajectory `Θ + r`, to measure what the carried remainders
//! move at the receiver (the collapse releases none of them).
//!
//! [established-bounded; measured] **`equality`** is the receipt that the integral chart changes no
//! value (the protocol: "a check that an optimization changes no value runs once on the real
//! case"). At every deposit it recomputes each update termwise, over `Rat` alone: each prox law's
//! `ΔH = Σ w f fᵀ` and `ΔW = γ Σ w g (X̂ f)ᵀ`; the receiving map's exogenous law (Decision 26)
//! `ΔH = Σ w f fᵀ`, `ΔB = Σ w χ fᵀ` and `ΔW = Σ w (χ − W f)(X̂ f)ᵀ`, with `χ = χ_R(T)` the target's
//! code face each sample carries; each factor family's `Δh_x = Σ w|f|²` and `Δx = (η_x / h_x') G_x`
//! (the product `rate_times` reads by Euclid's remainder), and the receiving parametron's bound
//! harmonic coordinate by the same law, `Δh_x = energy` and `Δh_R = (η_x / h_x') · gradient`. It
//! checks the carry's accounting on every carried entry of the constitution (`W`, `H` and `B`, `h_R`
//! and its statistic included), `x' + r' + e = x + r + Δ` (Lean
//! `HNN/LatticeDeposit.carry_accounting`), which holds exactly when the published update is the
//! termwise one. It checks each normal law's solved chart against its certificate: the exact left
//! residual `‖1 − X̂H‖∞` is at most the chart's certified `δ` (Decision 24, Lean
//! `HNN/LatticeWord.rounded_refinement_certificate_left`). At the exogenous locus it checks the law's
//! exact receipt `(W'H' − B') − (WH − B) = −(T − WF)(1 − X̂H')` at the termwise step, `T − WF` read
//! as matrices; the chart term at the carried Gram within the released bound
//! `δ Σ_t |w| ‖χ_t − W f_t‖∞ ‖f_t‖₁`, which equals the deposit's `ChartReading::released`; and the
//! reading's `‖W'H' − B'‖∞` and prior weight `tr(X̂)/n` (`ExogenousReading`), each recomputed.
//!
//! [established-bounded; measured] **`openness`** reads campaign 1's declared field (review C2): the
//! least source-to-receiver path attenuation `2^(−Σ_a β_a Q_a / 2)` within the receiver's last
//! epoch against its grain `1/L_R`, over every phase configuration of the four rings
//! (`configurations`: `5·7·11·13 = 5,005`, pitch 0 so the windings do not enter), at each receiving
//! window of `n*` uniform bytes (`uniform`: SplitMix64 from seed 0), and at each receiving window of
//! the pinned cut (`cut`).
//!
//! `chain` is the chain control of the HNN tests (rings of periods 2, 3, 2, `|A| = 4`, a periodic
//! source with one cell in eight drawn); `campaign` is campaign 1's declared field (`|A| = 256`)
//! over **the pinned cut**: `docs/plans/THE_REBUILD.md` at commit [`CUT_COMMIT`] as UTF-8 bytes, read
//! by `git show` (171,754 bytes), never the live file. `declared` runs the declared steps
//! (`γ_U = 1`, `η_x = 1/2`); `normal` turns the factor steps off (`η_x = 0`). Every value in a run
//! is exact; the only integers outside the law are the milliseconds. No decimal is printed (a
//! decimal is a collapse): a logit move is its exact ratio in grains with its integer quotient and
//! remainder, and its reading at the receiver's grain `L_R` (`GrainCell::of`: carry, phase class
//! and exact fibre `< 1/L_R`); a mean of milliseconds is the integer quotient with its remainder.

use std::collections::BTreeMap;
use std::time::Instant;

use holonics::geometry::RatVec3;
use holonics::geometry::screw::ScrewGenerator;
use holonics::hnn::constitution::{FactorGradient, LinearLocus};
use holonics::hnn::field::{ConstitutionRead, CribDeclaration, ReceiverDeclaration};
use holonics::hnn::pending::PendingRatio;
use holonics::hnn::propagation::path_attenuation;
use holonics::hnn::receiving::GrainCell;
use holonics::hnn::reference::one_hot;
use holonics::hnn::{
    Carrier, Constitution, ContactDeclaration, Current, Deposit, ExecutionPort, Field,
    FieldDeclaration, Locus, NormalLaw, Reference, RingDeclaration, Steps,
};
use holonics::ratio::{Rat, integer, rat};
use num_bigint::BigInt;
use num_traits::{One, Signed, Zero};

/// **The pinned campaign cut**: the commit whose `docs/plans/THE_REBUILD.md` is the campaign
/// field's cut (the last commit that changed the file before campaign 1's measurements).
const CUT_COMMIT: &str = "fed5488ce70eb5ffbc90f2f03d23638be9d69189";
const CUT_PATH: &str = "docs/plans/THE_REBUILD.md";

/// An exact rational: an integer, `n/2^e` on a wide dyadic denominator, `n/(2^e·m)` on a wide
/// denominator with a power-of-two factor, or `n/d`.
fn exact(value: &Rat) -> String {
    let denominator = value.denom().magnitude();
    if denominator.is_one() {
        return value.numer().to_string();
    }
    let twos = denominator.trailing_zeros().unwrap_or(0);
    let odd = denominator >> twos;
    if denominator.bits() <= 16 {
        format!("{}/{}", value.numer(), denominator)
    } else if odd.is_one() {
        format!("{}/2^{twos}", value.numer())
    } else if twos > 0 {
        format!("{}/(2^{twos}·{odd})", value.numer())
    } else {
        format!("{}/{}", value.numer(), denominator)
    }
}

/// An exact ratio, reduced, with its integer quotient and remainder: `n/d (q rem r over d)`.
fn ratio(value: &Rat) -> String {
    if value.is_integer() {
        return value.numer().to_string();
    }
    let quotient = value.floor().to_integer();
    let remainder = value.numer() - &quotient * value.denom();
    format!(
        "{} ({quotient} rem {remainder} over {})",
        exact(value),
        value.denom()
    )
}

/// **A reading at the grain** `L` (`GrainCell::of`): `value = n + k/L + ε`, the carry `n`, the
/// phase class `k ∈ ℤ/L` and the unresolved fibre `0 ≤ ε < 1/L`, each exact.
fn reading(value: &Rat, grain: u64) -> String {
    let cell = GrainCell::of(value, grain);
    format!(
        "{} + {}/{grain} + ε, ε = {} < 1/{grain}",
        cell.carry,
        cell.phase,
        exact(&cell.fibre)
    )
}

/// A mean of whole milliseconds over a count: the integer quotient with its remainder.
fn mean(total: u128, count: usize) -> String {
    let count = count as u128;
    match (total.checked_div(count), total.checked_rem(count)) {
        (Some(quotient), Some(remainder)) => format!("{quotient} rem {remainder} over {count}"),
        _ => "-".to_string(),
    }
}

const CIRCLE: [(i64, i64); 16] = [
    (8, 1),
    (7, 4),
    (4, 7),
    (1, 8),
    (-1, 8),
    (-4, 7),
    (-7, 4),
    (-8, 1),
    (-8, -1),
    (-7, -4),
    (-4, -7),
    (-1, -8),
    (1, -8),
    (4, -7),
    (7, -4),
    (8, -1),
];

fn ring(period: u64, lock: Vec<u64>) -> RingDeclaration {
    RingDeclaration {
        period,
        screw: ScrewGenerator::new(RatVec3::from_i64(0, 0, 1), RatVec3::zero()),
        placements: (0..period as usize)
            .map(|node| RatVec3::from_i64(CIRCLE[node].0, CIRCLE[node].1, 0))
            .collect(),
        lock,
        reflector: (0..period)
            .map(|p| ((period - p) % period) as usize)
            .collect(),
        admittance: integer(2),
        initial: 0,
    }
}

fn contact(from: usize, to: usize, nodes: usize, exponent: i64) -> ContactDeclaration {
    ContactDeclaration {
        from,
        to,
        channel: (0..nodes).map(|node| (node, node)).collect(),
        admittance: integer(2),
        exponent: integer(exponent),
    }
}

/// The chain control of the HNN tests (`tests/learning.rs::chain`).
fn chain() -> Field {
    Field::declare(
        FieldDeclaration {
            rings: vec![ring(2, vec![0]), ring(3, vec![0]), ring(2, vec![])],
            contacts: vec![contact(0, 1, 2, 2), contact(1, 2, 2, 0)],
            loops: Vec::new(),
            sources: vec![0],
            offsets: vec![1],
            alphabet: 4,
            step: integer(1),
            exponent_grain: 1,
            receivers: vec![ReceiverDeclaration {
                ring: 2,
                aperture: 2,
                tolerance: rat(1, 16),
            }],
            crib: CribDeclaration {
                window: 16,
                offset: 1,
            },
            population: 1 << 20,
            lattice: Default::default(),
        }
        .by_lattice_rule(),
    )
    .expect("the chain control")
}

/// SplitMix64, as the tests' `Draw`.
struct Draw(u64);

impl Draw {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }
}

/// The tests' periodic source with one cell in eight drawn (`tests/reference.rs::source`).
fn periodic(length: usize, seed: u64) -> Vec<usize> {
    let mut draw = Draw(seed);
    (0..length)
        .map(|k| {
            if draw.next().is_multiple_of(8) {
                (draw.next() % 4) as usize
            } else {
                [0, 1, 2, 1][k % 4]
            }
        })
        .collect()
}

/// The pinned cut's bytes, read from the repository's history at [`CUT_COMMIT`]. The notebook's
/// exterior boundary reads it (guard 7 bans a file or a process inside the machinery, never at an
/// exterior reader).
#[allow(clippy::disallowed_types, clippy::disallowed_methods)]
fn pinned_cut() -> Vec<u8> {
    let output = std::process::Command::new("git")
        .args(["show", &format!("{CUT_COMMIT}:{CUT_PATH}")])
        .output()
        .expect("run from the repository: git show reads the pinned cut");
    assert!(output.status.success(), "git show {CUT_COMMIT}:{CUT_PATH}");
    output.stdout
}

/// The declared field and its cut, with the cut's name.
fn field_and_cut(which: &str) -> (Field, Vec<usize>, String) {
    match which {
        "campaign" => {
            let text = pinned_cut();
            let name = format!("{CUT_COMMIT}:{CUT_PATH} ({} bytes)", text.len());
            let field = Field::declare(FieldDeclaration::campaign_one(text.len() as u64))
                .expect("campaign 1's declared field");
            (field, text.into_iter().map(usize::from).collect(), name)
        }
        _ => (
            chain(),
            periodic(1 << 16, 81),
            "the chain control's periodic source, seed 81".to_string(),
        ),
    }
}

fn steps_of(name: &str) -> Steps {
    match name {
        "normal" => Steps {
            proxy: integer(1),
            factor: integer(0),
        },
        _ => Steps::campaign_one(),
    }
}

fn main() {
    let arguments: Vec<String> = std::env::args().collect();
    let argument = |index: usize, default: &'static str| -> String {
        arguments
            .get(index)
            .cloned()
            .unwrap_or_else(|| default.to_string())
    };
    match argument(1, "").as_str() {
        "growth" => growth(
            &argument(2, "chain"),
            argument(3, "128").parse().expect("a deposit count"),
            &steps_of(&argument(4, "declared")),
            argument(5, "6").parse().expect("an aeon count"),
        ),
        "equality" => equality(
            &argument(2, "chain"),
            argument(3, "32").parse().expect("a deposit count"),
            &steps_of(&argument(4, "declared")),
        ),
        "openness" => openness(&argument(2, "configurations")),
        _ => println!(
            "usage: hnn_lattice_growth growth|equality <chain|campaign> <deposits> <declared|normal> | openness <configurations|uniform|cut>"
        ),
    }
}

// -------------------------------------------------------------------------------------------
// openness

/// **The source-to-receiver path's openness** (review C2) on campaign 1's declared field.
fn openness(over: &str) {
    let open_at = |field: &Field, lift: &[BigInt]| -> bool {
        let receiver = &field.receivers()[0];
        let hops = field
            .first_epoch(receiver.ring)
            .expect("a reached receiver")
            + receiver.aperture
            - 1;
        let grain = (receiver.tolerance.recip().ceil().to_integer())
            .try_into()
            .expect("a grain fits a machine word");
        path_attenuation(field, lift, receiver.ring, hops, grain)
            .expect("a path reading")
            .open
    };
    let windows = |field: &Field, cells: &[usize]| -> (u64, u64) {
        let aperture = field.receivers()[0].aperture;
        let mut current = Current::at_rest(field);
        let (mut open, mut windows) = (0u64, 0u64);
        for (position, &code) in cells.iter().enumerate() {
            if position % aperture == 0 {
                windows += 1;
                open += u64::from(open_at(field, current.lift()));
            }
            current.step(field, code).expect("a cell of the chart");
        }
        (open, windows)
    };
    match over {
        "configurations" => {
            let field = Field::declare(FieldDeclaration::campaign_one(6_148))
                .expect("campaign 1's declared field at n*");
            let periods: Vec<u64> = field.rings().iter().map(|ring| ring.period()).collect();
            let (mut open, mut all) = (0u64, 0u64);
            let mut lift = vec![0u64; periods.len()];
            loop {
                let point: Vec<BigInt> = lift.iter().map(|x| BigInt::from(*x)).collect();
                all += 1;
                open += u64::from(open_at(&field, &point));
                let mut ring = 0;
                while ring < periods.len() {
                    lift[ring] += 1;
                    if lift[ring] < periods[ring] {
                        break;
                    }
                    lift[ring] = 0;
                    ring += 1;
                }
                if ring == periods.len() {
                    break;
                }
            }
            println!(
                "campaign 1's field: the path is open at {open} of its {all} phase configurations"
            );
        }
        "uniform" => {
            let field = Field::declare(FieldDeclaration::campaign_one(6_148))
                .expect("campaign 1's declared field at n*");
            let n = field.capacity().n_star() as usize;
            let mut draw = Draw(0);
            let cells: Vec<usize> = (0..n).map(|_| (draw.next() % 256) as usize).collect();
            let (open, windows) = windows(&field, &cells);
            println!(
                "campaign 1's field over n* = {n} uniform bytes (SplitMix64 from seed 0): the path is open on {open} of {windows} receiving windows"
            );
        }
        _ => {
            let (field, cells, name) = field_and_cut("campaign");
            let (open, windows) = windows(&field, &cells);
            println!(
                "campaign 1's field over {name}: the path is open on {open} of {windows} receiving windows"
            );
        }
    }
}

// -------------------------------------------------------------------------------------------
// the exposure's runs

/// One exposure step's deposit: the constitution before it, the staged deposit, the constitution
/// after it and its reading.
struct Deposited<'a> {
    before: &'a Constitution,
    deposit: &'a Deposit,
    after: &'a Constitution,
    reading: &'a holonics::hnn::constitution::DepositReading,
}

/// **Campaign 1's exposure protocol**, every return deposited, calling `on_deposit` after each
/// deposit, `on_boundary` at each aeon boundary before `close_aeon` (with the boundary's index), and
/// `after_boundary` with its reading and the boundary.
fn expose<T>(
    field: &Field,
    cells: &[usize],
    steps: &Steps,
    deposits: usize,
    mut on_deposit: impl FnMut(usize, Deposited<'_>, [u128; 3]),
    mut on_boundary: impl FnMut(usize, &holonics::hnn::Resident, &holonics::hnn::MomentId) -> T,
    mut after_boundary: impl FnMut(usize, usize, T, &holonics::hnn::AeonBoundary),
) -> (usize, usize) {
    let reference = Reference::new(64, steps.clone(), u64::MAX);
    let mut resident = reference
        .mount(field, &Current::at_rest(field))
        .expect("mount");
    let phases = resident.admitted()[0].clone();
    let family = resident.admitted().to_vec();
    let aperture = phases.aperture();
    let crib = field.crib();
    // Keys are located at each boundary from the crib that closed the aeon: its last cells, already
    // read (the port refuses any other crib).
    let locate = |resident: &mut holonics::hnn::Resident, start: usize, at: usize| {
        let from = at.saturating_sub(crib.window).max(start);
        if at > from + crib.offset {
            reference
                .locate_keys(resident, &one_hot(&cells[from..at]), crib.offset)
                .expect("keys");
        }
    };
    let mut aeon_start = 0usize;
    let (moment, _) = reference.ingest(&mut resident, None, &[]).expect("open");
    let (mut position, mut done, mut boundaries) = (0usize, 0usize, 0usize);
    while done < deposits && position + aperture <= cells.len() {
        let window = &cells[position..position + aperture];
        let before = resident.constitution().clone();
        let started = Instant::now();
        let (pending, _) = reference
            .refine(&mut resident, &moment, &phases)
            .expect("refine");
        let refined = started.elapsed().as_millis();
        let started = Instant::now();
        let (staged, compared) = reference
            .compare(&mut resident, pending, &one_hot(window))
            .expect("compare");
        let deposit = compared.deposit.into_present().expect("a staged deposit");
        let compared = started.elapsed().as_millis();
        let started = Instant::now();
        let reading = reference
            .deposit(&mut resident, staged)
            .expect("the deposit is admitted under an open budget")
            .deposit
            .into_present()
            .expect("a deposit reading");
        let deposited = started.elapsed().as_millis();
        done += 1;
        on_deposit(
            done,
            Deposited {
                before: &before,
                deposit: &deposit,
                after: resident.constitution(),
                reading: &reading,
            },
            [refined, compared, deposited],
        );
        let mut fed = 0;
        while fed < window.len() {
            let (_, ingested) = reference
                .ingest(&mut resident, Some(&moment), &one_hot(&window[fed..]))
                .expect("ingest");
            let ingested = ingested.forward.into_present().expect("ingest returns");
            fed += ingested.cells;
            if ingested.carry_out {
                let read = on_boundary(boundaries, &resident, &moment);
                let closed = reference
                    .close_aeon(&mut resident, &family)
                    .expect("the boundary");
                boundaries += 1;
                after_boundary(
                    boundaries,
                    done,
                    read,
                    &closed.forward.into_present().expect("a boundary"),
                );
                locate(&mut resident, aeon_start, position + fed);
                aeon_start = position + fed;
            }
        }
        position += aperture;
    }
    (done, boundaries)
}

/// **The growth run** (module header).
fn growth(which: &str, deposits: usize, steps: &Steps, graded: usize) {
    let (field, cells, name) = field_and_cut(which);
    println!(
        "field {which} over {name}; steps gamma = {}, eta = {}; lattices {:?}",
        steps.proxy,
        steps.factor,
        field
            .lattices()
            .iter()
            .map(|(locus, lattice)| format!("{locus:?}: {}", lattice.exponent()))
            .collect::<Vec<_>>()
    );
    let initial = Constitution::initial(&field, steps.clone(), u64::MAX)
        .expect("the declared constitution")
        .carrier_bits();
    println!(
        "deposit\tbits\tentries\tremainders\tsolved\tcarried\twidest\treleased\treleased_bits\tstepped\tupdate_bits\trefine_ms\tcompare_ms\tdeposit_ms\n0\t{}\t{}\t{}\t{}\t0\t0\t0\t0\t0\t-\t-\t-\t-",
        initial.total(),
        initial.entries,
        initial.remainders,
        initial.solved
    );
    let (mut released_total, mut released_bits_total, mut widest_ever) = (0usize, 0u64, 0u64);
    let mut totals = [0u128; 3];
    let mut last: Option<Constitution> = None;
    let clock = Instant::now();
    let (done, boundaries) = expose(
        &field,
        &cells,
        steps,
        deposits,
        |done, step, times| {
            released_total += step.reading.released.len();
            released_bits_total += step.reading.released_bits;
            for (total, time) in totals.iter_mut().zip(times) {
                *total += time;
            }
            let bits = step.after.carrier_bits();
            let carried = step.after.carried_remainders();
            let widest = carried
                .iter()
                .map(|(.., r)| r.numer().bits() + r.denom().bits())
                .max()
                .unwrap_or(0);
            widest_ever = widest_ever.max(widest);
            println!(
                "{done}\t{}\t{}\t{}\t{}\t{}\t{widest}\t{}\t{}\t{}\t{}\t{}\t{}\t{}",
                bits.total(),
                bits.entries,
                bits.remainders,
                bits.solved,
                carried.len(),
                step.reading.released.len(),
                step.reading.released_bits,
                step.reading.stepped,
                step.deposit.bits(),
                times[0],
                times[1],
                times[2]
            );
            last = Some(step.after.clone());
        },
        |index, resident, moment| {
            // What the carried remainders move: the admitted reading at Θ and at the carried
            // trajectory Θ + r, in units of the receiver's grain.
            (index < graded).then(|| {
                let theta = resident.constitution().clone();
                let phases = resident.admitted()[0].clone();
                let pending = PendingRatio::produce(
                    resident.current(),
                    resident.moment(moment).expect("the open moment"),
                    &phases,
                    theta.commit(),
                );
                let (_, faces) = pending.read(&field, &theta).expect("the read at Θ");
                let (_, carried) = pending
                    .read(&field, &theta.with_remainders().expect("Θ + r"))
                    .expect("the read at Θ + r");
                let grain = phases.grain();
                let largest = faces
                    .logits
                    .iter()
                    .flatten()
                    .zip(carried.logits.iter().flatten())
                    .map(|(a, b)| (a - b).abs())
                    .max()
                    .unwrap_or_else(Rat::zero);
                format!(
                    "{} grains; |Δf| at L_R = {grain}: {}",
                    ratio(&(&largest * Rat::from_integer(BigInt::from(grain)))),
                    reading(&largest, grain)
                )
            })
        },
        |index, done, moved: Option<String>, boundary| {
            println!(
                "aeon {index} closed after deposit {done}: released {} loci ({} remainders); bits {} -> {}; the largest logit move to Θ + r is {}",
                boundary.collapse.released.len(),
                boundary.collapse.released_remainders.len(),
                boundary.collapse.bits[0],
                boundary.collapse.bits[1],
                moved.as_deref().unwrap_or("unread")
            );
        },
    );
    if let Some(theta) = &last {
        for (locus, parts) in theta.carrier_bits_by_locus() {
            println!(
                "{locus:?}: entries {} remainders {} solved {}",
                parts.entries, parts.remainders, parts.solved
            );
        }
    }
    // An exposure of `n` cells reads ⌈n / A⌉ windows, each a refine, a compare and a deposit: the
    // capacity's `n*` (the real-cut exposure) and the declared population. The projection is the
    // exact `W · Σ / N` milliseconds, `Σ` the three phases' total over the `N` deposits read.
    let aperture = field.receivers()[0].aperture;
    let cycle: u128 = totals.iter().sum();
    let windows = |cells: u64| (cells as u128).div_ceil(aperture as u128);
    let (capacity, population) = (field.capacity().n_star(), field.population());
    println!(
        "{done} deposits, {boundaries} aeon boundaries, {} ms in all: per refine {} ms, per compare {} ms and per deposit {} ms (quotient rem remainder over the deposits); {released_total} residuals released ({released_bits_total} bits); the widest carried remainder {widest_ever} bits; at these means n* = {capacity} cells ({} windows) project to {} ms and the population's {population} cells ({} windows) to {} ms",
        clock.elapsed().as_millis(),
        mean(totals[0], done),
        mean(totals[1], done),
        mean(totals[2], done),
        windows(capacity),
        mean(windows(capacity) * cycle, done),
        windows(population),
        mean(windows(population) * cycle, done)
    );
}

// -------------------------------------------------------------------------------------------
// the equality receipt

type Entry = (Locus, Carrier, usize);

/// **Every carried entry of a constitution** by locus, carried array and entry, in the carry's own
/// order (`hnn::constitution`: a map or a factor row-major, the slices `(2ρ + side)·n + i`, a
/// family's rows in order, a statistic at entry 0).
fn values(field: &Field, theta: &Constitution) -> BTreeMap<Entry, Rat> {
    let mut out = BTreeMap::new();
    let mut put = |locus: Locus, carrier: Carrier, entries: Vec<Rat>| {
        for (entry, value) in entries.into_iter().enumerate() {
            out.insert((locus, carrier, entry), value);
        }
    };
    let law = |put: &mut dyn FnMut(Locus, Carrier, Vec<Rat>), locus: Locus, law: &NormalLaw| {
        put(locus, Carrier::Map, law.map().entries().to_vec());
        put(locus, Carrier::Gram, law.gram().entries().to_vec());
    };
    for g in 0..field.rings().len() {
        let element = Locus::Element(g);
        law(&mut put, element, theta.contrast_law(g));
        put(
            element,
            Carrier::Passive,
            theta.passive_factor(g).entries().to_vec(),
        );
        put(
            element,
            Carrier::Slices,
            theta
                .slices(g)
                .iter()
                .flat_map(|(u, v)| u.iter().chain(v).cloned())
                .collect(),
        );
        let scales = theta.ring_scales(g);
        put(element, Carrier::PassiveScale, vec![scales[1].clone()]);
        put(element, Carrier::SliceScale, vec![scales[2].clone()]);
        put(
            Locus::Standing(g),
            Carrier::Standing,
            theta.standing(g).to_vec(),
        );
        put(
            Locus::Standing(g),
            Carrier::StandingScale,
            vec![scales[0].clone()],
        );
        if let Some(source) = theta.source_law(g) {
            law(&mut put, Locus::SourcePort(g), source);
            for &offset in field.offsets() {
                let pair = theta.pair_port(g, offset).expect("a declared pair port");
                for (family, rows) in [pair.outputs(), pair.current_reads(), pair.earlier_reads()]
                    .into_iter()
                    .enumerate()
                {
                    put(
                        Locus::SourcePort(g),
                        Carrier::Pair { offset, family },
                        rows.iter().flatten().cloned().collect(),
                    );
                }
            }
            put(
                Locus::SourcePort(g),
                Carrier::PairScale,
                vec![scales[3].clone()],
            );
        }
        if let Some(receiving) = theta.receiving_law(g) {
            // The receiving locus (Decision 26): the exogenous law's `W`, `H` and `B`, and the
            // receiving parametron's bound harmonic coordinate `h_R` with its statistic.
            let locus = Locus::ReceivingMap(g);
            law(&mut put, locus, receiving);
            if let Some(target) = receiving.target() {
                put(locus, Carrier::Target, target.entries().to_vec());
            }
            if let Some(harmonic) = theta.harmonic(g) {
                put(locus, Carrier::Harmonic, harmonic.to_vec());
            }
            if let Some(scale) = theta.harmonic_scale(g) {
                put(locus, Carrier::HarmonicScale, vec![scale.clone()]);
            }
        }
    }
    for a in 0..field.contacts().len() {
        let channel = Locus::Channel(a);
        for (index, factor) in [
            theta.contact_storage(a),
            theta.contact_stiffness(a),
            theta.contact_dissipation(a),
        ]
        .into_iter()
        .enumerate()
        {
            put(channel, Carrier::Factor(index), factor.entries().to_vec());
            put(
                channel,
                Carrier::FactorScale(index),
                vec![theta.contact_scales(a)[index].clone()],
            );
        }
    }
    out
}

fn remainders(theta: &Constitution) -> BTreeMap<Entry, Rat> {
    theta
        .carried_remainders()
        .into_iter()
        .map(|(locus, carrier, entry, r)| ((locus, carrier, entry), r))
        .collect()
}

fn normal_law(theta: &Constitution, locus: LinearLocus) -> &NormalLaw {
    match locus {
        LinearLocus::SourcePort(g) => theta.source_law(g).expect("a source port"),
        LinearLocus::Contrast(g) => theta.contrast_law(g),
        LinearLocus::Receiving(g) => theta.receiving_law(g).expect("a receiving map"),
    }
}

/// `M v`, termwise over `Rat`.
fn apply(matrix: &[Vec<Rat>], vector: &[Rat]) -> Vec<Rat> {
    matrix
        .iter()
        .map(|row| row.iter().zip(vector).map(|(a, b)| a * b).sum())
        .collect()
}

/// `A B`, termwise over `Rat`.
fn product(a: &[Vec<Rat>], b: &[Vec<Rat>]) -> Vec<Vec<Rat>> {
    let columns = b.first().map_or(0, Vec::len);
    a.iter()
        .map(|row| {
            (0..columns)
                .map(|j| {
                    row.iter()
                        .zip(b)
                        .filter(|(x, _)| !x.is_zero())
                        .map(|(x, brow)| x * &brow[j])
                        .sum()
                })
                .collect()
        })
        .collect()
}

/// `A + s B`, termwise over `Rat`.
fn combine(a: &[Vec<Rat>], s: i64, b: &[Vec<Rat>]) -> Vec<Vec<Rat>> {
    let s = integer(s);
    a.iter()
        .zip(b)
        .map(|(x, y)| x.iter().zip(y).map(|(x, y)| x + &s * y).collect())
        .collect()
}

/// `1 − A` for a square `A`.
fn complement(a: &[Vec<Rat>]) -> Vec<Vec<Rat>> {
    a.iter()
        .enumerate()
        .map(|(i, row)| {
            row.iter()
                .enumerate()
                .map(|(j, x)| if i == j { Rat::one() - x } else { -x })
                .collect()
        })
        .collect()
}

/// `‖A‖∞`, the largest absolute row sum.
fn row_norm(a: &[Vec<Rat>]) -> Rat {
    a.iter()
        .map(|row| row.iter().map(Signed::abs).sum::<Rat>())
        .max()
        .unwrap_or_else(Rat::zero)
}

/// [definition] **An exogenous locus's receipt at one deposit** (Decision 26; `NormalLaw::exogenous`),
/// recomputed termwise over `Rat` from the predecessor `(W, H, B)`, the samples and the executed chart
/// `X̂` of the carried `H'`:
///
/// - the law's identity at the exact step `W'_e = W + ΔW`, `H'_e = H + F`, `B'_e = B + T`, with
///   `ΔW = Σ_t w (χ_t − W f_t)(X̂ f_t)ᵀ` read sample by sample and `T − WF` read as matrices:
///   `(W'_e H'_e − B'_e) − (W H − B) = −(T − WF)(1 − X̂ H'_e)`, checked equal entry by entry;
/// - `term`: the executed chart term `‖(T − WF)(1 − X̂H')‖∞` at the carried Gram `H'`, which the
///   chart's certificate `δ` bounds by `released = δ Σ_t |w| ‖χ_t − W f_t‖∞ ‖f_t‖₁` (checked, and
///   `released` checked equal to the deposit's `ChartReading::released`);
/// - `statistic`: the published law's `‖W'H' − B'‖∞`, checked equal to `ExogenousReading::statistic`;
/// - `prior`: `tr(X̂)/n`, checked equal to `ExogenousReading::prior`.
struct Receipt {
    locus: Locus,
    term: Rat,
    released: Rat,
    statistic: Rat,
    prior: Rat,
}

/// **The exogenous step's updates and receipt, termwise** ([`Receipt`]): each sample's
/// `ΔB = w χ fᵀ` and `ΔW = w (χ − W f)(X̂ f)ᵀ` added by entry, then the receipt checked against the
/// deposit's reading.
fn exogenous(
    locus: Locus,
    was: &NormalLaw,
    law: &NormalLaw,
    samples: &[holonics::hnn::constitution::Sample],
    reading: &holonics::hnn::constitution::DepositReading,
    add: &mut impl FnMut(Entry, Rat),
) -> Option<Receipt> {
    let (m, n) = (law.map().rows(), law.map().columns());
    let map = was.map().to_rows();
    let (gram_before, gram_after) = (was.gram().to_rows(), law.gram().to_rows());
    let statistic_before = was.target().expect("an exogenous law carries B").to_rows();
    let solved = law.solved().to_rows();
    let (mut target, mut feature_gram) =
        (vec![vec![Rat::zero(); n]; m], vec![vec![Rat::zero(); n]; n]);
    let mut step = vec![vec![Rat::zero(); n]; m];
    let mut shares = Rat::zero();
    for sample in samples {
        let chi = sample
            .target
            .as_ref()
            .expect("an exogenous sample carries its target face");
        let residual: Vec<Rat> = chi
            .iter()
            .zip(apply(&map, &sample.feature))
            .map(|(chi, read)| chi - read)
            .collect();
        let reach = apply(&solved, &sample.feature);
        for (row, left) in feature_gram.iter_mut().zip(&sample.feature) {
            for (entry, right) in row.iter_mut().zip(&sample.feature) {
                *entry += &sample.weight * left * right;
            }
        }
        for i in 0..m {
            for j in 0..n {
                let b = &sample.weight * &chi[i] * &sample.feature[j];
                target[i][j] += &b;
                add((locus, Carrier::Target, i * n + j), b);
                let w = &sample.weight * &residual[i] * &reach[j];
                step[i][j] += &w;
                add((locus, Carrier::Map, i * n + j), w);
            }
        }
        if sample.feature.iter().any(|x| !x.is_zero()) {
            let widest = residual
                .iter()
                .map(Signed::abs)
                .max()
                .unwrap_or_else(Rat::zero);
            let mass: Rat = sample.feature.iter().map(Signed::abs).sum();
            shares += sample.weight.abs() * widest * mass;
        }
    }
    // The law's identity at the exact step, T − WF read as matrices.
    let innovation = combine(&target, -1, &product(&map, &feature_gram));
    let (next_map, next_gram, next_statistic) = (
        combine(&map, 1, &step),
        combine(&gram_before, 1, &feature_gram),
        combine(&statistic_before, 1, &target),
    );
    let before = combine(&product(&map, &gram_before), -1, &statistic_before);
    let after = combine(&product(&next_map, &next_gram), -1, &next_statistic);
    let chart_term = product(&innovation, &complement(&product(&solved, &next_gram)));
    assert_eq!(
        combine(&after, -1, &before),
        combine(&vec![vec![Rat::zero(); n]; m], -1, &chart_term),
        "{locus:?}: (W'H' − B') − (WH − B) = −(T − WF)(1 − X̂H') at the exact step"
    );
    let chart = reading
        .charts
        .iter()
        .find_map(|(at, chart)| (*at == locus).then_some(chart));
    let Some(chart) = chart else {
        // The window reached nothing at the locus: nothing moved.
        assert!(
            shares.is_zero(),
            "{locus:?}: a reached window reads its chart"
        );
        return None;
    };
    let receipt = chart
        .exogenous
        .as_ref()
        .expect("an exogenous locus's chart reading carries its receipt");
    let released = law.chart().certificate() * &shares;
    assert_eq!(released, chart.released, "{locus:?}: the released bound");
    let term = row_norm(&product(
        &innovation,
        &complement(&product(&solved, &gram_after)),
    ));
    assert!(
        term <= released,
        "{locus:?}: the chart term within its bound"
    );
    let statistic = row_norm(&combine(
        &product(&law.map().to_rows(), &gram_after),
        -1,
        &law.target().expect("an exogenous law carries B").to_rows(),
    ));
    assert_eq!(statistic, receipt.statistic, "{locus:?}: ‖W'H' − B'‖∞");
    let prior = (0..n).map(|i| solved[i][i].clone()).sum::<Rat>() / integer(n as i64);
    assert_eq!(prior, receipt.prior, "{locus:?}: tr(X̂)/n");
    Some(Receipt {
        locus,
        term,
        released,
        statistic,
        prior,
    })
}

/// **One deposit's updates, termwise** (module header), with each normal law's solved chart
/// checked and each exogenous locus's receipt checked against the deposit's reading ([`Receipt`]);
/// returns the updates by entry, the count of solved charts checked by each branch, the exogenous
/// receipts and the count of harmonic steps.
fn termwise(
    before: &Constitution,
    deposit: &Deposit,
    after: &Constitution,
    reading: &holonics::hnn::constitution::DepositReading,
) -> (BTreeMap<Entry, Rat>, [usize; 2], Vec<Receipt>, usize) {
    let steps = after.steps();
    let mut updates: BTreeMap<Entry, Rat> = BTreeMap::new();
    let mut add = |key: Entry, value: Rat| {
        if !value.is_zero() {
            *updates.entry(key).or_insert_with(Rat::zero) += value;
        }
    };
    let mut branches = [0usize; 2];
    let mut receipts = Vec::new();
    for step in deposit.linear() {
        let locus = step.locus.locus();
        let (was, law) = (
            normal_law(before, step.locus),
            normal_law(after, step.locus),
        );
        assert_eq!(
            was.is_exogenous(),
            law.is_exogenous(),
            "{locus:?}: one law across the deposit"
        );
        let (m, n) = (law.map().rows(), law.map().columns());
        let rows = |matrix: holonics::ratio::linear::ExactRatMatrix| matrix.to_rows();
        let (gram_before, gram_after, solved) =
            (rows(was.gram()), rows(law.gram()), rows(law.solved()));
        let mut gram = vec![vec![Rat::zero(); n]; n];
        for sample in &step.samples {
            for (row, left) in gram.iter_mut().zip(&sample.feature) {
                for (entry, right) in row.iter_mut().zip(&sample.feature) {
                    *entry += &sample.weight * left * right;
                }
            }
        }
        // Decision 24: the solved chart is a lattice chart with an exactly certified left residual
        // `‖1 − X̂H‖∞ ≤ δ` within its declared target; the exact Sherman–Morrison and inversion
        // branches are retired.
        let _ = &gram_before;
        let product = rows(law.solved().multiply(&law.gram()).expect("square charts"));
        let residual = (0..n)
            .map(|i| {
                (0..n)
                    .map(|j| {
                        let identity = if i == j { Rat::one() } else { Rat::zero() };
                        (identity - &product[i][j]).abs()
                    })
                    .sum::<Rat>()
            })
            .max()
            .unwrap_or_else(Rat::zero);
        assert!(
            &residual <= law.chart().certificate(),
            "{locus:?}: the solved chart's certificate"
        );
        branches[usize::from(gram_after != gram_before)] += 1;
        for (i, row) in gram.into_iter().enumerate() {
            for (j, value) in row.into_iter().enumerate() {
                add((locus, Carrier::Gram, i * n + j), value);
            }
        }
        if was.is_exogenous() {
            // Decision 26: `ΔB = Σ w χ fᵀ`, `ΔW = Σ w (χ − W f)(X̂ f)ᵀ`, and the law's receipt.
            receipts.extend(exogenous(locus, was, law, &step.samples, reading, &mut add));
            continue;
        }
        for sample in &step.samples {
            let reach = apply(&solved, &sample.feature);
            for (i, covector) in sample.covector.iter().enumerate().take(m) {
                for (j, reached) in reach.iter().enumerate() {
                    add(
                        (locus, Carrier::Map, i * n + j),
                        &steps.proxy * &sample.weight * covector * reached,
                    );
                }
            }
        }
    }
    for step in deposit.factors() {
        let locus = step.gradient.locus();
        let (scale, statistic, families): (Carrier, Rat, Vec<(Carrier, Vec<Rat>)>) =
            match &step.gradient {
                FactorGradient::Passive { ring, gradient } => (
                    Carrier::PassiveScale,
                    after.ring_scales(*ring)[1].clone(),
                    vec![(Carrier::Passive, gradient.entries().to_vec())],
                ),
                FactorGradient::Slices { ring, gradient } => (
                    Carrier::SliceScale,
                    after.ring_scales(*ring)[2].clone(),
                    vec![(
                        Carrier::Slices,
                        gradient
                            .iter()
                            .flat_map(|(u, v)| u.iter().chain(v).cloned())
                            .collect(),
                    )],
                ),
                FactorGradient::Standing { ring, gradient } => (
                    Carrier::StandingScale,
                    after.ring_scales(*ring)[0].clone(),
                    vec![(Carrier::Standing, gradient.clone())],
                ),
                FactorGradient::PairPort {
                    ring,
                    offset,
                    outputs,
                    current,
                    earlier,
                } => (
                    Carrier::PairScale,
                    after.ring_scales(*ring)[3].clone(),
                    [outputs, current, earlier]
                        .into_iter()
                        .enumerate()
                        .map(|(family, rows)| {
                            (
                                Carrier::Pair {
                                    offset: *offset,
                                    family,
                                },
                                rows.iter().flatten().cloned().collect(),
                            )
                        })
                        .collect(),
                ),
                FactorGradient::Storage { contact, gradient }
                | FactorGradient::Stiffness { contact, gradient }
                | FactorGradient::Dissipation { contact, gradient } => {
                    let index = match &step.gradient {
                        FactorGradient::Storage { .. } => 0,
                        FactorGradient::Stiffness { .. } => 1,
                        _ => 2,
                    };
                    (
                        Carrier::FactorScale(index),
                        after.contact_scales(*contact)[index].clone(),
                        vec![(Carrier::Factor(index), gradient.entries().to_vec())],
                    )
                }
            };
        add((locus, scale, 0), step.energy.clone());
        let rate = &steps.factor / statistic;
        for (carrier, gradient) in families {
            for (entry, value) in gradient.iter().enumerate() {
                add((locus, carrier, entry), &rate * value);
            }
        }
    }
    // The receiving parametron's bound harmonic coordinate (Decision 26): the factor step's law at
    // the receiving locus, `h_x' = h_x + energy` and `Δh_R = (η_x / h_x') · gradient`.
    for step in deposit.harmonic() {
        let locus = Locus::ReceivingMap(step.ring);
        add((locus, Carrier::HarmonicScale, 0), step.energy.clone());
        let statistic = after
            .harmonic_scale(step.ring)
            .expect("a receiving ring carries its harmonic statistic");
        let rate = &steps.factor / statistic;
        for (entry, value) in step.gradient.iter().enumerate() {
            add((locus, Carrier::Harmonic, entry), &rate * value);
        }
    }
    (updates, branches, receipts, deposit.harmonic().len())
}

/// **The equality receipt** (module header).
fn equality(which: &str, deposits: usize, steps: &Steps) {
    let (field, cells, name) = field_and_cut(which);
    println!(
        "equality on field {which} over {name}; steps gamma = {}, eta = {}",
        steps.proxy, steps.factor
    );
    let (mut entries, mut solved) = (0usize, [0usize; 2]);
    let (mut receipts, mut harmonic) = (0usize, 0usize);
    // The prior weight's readings in order, to count where it rose (a reading: the chart's
    // certificate and the Gram's carry may move it, `ExogenousReading::prior`).
    let (mut prior, mut rose): (Option<Rat>, usize) = (None, 0);
    let clock = Instant::now();
    let (done, _) = expose(
        &field,
        &cells,
        steps,
        deposits,
        |done, step, _| {
            let (updates, branches, exogenous, steps) =
                termwise(step.before, step.deposit, step.after, step.reading);
            let (was, now) = (values(&field, step.before), values(&field, step.after));
            let (carried, carries) = (remainders(step.before), remainders(step.after));
            let released: BTreeMap<Entry, Rat> = step
                .reading
                .released
                .iter()
                .map(|(locus, carrier, entry, e)| ((*locus, *carrier, *entry), e.clone()))
                .collect();
            let at = |map: &BTreeMap<Entry, Rat>, key: &Entry| {
                map.get(key).cloned().unwrap_or_else(Rat::zero)
            };
            assert_eq!(was.len(), now.len(), "one carried shape");
            for key in updates
                .keys()
                .chain(released.keys())
                .chain(carried.keys())
                .chain(carries.keys())
            {
                assert!(now.contains_key(key), "{key:?} is a carried entry");
            }
            for (key, value) in &now {
                assert_eq!(
                    value + at(&carries, key) + at(&released, key),
                    at(&was, key) + at(&carried, key) + at(&updates, key),
                    "deposit {done}, {key:?}"
                );
            }
            entries += now.len();
            solved[0] += branches[0];
            solved[1] += branches[1];
            receipts += exogenous.len();
            harmonic += steps;
            println!(
                "deposit {done}: {} carried entries equal their termwise accounting ({} updated); solved charts certified: {} on an unmoved Gram, {} on a moved one; harmonic steps {steps}",
                now.len(),
                updates.len(),
                branches[0],
                branches[1]
            );
            for receipt in &exogenous {
                if prior.as_ref().is_some_and(|last| &receipt.prior > last) {
                    rose += 1;
                }
                prior = Some(receipt.prior.clone());
                println!(
                    "  {:?} exogenous receipt: (W'H' − B') − (WH − B) = −(T − WF)(1 − X̂H') at the exact step; the chart term ‖(T − WF)(1 − X̂H')‖∞ at the carried Gram {} ≤ released {}; ‖W'H' − B'‖∞ = {}; prior weight tr(X̂)/n = {}",
                    receipt.locus,
                    exact(&receipt.term),
                    exact(&receipt.released),
                    exact(&receipt.statistic),
                    ratio(&receipt.prior)
                );
            }
        },
        |_, _, _| {},
        |_, _, (), _| {},
    );
    println!(
        "every value equal over {done} deposits: {entries} carried entries checked, {} solved charts certified on an unmoved Gram and {} on a moved one, {receipts} exogenous receipts (the prior weight rose at {rose} of them) and {harmonic} harmonic steps checked, in {} ms",
        solved[0],
        solved[1],
        clock.elapsed().as_millis()
    );
}

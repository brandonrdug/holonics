//! **The HNN's campaign-1 measurements in the exact host reference** (rebuild step 4, #73, campaign
//! 1; design "Step 4 design: the HNN law", (d) and (f)): the notebook's receipts, each a committed
//! command run once in release. Three modes:
//!
//! ```sh
//! cargo run --release -p holonics --example hnn_lattice_growth -- growth chain 128 declared
//! cargo run --release -p holonics --example hnn_lattice_growth -- growth campaign 40 declared
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
//! case"). At every deposit it recomputes each update termwise, over `Rat` alone: each normal law's
//! `ΔH = Σ w f fᵀ` and `ΔW = γ Σ w g (H'⁻¹ f)ᵀ`, each factor family's `Δh_x = Σ w|f|²` and
//! `Δx = (η_x / h_x') G_x` (the product `rate_times` reads by Euclid's remainder), and checks the
//! carry's accounting on every carried entry of the constitution, `x' + r' + e = x + r + Δ`
//! (Lean `HNN/LatticeDeposit.carry_accounting`), which holds exactly when the published update is
//! the termwise one. It checks each normal law's solved chart against its certificate: the exact
//! left residual `‖1 − X̂H‖∞` is at most the chart's certified `δ` (Decision 24, Lean
//! `HNN/LatticeWord.rounded_refinement_certificate_left`). It checks the receiving parametron's
//! landmark deposit exactly (Decision 28, [`landmark_accounting`]): the staged steps are one per
//! target of the window, in cell order, each at its phase's causal address (the resident's active
//! suffix address after the window's earlier targets), and the published tree has passed exactly
//! those cells more, as the reading reports.
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
use holonics::hnn::constitution::LandmarkStep;
use holonics::hnn::constitution::{FactorGradient, LinearLocus};
use holonics::hnn::field::{ConstitutionRead, CribDeclaration, ReceiverDeclaration};
use holonics::hnn::landmark::Letter;
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
                depth: 2,
            }],
            crib: CribDeclaration {
                window: 16,
                offset: 1,
            },
            population: 1 << 16,
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
/// after it and its reading; the receiver's ring, each phase's causal address and the window's
/// targets (Decision 28's landmark deposit reads them).
struct Deposited<'a> {
    before: &'a Constitution,
    deposit: &'a Deposit,
    after: &'a Constitution,
    reading: &'a holonics::hnn::constitution::DepositReading,
    ring: usize,
    addresses: Vec<Vec<Letter>>,
    targets: &'a [usize],
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
        let addresses = phases
            .addresses(
                &resident
                    .address()
                    .truncated(phases.depth())
                    .expect("the receiver's address"),
                window,
            )
            .expect("the window's addresses");
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
                ring: phases.ring(),
                addresses,
                targets: window,
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
                    resident.address(),
                    &phases,
                    theta.commit(),
                )
                .expect("the pending ratio");
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
            law(&mut put, Locus::ReceivingMap(g), receiving);
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

/// **One deposit's updates, termwise** (module header), with each normal law's solved chart
/// checked; returns the updates by entry and the count of solved charts checked by each branch.
fn termwise(
    before: &Constitution,
    deposit: &Deposit,
    after: &Constitution,
) -> (BTreeMap<Entry, Rat>, [usize; 2]) {
    let steps = after.steps();
    let mut updates: BTreeMap<Entry, Rat> = BTreeMap::new();
    let mut add = |key: Entry, value: Rat| {
        if !value.is_zero() {
            *updates.entry(key).or_insert_with(Rat::zero) += value;
        }
    };
    let mut branches = [0usize; 2];
    for step in deposit.linear() {
        let locus = step.locus.locus();
        let (was, law) = (
            normal_law(before, step.locus),
            normal_law(after, step.locus),
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
    (updates, branches)
}

/// **The landmark deposit's exact accounting at one deposit** (Decision 28; Lean
/// `HNN/LandmarkTree.landmark_step`): the staged landmark steps are one per target of the window,
/// in cell order, each at its phase's causal address; the published tree has passed exactly those
/// cells more than its predecessor, and the reading reports them. Returns the steps checked.
fn landmark_accounting(step: &Deposited<'_>) -> usize {
    let expected: Vec<LandmarkStep> = step
        .addresses
        .iter()
        .zip(step.targets)
        .map(|(address, &class)| LandmarkStep {
            ring: step.ring,
            address: address.clone(),
            class,
        })
        .collect();
    assert_eq!(
        step.deposit.landmarks(),
        &expected[..],
        "the staged landmark steps"
    );
    assert_eq!(
        step.reading.landmarks,
        expected.len() as u64,
        "the reading's cells"
    );
    let passed = |theta: &Constitution| {
        theta
            .landmarks(step.ring)
            .expect("the receiving ring's tree")
            .passed()
    };
    assert_eq!(
        passed(step.after),
        passed(step.before) + expected.len() as u64,
        "the tree's passage"
    );
    expected.len()
}

/// **The equality receipt** (module header).
fn equality(which: &str, deposits: usize, steps: &Steps) {
    let (field, cells, name) = field_and_cut(which);
    println!(
        "equality on field {which} over {name}; steps gamma = {}, eta = {}",
        steps.proxy, steps.factor
    );
    let (mut entries, mut solved, mut landmarks) = (0usize, [0usize; 2], 0usize);
    let clock = Instant::now();
    let (done, _) = expose(
        &field,
        &cells,
        steps,
        deposits,
        |done, step, _| {
            let checked = landmark_accounting(&step);
            landmarks += checked;
            let (updates, branches) = termwise(step.before, step.deposit, step.after);
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
            for key in updates.keys().chain(released.keys()) {
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
            println!(
                "deposit {done}: {} carried entries equal their termwise accounting ({} updated); solved charts certified: {} on an unmoved Gram, {} on a moved one; landmark steps {checked} exact at their causal addresses {:?}",
                now.len(),
                updates.len(),
                branches[0],
                branches[1],
                step.addresses
            );
        },
        |_, _, _| {},
        |_, _, (), _| {},
    );
    println!(
        "every value equal over {done} deposits: {entries} carried entries checked, {} solved charts certified on an unmoved Gram and {} on a moved one, {landmarks} landmark steps exact, in {} ms",
        solved[0],
        solved[1],
        clock.elapsed().as_millis()
    );
}

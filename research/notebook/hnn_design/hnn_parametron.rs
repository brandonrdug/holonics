//! **`hnn_parametron`: the parametron re-derived from its constitution** (THE_REBUILD U6; #73, #63).
//! The Floquet certificate on declared pumped rings below and past their bifurcations, and a bank of
//! receiving parametrons reading the relative phase of two spectrally placed cells on known truth.
//! The pin is
//! `research/records/2026-09-29_THE_PARAMETRON_RE_DERIVED_PINNED_BEFORE_ITS_RUNS.md`; the owner is
//! `hnn::ring` (its header, "The parametron re-derived").
//!
//! ```sh
//! cargo run --release -p holonics --example hnn_parametron -- develop
//! cargo run --release -p holonics --example hnn_parametron -- rings
//! cargo run --release -p holonics --example hnn_parametron -- bank
//! ```
//!
//! - **`develop`** (before the pin; never a measurement): the bank's lock window in the pump
//!   strength, bracketed exactly, and the time and memory of a few ring decisions and bank reads on
//!   a development seed, from which the runs are projected.
//! - **`rings`** (acceptance 1): each declared pumped ring's monodromy on the exact law and on the
//!   lattice word's certified charts, decided exactly (`Floquet::decide`); the bifurcation strengths
//!   of the rotating pumps bracketed by exact bisection; the executed balance on every tick of a
//!   passage of each.
//! - **`bank`** (acceptance 2): the declared pair terrain and the order-2 terrain's placed cells,
//!   each pair's relative phase read by the bank, against its truth, beside the controls.
//!
//! Every reading is exact: counts are integers, growths are rationals, and times are integer
//! milliseconds. The run stops at its declared bound and reports a passage past it as incomplete.

#[path = "exterior.rs"]
mod exterior;

use std::time::Instant;

use holonics::hnn::chart::WordLattice;
use holonics::hnn::ring::{
    Floquet, FloquetReading, PumpDeclaration, PumpStep, ReceivingBank, ResonatorMaterial,
    ResonatorOperands, ResonatorRemainders, lock,
};
use holonics::holarchy::terrain::Draw;
use holonics::holon::parametron::Carrier;
use holonics::ratio::linear::ExactRatMatrix;
use holonics::ratio::{GaussianRat, Rat, integer, rat};
use num_traits::{One, Zero};
use rayon::prelude::*;

use exterior::resident_set;

// -------------------------------------------------------------------------------------------
// the declarations (the pin, §2)

/// The port admittance and hop of every declared ring: `Y = 2⁴`, `h = 1`.
fn admittance() -> Rat {
    integer(16)
}

/// The grain of a ring's growth enclosure (acceptance 1): `2^(−8)`.
const RING_GRAIN: u32 = 8;
/// The grain of a bank member's decision (acceptance 2): `2^(−6)`.
const BANK_GRAIN: u32 = 6;
/// The periods of each executed passage whose balance is checked.
const PASSAGE_PERIODS: usize = 8;
/// The receiving ring's period `D = 3·4·5` (the order repair's), and its mode `k = D/4 = 15`, the
/// character of its factor 4: a residue `r` carries the phase `i^(r mod 4)` there.
const PERIOD: usize = 60;
/// The declared pair terrain: its seed and its count.
const PAIR_SEED: u64 = 2_026_092_951;
const PAIRS: usize = 2048;
/// The order-2 terrain's evaluated draws (the order repair's, `hnn_prediction`'s `order_pairs` at
/// `EVALUATE_SEED`): 256 requests of 40 cells and 8 continuation stations over 4 symbols.
const ORDER_SEED: u64 = 2_026_092_902;
const ORDER_REQUESTS: usize = 256;
const ORDER_REQUEST: usize = 40;
const ORDER_STATIONS: usize = 8;
const ORDER_SYMBOLS: usize = 4;
/// The development seed (the `develop` mode only).
const DEVELOP_SEED: u64 = 2_026_092_941;
/// The declared stop of a measured mode, in milliseconds (the pin's projection bound).
const STOP_MS: u128 = 600_000;

/// The quarter turn `i^k`.
fn quarter(k: usize) -> Carrier {
    let (cos, sin) = match k % 4 {
        0 => (1, 0),
        1 => (0, 1),
        2 => (-1, 0),
        _ => (0, -1),
    };
    Carrier::new(integer(cos), integer(sin)).expect("a quarter turn")
}

/// `(a + ib)(c + id)` on unit carriers.
fn compose(first: &Carrier, second: &Carrier) -> Carrier {
    let product = first.as_gaussian().mul(&second.as_gaussian());
    Carrier::new(product.re, product.im).expect("a product of carriers")
}

/// **A cell placed on the receiving mode**: its carrier `i^x` carried to its residue `r` on the
/// ring of period `D`, read on the mode `k = D/4`, where the residue's phase is `i^(r mod 4)`.
fn placed(symbol: usize, residue: usize) -> Carrier {
    compose(&quarter(symbol), &quarter(residue % 4))
}

fn identity(n: usize) -> ExactRatMatrix {
    ExactRatMatrix::identity(n).expect("identity")
}

/// Realify a node form: each entry on the real and on the imaginary coordinate.
fn realify(form: &[Vec<Rat>]) -> ExactRatMatrix {
    let d = form.len();
    ExactRatMatrix::shaped(
        2 * d,
        2 * d,
        (0..2 * d)
            .map(|i| {
                (0..2 * d)
                    .map(|j| {
                        if i % 2 == j % 2 {
                            form[i / 2][j / 2].clone()
                        } else {
                            Rat::zero()
                        }
                    })
                    .collect()
            })
            .collect(),
    )
    .expect("a realified form")
}

/// **One complex node**: `C = I`, `K = I` (`k = 1`), no dissipation but its port.
fn node(pump: Option<PumpDeclaration>) -> ResonatorMaterial {
    ResonatorMaterial::new(
        identity(2),
        identity(2),
        ExactRatMatrix::zero(2, 2).unwrap(),
        pump,
    )
    .expect("the node")
}

/// **The grounded cycle of three**: `C = I`, `K = ½I + L` with `L` the cycle's Laplacian (unit
/// branches), realified; its softest node mode is the constant one, `k₀ = ½`.
fn cycle(pump: Option<PumpDeclaration>) -> ResonatorMaterial {
    let d = 3;
    let form: Vec<Vec<Rat>> = (0..d)
        .map(|i| {
            (0..d)
                .map(|j| {
                    if i == j {
                        rat(1, 2) + integer(2)
                    } else {
                        integer(-1)
                    }
                })
                .collect()
        })
        .collect();
    ResonatorMaterial::new(
        identity(2 * d),
        realify(&form),
        ExactRatMatrix::zero(2 * d, 2 * d).unwrap(),
        pump,
    )
    .expect("the cycle")
}

fn pump(strength: Rat, step: PumpStep) -> PumpDeclaration {
    PumpDeclaration::new(strength, quarter(0), step).expect("a pump")
}

/// The lattice word's declared precisions for these rings: `WordLattice::by_rule(16, 6, 6, 4)`.
fn word_lattice() -> WordLattice {
    WordLattice::by_rule(16, 6, 6, 4)
}

/// **The bank** (the pin, §2): one node, four members at the declared pump phases `a = 1`, steps
/// `i^j` (`j = 0, 1, 2, 3`), strength `p = 5/8`, each modulated by the crossing cells.
fn bank(strength: &Rat) -> ReceivingBank {
    ReceivingBank::new(
        node(None),
        [
            PumpStep::Stand,
            PumpStep::Quarter,
            PumpStep::Half,
            PumpStep::ThreeQuarters,
        ]
        .into_iter()
        .map(|step| pump(strength.clone(), step))
        .collect(),
        admittance(),
        Rat::one(),
        BANK_GRAIN,
    )
    .expect("the bank")
}

fn bank_strength() -> Rat {
    rat(5, 8)
}

// -------------------------------------------------------------------------------------------
// the readings

fn describe(reading: &FloquetReading) -> String {
    match reading {
        FloquetReading::Passive { certificate } => {
            format!("passive, certified at ρ = {}", certificate.growth())
        }
        FloquetReading::Edge {
            certificate,
            on_circle,
        } => format!(
            "the edge: {on_circle} multipliers on the unit circle, none outside; certified at ρ = {}",
            certificate.growth()
        ),
        FloquetReading::Growing { certificate, lower } => format!(
            "growing: spectral radius in [{lower}, {}], certified at ρ = {}",
            certificate.growth(),
            certificate.growth()
        ),
    }
}

fn side(reading: &FloquetReading) -> &'static str {
    match reading {
        FloquetReading::Passive { .. } => "passive",
        FloquetReading::Edge { .. } => "edge",
        FloquetReading::Growing { .. } => "growing",
    }
}

/// The executed, undriven passage of `periods` periods from the declared seed (node 0's real
/// displacement 1, its imaginary rate 1/2), on the exact law or the lattice word; the ticks whose
/// balance closed and the ticks run.
fn passage(
    operands: &ResonatorOperands,
    periods: usize,
    word: Option<&WordLattice>,
) -> (usize, usize) {
    let n = operands.width();
    let drive = vec![Rat::zero(); n];
    let mut state = [vec![Rat::zero(); n], vec![Rat::zero(); n]];
    state[0][0] = Rat::one();
    state[1][1] = rat(1, 2);
    let mut remainders = ResonatorRemainders::default();
    let transient = word.map(WordLattice::transient);
    let ticks = periods * operands.phases();
    let mut closed = 0;
    for tick in 0..ticks {
        let step = operands
            .step(
                tick,
                &drive,
                [&state[0], &state[1]],
                &remainders,
                transient.as_ref(),
            )
            .expect("a tick");
        if step.closes() {
            closed += 1;
        }
        remainders = step.remainders().clone();
        state = step.state;
    }
    (closed, ticks)
}

fn decide(material: &ResonatorMaterial, word: Option<&WordLattice>, grain: u32) -> FloquetReading {
    let operands = ResonatorOperands::at_cut(0, material, &admittance(), &Rat::one(), word)
        .expect("the operands");
    Floquet::of(&operands)
        .expect("the monodromy")
        .decide(grain)
        .expect("the decision")
}

/// **The bifurcation strength, bracketed**: exact bisection over the dyadic strengths between a
/// passive `lower` and a growing `upper`, each midpoint decided by the multipliers' placement at the
/// unit circle, to the grain `2^(−g)`; both ends then decided with their certificates.
fn bracket(
    material: impl Fn(PumpDeclaration) -> ResonatorMaterial,
    step: PumpStep,
    mut lower: Rat,
    mut upper: Rat,
    grain: u32,
) -> (Rat, Rat, FloquetReading, FloquetReading) {
    let cell = Rat::new(1.into(), num_bigint::BigInt::from(1u64 << grain));
    while &upper - &lower > cell {
        let middle = (&lower + &upper) / integer(2);
        let operands = ResonatorOperands::at_cut(
            0,
            &material(pump(middle.clone(), step)),
            &admittance(),
            &Rat::one(),
            None,
        )
        .expect("the operands");
        let placed = Floquet::of(&operands)
            .expect("the monodromy")
            .placement(&Rat::one())
            .expect("the placement");
        if placed.outside > 0 || placed.on > 0 {
            upper = middle;
        } else {
            lower = middle;
        }
    }
    let below = decide(&material(pump(lower.clone(), step)), None, RING_GRAIN);
    let above = decide(&material(pump(upper.clone(), step)), None, RING_GRAIN);
    (lower, upper, below, above)
}

fn peak() -> String {
    resident_set().map_or_else(|| "unread".to_string(), |(_, peak)| peak.to_string())
}

// -------------------------------------------------------------------------------------------
// acceptance 1: the rings

type Declared = (
    &'static str,
    fn(Option<PumpDeclaration>) -> ResonatorMaterial,
    PumpStep,
    Rat,
    &'static str,
);

fn declared_rings() -> Vec<Declared> {
    vec![
        (
            "one node, standing pump",
            node,
            PumpStep::Stand,
            rat(3, 8),
            "passive",
        ),
        (
            "one node, standing pump",
            node,
            PumpStep::Stand,
            rat(1, 2),
            "edge",
        ),
        (
            "one node, standing pump",
            node,
            PumpStep::Stand,
            rat(5, 8),
            "growing",
        ),
        (
            "one node, quarter-turn pump",
            node,
            PumpStep::Quarter,
            rat(1, 16),
            "passive",
        ),
        (
            "one node, quarter-turn pump",
            node,
            PumpStep::Quarter,
            rat(1, 4),
            "growing",
        ),
        (
            "one node, half-turn pump",
            node,
            PumpStep::Half,
            Rat::one(),
            "passive",
        ),
        (
            "cycle of three, standing pump",
            cycle,
            PumpStep::Stand,
            rat(1, 8),
            "passive",
        ),
        (
            "cycle of three, standing pump",
            cycle,
            PumpStep::Stand,
            rat(1, 4),
            "edge",
        ),
        (
            "cycle of three, standing pump",
            cycle,
            PumpStep::Stand,
            rat(3, 8),
            "growing",
        ),
        (
            "cycle of three, quarter-turn pump",
            cycle,
            PumpStep::Quarter,
            rat(1, 32),
            "passive",
        ),
        (
            "cycle of three, quarter-turn pump",
            cycle,
            PumpStep::Quarter,
            rat(1, 8),
            "growing",
        ),
        (
            "cycle of three, half-turn pump",
            cycle,
            PumpStep::Half,
            rat(1, 4),
            "passive",
        ),
        (
            "cycle of three, half-turn pump",
            cycle,
            PumpStep::Half,
            rat(3, 8),
            "growing",
        ),
    ]
}

fn rings() {
    let clock = Instant::now();
    println!(
        "hnn_parametron rings: Y = {}, h = 1, grain 2^(-{RING_GRAIN}), passages of {PASSAGE_PERIODS} periods",
        admittance()
    );
    let word = word_lattice();
    let mut held = 0;
    let mut closed_all = 0;
    let mut ticks_all = 0;
    let declared = declared_rings();
    for (name, material, step, strength, expected) in &declared {
        let material = material(Some(pump(strength.clone(), *step)));
        let law = decide(&material, None, RING_GRAIN);
        let charted = decide(&material, Some(&word), RING_GRAIN);
        let operands_law =
            ResonatorOperands::at_cut(0, &material, &admittance(), &Rat::one(), None).unwrap();
        let operands_word =
            ResonatorOperands::at_cut(0, &material, &admittance(), &Rat::one(), Some(&word))
                .unwrap();
        let (closed_law, ticks_law) = passage(&operands_law, PASSAGE_PERIODS, None);
        let (closed_word, ticks_word) = passage(&operands_word, PASSAGE_PERIODS, Some(&word));
        closed_all += closed_law + closed_word;
        ticks_all += ticks_law + ticks_word;
        // The pin (§3): at an edge a multiplier sits on the unit circle, and the chart's deviation
        // may move it to either side, so the lattice word's reading of an edge is reported, not pinned.
        let holds = side(&law) == *expected && (*expected == "edge" || side(&charted) == *expected);
        if holds {
            held += 1;
        }
        println!("{name}, p = {strength}: declared {expected}");
        println!("  the law:          {}", describe(&law));
        println!("  the lattice word: {}", describe(&charted));
        println!(
            "  executed balance: {closed_law} of {ticks_law} ticks closed (law), {closed_word} of {ticks_word} (lattice word); {}",
            if holds {
                "as declared"
            } else {
                "NOT as declared"
            }
        );
    }
    println!(
        "rings as declared: {held} of {}; executed balance closed on {closed_all} of {ticks_all} ticks",
        declared.len()
    );
    // The bifurcation strengths of the rotating pumps, bracketed at 2^(-8).
    for (name, material, step, lower, upper) in [
        (
            "one node, quarter-turn pump",
            node as fn(_) -> _,
            PumpStep::Quarter,
            rat(1, 16),
            rat(1, 4),
        ),
        (
            "cycle of three, quarter-turn pump",
            cycle,
            PumpStep::Quarter,
            rat(1, 32),
            rat(1, 8),
        ),
        (
            "cycle of three, half-turn pump",
            cycle,
            PumpStep::Half,
            rat(1, 4),
            rat(3, 8),
        ),
    ] {
        let (lower, upper, below, above) =
            bracket(|pump| material(Some(pump)), step, lower, upper, RING_GRAIN);
        println!("the bifurcation of the {name} lies in ({lower}, {upper}]:");
        println!("  at p = {lower}: {}", describe(&below));
        println!("  at p = {upper}: {}", describe(&above));
    }
    println!(
        "rings: {} ms, peak resident {} bytes",
        clock.elapsed().as_millis(),
        peak()
    );
}

// -------------------------------------------------------------------------------------------
// acceptance 2: the bank

/// One pair of placed cells: the earlier (by residue) and the later, and the truth: the relative
/// quarter-turn class of their placed carriers, `(x_e + r_e) − (x_l + r_l) mod 4`.
#[derive(Clone)]
struct Pair {
    early: Carrier,
    late: Carrier,
    truth: usize,
    /// On the order-2 terrain: whether the later cell is a continuation station.
    station: bool,
}

fn pair(symbols: (usize, usize), residues: (usize, usize), station: bool) -> Pair {
    let truth = (symbols.0 + residues.0 + 8 * PERIOD - symbols.1 - residues.1) % 4;
    Pair {
        early: placed(symbols.0, residues.0),
        late: placed(symbols.1, residues.1),
        truth,
        station,
    }
}

/// **The declared pair terrain**: two cells of `ℤ/4` and two distinct residues below `D`, drawn.
fn pair_terrain(seed: u64, count: usize) -> Vec<Pair> {
    let mut draw = Draw::new(seed);
    (0..count)
        .map(|_| {
            let (first, second) = (draw.below(4), draw.below(4));
            let early = draw.below(PERIOD);
            let mut late = draw.below(PERIOD);
            while late == early {
                late = draw.below(PERIOD);
            }
            if late < early {
                pair((second, first), (late, early), false)
            } else {
                pair((first, second), (early, late), false)
            }
        })
        .collect()
}

/// **The order-2 terrain's placed cells**: the order repair's evaluated draws (`hnn_prediction`'s
/// `order_pairs` at its evaluation seed: a request of 40 cells drawn below 4, then the 8 stations
/// `x_t = x_(t−2) + 1 mod 4`), every cell at the residue of its position, every pair `(t − 2, t)`.
fn order_terrain() -> Vec<Pair> {
    let mut draw = Draw::new(ORDER_SEED);
    let mut pairs = Vec::new();
    for _ in 0..ORDER_REQUESTS {
        let mut passage: Vec<usize> = (0..ORDER_REQUEST)
            .map(|_| draw.below(ORDER_SYMBOLS))
            .collect();
        for _ in 0..ORDER_STATIONS {
            let next = (passage[passage.len() - 2] + 1) % ORDER_SYMBOLS;
            passage.push(next);
        }
        for t in 2..passage.len() {
            pairs.push(pair(
                (passage[t - 2], passage[t]),
                ((t - 2) % PERIOD, t % PERIOD),
                t >= ORDER_REQUEST,
            ));
        }
    }
    pairs
}

/// A selection of pairs with the bank's classes and the linear lock's sheet patterns.
type Selection = (Vec<Pair>, Vec<Option<usize>>, Vec<Pattern>);
/// The linear lock's sheet pattern at the axes `1` and `i` (`None` held).
type Pattern = (Option<bool>, Option<bool>);

/// The linear lock's reading of a pair: the standing members at the axes `1` and `i`, seeded on
/// the displacement by the sum of the two placed carriers, their sheets after 12 periods.
fn linear_reading(axes: &[(ResonatorOperands, Carrier)], pair: &Pair) -> Pattern {
    let sum: GaussianRat = pair.early.as_gaussian().add(&pair.late.as_gaussian());
    let seed = [sum.re, sum.im];
    let read = |(operands, axis): &(ResonatorOperands, Carrier)| {
        let locked =
            lock(operands, [&seed, &[Rat::zero(), Rat::zero()]], 12, axis).expect("a lock");
        assert!(locked.closed);
        locked.sheets[0]
    };
    (read(&axes[0]), read(&axes[1]))
}

/// A terrain's readings: the bank's class of each pair, in chunks within the stop.
fn read_bank(bank: &ReceivingBank, pairs: &[Pair], clock: &Instant) -> (Vec<Option<usize>>, bool) {
    let mut classes = Vec::with_capacity(pairs.len());
    for chunk in pairs.chunks(256) {
        if clock.elapsed().as_millis() > STOP_MS {
            return (classes, false);
        }
        let read: Vec<Option<usize>> = chunk
            .par_iter()
            .map(|pair| {
                bank.read(&[pair.early.clone(), pair.late.clone()])
                    .expect("a bank reading")
                    .class()
            })
            .collect();
        classes.extend(read);
    }
    (classes, true)
}

fn report(
    name: &str,
    pairs: &[Pair],
    classes: &[Option<usize>],
    linear: &[Pattern],
    constant: Option<usize>,
) {
    let right = pairs
        .iter()
        .zip(classes)
        .filter(|(pair, class)| **class == Some(pair.truth))
        .count();
    let unread = classes.iter().filter(|class| class.is_none()).count();
    let mut truths = [0usize; 4];
    for pair in pairs {
        truths[pair.truth] += 1;
    }
    let constant_right = constant.map_or(0, |class| truths[class]);
    // The linear lock's best fixed map from its sheet pattern to a class.
    let mut table: std::collections::BTreeMap<Pattern, [usize; 4]> =
        std::collections::BTreeMap::new();
    for (pair, pattern) in pairs.iter().zip(linear) {
        table.entry(*pattern).or_insert([0; 4])[pair.truth] += 1;
    }
    let linear_best: usize = table
        .values()
        .map(|counts| *counts.iter().max().unwrap())
        .sum();
    println!(
        "{name}: {} pairs, truths by class {:?}",
        pairs.len(),
        truths
    );
    println!(
        "  the bank (the cells in its pump): {right} of {} read exactly; {unread} with no class",
        pairs.len()
    );
    println!(
        "  the bank with the cells out of its pump (reads class {constant:?} for every pair): {constant_right} of {}",
        pairs.len()
    );
    println!(
        "  the linear lock (the cells as its seed), its best fixed map from {} sheet patterns: {linear_best} of {}",
        table.len(),
        pairs.len()
    );
    println!(
        "  the best constant class: {} of {}",
        truths.iter().max().unwrap(),
        pairs.len()
    );
}

fn run_bank(pairs_seed: u64, pairs_count: usize, order: bool) {
    let clock = Instant::now();
    let strength = bank_strength();
    let bank = bank(&strength);
    println!(
        "hnn_parametron bank: one node (C = I, K = I, Y = {}, h = 1), four members at p = {strength}, steps i^j, grain 2^(-{BANK_GRAIN}); cells placed on the mode k = {} of the ring of period {PERIOD}",
        admittance(),
        PERIOD / 4
    );
    // The control's bank reading with the cells out of the pump: one reading, the same for every
    // pair (the members' pumps unmodulated over the two crossings).
    let constant = bank
        .read(&[quarter(0), quarter(0)])
        .expect("the unmodulated bank")
        .class();
    let axes: Vec<(ResonatorOperands, Carrier)> = [quarter(0), quarter(1)]
        .into_iter()
        .map(|axis| {
            let material = node(Some(
                PumpDeclaration::new(strength.clone(), axis.clone(), PumpStep::Stand).unwrap(),
            ));
            (
                ResonatorOperands::at_cut(0, &material, &admittance(), &Rat::one(), None).unwrap(),
                axis,
            )
        })
        .collect();
    let mut complete = true;
    let pairs = pair_terrain(pairs_seed, pairs_count);
    let (classes, done) = read_bank(&bank, &pairs, &clock);
    complete &= done;
    let linear: Vec<_> = pairs[..classes.len()]
        .par_iter()
        .map(|pair| linear_reading(&axes, pair))
        .collect();
    report(
        &format!("the declared pair terrain (seed {pairs_seed})"),
        &pairs[..classes.len()],
        &classes,
        &linear,
        constant,
    );
    println!("  after {} ms", clock.elapsed().as_millis());
    if order {
        let pairs = order_terrain();
        let (classes, done) = read_bank(&bank, &pairs, &clock);
        complete &= done;
        let linear: Vec<_> = pairs[..classes.len()]
            .par_iter()
            .map(|pair| linear_reading(&axes, pair))
            .collect();
        let read = &pairs[..classes.len()];
        report(
            "the order-2 terrain's placed cells, every pair (t − 2, t)",
            read,
            &classes,
            &linear,
            constant,
        );
        let stations: Vec<usize> = (0..read.len()).filter(|i| read[*i].station).collect();
        let pick = |indices: &[usize]| -> Selection {
            (
                indices.iter().map(|i| read[*i].clone()).collect(),
                indices.iter().map(|i| classes[*i]).collect(),
                indices.iter().map(|i| linear[*i]).collect(),
            )
        };
        let (p, c, l) = pick(&stations);
        report(
            "  of which the continuation's stations (t ≥ 40)",
            &p,
            &c,
            &l,
            constant,
        );
        let request: Vec<usize> = (0..read.len()).filter(|i| !read[*i].station).collect();
        let (p, c, l) = pick(&request);
        report(
            "  of which the request's pairs (t < 40)",
            &p,
            &c,
            &l,
            constant,
        );
    }
    println!(
        "bank: {} ms, peak resident {} bytes; {}",
        clock.elapsed().as_millis(),
        peak(),
        if complete {
            "complete"
        } else {
            "INCOMPLETE: the stop was reached"
        }
    );
}

// -------------------------------------------------------------------------------------------
// development (before the pin)

fn develop() {
    let clock = Instant::now();
    println!("hnn_parametron develop (development reads only; never a measurement)");
    // The bank's lock window: the aligned member grows exactly past the standing bifurcation
    // p = 1/2 (its two ticks are the standing pump's); each misaligned member's growth threshold is
    // bracketed exactly.
    for (name, second) in [
        ("a quarter apart", 1usize),
        ("a half-turn apart", 2),
        ("three quarters apart", 3),
    ] {
        let mut lower = rat(1, 2);
        let mut upper = integer(2);
        let cell = rat(1, 256);
        let grows = |strength: &Rat| {
            let schedule = holonics::hnn::ring::PumpSchedule::new(
                strength.clone(),
                vec![quarter(0), quarter(second)],
            )
            .unwrap();
            let operands = ResonatorOperands::scheduled(
                0,
                &node(None),
                &schedule,
                &admittance(),
                &Rat::one(),
                None,
            )
            .unwrap();
            let placed = Floquet::of(&operands)
                .unwrap()
                .placement(&Rat::one())
                .unwrap();
            placed.outside > 0 || placed.on > 0
        };
        assert!(!grows(&lower) && grows(&upper));
        while &upper - &lower > cell {
            let middle = (&lower + &upper) / integer(2);
            if grows(&middle) {
                upper = middle;
            } else {
                lower = middle;
            }
        }
        println!("  the member with carriers {name} starts to grow in ({lower}, {upper}]");
    }
    let started = Instant::now();
    let pairs = pair_terrain(DEVELOP_SEED, 64);
    let bank = bank(&bank_strength());
    let right = pairs
        .iter()
        .filter(|pair| {
            bank.read(&[pair.early.clone(), pair.late.clone()])
                .unwrap()
                .class()
                == Some(pair.truth)
        })
        .count();
    println!(
        "  64 development pairs read serially in {} ms ({right} read exactly)",
        started.elapsed().as_millis()
    );
    let started = Instant::now();
    for (_, material, step, strength, _) in declared_rings().iter().take(3) {
        let material = material(Some(pump(strength.clone(), *step)));
        let _ = decide(&material, None, RING_GRAIN);
    }
    println!(
        "  three node decisions in {} ms",
        started.elapsed().as_millis()
    );
    let started = Instant::now();
    let material = cycle(Some(pump(rat(1, 8), PumpStep::Quarter)));
    let _ = decide(&material, None, RING_GRAIN);
    let _ = decide(&material, Some(&word_lattice()), RING_GRAIN);
    println!(
        "  one cycle-of-three quarter-turn decision, law and lattice word, in {} ms",
        started.elapsed().as_millis()
    );
    println!(
        "develop: {} ms, peak resident {} bytes",
        clock.elapsed().as_millis(),
        peak()
    );
}

fn main() {
    let arguments: Vec<String> = std::env::args().collect();
    match arguments.get(1).map(String::as_str) {
        Some("develop") => develop(),
        Some("rings") => rings(),
        Some("bank") => run_bank(PAIR_SEED, PAIRS, true),
        _ => panic!("hnn_parametron develop | rings | bank"),
    }
}

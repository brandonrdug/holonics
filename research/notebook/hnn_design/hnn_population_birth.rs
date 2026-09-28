//! **`birth`: residual-founded transport discovery on the moiré** (`holonics::receiver::population::
//! birth`; Lean `Compression/Landmark/Context/Birth`; the learner record's §14.1; THE_REBUILD's
//! ring-search row, "residual-founded transport discovery first"; #73, #63). Included by
//! `hnn_population.rs` as its `birth` and `birth-probe` modes; count-only **development receipts**, a
//! committed command run once in release, never a test.
//!
//! ```sh
//! cargo run --release -p holonics --example hnn_population -- birth-probe
//! cargo run --release -p holonics --example hnn_population -- birth
//! ```
//!
//! [definition; agent-inferred] **The pins** (fixed in the commit before any measured run; the
//! record `research/records/2026-09-28_RESIDUAL_FOUNDED_TRANSPORT_DISCOVERY_PINNED_BEFORE_ITS_SEEDS_
//! ARE_READ.md`):
//! - **Terrain.** The moiré's parity color, `k = 3` gratings drawn from `MoireFamily { rings: 3,
//!   denominator: 8 }` by `Moire::draw` on each of the eight fresh seeds [`SEEDS`], `n = 2^14` cells.
//! - **The declared population** (the control, "without the birth"): the receiving tree at every
//!   depth of the ladder `1, 2, 4, …, 32` and the parity gratings over `MoireFamily { rings: 2,
//!   denominator: 8 }` (the receiver expected two gratings), each named by `3` bits (seven families
//!   and the founding's slot): `M = 7/8`, the reserve `1/8`.
//! - **The founding** ("with the birth"): the same population and `SectionFounding` over
//!   `TransportBirth::moire` of the three gratings' rates (the admitted transports: their rotors on the
//!   joint port torus `d = Π q_i`), the section every `2^8` cells. Its description is
//!   `ℓ_g = 3 + ⌈log₂ R^3⌉ = 3 + 14 = 17` bits: its slot, and the three rates named among the
//!   family's `R = Σ_(q=2)^8 φ(q) = 21` rates a ring (`21^3 = 9261 = 3^3·7^3`). The phases are not
//!   declared; the founded family locates them.
//! - **The truth.** The emission's observable dimension is the rank of its Hankel matrix over one
//!   least period `L`, `[y_((i+j) mod L)]_(i,j<L)`; its code after the birth is `log₂ d − log₂ #S`,
//!   `S` the torus states at the birth cell whose emission (read through `Grating::sheet`) is the
//!   passage after it.
//! - **The acceptance**, on every seed: (1) `E T = U E` exactly (`Closure::found` refuses otherwise)
//!   and at most `d` strict steps (at most `d − dim V₀`); (2) the founded dimension equals the
//!   Hankel rank; (3) the population's code after the birth, `code(n) − code(t_g)`, is at most the
//!   truth's code after the birth plus the declared margin `−log₂(m_g/M_n)` (the newborn's charge in
//!   the founded mass), decided on the enclosures; (4) the population with the birth codes the whole
//!   passage strictly below the population without it (every charge in both codes), decided on the
//!   enclosures. A seed on which no section's residual passes `ℓ_g` founds nothing and fails (3)
//!   and (4) with that named.
//! - **Budgets.** Projected by `birth-probe` before the run against ten minutes and 20 GB.
//!
//! [definition] **Printed, exactly**, seed by seed: the drawn rates and phases, the torus and its
//! orbits `d/L`, the Hankel rank; the founding's cell, arrival, residual, rungs, founded dimension,
//! strict steps and the bound, charts, exact work and wall time; both populations' codes, their
//! difference, the code after the birth against the truth and the margin; the declared key family's
//! death; the founded family's acts. Then the peak resident set.

use std::time::Instant;

use holonics::compression::landmark::context::ratio_code_length;
use holonics::holarchy::terrain::{Draw, Grating, Moire, MoireClass, MoireFamily};
use holonics::ratio::Rat;
use holonics::ratio::algebraic::ExactInterval;
use holonics::ratio::linear::ExactRatMatrix;
use holonics::receiver::population::{
    Family, KeyFamily, Population, PopulationReceipt, SectionFounding, TransportBirth, TreeFamily,
    Work,
};
use num_bigint::BigInt;

use super::exterior::{against, difference, enclosure, exact, resident_set};
use super::{DEPTHS, ENUMERATION, GRAIN, SECTION, tree_declaration};

/// The eight fresh seeds.
const SEEDS: [u64; 8] = [
    2_026_092_881,
    2_026_092_882,
    2_026_092_883,
    2_026_092_884,
    2_026_092_885,
    2_026_092_886,
    2_026_092_887,
    2_026_092_888,
];

/// The passage `2^14`.
const CELLS: usize = 1 << 14;

/// Each declared family's naming bits: `⌈log₂ 8⌉` (seven families and the founding's slot).
const NAMING: u64 = 3;

/// The terrain's draw family and the declared (two-ring) key family.
const TERRAIN: MoireFamily = MoireFamily {
    rings: 3,
    denominator: 8,
};
const DECLARED: MoireFamily = MoireFamily {
    rings: 2,
    denominator: 8,
};

/// `φ(q)`, by count.
fn totient(q: u64) -> u64 {
    (1..=q)
        .filter(|&p| (1..=p).rev().find(|d| p % d == 0 && q % d == 0) == Some(1))
        .count() as u64
}

/// `⌈log₂ x⌉` for `x ≥ 1`.
fn ceil_log2(x: u64) -> u64 {
    u64::from(64 - (x - 1).leading_zeros()) * u64::from(x > 1)
}

/// **The founding's description** `ℓ_g = 3 + ⌈log₂ R^k⌉`, `R = Σ_(q=2)^Q φ(q)`.
fn founding_bits() -> u64 {
    let rates: u64 = (2..=TERRAIN.denominator).map(totient).sum();
    NAMING + ceil_log2(rates.pow(TERRAIN.rings as u32))
}

/// The declared population: the trees at every depth and the two-ring parity gratings.
fn declare() -> Population {
    let mut families: Vec<Box<dyn Family>> = DEPTHS
        .iter()
        .map(|&depth| {
            Box::new(
                TreeFamily::new(tree_declaration(2, depth, CELLS), NAMING)
                    .expect("a declared tree"),
            ) as Box<dyn Family>
        })
        .collect();
    families.push(Box::new(
        KeyFamily::gratings(&DECLARED, MoireClass::Parity, ENUMERATION, NAMING)
            .expect("the declared two-ring gratings"),
    ));
    Population::new(families).expect("a declared population")
}

/// **The Hankel rank** of a periodic word over one period.
fn hankel_rank(word: &[usize]) -> usize {
    let l = word.len();
    let rows = (0..l)
        .map(|i| {
            (0..l)
                .map(|j| Rat::from_integer(BigInt::from(word[(i + j) % l])))
                .collect()
        })
        .collect();
    ExactRatMatrix::new(rows)
        .expect("a square word matrix")
        .rank()
        .expect("an exact rank")
}

/// **The truth's fibre after the birth**: the torus states whose parity emission is `after`.
fn fibre_after(rates: &[(u64, u64)], after: &[usize]) -> u64 {
    let chart: u64 = rates.iter().map(|&(_, q)| q).product();
    (0..chart)
        .filter(|&state| {
            let mut rest = state;
            let rings: Vec<Grating> = rates
                .iter()
                .map(|&(p, q)| {
                    let port = rest % q;
                    rest /= q;
                    Grating::new(p, q, port).expect("a port of a declared ring")
                })
                .collect();
            after.iter().enumerate().all(|(tick, &cell)| {
                rings.iter().filter(|ring| ring.sheet(tick as u64)).count() % 2 == cell
            })
        })
        .count() as u64
}

/// `−log₂(a/b)`, enclosed.
fn bits(numerator: u64, denominator: u64) -> ExactInterval {
    ratio_code_length(&numerator.into(), &denominator.into()).expect("a positive ratio")
}

/// `−log₂ x`, enclosed.
fn bits_of(x: &Rat) -> ExactInterval {
    ratio_code_length(x.numer().magnitude(), x.denom().magnitude()).expect("a positive mass")
}

fn sum(a: &ExactInterval, b: &ExactInterval) -> ExactInterval {
    ExactInterval {
        lower: &a.lower + &b.lower,
        upper: &a.upper + &b.upper,
    }
}

fn minus(a: &ExactInterval, b: &ExactInterval) -> ExactInterval {
    ExactInterval {
        lower: &a.lower - &b.upper,
        upper: &a.upper - &b.lower,
    }
}

fn acts(work: &Work) -> String {
    work.acts
        .iter()
        .map(|(act, count)| format!("{act:?} {count}"))
        .collect::<Vec<_>>()
        .join(", ")
}

fn memory() -> String {
    match resident_set() {
        Some((now, peak)) => format!(
            "resident {} KiB, peak {} KiB (VmRSS, VmHWM)",
            now / 1024,
            peak / 1024
        ),
        None => "the resident set does not read".to_string(),
    }
}

/// **`birth-probe`** (module header, "Budgets"): the founding alone on the largest single orbit the
/// family admits (rates `1/8, 1/7, 1/5`, `d = 280`), then both populations over `2^12` cells of a
/// hand moiré on that orbit. No pinned seed is read.
pub fn probe() {
    let rates = [(1, 8), (1, 7), (1, 5)];
    let bits_g = founding_bits();
    println!("hnn_population birth-probe: rates 1/8, 1/7, 1/5 (d = 280), ℓ_g = {bits_g}");
    let started = Instant::now();
    let birth = TransportBirth::moire(&rates, MoireClass::Parity, bits_g).expect("the chart");
    let chart_ms = started.elapsed().as_millis();
    let started = Instant::now();
    let separator = birth
        .reached(&[-Rat::from_integer(1.into()), Rat::from_integer(1.into())])
        .expect("the polarized reading");
    let founded = birth.found(&separator).expect("a founding");
    let found_ms = started.elapsed().as_millis();
    let work = founded.closure.work();
    println!(
        "  chart built in {chart_ms} ms; founded in {found_ms} ms: dimension {}, rungs {}, strict steps {}, charts {}",
        founded.closure.dimension(),
        founded.closure.rungs().len(),
        founded.closure.strict_steps(),
        founded.closure.charts()
    );
    for (name, value) in work.coordinates() {
        println!("    {name}: {value}");
    }
    let moire = Moire::new(
        vec![
            Grating::new(1, 8, 3).expect("a grating"),
            Grating::new(1, 7, 5).expect("a grating"),
            Grating::new(1, 5, 1).expect("a grating"),
        ],
        MoireClass::Parity,
    )
    .expect("the hand moiré");
    let cells = moire.emit(1 << 12);
    let started = Instant::now();
    let mut without = declare();
    without.receive_passage(&cells).expect("the passage");
    let without_ms = started.elapsed().as_millis();
    let started = Instant::now();
    let mut with = declare();
    let mut section = SectionFounding::new(birth, SECTION).expect("a section founding");
    for &cell in &cells {
        section.receive(&mut with, cell).expect("a cell");
    }
    let with_ms = started.elapsed().as_millis();
    println!(
        "  2^12 cells: without the birth {without_ms} ms, with it {with_ms} ms; founded at {:?}",
        section.receipt().map(|receipt| receipt.birth.cell)
    );
    println!("  {}", memory());
}

/// One seed's run (module header).
fn run(seed: u64, bits_g: u64) -> Vec<bool> {
    let moire = Moire::draw(&TERRAIN, MoireClass::Parity, &mut Draw::new(seed)).expect("a moiré");
    let truth = moire.truth(&TERRAIN).expect("its truth");
    let rates: Vec<(u64, u64)> = moire
        .gratings()
        .iter()
        .map(|g| (g.numerator(), g.denominator()))
        .collect();
    let chart: u64 = rates.iter().map(|&(_, q)| q).product();
    let joint = u64::try_from(&truth.joint_period).expect("a joint period in a word");
    let cells = moire.emit(CELLS);
    let hankel = hankel_rank(&cells[..truth.least_period]);
    println!("seed {seed}:");
    for g in moire.gratings() {
        println!(
            "  grating: rate {}/{}, phase {}/{}",
            g.numerator(),
            g.denominator(),
            g.phase(),
            g.denominator()
        );
    }
    println!(
        "  torus d = Π q = {chart}, joint period {joint}, orbits d/L = {}, least period {}, Hankel rank {hankel}; key bits {}",
        chart / joint,
        truth.least_period,
        truth.key_bits
    );
    // Without the birth.
    let started = Instant::now();
    let mut without = declare();
    without.receive_passage(&cells).expect("the passage");
    let without_ms = started.elapsed().as_millis();
    let control: PopulationReceipt = without.receipt().expect("a receipt");
    // With the birth.
    let started = Instant::now();
    let mut with = declare();
    let birth = TransportBirth::moire(&rates, MoireClass::Parity, bits_g).expect("the chart");
    let mut section = SectionFounding::new(birth, SECTION).expect("a section founding");
    let mut founding_ms = None;
    for &cell in &cells {
        let before = Instant::now();
        section.receive(&mut with, cell).expect("a cell");
        if founding_ms.is_none() && section.receipt().is_some() {
            founding_ms = Some(before.elapsed().as_millis());
        }
    }
    let with_ms = started.elapsed().as_millis();
    let receipt = with.receipt().expect("a receipt");
    let key = &control.families[DEPTHS.len()];
    println!(
        "  the declared two-ring gratings: {}",
        match key.died {
            Some(cell) => format!("died at cell {cell}"),
            None => "survived the passage".to_string(),
        }
    );
    println!(
        "  without the birth: code {} ({without_ms} ms)",
        enclosure(&control.code, GRAIN)
    );
    let Some(founding) = section.receipt() else {
        println!("  with the birth: no section's residual passed ℓ_g = {bits_g}: nothing founded");
        return vec![false; 5];
    };
    let d_bound = founding.chart - founding.rungs[0];
    let steps = founding.rungs.len() - 1;
    println!(
        "  founded at cell {} on arrival {} (residual {}), from the reserve: mass {}, charge {}",
        founding.birth.cell,
        founding.arrived,
        founding
            .birth
            .residual
            .as_ref()
            .map_or("-".to_string(), |r| enclosure(r, GRAIN)),
        exact(&founding.birth.mass),
        enclosure(&founding.birth.charge, GRAIN)
    );
    println!(
        "    chart {}, forms held {}, rungs {:?}, founded dimension {}, strict steps {steps} (bound d − dim V₀ = {d_bound}), prime charts {}; E T = U E and D E = ρ checked exactly ({} ms)",
        founding.chart,
        founding.held,
        founding.rungs,
        founding.dimension,
        founding.charts,
        founding_ms.unwrap_or(0)
    );
    let work = founding
        .work
        .coordinates()
        .into_iter()
        .map(|(name, value)| format!("{name} {value}"))
        .collect::<Vec<_>>()
        .join(", ");
    println!("    exact work: {work}");
    let dimension_holds = founding.dimension == hankel;
    println!(
        "  (2) founded dimension {} against the Hankel rank {hankel}: {}",
        founding.dimension,
        if dimension_holds {
            "equal".to_string()
        } else {
            format!("differ by {}", founding.dimension as i64 - hankel as i64)
        }
    );
    // After the birth.
    let born = founding.birth.cell;
    let newborn = &receipt.families[founding.birth.family];
    let fibre = fibre_after(&rates, &cells[born..]);
    let truth_after = bits(fibre, chart);
    let own = newborn.code.clone().expect("a living newborn");
    println!(
        "  the truth after the birth: #S = {fibre} of {chart}, code {}; the newborn's own code {} ({})",
        enclosure(&truth_after, GRAIN),
        enclosure(&own, GRAIN),
        if own == truth_after {
            "equal"
        } else {
            "differs"
        }
    );
    let after = minus(&receipt.code, &founding.birth.inherited);
    let margin = bits_of(&(&founding.birth.mass / &receipt.founded));
    let bound = sum(&truth_after, &margin);
    let margin_holds = after.upper <= bound.lower;
    println!(
        "  (3) the population after the birth {} against the truth plus the margin −log₂(m_g/M_n) = {}: {}",
        enclosure(&after, GRAIN),
        enclosure(&margin, GRAIN),
        if margin_holds {
            "decided at or below"
        } else {
            against(&after, &bound)
        }
    );
    println!(
        "      the population after the birth less the truth: {}",
        difference(&after, &truth_after, GRAIN)
    );
    let below = receipt.code.upper < control.code.lower;
    println!(
        "  (4) with the birth: code {} ({with_ms} ms); with less without: {}: {}",
        enclosure(&receipt.code, GRAIN),
        difference(&receipt.code, &control.code, GRAIN),
        if below {
            "strictly below"
        } else {
            against(&receipt.code, &control.code)
        }
    );
    println!("  the newborn's acts: {}", acts(&newborn.work));
    let steps_hold = steps <= d_bound && steps <= founding.chart;
    vec![true, steps_hold, dimension_holds, margin_holds, below]
}

/// **`birth`** (module header).
pub fn harness() {
    let bits_g = founding_bits();
    println!(
        "hnn_population birth: the moiré's parity color, 3 gratings, denominators up to 8, n = 2^14 cells, seeds {:?}; ℓ_g = {bits_g}",
        SEEDS
    );
    let started = Instant::now();
    let mut verdicts = Vec::new();
    for seed in SEEDS {
        verdicts.push((seed, run(seed, bits_g)));
    }
    println!(
        "the acceptance, seed by seed (founded, (1) steps, (2) dimension, (3) margin, (4) below):"
    );
    for (seed, verdict) in &verdicts {
        println!("  {seed}: {verdict:?}");
    }
    let all = verdicts.iter().all(|(_, v)| v.iter().all(|&x| x));
    println!(
        "the acceptance {}; {} ms (exterior wall); {}",
        if all { "passes" } else { "fails" },
        started.elapsed().as_millis(),
        memory()
    );
}

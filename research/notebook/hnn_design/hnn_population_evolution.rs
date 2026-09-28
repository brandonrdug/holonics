//! **`evolution` and `species`: the evolved prior across aeons, and species collapse relative to
//! the admitted future** (`holonics::receiver::population::{evolution, species}`; Lean
//! `Compression/Landmark/Context/Evolution`; #73). Included by `hnn_population.rs` as its
//! `evolution` and `species` modes; count-only **development receipts**, a committed command run
//! once in release, never a test: the conversation cut stays the living substrate and the milestone
//! (Brandon's ruling of August 26), and no claim here is joined to the cut's.
//!
//! ```sh
//! cargo run --release -p holonics --example hnn_population -- evolution
//! cargo run --release -p holonics --example hnn_population -- species
//! ```
//!
//! [definition; agent-inferred] **The aeons** (`evolution`). Twelve declared aeons, three cycles of
//! four terrains, each drawn by the seed plus its aeon's index: a moiré's parity color (`k = 3`,
//! `q ≤ 2^3`, `2^12` cells), a tree source (depth 2 over bits, `2^12` cells), products in base 2
//! (`L = 4` least significant first, `k = 2`, `2^8` records of 19 cells) and a prime stream in base
//! 10 (`L = 3`, most significant first, over `[100c, 1000)` in cycle `c`). Each aeon declares the
//! receiving tree at every depth of the ladder and the one key family of the catalogue that reads
//! its cell alphabet (the parity gratings on both binary terrains, `clock ⊳ carry` on the
//! products, `clock ⊳ (counter ⊳ sieve)` on the primes): seven families, each named by 3 bits, so
//! the static prior is `1/7` a family at the Kraft mass `7/8`. Two populations read the same cells:
//! the **static** one, and the **evolved** one, declared at the aeon's opening by
//! `Population::evolved` from the counts retained so far at `λ = ½`. The retention reads the evolved
//! population's receipt after each aeon; the counts are the only history kept.
//!
//! [definition] **Printed, exactly**, aeon by aeon: the terrain, the evolved prior of the family the
//! aeon selects and of the key family (its founding charge `−log₂ m_f` against the static 3 bits),
//! both populations' codes and their difference, the evolved code against the bound
//! `code(selected) − log₂ π(selected)` (no aeon here founds a family, so the no-birth form holds;
//! read two-sided: below, above or undecided, with the enclosed slack), the selected family's
//! work, and the retained counts `(declared, selected, died)` per identity; then the totals.
//!
//! [definition; agent-inferred] **The species** (`species`): the parity moiré and the sheet tuple of
//! the `moire` mode and the rotor crib of the `crib` mode, each read whole by its population, then its
//! key family collapsed over the whole future: the members before and after, the species, and the
//! population's code, face and the family's own code before and after. On the parity moiré the
//! species are also read relative to a growing admitted future at the first cell whose survivors
//! number at most `2^12`: one tick, two, …, then the whole future, each collapse split from its
//! receipt before the next.

use std::collections::BTreeMap;
use std::time::Instant;

use holonics::compression::landmark::context::ratio_code_length;
use holonics::holarchy::terrain::arithmetic::{
    DigitOrder, PrimeEmission, PrimeWindow, ProductFamily, Products,
};
use holonics::holarchy::terrain::{
    Draw, Moire, MoireClass, MoireFamily, RotorCrib, TreeSource, TreeSourceFamily,
};
use holonics::ratio::Rat;
use holonics::ratio::algebraic::{ExactInterval, interval_sum};
use holonics::receiver::face::GrainCell;
use holonics::receiver::population::{
    AdmittedFuture, Collapse, Composed, Family, Identity, KeyFamily, Population, PopulationReceipt,
    Selections, TreeFamily, Work,
};
use num_bigint::BigInt;

use super::exterior::{against, exact};
use super::{CRIB_RING, DEPTHS, ENUMERATION, GRAIN, SEED, crib_field, factored, tree_declaration};

/// The aeons: three cycles of the four terrains.
const AEONS: usize = 12;
/// The moiré's and the tree source's cells an aeon.
const AEON_CELLS: usize = 1 << 12;
/// The products' records an aeon.
const AEON_RECORDS: usize = 1 << 8;
/// Each family's naming bits: `⌈log₂ 7⌉`.
const NAMING: u64 = 3;

/// **A reading at the grain**, `n + k/16 + ε` (both endpoints when their cells differ).
fn short(interval: &ExactInterval) -> String {
    let (lower, upper) = (
        GrainCell::of(&interval.lower, GRAIN),
        GrainCell::of(&interval.upper, GRAIN),
    );
    if lower.carry == upper.carry && lower.phase == upper.phase {
        format!("{} + {}/{GRAIN} + ε", lower.carry, lower.phase)
    } else {
        format!(
            "[{} + {}/{GRAIN}, {} + {}/{GRAIN}] + ε",
            lower.carry, lower.phase, upper.carry, upper.phase
        )
    }
}

/// `a − b`, enclosed.
fn minus(a: &ExactInterval, b: &ExactInterval) -> ExactInterval {
    ExactInterval {
        lower: &a.lower - &b.upper,
        upper: &a.upper - &b.lower,
    }
}

/// **A code against its bound, two-sided** (`exterior::against`): decided below (the bound holds),
/// decided above (the bound is refuted), or undecided where the enclosures overlap (not refuted).
fn verdict(code: &ExactInterval, bound: &ExactInterval) -> String {
    match against(code, bound) {
        "below" => "below: the bound holds".to_string(),
        "above" => "above: the bound is refuted".to_string(),
        undecided => format!("{undecided}: not refuted"),
    }
}

/// `−log₂ x`, enclosed.
fn bits(x: &Rat) -> ExactInterval {
    ratio_code_length(x.numer().magnitude(), x.denom().magnitude()).expect("a positive mass")
}

/// A work's acts, in counts.
fn work_line(work: &Work) -> String {
    work.acts
        .iter()
        .map(|(act, count)| format!("{act:?} {count}"))
        .collect::<Vec<_>>()
        .join(", ")
}

/// One aeon's terrain: its name, its cells, its alphabet, and its key family's declaration.
struct Terrain {
    name: String,
    cells: Vec<usize>,
    alphabet: usize,
    key: Box<dyn Fn() -> Box<dyn Family>>,
}

fn terrain(aeon: usize) -> Terrain {
    let seed = SEED + aeon as u64;
    let parity = MoireFamily {
        rings: 3,
        denominator: 8,
    };
    let declared = parity.clone();
    let gratings = move || -> Box<dyn Family> {
        Box::new(
            KeyFamily::gratings(&declared, MoireClass::Parity, ENUMERATION, NAMING)
                .expect("the parity gratings"),
        )
    };
    match aeon % 4 {
        0 => {
            let moire = Moire::draw(&parity, MoireClass::Parity, &mut Draw::new(seed))
                .expect("a drawn moiré");
            let drawn: Vec<String> = moire
                .gratings()
                .iter()
                .map(|g| {
                    format!(
                        "{}/{} @ {}/{}",
                        g.numerator(),
                        g.denominator(),
                        g.phase(),
                        g.denominator()
                    )
                })
                .collect();
            Terrain {
                name: format!("moiré parity ({})", drawn.join(", ")),
                cells: moire.emit(AEON_CELLS),
                alphabet: 2,
                key: Box::new(gratings),
            }
        }
        1 => {
            let family = TreeSourceFamily {
                alphabet: 2,
                depth: 2,
                grid: 16,
            };
            let mut draw = Draw::new(seed);
            let source = TreeSource::draw(&family, &mut draw).expect("a tree source");
            Terrain {
                name: "tree source (depth 2 over bits)".to_string(),
                cells: source.emit(AEON_CELLS, &mut draw),
                alphabet: 2,
                key: Box::new(gratings),
            }
        }
        2 => {
            let family = ProductFamily {
                base: 2,
                digits: 4,
                face: 2,
                order: DigitOrder::LeastFirst,
            };
            let products =
                Products::draw(&family, AEON_RECORDS, &mut Draw::new(seed)).expect("products");
            let declared = family.clone();
            Terrain {
                name: "products in base 2 (L = 4, 2^8 records)".to_string(),
                cells: products.emit(),
                alphabet: family.alphabet(),
                key: Box::new(move || {
                    Box::new(Composed::products(&declared, NAMING).expect("clock ⊳ carry"))
                }),
            }
        }
        _ => {
            let start = 100 * (aeon / 4) as u64;
            let window = PrimeWindow {
                base: 10,
                start,
                end: 1000,
                digits: 3,
                trailing: 1,
                order: DigitOrder::MostFirst,
                emission: PrimeEmission::Digits,
            };
            let cells = window.emit().expect("the prime stream");
            Terrain {
                name: format!("primes in base 10 over [{start}, 1000) (L = 3)"),
                cells,
                alphabet: 12,
                key: Box::new(move || {
                    Box::new(
                        Composed::primes(&window, ENUMERATION, NAMING)
                            .expect("clock ⊳ (counter ⊳ sieve)"),
                    )
                }),
            }
        }
    }
}

fn families(terrain: &Terrain) -> Vec<Box<dyn Family>> {
    let mut families: Vec<Box<dyn Family>> = DEPTHS
        .iter()
        .map(|&depth| {
            Box::new(
                TreeFamily::new(
                    tree_declaration(terrain.alphabet, depth, terrain.cells.len()),
                    NAMING,
                )
                .expect("a declared tree"),
            ) as Box<dyn Family>
        })
        .collect();
    families.push((terrain.key)());
    families
}

fn read(population: &mut Population, cells: &[usize]) -> PopulationReceipt {
    population.receive_passage(cells).expect("the passage");
    population.receipt().expect("the receipt")
}

/// **`evolution`** (module header).
pub fn evolution() {
    let started = Instant::now();
    let half = Rat::new(BigInt::from(1), BigInt::from(2));
    let mut selections = Selections::new();
    let mut names: BTreeMap<Identity, String> = BTreeMap::new();
    let zero = ExactInterval::point(Rat::from_integer(BigInt::from(0)));
    let (mut total_static, mut total_evolved) = (zero.clone(), zero.clone());
    let mut cycles = vec![(zero.clone(), zero.clone()); AEONS / 4];
    println!(
        "hnn_population evolution: {AEONS} aeons, seed {SEED} + the aeon; seven families an aeon, each named by {NAMING} bits; the evolved prior at λ = 1/2"
    );
    for aeon in 0..AEONS {
        let terrain = terrain(aeon);
        let mut stat = Population::new(families(&terrain)).expect("the static population");
        let mut evolved = Population::evolved(families(&terrain), &selections, &half)
            .expect("the evolved population");
        let key = DEPTHS.len();
        let key_prior = evolved.prior(key).expect("a prior").clone();
        let key_charge = bits(&(evolved.mass() * &key_prior));
        let static_receipt = read(&mut stat, &terrain.cells);
        let receipt = read(&mut evolved, &terrain.cells);
        println!(
            "aeon {aeon}: {}; n = {} cells, alphabet {}",
            terrain.name,
            factored(&num_bigint::BigUint::from(terrain.cells.len())),
            terrain.alphabet
        );
        println!(
            "  the key family [{key}] {}: evolved prior {} (static 1/7), its founding charge −log₂ m_f {} (static 3)",
            receipt.families[key].label,
            exact(&key_prior),
            short(&key_charge)
        );
        match receipt.selected {
            Some(selected) => {
                let family = &receipt.families[selected];
                let prior = evolved.prior(selected).expect("a prior").clone();
                let code = family.code.clone().expect("a living family's code");
                let bound = interval_sum(&code, &bits(&prior)).expect("an enclosure");
                println!(
                    "  selected [{selected}] {} (the static population selects [{}]); its evolved prior {}; its code alone {}",
                    family.label,
                    static_receipt
                        .selected
                        .map_or("none".to_string(), |s| s.to_string()),
                    exact(&prior),
                    short(&code)
                );
                let slack = minus(&bound, &receipt.code);
                println!(
                    "  the bound (an aeon without births): the evolved population's code {} against code(selected) − log₂ π(selected) = {}: {}; the slack bound − code, enclosed: exact [{}, {}] bits",
                    short(&receipt.code),
                    short(&bound),
                    verdict(&receipt.code, &bound),
                    exact(&slack.lower),
                    exact(&slack.upper)
                );
                println!("  the selected family's work: {}", work_line(&family.work));
            }
            None => println!("  selected: none decided above 1/2"),
        }
        let difference = minus(&receipt.code, &static_receipt.code);
        println!(
            "  static code {}; evolved code {}; evolved − static {} (exact [{}, {}])",
            short(&static_receipt.code),
            short(&receipt.code),
            short(&difference),
            exact(&difference.lower),
            exact(&difference.upper)
        );
        total_static = interval_sum(&total_static, &static_receipt.code).expect("a sum");
        total_evolved = interval_sum(&total_evolved, &receipt.code).expect("a sum");
        let cycle = &mut cycles[aeon / 4];
        cycle.0 = interval_sum(&cycle.0, &static_receipt.code).expect("a sum");
        cycle.1 = interval_sum(&cycle.1, &receipt.code).expect("a sum");
        for family in &receipt.families {
            names
                .entry(family.identity.clone())
                .or_insert_with(|| family.label.clone());
        }
        selections.record(&receipt);
        let counts: Vec<String> = selections
            .tallies()
            .filter(|(_, tally)| tally.selected > 0 || tally.died > 0)
            .map(|(identity, tally)| {
                format!(
                    "{}: ({}, {}, {})",
                    names.get(identity).map_or("?", String::as_str),
                    tally.declared,
                    tally.selected,
                    tally.died
                )
            })
            .collect();
        println!(
            "  retained counts (declared, selected, died), the identities selected or dead: {}",
            counts.join("; ")
        );
    }
    for (cycle, (stat, evolved)) in cycles.iter().enumerate() {
        println!(
            "cycle {cycle} (aeons {}–{}): static {}, evolved {}, evolved − static {}",
            4 * cycle,
            4 * cycle + 3,
            short(stat),
            short(evolved),
            short(&minus(evolved, stat))
        );
    }
    println!(
        "all {AEONS} aeons: static {}, evolved {}, evolved − static {} (exact [{}, {}]); {} ms (exterior wall)",
        short(&total_static),
        short(&total_evolved),
        short(&minus(&total_evolved, &total_static)),
        exact(&minus(&total_evolved, &total_static).lower),
        exact(&minus(&total_evolved, &total_static).upper),
        started.elapsed().as_millis()
    );
}

/// The population of the tree ladder and one key family, each named by 3 bits.
fn declare(alphabet: usize, cells: usize, key: Box<dyn Family>) -> Population {
    let mut families: Vec<Box<dyn Family>> = DEPTHS
        .iter()
        .map(|&depth| {
            Box::new(
                TreeFamily::new(tree_declaration(alphabet, depth, cells), NAMING)
                    .expect("a declared tree"),
            ) as Box<dyn Family>
        })
        .collect();
    families.push(key);
    Population::new(families).expect("a declared population")
}

/// A population read whole, then its key family collapsed over the whole future.
fn collapse_whole(name: &str, alphabet: usize, cells: &[usize], key: Box<dyn Family>) {
    let started = Instant::now();
    let mut population = declare(alphabet, cells.len(), key);
    population.receive_passage(cells).expect("the passage");
    let family = DEPTHS.len();
    let (code, face) = (
        population.code().expect("its code"),
        population.face().expect("its face"),
    );
    let posterior = population.posterior_of(&[family]).expect("a posterior");
    let alone = population.receipt().expect("a receipt").families[family]
        .code
        .clone();
    let collapse = population
        .collapse(family, AdmittedFuture::Whole)
        .expect("the key family's species");
    println!("{name}: n = {} cells", cells.len());
    println!(
        "  members before {}, after {} (the whole future)",
        collapse.before(),
        collapse.after()
    );
    if let Collapse::Keys { factors, .. } = &collapse {
        for (index, factor) in factors.iter().enumerate() {
            for species in &factor.species {
                let shown: Vec<String> = species
                    .coordinates
                    .iter()
                    .take(4)
                    .map(|c| format!("{c:?}"))
                    .collect();
                println!(
                    "  factor {index}: a species of {} members at posterior {}, representative {:?}; members {}{}",
                    species.members.len(),
                    exact(&species.posterior),
                    species.coordinates[0],
                    shown.join(" "),
                    if species.members.len() > 4 {
                        " …"
                    } else {
                        ""
                    }
                );
            }
        }
    }
    let after = population.receipt().expect("a receipt");
    println!(
        "  the population's code before {} and after {}: equal {}",
        short(&code),
        short(&after.code),
        after.code == code
    );
    println!(
        "  its face equal {}; the family's posterior equal {}; its own code equal {}",
        population.face().expect("its face") == face,
        population.posterior_of(&[family]).expect("a posterior") == posterior,
        after.families[family].code == alone
    );
    println!("  {} ms (exterior wall)", started.elapsed().as_millis());
}

/// **`species`** (module header).
pub fn species() {
    let parity = MoireFamily {
        rings: 3,
        denominator: 8,
    };
    let moire =
        Moire::draw(&parity, MoireClass::Parity, &mut Draw::new(SEED)).expect("a drawn moiré");
    let cells = moire.emit(1 << 14);
    collapse_whole(
        "the parity moiré (k = 3, q ≤ 2^3, the moire mode's)",
        2,
        &cells,
        Box::new(
            KeyFamily::gratings(&parity, MoireClass::Parity, ENUMERATION, NAMING)
                .expect("the parity gratings"),
        ),
    );

    // Species relative to a growing admitted future, at the first cell with at most 2^12 survivors.
    let mut family = KeyFamily::gratings(&parity, MoireClass::Parity, ENUMERATION, NAMING)
        .expect("the parity gratings");
    let mut at = 0;
    while family.factors()[0].count() > 1 << 12 {
        family.receive(cells[at]).expect("a cell");
        at += 1;
    }
    println!(
        "  at cell {at}: {} survivors; the species relative to the admitted future:",
        family.factors()[0].count()
    );
    let mut futures: Vec<AdmittedFuture> = (0..10).map(|j| AdmittedFuture::Ticks(1 << j)).collect();
    futures.push(AdmittedFuture::Whole);
    for future in futures {
        let collapse = family
            .collapse(future)
            .expect("the species")
            .expect("the parity keys declare their check");
        println!(
            "    {future:?}: {} species of {} members",
            collapse.after(),
            collapse.before()
        );
        family.split(&collapse).expect("the split");
    }

    let wide = MoireFamily {
        rings: 3,
        denominator: 16,
    };
    let parity_wide =
        Moire::draw(&wide, MoireClass::Parity, &mut Draw::new(SEED)).expect("the moiré");
    let sheets_wide =
        Moire::new(parity_wide.gratings().to_vec(), MoireClass::Sheets).expect("its sheets");
    collapse_whole(
        "the sheet tuple (k = 3, q ≤ 2^4, the moire mode's)",
        8,
        &sheets_wide.emit(1 << 14),
        Box::new(
            KeyFamily::gratings(&wide, MoireClass::Sheets, ENUMERATION, NAMING)
                .expect("the sheet gratings"),
        ),
    );

    let field = crib_field();
    let configurations = [0u64; 4];
    let crib = RotorCrib::draw(
        &field,
        CRIB_RING,
        &configurations,
        1 << 10,
        &mut Draw::new(SEED),
    )
    .expect("a drawn crib");
    collapse_whole(
        "the rotor crib (the crib mode's)",
        field.ring(CRIB_RING).period() as usize,
        &crib.cells,
        Box::new(
            KeyFamily::rotor(&field, CRIB_RING, &configurations, ENUMERATION, NAMING)
                .expect("the rotor keys"),
        ),
    );
}

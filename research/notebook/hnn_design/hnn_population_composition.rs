//! **`composition`: the arithmetic eggs composed at ports** (`holonics::receiver::population::
//! {composition, arithmetic}`; Lean `Compression/Landmark/Context/Composition`; #73). Included by
//! `hnn_population.rs` as its `composition` mode; count-only **development receipts**, a committed
//! command run once in release, never a test: the conversation cut stays the living substrate and
//! the milestone (Brandon's ruling of August 26), and no claim here is joined to the cut's.
//!
//! ```sh
//! cargo run --release -p holonics --example hnn_population -- composition
//! cargo run --release -p holonics --example hnn_population -- composition products
//! cargo run --release -p holonics --example hnn_population -- composition primes
//! ```
//!
//! [definition; agent-inferred] **The terrains** are the terrain notebook's arithmetic ones
//! (`hnn_terrain -- arithmetic`), drawn by the same seed: products in bases 2, 10 and 16 (`L = 4`
//! digits least significant first, `k = 2`, `2^12` records of 19 cells, `n = 77824 = 2^12·19`), and
//! the prime streams over `[0, 10^4)` in base 10 (`L = 4`) and base 6 (`L = 6`), most significant
//! first with the primality cell.
//!
//! [definition; agent-inferred] **The population** on each: two families, each named by one bit
//! (`M = 1`): the receiving tree (cell-only, `½` stop prior, `L_R = 16`) at the depth the terrain
//! notebook's sweep chose on the same cells (products `13`, `5`, `4`; primes `4`, `6`: the tree at
//! its best, recorded, not re-chosen), and the composed egg: `record clock ⊳ carry egg` on products,
//! `record clock ⊳ (counter ⊳ sieve)` on the prime streams. It is read once over the cells,
//! partitioned by cell class (`Population::receive_partitioned`), so each family's code and the
//! population's are read class by class in one pass, every cell scored before its deposit.
//!
//! [definition] **Printed, exactly**, per class (operands, marks, trailing, middle, leading; digits,
//! primality): the truth (the operands' entropy `2L log₂ b` a record exactly; every other cell
//! determined, zero), the tree's code, the composed egg's, the population's, and each against the
//! truth; the keys the composed egg located against the drawn configuration (offset zero, start
//! zero); **each keystone's value**, the joint code without it against with it, beside its own
//! description:
//! - the record clock: without it neither the carry egg nor the counter has a port, so the
//!   population without it is the tree alone (named by zero bits): value = `code(tree) − code(P)`;
//! - the counter (the sieve's keystone): the sieve at the counter's unheld port, under the located
//!   clock (`Composed::primes_unheld_counter`, its own population): value =
//!   `code(clock ⊳ (unheld counter ⊳ sieve)) − code(clock ⊳ (counter ⊳ sieve))`;
//!
//! and the sieve's work over the window: the face that decided each integer (the cheap faces first,
//! then the gratings). Bits are enclosures read at `L_R = 16` as `n + k/16 + ε` (the exact
//! endpoints for the totals); no decimal is printed.

use std::time::Instant;

use holonics::holarchy::terrain::Draw;
use holonics::holarchy::terrain::arithmetic::{
    DigitOrder, PrimeCell, PrimeEmission, PrimeWindow, ProductCell, ProductFamily, Products,
};
use holonics::ratio::Rat;
use holonics::ratio::algebraic::{ExactInterval, interval_difference, interval_sum};
use holonics::ratio::surprisal::SymbolicSurprisal;
use holonics::receiver::face::GrainCell;
use holonics::receiver::population::{
    Composed, Family, PartReading, Population, PopulationReceipt, Sieve, SieveFace, TreeFamily,
};
use num_bigint::{BigInt, BigUint};

use super::exterior::{enclosure, exact, resident_set};
use super::{ENUMERATION, GRAIN, SEED, factored, on_grid, point, tree_declaration};

/// The products' records `2^12`, digits an operand `L = 4` and face width `k = 2` (the terrain
/// notebook's).
const RECORDS: usize = 1 << 12;
const DIGITS: usize = 4;
const FACE: usize = 2;

/// The prime window `[0, 10^4)` (the terrain notebook's).
const WINDOW: u64 = 10_000;

/// The recorded class codes of the tree at its chosen depth (the terrain notebook's README, "The
/// arithmetic terrain"), for the cross-check: products (base, D, [operands, marks, trailing,
/// middle, leading]) and primes (base, L, D, [digits, primality]).
const PRODUCT_TREES: [(u64, usize, [&str; 5]); 3] = [
    (
        2,
        13,
        [
            "33179 + 11/16",
            "1524 + 0/16",
            "1422 + 4/16",
            "3966 + 1/16",
            "1465 + 6/16",
        ],
    ),
    (
        10,
        5,
        [
            "114394 + 15/16",
            "41600 + 2/16",
            "26466 + 6/16",
            "60508 + 10/16",
            "30550 + 4/16",
        ],
    ),
    (
        16,
        4,
        [
            "137510 + 1/16",
            "41831 + 7/16",
            "32396 + 10/16",
            "72206 + 12/16",
            "36363 + 10/16",
        ],
    ),
];
const PRIME_TREES: [(u64, usize, usize, [&str; 2]); 2] = [
    (10, 4, 4, ["146345 + 2/16", "15435 + 1/16"]),
    (6, 6, 6, ["145167 + 12/16", "19550 + 13/16"]),
];

/// **A short reading at the grain**, `n + k/16 + ε` (the enclosure's two endpoints when their
/// cells differ).
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

/// A class's code a cell, read short.
fn per_cell(interval: &ExactInterval, cells: usize) -> String {
    if cells == 0 {
        return "-".to_string();
    }
    let count = Rat::from_integer(BigInt::from(cells));
    short(&ExactInterval {
        lower: &interval.lower / &count,
        upper: &interval.upper / &count,
    })
}

/// `a − b`, exactly, read short.
fn minus(a: &ExactInterval, b: &ExactInterval) -> String {
    short(&interval_difference(a, b).expect("a difference"))
}

fn truth_of(form: &SymbolicSurprisal) -> ExactInterval {
    on_grid(&form.enclosure().expect("an enclosure"))
}

fn log2_form(value: u64) -> SymbolicSurprisal {
    SymbolicSurprisal::log2_of_ratio(&Rat::from_integer(BigInt::from(value))).expect("log₂")
}

/// An exact form in `log₂ p`.
fn form(value: &SymbolicSurprisal) -> String {
    if value.is_zero() {
        return "0".to_string();
    }
    value
        .terms()
        .iter()
        .map(|(prime, coefficient)| format!("{} log₂ {prime}", exact(coefficient)))
        .collect::<Vec<_>>()
        .join(" + ")
}

fn tree(alphabet: usize, depth: usize, cells: usize) -> Box<dyn Family> {
    Box::new(TreeFamily::new(tree_declaration(alphabet, depth, cells), 1).expect("a declared tree"))
}

fn sum(parts: impl Iterator<Item = ExactInterval>) -> ExactInterval {
    parts.fold(point(0), |total, part| {
        interval_sum(&total, &part).expect("a sum")
    })
}

/// **One class's lines** (module header).
fn class_lines(
    name: &str,
    reading: &PartReading,
    truth: &ExactInterval,
    truth_form: &str,
    recorded: &str,
) {
    let tree = reading.families[0].as_ref().expect("the tree lives");
    println!(
        "    {name} ({} cells), the truth {truth_form} = {}:",
        reading.cells,
        short(truth)
    );
    println!(
        "      the tree (its own code): {} (a cell {}; recorded {recorded} + ε), − truth {}",
        short(tree),
        per_cell(tree, reading.cells),
        minus(tree, truth)
    );
    match &reading.families[1] {
        Some(composed) => println!(
            "      the composed egg: {} (a cell {}), − truth {}",
            short(composed),
            per_cell(composed, reading.cells),
            minus(composed, truth)
        ),
        None => println!("      the composed egg: dead"),
    }
    println!(
        "      the population: {} (a cell {}), − truth {}",
        short(&reading.population),
        per_cell(&reading.population, reading.cells),
        minus(&reading.population, truth)
    );
    println!(
        "      the record clock's value here, code(tree alone) − code(P): {}",
        minus(tree, &reading.population)
    );
}

fn located_lines(receipt: &PopulationReceipt) {
    let Some(keys) = &receipt.families[1].keys else {
        return;
    };
    let names = ["the record clock's offset", "the counter's start"];
    for (factor, survivors) in keys.survivors.iter().enumerate() {
        let masses: Vec<String> = keys
            .masses
            .get(factor)
            .map(|masses| masses.iter().map(exact).collect())
            .unwrap_or_default();
        let posterior = if masses.is_empty() {
            "uniform over the survivors".to_string()
        } else {
            masses.join(", ")
        };
        println!(
            "  located: {} of {} keys, survivors {:?}, posterior {posterior}",
            names.get(factor).unwrap_or(&"a factor"),
            factored(&BigUint::from(keys.spaces[factor])),
            survivors
        );
    }
}

fn totals(receipt: &PopulationReceipt, truth: &ExactInterval) {
    let tree = receipt.families[0].code.as_ref().expect("the tree lives");
    let exact_minus =
        |a: &ExactInterval| enclosure(&interval_difference(a, truth).expect("a difference"), GRAIN);
    println!(
        "  in all: the tree {}; the population {}; − truth {}",
        short(tree),
        short(&receipt.code),
        exact_minus(&receipt.code)
    );
    if let Some(composed) = &receipt.families[1].code {
        println!(
            "    the composed egg alone {}, − truth {}",
            short(composed),
            exact_minus(composed)
        );
    }
    println!(
        "    the record clock's value, code(tree alone) − code(P): {}",
        minus(tree, &receipt.code)
    );
    match receipt.selected {
        Some(index) => println!(
            "    selected (posterior decided above ½): [{index}] {}",
            receipt.families[index].label
        ),
        None => println!("    selected: none decided above ½"),
    }
}

fn close(started: Instant) {
    let peak = resident_set().map_or("unread".to_string(), |(_, peak)| {
        format!("{} kB", peak / 1024)
    });
    println!(
        "  wall (exterior): {} ms; the process's peak resident set {peak}",
        started.elapsed().as_millis()
    );
}

/// **Products in one base** (module header).
fn products_run(base: u64, depth: usize, recorded: &[&str; 5]) {
    let started = Instant::now();
    let family = ProductFamily {
        base,
        digits: DIGITS,
        face: FACE,
        order: DigitOrder::LeastFirst,
    };
    let products =
        Products::draw(&family, RECORDS, &mut Draw::new(SEED)).expect("the drawn products");
    let cells = products.emit();
    let classes = products.classes();
    let parts: Vec<usize> = classes.iter().map(|class| *class as usize).collect();
    println!(
        "hnn_population composition, products in base {base}: L = {DIGITS} least significant first, k = {FACE}; {RECORDS} = 2^12 records of {} cells, seed {SEED}; n = {} cells",
        family.record_length(),
        factored(&BigUint::from(cells.len()))
    );
    let operand = family.operand_code().expect("the operand code");
    let key = log2_form(family.record_length() as u64);
    println!(
        "the truth: a record's operands carry 2L log₂ b = {} bits, every other cell is determined; the record clock's key log₂ {} = {} (its own description: this key and the one bit naming the composed egg)",
        form(&operand),
        family.record_length(),
        short(&truth_of(&key))
    );
    let mut population = Population::new(vec![
        tree(family.alphabet(), depth, cells.len()),
        Box::new(Composed::products(&family, 1).expect("clock ⊳ carry")),
    ])
    .expect("the population");
    println!(
        "  the population: [0] the tree D = {depth} (the terrain notebook's choice), [1] {}; each named by 1 bit, M = 1",
        population
            .families()
            .nth(1)
            .expect("the composed egg")
            .label()
    );
    let (_, readings) = population
        .receive_partitioned(&cells, &parts, 5)
        .expect("the passage");
    let receipt = population.receipt().expect("the receipt");
    let records = Rat::from_integer(BigInt::from(RECORDS));
    let names = [
        (ProductCell::Operand, "operand cells"),
        (ProductCell::Mark, "marks ⊗ = ;"),
        (ProductCell::Trailing, "the product's trailing cells"),
        (ProductCell::Middle, "the product's middle cells"),
        (ProductCell::Leading, "the product's leading cells"),
    ];
    println!("  per class:");
    for (class, name) in names {
        let reading = &readings[class as usize];
        let (truth, truth_form) = match class {
            ProductCell::Operand => {
                let total = operand.scaled(&records);
                (truth_of(&total), form(&total))
            }
            _ => (point(0), "0".to_string()),
        };
        class_lines(name, reading, &truth, &truth_form, recorded[class as usize]);
    }
    let determined: Vec<&PartReading> = names[1..]
        .iter()
        .map(|(class, _)| &readings[*class as usize])
        .collect();
    let composed_determined = sum(determined
        .iter()
        .map(|reading| reading.families[1].clone().expect("alive")));
    let tree_determined = sum(determined
        .iter()
        .map(|reading| reading.families[0].clone().expect("alive")));
    let count: usize = determined.iter().map(|reading| reading.cells).sum();
    println!(
        "  the determined cells together ({count}): the composed egg {} (a cell {}), the tree {} (a cell {}); against the clock's key {}",
        short(&composed_determined),
        per_cell(&composed_determined, count),
        short(&tree_determined),
        per_cell(&tree_determined, count),
        short(&truth_of(&key))
    );
    let total_truth = truth_of(&operand.scaled(&records).plus(&key));
    println!(
        "  the truth with the clock's key: {} + log₂ {} = {}",
        form(&operand.scaled(&records)),
        family.record_length(),
        short(&total_truth)
    );
    totals(&receipt, &total_truth);
    located_lines(&receipt);
    close(started);
}

/// The sieve's work over the window (module header): the deciding face of each integer.
fn sieve_work(window: &PrimeWindow) {
    let sieve = Sieve::of(window, ENUMERATION).expect("the sieve");
    let mut tally = std::collections::BTreeMap::<String, u64>::new();
    for n in window.start..window.end {
        let key = match sieve.verdict(n).1 {
            SieveFace::Unit => "below two".to_string(),
            SieveFace::LastDigit(p) => format!("the last digit reads {p}"),
            SieveFace::DigitSum(p) => format!("the digit sum reads {p}"),
            SieveFace::Alternating(p) => format!("the alternating sum reads {p}"),
            SieveFace::Grating(_) => "a grating".to_string(),
            SieveFace::Gap => "a gap of every grating (prime)".to_string(),
        };
        *tally.entry(key).or_default() += 1;
    }
    let gratings: Vec<u64> = sieve.gratings().collect();
    println!(
        "  the sieve: cheap faces {:?} (last digit, digit sum, alternating sum), then {} gratings {}..={} on the leading index; the deciding face over the window:",
        sieve.cheap(),
        gratings.len(),
        gratings.first().copied().unwrap_or(0),
        gratings.last().copied().unwrap_or(0)
    );
    for (face, count) in &tally {
        println!("    {face}: {}", factored(&BigUint::from(*count)));
    }
}

/// **A prime stream in one base** (module header).
fn primes_run(base: u64, digits: usize, depth: usize, recorded: &[&str; 2]) {
    let started = Instant::now();
    let window = PrimeWindow {
        base,
        start: 0,
        end: WINDOW,
        digits,
        trailing: 1,
        order: DigitOrder::MostFirst,
        emission: PrimeEmission::Digits,
    };
    let cells = window.emit().expect("the window's cells");
    let parts: Vec<usize> = window
        .classes()
        .iter()
        .map(|class| match class {
            PrimeCell::Digit => 0,
            PrimeCell::Primality => 1,
        })
        .collect();
    println!(
        "hnn_population composition, primes in base {base}: the window [0, {}), L = {digits} most significant first and the primality cell; n = {} cells",
        factored(&BigUint::from(WINDOW)),
        factored(&BigUint::from(cells.len()))
    );
    let range = base.pow(digits as u32);
    let key = log2_form(digits as u64 + 1)
        .plus(&log2_form(base).scaled(&Rat::from_integer(BigInt::from(digits))));
    println!(
        "the truth: every cell is determined (the stream's rate is zero); the keys: the record clock's offset log₂ {} and the counter's start log₂ {} = {}, together {} = {}",
        digits + 1,
        factored(&BigUint::from(range)),
        form(&log2_form(base).scaled(&Rat::from_integer(BigInt::from(digits)))),
        form(&key),
        short(&truth_of(&key))
    );
    let density = window.face_code(1).expect("the density's code");
    println!(
        "  the density's code (d = 1) {} = {}",
        form(&density.code),
        short(&truth_of(&density.code))
    );
    sieve_work(&window);
    let mut population = Population::new(vec![
        tree(window.alphabet(), depth, cells.len()),
        Box::new(Composed::primes(&window, ENUMERATION, 1).expect("clock ⊳ counter ⊳ sieve")),
    ])
    .expect("the population");
    println!(
        "  the population: [0] the tree D = {depth} (the terrain notebook's choice), [1] {}; each named by 1 bit, M = 1",
        population
            .families()
            .nth(1)
            .expect("the composed egg")
            .label()
    );
    let (_, readings) = population
        .receive_partitioned(&cells, &parts, 2)
        .expect("the passage");
    let receipt = population.receipt().expect("the receipt");
    let mut unheld = Population::new(vec![Box::new(
        Composed::primes_unheld_counter(&window, ENUMERATION, 0).expect("the unheld counter"),
    ) as Box<dyn Family>])
    .expect("the unheld population");
    let (_, unheld_readings) = unheld
        .receive_partitioned(&cells, &parts, 2)
        .expect("the passage at the unheld counter");
    println!("  per class:");
    for (part, name) in ["digit cells (the counter)", "primality cells"]
        .iter()
        .enumerate()
    {
        class_lines(name, &readings[part], &point(0), "0", recorded[part]);
        let unheld_code = unheld_readings[part].families[0]
            .as_ref()
            .expect("the unheld egg lives");
        let composed = readings[part].families[1].as_ref().expect("alive");
        println!(
            "      the sieve at the counter's unheld port: {} (a cell {}); the counter's value here: {}",
            short(unheld_code),
            per_cell(unheld_code, readings[part].cells),
            minus(unheld_code, composed)
        );
        if part == 1 {
            println!(
                "      the unheld port's primality − the density's code: {}",
                minus(unheld_code, &truth_of(&density.code))
            );
        }
    }
    totals(&receipt, &truth_of(&key));
    let unheld_receipt = unheld.receipt().expect("the unheld receipt");
    let composed = receipt.families[1].code.as_ref().expect("alive");
    println!(
        "    the counter's value in all, code(clock ⊳ (unheld counter ⊳ sieve)) − code(clock ⊳ (counter ⊳ sieve)): {} − {} = {}, beside its key log₂ {}",
        short(&unheld_receipt.code),
        short(composed),
        minus(&unheld_receipt.code, composed),
        factored(&BigUint::from(range))
    );
    located_lines(&receipt);
    close(started);
}

/// **`composition [products | primes]`** (module header).
pub fn harness(which: Option<&str>) {
    if which != Some("primes") {
        for (base, depth, recorded) in &PRODUCT_TREES {
            products_run(*base, *depth, recorded);
        }
    }
    if which != Some("products") {
        for (base, digits, depth, recorded) in &PRIME_TREES {
            primes_run(*base, *digits, *depth, recorded);
        }
    }
}

//! **`arithmetic`: the landmark tree on the arithmetic terrain** (`holonics::holarchy::terrain::
//! arithmetic`; the record of September 27 on the faces of integers, §7 and §9; #73). Included by
//! `hnn_terrain.rs` as its `arithmetic` mode; count-only, a committed command run once in release,
//! never a test. These are **development receipts**: the conversation cut stays the living
//! substrate and the milestone (Brandon's ruling of August 26), and no claim here is joined to the
//! cut's.
//!
//! ```sh
//! cargo run --release -p holonics --example hnn_terrain -- arithmetic
//! ```
//!
//! [definition; agent-inferred] **Products** (`arithmetic::Products`) in bases 2, 10 and 16: `L = 4`
//! digits an operand, least significant first, face width `k = 2`, `2^12` records `a ⊗ c = P ;` of
//! `4L + 3 = 19` cells drawn by the seeded draw [`SEED`], so `n = 2^12·19 = 77824` cells. **Primes**
//! (`arithmetic::PrimeWindow`) over the window `[0, 10^4)`: the digit cells with the primality cell,
//! most significant first (so the last digit stands just before the primality cell), in base 10
//! (`L = 4`) and base 6 (`L = 6`), and the bare prime indicator (one cell an integer, the base only
//! in its truth).
//!
//! Each run states its cost first, then its truth, then the receiving tree
//! (`compression::landmark::context`, the cell-only family, the `½` stop prior, KT nodes,
//! `L_R = 16`) through the prequential harness (`hnn::reference`): the depth sweep
//! (`choose_depth_within`, `D ≤ 48`), the passage with its online baselines at the chosen depth, and
//! **the code on each cell class separately** (`tree_prequential` with the class's cells as the
//! scored-apart range: one tree run a class, every cell still scored before its own deposit), each
//! against its truth: the operand cells at the operand entropy `2L log₂ b` a record, exactly, and
//! every determined cell (the marks, the product's trailing, middle and leading cells, the digit
//! cells of the counter, the primality cells) at zero. The primality cells are also read against
//! the density's code through a face (`PrimeWindow::face_code`): the density alone (`d = 1`) and
//! the trailing face (`d = b`). A control depth, declared and never chosen, repeats the class codes:
//! the record span (`4L + 2` for products, `L + 1` for the digit cells of the counter), at which
//! every determined cell's context holds what determines it.
//!
//! Every reading is exact (the notebook's exterior, `exterior.rs`): bits are enclosures with exact
//! endpoints read at `L_R = 16` as `n + k/16 + ε`; no decimal is printed.

use std::ops::Range;
use std::time::Instant;

use holonics::compression::landmark::context::cell_letters;
use holonics::hnn::Cut;
use holonics::hnn::reference::{choose_depth_within, prequential, tree_prequential};
use holonics::holarchy::terrain::Draw;
use holonics::holarchy::terrain::arithmetic::{
    DigitOrder, Factorization, PrimeCell, PrimeEmission, PrimeWindow, ProductCell, ProductFamily,
    Products,
};
use holonics::ratio::Rat;
use holonics::ratio::surprisal::SymbolicSurprisal;
use num_bigint::{BigInt, BigUint};

use super::exterior::{difference, enclosure, exact, per, ratio, resident_set};
use super::{DEEPEST, GRAIN, SEED, coded_lines, declaration, factored, on_grid};

/// The products' records `2^12`, digits an operand `L = 4` and face width `k = 2`.
const RECORDS: usize = 1 << 12;
const DIGITS: usize = 4;
const FACE: usize = 2;

/// The prime window `[0, 10^4)`.
const WINDOW: u64 = 10_000;

/// **A cell class with its truth** (module header): the exact form of the bits its cells carry,
/// and the references its code is also read against.
struct ClassTruth<C> {
    class: C,
    name: &'static str,
    truth: SymbolicSurprisal,
    references: Vec<(String, SymbolicSurprisal)>,
}

/// An exact form in `log₂ p`, or `0`.
fn form(value: &SymbolicSurprisal) -> String {
    if value.is_zero() {
        return "0".to_string();
    }
    value
        .terms()
        .iter()
        .map(|(prime, coefficient)| format!("({}) log₂ {prime}", exact(coefficient)))
        .collect::<Vec<_>>()
        .join(" + ")
}

/// A factorization as `p^e·q`, `1` for the empty product, `0` for none.
fn factors(factorization: &Option<Factorization>) -> String {
    match factorization {
        None => "0".to_string(),
        Some(factors) if factors.is_empty() => "1".to_string(),
        Some(factors) => factors
            .iter()
            .map(|(p, e)| {
                if *e == 1 {
                    p.to_string()
                } else {
                    format!("{p}^{e}")
                }
            })
            .collect::<Vec<_>>()
            .join("·"),
    }
}

/// The contiguous runs of the positions whose class is `class`.
fn runs<C: PartialEq + Copy>(classes: &[C], class: C) -> Vec<Range<usize>> {
    let mut runs = Vec::new();
    let mut start = None;
    for (position, current) in classes.iter().enumerate() {
        match (start, *current == class) {
            (None, true) => start = Some(position),
            (Some(first), false) => {
                runs.push(first..position);
                start = None;
            }
            _ => {}
        }
    }
    if let Some(first) = start {
        runs.push(first..classes.len());
    }
    runs
}

/// **The code on each cell class at one declared depth** (module header), each against its truth
/// and its references.
fn class_codes<C: PartialEq + Copy>(
    cells: &[usize],
    classes: &[C],
    truths: &[ClassTruth<C>],
    alphabet: usize,
    depth: usize,
) {
    let letters = cell_letters(cells);
    let declared = declaration(alphabet, depth, cells.len());
    for entry in truths {
        let held_out = runs(classes, entry.class);
        let count: usize = held_out.iter().map(|range| range.len()).sum();
        let cut = Cut {
            cells: cells.to_vec(),
            held_out,
        };
        let ([_, bits], _) = tree_prequential(&cut, &letters, &declared).expect("the class's code");
        let truth = on_grid(&entry.truth.enclosure().expect("an enclosure"));
        println!(
            "    {} ({count} cells): {}",
            entry.name,
            enclosure(&bits, GRAIN)
        );
        println!("      a cell: {}", per(&bits, count as u64, GRAIN));
        println!(
            "      its truth {}: {}",
            form(&entry.truth),
            enclosure(&truth, GRAIN)
        );
        println!("      code − truth: {}", difference(&bits, &truth, GRAIN));
        for (name, reference) in &entry.references {
            let reference = on_grid(&reference.enclosure().expect("an enclosure"));
            println!(
                "      code − {name}: {}",
                difference(&bits, &reference, GRAIN)
            );
        }
    }
}

/// **The receiving tree on one stream** (module header): the depth sweep, the passage with its
/// baselines at the chosen depth, the class codes there, and at the declared control depth.
fn gauge<C: PartialEq + Copy>(
    cells: &[usize],
    classes: &[C],
    truths: &[ClassTruth<C>],
    alphabet: usize,
    control: Option<(usize, &str)>,
) {
    let letters = cell_letters(cells);
    let cut = Cut {
        cells: cells.to_vec(),
        held_out: Vec::new(),
    };
    let sweep = choose_depth_within(
        &cut,
        &letters,
        &declaration(alphabet, 1, cells.len()),
        DEEPEST,
    )
    .expect("the depth sweep");
    println!(
        "  the harness's depth sweep (choose_depth_within, D ≤ {DEEPEST}): chosen D = {} of {} tried (charged ⌈log₂ {}⌉ = {} bits); the code in all by depth:",
        sweep.chosen,
        sweep.tried.len(),
        sweep.tried.len(),
        sweep.description_bits
    );
    for (depth, bits) in &sweep.tried {
        println!("    D = {depth}: {}", enclosure(bits, GRAIN));
    }
    let run = prequential(
        &cut,
        &letters,
        &declaration(alphabet, sweep.chosen, cells.len()),
    )
    .expect("the passage");
    println!("  the passage at the chosen D = {}:", sweep.chosen);
    coded_lines(&run.development);
    println!(
        "  the code on each cell class at the chosen D = {} (each cell scored before its own deposit):",
        sweep.chosen
    );
    class_codes(cells, classes, truths, alphabet, sweep.chosen);
    if let Some((depth, name)) = control
        && depth != sweep.chosen
    {
        let ([bits, _], _) =
            tree_prequential(&cut, &letters, &declaration(alphabet, depth, cells.len()))
                .expect("the control's code");
        println!(
            "  the control at D = {depth} ({name}; declared, never chosen): the passage {}",
            enclosure(&bits, GRAIN)
        );
        class_codes(cells, classes, truths, alphabet, depth);
    }
}

/// The cost line every run states first.
fn cost(cells: usize, classes: usize, control: bool) {
    println!(
        "  cost, stated first: n = {cells} cells a pass; the depth sweep at most {DEEPEST} passes (it stops where the code stops falling strictly), then the passage with its baselines and one pass a cell class ({classes}) at the chosen depth{}; a pass deposits each cell at no more than D nodes",
        if control {
            " and again at the control"
        } else {
            ""
        }
    );
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
fn products_run(base: u64) {
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
    println!(
        "hnn_terrain arithmetic, products in base {base}: L = {DIGITS} digits an operand, least significant first, k = {FACE}; {RECORDS} = 2^12 records of 4L + 3 = {} cells, seed {SEED}; n = {} cells, alphabet b + 3 = {}",
        family.record_length(),
        factored(&BigUint::from(cells.len())),
        family.alphabet()
    );
    cost(cells.len(), 5, true);
    let truths = products.truth().expect("the records' truths");
    let operand = family.operand_code().expect("the operand code");
    println!(
        "the truth: a record's operands carry 2L log₂ b = {} bits (uniform on [0, {})²), its key description ⌈log₂ b^(2L)⌉ = {} bits; every other cell is determined",
        form(&operand),
        factored(&BigUint::from(family.operands().expect("b^L"))),
        family.key_bits().expect("the key description")
    );
    let first = &truths[0];
    println!(
        "  the first record: {} ⊗ {} = {} (factored {} ⊗ {}); least significant first, the convolution {:?}, the carry word {:?}, the product's digits {:?}; the trailing face mod b^{FACE} = {}; the leading face: the operands' first {FACE} digits ({}, {}) confine the product to [{}, {}], whose first {FACE} digits of {} read the fibre [{}, {}]; the product reads {}",
        first.operands.0,
        first.operands.1,
        first.value,
        factors(&first.factorizations.0),
        factors(&first.factorizations.1),
        first.product.convolution,
        first.product.carries,
        first.product.digits,
        first.trailing,
        first.leading.operands.0,
        first.leading.operands.1,
        first.leading.products.0,
        first.leading.products.1,
        2 * DIGITS,
        first.leading.fibre.0,
        first.leading.fibre.1,
        first.leading.reading
    );
    let mut widths = std::collections::BTreeMap::new();
    for truth in &truths {
        *widths.entry(truth.leading.width()).or_insert(0u64) += 1;
    }
    let widths: Vec<String> = widths
        .iter()
        .map(|(width, records)| format!("width {width}: {records}"))
        .collect();
    println!(
        "  the leading fibre's width over the records (the leading readings consistent with the operands' leading faces): {}",
        widths.join(", ")
    );
    let records = Rat::from_integer(BigInt::from(RECORDS));
    let determined = |class, name| ClassTruth {
        class,
        name,
        truth: SymbolicSurprisal::zero(),
        references: Vec::new(),
    };
    let classes = [
        ClassTruth {
            class: ProductCell::Operand,
            name: "operand cells",
            truth: operand.scaled(&records),
            references: Vec::new(),
        },
        determined(ProductCell::Mark, "marks ⊗ = ;"),
        determined(ProductCell::Trailing, "the product's trailing cells"),
        determined(ProductCell::Middle, "the product's middle cells"),
        determined(ProductCell::Leading, "the product's leading cells"),
    ];
    gauge(
        &cells,
        &products.classes(),
        &classes,
        family.alphabet(),
        Some((family.record_span(), "the record span 4L + 2")),
    );
    close(started);
}

/// The density read through the face `n mod d` (module header), as a reference.
fn face_reference(window: &PrimeWindow, modulus: u64) -> (String, SymbolicSurprisal) {
    let face = window.face_code(modulus).expect("the face's code");
    let name = if modulus == 1 {
        "the density's code (d = 1)".to_string()
    } else {
        format!("the face n mod {modulus}'s code")
    };
    (name, face.code)
}

/// **Primes in one base, or the bare indicator** (module header).
fn primes_run(base: u64, digits: usize, emission: PrimeEmission) {
    let started = Instant::now();
    let window = PrimeWindow {
        base,
        start: 0,
        end: WINDOW,
        digits,
        trailing: 1,
        order: DigitOrder::MostFirst,
        emission,
    };
    let cells = window.emit().expect("the window's cells");
    let classes = window.classes();
    match emission {
        PrimeEmission::Digits => println!(
            "hnn_terrain arithmetic, primes in base {base}: the window [0, {}), L = {digits} digits most significant first and the primality cell; n = {} cells, alphabet b + 2 = {}",
            factored(&BigUint::from(WINDOW)),
            factored(&BigUint::from(cells.len())),
            window.alphabet()
        ),
        PrimeEmission::Indicator => println!(
            "hnn_terrain arithmetic, the bare prime indicator over [0, {}): n = {} cells, one an integer",
            factored(&BigUint::from(WINDOW)),
            factored(&BigUint::from(cells.len()))
        ),
    }
    let digit_classes = usize::from(emission == PrimeEmission::Digits);
    cost(
        cells.len(),
        1 + digit_classes,
        emission == PrimeEmission::Digits,
    );
    let density = window.face_code(1).expect("the density");
    let primes = density.classes[0].primes;
    println!(
        "the truth: {} primes in the window, the density {}; every cell is determined by the cells before it (the stream's rate is zero)",
        factored(&BigUint::from(primes)),
        ratio(&Rat::new(BigInt::from(primes), BigInt::from(WINDOW)))
    );
    let moduli: Vec<u64> = match emission {
        PrimeEmission::Digits => vec![1, base],
        PrimeEmission::Indicator => vec![1, 2, 6, 10, 30],
    };
    for modulus in &moduli {
        let face = window.face_code(*modulus).expect("the face's code");
        let enclosed = on_grid(&face.code.enclosure().expect("an enclosure"));
        println!(
            "  the density read through n mod {modulus} (Σ_r |W_r| H(π_r/|W_r|)): {} bits; {}",
            form(&face.code),
            enclosure(&enclosed, GRAIN)
        );
    }
    if emission == PrimeEmission::Digits {
        let faces = window.cheap_faces().expect("the cheap faces");
        let [last, sum, alternating] = faces.primes();
        println!(
            "  the cheap faces of base {base}: the last digit reads {last:?}, the digit sum {sum:?}, the alternating sum {alternating:?}"
        );
    }
    let references = moduli
        .iter()
        .map(|modulus| face_reference(&window, *modulus))
        .collect();
    let mut truths = vec![ClassTruth {
        class: PrimeCell::Primality,
        name: "primality cells",
        truth: SymbolicSurprisal::zero(),
        references,
    }];
    if emission == PrimeEmission::Digits {
        truths.insert(
            0,
            ClassTruth {
                class: PrimeCell::Digit,
                name: "digit cells (the counter)",
                truth: SymbolicSurprisal::zero(),
                references: Vec::new(),
            },
        );
    }
    let control = (emission == PrimeEmission::Digits)
        .then_some((window.record_length(), "the record span L + 1"));
    gauge(&cells, &classes, &truths, window.alphabet(), control);
    close(started);
}

/// **`arithmetic`** (module header).
pub fn harness() {
    for base in [2, 10, 16] {
        products_run(base);
    }
    primes_run(10, 4, PrimeEmission::Digits);
    primes_run(6, 6, PrimeEmission::Digits);
    primes_run(10, 4, PrimeEmission::Indicator);
}

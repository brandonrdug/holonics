//! **`arithmetic`: the arithmetic contract's acceptance run** (THE_REBUILD U6 item 3; the record
//! `2026-09-29_THE_ARITHMETIC_CONTRACT_A_NUMERAL_IS_A_FACE_OF_A_COUNTING_NAVIGATOR_AND_ITS_PRODUCER_IS_A_KEY.md`,
//! §6; #73, #148, #63). Included by `hnn_population.rs` as its `arithmetic` mode. The streams are
//! synthetic (`holonics::holarchy::terrain::arithmetic::Expressions`); the receipts are exact; a
//! committed command run once in release, never a test.
//!
//! ```sh
//! cargo run --release -p holonics --example hnn_population -- arithmetic
//! cargo run --release -p holonics --example hnn_population -- arithmetic development
//! ```
//!
//! [definition; agent-inferred] **The pin** (committed in one commit before the pinned run; the
//! constants below): the seed [`SEED`], whose draws no run read before that commit (the development
//! runs read [`DEVELOPMENT_SEED`], the tests their own seeds); `N = 2^10` expressions a base
//! ([`EXPRESSIONS`]), one draw serving the three charts of a base; operands below `2^13`
//! ([`OPERANDS`]) and exponents below 4 ([`EXPONENTS`]); the bases 2, 10 and 16 in that order,
//! then the faces-only control, then the release keys, all from the one seeded draw; the byte tree
//! at depth [`DEPTH`] over the 256 bytes (cell-only letters, the `½` stop prior, KT nodes,
//! `L_R = 16`), its declared population the stream's cells and [`REQUESTS`]; the projection
//! ([`PROJECTED_SECONDS`], [`PROJECTED_BYTES`]) against the caps of ten minutes and 20 GB.
//!
//! [definition; agent-inferred] **The receivers.** On each stream the expression egg
//! (`receiver::population::arithmetic::ExpressionEgg`: the numeral port ⊳ the `^` pairing ⊳ the holds
//! sheet over the byte tree) reads every cell once, each scored before its deposit; **the byte tree
//! alone** is the egg's own byte tree, whose face of every cell the egg returns beside its own
//! (`CellReading::tree`): one tree a stream, read on the same cells.
//!
//! [definition] **Printed, exactly** (the record's §6):
//! - **A1**: on every holding expression the result cells (digits and end) under the located key's
//!   sheet, `A + B ≥ P(holds)` checked as an exact rational inequality expression by expression,
//!   and their total against `2N − log₂ C(2N, N)` (the priors' product checked equal to
//!   `C(2N, N)/4^N` exactly); the egg's own sheet parts (the pairing mixed in) against the same
//!   bound plus the pairing's one bit; the square and its rebase on every expression.
//! - **A2**: every expression whose face two admitted producers share, with its receipt (the
//!   carried producer, the fibre, each family's contribution); the faces-only control of seeded
//!   sums, products and powers (`a ≥ 2`) with the tied fibre face by face and each death's receipt.
//! - **A3**: the port's reach on every expression of the three charts; the contract's result code
//!   equal on equal expressions across charts, and the measured codes' spread; the keystone's value,
//!   the byte tree alone against the egg on the same cells, by class and in all.
//! - **The failure branch**: every unreached expression named by its line; the declared forms outside
//!   the glyph set, each read through the egg and recorded.
//! - **The releases** (the output product): requests released as egg packing beside the byte tree's
//!   release from its face under the same keys.
//! - Wall and peak resident set against the projection.
//!
//! Bits are enclosures with exact endpoints read at `L_R = 16` as `n + k/16 + ε`; no decimal is
//! printed.

use std::collections::BTreeMap;
use std::time::Instant;

use holonics::compression::landmark::context::{
    Capacity, LandmarkDeclaration, LetterFamily, PassageCode, StopPrior,
};
use holonics::holarchy::terrain::Draw;
use holonics::holarchy::terrain::arithmetic::{
    Chart, ExpressionFamily, ExpressionStream, Expressions, Producer, Slot, digit_of,
};
use holonics::ratio::Rat;
use holonics::ratio::algebraic::{ExactInterval, interval_difference, log2_enclosure};
use holonics::receiver::population::arithmetic::{
    ExpressionEgg, ExpressionPhase, ExpressionRelease, KeyReading,
};
use holonics::receiver::population::{Family, TreeFamily};
use holonics::receiver::release::{ReleaseReturn, draw_exact};
use num_bigint::{BigInt, BigUint};
use num_traits::One;

use super::GRAIN;
use super::exterior::{against, enclosure, exact, reading_of, resident_set};

/// **The pinned seed**: the draw's initial configuration for the acceptance run.
pub const SEED: u64 = 2_026_092_903;

/// The development runs' seed (never the pinned one).
pub const DEVELOPMENT_SEED: u64 = 2_026_092_913;

/// `N = 2^10` expressions a base, one draw serving the three charts.
const EXPRESSIONS: usize = 1 << 10;

/// The operands' bound `2^13` (the record's `347 × 5102` lies below it; every Rust line stays
/// within `i32`).
const OPERANDS: u64 = 1 << 13;

/// The exponents' bound: `a^e` for `e < 4`.
const EXPONENTS: u64 = 4;

/// The byte tree's depth: sixteen bytes span the longest run between an operand and the result's
/// first glyph in the three charts (`B * 0x13EE == 0x`).
const DEPTH: usize = 16;

/// The byte tree's declared population beyond a stream's cells: room for the release requests.
const REQUESTS: u64 = 1 << 12;

/// The faces-only control: runs a producer, faces a run, the left operand's range `[2, 16)` and the
/// clock's start range `[0, 8)` (each family's keys the same ranges).
const RUNS: usize = 1 << 6;
const FACES: usize = 4;
const LEFTS: u64 = 1 << 4;
const STARTS: u64 = 1 << 3;

/// **The projection** (the pin): the whole run's wall and peak resident set, projected from the
/// development run on [`DEVELOPMENT_SEED`] (the same sizes: 105877 ms and 623000 kB, one core) with
/// room for a loaded host, against the caps of ten minutes and 20 GB. A run past its projection of
/// time stops and reports its partial evidence as incomplete; its peak is read against the
/// projection at the end.
const PROJECTED_SECONDS: u64 = 4 * 60;
const PROJECTED_BYTES: u128 = 1 << 30;

/// A cell's class on the truth's partition.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Class {
    Syntax,
    Start,
    Glyph,
    End,
}

const CLASSES: [(Class, &str); 4] = [
    (Class::Syntax, "the chart's other cells"),
    (Class::Start, "the result's first glyph"),
    (Class::Glyph, "the result's other glyphs"),
    (Class::End, "the numeral's end"),
];

fn byte_tree(cells: usize) -> TreeFamily {
    TreeFamily::new(
        LandmarkDeclaration {
            alphabet: 256,
            depth: DEPTH,
            forced: 0,
            population: cells as u64 + REQUESTS,
            grain: GRAIN,
            family: LetterFamily::cells(),
            prior: StopPrior::half(),
            capacity: Capacity::Unbounded,
        },
        0,
    )
    .expect("a declared byte tree")
}

fn bits(code: &PassageCode) -> ExactInterval {
    code.bits().expect("an enclosure")
}

fn log2(value: &Rat) -> ExactInterval {
    log2_enclosure(value).expect("a positive ratio")
}

/// `−log₂` of a positive ratio, enclosed.
fn code_of(value: &Rat) -> ExactInterval {
    let log = log2(value);
    ExactInterval {
        lower: -log.upper,
        upper: -log.lower,
    }
}

fn short(interval: &ExactInterval) -> String {
    reading_of(interval, GRAIN)
}

fn minus(a: &ExactInterval, b: &ExactInterval) -> ExactInterval {
    interval_difference(a, b).expect("a difference")
}

fn text(glyphs: impl IntoIterator<Item = usize>) -> String {
    let bytes: Vec<u8> = glyphs.into_iter().map(|cell| cell as u8).collect();
    String::from_utf8_lossy(&bytes)
        .replace('\n', "\\n")
        .to_string()
}

fn key(draw: &mut Draw) -> Rat {
    Rat::new(BigInt::from(draw.next()), BigInt::from(1u128 << 64))
}

/// An integer with its factorization, from the receipt's.
fn with_factors(value: &BigUint, factors: &Option<Vec<(u64, u32)>>) -> String {
    match factors {
        Some(factors) if factors.len() == 1 && factors[0].1 == 1 => format!("{value} (prime)"),
        Some(factors) if !factors.is_empty() => format!(
            "{value} = {}",
            factors
                .iter()
                .map(|(p, e)| if *e == 1 {
                    p.to_string()
                } else {
                    format!("{p}^{e}")
                })
                .collect::<Vec<_>>()
                .join("·")
        ),
        _ => value.to_string(),
    }
}

/// One expression's measured parts, kept for the cross-chart comparison: the contract's bound
/// `Σ_held W·P(holds)` and the result cells' measured sheet product.
#[derive(Clone)]
struct Measured {
    bound: Rat,
    sheet: Rat,
}

/// One stream's reading.
struct StreamReading {
    measured: Vec<Option<Measured>>,
    egg: ExpressionEgg,
}

/// **One stream through the egg** (module header).
fn stream_run(stream: &ExpressionStream, started: Instant) -> Option<StreamReading> {
    let n = stream.cells.len();
    let mut egg = ExpressionEgg::new(0, byte_tree(n)).expect("the expression egg");
    let mut class = vec![Class::Syntax; n];
    for truth in &stream.truths {
        class[truth.result.start] = Class::Start;
        class[truth.result.start + 1..truth.result.end].fill(Class::Glyph);
        class[truth.end] = Class::End;
    }
    let index = |class: Class| class as usize;
    let mut egg_codes = [PassageCode::new(); 4];
    let mut tree_codes = [PassageCode::new(); 4];
    let (mut sheet_code, mut chart_code) = (PassageCode::new(), PassageCode::new());
    let (mut located_code, mut bound_code) = (PassageCode::new(), PassageCode::new());
    let (mut bound_product, mut prior_product) = (Rat::one(), Rat::one());
    let mut counts: BTreeMap<&str, u64> = BTreeMap::new();
    let mut unreached: Vec<String> = Vec::new();
    let mut shared: BTreeMap<Vec<Producer>, (u64, String)> = BTreeMap::new();
    let mut measured: Vec<Option<Measured>> = vec![None; stream.truths.len()];
    let mut sheet = Rat::one();
    let mut awaited = false;
    let mut next = 0usize;
    let mut partings = 0u64;
    let (mut syntax, mut syntax_equal) = (0u64, 0u64);
    let mut shared_count: BTreeMap<&str, u64> = BTreeMap::new();
    for (position, &cell) in stream.cells.iter().enumerate() {
        if position % (1 << 12) == 0 && started.elapsed().as_secs() > PROJECTED_SECONDS {
            println!(
                "  incomplete: the run passed its projection of {PROJECTED_SECONDS} s at cell {position} of {n}"
            );
            return None;
        }
        let phase = egg.port().phase();
        let face = egg.receive(cell).expect("a received cell");
        let last = egg.last().expect("the cell's reading").clone();
        egg_codes[index(class[position])]
            .face(&face)
            .expect("a face");
        tree_codes[index(class[position])]
            .face(&last.tree)
            .expect("a face");
        if class[position] == Class::Start {
            awaited = phase == ExpressionPhase::Awaiting;
        }
        if class[position] == Class::Syntax {
            syntax += 1;
            syntax_equal += u64::from(face == last.tree);
        }
        if class[position] != Class::Syntax {
            sheet = &sheet * &last.sheet;
            if !last.sheet.is_one() {
                sheet_code.face(&last.sheet).expect("a face");
            }
            if !last.chart.is_one() {
                chart_code.face(&last.chart).expect("a face");
            }
        }
        if class[position] != Class::End {
            continue;
        }
        let truth = &stream.truths[next];
        next += 1;
        let receipt = egg.receipt().filter(|_| egg.counts().closed == next as u64);
        let carried = receipt.and_then(|receipt| {
            receipt
                .readings
                .iter()
                .find(|reading: &&KeyReading| reading.held && reading.producer == truth.producer)
        });
        let reached = awaited
            && receipt.is_some_and(|receipt| {
                receipt
                    .result
                    .as_ref()
                    .is_some_and(|result| result.value() == truth.value)
            })
            && carried.is_some();
        let (Some(receipt), Some(carried), true) = (receipt, carried, reached) else {
            unreached.push(text(stream.cells[truth.line.clone()].iter().copied()));
            sheet = Rat::one();
            continue;
        };
        *counts.entry("reached").or_default() += 1;
        let telescope: Rat = receipt
            .readings
            .iter()
            .map(|reading| &reading.weight * (&reading.holds + &reading.free))
            .sum();
        let bound: Rat = receipt
            .readings
            .iter()
            .filter(|reading| reading.held)
            .map(|reading| &reading.weight * &reading.prior)
            .sum();
        *counts.entry("sheet = Σ W (A + B)").or_default() += u64::from(sheet == telescope);
        *counts.entry("sheet ≥ Σ_held W·P(holds)").or_default() += u64::from(sheet >= bound);
        let located = &carried.holds + &carried.free;
        *counts
            .entry("A + B ≥ P(holds) under the carried key")
            .or_default() += u64::from(located >= carried.prior);
        let kt = Rat::new(
            BigInt::from(2 * (next as u64 - 1) + 1),
            BigInt::from(2 * (next as u64 - 1) + 2),
        );
        *counts.entry("P(holds) = (2i + 1)/(2i + 2)").or_default() +=
            u64::from(carried.prior == kt);
        *counts.entry("square").or_default() += u64::from(carried.square);
        *counts.entry("rebase").or_default() += u64::from(carried.rebase);
        partings += receipt.deaths.len() as u64;
        located_code.face(&located).expect("a face");
        bound_code.face(&bound).expect("a face");
        bound_product = &bound_product * &bound;
        prior_product = &prior_product * &carried.prior;
        if receipt.fibre.len() >= 2 {
            *shared_count.entry("shared faces").or_default() += 1;
            *shared_count
                .entry("each with a receipt naming its carried producer in the fibre")
                .or_default() += u64::from(receipt.fibre.contains(&carried.producer));
            let entry = shared
                .entry(receipt.fibre.clone())
                .or_insert((0, String::new()));
            entry.0 += 1;
            if entry.1.is_empty() {
                let contributions: Vec<String> = receipt
                    .readings
                    .iter()
                    .map(|reading| {
                        format!(
                            "[{}: W {}, holds W·A = {}, free W·B = 2^−({})]",
                            reading.producer.name(),
                            exact(&reading.weight),
                            exact(&(&reading.weight * &reading.holds)),
                            short(&code_of(&(&reading.weight * &reading.free)))
                        )
                    })
                    .collect();
                entry.1 = format!(
                    "`{}`: carried {} (the operator glyph's key), result {}; contributions {}",
                    text(stream.cells[truth.line.clone()].iter().copied()).trim_end_matches("\\n"),
                    carried.producer.name(),
                    with_factors(&truth.value, &truth.factorization),
                    contributions.join(" ")
                );
            }
        }
        measured[truth.index] = Some(Measured {
            bound,
            sheet: sheet.clone(),
        });
        sheet = Rat::one();
    }
    let n_expressions = stream.truths.len() as u64;
    let reached = counts.get("reached").copied().unwrap_or(0);
    println!(
        "  reach: {reached} of {n_expressions} expressions reached; the egg's counts {:?}",
        egg.counts()
    );
    for (name, count) in &counts {
        if *name != "reached" {
            println!("    {name}: {count} of {reached}");
        }
    }
    // A1: the telescope and the bound.
    let central = {
        let n = reached;
        let mut value = Rat::one();
        for i in 0..n {
            value *= Rat::new(BigInt::from(2 * i + 1), BigInt::from(2 * i + 2));
        }
        value
    };
    let binomial = {
        let n = reached as usize;
        let mut c = BigUint::one();
        for i in 0..n {
            c = c * BigUint::from((2 * n - i) as u64) / BigUint::from((i + 1) as u64);
        }
        Rat::new(
            BigInt::from(c),
            BigInt::from(BigUint::from(4u32).pow(n as u32)),
        )
    };
    println!(
        "  A1 the priors' product ∏ (2i + 1)/(2i + 2) = C(2N, N)/4^N at N = {reached}: {}; ∏ Σ_held W·P(holds) = that · 2^−{partings} (the pairing's partings): {}",
        prior_product == binomial && central == binomial,
        bound_product == &binomial / Rat::from_integer(BigInt::from(1u64 << partings))
    );
    let sheet_bound = code_of(&binomial);
    let located = bits(&located_code);
    let exactly = counts
        .get("A + B ≥ P(holds) under the carried key")
        .copied()
        .unwrap_or(0)
        == reached
        && reached == n_expressions
        && prior_product == binomial;
    println!(
        "  A1 the located key's sheet on the result cells: {}; the bound 2N − log₂ C(2N, N) = {}; code − bound = {}; {}; the two enclosures: the code {} the bound",
        short(&located),
        short(&sheet_bound),
        short(&minus(&located, &sheet_bound)),
        if exactly {
            "within the bound: A + B ≥ P(holds) exactly on every expression and ∏ P(holds) = C(2N, N)/4^N exactly"
        } else {
            "NOT shown within the bound"
        },
        against(&located, &sheet_bound)
    );
    let egg_sheet = bits(&sheet_code);
    let pairing_bound = bits(&bound_code);
    println!(
        "  A1 the egg's sheet parts on the result cells (the pairing mixed in): {}; Σ −log₂ Σ_held W·P(holds) = the bound + {partings} = {}; − {}",
        short(&egg_sheet),
        short(&pairing_bound),
        short(&minus(&egg_sheet, &pairing_bound))
    );
    println!(
        "  the result cells' chart parts (the numeral's start T(S) and the glyph after its end T(y)/T(N), the byte tree's in both receivers): {}",
        short(&bits(&chart_code))
    );
    // A2
    println!(
        "  A2 shared faces: {} expressions whose face two admitted producers share, {} with a receipt naming the carried producer",
        shared_count.get("shared faces").copied().unwrap_or(0),
        shared_count
            .get("each with a receipt naming its carried producer in the fibre")
            .copied()
            .unwrap_or(0)
    );
    if shared.is_empty() {
        println!("  A2 shared faces: none on this stream");
    }
    for (fibre, (count, example)) in &shared {
        println!(
            "  A2 shared face, fibre {{{}}}: {count} expressions, each with its receipt; first: {example}",
            fibre
                .iter()
                .map(|producer| producer.name())
                .collect::<Vec<_>>()
                .join(", ")
        );
    }
    // A3: the keystone's value by class.
    println!(
        "  the chart's other cells: the egg's face equals the byte tree's exactly on {syntax_equal} of {syntax}"
    );
    let mut egg_total = PassageCode::new();
    let mut tree_total = PassageCode::new();
    for (class, name) in CLASSES {
        let (e, t) = (
            bits(&egg_codes[index(class)]),
            bits(&tree_codes[index(class)]),
        );
        println!(
            "  {name} ({} cells): the byte tree alone {}; the egg {}; tree − egg = {}",
            egg_codes[index(class)].factors(),
            short(&t),
            short(&e),
            short(&minus(&t, &e))
        );
        egg_total.join(&egg_codes[index(class)]);
        tree_total.join(&tree_codes[index(class)]);
    }
    let (e, t) = (bits(&egg_total), bits(&tree_total));
    println!(
        "  in all ({n} cells): the byte tree alone {}; the egg {}; the keystone's value, tree − egg = {}",
        enclosure(&t, GRAIN),
        enclosure(&e, GRAIN),
        short(&minus(&t, &e))
    );
    let located_producer = egg.located();
    println!(
        "  the `^` pairing: located {}; keys {}",
        located_producer.map_or("none (no `^` parted the keys)", Producer::name),
        egg.pairing()
            .iter()
            .map(|key| format!(
                "[{}: weight {}, held {}, free {}{}]",
                key.producer.name(),
                exact(&key.weight),
                key.held,
                key.free,
                key.death.as_ref().map_or(String::new(), |death| format!(
                    ", died at `{} {} {}`: its consequence {}, the result read {}, held under {}",
                    death.key.left.value(),
                    String::from_utf8_lossy(death.key.operator.glyphs()),
                    death.key.right.value(),
                    death.value.as_ref().map_or(
                        "not computed (a power past the admitted exponents)".to_string(),
                        |v| v.to_string()
                    ),
                    death
                        .read
                        .as_ref()
                        .map_or("-".to_string(), |v| v.to_string()),
                    death
                        .held
                        .iter()
                        .map(|producer| producer.name())
                        .collect::<Vec<_>>()
                        .join(", ")
                ))
            ))
            .collect::<Vec<_>>()
            .join(" ")
    );
    if unreached.is_empty() {
        println!("  the failure branch: no expression unreached");
    } else {
        println!("  the failure branch: {} unreached:", unreached.len());
        for line in &unreached {
            println!("    `{line}`");
        }
    }
    Some(StreamReading { measured, egg })
}

/// **A3 across a base's charts**: the contract's code (the bound) equal on equal expressions, and
/// the measured codes' widest ratio.
fn across(expressions: &Expressions, readings: &[(Chart, Vec<Option<Measured>>)]) {
    let mut equal = 0u64;
    let mut unequal = 0u64;
    let mut widest: Option<(Rat, usize)> = None;
    for (index, drawn) in expressions.drawn().iter().enumerate() {
        let charts: Vec<&Measured> = readings
            .iter()
            .filter(|(chart, _)| drawn.slot != Slot::Caret || *chart != Chart::Rust)
            .filter_map(|(_, measured)| measured[index].as_ref())
            .collect();
        if charts.len() < 2 {
            continue;
        }
        for pair in charts.windows(2) {
            if pair[0].bound == pair[1].bound {
                equal += 1;
            } else {
                unequal += 1;
            }
            let ratio = if pair[0].sheet >= pair[1].sheet {
                &pair[0].sheet / &pair[1].sheet
            } else {
                &pair[1].sheet / &pair[0].sheet
            };
            if widest.as_ref().is_none_or(|(known, _)| &ratio > known) {
                widest = Some((ratio, index));
            }
        }
    }
    println!(
        "  A3 equal expressions across the charts (sums and products in all three, powers in prose and Lean): {equal} chart pairs with the contract's code −log₂ Σ_held W·P(holds) equal exactly, {unequal} unequal"
    );
    if let Some((ratio, index)) = widest {
        println!(
            "  A3 the measured sheet codes' widest spread on an equal expression (the free key's share, the byte tree's belief): |Δ| = {} at expression {index}",
            short(&log2(&ratio))
        );
    }
}

/// **The faces-only control** (module header): seeded runs of sums, products and powers along the
/// right operand's clock; each producer family's keys `(a, k)` filtered by the faces.
fn control(draw: &mut Draw) {
    let producers = [Producer::Sum, Producer::Product, Producer::Power];
    let face = |producer: Producer, a: u64, k: u64| -> u128 {
        let (a, k) = (u128::from(a), u128::from(k));
        match producer {
            Producer::Sum => a + k,
            Producer::Product => a * k,
            _ => a.pow(k as u32),
        }
    };
    let keys: Vec<(u64, u64)> = (2..LEFTS)
        .flat_map(|a| (0..STARTS).map(move |k| (a, k)))
        .collect();
    println!(
        "faces-only control: {RUNS} runs a producer of {FACES} faces f_t = p(a, k + t), a ∈ [2, {LEFTS}), k ∈ [0, {STARTS}); each family's keys the same {} pairs; the provenance code is log₂ of the tied fibre",
        keys.len()
    );
    let mut sequences: BTreeMap<(Producer, Vec<usize>), u64> = BTreeMap::new();
    let mut deaths: BTreeMap<(Producer, Producer, usize), (u64, String)> = BTreeMap::new();
    let mut late = 0u64;
    let mut carried_dead = 0u64;
    for &carried in &producers {
        for _ in 0..RUNS {
            let a = 2 + draw.below((LEFTS - 2) as usize) as u64;
            let k = draw.below(STARTS as usize) as u64;
            let faces: Vec<u128> = (0..FACES as u64).map(|t| face(carried, a, k + t)).collect();
            let mut survivors: Vec<Vec<(u64, u64)>> = vec![keys.clone(); producers.len()];
            let mut fibre = Vec::new();
            for (t, &f) in faces.iter().enumerate() {
                for (q, family) in producers.iter().enumerate() {
                    let before = survivors[q].len();
                    survivors[q].retain(|&(a2, k2)| face(*family, a2, k2 + t as u64) == f);
                    if before > 0 && survivors[q].is_empty() {
                        let entry = deaths
                            .entry((carried, *family, t))
                            .or_insert((0, String::new()));
                        entry.0 += 1;
                        if entry.1.is_empty() {
                            entry.1 = format!(
                                "run (a, k) = ({a}, {k}), faces {:?}: killed by face {t} = {f}, its {before} keys before",
                                &faces[..=t]
                            );
                        }
                    }
                }
                let living = survivors.iter().filter(|s| !s.is_empty()).count();
                fibre.push(living);
            }
            let carried_index = producers.iter().position(|p| *p == carried).unwrap();
            if survivors[carried_index].is_empty() {
                carried_dead += 1;
            }
            if fibre[2] != 1 {
                late += 1;
            }
            *sequences.entry((carried, fibre)).or_default() += 1;
        }
    }
    let code = |living: usize| match living {
        1 => "0".to_string(),
        2 => "1".to_string(),
        n => format!("log₂ {n}"),
    };
    for ((carried, fibre), count) in &sequences {
        println!(
            "  {}: tied fibre face by face {:?}, provenance code [{}]: {count} runs",
            carried.name(),
            fibre,
            fibre
                .iter()
                .map(|&n| code(n))
                .collect::<Vec<_>>()
                .join(", ")
        );
    }
    for ((carried, dead, t), (count, example)) in &deaths {
        println!(
            "  death receipt: {} dies at face {t} on {} runs: {count}; first {example}",
            dead.name(),
            carried.name()
        );
    }
    println!(
        "  every other family dead by the third face (index 2): {}; runs where the carried family died: {carried_dead}",
        if late == 0 {
            "yes, on every run".to_string()
        } else {
            format!("no, {late} runs tied past it")
        }
    );
}

/// **The declared forms outside the layouts**, read through a fresh egg (the failure branch's
/// named cases).
fn forms() {
    println!("the failure branch's declared forms, each read through a fresh egg:");
    for form in [
        "example : (2 : ℕ) + 2 = 4 := by norm_num\n",
        "assert!(2u64 + 2 == 4);\n",
        "so 1_000 + 1 = 1001.\n",
        "so 1,000 + 1 = 1,001.\n",
        "so 0o17 + 1 = 0o20.\n",
        "so 5 - 3 = 2.\n",
        "so two + two = four.\n",
        "so 2 + 2 + 2 = 6.\n",
        "example : 2 ^ 70 = 1180591620717411303424 := by norm_num\n",
        "so 2 + 2 = 5.\n",
    ] {
        let cells: Vec<usize> = form.bytes().map(usize::from).collect();
        let mut egg = ExpressionEgg::new(0, byte_tree(cells.len())).expect("an egg");
        for &cell in &cells {
            egg.receive(cell).expect("a cell");
        }
        let counts = egg.counts();
        let verdict = if counts.held > 0 {
            "reached, held"
        } else if counts.failed > 0 {
            "reached, held under no key that computed"
        } else if counts.unreached > 0 {
            "keyed and closed, no consequence computed: unreached"
        } else if counts.keyed > 0 {
            "keyed, broken before a result: unreached"
        } else {
            "never keyed: unreached"
        };
        let readings = egg.receipt().map_or(String::new(), |receipt| {
            format!(
                "; read `{} {} {}` → {}: {}",
                receipt.key.left.value(),
                String::from_utf8_lossy(receipt.key.operator.glyphs()),
                receipt.key.right.value(),
                receipt
                    .result
                    .as_ref()
                    .map_or("-".to_string(), |result| result.value().to_string()),
                receipt
                    .readings
                    .iter()
                    .map(|reading| format!(
                        "{} {}",
                        reading.producer.name(),
                        match (&reading.value, reading.held) {
                            (None, _) => "not computed (past the admitted exponents)".to_string(),
                            (Some(value), true) => format!("{value}, held"),
                            (Some(value), false) => format!("{value}, not held"),
                        }
                    ))
                    .collect::<Vec<_>>()
                    .join("; ")
            )
        });
        println!("  `{}`: {verdict}{readings}", form.trim_end());
    }
}

/// **The record's shared faces** (A2): `2 + 2`, `2 · 2`, `2 ^ 2` written in each chart in bases 10
/// and 2, read through a fresh egg a chart and base; each receipt's carried producer, fibre and
/// contributions.
fn record_faces() {
    println!("A2 the record's shared faces, each chart and base through a fresh egg:");
    for base in [10u64, 2] {
        for chart in Chart::ALL {
            let mut cells: Vec<usize> = Vec::new();
            let mut lines = Vec::new();
            for producer in [Producer::Sum, Producer::Product, chart.caret()] {
                let mut line = chart.request(producer, base, 2, 2).expect("a request");
                let value = producer
                    .scalar(&BigUint::from(2u32), &BigUint::from(2u32))
                    .expect("a value");
                line.extend(
                    holonics::holarchy::terrain::arithmetic::numeral(
                        base,
                        &holonics::holarchy::terrain::arithmetic::encode(base, &value)
                            .expect("a word"),
                    )
                    .expect("a numeral"),
                );
                line.extend(chart.close());
                lines.push(line.clone());
                cells.extend(line.into_iter().map(usize::from));
            }
            let mut egg = ExpressionEgg::new(0, byte_tree(cells.len())).expect("an egg");
            let mut line = 0;
            for &cell in &cells {
                let closed = egg.counts().closed;
                egg.receive(cell).expect("a cell");
                if egg.counts().closed > closed {
                    let receipt = egg.receipt().expect("a receipt");
                    println!(
                        "  `{}`: fibre {{{}}}; {}",
                        text(lines[line].iter().map(|&glyph| usize::from(glyph)))
                            .trim_end_matches("\\n"),
                        receipt
                            .fibre
                            .iter()
                            .map(|producer| producer.name())
                            .collect::<Vec<_>>()
                            .join(", "),
                        receipt
                            .readings
                            .iter()
                            .map(|reading| format!(
                                "under the `^` key {}: carried {}, {}, W {}, P(holds) {}, holds W·A = {}{}",
                                egg.pairing()[reading.key].producer.name(),
                                reading.producer.name(),
                                if reading.held { "held" } else { "not held" },
                                exact(&reading.weight),
                                exact(&reading.prior),
                                exact(&(&reading.weight * &reading.holds)),
                                if receipt.deaths.contains(&egg.pairing()[reading.key].producer) {
                                    " (this key died here)"
                                } else {
                                    ""
                                }
                            ))
                            .collect::<Vec<_>>()
                            .join("; ")
                    );
                    line += 1;
                }
            }
        }
    }
}

/// **A request released** (the output product) beside the byte tree's release from its face under
/// the same keys.
fn release(
    egg: &ExpressionEgg,
    chart: Chart,
    producer: Producer,
    base: u64,
    left: u64,
    right: u64,
    draw: &mut Draw,
) {
    let request = match chart.request(producer, base, left, right) {
        Ok(request) => request,
        Err(refusal) => {
            println!(
                "    request {} {left}, {right} in {}: refused, {refusal}",
                producer.name(),
                chart.name()
            );
            return;
        }
    };
    let cells: Vec<usize> = request.iter().map(|&glyph| usize::from(glyph)).collect();
    let keys: Vec<Rat> = (0..64).map(|_| key(draw)).collect();
    let shown = text(cells.iter().copied());
    match egg.release(&cells, &keys).expect("a release") {
        ExpressionRelease::Released(released) => {
            println!(
                "    request `{shown}` ({}, operands {left} and {right}, base {base}, {}): the egg releases `{}`, then the end ({} certified draws at tolerance zero, each cell [{}, {}), the end's class {})",
                producer.name(),
                chart.name(),
                String::from_utf8_lossy(&released.glyphs),
                released.draws.len() + 1,
                exact(&released.draws[0].prior_upper),
                exact(&released.draws[0].through_lower),
                released.end.class
            );
            println!(
                "      receipt: producer {} (the located key of `{}`), value {}, digit word (least significant first) {:?}, carry words {:?}, decoder: base {base}, declaration `{}`, glyphs 0–9 A–F; square {}, rebase {}",
                released.producer.name(),
                String::from_utf8_lossy(released.key.operator.glyphs()),
                with_factors(&released.value, &released.factorization),
                released.consequence.digits,
                released.consequence.carries,
                String::from_utf8_lossy(&released.prefix),
                released.square,
                released.rebase
            );
        }
        ExpressionRelease::Hold { producers, .. } => {
            println!(
                "    request `{shown}`: held, the pairing plural over {:?}",
                producers
            );
        }
    }
    let mut tree = egg.byte_tree().branch_future().expect("a branch");
    for &cell in &cells {
        tree.receive(cell).expect("a request cell");
    }
    let mut drawn = Vec::new();
    for key in keys.iter().take(40) {
        let face = tree.face().expect("the tree's face");
        let Ok(ReleaseReturn::Drawn(certified)) = draw_exact(&face, key) else {
            println!("      the byte tree's draw: unresolved");
            break;
        };
        let glyph = certified.class as u8;
        let continues = digit_of(glyph).is_some() || matches!(glyph, b'x' | b'X');
        drawn.push(certified.class);
        tree.receive(certified.class).expect("a drawn cell");
        if !continues {
            break;
        }
    }
    println!(
        "      control, the byte tree alone on the same request and keys: `{}`",
        text(drawn)
    );
}

/// **`arithmetic [development]`** (module header).
pub fn harness(development: bool) {
    let started = Instant::now();
    let seed = if development { DEVELOPMENT_SEED } else { SEED };
    println!(
        "hnn_population arithmetic ({}): seed {seed}; N = {EXPRESSIONS} = 2^10 expressions a base and chart, operands below 2^13, exponents below {EXPONENTS}; the byte tree D = {DEPTH}; projection: {PROJECTED_SECONDS} s and {} MB at most (the caps), the development run's measurement in the pin",
        if development {
            "development"
        } else {
            "the pinned acceptance run"
        },
        PROJECTED_BYTES >> 20
    );
    let mut draw = Draw::new(seed);
    let mut drawn: Vec<(u64, Expressions)> = Vec::new();
    for base in [2u64, 10, 16] {
        let family = ExpressionFamily {
            base,
            operands: OPERANDS,
            exponents: EXPONENTS,
        };
        drawn.push((
            base,
            Expressions::draw(family, EXPRESSIONS, &mut draw).expect("the drawn expressions"),
        ));
    }
    let mut eggs: Vec<(u64, Chart, ExpressionEgg)> = Vec::new();
    for (base, expressions) in &drawn {
        let slots = |slot: Slot| {
            expressions
                .drawn()
                .iter()
                .filter(|drawn| drawn.slot == slot)
                .count()
        };
        println!(
            "base {base}: {} sums, {} products, {} of the chart's `^`",
            slots(Slot::Sum),
            slots(Slot::Product),
            slots(Slot::Caret)
        );
        let mut readings = Vec::new();
        for chart in Chart::ALL {
            let stream = expressions.emit(chart).expect("the stream");
            println!(
                "{} base {base}: {} cells (bytes); first line `{}`",
                chart.name(),
                stream.cells.len(),
                text(stream.cells[stream.truths[0].line.clone()].iter().copied())
            );
            let Some(reading) = stream_run(&stream, started) else {
                return;
            };
            readings.push((chart, reading.measured));
            eggs.push((*base, chart, reading.egg));
        }
        across(expressions, &readings);
    }
    control(&mut draw);
    record_faces();
    forms();
    println!("the releases (egg packing at the port, after each stream):");
    for (base, chart, egg) in &eggs {
        release(egg, *chart, Producer::Product, *base, 347, 5102, &mut draw);
        let (caret, right) = match chart.caret() {
            Producer::Power => (Producer::Power, 3),
            other => (other, 5102),
        };
        release(egg, *chart, caret, *base, 347, right, &mut draw);
        if *base == 10 && *chart == Chart::Prose {
            release(egg, *chart, Producer::Power, *base, 2, 2, &mut draw);
            release(egg, *chart, Producer::CarryFree, *base, 2, 2, &mut draw);
        }
        if *base == 2 && *chart == Chart::Rust {
            release(egg, *chart, Producer::Power, *base, 2, 2, &mut draw);
        }
    }
    let wall = started.elapsed();
    let peak = resident_set().map_or("unread".to_string(), |(_, peak)| {
        format!(
            "{} kB{}",
            peak / 1024,
            if peak > PROJECTED_BYTES {
                " (past the projection)"
            } else {
                ""
            }
        )
    });
    println!(
        "wall (exterior): {} ms against {PROJECTED_SECONDS} s projected; the process's peak resident set {peak}",
        wall.as_millis()
    );
}

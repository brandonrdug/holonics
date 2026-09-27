//! **The Born receiver on the standing real cut, against and beside the landmark tree** (Decision
//! 33; rebuild step 4, #73): the notebook's receipt of `holonics::hnn::born`, a committed command
//! run once in release, never a test.
//!
//! ```sh
//! cargo run --release -p holonics --example hnn_born -- cut-file .local/cuts/standing-real-cut-campaign-1.bin
//! ```
//!
//! [definition; agent-inferred] **The development harness** (Decision 31): the manifest's held-out
//! range is cut away before anything is read, and every choice is made on the development cells:
//! - **the tree** is its current law through its public API: the receiver's declaration
//!   (`hnn::receiving::landmark_declaration_with`, the cell-only family at campaign 1's depth), read
//!   prequentially (`Landmarks::receive`: each cell scored at the standing before its own deposit);
//! - **the Born face** (`hnn::born::Born`), prequential the same way, for the declared family: both
//!   emissions (`Position`, `Dyadic`) at every register width `χ = 2^j`, `j = 0, …, J` (the whole
//!   family within the cost bound: a first run rising in `χ` while the development code decreased
//!   stopped the `Dyadic` emission at `χ = 2`, whose code sat above `χ = 1`'s, while the `Position`
//!   emission kept falling to `χ = 256`; nothing establishes that the code is unimodal in `χ`, so
//!   no early stop is declared);
//! - **the carrier**: a width whose derived lattices pass the receiver's `i128` carrier at the
//!   declared population is refused (`BornWidths::derived`), and the family stops before it (at the
//!   wide cut's `n* = 2^20` the solve's residual needs 128 bits at `χ = 32`, above the 126 admitted);
//! - **the code lengths**: each population's faces multiplied and enclosed once
//!   (`context::PassageCode`);
//! - **the cost bound `J`**: a digit costs `2χ²` complex products to read (the pair's images) and
//!   about `12χ²` to deposit (the Gram, the preconditioner, the solve and its refinements, the two
//!   rank-one steps), so a development passage of `B·n_dev` digits costs `14χ² B n_dev` products;
//!   `J` is the largest `j` with `14·4^j·B·n_dev ≤ 2^37`, the harness's declared work a passage
//!   (a probe read `333` µs a digit at `χ = 128`, whose `14·128² = 229,376` products take
//!   `1 rem 103,624 over 229,376` ns each), which keeps the largest passage within a minute and the
//!   sweep within minutes (`J = 8`, `χ ≤ 256`, on the standing cut's `8 · 4,958` development
//!   digits);
//! - **the mixture** (Decision 30's law, `hnn::receiving::Mixture`): `q = λ q_T + (1 − λ) q_B`,
//!   `λ = β/(1 + β)`, `β` from 1 stepped after each cell by `q_T(x)/q_B(x)` on the landmark β chart at
//!   the tree's carrier width (the Born face is dyadic and exact, so the step's chart residual is
//!   zero; the rebases' drift is reported);
//! - **the charge**: `⌈log₂⌉` of the family members tried, added to the Born face's and the
//!   mixture's code lengths;
//! - **the choice**: the member whose charged mixture codes least on the development cells; when it
//!   codes below the tree by disjoint enclosures, one held-out pass follows (the whole cut
//!   prequentially, the held-out cells scored before their own deposits); otherwise that is the
//!   result, and no held-out cell is read.
//!
//! [derived] The ideal mixture telescopes, `∏ q = ½ W_T + ½ W_B` (Lean
//! `Compression/Landmark/Context/Tree.sequential_mixture`), so it codes below the tree exactly when the Born face
//! alone does, `L_B < L_T`, up to the chart's drift; the harness reports both orderings.
//!
//! [established-bounded; measured] **The readout**: per member, bits a cell at the receiver's grain
//! (`n + k/L_R + ε`) and exact totals for the Born face, the tree and the mixture; the orderings
//! mixture − tree and Born − tree (charged) by disjoint exact enclosures, or undecided with the
//! overlap; `log₂ β` at the end, the chart's rebases and drift; the receiver's founded loci, stored
//! bits and chart receipts (the solve's refinements and largest certificate, the preconditioner's
//! refreshes, the state's rounding rebases); and wall times in integer milliseconds, a digit's time
//! as a quotient with its remainder in microseconds. The cut is private: only its scope and counts
//! are printed.

#[path = "exterior.rs"]
mod exterior;

use std::time::Instant;

use holonics::compression::landmark::context::{
    LandmarkDeclaration, Landmarks, LetterFamily, PassageCode, address,
};
use holonics::hnn::born::{Born, BornDeclaration, BornReport, Emission};
use holonics::hnn::receiving::{Mixture, MixtureStep, landmark_declaration_with};
use holonics::hnn::{Field, FieldDeclaration};
use holonics::ratio::Rat;
use holonics::ratio::algebraic::ExactInterval;
use holonics::ratio::algebraic::interval_sum;
use num_bigint::BigInt;
use num_traits::One;

use exterior::{against, difference, enclosure, exact, per, read_cut, receiver_grain};

/// The cost bound's declared work: `2^37` complex products a development passage.
const WORK: u128 = 1 << 37;

fn charged(bits: &ExactInterval, description: u64) -> ExactInterval {
    interval_sum(
        bits,
        &ExactInterval::point(Rat::from_integer(BigInt::from(description))),
    )
    .expect("an enclosure")
}

/// `⌈log₂ x⌉` of a positive count.
fn ceil_log2(x: u64) -> u64 {
    u64::from(64 - (x.max(1) - 1).leading_zeros())
}

/// **The tree's prequential faces** over a stream: each cell's executed face before its deposit.
fn tree_faces(cells: &[usize], declaration: &LandmarkDeclaration) -> (Vec<Rat>, u128, u64) {
    let clock = Instant::now();
    let mut tree = Landmarks::new(declaration.clone()).expect("the tree's declaration");
    let faces = (0..cells.len())
        .map(|position| {
            tree.receive(
                &address(cells, position, declaration.depth),
                cells[position],
            )
            .expect("a cell within the declaration")
            .executed
        })
        .collect();
    (faces, clock.elapsed().as_millis(), tree.widths().carrier)
}

/// One member's prequential pass over a stream: the Born face, the tree and the mixture, each
/// summed on the development part and the held-out part.
struct Pass {
    born: [ExactInterval; 2],
    tree: [ExactInterval; 2],
    mixture: [ExactInterval; 2],
    cells: [u64; 2],
    born_ms: u128,
    wall_ms: u128,
    report: BornReport,
    founded: usize,
    bits: u64,
    beta: ExactInterval,
    rebases: u64,
    drift: Rat,
}

fn pass(
    cells: &[usize],
    held_out: &dyn Fn(usize) -> bool,
    trees: &[Rat],
    declaration: &BornDeclaration,
    carrier: u64,
    ring: usize,
) -> Pass {
    let wall = Instant::now();
    let mut born = Born::new(declaration.clone()).expect("a Born declaration");
    let mut mixture = Mixture::new(carrier);
    let (mut born_sum, mut tree_sum, mut mixture_sum) = (
        [PassageCode::new(); 2],
        [PassageCode::new(); 2],
        [PassageCode::new(); 2],
    );
    let mut counts = [0u64; 2];
    let mut born_ms = 0u128;
    for (position, &cell) in cells.iter().enumerate() {
        let part = usize::from(held_out(position));
        let clock = Instant::now();
        let face = born.receive(cell).expect("a Born reception");
        born_ms += clock.elapsed().as_micros();
        let tree = &trees[position];
        let weight = mixture.weight();
        let mixed = &weight * tree + (Rat::one() - &weight) * &face;
        born_sum[part].face(&face).expect("a positive face");
        tree_sum[part].face(tree).expect("a positive face");
        mixture_sum[part].face(&mixed).expect("a positive face");
        mixture
            .step(&MixtureStep {
                ring,
                tree: tree.clone(),
                combined: face,
                residual: Rat::from_integer(BigInt::from(0)),
            })
            .expect("a positive step");
        counts[part] += 1;
    }
    let bits = |codes: [PassageCode; 2]| codes.map(|code| code.bits().expect("an enclosure"));
    Pass {
        born: bits(born_sum),
        tree: bits(tree_sum),
        mixture: bits(mixture_sum),
        cells: counts,
        born_ms: born_ms / 1000,
        wall_ms: wall.elapsed().as_millis(),
        report: born.report().clone(),
        founded: born.founded(),
        bits: born.bits(),
        beta: mixture.log2_beta().expect("log₂ β"),
        rebases: mixture.rebases(),
        drift: mixture.drift().clone(),
    }
}

/// **A strict ordering**, `a` against `b`: decided by disjoint exact enclosures with the exact
/// difference in all and a cell, or undecided with the overlap.
fn ordering(label: &str, a: &ExactInterval, b: &ExactInterval, cells: u64, grain: u64) -> bool {
    println!("  {label}: {}", against(a, b));
    if a.upper < b.lower || a.lower > b.upper {
        let delta = ExactInterval {
            lower: &a.lower - &b.upper,
            upper: &a.upper - &b.lower,
        };
        println!("    difference {}", difference(a, b, grain));
        println!("    a cell: {}", per(&delta, cells, grain));
    } else {
        let lower = if a.lower > b.lower {
            &a.lower
        } else {
            &b.lower
        };
        let upper = if a.upper < b.upper {
            &a.upper
        } else {
            &b.upper
        };
        println!("    overlap [{}, {}] bits", exact(lower), exact(upper));
    }
    a.upper < b.lower
}

fn name(emission: Emission) -> &'static str {
    match emission {
        Emission::Position => "Position",
        Emission::Dyadic => "Dyadic",
    }
}

/// A total of microseconds over `count` digits: the quotient with its remainder.
fn per_digit(total_ms: u128, digits: u64) -> String {
    let micros = total_ms * 1000;
    let digits = u128::from(digits.max(1));
    format!(
        "{} rem {} over {digits} µs a digit",
        micros / digits,
        micros % digits
    )
}

fn member(label: &str, pass: &Pass, part: usize, description: u64, grain: u64) {
    let cells = pass.cells[part];
    let (born, mixture) = (
        charged(&pass.born[part], description),
        charged(&pass.mixture[part], description),
    );
    println!("  {label} ({cells} cells), bits a cell at L_R = {grain}:");
    println!(
        "    Born face alone: {} (uncharged)",
        per(&pass.born[part], cells, grain)
    );
    println!("      total {}", enclosure(&pass.born[part], grain));
    println!("    tree alone: {}", per(&pass.tree[part], cells, grain));
    println!("      total {}", enclosure(&pass.tree[part], grain));
    println!(
        "    mixture: {} (uncharged)",
        per(&pass.mixture[part], cells, grain)
    );
    println!("      total {}", enclosure(&pass.mixture[part], grain));
    println!("    the orderings, the Born face and the mixture charged {description} bits:");
    ordering("mixture − tree", &mixture, &pass.tree[part], cells, grain);
    ordering("Born − tree", &born, &pass.tree[part], cells, grain);
}

fn chart_receipts(pass: &Pass, declaration: &BornDeclaration, grain: u64) {
    let report = &pass.report;
    println!(
        "    log₂ β at the end {}; the β chart's rebases {}, drift ≤ {} bits",
        enclosure(&pass.beta, grain),
        pass.rebases,
        exact(&pass.drift)
    );
    println!(
        "    the receiver: {} loci founded, {} stored bits; {} digits read, {} state rebases rounded; {} locus deposits, {} solve refinements (at most {} in one), {} preconditioner refreshes, the largest solve certificate ‖r‖∞/‖ψ‖∞ ≤ {}",
        pass.founded,
        pass.bits,
        report.digits,
        report.state_rebases,
        report.locus_deposits,
        report.refinements,
        report.most_refinements,
        report.refreshes,
        exact(&report.largest_certificate),
    );
    println!(
        "    wall: the Born receiver {} ms ({}), the pass {} ms (χ = {})",
        pass.born_ms,
        per_digit(pass.born_ms, report.digits),
        pass.wall_ms,
        declaration.width
    );
}

fn main() {
    let arguments: Vec<String> = std::env::args().skip(1).collect();
    let path = match arguments.as_slice() {
        [key, value] if key == "cut-file" => value.clone(),
        _ => {
            println!("usage: hnn_born cut-file <path>");
            return;
        }
    };
    let setup = Instant::now();
    let (bytes, count, held) = read_cut(&path);
    let field = Field::declare(FieldDeclaration::campaign_one(count as u64))
        .expect("campaign 1's declared field over the cut");
    let grain = receiver_grain(&field);
    let alphabet = field.alphabet();
    let receiver = field.receivers()[0].clone();
    let tree_declaration = landmark_declaration_with(&field, &receiver, LetterFamily::cells())
        .expect("the receiver's tree");
    let cells: Vec<usize> = bytes.iter().map(|&byte| usize::from(byte)).collect();
    let development: Vec<usize> = cells
        .iter()
        .enumerate()
        .filter(|(position, _)| !held.contains(position))
        .map(|(_, &cell)| cell)
        .collect();
    let digits = u128::from(64 - (alphabet as u64 - 1).leading_zeros());
    let dev_digits = digits * development.len() as u128;
    let mut bound = 0u32;
    while 14 * (1u128 << (2 * (bound + 1))) * dev_digits <= WORK {
        bound += 1;
    }
    println!(
        "hnn_born: the Born receiver (Decision 33) against and beside the landmark tree over the cut file {path}"
    );
    println!(
        "cut: {count} cells, |A| = {alphabet}; held out: cells {}..{} ({} cells, from the manifest; cut away before the development harness); development: {} cells",
        held.start,
        held.end,
        held.len(),
        development.len()
    );
    println!(
        "declared: n* = {count}, L_R = {grain}, the tree at depth D = {} (its current law, the cell-only family); the cost bound J = {bound} (14·4^J·B·n_dev ≤ 2^37 products, B·n_dev = {dev_digits} digits); setup {} ms",
        tree_declaration.depth,
        setup.elapsed().as_millis()
    );
    let never = |_: usize| false;
    let (trees, tree_ms, carrier) = tree_faces(&development, &tree_declaration);
    println!("the tree's development passage: {tree_ms} ms; its β carrier W = {carrier}");
    println!();

    // The family: both emissions at every declared width within the cost bound and the carrier.
    let mut runs: Vec<(BornDeclaration, Pass)> = Vec::new();
    for emission in [Emission::Position, Emission::Dyadic] {
        for order in 0..=bound {
            let declaration = BornDeclaration {
                alphabet,
                width: 1 << order,
                emission,
                population: count as u64,
                grain,
            };
            if let Err(refusal) = Born::new(declaration.clone()) {
                println!(
                    "{} χ = {} is refused by its carrier at n* = {count}: {refusal}; the family stops there",
                    name(emission),
                    declaration.width
                );
                break;
            }
            let run = pass(
                &development,
                &never,
                &trees,
                &declaration,
                carrier,
                receiver.ring,
            );
            let widths = Born::new(declaration.clone())
                .expect("a declaration")
                .widths();
            println!(
                "{} χ = {} (M = {}, S = {}, L_A = {}, L_H = {}, C = {}, F = {}): Born {} a cell, mixture {} a cell, tree {} a cell",
                name(emission),
                declaration.width,
                widths.face,
                widths.state,
                widths.operator,
                widths.gram,
                widths.chart,
                widths.solve,
                per(&run.born[0], run.cells[0], grain),
                per(&run.mixture[0], run.cells[0], grain),
                per(&run.tree[0], run.cells[0], grain),
            );
            chart_receipts(&run, &declaration, grain);
            runs.push((declaration, run));
        }
    }
    let description = ceil_log2(runs.len() as u64);
    println!();
    println!(
        "the family tried: {} members; description ⌈log₂ {}⌉ = {description} bits",
        runs.len(),
        runs.len()
    );
    println!();
    println!(
        "development, each member (the Born face and the mixture charged {description} bits):"
    );
    for (declaration, run) in &runs {
        member(
            &format!("{} χ = {}", name(declaration.emission), declaration.width),
            run,
            0,
            description,
            grain,
        );
    }
    let (chosen, run) = runs
        .iter()
        .min_by(|a, b| a.1.mixture[0].upper.cmp(&b.1.mixture[0].upper))
        .expect("a member");
    let mixture = charged(&run.mixture[0], description);
    println!();
    println!(
        "the choice: {} χ = {} (the least charged development mixture)",
        name(chosen.emission),
        chosen.width
    );
    let below = ordering(
        "chosen mixture − tree (development, charged)",
        &mixture,
        &run.tree[0],
        run.cells[0],
        grain,
    );
    let digits_read = run.report.digits;
    println!(
        "  its time a digit: {} (the Born receiver's {} ms over {} digits)",
        per_digit(run.born_ms, digits_read),
        run.born_ms,
        digits_read
    );
    if !below {
        println!(
            "no member's mixture codes below the tree on the development cells: that is the result, and no held-out cell is read"
        );
    } else {
        println!();
        println!("the held-out pass (the whole cut, prequential) for the chosen member:");
        let is_held = |position: usize| held.contains(&position);
        let (all_trees, all_tree_ms, all_carrier) = tree_faces(&cells, &tree_declaration);
        println!("  the tree's whole passage: {all_tree_ms} ms");
        let whole = pass(
            &cells,
            &is_held,
            &all_trees,
            chosen,
            all_carrier,
            receiver.ring,
        );
        member("held out", &whole, 1, description, grain);
        member("development (the same pass)", &whole, 0, description, grain);
        chart_receipts(&whole, chosen, grain);
    }
    println!();
    println!(
        "wall time (exterior): the harness {} ms",
        setup.elapsed().as_millis()
    );
}

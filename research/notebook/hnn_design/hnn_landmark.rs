//! **The landmark tree on the standing real cut, executed on its declared dyadic lattice**
//! (Decision 28, count-only; rebuild step 4, #73): the notebook's receipt of
//! `holonics::hnn::landmark::{choose_depth, prequential, oracle_cost}`, a committed command run once
//! in release, never a test.
//!
//! ```sh
//! cargo run --release -p holonics --example hnn_landmark -- cut-file .local/cuts/standing-real-cut-campaign-1.bin
//! cargo run --release -p holonics --example hnn_landmark -- cut-file .local/cuts/standing-real-cut-campaign-1.bin letters
//! cargo run --release -p holonics --example hnn_landmark -- cut-file .local/cuts/standing-real-cut-campaign-1.bin letters contacts
//! cargo run --release -p holonics --example hnn_landmark -- cut-file .local/cuts/standing-real-cut-campaign-1.bin prior
//! cargo run --release -p holonics --example hnn_landmark -- cut-file .local/cuts/standing-real-cut-campaign-1.bin local
//! cargo run --release -p holonics --example hnn_landmark -- cut-file .local/cuts/wide-real-cut.bin wide .local/cuts/standing-real-cut-campaign-1.bin
//! cargo run --release -p holonics --example hnn_landmark -- cut-file .local/cuts/wide-real-cut.bin wide-adopted .local/cuts/standing-real-cut-campaign-1.bin
//! ```
//!
//! [definition; agent-inferred] **The wide cut** (`wide <standing cut>`; Decision 35): the
//! count-only receiver's laws chosen on a larger development cut, then read once held out. The
//! standing cut must be the wide cut's tail (checked), so its cells lie in the wide held-out range.
//! Every code is a population's faces' product enclosed once (`landmark::PassageCode`), and
//! nothing per digit is retained but the `½` tree's splits, the global ladder's and the Born
//! members' (the laws are streamed).
//! - **0. The memory**: the `½` tree's live bytes a node and the baselines' a cell, measured on the
//!   standing cut by the harness's counted allocator (each built alone); the resident bound
//!   `3 (n B D + 2^B − 1)` bytes a node `+ n` bytes a cell (the tree and the two-law stop mixture's
//!   two trees at the a-priori node bound, each cell founding at most `D` nodes in each of its `B`
//!   digit trees, and the baselines) at the standing cut's declared depth, for every power of two
//!   the development stream holds; the largest within Brandon's 20 GB cap, which the pinned cut must
//!   be; and at the pinned population the deepest depth within the cap, which bounds every depth
//!   sweep. The workers of each parallel stage are the memory's: `⌊(budget − resident)/(5/4 ·
//!   bytes)⌋`, the budget the cap or the memory the host has available, whichever is less.
//! - **1. The depth** on the development cells (`choose_depth_within`), charged `⌈log₂⌉` of the
//!   depths tried.
//! - **2. Decision 32's family** (`prior_family(ladder_top)`), each law with its own depth sweep
//!   within the cap (`choose_prior_within`), the choice charged `⌈log₂⌉` of the laws.
//! - **3. The faces at the chosen depth**, prequential on the development cells: the `½` tree, every
//!   other law streamed (its code in all and per dyadic cell, its oracles at the digit and cell
//!   grains, its incumbent joins `(½, law)` at every rung, executed), and the Born family (both
//!   emissions at `χ = 2^j` within the cost bound `14·4^J·B·n_dev ≤ 2^37` and the receiver's
//!   carrier); the oracles `Σ_u min(ℓ_T(u), ℓ_X(u)) − L_T` at the three grains, and the least stop
//!   law in every unit.
//! - **4. The development decisions**, each charged `⌈log₂⌉` of its family, orderings by disjoint
//!   enclosures, each local law refused when its oracle's gain does not exceed its price (the
//!   `local` mode's rule): the Born face alone; at each landmark (every Born member × every rung);
//!   in each digit tree (the `½` tree against every other law at the incumbent's rungs, and the
//!   balanced global ladder; the whole family mixed per digit tree is read ideally, from the laws'
//!   per-dyadic products, and is not a member: its `StopMixture` would hold one tree a law); across
//!   epochs (every Born member × `α = 2^(−j)`, with Decision 30's plain mixture and the exact
//!   dominance bound, by Viterbi on product bounds).
//! - **5. The held-out pass, once**: the `½` tree (its whole passage's widths, operand bits,
//!   rebases, releases, drift, rule, largest certified residual, founded nodes and live bytes: the
//!   scale checks) and the baselines, Decision 32's choice when it is not `½`, each local law whose
//!   charged development code lies below the tree, and Decision 34's adopted law (`½` with `(1, 3)`
//!   at `π_½ = ½`, declared before this cut: a family of one) unless it is the stop choice, each
//!   read on the development cells, the held-out cells, and the standing cut's two parts within
//!   them. `wide-adopted` runs the memory's derivation, the depth and then only that whole passage
//!   of the `½` tree, the baselines and the adopted law.
//! - **6. The standing cut alone** (its own `½` tree at its declared depth and population, from its
//!   first cell), beside the same cells read at the wide cut's standing.
//!
//! [definition; agent-inferred] **Weighing is local** (`local`; Decision 34): on the **development
//! cells only** (the manifest's held-out range is cut away before anything is read), the receiver's
//! tree (`hnn::receiving::landmark_declaration_with`: the cell-only family at `D = 4`, Decision 28's
//! `½`), every law of Decision 32's declared family (`prior_family(ladder_top)`) and every member of
//! Decision 33's Born family (both emissions at `χ = 2^j`, `j ≤ J` by the cost bound
//! `14·4^J·B·n_dev ≤ 2^37`) are read prequentially, each digit's split before its cell's deposit
//! (`Landmarks::receive_digits`, `Born::read`). These per-digit splits are an exterior measurement
//! of this harness; no owner retains them (no tape).
//! - **1. The oracles** `Σ_u min(ℓ_T(u), ℓ_X(u)) − L_T` at three grains (`u` a digit, a cell, a
//!   dyadic cell), each exactly enclosed: the units' products of observed sides on the tree's
//!   lattice compare exactly, and the chosen products' ratio to the tree's is read by one certified
//!   binary logarithm; for every Born member, every stop law (the eight least and the constant-slot
//!   controls printed), and the least stop law in every unit.
//! - **2. The three local laws**, each measured prequentially on the development cells and charged
//!   `⌈log₂⌉` of its family (the tree's depth bits are common and cancel), each ordering decided by
//!   disjoint exact enclosures, each law refused when its oracle's gain does not exceed its price:
//!   - **at each landmark**: the tree under `LocalLaw` at every rung `j = 1..J` of the ladder
//!     (`J = ladder_top`), the external face each Born member's digit split (`rescale_split` onto
//!     the tree's lattice); the oracle the best member's digit grain, the price its family charge
//!     (a landmark's naming is per landmark and cannot be read from a per-digit oracle);
//!   - **in each digit tree**: the owner's joins (`FaceJoins`) on the laws' executed digit faces,
//!     the members the `½` tree against every other law at the incumbent's rungs `j = 1..J`
//!     (`JoinTree::incumbent`) and the balanced joins of the global ladder and of the whole family;
//!     the oracle the best pair's dyadic-cell grain, the price one bit a dyadic cell opened plus the
//!     charge; and the least law in every dyadic cell against its naming (`⌈log₂⌉` of the laws a
//!     dyadic cell);
//!   - **across epochs**: `Mixture::switching` of the tree's and each Born member's cell faces at
//!     `α = 2^(−j)`, `j = 1..⌈log₂ n*⌉`, beside Decision 30's plain mixture; the oracle the best
//!     member's cell grain, the price the best switching sequence's naming (its dominance bound,
//!     Lean `fixed_share`, by exact Viterbi on integers, less the oracle) plus the charge.
//! - **3. The held-out pass**, once, only for a law whose charged development code lies below the
//!   tree: the tree, online order-0, order-1, PPM-2 (`prequential`) and the chosen law over the
//!   whole cut, every cell scored before its own deposit, in all and a cell at the grain; the stop
//!   mixture's pass through the owner's `StopMixture`, checked against the joins' development code.
//!
//! [definition; agent-inferred] **The stop-prior decision** (`prior`; Decision 32): on the
//! **development cells only** (the manifest's held-out range is cut away before the sweep reads
//! anything), the cell-only tree under every law of the declared family
//! (`hnn::landmark::prior_family`: the global dyadic ladder `w = 1 − 2^(−j)`, `j = 1, …, J`, then the
//! per-depth pairs `(j_root, j_below)`, `j_root ≠ j_below`; `J = ⌈log₂(n* B)⌉`,
//! `hnn::landmark::ladder_top`), each law with its own depth sweep (`choose_depth`) and charged
//! `⌈log₂⌉` of its depths tried, the choice charged `⌈log₂⌉` of the laws tried
//! (`hnn::landmark::choose_prior`):
//! - each law's development code length and its difference from the `½` tree (Decision 28's law),
//!   uncharged and charged, with its sign when decided by disjoint enclosures;
//! - the choice: the least charged law when it lies strictly below the `½` tree, the `½` tree
//!   otherwise, and whether it lies strictly below every other law;
//! - **where campaign 2's constant-slot controls found their bits** (development only; it chooses
//!   nothing): every law's development code length split by dyadic cell (the digit trees), each
//!   digit's executed face read by `Landmarks::opened` before its deposit. The controls are the
//!   cell tree joined, per dyadic cell, with the per-depth law `(1, r + 1)` (the test
//!   `landmark_constant_slots_are_the_per_depth_prior`), and a join codes each dyadic cell within
//!   `[min, min + 1]` of its two branches (Lean `sequential_mixture_bounds`): so it prints, per law,
//!   `Σ_h min(L_(½,h), L_(law,h)) − L_½` and the dyadic cells where the law is decided below `½`,
//!   and the least law per dyadic cell over the whole family, `Σ_h min_law L_(law,h) − L_½`;
//! - **then the held-out pass, once, for the chosen law** at its chosen depth (`prequential` over
//!   the whole cut, every cell scored before its own deposit): the chosen tree against online
//!   order-0, order-1, PPM-2 and the `½` tree (`tree_prequential` at its own chosen depth), each in
//!   all and a cell at the grain, the chosen tree charged its whole description (the laws' and its
//!   depths' `⌈log₂⌉`) and the `½` tree its depths' (Decision 28's receipt); and the wall times.
//!
//! [definition; agent-inferred] **The development harness** (`letters`; campaign 2's receiving
//! letters, Decision 31): on the **development cells only** (the manifest's held-out range is cut
//! away before anything is read, and no held-out cell reaches any choice or reading), the tree
//! addressed by typed bundles (each tick's cell with its declared rings' phase classes, read by the
//! clock-only replay `hnn::receiving::clock_letters`, the resident's clock law with its key
//! location and re-keying at each carry-out, without the wave) against the tree with cells only:
//! - the families tried: every nonempty set of campaign 1's four rings at one declared grain, the
//!   ring's period `d_g` (its own port chart, an empty fibre) or `2` (the half of the rotor's cycle
//!   its clock phase is in; not the parametron's half-turn sheets, which no letter reads), so
//!   `2 (2^4 − 1) = 30` families; each is declared (`LetterFamily`) and read with its own depth
//!   sweep (`choose_depth`), prequentially, every cell scored before its own deposit;
//! - each family's description charge: `⌈log₂(N + 1)⌉` bits for the family chosen among the `N`
//!   declared and the cell-only one, plus `⌈log₂⌉` of its depths tried; a slot of one letter is never
//!   declared (`LetterFamily::new` refuses it: it carries nothing), so nothing is charged for one;
//! - `Δ_tree = L_(tree+letters) − L_(tree, cells) + description`, an exact enclosure, and its
//!   sign when decided;
//! - with `contacts`, the contact families (every set of the field's contacts whose code fits 32
//!   bits, each contact's letter its owner's reading, `hnn::contact::ContactReading`), their site
//!   kinds read from the exposure's development part on the host (its deadline the development's
//!   last window: only its constitution curve's contact site readings are read);
//! - the constant-slot controls (`LetterFamily::constant_control`: `r` slots of one letter each,
//!   never declared and never charged), whose difference from the cell-only tree is the enlarged
//!   tree's own reweighting, and each family's
//!   `Δ_letters = L_(tree+letters) − L_(control, r slots) + description`; the family chosen is the
//!   least charged one with both `Δ_tree < 0` and `Δ_letters < 0` decided, the cell-only tree
//!   otherwise;
//! - the passage bound of every enlarged tree, family or control (Lean
//!   `HNN/LandmarkAddress.cell_only_dominance_with_feature_charge`, `passage_join_bound`): at its
//!   chosen depth `D` its executed code is at most the cell-only tree's at `D` plus one bit a dyadic
//!   cell the development cells opened, plus both trees' certified drift (each tree's a-priori rule
//!   a cell, `Landmarks::face_rule`, times the cells), checked by exact enclosures;
//! - the widths each family derives (its path depth `P = D + D(1 + r) + 2`) and its wall time.
//!
//! [definition] **What it runs** (the owner's header, `hnn::landmark`):
//! - the cut file and its manifest (`exterior::read_cut`): the cells and the held-out range;
//! - the receiver's grain `L_R` and the exterior chart's `|A|` from campaign 1's field declared at
//!   the cut's population (`FieldDeclaration::campaign_one`), so no grain is a literal here;
//! - the depth sweep on the development cells only (`choose_depth`: `D = 1, 2, …` while the
//!   development code length decreases strictly), every depth tried printed with its development
//!   code length and its derived widths, and the choice's description bits `⌈log₂⌉` of the family;
//! - the prequential measurement at the chosen depth (`prequential`): every cell, development and
//!   held-out, scored at the current standing before its own deposit, then deposited, for the tree
//!   (its executed lattice face) and the online baselines (uniform, order-0 and order-1 KT, PPM-2)
//!   over the same cells in the same order;
//! - the hot path alone: the passage through the tree without any reading, one all-class face read
//!   at the final standing, the held-out addresses' face reads at that standing, and a clone of the
//!   final tree;
//! - the executed face's cost against the reference oracle (`oracle_cost`): the ideal tree
//!   weighting in ℚ at the reference width `W_o`, cell by cell, never on the hot path.
//!
//! [established-bounded; measured] **The readout**: per population, each coder's bits a cell read
//! at the receiver's grain (`n + k/L_R + ε`, with `ε`'s exact enclosure); each strict ordering of the
//! tree against order-0, order-1 and PPM-2, decided by disjoint exact enclosures (the tree charged
//! its choice's description bits) or printed undecided with the overlap; the derived widths, the β
//! chart's rebases and drift, the rule's bound and the largest certified per-cell residual; the
//! executed face's cost over the oracle; and wall times in integer milliseconds or microseconds,
//! averages as a quotient with its remainder. The cut is private: only its scope and counts are
//! printed.

#[path = "exterior.rs"]
mod exterior;

use std::time::Instant;

use rayon::prelude::*;

use holonics::compression::cost::ceil_log2;
use holonics::hnn::born::{Born, BornDeclaration, Emission};
use holonics::hnn::landmark::{
    ChartReport, Coded, DepthSweep, FaceJoins, Feature, IdealLandmarks, JoinTree,
    LandmarkDeclaration, Landmarks, Letter, LetterFamily, LocalLaw, OracleCost, PassageCode,
    PriorSweep, ProductBound, StopMixture, StopPrior, TreeRun, Widths, address, cell_letters,
    choose_depth, choose_depth_within, choose_prior, choose_prior_within, code_length, development,
    development_run, ladder_top, odometer_digits, oracle_cost, prequential, prior_family,
    ratio_code_length, rescale_split, tree_prequential,
};
use holonics::hnn::ratio::interval_sum;
use holonics::hnn::receiving::clock_letters;
use holonics::hnn::receiving::{Mixture, MixtureStep, landmark_declaration_with};
use holonics::hnn::reference::{Baselines, PPM_ORDER};
use holonics::hnn::{Cut, Field, FieldDeclaration, Reference};
use holonics::navigator::trace::SiteKind;
use holonics::ratio::Rat;
use holonics::ratio::algebraic::ExactInterval;
use num_bigint::BigInt;
use num_bigint::BigUint;
use num_traits::{One, Zero};
use std::collections::BTreeSet;

use exterior::{
    against, difference, enclosure, exact, manifest_number, per, read_cut, reading_of,
    receiver_grain,
};

/// [definition; agent-inferred] **The harness's allocator, counted when asked** (exterior; Decision
/// 35's memory derivation): the system allocator; while counting is on, the bytes allocated less the
/// bytes freed are kept in one counter, so a tree built alone on its thread holds the counter's
/// difference across its building. Counting is off by default (the counter's cache line would be
/// shared by every worker).
struct Counted;

static COUNTING: std::sync::atomic::AtomicBool = std::sync::atomic::AtomicBool::new(false);
static LIVE: std::sync::atomic::AtomicIsize = std::sync::atomic::AtomicIsize::new(0);

unsafe impl std::alloc::GlobalAlloc for Counted {
    unsafe fn alloc(&self, layout: std::alloc::Layout) -> *mut u8 {
        let pointer = unsafe { std::alloc::System.alloc(layout) };
        if !pointer.is_null() && COUNTING.load(std::sync::atomic::Ordering::Relaxed) {
            LIVE.fetch_add(layout.size() as isize, std::sync::atomic::Ordering::Relaxed);
        }
        pointer
    }

    unsafe fn dealloc(&self, pointer: *mut u8, layout: std::alloc::Layout) {
        unsafe { std::alloc::System.dealloc(pointer, layout) };
        if COUNTING.load(std::sync::atomic::Ordering::Relaxed) {
            LIVE.fetch_sub(layout.size() as isize, std::sync::atomic::Ordering::Relaxed);
        }
    }

    unsafe fn realloc(&self, pointer: *mut u8, layout: std::alloc::Layout, size: usize) -> *mut u8 {
        let moved = unsafe { std::alloc::System.realloc(pointer, layout, size) };
        if !moved.is_null() && COUNTING.load(std::sync::atomic::Ordering::Relaxed) {
            LIVE.fetch_add(
                size as isize - layout.size() as isize,
                std::sync::atomic::Ordering::Relaxed,
            );
        }
        moved
    }
}

#[global_allocator]
static COUNTED: Counted = Counted;

/// Counting on or off.
fn counting(on: bool) {
    COUNTING.store(on, std::sync::atomic::Ordering::Relaxed);
}

/// The counter: the bytes allocated less the bytes freed while counting.
fn live() -> isize {
    LIVE.load(std::sync::atomic::Ordering::Relaxed)
}

/// The counter's growth since `before`, in bytes.
fn grown(before: isize) -> usize {
    usize::try_from(live() - before).unwrap_or(0)
}

/// The process's resident set now and at its peak (exterior), for a person.
fn resident() -> String {
    exterior::resident_set().map_or_else(
        || "unread".to_string(),
        |(now, peak)| format!("{now} bytes now, {peak} bytes at the peak"),
    )
}

/// The tree's code length charged its depth choice's description bits.
fn charged(bits: &ExactInterval, description: u64) -> ExactInterval {
    interval_sum(
        bits,
        &ExactInterval::point(Rat::from_integer(BigInt::from(description))),
    )
    .expect("an enclosure")
}

/// **A strict ordering**, `a` against `b`: decided by disjoint exact enclosures, with the exact
/// difference in bits and a cell; or undecided, with the overlap.
fn ordering(label: &str, a: &ExactInterval, b: &ExactInterval, cells: u64, grain: u64) {
    let side = against(a, b);
    println!("  {label}: {side}");
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
}

fn widths(widths: &Widths) -> String {
    format!(
        "B = {}, M_p = {}, W = {}, C = {}",
        widths.digits, widths.face, widths.carrier, widths.certificate
    )
}

fn sweep(sweep: &DepthSweep, declared: &LandmarkDeclaration, cells: u64, grain: u64) {
    println!("the depth sweep: the development code length by depth ({cells} cells)");
    for (depth, bits) in &sweep.tried {
        let tree = Landmarks::new(LandmarkDeclaration {
            depth: *depth,
            ..declared.clone()
        })
        .expect("a declared depth");
        println!(
            "  D = {depth} ({}): {}; a cell {}",
            widths(&tree.widths()),
            enclosure(bits, grain),
            per(bits, cells, grain)
        );
    }
    println!(
        "  chosen D = {} of {} tried; description bits ⌈log₂ {}⌉ = {}",
        sweep.chosen,
        sweep.tried.len(),
        sweep.tried.len(),
        sweep.description_bits
    );
}

fn population(label: &str, coded: &Coded, grain: u64) {
    let cells = coded.cells;
    println!("{label} ({cells} cells), bits a cell at L_R = {grain}:");
    let rows: [(&str, &ExactInterval); 5] = [
        ("tree (executed lattice face)", &coded.tree),
        ("uniform", &coded.uniform),
        ("online order-0 KT", &coded.order_zero),
        ("online order-1 KT", &coded.order_one),
        ("PPM order 2, escape C", &coded.ppm),
    ];
    for (name, bits) in rows {
        println!("  {name}: {}", per(bits, cells, grain));
        println!(
            "    total exact [{}, {}] bits",
            exact(&bits.lower),
            exact(&bits.upper)
        );
    }
}

fn orderings(label: &str, coded: &Coded, description: u64, grain: u64) {
    println!("{label}: the tree charged its depth choice's {description} description bits");
    let cells = coded.cells;
    let bits = charged(&coded.tree, description);
    ordering(
        "tree against online order-0 KT",
        &bits,
        &coded.order_zero,
        cells,
        grain,
    );
    ordering(
        "tree against online order-1 KT",
        &bits,
        &coded.order_one,
        cells,
        grain,
    );
    ordering(
        &format!("tree against PPM order {PPM_ORDER}"),
        &bits,
        &coded.ppm,
        cells,
        grain,
    );
}

fn below_grain(value: &Rat, grain: u64) -> &'static str {
    if value < &Rat::new(BigInt::from(1), BigInt::from(grain)) {
        "below"
    } else {
        "NOT below"
    }
}

fn tree_run(run: &TreeRun, grain: u64) {
    let chart = &run.chart;
    println!(
        "the tree: D = {}, {}; {} nodes founded, {} stored bits",
        run.declaration.depth,
        widths(&run.widths),
        run.nodes,
        run.bits
    );
    println!(
        "  β chart: {} rebases, {} at the most-rebased node; the largest node drift certificate |log₂ β̂ − log₂ β| ≤ {} bits",
        chart.rebases,
        chart.node_rebases,
        exact(&dyadic_ceiling(&chart.drift))
    );
    println!(
        "  the rule's bound a cell: {} bits, {} 1/L_R",
        exact(&dyadic_ceiling(&run.face_rule)),
        below_grain(&run.face_rule, grain)
    );
    println!(
        "  the largest certified per-cell residual: at most {} bits, {} the rule's bound",
        exact(&dyadic_ceiling(&run.largest_residual)),
        if run.largest_residual <= run.face_rule {
            "within"
        } else {
            "ABOVE"
        }
    );
}

fn oracle(cost: &OracleCost, cells: [u64; 2], grain: u64) {
    println!(
        "the reference oracle: β at W_o = {} bits ({} rebases), its own rule a cell {} bits",
        cost.reference_width,
        cost.rebases,
        exact(&dyadic_ceiling(&cost.drift_rule))
    );
    for (part, label) in ["development", "held out"].iter().enumerate() {
        let delta = ExactInterval {
            lower: &cost.executed[part].lower - &cost.ideal[part].upper,
            upper: &cost.executed[part].upper - &cost.ideal[part].lower,
        };
        println!(
            "  {label} ({} cells): the ideal face {}",
            cells[part],
            per(&cost.ideal[part], cells[part], grain)
        );
        println!(
            "    the executed face's cost over the ideal: {}",
            difference(&cost.executed[part], &cost.ideal[part], grain)
        );
        println!("    a cell: {}", per(&delta, cells[part], grain));
    }
    println!(
        "  the largest observed per-cell deviation |log₂(q̂/q)|: at most {} bits; the largest certificate {} bits; every cell within its certificate: {}",
        exact(&dyadic_ceiling(&cost.largest_deviation)),
        exact(&dyadic_ceiling(&cost.largest_certificate)),
        cost.certified
    );
}

/// An exact upper bound of a nonnegative value on the dyadic grid `2^(−READING)`, `⌈v 2^R⌉ / 2^R`:
/// a long ratio printed short, never below it.
fn dyadic_ceiling(value: &Rat) -> Rat {
    let scale = BigInt::from(1) << READING;
    let scaled = value * Rat::from_integer(scale.clone());
    Rat::new(scaled.ceil().to_integer(), scale)
}

/// The dyadic grid of a printed upper bound: `2^(−48)`.
const READING: usize = 48;

/// A total of microseconds over `count` reads: the integer quotient with its remainder.
fn average(total: u128, count: u128) -> String {
    format!(
        "{} µs in all, {} rem {} over {count} µs a read",
        total,
        total / count,
        total % count
    )
}

/// **The hot path alone** at the chosen depth: the passage without any reading, one all-class
/// face read at the final standing, the held-out addresses' face reads there, and a clone.
fn hot_path(cut: &Cut, declared: &LandmarkDeclaration, held: &std::ops::Range<usize>) {
    let mut tree = Landmarks::new(declared.clone()).expect("the chosen declaration");
    let clock = Instant::now();
    for (position, &cell) in cut.cells.iter().enumerate() {
        tree.receive(&address(&cut.cells, position, declared.depth), cell)
            .expect("a cell within the declaration");
    }
    let passage = clock.elapsed().as_millis();
    let mut read = Landmarks::new(declared.clone()).expect("the chosen declaration");
    let mut sum = ExactInterval::point(Rat::from_integer(BigInt::from(0)));
    let clock = Instant::now();
    for (position, &cell) in cut.cells.iter().enumerate() {
        let reading = read
            .receive(&address(&cut.cells, position, declared.depth), cell)
            .expect("a cell within the declaration");
        sum = interval_sum(
            &sum,
            &code_length(&reading.executed).expect("a code length"),
        )
        .expect("an enclosure");
    }
    let scored = clock.elapsed().as_millis();
    let next = address(&cut.cells, cut.cells.len(), declared.depth);
    let clock = Instant::now();
    let face = tree.face(&next, declared.grain).expect("a face");
    let one = clock.elapsed().as_micros();
    let total: Rat = face.probabilities.iter().cloned().sum();
    let clock = Instant::now();
    for position in held.clone() {
        tree.face(
            &address(&cut.cells, position, declared.depth),
            declared.grain,
        )
        .expect("a face");
    }
    let reads = clock.elapsed().as_micros();
    let clock = Instant::now();
    let copy = tree.clone();
    let cloned = clock.elapsed().as_micros();
    println!(
        "the hot path at D = {}: the passage of {} cells (receive only) {} ms; one all-class face read ({} classes) at the final standing {} µs, the faces summing to {}",
        declared.depth,
        cut.cells.len(),
        passage,
        face.probabilities.len(),
        one,
        exact(&total)
    );
    println!(
        "  the tree's own prequential run (receive, code length and sum of every cell): {scored} ms, {} bits in all",
        exact(&sum.upper)
    );
    println!(
        "  the held-out addresses' all-class face reads at the final standing: {}",
        average(reads, held.len() as u128)
    );
    println!(
        "  a clone of the final tree ({} nodes): {} µs; equal: {}",
        tree.nodes(),
        cloned,
        copy == tree
    );
}

/// One family's development sweep: its declaration's features, its sweep, the chosen depth's code
/// length, its description bits, and its wall time.
struct FamilyRun {
    name: String,
    family: LetterFamily,
    sweep: DepthSweep,
    bits: ExactInterval,
    description: u64,
    wall: u128,
    /// The distinct feature codes the family read over the development passage.
    distinct: usize,
}

/// The sign of an enclosure, when decided.
fn decided(delta: &ExactInterval) -> &'static str {
    if delta.upper < Rat::from_integer(BigInt::from(0)) {
        "< 0 (decided)"
    } else if delta.lower > Rat::from_integer(BigInt::from(0)) {
        "> 0 (decided)"
    } else {
        "undecided"
    }
}

fn chosen_bits(sweep: &DepthSweep) -> ExactInterval {
    sweep
        .tried
        .iter()
        .find(|(depth, _)| *depth == sweep.chosen)
        .map(|(_, bits)| bits.clone())
        .expect("the chosen depth was tried")
}

/// **The site kinds of the development pass** (module header, "The contact letters"): the exposure's
/// development part on the host (the reference, its deadline the development's last window, so no
/// held-out cell is read), whose constitution curve carries each commit's contact site readings;
/// the kinds the register holds at cell `i` are the commit after the deposits of the windows
/// before `i`'s (the register refreshes after each ingest). Only the kinds are read of it.
fn development_kinds(field: &Field, full: &Cut, development: usize) -> Vec<Vec<SiteKind>> {
    let aperture = field.receivers()[0].aperture;
    let windows = (development / aperture) as u64;
    let clock = Instant::now();
    let exposure = Reference::campaign_one()
        .with_deadline(windows)
        .expose(field, full)
        .expect("the exposure's development pass");
    let wall = clock.elapsed().as_millis();
    let stopped = exposure
        .deadline
        .expect("the development pass ends at its deadline");
    assert!(
        stopped as usize <= development,
        "the development pass read no held-out cell"
    );
    let curve = &exposure.constitution_curve;
    println!(
        "the site kinds: the exposure's development part on the host, {} windows, stopped at cell {stopped} (the held-out range opens at {development}); {} commits; budget stop: {}; {wall} ms wall",
        exposure.compares,
        curve.len(),
        if exposure.stop.is_some() {
            "yes"
        } else {
            "none"
        }
    );
    for contact in 0..field.contacts().len() {
        let mut seen: Vec<(String, usize)> = Vec::new();
        for point in curve {
            let reading = &point.contacts[contact];
            let label = format!(
                "{:?} (rotations {}, nulls {}, boosts {})",
                reading.kind, reading.census.rotation, reading.census.null, reading.census.boost
            );
            match seen.iter_mut().find(|(seen, _)| *seen == label) {
                Some((_, count)) => *count += 1,
                None => seen.push((label, 1)),
            }
        }
        let (from, to) = field.contact(contact).ends();
        println!(
            "  contact {contact} ({from} → {to}): {}",
            seen.iter()
                .map(|(label, count)| format!("{label} at {count} commits"))
                .collect::<Vec<_>>()
                .join("; ")
        );
    }
    (0..development)
        .map(|cell| {
            let point = &curve[(cell / aperture).min(curve.len() - 1)];
            point.contacts.iter().map(|reading| reading.kind).collect()
        })
        .collect()
}

/// **The development harness** (module header, "The development harness").
fn letters_harness(path: &str, contacts: bool) {
    let setup = Instant::now();
    let (bytes, count, held) = read_cut(path);
    let field = Field::declare(FieldDeclaration::campaign_one(count as u64))
        .expect("campaign 1's declared field over the cut");
    let grain = receiver_grain(&field);
    let alphabet = field.alphabet();
    let full = Cut {
        cells: bytes.iter().map(|&byte| usize::from(byte)).collect(),
        held_out: vec![held.clone()],
    };
    println!(
        "hnn_landmark letters: the development harness (campaign 2's receiving letters, Decision 31) over the cut file {path}"
    );
    // The contact letters' site kinds need the learned constitution: the exposure's development
    // part, stopped before the held-out range.
    let kinds = if contacts {
        development_kinds(&field, &full, held.start)
    } else {
        Vec::new()
    };
    // The development cells alone: nothing after this line reads a held-out cell.
    let cut = Cut {
        cells: development(&full),
        held_out: Vec::new(),
    };
    drop(full);
    let cells = cut.cells.len() as u64;
    let declared = LandmarkDeclaration {
        alphabet,
        depth: 1,
        forced: 0,
        population: count as u64,
        grain,
        family: LetterFamily::cells(),
        prior: holonics::hnn::StopPrior::half(),
    };
    println!(
        "development: {cells} cells (the manifest's held-out range {}..{} is cut away before any reading); |A| = {alphabet}, n* = {count}, L_R = {grain}",
        held.start, held.end
    );
    println!("setup: {} ms wall", setup.elapsed().as_millis());
    println!();

    let clock = Instant::now();
    let letters = cell_letters(&cut.cells);
    let cell_sweep = choose_depth(&cut, &letters, &declared).expect("the cell-only sweep");
    let cell_wall = clock.elapsed().as_millis();
    sweep(&cell_sweep, &declared, cells, grain);
    let cell_bits = chosen_bits(&cell_sweep);
    println!("the cell-only tree: {cell_wall} ms wall");
    println!();

    let rings = field.rings();
    let mut families: Vec<(String, LetterFamily)> = Vec::new();
    for sheet in [false, true] {
        for subset in 1u32..(1 << rings.len()) {
            let chosen: Vec<usize> = (0..rings.len()).filter(|g| subset >> g & 1 == 1).collect();
            let features = chosen
                .iter()
                .map(|&ring| Feature::Phase {
                    ring,
                    grain: if sheet { 2 } else { rings[ring].period() },
                })
                .collect();
            let name = chosen
                .iter()
                .map(|&ring| {
                    format!(
                        "ring {ring} (d = {}) at grain {}",
                        rings[ring].period(),
                        if sheet { 2 } else { rings[ring].period() }
                    )
                })
                .collect::<Vec<_>>()
                .join(", ");
            families.push((
                name,
                LetterFamily::new(features).expect("a declared family"),
            ));
        }
    }
    if contacts {
        // Every set of contacts whose letters' code fits the bundle's 32 bits, each contact's
        // letter its lock address at its derived bound times its site kind.
        let count = field.contacts().len();
        for subset in 1u32..(1 << count) {
            let chosen: Vec<usize> = (0..count).filter(|a| subset >> a & 1 == 1).collect();
            let features: Vec<Feature> = chosen
                .iter()
                .map(|&contact| Feature::contact(&field, contact))
                .collect();
            let name = chosen
                .iter()
                .map(|&contact| {
                    let (from, to) = field.contact(contact).ends();
                    let Feature::Contact { bound, .. } = Feature::contact(&field, contact) else {
                        unreachable!("a contact feature")
                    };
                    format!(
                        "contact {contact} ({from} → {to}, P = {}, Q = {})",
                        bound.numerator, bound.denominator
                    )
                })
                .collect::<Vec<_>>()
                .join(", ");
            match LetterFamily::new(features) {
                Ok(family) => families.push((name, family)),
                Err(refusal) => println!("not declared: {name}: {refusal}"),
            }
        }
    }
    // ⌈log₂(N + 1)⌉: the family chosen among the N tried and the cell-only tree.
    let choice_bits = u64::from(64 - (families.len() as u64).leading_zeros());
    println!(
        "families tried: {}; the family's description: ⌈log₂({} + 1)⌉ = {choice_bits} bits, plus ⌈log₂⌉ of its depths tried",
        families.len(),
        families.len()
    );
    let run_family = |name: String, family: LetterFamily, charge: u64| -> FamilyRun {
        let clock = Instant::now();
        let letters =
            clock_letters(&field, &family, &cut.cells, &kinds).expect("the passage's letters");
        let distinct = letters
            .iter()
            .filter_map(|letter| match letter {
                Letter::Bundle(bundle) => Some(bundle.features),
                _ => None,
            })
            .collect::<std::collections::BTreeSet<u32>>()
            .len();
        let at = LandmarkDeclaration {
            family: family.clone(),
            ..declared.clone()
        };
        let family_sweep = choose_depth(&cut, &letters, &at).expect("a family's sweep");
        let wall = clock.elapsed().as_millis();
        let bits = chosen_bits(&family_sweep);
        let description = charge + family_sweep.description_bits;
        FamilyRun {
            name,
            family,
            sweep: family_sweep,
            bits,
            description,
            wall,
            distinct,
        }
    };
    let runs: Vec<FamilyRun> = families
        .into_iter()
        .map(|(name, family)| run_family(name, family, choice_bits))
        .collect();
    // [agent-inferred] **The constant-slot controls**: `r` slots that read one letter at every tick
    // (a ring's phase class at grain 1). They carry no information, so their code length against
    // the cell-only tree is the enlarged tree's own reweighting (`r` constant slots after each cell
    // make the stop weight at every cell depth past the first `1 − 2^(−(r+1))` instead of `1/2`,
    // joined with the cell tree), not a letter's; a family's letters are credited only with what
    // they code below the control of its slots,
    // `Δ_letters = L_(tree+letters) − L_(control, r slots) + description`.
    let widest = runs.iter().map(|run| run.family.slots()).max().unwrap_or(0);
    let controls: Vec<FamilyRun> = (1..=widest)
        .map(|slots| {
            run_family(
                format!("the constant control of {slots} slots"),
                LetterFamily::constant_control(slots),
                0,
            )
        })
        .collect();
    println!();
    println!(
        "the constant-slot controls against the cell-only tree (no letter information: the enlarged tree's reweighting, uncharged):"
    );
    for control in &controls {
        let delta = ExactInterval {
            lower: &control.bits.lower - &cell_bits.upper,
            upper: &control.bits.upper - &cell_bits.lower,
        };
        println!(
            "  {} ({} distinct letters): chosen D = {}; L_control − L_(tree, cells): {}",
            control.name,
            control.distinct,
            control.sweep.chosen,
            enclosure(&delta, grain)
        );
    }
    // The passage bound (Lean `cell_only_dominance_with_feature_charge`): at its chosen depth an
    // enlarged tree codes within one bit a dyadic cell opened of the cell-only tree at that depth,
    // plus both trees' certified drift (the a-priori rule a cell times the cells).
    let opened: BTreeSet<usize> = cut
        .cells
        .iter()
        .flat_map(|&class| declared.emitted(class).into_iter().map(|(h, _)| h))
        .collect();
    let opened = opened.len() as u64;
    let cell_bits_at = |depth: usize| -> ExactInterval {
        cell_sweep
            .tried
            .iter()
            .find(|(tried, _)| *tried == depth)
            .map(|(_, bits)| bits.clone())
            .unwrap_or_else(|| {
                prequential(
                    &cut,
                    &letters,
                    &LandmarkDeclaration {
                        depth,
                        ..declared.clone()
                    },
                )
                .expect("the cell-only tree at a family's depth")
                .development
                .tree
            })
    };
    let rule = |declaration: LandmarkDeclaration| -> Rat {
        Landmarks::new(declaration)
            .expect("a declared tree")
            .face_rule()
            * Rat::from_integer(BigInt::from(cells))
    };
    println!();
    println!(
        "the passage bound (Lean cell_only_dominance_with_feature_charge): L_(tree+letters) ≤ L_(tree, cells) at the same depth + {opened} (one bit a dyadic cell the development cells opened) + ρ_letters + ρ_cells (the rule a cell times {cells} cells):"
    );
    let mut bound_holds = true;
    for run in runs.iter().chain(&controls) {
        let depth = run.sweep.chosen;
        let cells_at = cell_bits_at(depth);
        let drift = rule(LandmarkDeclaration {
            depth,
            family: run.family.clone(),
            ..declared.clone()
        }) + rule(LandmarkDeclaration {
            depth,
            ..declared.clone()
        });
        let ceiling = &cells_at.lower + Rat::from_integer(BigInt::from(opened)) + &drift;
        let holds = run.bits.upper <= ceiling;
        bound_holds &= holds;
        let margin = ExactInterval {
            lower: &ceiling - &run.bits.upper,
            upper: &ceiling - &run.bits.upper,
        };
        println!(
            "  {} at D = {depth}: {}; margin (ceiling − L_(tree+letters).upper) {}",
            run.name,
            if holds { "holds" } else { "VIOLATED" },
            enclosure(&margin, grain)
        );
    }
    println!("  every enlarged tree within its passage bound: {bound_holds}");
    println!();
    println!(
        "each family against the cell-only tree at its chosen depth, Δ_tree = L_(tree+letters) − L_(tree, cells) + description:"
    );
    for run in &runs {
        let tried: Vec<String> = run
            .sweep
            .tried
            .iter()
            .map(|(depth, bits)| format!("D = {depth}: {}", per(bits, cells, grain)))
            .collect();
        let charged = charged(&run.bits, run.description);
        let delta = ExactInterval {
            lower: &charged.lower - &cell_bits.upper,
            upper: &charged.upper - &cell_bits.lower,
        };
        let sign = if delta.upper < Rat::from_integer(BigInt::from(0)) {
            "Δ_tree < 0 (decided)"
        } else if delta.lower > Rat::from_integer(BigInt::from(0)) {
            "Δ_tree > 0 (decided)"
        } else {
            "Δ_tree undecided"
        };
        let tree = Landmarks::new(LandmarkDeclaration {
            depth: run.sweep.chosen,
            family: run.family.clone(),
            ..declared.clone()
        })
        .expect("the chosen declaration");
        println!(
            "  {} ({} slots, {} bundle codes):",
            run.name,
            run.family.slots(),
            run.family.bundle_codes(alphabet)
        );
        println!("    sweep {}", tried.join("; "));
        println!(
            "    chosen D = {} ({}, P = {}); description {} bits; {} ms wall",
            run.sweep.chosen,
            widths(&tree.widths()),
            tree.declaration().path_depth(),
            run.description,
            run.wall
        );
        let uncharged = ExactInterval {
            lower: &run.bits.lower - &cell_bits.upper,
            upper: &run.bits.upper - &cell_bits.lower,
        };
        println!(
            "    uncharged L_(tree+letters) − L_(tree, cells): {}",
            enclosure(&uncharged, grain)
        );
        println!("    Δ_tree {}: {}", sign, enclosure(&delta, grain));
        let control = &controls[run.family.slots() - 1];
        let against = ExactInterval {
            lower: &charged.lower - &control.bits.upper,
            upper: &charged.upper - &control.bits.lower,
        };
        println!(
            "    distinct feature codes read: {}; Δ_letters (against the constant control of {} slots, charged) {}: {}",
            run.distinct,
            run.family.slots(),
            decided(&against),
            enclosure(&against, grain)
        );
    }
    // The choice: the least charged family whose letters pay their description beyond both the
    // cell-only tree and the constant control of their slots, each decided by disjoint enclosures.
    let admitted: Vec<&FamilyRun> = runs
        .iter()
        .filter(|run| {
            let charged = charged(&run.bits, run.description);
            let control = &controls[run.family.slots() - 1];
            charged.upper < cell_bits.lower && charged.upper < control.bits.lower
        })
        .collect();
    let best = runs
        .iter()
        .min_by(|a, b| {
            let (a, b) = (
                charged(&a.bits, a.description),
                charged(&b.bits, b.description),
            );
            a.upper.cmp(&b.upper)
        })
        .expect("a family");
    let best_charged = charged(&best.bits, best.description);
    println!();
    println!(
        "the least charged family: {} at D = {}: {} a cell charged ({} bits in all)",
        best.name,
        best.sweep.chosen,
        per(&best_charged, cells, grain),
        exact(&best_charged.upper)
    );
    println!(
        "the cell-only tree at D = {}: {} a cell",
        cell_sweep.chosen,
        per(&cell_bits, cells, grain)
    );
    ordering(
        "least charged family against the cell-only tree",
        &best_charged,
        &cell_bits,
        cells,
        grain,
    );
    match admitted.iter().min_by(|a, b| {
        charged(&a.bits, a.description)
            .upper
            .cmp(&charged(&b.bits, b.description).upper)
    }) {
        Some(chosen) => println!(
            "the choice: {} at D = {} (Δ_tree < 0 and Δ_letters < 0 decided)",
            chosen.name, chosen.sweep.chosen
        ),
        None => println!(
            "the choice: the cell-only family at D = {} (no family's letters code below both the cell-only tree and the constant control of their slots by their description)",
            cell_sweep.chosen
        ),
    }
    println!();
    println!(
        "wall time (exterior): the harness {} ms",
        setup.elapsed().as_millis()
    );
}

/// One law's line of the stop-prior sweep: its depths, its development code length and its
/// difference from the `½` tree, uncharged and charged (each law its depths' `⌈log₂⌉`).
fn prior_line(sweep: &PriorSweep, index: usize, cells: u64, grain: u64) {
    let (prior, depths) = &sweep.tried[index];
    let bits = sweep.bits(index);
    let half = sweep.bits(sweep.incumbent);
    let uncharged = ExactInterval {
        lower: &bits.lower - &half.upper,
        upper: &bits.upper - &half.lower,
    };
    let (charged, half_charged) = (sweep.charged(index), sweep.charged(sweep.incumbent));
    let delta = ExactInterval {
        lower: &charged.lower - &half_charged.upper,
        upper: &charged.upper - &half_charged.lower,
    };
    println!(
        "  {prior}: D = {} of {} tried ({} depth bits); L = {} bits in all, {} a cell",
        depths.chosen,
        depths.tried.len(),
        depths.description_bits,
        exact(&bits.upper),
        per(&bits, cells, grain)
    );
    println!(
        "    L − L_½ {}: {}; charged {}",
        decided(&uncharged),
        reading_of(&uncharged, grain),
        reading_of(&delta, grain)
    );
}

/// **One law's development code length by dyadic cell**: every digit's executed face read at the
/// standing before its cell's deposit (`Landmarks::opened`), enclosed and summed per dyadic cell.
fn dyadic_lengths(dev: &Cut, declared: &LandmarkDeclaration) -> Vec<ExactInterval> {
    let mut tree = Landmarks::new(declared.clone()).expect("a declared law");
    let zero = ExactInterval::point(Rat::from_integer(BigInt::from(0)));
    let mut sums = vec![zero; 1usize << tree.digits()];
    for (position, &class) in dev.cells.iter().enumerate() {
        let here = address(&dev.cells, position, declared.depth);
        for path in tree
            .opened(&here, class)
            .expect("a cell within the declaration")
        {
            let length = code_length(&path.faces[0]).expect("a code length");
            sums[path.dyadic] = interval_sum(&sums[path.dyadic], &length).expect("an enclosure");
        }
        tree.deposit(&here, class)
            .expect("a cell within the declaration");
    }
    sums
}

/// **Where the constant-slot controls found their bits** (module header; development only).
fn dyadic_split(dev: &Cut, declared: &LandmarkDeclaration, sweep: &PriorSweep, grain: u64) {
    let clock = Instant::now();
    let lengths: Vec<Vec<ExactInterval>> = (0..sweep.tried.len())
        .into_par_iter()
        .map(|index| {
            let (prior, depths) = &sweep.tried[index];
            dyadic_lengths(
                dev,
                &LandmarkDeclaration {
                    depth: depths.chosen,
                    prior: prior.clone(),
                    ..declared.clone()
                },
            )
        })
        .collect();
    let wall = clock.elapsed().as_millis();
    let half = &lengths[sweep.incumbent];
    let opened: Vec<usize> = (0..half.len())
        .filter(|&h| half[h].upper > Rat::from_integer(BigInt::from(0)))
        .collect();
    let total = |pick: &dyn Fn(usize) -> ExactInterval| -> ExactInterval {
        opened.iter().fold(
            ExactInterval::point(Rat::from_integer(BigInt::from(0))),
            |sum, &h| interval_sum(&sum, &pick(h)).expect("an enclosure"),
        )
    };
    let least = |a: &ExactInterval, b: &ExactInterval| {
        if a.upper <= b.upper {
            a.clone()
        } else {
            b.clone()
        }
    };
    let half_total = total(&|h| half[h].clone());
    let whole = sweep.bits(sweep.incumbent);
    let meets = half_total.lower <= whole.upper && whole.lower <= half_total.upper;
    println!(
        "where the constant-slot controls found their bits (development, {} dyadic cells opened; {wall} ms wall): per law, Σ_h min(L_(½,h), L_(law,h)) − L_½ (a join of the two codes within [that, that + {}]) and the dyadic cells where the law lies below ½:",
        opened.len(),
        opened.len()
    );
    let mut rows: Vec<(usize, ExactInterval, usize)> = (0..sweep.tried.len())
        .filter(|&index| index != sweep.incumbent)
        .map(|index| {
            let law = &lengths[index];
            let joined = total(&|h| least(&half[h], &law[h]));
            let below = opened
                .iter()
                .filter(|&&h| law[h].upper < half[h].lower)
                .count();
            (
                index,
                ExactInterval {
                    lower: &joined.lower - &half_total.upper,
                    upper: &joined.upper - &half_total.lower,
                },
                below,
            )
        })
        .collect();
    println!("  check: the ½ tree's dyadic cells sum to its code length: {meets}");
    rows.sort_by(|a, b| a.1.upper.cmp(&b.1.upper));
    for (index, gain, below) in rows.iter().take(8) {
        println!(
            "  {}: {}; below ½ at {below} of {} dyadic cells",
            sweep.tried[*index].0,
            reading_of(gain, grain),
            opened.len()
        );
    }
    for slots in 1..=4u32 {
        let law = StopPrior::per_depth(vec![1, slots + 1]).expect("a ladder law");
        if let Some((index, gain, below)) = rows
            .iter()
            .find(|(index, _, _)| sweep.tried[*index].0 == law)
        {
            println!(
                "  the control of {slots} slots, {}: {}; below ½ at {below} dyadic cells",
                sweep.tried[*index].0,
                reading_of(gain, grain)
            );
        }
    }
    // The least join by the odometer's digit level (the dyadic cell's depth in the tower thread).
    let (join, _, _) = &rows[0];
    let law = &lengths[*join];
    println!(
        "  by digit level, the least join ({}): Σ_(h at level i) min(L_(½,h), L_(law,h)) − L_(½,h) and the dyadic cells where the law lies below ½",
        sweep.tried[*join].0
    );
    let digits = half.len().trailing_zeros();
    for level in 0..digits {
        let at: Vec<usize> = opened
            .iter()
            .copied()
            .filter(|&h| h >> level == 1)
            .collect();
        let sum = |pick: &dyn Fn(usize) -> ExactInterval| {
            at.iter().fold(
                ExactInterval::point(Rat::from_integer(BigInt::from(0))),
                |sum, &h| interval_sum(&sum, &pick(h)).expect("an enclosure"),
            )
        };
        let (joined, alone) = (
            sum(&|h| least(&half[h], &law[h])),
            sum(&|h| half[h].clone()),
        );
        let below = at.iter().filter(|&&h| law[h].upper < half[h].lower).count();
        println!(
            "    level {level}: {}; below ½ at {below} of {}",
            reading_of(
                &ExactInterval {
                    lower: &joined.lower - &alone.upper,
                    upper: &joined.upper - &alone.lower,
                },
                grain
            ),
            at.len()
        );
    }
    let best = total(&|h| {
        lengths
            .iter()
            .map(|law| law[h].clone())
            .reduce(|a, b| least(&a, &b))
            .expect("a law")
    });
    let gain = ExactInterval {
        lower: &best.lower - &half_total.upper,
        upper: &best.upper - &half_total.lower,
    };
    println!(
        "  the least law in every dyadic cell (uncharged; naming it costs ⌈log₂ {}⌉ bits a dyadic cell): Σ_h min_law L_(law,h) − L_½ = {}",
        sweep.tried.len(),
        reading_of(&gain, grain)
    );
}

/// **The stop-prior decision** (module header, "The stop-prior decision"; Decision 32).
fn prior_harness(path: &str) {
    let setup = Instant::now();
    let (bytes, count, held) = read_cut(path);
    let field = Field::declare(FieldDeclaration::campaign_one(count as u64))
        .expect("campaign 1's declared field over the cut");
    let grain = receiver_grain(&field);
    let alphabet = field.alphabet();
    let full = Cut {
        cells: bytes.iter().map(|&byte| usize::from(byte)).collect(),
        held_out: vec![held.clone()],
    };
    // The development cells alone: the sweep reads nothing else.
    let dev = Cut {
        cells: development(&full),
        held_out: Vec::new(),
    };
    let cells = dev.cells.len() as u64;
    let declared = LandmarkDeclaration {
        alphabet,
        depth: 1,
        forced: 0,
        population: count as u64,
        grain,
        family: LetterFamily::cells(),
        prior: StopPrior::half(),
    };
    let top = ladder_top(&declared);
    let family = prior_family(top);
    println!("hnn_landmark prior: the stop-prior decision (Decision 32) over the cut file {path}");
    println!(
        "development: {cells} cells (the manifest's held-out range {}..{} is cut away before the sweep); |A| = {alphabet}, n* = {count}, L_R = {grain}",
        held.start, held.end
    );
    println!(
        "the family: the global ladder j = 1..{top} and the per-depth pairs (j_0, j_(≥1)), j_0 ≠ j_(≥1): {} laws, J = ⌈log₂(n* B)⌉ = ⌈log₂({count} · {})⌉ = {top}",
        family.len(),
        odometer_digits(alphabet)
    );
    let setup = setup.elapsed().as_millis();
    println!("setup: {setup} ms wall");
    println!();

    let clock = Instant::now();
    let sweep = choose_prior(&dev, &cell_letters(&dev.cells), &declared, &family)
        .expect("the stop-prior sweep");
    let sweep_wall = clock.elapsed().as_millis();
    println!(
        "the sweep: every law with its own depth sweep, charged ⌈log₂⌉ of its depths; the choice ⌈log₂ {}⌉ = {} bits; {sweep_wall} ms wall",
        family.len(),
        sweep.description_bits
    );
    for index in 0..sweep.tried.len() {
        prior_line(&sweep, index, cells, grain);
    }
    let mut least = 0;
    for index in 0..sweep.tried.len() {
        if sweep.charged(index).upper < sweep.charged(least).upper {
            least = index;
        }
    }
    let (chosen, depths) = &sweep.tried[sweep.chosen];
    println!();
    println!(
        "the least charged law: {} at D = {}",
        sweep.tried[least].0, sweep.tried[least].1.chosen
    );
    println!(
        "the choice: {chosen} at D = {} ({}); strictly below every other law: {}; its description {} bits (the laws' {} and its depths' {})",
        depths.chosen,
        if sweep.chosen == sweep.incumbent {
            "Decision 28's ½: no law lies strictly below it"
        } else {
            "strictly below the ½ tree"
        },
        sweep.decided,
        sweep.chosen_description(),
        sweep.description_bits,
        depths.description_bits
    );
    let (half_depths, chosen_bits) = (&sweep.tried[sweep.incumbent].1, sweep.bits(sweep.chosen));
    ordering(
        "development: the chosen law (charged its whole description) against the ½ tree (charged its depths)",
        &charged(&chosen_bits, sweep.chosen_description()),
        &charged(&sweep.bits(sweep.incumbent), half_depths.description_bits),
        cells,
        grain,
    );
    println!();
    dyadic_split(&dev, &declared, &sweep, grain);
    println!();

    // The held-out pass, once, for the chosen law.
    let at = LandmarkDeclaration {
        depth: depths.chosen,
        prior: chosen.clone(),
        ..declared.clone()
    };
    let half_at = LandmarkDeclaration {
        depth: half_depths.chosen,
        ..declared.clone()
    };
    let letters = cell_letters(&full.cells);
    let clock = Instant::now();
    let run = prequential(&full, &letters, &at).expect("the chosen law's prequential run");
    let run_wall = clock.elapsed().as_millis();
    let clock = Instant::now();
    let ([half_development, half_held], half_run) =
        tree_prequential(&full, &letters, &half_at).expect("the ½ tree's prequential run");
    let half_wall = clock.elapsed().as_millis();
    println!(
        "the held-out pass (once): {chosen} at D = {}, every cell scored before its own deposit",
        at.depth
    );
    println!(
        "check: the run's development code length is the sweep's: {}; the ½ tree's: {}",
        run.development.tree == chosen_bits,
        half_development == sweep.bits(sweep.incumbent)
    );
    let held_cells = run.held_out.cells;
    println!("held out ({held_cells} cells), bits a cell at L_R = {grain}:");
    let rows: [(&str, &ExactInterval); 5] = [
        ("the chosen tree", &run.held_out.tree),
        ("the ½ tree (Decision 28)", &half_held),
        ("online order-0 KT", &run.held_out.order_zero),
        ("online order-1 KT", &run.held_out.order_one),
        ("PPM order 2, escape C", &run.held_out.ppm),
    ];
    for (name, bits) in rows {
        println!("  {name}: {}", per(bits, held_cells, grain));
        println!(
            "    total exact [{}, {}] bits",
            exact(&bits.lower),
            exact(&bits.upper)
        );
    }
    let description = sweep.chosen_description();
    let bits = charged(&run.held_out.tree, description);
    println!("held out, the orderings: the chosen tree charged its {description} description bits");
    ordering(
        "chosen tree against online order-0 KT",
        &bits,
        &run.held_out.order_zero,
        held_cells,
        grain,
    );
    ordering(
        "chosen tree against online order-1 KT",
        &bits,
        &run.held_out.order_one,
        held_cells,
        grain,
    );
    ordering(
        &format!("chosen tree against PPM order {PPM_ORDER}"),
        &bits,
        &run.held_out.ppm,
        held_cells,
        grain,
    );
    ordering(
        &format!(
            "chosen tree against the ½ tree (charged its {} depth bits)",
            half_depths.description_bits
        ),
        &bits,
        &charged(&half_held, half_depths.description_bits),
        held_cells,
        grain,
    );
    ordering(
        "chosen tree against the ½ tree, uncharged",
        &run.held_out.tree,
        &half_held,
        held_cells,
        grain,
    );
    println!();
    tree_run(&run.run, grain);
    println!(
        "the ½ tree at D = {}: {} nodes founded, {} stored bits",
        half_at.depth, half_run.nodes, half_run.bits
    );
    println!();
    println!(
        "wall time (exterior): setup {setup} ms; the sweep {sweep_wall} ms; the held-out pass: the chosen law's prequential run (the tree and the baselines together) {run_wall} ms, the ½ tree's run {half_wall} ms"
    );
}

// -------------------------------------------------------------------------------------------
// Decision 34: weighing is local (`local`)

/// The development digits in cell order: per opened digit its cell, its dyadic cell and its digit,
/// and each cell's first digit.
struct Digits {
    cell: Vec<usize>,
    dyadic: Vec<usize>,
    symbol: Vec<usize>,
    starts: Vec<usize>,
}

impl Digits {
    fn len(&self) -> usize {
        self.cell.len()
    }

    fn of_cell(&self, cell: usize) -> std::ops::Range<usize> {
        self.starts[cell]..self.starts.get(cell + 1).copied().unwrap_or(self.len())
    }
}

/// **A face source's development splits**: each digit's digit-0 numerator on `2^(−bits)`, read
/// before its cell's deposit.
struct Source {
    label: String,
    splits: Vec<u64>,
    bits: u64,
}

impl Source {
    /// The observed side on the common lattice `2^(−lattice)` (`lattice ≥ bits`, exact).
    fn side(&self, digits: &Digits, i: usize, lattice: u64) -> u64 {
        let zero = self.splits[i];
        let side = if digits.symbol[i] == 0 {
            zero
        } else {
            (1u64 << self.bits) - zero
        };
        side << (lattice - self.bits)
    }
}

/// A balanced product of integers.
fn product(mut values: Vec<BigUint>) -> BigUint {
    if values.is_empty() {
        return BigUint::from(1u32);
    }
    while values.len() > 1 {
        values = values
            .par_chunks(2)
            .map(|pair| {
                if pair.len() == 2 {
                    &pair[0] * &pair[1]
                } else {
                    pair[0].clone()
                }
            })
            .collect();
    }
    values.pop().expect("a product")
}

/// `−log₂(numerator/denominator)`, enclosed (`landmark::ratio_code_length`, unreduced).
fn log_ratio(numerator: &BigUint, denominator: &BigUint) -> ExactInterval {
    ratio_code_length(numerator, denominator).expect("a positive ratio")
}

/// The grains of the oracle: each digit alone, each cell's digits, each dyadic cell's digits.
#[derive(Clone, Copy)]
enum Grain {
    Digit,
    Cell,
    Dyadic,
}

impl Grain {
    fn name(self) -> &'static str {
        match self {
            Grain::Digit => "digit",
            Grain::Cell => "cell",
            Grain::Dyadic => "dyadic cell",
        }
    }

    fn unit(self, digits: &Digits, i: usize) -> usize {
        match self {
            Grain::Digit => i,
            Grain::Cell => digits.cell[i],
            Grain::Dyadic => digits.dyadic[i],
        }
    }

    fn units(self, digits: &Digits, cells: usize, dyadic: usize) -> usize {
        match self {
            Grain::Digit => digits.len(),
            Grain::Cell => cells,
            Grain::Dyadic => dyadic,
        }
    }
}

/// **Each unit's product of observed sides** on the common lattice (each unit's code length is
/// `−log₂` of it over its lattice power; units share the lattice, so products compare exactly).
fn unit_products(
    source: &Source,
    digits: &Digits,
    grain: Grain,
    units: usize,
    lattice: u64,
) -> Vec<BigUint> {
    let mut sides: Vec<Vec<BigUint>> = vec![Vec::new(); units];
    for i in 0..digits.len() {
        sides[grain.unit(digits, i)].push(BigUint::from(source.side(digits, i, lattice)));
    }
    sides.into_par_iter().map(product).collect()
}

/// **The oracle** `Σ_u min_X ℓ_X(u) − L_T ≤ 0` at a grain, exactly enclosed: every unit takes the
/// largest product among the sources, against the tree's (`−log₂` of the chosen products' ratio to
/// the tree's); with how many units a source other than the tree wins.
fn unit_oracle(
    tree: &[BigUint],
    tree_total: &BigUint,
    others: &[&Vec<BigUint>],
) -> (ExactInterval, usize) {
    let mut wins = 0;
    let chosen: Vec<BigUint> = (0..tree.len())
        .map(|u| {
            let mut best = &tree[u];
            for other in others {
                if other[u] > *best {
                    best = &other[u];
                }
            }
            if best != &tree[u] {
                wins += 1;
            }
            best.clone()
        })
        .collect();
    let oracle = log_ratio(&product(chosen), tree_total);
    (oracle, wins)
}

/// A code length accumulated exactly: the faces' product held between exact integer bounds and
/// enclosed once (`landmark::PassageCode`).
#[derive(Default)]
struct Coder(PassageCode);

impl Coder {
    fn add(&mut self, face: &Rat) {
        self.0.face(face).expect("a positive face");
    }

    fn add_side(&mut self, side: u64, bits: u64) {
        self.0.side(side, bits);
    }

    fn bits(self) -> ExactInterval {
        self.0.bits().expect("an enclosure")
    }
}

/// The Born receiver's development splits: each digit's digit-0 numerator on `2^(−M)`, read before
/// its cell's deposit, and the wall time.
fn born_source(cells: &[usize], declaration: &BornDeclaration) -> (Source, u128) {
    let clock = Instant::now();
    let mut born = Born::new(declaration.clone()).expect("a Born declaration");
    let bits = u64::from(born.widths().face);
    let mut splits = Vec::with_capacity(cells.len() * 8);
    for &cell in cells {
        let reception = born.read(cell).expect("a Born reception");
        splits.extend(reception.digits.iter().map(|digit| digit.numerator));
        born.deposit(reception).expect("a Born deposit");
    }
    let label = format!(
        "Born {} χ = {}",
        match declaration.emission {
            Emission::Position => "Position",
            Emission::Dyadic => "Dyadic",
        },
        declaration.width
    );
    (
        Source {
            label,
            splits,
            bits,
        },
        clock.elapsed().as_millis(),
    )
}

/// A tree's development splits (any stop prior), with the digits it opens.
fn tree_source(cells: &[usize], declaration: &LandmarkDeclaration) -> (Source, Digits) {
    let mut tree = Landmarks::new(declaration.clone()).expect("a declared tree");
    let bits = tree.face_bits();
    let mut digits = Digits {
        cell: Vec::new(),
        dyadic: Vec::new(),
        symbol: Vec::new(),
        starts: Vec::new(),
    };
    let mut splits = Vec::new();
    for (position, &class) in cells.iter().enumerate() {
        digits.starts.push(digits.len());
        let reading = tree
            .receive_digits(&address(cells, position, declaration.depth), class, &[])
            .expect("a cell within the declaration");
        for digit in reading.digits {
            digits.cell.push(position);
            digits.dyadic.push(digit.dyadic);
            digits.symbol.push(digit.symbol);
            splits.push(digit.split);
        }
    }
    (
        Source {
            label: declaration.prior.to_string(),
            splits,
            bits,
        },
        digits,
    )
}

/// One member's development code length and its label.
struct Member {
    label: String,
    bits: ExactInterval,
    note: String,
}

/// The least member (by upper endpoint) and whether it lies strictly below every other member.
fn least(members: &[Member]) -> (usize, bool) {
    let mut best = 0;
    for (index, member) in members.iter().enumerate() {
        if member.bits.upper < members[best].bits.upper {
            best = index;
        }
    }
    let decided = members
        .iter()
        .enumerate()
        .all(|(index, member)| index == best || members[best].bits.upper < member.bits.lower);
    (best, decided)
}

/// A family's charge `⌈log₂ |family|⌉`.
fn family_charge(members: usize) -> u64 {
    ceil_log2(&BigUint::from(members))
}

/// **The node-local law's run** over a stream: the tree under [`LocalLaw`] reading the external
/// source's splits at each opened digit; the faces' products on the slots `slots` names for each
/// cell (the development and held-out parts, and the standing cut's), the largest certified residual
/// and the founded nodes.
fn local_run(
    cells: &[usize],
    slots: &dyn Fn(usize) -> [Option<usize>; 2],
    declaration: &LandmarkDeclaration,
    law: LocalLaw,
    external: &Source,
) -> ([PassageCode; 4], Rat, usize) {
    let (codes, residual, nodes, _) =
        local_counted(cells, slots, declaration, law, external, false);
    (codes, residual, nodes)
}

/// [`local_run`], with the tree's live bytes when `count` (the tree alone on its thread).
fn local_counted(
    cells: &[usize],
    slots: &dyn Fn(usize) -> [Option<usize>; 2],
    declaration: &LandmarkDeclaration,
    law: LocalLaw,
    external: &Source,
    count: bool,
) -> ([PassageCode; 4], Rat, usize, Option<usize>) {
    counting(count);
    let before = live();
    let mut tree = Landmarks::local(declaration.clone(), law).expect("a node-local tree");
    let lattice = tree.face_bits();
    let (mut codes, mut residual) = ([PassageCode::new(); 4], Rat::zero());
    let mut index = 0;
    for (position, &class) in cells.iter().enumerate() {
        let opened = declaration.emitted(class).len();
        let splits: Vec<u64> = external.splits[index..index + opened]
            .iter()
            .map(|&x| rescale_split(x, external.bits, lattice))
            .collect();
        index += opened;
        let reading = tree
            .receive_with(&address(cells, position, declaration.depth), class, &splits)
            .expect("a node-local reception");
        for slot in slots(position).into_iter().flatten() {
            codes[slot]
                .face(&reading.executed)
                .expect("a positive face");
        }
        if reading.residual > residual {
            residual = reading.residual;
        }
    }
    let bytes = count.then(|| grown(before));
    counting(false);
    (codes, residual, tree.nodes(), bytes)
}

/// **The stop-weight mixture's run on the laws' development splits** (the owner's joins,
/// [`FaceJoins`], on the trees' executed digit faces, which the mixture does not change): the
/// code length of the mixed faces.
fn joins_run(
    digits: &Digits,
    sources: &[&Source],
    tree: JoinTree,
    widths: holonics::hnn::landmark::Widths,
) -> ExactInterval {
    let mut joins = FaceJoins::new(tree, widths).expect("the joins");
    let full = 1u64 << widths.face;
    let zeros = vec![0u128; sources.len()];
    let mut coder = Coder::default();
    for i in 0..digits.len() {
        let faces: Vec<u64> = sources.iter().map(|source| source.splits[i]).collect();
        let symbol = digits.symbol[i];
        let receipt = joins
            .receive(digits.dyadic[i], &faces, symbol, &zeros, &zeros)
            .expect("a join step");
        let side = if symbol == 0 {
            receipt.split
        } else {
            full - receipt.split
        };
        coder.add_side(side, widths.face);
    }
    coder.bits()
}

/// **The switching mixture's run** over the development cells: the tree's cell face and the
/// external source's, mixed by [`Mixture::switching`] (or the plain mixture at `None`), each cell
/// scored before its step; the code length enclosed cell by cell, and the chart's drift.
fn switching_run(
    tree: &[Rat],
    other: &[Rat],
    rung: Option<u32>,
    carrier: u64,
) -> (ExactInterval, Rat) {
    let mut mixture = match rung {
        Some(rung) => Mixture::switching(carrier, rung).expect("a switch rate"),
        None => Mixture::new(carrier),
    };
    let mut bits = ExactInterval::point(Rat::zero());
    for (q_tree, q_other) in tree.iter().zip(other) {
        let weight = mixture.weight();
        let face = &weight * q_tree + (Rat::one() - &weight) * q_other;
        bits = interval_sum(&bits, &code_length(&face).expect("a face")).expect("an enclosure");
        mixture
            .step(&MixtureStep {
                ring: 0,
                tree: q_tree.clone(),
                combined: q_other.clone(),
                residual: Rat::zero(),
            })
            .expect("a positive step");
    }
    (bits, mixture.drift().clone())
}

/// Each cell's face from a source's splits on the common lattice: `Π side/2^(lattice · digits)`.
fn cell_faces(source: &Source, digits: &Digits, cells: usize, lattice: u64) -> Vec<Rat> {
    (0..cells)
        .map(|cell| {
            let range = digits.of_cell(cell);
            let numerator: BigUint = range
                .clone()
                .map(|i| BigUint::from(source.side(digits, i, lattice)))
                .product();
            Rat::new(
                BigInt::from(numerator),
                BigInt::from(1u32) << (lattice as usize * range.len()),
            )
        })
        .collect()
}

/// **The switching law's dominance bound** (Lean `HNN/LocalWeighing.fixed_share`), exact: the
/// best switching sequence's prior times its faces, `max_σ ½ Π T(σ_t, σ_(t+1)) Π f_σ(t)`, by
/// Viterbi on integers over the common lattice; returned as the bound minus `L_T` (`−log₂` of its
/// ratio to the tree's product).
fn switching_bound(
    tree: &[BigUint],
    tree_total: &BigUint,
    other: &[BigUint],
    rung: u32,
) -> ExactInterval {
    let keep = (BigUint::from(1u32) << rung as usize) - 1u32;
    let mut values = [tree[0].clone(), other[0].clone()];
    for t in 1..tree.len() {
        let faces = [&tree[t], &other[t]];
        let next = [0, 1].map(|x| {
            let stay = &values[x] * &keep;
            let switch = &values[1 - x];
            let best = if &stay >= switch {
                stay
            } else {
                switch.clone()
            };
            best * faces[x]
        });
        values = next;
    }
    let best = if values[0] >= values[1] {
        &values[0]
    } else {
        &values[1]
    };
    // The prior's denominator: ½ at the opening and 2^j a transition.
    let transitions = (tree.len() - 1) as u64 * u64::from(rung) + 1;
    log_ratio(best, &(tree_total << transitions as usize))
}

/// **Decision 34's development decision** (module header, "Weighing is local").
fn local_harness(path: &str) {
    let setup = Instant::now();
    let (bytes, count, held) = read_cut(path);
    let field = Field::declare(FieldDeclaration::campaign_one(count as u64))
        .expect("campaign 1's declared field over the cut");
    let grain = receiver_grain(&field);
    let alphabet = field.alphabet();
    let receiver = field.receivers()[0].clone();
    let declared = landmark_declaration_with(&field, &receiver, LetterFamily::cells())
        .expect("the receiver's tree");
    let full = Cut {
        cells: bytes.iter().map(|&byte| usize::from(byte)).collect(),
        held_out: vec![held.clone()],
    };
    let dev = development(&full);
    let cells = dev.len();
    let population = count as u64;
    println!("hnn_landmark local: weighing is local (Decision 34) over the cut file {path}");
    println!(
        "development: {cells} cells (the manifest's held-out range {}..{} is cut away before anything is read); |A| = {alphabet}, n* = {count}, L_R = {grain}; the tree at D = {} under {}",
        held.start, held.end, declared.depth, declared.prior
    );

    // The tree, the declared stop laws and the Born members, each prequential on the development
    // cells; their splits read before each cell's deposit (an exterior measurement, never retained
    // by the machine).
    let clock = Instant::now();
    let (tree, digits) = tree_source(&dev, &declared);
    let lattice = tree.bits;
    let tree_widths = Landmarks::new(declared.clone()).expect("a tree").widths();
    let top = ladder_top(&declared);
    let laws = prior_family(top);
    let law_sources: Vec<Source> = laws
        .par_iter()
        .map(|prior| {
            tree_source(
                &dev,
                &LandmarkDeclaration {
                    prior: prior.clone(),
                    ..declared.clone()
                },
            )
            .0
        })
        .collect();
    let laws_ms = clock.elapsed().as_millis();
    let bits_b = u128::from(odometer_digits(alphabet));
    let mut bound = 0u32;
    while 14 * (1u128 << (2 * (bound + 1))) * bits_b * cells as u128 <= 1u128 << 37 {
        bound += 1;
    }
    let born_declarations: Vec<BornDeclaration> = [Emission::Position, Emission::Dyadic]
        .into_iter()
        .flat_map(|emission| {
            (0..=bound).map(move |order| BornDeclaration {
                alphabet,
                width: 1 << order,
                emission,
                population,
                grain,
            })
        })
        .collect();
    let clock = Instant::now();
    let born: Vec<(Source, u128)> = born_declarations
        .par_iter()
        .map(|declaration| born_source(&dev, declaration))
        .collect();
    let born_ms = clock.elapsed().as_millis();
    let dyadic_cells = 1usize << odometer_digits(alphabet);
    println!(
        "read: the ½ tree and the {} declared stop laws (J = {top}) in {laws_ms} ms; the {} Born members (both emissions, χ = 1..2^{bound}) in {born_ms} ms wall ({} digits)",
        laws.len(),
        born.len(),
        digits.len()
    );
    for (source, ms) in &born {
        println!("  {}: M = {}, {ms} ms", source.label, source.bits);
    }
    let setup_ms = setup.elapsed().as_millis();
    println!();

    // ---- 1. The oracles, on the development cells only.
    let tree_code = {
        let mut coder = Coder::default();
        for i in 0..digits.len() {
            coder.add_side(tree.side(&digits, i, lattice), lattice);
        }
        coder.bits()
    };
    let (sweep_bits, _) = development_run(&dev_cut(&dev), &cell_letters(&dev), &declared)
        .expect("the tree's development run");
    // The tree's depth, chosen on the development cells (Decision 28), and its description bits.
    let depth_sweep =
        choose_depth(&dev_cut(&dev), &cell_letters(&dev), &declared).expect("the depth sweep");
    assert_eq!(
        depth_sweep.chosen, declared.depth,
        "the receiver's depth is the sweep's"
    );
    let depth_bits = depth_sweep.description_bits;
    println!(
        "the ½ tree: L_T {} ({} a cell); the sweep's enclosure agrees: {}; its depth D = {} of {} tried, {depth_bits} description bits, common to every law here",
        enclosure(&tree_code, grain),
        per(&tree_code, cells as u64, grain),
        sweep_bits.lower <= tree_code.upper && tree_code.lower <= sweep_bits.upper,
        depth_sweep.chosen,
        depth_sweep.tried.len()
    );
    println!(
        "1. the oracles Σ_u min(ℓ_T(u), ℓ_X(u)) − L_T (development; u a digit, a cell or a dyadic cell; exact enclosures, bits at L_R = {grain}; before any price):"
    );
    let grains = [Grain::Digit, Grain::Cell, Grain::Dyadic];
    let tree_units: Vec<Vec<BigUint>> = grains
        .iter()
        .map(|&g| {
            unit_products(
                &tree,
                &digits,
                g,
                g.units(&digits, cells, dyadic_cells),
                lattice,
            )
        })
        .collect();
    let tree_totals: Vec<BigUint> = tree_units
        .iter()
        .map(|units| product(units.clone()))
        .collect();
    let units_of = |source: &Source| -> Vec<Vec<BigUint>> {
        grains
            .iter()
            .map(|&g| {
                unit_products(
                    source,
                    &digits,
                    g,
                    g.units(&digits, cells, dyadic_cells),
                    lattice,
                )
            })
            .collect()
    };
    let oracle_line = |label: &str, units: &[Vec<BigUint>]| -> Vec<ExactInterval> {
        let mut gains = Vec::new();
        let mut line = format!("  {label}:");
        for (g, grain_units) in units.iter().enumerate() {
            let (oracle, wins) = unit_oracle(&tree_units[g], &tree_totals[g], &[grain_units]);
            line += &format!(
                " {} {} (wins {wins});",
                grains[g].name(),
                reading_of(&oracle, grain)
            );
            gains.push(oracle);
        }
        println!("{line}");
        gains
    };
    let born_units: Vec<Vec<Vec<BigUint>>> = born.iter().map(|(s, _)| units_of(s)).collect();
    let mut born_oracles = Vec::new();
    for ((source, _), units) in born.iter().zip(&born_units) {
        let code = {
            let mut coder = Coder::default();
            for i in 0..digits.len() {
                coder.add_side(source.side(&digits, i, lattice), lattice);
            }
            coder.bits()
        };
        println!(
            "  {} alone: {} a cell",
            source.label,
            per(&code, cells as u64, grain)
        );
        born_oracles.push(oracle_line(&source.label, units));
    }
    let law_units: Vec<Vec<Vec<BigUint>>> = law_sources.par_iter().map(units_of).collect();
    let mut law_rows: Vec<(usize, Vec<ExactInterval>)> = (1..laws.len())
        .into_par_iter()
        .map(|k| {
            let gains = (0..grains.len())
                .map(|g| unit_oracle(&tree_units[g], &tree_totals[g], &[&law_units[k][g]]).0)
                .collect();
            (k, gains)
        })
        .collect();
    law_rows.sort_by(|a, b| a.1[2].upper.cmp(&b.1[2].upper));
    println!(
        "  the stop laws, by their dyadic-cell oracle (the eight least, then the constant-slot controls):"
    );
    let law_line = |k: usize, gains: &[ExactInterval]| {
        println!(
            "    {}: digit {}; cell {}; dyadic cell {}",
            laws[k],
            reading_of(&gains[0], grain),
            reading_of(&gains[1], grain),
            reading_of(&gains[2], grain)
        );
    };
    for (k, gains) in law_rows.iter().take(8) {
        law_line(*k, gains);
    }
    for slots in 1..=4u32 {
        let control = StopPrior::per_depth(vec![1, slots + 1]).expect("a ladder law");
        if let Some((k, gains)) = law_rows.iter().find(|(k, _)| laws[*k] == control) {
            law_line(*k, gains);
        }
    }
    let least_law: Vec<(ExactInterval, usize)> = (0..grains.len())
        .map(|g| {
            let all: Vec<&Vec<BigUint>> = (1..laws.len()).map(|k| &law_units[k][g]).collect();
            unit_oracle(&tree_units[g], &tree_totals[g], &all)
        })
        .collect();
    println!(
        "  the least stop law in every unit: digit {} (the least law wins {}); cell {} ({}); dyadic cell {} ({} of {} dyadic cells opened)",
        reading_of(&least_law[0].0, grain),
        least_law[0].1,
        reading_of(&least_law[1].0, grain),
        least_law[1].1,
        reading_of(&least_law[2].0, grain),
        least_law[2].1,
        tree_units[2]
            .iter()
            .filter(|p| **p != BigUint::from(1u32))
            .count()
    );
    println!();

    // ---- 2. The laws, measured prequentially on the development cells, charged.
    let opened = tree_units[2]
        .iter()
        .filter(|p| **p != BigUint::from(1u32))
        .count() as u64;
    println!(
        "2. the local laws on the development cells, prequential, each charged ⌈log₂⌉ of its family (the tree's depth bits are common and cancel):"
    );

    // (a) Node-local mixing, Born's digit split as the admitted external face.
    let clock = Instant::now();
    let local_members: Vec<(usize, u32)> = (0..born.len())
        .flat_map(|m| (1..=top).map(move |j| (m, j)))
        .collect();
    let development_slot = |_: usize| [Some(0usize), None];
    let local_runs: Vec<Member> = local_members
        .par_iter()
        .map(|&(m, j)| {
            let law = LocalLaw::new(j).expect("a rung");
            let (codes, residual, nodes) =
                local_run(&dev, &development_slot, &declared, law, &born[m].0);
            Member {
                label: format!("{} with {}", law, born[m].0.label),
                bits: bits_of(&codes[0]),
                note: format!(
                    "{nodes} nodes, largest residual ≤ {} bits",
                    exact(&residual)
                ),
            }
        })
        .collect();
    let local_ms = clock.elapsed().as_millis();
    let local_charge = family_charge(local_runs.len());
    let decide = |label: &str,
                  runs: &[Member],
                  charge: u64,
                  oracle: &ExactInterval,
                  price: &Rat|
     -> Option<usize> {
        let (best, decided) = least(runs);
        let charged_bits = charged(&runs[best].bits, charge);
        let gain = ExactInterval {
            lower: -&oracle.upper,
            upper: -&oracle.lower,
        };
        let exceeds = gain.lower > *price;
        println!(
            "  {label}: {} members, charged {charge} bits; the oracle's gain {} against the price {}: {}",
            runs.len(),
            reading_of(&gain, grain),
            reading_of(&ExactInterval::point(price.clone()), grain),
            if exceeds {
                "exceeds it"
            } else {
                "does not exceed it: refused"
            }
        );
        println!(
            "    the least member: {} ({}); {} a cell uncharged; strictly below every other member: {decided}",
            runs[best].label,
            runs[best].note,
            per(&runs[best].bits, cells as u64, grain)
        );
        ordering(
            "    the least member, charged, against the ½ tree",
            &charged_bits,
            &tree_code,
            cells as u64,
            grain,
        );
        let below = charged_bits.upper < tree_code.lower;
        (exceeds && below).then_some(best)
    };
    println!("  (a) at each landmark (node-local mixing; {local_ms} ms wall):");
    for (m, (source, _)) in born.iter().enumerate() {
        let (row, _) = least(&local_runs[m * top as usize..(m + 1) * top as usize]);
        let run = &local_runs[m * top as usize + row];
        println!(
            "    {}: best {} {} a cell ({} against the tree uncharged)",
            source.label,
            run.label,
            per(&run.bits, cells as u64, grain),
            reading_of(&difference_interval(&run.bits, &tree_code), grain)
        );
    }
    let local_oracle = born_oracles
        .iter()
        .map(|gains| gains[0].clone())
        .min_by(|a, b| a.upper.cmp(&b.upper))
        .expect("a member");
    let local_choice = decide(
        "node-local (the digit-grain oracle of the best Born member; the price its family charge)",
        &local_runs,
        local_charge,
        &local_oracle,
        &Rat::from_integer(BigInt::from(local_charge)),
    );

    // (b) The stop-weight mixture per digit tree.
    let clock = Instant::now();
    let mut stop_members: Vec<(Vec<usize>, JoinTree, String)> = Vec::new();
    for (k, law) in laws.iter().enumerate().skip(1) {
        for j in 1..=top {
            stop_members.push((
                vec![0, k],
                JoinTree::incumbent(2, j).expect("a rung"),
                format!("½ with {law} at π_½ = 1 − 2^(−{j})"),
            ));
        }
    }
    let ladder: Vec<usize> = (0..laws.len()).filter(|&k| laws[k].is_global()).collect();
    stop_members.push((
        ladder.clone(),
        JoinTree::balanced(ladder.len()).expect("a family"),
        format!("the global ladder j = 1..{top}, balanced"),
    ));
    stop_members.push((
        (0..laws.len()).collect(),
        JoinTree::balanced(laws.len()).expect("a family"),
        format!("all {} laws, balanced", laws.len()),
    ));
    let stop_runs: Vec<Member> = stop_members
        .par_iter()
        .map(|(faces, join, label)| {
            let sources: Vec<&Source> = faces.iter().map(|&k| &law_sources[k]).collect();
            Member {
                label: label.clone(),
                bits: joins_run(&digits, &sources, join.clone(), tree_widths),
                note: format!("{} faces", faces.len()),
            }
        })
        .collect();
    let stop_ms = clock.elapsed().as_millis();
    let stop_charge = family_charge(stop_runs.len());
    // The price at the dyadic-cell grain: naming the least law in every dyadic cell opened among the
    // pair (one bit a dyadic cell at π = ½) and the family's charge.
    let stop_oracle = law_rows
        .iter()
        .map(|(_, gains)| gains[2].clone())
        .min_by(|a, b| a.upper.cmp(&b.upper))
        .expect("a law");
    println!(
        "  (b) in each digit tree (the stop-weight mixture; {} members: the ½ tree against each other law at the incumbent's rungs j = 1..{top}, and two balanced families; {stop_ms} ms wall):",
        stop_runs.len()
    );
    for index in [stop_runs.len() - 2, stop_runs.len() - 1] {
        println!(
            "    {}: {} a cell ({} against the tree uncharged)",
            stop_runs[index].label,
            per(&stop_runs[index].bits, cells as u64, grain),
            reading_of(
                &difference_interval(&stop_runs[index].bits, &tree_code),
                grain
            )
        );
    }
    let least_all = least_law[2].0.clone();
    println!(
        "    the least law in every dyadic cell: oracle {} against its naming ⌈log₂ {}⌉ = {} bits a dyadic cell over {opened} opened, {} bits: {}",
        reading_of(&least_all, grain),
        laws.len() - 1,
        family_charge(laws.len() - 1),
        family_charge(laws.len() - 1) * opened,
        if -&least_all.upper
            > Rat::from_integer(BigInt::from(family_charge(laws.len() - 1) * opened))
        {
            "exceeds it"
        } else {
            "does not exceed it: refused"
        }
    );
    let stop_price = Rat::from_integer(BigInt::from(opened + stop_charge));
    let stop_choice = decide(
        "stop mixture (the best pair's dyadic-cell oracle; the price one bit a dyadic cell opened plus the family charge)",
        &stop_runs,
        stop_charge,
        &stop_oracle,
        &stop_price,
    );

    // (c) Fixed-share across epochs: the tree's cell face against each Born member's.
    let clock = Instant::now();
    let shares = u32::try_from(ceil_log2(&BigUint::from(population))).expect("a rung");
    let tree_cells = cell_faces(&tree, &digits, cells, lattice);
    let born_cells: Vec<Vec<Rat>> = born
        .iter()
        .map(|(s, _)| cell_faces(s, &digits, cells, lattice))
        .collect();
    let switch_members: Vec<(usize, u32)> = (0..born.len())
        .flat_map(|m| (1..=shares).map(move |j| (m, j)))
        .collect();
    let switch_runs: Vec<Member> = switch_members
        .par_iter()
        .map(|&(m, j)| {
            let (bits, drift) =
                switching_run(&tree_cells, &born_cells[m], Some(j), tree_widths.carrier);
            Member {
                label: format!("α = 2^(−{j}) with {}", born[m].0.label),
                bits,
                note: format!("drift ≤ {} bits", exact(&drift)),
            }
        })
        .collect();
    let bounds: Vec<ExactInterval> = switch_members
        .par_iter()
        .map(|&(m, j)| switching_bound(&tree_units[1], &tree_totals[1], &born_units[m][1], j))
        .collect();
    let switch_ms = clock.elapsed().as_millis();
    let switch_charge = family_charge(switch_runs.len());
    println!(
        "  (c) across epochs (the switching mixture of the tree's and a Born member's cell faces at α = 2^(−j), j = 1..{shares}; {} members; {switch_ms} ms wall):",
        switch_runs.len()
    );
    for (m, (source, _)) in born.iter().enumerate() {
        let span = m * shares as usize..(m + 1) * shares as usize;
        let (row, _) = least(&switch_runs[span.clone()]);
        let best_bound = bounds[span.clone()]
            .iter()
            .min_by(|a, b| a.upper.cmp(&b.upper))
            .expect("a rate");
        let (plain, _) = switching_run(&tree_cells, &born_cells[m], None, tree_widths.carrier);
        println!(
            "    {}: best {} {} against the tree; Decision 30's plain mixture {}; the dominance bound (best switching sequence with its price) {}; the cell-grain oracle {}",
            source.label,
            switch_runs[span.start + row].label,
            reading_of(
                &difference_interval(&switch_runs[span.start + row].bits, &tree_code),
                grain
            ),
            reading_of(&difference_interval(&plain, &tree_code), grain),
            reading_of(best_bound, grain),
            reading_of(&born_oracles[m][1], grain),
        );
    }
    let switch_oracle = born_oracles
        .iter()
        .map(|gains| gains[1].clone())
        .min_by(|a, b| a.upper.cmp(&b.upper))
        .expect("a member");
    let best_bound = bounds
        .iter()
        .min_by(|a, b| a.upper.cmp(&b.upper))
        .expect("a bound");
    // The price at the cell grain: the best switching sequence's naming, read off its dominance
    // bound minus its oracle, with the family's charge.
    let switch_price =
        &best_bound.upper - &switch_oracle.lower + Rat::from_integer(BigInt::from(switch_charge));
    let switch_choice = decide(
        "switching (the best Born member's cell-grain oracle; the price the best switching sequence's naming plus the family charge)",
        &switch_runs,
        switch_charge,
        &switch_oracle,
        &switch_price.max(Rat::from_integer(BigInt::from(switch_charge))),
    );
    println!();

    // ---- 3. The held-out pass, once, for each law that codes below the tree.
    let chosen = [
        local_choice.map(|i| ("node-local", i)),
        stop_choice.map(|i| ("stop mixture", i)),
        switch_choice.map(|i| ("switching", i)),
    ];
    if chosen.iter().all(Option::is_none) {
        println!(
            "3. no local law codes below the ½ tree on the development cells, charged: that is the result, and no held-out cell is read"
        );
    } else {
        println!("3. the held-out pass, once, for each law that codes below the tree:");
        let letters = cell_letters(&full.cells);
        let clock = Instant::now();
        let run = prequential(&full, &letters, &declared).expect("the tree and the baselines");
        let held_cells = run.held_out.cells;
        let is_held = |position: usize| held.contains(&position);
        println!("  held out ({held_cells} cells), bits a cell at L_R = {grain}:");
        for (name, bits) in [
            ("the ½ tree", &run.held_out.tree),
            ("online order-0 KT", &run.held_out.order_zero),
            ("online order-1 KT", &run.held_out.order_one),
            ("PPM order 2, escape C", &run.held_out.ppm),
        ] {
            println!(
                "    {name}: {} (total {})",
                per(bits, held_cells, grain),
                enclosure(bits, grain)
            );
        }
        let clock_half = Instant::now();
        let mut half_tree = Landmarks::new(declared.clone()).expect("the ½ tree");
        for (position, &class) in full.cells.iter().enumerate() {
            half_tree
                .receive(&address(&full.cells, position, declared.depth), class)
                .expect("a cell");
        }
        println!(
            "    the ½ tree's whole passage: {} ms, {} nodes, {} stored bits",
            clock_half.elapsed().as_millis(),
            half_tree.nodes(),
            half_tree.bits()
        );
        for (name, index) in chosen.into_iter().flatten() {
            let clock_law = Instant::now();
            let (bits, charge) = match name {
                "node-local" => {
                    let (m, j) = local_members[index];
                    let (whole, _) = born_source(&full.cells, &born_declarations[m]);
                    let halves = |position: usize| [Some(usize::from(is_held(position))), None];
                    let (codes, _, _) = local_run(
                        &full.cells,
                        &halves,
                        &declared,
                        LocalLaw::new(j).expect("a rung"),
                        &whole,
                    );
                    (bits_of(&codes[1]), local_charge)
                }
                "stop mixture" => {
                    let (faces, join, _) = &stop_members[index];
                    let mut mixture = StopMixture::new(
                        declared.clone(),
                        faces.iter().map(|&k| laws[k].clone()).collect(),
                        join.clone(),
                    )
                    .expect("the chosen mixture");
                    let mut coders = [Coder::default(), Coder::default()];
                    for (position, &class) in full.cells.iter().enumerate() {
                        let reading = mixture
                            .receive(&address(&full.cells, position, declared.depth), class)
                            .expect("a cell");
                        coders[usize::from(is_held(position))].add(&reading.executed);
                    }
                    let [development_bits, held_bits] = coders.map(Coder::bits);
                    println!(
                        "    check: the owner's StopMixture reproduces the development code: {}",
                        development_bits == stop_runs[index].bits
                    );
                    let nodes: usize = mixture.trees().iter().map(Landmarks::nodes).sum();
                    let stored: u64 = mixture.trees().iter().map(Landmarks::bits).sum();
                    let (rebases, _) = mixture.joins().rebases();
                    println!(
                        "    the mixture's whole passage: {} ms, {nodes} nodes and {stored} stored bits in its {} trees, {} join rebases, the joins' largest drift ≤ {} bits",
                        clock_law.elapsed().as_millis(),
                        mixture.trees().len(),
                        rebases,
                        exact(&mixture.joins().drift())
                    );
                    (held_bits, stop_charge)
                }
                _ => {
                    let (m, j) = switch_members[index];
                    let (whole, _) = born_source(&full.cells, &born_declarations[m]);
                    let (whole_tree, whole_digits) = tree_source(&full.cells, &declared);
                    let n = full.cells.len();
                    let tree_faces = cell_faces(&whole_tree, &whole_digits, n, lattice);
                    let born_faces = cell_faces(&whole, &whole_digits, n, lattice);
                    let mut mixture = Mixture::switching(tree_widths.carrier, j).expect("a rate");
                    let mut bits = ExactInterval::point(Rat::zero());
                    for position in 0..n {
                        let weight = mixture.weight();
                        let face = &weight * &tree_faces[position]
                            + (Rat::one() - &weight) * &born_faces[position];
                        if is_held(position) {
                            bits = interval_sum(&bits, &code_length(&face).expect("a face"))
                                .expect("an enclosure");
                        }
                        mixture
                            .step(&MixtureStep {
                                ring: 0,
                                tree: tree_faces[position].clone(),
                                combined: born_faces[position].clone(),
                                residual: Rat::zero(),
                            })
                            .expect("a step");
                    }
                    (bits, switch_charge)
                }
            };
            println!(
                "  {name} ({}): {} a cell (total {})",
                match name {
                    "node-local" => &local_runs[index].label,
                    "stop mixture" => &stop_runs[index].label,
                    _ => &switch_runs[index].label,
                },
                per(&bits, held_cells, grain),
                enclosure(&bits, grain)
            );
            println!(
                "    {name}'s held-out pass: {} ms",
                clock_law.elapsed().as_millis()
            );
            ordering(
                &format!(
                    "  {name}, charged its family's {charge} bits, against the ½ tree (both charged the depth's {depth_bits})"
                ),
                &charged(&bits, charge),
                &run.held_out.tree,
                held_cells,
                grain,
            );
            let total = charge + depth_bits;
            for (label, against) in [
                ("online order-0 KT", &run.held_out.order_zero),
                ("online order-1 KT", &run.held_out.order_one),
                ("PPM order 2", &run.held_out.ppm),
            ] {
                ordering(
                    &format!(
                        "  {name}, charged {total} bits (its family's and the depth's), against {label}"
                    ),
                    &charged(&bits, total),
                    against,
                    held_cells,
                    grain,
                );
            }
        }
        println!(
            "  the held-out pass: {} ms wall",
            clock.elapsed().as_millis()
        );
    }
    println!();
    println!(
        "wall time (exterior): setup and reads {setup_ms} ms; the harness {} ms",
        setup.elapsed().as_millis()
    );
}

/// `a − b` of two enclosures.
fn difference_interval(a: &ExactInterval, b: &ExactInterval) -> ExactInterval {
    ExactInterval {
        lower: &a.lower - &b.upper,
        upper: &a.upper - &b.lower,
    }
}

/// A cut of the development cells alone.
fn dev_cut(cells: &[usize]) -> Cut {
    Cut {
        cells: cells.to_vec(),
        held_out: Vec::new(),
    }
}

// -------------------------------------------------------------------------------------------
// Decision 35: the count-only receiver on the wide cut (`wide`)

/// Brandon's cap on resident memory: 20 GB (`20 · 10^9` bytes).
const CAP: u128 = 20_000_000_000;

/// **The bytes a node and a baseline cell, measured on the standing cut** (Decision 35): the `½`
/// tree at `depth` over the standing cut's cells, its live bytes (the counted allocator's, the tree
/// alone on its thread) over its founded nodes; the online baselines' live bytes over the cells
/// they read.
struct Measured {
    tree_bytes: u128,
    nodes: u128,
    baseline_bytes: u128,
    cells: u128,
}

fn measure_bytes(cells: &[usize], declaration: &LandmarkDeclaration) -> Measured {
    counting(true);
    let before = live();
    let mut tree = Landmarks::new(declaration.clone()).expect("the standing cut's tree");
    for (position, &cell) in cells.iter().enumerate() {
        tree.receive(&address(cells, position, declaration.depth), cell)
            .expect("a cell within the declaration");
    }
    let tree_bytes = grown(before);
    let before = live();
    let mut baselines = Baselines::new(declaration.alphabet).expect("the baselines");
    for &cell in cells {
        baselines.face_cell(cell).expect("a cell");
    }
    let baseline_bytes = grown(before);
    counting(false);
    Measured {
        tree_bytes: tree_bytes as u128,
        nodes: tree.nodes() as u128,
        baseline_bytes: baseline_bytes as u128,
        cells: cells.len() as u128,
    }
}

/// **The resident bound at a population** `n` and depth `D`: the tree, the two-law stop mixture's
/// two trees and the baselines, each tree at its a-priori node bound `n B D + 2^B − 1` (each cell
/// founds at most `D` nodes in each of its `B` opened digit trees, and each tree its root once),
/// at the measured bytes a node, and the baselines at the measured bytes a cell; `⌈·⌉` in bytes.
fn resident_bound(measured: &Measured, population: u128, digits: u128, depth: u128) -> u128 {
    let nodes = population * digits * depth + (1u128 << digits) - 1;
    let numerator = 3 * nodes * measured.tree_bytes * measured.cells
        + population * measured.baseline_bytes * measured.nodes;
    numerator.div_ceil(measured.nodes * measured.cells)
}

/// **The memory derivation** (module header, "The wide cut"): the bytes a node measured on the
/// standing cut; the resident bound at every power of two the development stream holds at the
/// standing cut's declared depth, and the largest within the cap (the pinned cut must be it); and
/// at the pinned population the deepest depth within the cap, which bounds every depth sweep.
fn memory_derivation(
    standing: &[usize],
    declaration: &LandmarkDeclaration,
    population: usize,
    stream: u128,
) -> (Measured, usize) {
    let measured = measure_bytes(standing, declaration);
    let digits = u128::from(odometer_digits(declaration.alphabet));
    let depth = declaration.depth as u128;
    println!(
        "0. memory (the cap {CAP} bytes): on the standing cut ({} cells) the ½ tree at D = {depth} holds {} nodes in {} live bytes, {} bytes a node ({} rem {} over {}); the baselines {} live bytes, {} bytes a cell ({} rem {} over {})",
        measured.cells,
        measured.nodes,
        measured.tree_bytes,
        measured.tree_bytes.div_ceil(measured.nodes),
        measured.tree_bytes / measured.nodes,
        measured.tree_bytes % measured.nodes,
        measured.nodes,
        measured.baseline_bytes,
        measured.baseline_bytes.div_ceil(measured.cells),
        measured.baseline_bytes / measured.cells,
        measured.baseline_bytes % measured.cells,
        measured.cells
    );
    println!(
        "  the resident bound 3 (n B D + 2^B − 1) · bytes a node + n · bytes a cell (the tree and the two-law stop mixture's two trees at the a-priori node bound, and the baselines), at D = {depth}:"
    );
    let mut largest = 0u32;
    let mut k = 1u32;
    while (1u128 << k) <= stream {
        let bound = resident_bound(&measured, 1u128 << k, digits, depth);
        let fits = bound <= CAP;
        if k >= 16 {
            println!(
                "    n = 2^{k}: {bound} bytes, {}",
                if fits {
                    "within the cap"
                } else {
                    "above the cap"
                }
            );
        }
        if fits {
            largest = k;
        }
        k += 1;
    }
    println!(
        "  the largest power of two within the cap and the stream ({stream} cells): 2^{largest}; the pinned cut holds {population} cells: {}",
        if population as u128 == 1u128 << largest {
            "it is that power, and a larger cut is refused"
        } else {
            "NOT that power"
        }
    );
    let mut deepest = 0usize;
    while resident_bound(&measured, population as u128, digits, deepest as u128 + 1) <= CAP {
        deepest += 1;
    }
    println!(
        "  at the pinned n = {population} the deepest depth within the cap: D ≤ {deepest} (D = {} bounds {} bytes); every depth sweep stops there",
        deepest + 1,
        resident_bound(&measured, population as u128, digits, deepest as u128 + 1)
    );
    (measured, deepest)
}

/// **The workers the memory admits** for tasks of `bytes` each: `⌊(budget − resident now)/(5/4 ·
/// bytes)⌋` within `1..=` the host's workers, the budget the cap or the memory the host had
/// available at the start, whichever is less (agent-inferred: a quarter's slack for each task's own
/// buffers).
fn workers_for(bytes: u128, budget: u128) -> usize {
    let threads = rayon::current_num_threads();
    let now = exterior::resident_set().map_or(0, |(now, _)| now);
    let each = (bytes + bytes / 4).max(1);
    usize::try_from(budget.saturating_sub(now) / each)
        .unwrap_or(threads)
        .clamp(1, threads)
}

/// A pool of `workers` threads.
fn pool(workers: usize) -> rayon::ThreadPool {
    rayon::ThreadPoolBuilder::new()
        .num_threads(workers)
        .build()
        .expect("a worker pool")
}

/// **A tree's live bytes** after its passage over `cells` (the tree alone, counted), and its nodes.
fn tree_bytes(cells: &[usize], declaration: &LandmarkDeclaration) -> (usize, usize) {
    counting(true);
    let before = live();
    let mut tree = Landmarks::new(declaration.clone()).expect("a declared tree");
    for (position, &cell) in cells.iter().enumerate() {
        tree.receive(&address(cells, position, declaration.depth), cell)
            .expect("a cell within the declaration");
    }
    let bytes = grown(before);
    counting(false);
    (bytes, tree.nodes())
}

/// The partitions a whole passage is read on: the development cells, the held-out cells, and within
/// the held-out cells the standing cut's development part and its held-out part.
#[derive(Clone)]
struct Parts {
    held: std::ops::Range<usize>,
    standing: std::ops::Range<usize>,
    standing_held: std::ops::Range<usize>,
}

impl Parts {
    /// The slots a cell's face enters: `0` development or `1` held out, then `2` the standing cut's
    /// development part or `3` its held-out part.
    fn slots(&self, position: usize) -> [Option<usize>; 2] {
        let first = usize::from(self.held.contains(&position));
        let second = if self.standing_held.contains(&position) {
            Some(3)
        } else if self.standing.contains(&position) {
            Some(2)
        } else {
            None
        };
        [Some(first), second]
    }

    fn counts(&self, cells: usize) -> [u64; 4] {
        [
            (cells - self.held.len()) as u64,
            self.held.len() as u64,
            (self.standing.len() - self.standing_held.len()) as u64,
            self.standing_held.len() as u64,
        ]
    }
}

const SLOTS: [&str; 4] = [
    "development",
    "held out",
    "the standing cut's development part (held out here)",
    "the standing cut's held-out part (held out here)",
];

/// **A whole passage's tree, read on the parts**: every cell scored at the standing before its own
/// deposit; the faces' products per slot, the tree's chart, founded nodes, stored bits, rule and
/// largest certified residual, its live bytes when counted alone, and its wall time.
struct TreePass {
    codes: [PassageCode; 4],
    chart: ChartReport,
    widths: Widths,
    nodes: usize,
    bits: u64,
    rule: Rat,
    largest: Rat,
    bytes: Option<usize>,
    wall: u128,
}

fn tree_pass(
    cells: &[usize],
    declaration: &LandmarkDeclaration,
    parts: &Parts,
    count: bool,
) -> TreePass {
    let clock = Instant::now();
    counting(count);
    let before = live();
    let mut tree = Landmarks::new(declaration.clone()).expect("a declared tree");
    let mut codes = [PassageCode::new(); 4];
    let mut largest = Rat::zero();
    for (position, &class) in cells.iter().enumerate() {
        let reading = tree
            .receive(&address(cells, position, declaration.depth), class)
            .expect("a cell within the declaration");
        for slot in parts.slots(position).into_iter().flatten() {
            codes[slot]
                .face(&reading.executed)
                .expect("a positive face");
        }
        if reading.residual > largest {
            largest = reading.residual;
        }
    }
    let bytes = count.then(|| grown(before));
    counting(false);
    TreePass {
        codes,
        chart: tree.chart(),
        widths: tree.widths(),
        nodes: tree.nodes(),
        bits: tree.bits(),
        rule: tree.face_rule(),
        largest,
        bytes,
        wall: clock.elapsed().as_millis(),
    }
}

/// **The online baselines over a whole passage**, read on the parts: uniform, order-0 and order-1
/// KT, PPM-2, each cell's exact face before its own count.
fn baselines_pass(
    cells: &[usize],
    alphabet: usize,
    parts: &Parts,
) -> ([[PassageCode; 4]; 4], u128) {
    let clock = Instant::now();
    let mut baselines = Baselines::new(alphabet).expect("the baselines");
    let mut codes = [[PassageCode::new(); 4]; 4];
    for (position, &class) in cells.iter().enumerate() {
        let faces = baselines.face_cell(class).expect("a cell");
        for slot in parts.slots(position).into_iter().flatten() {
            for (coder, face) in codes.iter_mut().zip([
                &faces.uniform,
                &faces.order_zero,
                &faces.order_one,
                &faces.ppm,
            ]) {
                coder[slot].face(face).expect("a positive face");
            }
        }
    }
    (codes, clock.elapsed().as_millis())
}

const BASELINES: [&str; 4] = [
    "uniform",
    "online order-0 KT",
    "online order-1 KT",
    "PPM order 2, escape C",
];

fn bits_of(code: &PassageCode) -> ExactInterval {
    code.bits().expect("an enclosure")
}

/// A tree's chart and scale readings (the scale checks).
fn scale_readings(label: &str, pass: &TreePass, population: u64, grain: u64) {
    println!(
        "  {label}: {}; the largest u128 operand {} bits; {} nodes founded, {} stored bits{}; {} ms",
        widths(&pass.widths),
        pass.widths.operand_bits(population),
        pass.nodes,
        pass.bits,
        pass.bytes.map_or(String::new(), |bytes| format!(
            ", {bytes} live bytes ({} rem {} over {} a node)",
            bytes / pass.nodes.max(1),
            bytes % pass.nodes.max(1),
            pass.nodes
        )),
        pass.wall
    );
    println!(
        "    β chart: {} rebases ({} at the most-rebased node), {} carrier releases (R = {}); the largest node drift |log₂ β̂ − log₂ β| ≤ {} bits",
        pass.chart.rebases,
        pass.chart.node_rebases,
        pass.chart.released,
        pass.widths.rebase,
        exact(&dyadic_ceiling(&pass.chart.drift))
    );
    println!(
        "    the rule's bound a cell {} bits ({} 1/L_R); the largest certified per-cell residual ≤ {} bits, {} the rule",
        exact(&dyadic_ceiling(&pass.rule)),
        below_grain(&pass.rule, grain),
        exact(&dyadic_ceiling(&pass.largest)),
        if pass.largest <= pass.rule {
            "within"
        } else {
            "ABOVE"
        }
    );
}

/// **One stop law's development reading at the common depth, streamed** (Decision 35: nothing per
/// digit is retained but the `½` tree's splits and the global ladder's own): the law's code in all
/// and per dyadic cell; its oracles against the `½` tree at the digit and cell grains (each unit's
/// larger product of observed sides); the incumbent joins `(½, law)` at every rung `j = 1..J`,
/// executed (`FaceJoins` on the two trees' executed digit faces, which the joins do not change);
/// its digits' sides folded into the least law in every digit; and its cells' products.
struct LawReading {
    total: PassageCode,
    dyadic: Vec<PassageCode>,
    digit: PassageCode,
    cell: PassageCode,
    joins: Vec<PassageCode>,
    nodes: usize,
}

fn law_reading(
    cells: &[usize],
    declaration: &LandmarkDeclaration,
    half: &Source,
    digits: &Digits,
    rungs: u32,
    best: &[std::sync::atomic::AtomicU64],
    keep: bool,
) -> (LawReading, Vec<BigUint>, Option<Vec<u64>>) {
    let mut tree = Landmarks::new(declaration.clone()).expect("a declared law");
    let (bits, widths) = (tree.face_bits(), tree.widths());
    assert_eq!(bits, half.bits, "the laws share the ½ tree's lattice");
    let full = 1u64 << bits;
    let mut reading = LawReading {
        total: PassageCode::new(),
        dyadic: vec![PassageCode::new(); 1usize << tree.digits()],
        digit: PassageCode::new(),
        cell: PassageCode::new(),
        joins: vec![PassageCode::new(); rungs as usize],
        nodes: 0,
    };
    let mut joins: Vec<FaceJoins> = (1..=rungs)
        .map(|rung| {
            FaceJoins::new(JoinTree::incumbent(2, rung).expect("a rung"), widths)
                .expect("the joins")
        })
        .collect();
    let zeros = [0u128; 2];
    let mut products = Vec::with_capacity(cells.len());
    let mut kept = keep.then(|| Vec::with_capacity(digits.len()));
    let mut index = 0;
    for (position, &class) in cells.iter().enumerate() {
        let read = tree
            .receive_digits(&address(cells, position, declaration.depth), class, &[])
            .expect("a cell within the declaration");
        let (mut own, mut other) = (BigUint::one(), BigUint::one());
        let opened = read.digits.len() as u64;
        for digit in read.digits {
            let side = if digit.symbol == 0 {
                digit.split
            } else {
                full - digit.split
            };
            let half_side = half.side(digits, index, bits);
            reading.total.side(side, bits);
            reading.dyadic[digit.dyadic].side(side, bits);
            reading.digit.side(side.max(half_side), bits);
            best[index].fetch_max(side, std::sync::atomic::Ordering::Relaxed);
            own *= side;
            other *= half_side;
            for (join, code) in joins.iter_mut().zip(&mut reading.joins) {
                let receipt = join
                    .receive(
                        digit.dyadic,
                        &[half.splits[index], digit.split],
                        digit.symbol,
                        &zeros,
                        &zeros,
                    )
                    .expect("a join step");
                code.side(
                    if digit.symbol == 0 {
                        receipt.split
                    } else {
                        full - receipt.split
                    },
                    bits,
                );
            }
            if let Some(kept) = kept.as_mut() {
                kept.push(digit.split);
            }
            index += 1;
        }
        reading
            .cell
            .dyadic(if own > other { &own } else { &other }, bits * opened);
        products.push(own);
    }
    reading.nodes = tree.nodes();
    (reading, products, kept)
}

/// The code of a source's sides on the common lattice, over the development digits, in all and by
/// dyadic cell.
fn source_code(
    source: &Source,
    digits: &Digits,
    lattice: u64,
    dyadic: usize,
) -> (PassageCode, Vec<PassageCode>) {
    let mut total = PassageCode::new();
    let mut cells = vec![PassageCode::new(); dyadic];
    for i in 0..digits.len() {
        let side = source.side(digits, i, lattice);
        total.side(side, lattice);
        cells[digits.dyadic[i]].side(side, lattice);
    }
    (total, cells)
}

/// Each cell's product of a source's sides on the common lattice.
fn cell_products(source: &Source, digits: &Digits, cells: usize, lattice: u64) -> Vec<BigUint> {
    (0..cells)
        .map(|cell| {
            digits
                .of_cell(cell)
                .map(|i| BigUint::from(source.side(digits, i, lattice)))
                .product()
        })
        .collect()
}

/// **The oracles of a face `X` against the tree at three grains** (`Σ_u min(ℓ_T(u), ℓ_X(u)) − L_T`,
/// each exactly enclosed), with the units `X` wins (decided): the digit and cell grains by each
/// unit's larger product, the dyadic cell by the least of the two enclosures.
fn grain_oracles(
    tree: (&Source, &[BigUint], &PassageCode, &[ExactInterval]),
    other: (&Source, &[BigUint], &[ExactInterval]),
    digits: &Digits,
    lattice: u64,
) -> [(ExactInterval, usize); 3] {
    let (tree_source, tree_cells, tree_total, tree_dyadic) = tree;
    let (source, cells, dyadic) = other;
    let total = bits_of(tree_total);
    let mut digit = PassageCode::new();
    let mut wins = [0usize; 3];
    for i in 0..digits.len() {
        let (t, x) = (
            tree_source.side(digits, i, lattice),
            source.side(digits, i, lattice),
        );
        wins[0] += usize::from(x > t);
        digit.side(t.max(x), lattice);
    }
    let mut cell = PassageCode::new();
    for (index, (t, x)) in tree_cells.iter().zip(cells).enumerate() {
        wins[1] += usize::from(x > t);
        cell.dyadic(
            if x > t { x } else { t },
            lattice * digits.of_cell(index).len() as u64,
        );
    }
    let (least, dyadic_wins) = least_dyadic(tree_dyadic, &[dyadic]);
    wins[2] = dyadic_wins;
    [
        (difference_interval(&bits_of(&digit), &total), wins[0]),
        (difference_interval(&bits_of(&cell), &total), wins[1]),
        (
            difference_interval(&least, &interval_total(tree_dyadic)),
            wins[2],
        ),
    ]
}

/// The enclosures' sum over dyadic cells.
fn interval_total(codes: &[ExactInterval]) -> ExactInterval {
    codes
        .iter()
        .fold(ExactInterval::point(Rat::zero()), |sum, code| {
            interval_sum(&sum, code).expect("an enclosure")
        })
}

/// `Σ_h min(ℓ_T(h), min_X ℓ_X(h))` over the dyadic cells, each unit the least enclosure (`[min lower,
/// min upper]` encloses the least), with the cells some `X` wins (decided below the tree).
fn least_dyadic(tree: &[ExactInterval], others: &[&[ExactInterval]]) -> (ExactInterval, usize) {
    let mut sum = ExactInterval::point(Rat::zero());
    let mut wins = 0;
    for (h, own) in tree.iter().enumerate() {
        let (mut lower, mut upper) = (own.lower.clone(), own.upper.clone());
        let mut won = false;
        for other in others {
            let theirs = &other[h];
            won |= theirs.upper < own.lower;
            if theirs.lower < lower {
                lower = theirs.lower.clone();
            }
            if theirs.upper < upper {
                upper = theirs.upper.clone();
            }
        }
        wins += usize::from(won);
        sum = interval_sum(&sum, &ExactInterval { lower, upper }).expect("an enclosure");
    }
    (sum, wins)
}

/// **The Born family's development splits**, each member on its own thread with its own pool of
/// `⌊workers/members⌋` for its deposits (so no member's wall time holds another's stolen work),
/// with each member's wall time and the pool's size.
fn born_family(cells: &[usize], declarations: &[BornDeclaration]) -> (Vec<(Source, u128)>, usize) {
    let workers = (rayon::current_num_threads() / declarations.len().max(1)).max(1);
    let sources = std::thread::scope(|scope| {
        let handles: Vec<_> = declarations
            .iter()
            .map(|declaration| {
                scope.spawn(move || pool(workers).install(|| born_source(cells, declaration)))
            })
            .collect();
        handles
            .into_iter()
            .map(|handle| handle.join().expect("a Born member"))
            .collect()
    });
    (sources, workers)
}

/// Each cell's face from its product of sides on the common lattice.
fn cell_face(product: &BigUint, digits: usize, lattice: u64) -> Rat {
    Rat::new(
        BigInt::from(product.clone()),
        BigInt::one() << (lattice as usize * digits),
    )
}

/// **The switching mixture over a stream** (Decision 34; Decision 30's plain mixture at `None`):
/// the tree's and a face's cell faces from their cells' products of sides on the common lattice,
/// mixed by `Mixture::switching`, each cell scored before its step, the mixed faces' products per
/// slot; and the chart's drift.
#[allow(clippy::too_many_arguments)]
fn switching_stream(
    tree: &[BigUint],
    other: &[BigUint],
    digits: &Digits,
    lattice: u64,
    rung: Option<u32>,
    carrier: u64,
    slots: &dyn Fn(usize) -> [Option<usize>; 2],
) -> ([PassageCode; 4], Rat) {
    let mut mixture = match rung {
        Some(rung) => Mixture::switching(carrier, rung).expect("a switch rate"),
        None => Mixture::new(carrier),
    };
    let mut codes = [PassageCode::new(); 4];
    for (position, (t, x)) in tree.iter().zip(other).enumerate() {
        let opened = digits.of_cell(position).len();
        let (q_tree, q_other) = (cell_face(t, opened, lattice), cell_face(x, opened, lattice));
        let weight = mixture.weight();
        let face = &weight * &q_tree + (Rat::one() - &weight) * &q_other;
        for slot in slots(position).into_iter().flatten() {
            codes[slot].face(&face).expect("a positive face");
        }
        mixture
            .step(&MixtureStep {
                ring: 0,
                tree: q_tree,
                combined: q_other,
                residual: Rat::zero(),
            })
            .expect("a positive step");
    }
    (codes, mixture.drift().clone())
}

/// **The switching law's dominance bound** (Lean `HNN/LocalWeighing.fixed_share`), enclosed: the
/// best switching sequence's prior times its faces, `max_σ ½ Π T(σ_t, σ_(t+1)) Π f_σ(t)`, by
/// Viterbi on the cells' products (the common lattice's denominator factors out), each state's
/// value held between product bounds; returned as the bound minus `L_T`.
fn switching_dominance(
    tree: &[BigUint],
    other: &[BigUint],
    exponent: u64,
    tree_code: &ExactInterval,
    rung: u32,
) -> ExactInterval {
    let keep = (1u64 << rung) - 1;
    let start = |x: &BigUint| {
        [
            ProductBound::ONE.times_integer(x, false),
            ProductBound::ONE.times_integer(x, true),
        ]
    };
    let mut values = [start(&tree[0]), start(&other[0])];
    for t in 1..tree.len() {
        let faces = [&tree[t], &other[t]];
        values = [0, 1].map(|x| {
            [0, 1].map(|side| {
                let up = side == 1;
                let stay = values[x][side].times(keep, up);
                let switch = values[1 - x][side];
                stay.max(switch).times_integer(faces[x], up)
            })
        });
    }
    let best = [0, 1].map(|side| values[0][side].max(values[1][side]));
    // The prior's denominator: ½ at the opening and 2^j a transition.
    let transitions = (tree.len() as u64 - 1) * u64::from(rung) + 1;
    let fixed = Rat::from_integer(BigInt::from(exponent + transitions));
    let bits = LOG_BITS;
    let bound = ExactInterval {
        lower: &fixed - best[1].log2(bits).1,
        upper: fixed - best[0].log2(bits).0,
    };
    difference_interval(&bound, tree_code)
}

/// The fraction bits of a bound's logarithm: the enclosure grid's `O + 1`.
const LOG_BITS: u32 = 97;

/// **The whole family mixed per digit tree, ideal** (uncharged; not executable at this scale, its
/// `StopMixture` holding one tree a law): per dyadic cell `−log₂ Σ_k π_k P_k(h)` from the laws'
/// per-dyadic products (every law's digits share the lattice, so `P_k(h) = N_k(h)/2^(E(h))`), with
/// `π` the balanced join tree's prior; the joins' executed code lies within their drift of it.
fn ideal_family_mixture(codes: &[&[PassageCode]], prior: &[Rat]) -> ExactInterval {
    let cells = codes[0].len();
    let scale = prior
        .iter()
        .map(|p| p.denom().bits() - 1)
        .max()
        .expect("a prior");
    let mut total = ExactInterval::point(Rat::zero());
    for h in 0..cells {
        if codes[0][h].factors() == 0 {
            continue;
        }
        let exponent = codes[0][h].bounds().2;
        let top = codes
            .iter()
            .map(|code| code[h].bounds().0[1].exponent)
            .max()
            .expect("a law");
        let base = top.saturating_sub(256);
        let mut sums = [BigUint::zero(), BigUint::zero()];
        for (code, weight) in codes.iter().zip(prior) {
            debug_assert_eq!(code[h].bounds().2, exponent);
            let numerator =
                weight.numer().magnitude() << (scale - (weight.denom().bits() - 1)) as usize;
            let bounds = code[h].bounds().0;
            for (side, sum) in sums.iter_mut().enumerate() {
                let bound = bounds[side];
                let value = BigUint::from(bound.mantissa) * &numerator;
                *sum += if bound.exponent >= base {
                    value << (bound.exponent - base) as usize
                } else {
                    let shift = (base - bound.exponent) as usize;
                    let floor = &value >> shift;
                    if side == 1 && (&floor << shift) != value {
                        floor + 1u32
                    } else {
                        floor
                    }
                };
            }
        }
        let low = ProductBound::ONE
            .times_integer(&sums[0], false)
            .log2(LOG_BITS)
            .0;
        let high = ProductBound::ONE
            .times_integer(&sums[1], true)
            .log2(LOG_BITS)
            .1;
        let fixed = Rat::from_integer(BigInt::from(exponent + scale) - BigInt::from(base));
        let enclosure = ExactInterval {
            lower: &fixed - high,
            upper: fixed - low,
        };
        total = interval_sum(&total, &enclosure).expect("an enclosure");
    }
    total
}

/// **Decision 34's adopted count law**: the `½` tree joined in each digit tree with the per-depth
/// law `(1, 3)` at `π_½ = ½` (the standing cut's development choice, adopted as the count face's
/// law), declared before the wide cut was read: a family of one.
fn adopted_law() -> (Vec<StopPrior>, JoinTree) {
    (
        vec![
            StopPrior::half(),
            StopPrior::per_depth(vec![1, 3]).expect("a ladder law"),
        ],
        JoinTree::incumbent(2, 1).expect("a rung"),
    )
}

/// **A stop mixture over a whole passage**, read on the parts, with its scale readings printed:
/// the owner's `StopMixture`, every cell scored before its own deposit.
fn mixture_pass(
    cells: &[usize],
    declaration: &LandmarkDeclaration,
    priors: Vec<StopPrior>,
    join: JoinTree,
    parts: &Parts,
) -> [PassageCode; 4] {
    let clock = Instant::now();
    let mut mixture =
        StopMixture::new(declaration.clone(), priors, join).expect("a declared mixture");
    let mut codes = [PassageCode::new(); 4];
    for (position, &class) in cells.iter().enumerate() {
        let reading = mixture
            .receive(&address(cells, position, declaration.depth), class)
            .expect("a cell");
        for slot in parts.slots(position).into_iter().flatten() {
            codes[slot]
                .face(&reading.executed)
                .expect("a positive face");
        }
    }
    let nodes: usize = mixture.trees().iter().map(Landmarks::nodes).sum();
    let stored: u64 = mixture.trees().iter().map(Landmarks::bits).sum();
    let (rebases, releases) = mixture.joins().rebases();
    println!(
        "    the mixture's whole passage: {} ms, {nodes} nodes and {stored} stored bits in its {} trees, {rebases} join rebases and {releases} releases, the joins' largest drift ≤ {} bits",
        clock.elapsed().as_millis(),
        mixture.trees().len(),
        exact(&dyadic_ceiling(&mixture.joins().drift()))
    );
    codes
}

/// **A local law's development decision** (Decision 34's rule): the least member, charged
/// `⌈log₂⌉` of its family, refused when its oracle's gain does not exceed its price, and chosen for
/// the held-out pass only when it also lies below the `½` tree by disjoint enclosures.
#[allow(clippy::too_many_arguments)]
fn decide_law(
    label: &str,
    runs: &[Member],
    charge: u64,
    oracle: &ExactInterval,
    price: &Rat,
    tree: &ExactInterval,
    cells: u64,
    grain: u64,
) -> Option<usize> {
    let (best, decided) = least(runs);
    let charged_bits = charged(&runs[best].bits, charge);
    let gain = ExactInterval {
        lower: -&oracle.upper,
        upper: -&oracle.lower,
    };
    let exceeds = gain.lower > *price;
    println!(
        "  {label}: {} members, charged {charge} bits; the oracle's gain {} against the price {}: {}",
        runs.len(),
        reading_of(&gain, grain),
        reading_of(&ExactInterval::point(price.clone()), grain),
        if exceeds {
            "exceeds it"
        } else {
            "does not exceed it: refused"
        }
    );
    println!(
        "    the least member: {} ({}); {} a cell uncharged, {} against the ½ tree uncharged; strictly below every other member: {decided}",
        runs[best].label,
        runs[best].note,
        per(&runs[best].bits, cells, grain),
        reading_of(&difference_interval(&runs[best].bits, tree), grain)
    );
    ordering(
        "    the least member, charged, against the ½ tree",
        &charged_bits,
        tree,
        cells,
        grain,
    );
    (exceeds && charged_bits.upper < tree.lower).then_some(best)
}

/// The held-out readings of one coder on the parts, and its orderings against the baselines and
/// the `½` tree (charged `charge` beside each baseline, `own` beside the tree whose own charge is
/// `tree_charge`).
#[allow(clippy::too_many_arguments)]
fn held_out_readings(
    label: &str,
    codes: &[PassageCode; 4],
    counts: &[u64; 4],
    charge: u64,
    own: u64,
    tree: Option<(&[PassageCode; 4], u64)>,
    baselines: &[[PassageCode; 4]; 4],
    grain: u64,
) {
    println!("  {label}:");
    for (slot, name) in SLOTS.iter().enumerate() {
        println!(
            "    {name} ({} cells): {} a cell; total {}",
            counts[slot],
            per(&bits_of(&codes[slot]), counts[slot], grain),
            enclosure(&bits_of(&codes[slot]), grain)
        );
    }
    let held = bits_of(&codes[1]);
    for (index, name) in BASELINES.iter().enumerate().skip(1) {
        ordering(
            &format!("    held out, charged {charge} bits, against {name}"),
            &charged(&held, charge),
            &bits_of(&baselines[index][1]),
            counts[1],
            grain,
        );
    }
    if let Some((tree, tree_charge)) = tree {
        ordering(
            &format!(
                "    held out, charged {own} bits, against the ½ tree (charged {tree_charge})"
            ),
            &charged(&held, own),
            &charged(&bits_of(&tree[1]), tree_charge),
            counts[1],
            grain,
        );
    }
}

/// **Decision 34's adopted law held out** (a family of one, declared before the wide cut was read):
/// its whole passage, its development code against the joins' when the development decision read
/// it, and its readings on the parts, against the baselines charged the depth's bits and against the
/// `½` tree uncharged (both at the same depth).
#[allow(clippy::too_many_arguments)]
fn adopted_readings(
    cells: &[usize],
    at: &LandmarkDeclaration,
    parts: &Parts,
    counts: &[u64; 4],
    depth_bits: u64,
    tree: &[PassageCode; 4],
    baselines: &[[PassageCode; 4]; 4],
    joins: Option<&ExactInterval>,
    grain: u64,
) {
    let (priors, join) = adopted_law();
    let label = format!("½ with {} at π_½ = ½", priors[1]);
    println!("  Decision 34's adopted law, {label} (declared before this cut; a family of one):");
    let codes = mixture_pass(cells, at, priors, join, parts);
    if let Some(joins) = joins {
        let development = bits_of(&codes[0]);
        println!(
            "    check: the owner's StopMixture meets the joins' development code (one exact product): {}; development, against the ½ tree uncharged: {}",
            development.lower <= joins.upper && joins.lower <= development.upper,
            reading_of(
                &difference_interval(&development, &bits_of(&tree[0])),
                grain
            )
        );
    }
    held_out_readings(
        &format!("the adopted law {label} (charged the depth's {depth_bits} bits)"),
        &codes,
        counts,
        depth_bits,
        0,
        Some((tree, 0)),
        baselines,
        grain,
    );
}

/// **Decision 35's adopted-law pass alone** (`wide-adopted`): the memory's depth cap and the depth
/// on the development cells, as the `wide` mode derives them, then the whole passage of the `½`
/// tree, the baselines and Decision 34's adopted law, each read on the parts.
fn wide_adopted_harness(path: &str, standing_path: &str) {
    let setup = Instant::now();
    let (bytes, count, held) = read_cut(path);
    let (standing_bytes, standing_count, standing_held) = read_cut(standing_path);
    assert!(
        bytes.ends_with(&standing_bytes),
        "the wide cut holds the standing cut as its tail"
    );
    let stream = manifest_number(path, "\"development_stream_bytes\":") as u128;
    let field = Field::declare(FieldDeclaration::campaign_one(count as u64))
        .expect("campaign 1's declared field over the cut");
    let grain = receiver_grain(&field);
    let alphabet = field.alphabet();
    let cells: Vec<usize> = bytes.iter().map(|&byte| usize::from(byte)).collect();
    let cut = Cut {
        cells: cells.clone(),
        held_out: vec![held.clone()],
    };
    let dev = development(&cut);
    let offset = count - standing_count;
    let parts = Parts {
        held: held.clone(),
        standing: offset..count,
        standing_held: offset + standing_held.start..count,
    };
    let counts = parts.counts(count);
    let standing_cells: Vec<usize> = standing_bytes.iter().map(|&b| usize::from(b)).collect();
    let standing_field = Field::declare(FieldDeclaration::campaign_one(standing_count as u64))
        .expect("campaign 1's declared field over the standing cut");
    let standing_declared = landmark_declaration_with(
        &standing_field,
        &standing_field.receivers()[0].clone(),
        LetterFamily::cells(),
    )
    .expect("the standing cut's receiver tree");
    println!(
        "hnn_landmark wide-adopted: Decision 34's adopted law held out on the wide cut (Decision 35) over the cut file {path}"
    );
    let (_, deepest) = memory_derivation(&standing_cells, &standing_declared, count, stream);
    let declared = LandmarkDeclaration {
        alphabet,
        depth: 1,
        forced: 0,
        population: count as u64,
        grain,
        family: LetterFamily::cells(),
        prior: StopPrior::half(),
    };
    let depth_sweep = choose_depth_within(&dev_cut(&dev), &cell_letters(&dev), &declared, deepest)
        .expect("the depth sweep");
    let (depth, depth_bits) = (depth_sweep.chosen, depth_sweep.description_bits);
    println!(
        "the depth on the development cells: D = {depth} of {} tried, {depth_bits} bits",
        depth_sweep.tried.len()
    );
    let at = LandmarkDeclaration {
        depth,
        ..declared.clone()
    };
    let tree = tree_pass(&cells, &at, &parts, false);
    let (baselines, _) = baselines_pass(&cells, alphabet, &parts);
    held_out_readings(
        &format!("the ½ tree at D = {depth} (charged its {depth_bits} depth bits)"),
        &tree.codes,
        &counts,
        depth_bits,
        depth_bits,
        None,
        &baselines,
        grain,
    );
    adopted_readings(
        &cells,
        &at,
        &parts,
        &counts,
        depth_bits,
        &tree.codes,
        &baselines,
        None,
        grain,
    );
    println!(
        "wall time (exterior): the harness {} ms; the process's resident peak {}",
        setup.elapsed().as_millis(),
        resident()
    );
}

/// **Decision 35's measurement on the wide cut** (module header, "The wide cut").
#[allow(clippy::too_many_lines)]
fn wide_harness(path: &str, standing_path: &str) {
    let setup = Instant::now();
    let (bytes, count, held) = read_cut(path);
    let (standing_bytes, standing_count, standing_held) = read_cut(standing_path);
    assert!(
        bytes.ends_with(&standing_bytes),
        "the wide cut holds the standing cut as its tail"
    );
    let stream = manifest_number(path, "\"development_stream_bytes\":") as u128;
    let field = Field::declare(FieldDeclaration::campaign_one(count as u64))
        .expect("campaign 1's declared field over the cut");
    let grain = receiver_grain(&field);
    let alphabet = field.alphabet();
    let population = count as u64;
    let cells: Vec<usize> = bytes.iter().map(|&byte| usize::from(byte)).collect();
    let cut = Cut {
        cells: cells.clone(),
        held_out: vec![held.clone()],
    };
    let dev = development(&cut);
    let n_dev = dev.len() as u64;
    let offset = count - standing_count;
    let parts = Parts {
        held: held.clone(),
        standing: offset..count,
        standing_held: offset + standing_held.start..count,
    };
    let counts = parts.counts(count);
    let standing_cells: Vec<usize> = standing_bytes.iter().map(|&b| usize::from(b)).collect();
    let standing_field = Field::declare(FieldDeclaration::campaign_one(standing_count as u64))
        .expect("campaign 1's declared field over the standing cut");
    let standing_receiver = standing_field.receivers()[0].clone();
    let standing_declared =
        landmark_declaration_with(&standing_field, &standing_receiver, LetterFamily::cells())
            .expect("the standing cut's receiver tree");
    let digits_b = odometer_digits(alphabet);
    let threads = rayon::current_num_threads();
    println!(
        "hnn_landmark wide: the count-only receiver on the wide cut (Decision 35) over the cut file {path}"
    );
    println!(
        "cut: {count} cells, |A| = {alphabet}, B = {digits_b}; held out: cells {}..{} ({} cells, from the manifest); development: {n_dev} cells; n* = {count}, L_R = {grain}; the standing cut ({standing_count} cells, held out {}..{}) is its tail, cells {}..{count}; {threads} workers",
        held.start,
        held.end,
        held.len(),
        standing_held.start,
        standing_held.end,
        offset
    );
    println!();

    // ---- 0. The memory derivation, on the standing cut's measured bytes a node.
    let clock = Instant::now();
    let (measured, deepest) = memory_derivation(&standing_cells, &standing_declared, count, stream);
    let budget = exterior::memory_available().map_or(CAP, |available| available.min(CAP));
    println!(
        "  the workers' budget: the cap or the memory the host has available now, whichever is less: {budget} bytes; {} ms",
        clock.elapsed().as_millis()
    );
    println!();

    // ---- 1. The depth, on the development cells.
    let declared = LandmarkDeclaration {
        alphabet,
        depth: 1,
        forced: 0,
        population,
        grain,
        family: LetterFamily::cells(),
        prior: StopPrior::half(),
    };
    let dev_cells = dev_cut(&dev);
    let dev_letters = cell_letters(&dev);
    let clock = Instant::now();
    let depth_sweep =
        choose_depth_within(&dev_cells, &dev_letters, &declared, deepest).expect("the depth sweep");
    println!(
        "1. the depth, D = 1..{deepest} at most ({} ms):",
        clock.elapsed().as_millis()
    );
    sweep(&depth_sweep, &declared, n_dev, grain);
    let depth = depth_sweep.chosen;
    let depth_bits = depth_sweep.description_bits;
    let at = LandmarkDeclaration {
        depth,
        ..declared.clone()
    };
    let bound = resident_bound(
        &measured,
        count as u128,
        u128::from(digits_b),
        depth as u128,
    );
    println!(
        "  at the chosen D = {depth} the resident bound at n = {count} is {bound} bytes: {}",
        if bound <= CAP {
            "within the cap"
        } else {
            "ABOVE the cap"
        }
    );
    println!("  peak resident so far: {}", resident());
    println!();

    // The live bytes of a tree at the deepest depth a law's sweep is expected to reach (one past
    // the ½ tree's, within the cap: the founded nodes at a depth are the same under every law, which
    // enters only at the founding), and the workers they admit.
    let clock = Instant::now();
    let sized = deepest.min(depth_sweep.tried.last().expect("a depth tried").0 + 1);
    let sized_at = LandmarkDeclaration {
        depth: sized,
        ..declared.clone()
    };
    let (deep_bytes, deep_nodes) = tree_bytes(&dev, &sized_at);
    let prior_workers = workers_for(deep_bytes as u128, budget);
    println!(
        "  the ½ tree at D = {sized} on the development cells: {deep_nodes} nodes in {deep_bytes} live bytes ({} rem {} over {deep_nodes} a node), {} ms; the workers this admits: {prior_workers}",
        deep_bytes / deep_nodes.max(1),
        deep_bytes % deep_nodes.max(1),
        clock.elapsed().as_millis()
    );
    println!();

    // ---- 2. Decision 32's stop-weight family, each law with its own depth sweep.
    let top = ladder_top(&at);
    let laws = prior_family(top);
    let clock = Instant::now();
    let prior_sweep = pool(prior_workers)
        .install(|| choose_prior_within(&dev_cells, &dev_letters, &declared, &laws, deepest))
        .expect("the stop-prior sweep");
    println!(
        "2. Decision 32's stop-weight family: the global ladder j = 1..{top} and the per-depth pairs, {} laws (J = ⌈log₂(n* B)⌉ = {top}), each with its own depth sweep within D ≤ {deepest}, the choice charged ⌈log₂ {}⌉ = {} bits; {} ms on {prior_workers} workers",
        laws.len(),
        laws.len(),
        prior_sweep.description_bits,
        clock.elapsed().as_millis()
    );
    for index in 0..prior_sweep.tried.len() {
        prior_line(&prior_sweep, index, n_dev, grain);
    }
    let (chosen_prior, chosen_depths) = &prior_sweep.tried[prior_sweep.chosen];
    println!(
        "  the deepest depth any law tried: {}",
        prior_sweep
            .tried
            .iter()
            .map(|(_, sweep)| sweep.tried.last().expect("a depth").0)
            .max()
            .expect("a law")
    );
    println!(
        "  the choice: {chosen_prior} at D = {} ({}); strictly below every other law: {}; its description {} bits",
        chosen_depths.chosen,
        if prior_sweep.chosen == prior_sweep.incumbent {
            "Decision 28's ½: no law lies strictly below it"
        } else {
            "strictly below the ½ tree"
        },
        prior_sweep.decided,
        prior_sweep.chosen_description()
    );
    println!("  peak resident so far: {}", resident());
    println!();

    // ---- 3. The faces at the common depth D, streamed.
    let clock = Instant::now();
    let (half, digits) = tree_source(&dev, &at);
    let lattice = half.bits;
    let widths_at = Landmarks::new(at.clone()).expect("the ½ tree").widths();
    let dyadic_cells = 1usize << digits_b;
    let (half_total, half_dyadic) = source_code(&half, &digits, lattice, dyadic_cells);
    let tree_code = bits_of(&half_total);
    let sweep_code = depth_sweep
        .tried
        .iter()
        .find(|(d, _)| *d == depth)
        .map(|(_, bits)| bits.clone())
        .expect("the chosen depth");
    let half_cells = cell_products(&half, &digits, dev.len(), lattice);
    let half_enclosures: Vec<ExactInterval> = half_dyadic.iter().map(bits_of).collect();
    let opened = half_dyadic.iter().filter(|code| code.factors() > 0).count() as u64;
    println!(
        "3. the faces at D = {depth} ({}), read prequentially on the development cells ({} digits, {opened} dyadic cells opened): the ½ tree L_T {} ({} a cell); the sweep's enclosure meets it: {}",
        widths(&widths_at),
        digits.len(),
        enclosure(&tree_code, grain),
        per(&tree_code, n_dev, grain),
        sweep_code.lower <= tree_code.upper && tree_code.lower <= sweep_code.upper
    );
    let best: Vec<std::sync::atomic::AtomicU64> = (0..digits.len())
        .map(|i| std::sync::atomic::AtomicU64::new(half.side(&digits, i, lattice)))
        .collect();
    let mut best_cells = half_cells.clone();
    let mut readings: Vec<LawReading> = Vec::with_capacity(laws.len() - 1);
    let mut ladder: Vec<Vec<u64>> = Vec::new();
    let others: Vec<usize> = (1..laws.len()).collect();
    let at_bytes = if depth == sized {
        deep_bytes
    } else {
        tree_bytes(&dev, &at).0
    };
    // A law's stream holds its tree, its cells' products and, on the ladder, its splits.
    let stream_bytes = at_bytes as u128 + 160 * u128::from(n_dev) + 8 * digits.len() as u128;
    let law_workers = workers_for(stream_bytes, budget);
    let law_pool = pool(law_workers);
    println!(
        "  the laws stream on {law_workers} workers (a tree at D = {depth} holds {at_bytes} live bytes; with its products and splits about {stream_bytes} bytes a worker)"
    );
    for batch in others.chunks(law_workers) {
        let results: Vec<(LawReading, Vec<BigUint>, Option<Vec<u64>>)> = law_pool.install(|| {
            batch
                .par_iter()
                .map(|&k| {
                    law_reading(
                        &dev,
                        &LandmarkDeclaration {
                            prior: laws[k].clone(),
                            ..at.clone()
                        },
                        &half,
                        &digits,
                        top,
                        &best,
                        laws[k].is_global(),
                    )
                })
                .collect()
        });
        for (reading, products, kept) in results {
            for (cell, product) in best_cells.iter_mut().zip(products) {
                if product > *cell {
                    *cell = product;
                }
            }
            if let Some(kept) = kept {
                ladder.push(kept);
            }
            readings.push(reading);
        }
    }
    let laws_ms = clock.elapsed().as_millis();
    println!(
        "  the {} other laws streamed at D = {depth} with their {} incumbent joins each: {laws_ms} ms; peak resident so far: {}",
        readings.len(),
        top,
        resident()
    );
    // The Born members: both emissions at χ = 2^j within the cost bound and the carrier.
    let mut cost = 0u32;
    while 14 * (1u128 << (2 * (cost + 1))) * u128::from(digits_b) * u128::from(n_dev) <= 1u128 << 37
    {
        cost += 1;
    }
    let mut born_declarations: Vec<BornDeclaration> = Vec::new();
    for emission in [Emission::Position, Emission::Dyadic] {
        for order in 0..=cost {
            let declaration = BornDeclaration {
                alphabet,
                width: 1 << order,
                emission,
                population,
                grain,
            };
            match Born::new(declaration.clone()) {
                Ok(_) => born_declarations.push(declaration),
                Err(refusal) => {
                    println!(
                        "  the Born member {emission:?} χ = {} is refused by its carrier at n* = {count}: {refusal}",
                        1usize << order
                    );
                    break;
                }
            }
        }
    }
    let clock = Instant::now();
    let (born, born_workers) = born_family(&dev, &born_declarations);
    let born_ms = clock.elapsed().as_millis();
    println!(
        "  the Born family: both emissions at χ = 2^j, j ≤ {cost} by the cost bound 14·4^J·B·n_dev ≤ 2^37 and within the carrier: {} members, each on its own thread with {born_workers} workers for its deposits, read in {born_ms} ms wall",
        born.len()
    );
    for (source, ms) in &born {
        println!(
            "    {}: M = {}, {ms} ms, {} µs a digit ({} rem {} over {})",
            source.label,
            source.bits,
            ms * 1000 / digits.len() as u128,
            ms * 1000 / digits.len() as u128,
            ms * 1000 % digits.len() as u128,
            digits.len()
        );
    }
    let born_codes: Vec<(PassageCode, Vec<ExactInterval>, Vec<BigUint>)> = born
        .par_iter()
        .map(|(source, _)| {
            let (total, dyadic) = source_code(source, &digits, lattice, dyadic_cells);
            (
                total,
                dyadic.iter().map(bits_of).collect(),
                cell_products(source, &digits, dev.len(), lattice),
            )
        })
        .collect();
    println!("  peak resident so far: {}", resident());
    println!();

    // ---- The oracles.
    println!(
        "the oracles Σ_u min(ℓ_T(u), ℓ_X(u)) − L_T (development; u a digit, a cell or a dyadic cell; exact enclosures, bits at L_R = {grain}; before any price):"
    );
    let born_oracles: Vec<[(ExactInterval, usize); 3]> = born
        .iter()
        .zip(&born_codes)
        .map(|((source, _), (total, dyadic, products))| {
            let oracles = grain_oracles(
                (&half, &half_cells, &half_total, &half_enclosures),
                (source, products, dyadic),
                &digits,
                lattice,
            );
            println!(
                "  {} alone {} a cell: digit {} (wins {}); cell {} (wins {}); dyadic cell {} (wins {})",
                source.label,
                per(&bits_of(total), n_dev, grain),
                reading_of(&oracles[0].0, grain),
                oracles[0].1,
                reading_of(&oracles[1].0, grain),
                oracles[1].1,
                reading_of(&oracles[2].0, grain),
                oracles[2].1
            );
            oracles
        })
        .collect();
    let law_enclosures: Vec<Vec<ExactInterval>> = readings
        .par_iter()
        .map(|reading| reading.dyadic.iter().map(bits_of).collect())
        .collect();
    let half_dyadic_total = half_enclosures
        .iter()
        .fold(ExactInterval::point(Rat::zero()), |sum, e| {
            interval_sum(&sum, e).expect("an enclosure")
        });
    let mut law_rows: Vec<(usize, [ExactInterval; 3])> = readings
        .par_iter()
        .zip(&law_enclosures)
        .enumerate()
        .map(|(index, (reading, enclosures))| {
            let (least_h, _) = least_dyadic(&half_enclosures, &[enclosures]);
            (
                index + 1,
                [
                    difference_interval(&bits_of(&reading.digit), &tree_code),
                    difference_interval(&bits_of(&reading.cell), &tree_code),
                    difference_interval(&least_h, &half_dyadic_total),
                ],
            )
        })
        .collect();
    law_rows.sort_by(|a, b| a.1[2].upper.cmp(&b.1[2].upper));
    println!(
        "  the stop laws, by their dyadic-cell oracle (the eight least, then the constant-slot controls):"
    );
    let law_line = |k: usize, gains: &[ExactInterval; 3]| {
        println!(
            "    {}: digit {}; cell {}; dyadic cell {}",
            laws[k],
            reading_of(&gains[0], grain),
            reading_of(&gains[1], grain),
            reading_of(&gains[2], grain)
        );
    };
    for (k, gains) in law_rows.iter().take(8) {
        law_line(*k, gains);
    }
    for slots in 1..=4u32 {
        let control = StopPrior::per_depth(vec![1, slots + 1]).expect("a ladder law");
        if let Some((k, gains)) = law_rows.iter().find(|(k, _)| laws[*k] == control) {
            law_line(*k, gains);
        }
    }
    let mut digit_best = PassageCode::new();
    let mut digit_wins = 0;
    for (i, value) in best.iter().enumerate() {
        let side = value.load(std::sync::atomic::Ordering::Relaxed);
        digit_wins += usize::from(side > half.side(&digits, i, lattice));
        digit_best.side(side, lattice);
    }
    let mut cell_best = PassageCode::new();
    let mut cell_wins = 0;
    for (index, (product, own)) in best_cells.iter().zip(&half_cells).enumerate() {
        cell_wins += usize::from(product > own);
        cell_best.dyadic(product, lattice * digits.of_cell(index).len() as u64);
    }
    let all_laws: Vec<&[ExactInterval]> = law_enclosures.iter().map(Vec::as_slice).collect();
    let (least_all, dyadic_wins) = least_dyadic(&half_enclosures, &all_laws);
    let least_all = difference_interval(&least_all, &half_dyadic_total);
    println!(
        "  the least stop law in every unit: digit {} (the least law wins {digit_wins}); cell {} ({cell_wins}); dyadic cell {} ({dyadic_wins} of {opened} dyadic cells opened)",
        reading_of(
            &difference_interval(&bits_of(&digit_best), &tree_code),
            grain
        ),
        reading_of(
            &difference_interval(&bits_of(&cell_best), &tree_code),
            grain
        ),
        reading_of(&least_all, grain),
    );
    println!();

    // ---- The Born face alone (Decision 33 at this scale).
    let born_charge = family_charge(born.len());
    let born_members: Vec<Member> = born
        .iter()
        .zip(&born_codes)
        .map(|((source, _), (total, _, _))| Member {
            label: source.label.clone(),
            bits: bits_of(total),
            note: format!("M = {}", source.bits),
        })
        .collect();
    let (born_best, _) = least(&born_members);
    println!(
        "4. the development decisions (each prequential, charged ⌈log₂⌉ of its family; the ½ tree's {depth_bits} depth bits are common and cancel):"
    );
    println!(
        "  the Born face alone ({} members, charged {born_charge} bits): the least {} {} a cell",
        born.len(),
        born_members[born_best].label,
        per(&born_members[born_best].bits, n_dev, grain)
    );
    let born_below = charged(&born_members[born_best].bits, born_charge).upper < tree_code.lower;
    ordering(
        "    the least Born face, charged, against the ½ tree",
        &charged(&born_members[born_best].bits, born_charge),
        &tree_code,
        n_dev,
        grain,
    );

    // (a) Node-local mixing, each Born member's digit split the admitted external face.
    let clock = Instant::now();
    let local_members: Vec<(usize, u32)> = (0..born.len())
        .flat_map(|m| (1..=top).map(move |j| (m, j)))
        .collect();
    let dev_slots = |_: usize| [Some(0usize), None];
    let local_member = |&(m, j): &(usize, u32), count: bool| {
        let law = LocalLaw::new(j).expect("a rung");
        let (codes, residual, nodes, bytes) =
            local_counted(&dev, &dev_slots, &at, law, &born[m].0, count);
        (
            Member {
                label: format!("{} with {}", law, born[m].0.label),
                bits: bits_of(&codes[0]),
                note: format!(
                    "{nodes} nodes, largest residual ≤ {} bits",
                    exact(&dyadic_ceiling(&residual))
                ),
            },
            bytes,
        )
    };
    let (first, local_bytes) = local_member(&local_members[0], true);
    let local_bytes = local_bytes.expect("counted") as u128;
    let local_workers = workers_for(local_bytes, budget);
    let mut local_runs = vec![first];
    local_runs.extend(pool(local_workers).install(|| {
        local_members[1..]
            .par_iter()
            .map(|member| local_member(member, false).0)
            .collect::<Vec<Member>>()
    }));
    let local_ms = clock.elapsed().as_millis();
    println!(
        "  a node-local tree at D = {depth} holds {local_bytes} live bytes; its members run on {local_workers} workers"
    );
    let local_charge = family_charge(local_runs.len());
    println!(
        "  (a) at each landmark (node-local mixing; {} members, Born members × rungs j = 1..{top}; {local_ms} ms wall):",
        local_runs.len()
    );
    let local_oracle = born_oracles
        .iter()
        .map(|o| o[0].0.clone())
        .min_by(|a, b| a.upper.cmp(&b.upper))
        .expect("a member");
    let local_choice = decide_law(
        "node-local (the digit-grain oracle of the best Born member; the price its family charge)",
        &local_runs,
        local_charge,
        &local_oracle,
        &Rat::from_integer(BigInt::from(local_charge)),
        &tree_code,
        n_dev,
        grain,
    );

    // (b) The stop-weight mixture per digit tree.
    let clock = Instant::now();
    let mut stop_members: Vec<(Vec<usize>, JoinTree, String)> = Vec::new();
    let mut stop_runs: Vec<Member> = Vec::new();
    for (index, reading) in readings.iter().enumerate() {
        for (j, code) in (1..=top).zip(&reading.joins) {
            stop_members.push((
                vec![0, index + 1],
                JoinTree::incumbent(2, j).expect("a rung"),
                format!("½ with {} at π_½ = 1 − 2^(−{j})", laws[index + 1]),
            ));
            stop_runs.push(Member {
                label: stop_members.last().expect("a member").2.clone(),
                bits: bits_of(code),
                note: "2 faces".to_string(),
            });
        }
    }
    let ladder_indices: Vec<usize> = (0..laws.len()).filter(|&k| laws[k].is_global()).collect();
    let ladder_sources: Vec<Source> = std::iter::once(Source {
        label: laws[0].to_string(),
        splits: half.splits.clone(),
        bits: lattice,
    })
    .chain(
        ladder
            .into_iter()
            .zip(&ladder_indices[1..])
            .map(|(splits, &k)| Source {
                label: laws[k].to_string(),
                splits,
                bits: lattice,
            }),
    )
    .collect();
    let ladder_refs: Vec<&Source> = ladder_sources.iter().collect();
    let ladder_join = JoinTree::balanced(ladder_indices.len()).expect("a family");
    let ladder_bits = joins_run(&digits, &ladder_refs, ladder_join.clone(), widths_at);
    drop(ladder_sources);
    stop_members.push((
        ladder_indices.clone(),
        ladder_join,
        format!("the global ladder j = 1..{top}, balanced"),
    ));
    stop_runs.push(Member {
        label: stop_members.last().expect("a member").2.clone(),
        bits: ladder_bits,
        note: format!("{} faces", ladder_indices.len()),
    });
    let stop_ms = clock.elapsed().as_millis();
    let stop_charge = family_charge(stop_runs.len());
    println!(
        "  (b) in each digit tree (the stop-weight mixture; {} members: the ½ tree against each other law at the incumbent's rungs j = 1..{top}, and the balanced global ladder; {stop_ms} ms wall beside the streaming):",
        stop_runs.len()
    );
    let ladder_member = stop_runs.last().expect("the ladder");
    println!(
        "    {}: {} a cell ({} against the tree uncharged)",
        ladder_member.label,
        per(&ladder_member.bits, n_dev, grain),
        reading_of(&difference_interval(&ladder_member.bits, &tree_code), grain)
    );
    let mut family_codes: Vec<&[PassageCode]> = vec![&half_dyadic];
    family_codes.extend(readings.iter().map(|r| r.dyadic.as_slice()));
    let family_prior = JoinTree::balanced(laws.len()).expect("a family").prior();
    let ideal = ideal_family_mixture(&family_codes, &family_prior);
    println!(
        "    all {} laws balanced, ideal (the Bayesian mixture per dyadic cell of the executed trees' faces; not a member: its StopMixture would hold {} trees): {} a cell ({} against the tree uncharged)",
        laws.len(),
        laws.len(),
        per(&ideal, n_dev, grain),
        reading_of(&difference_interval(&ideal, &tree_code), grain)
    );
    let naming = family_charge(laws.len() - 1) * opened;
    println!(
        "    the least law in every dyadic cell: oracle {} against its naming ⌈log₂ {}⌉ = {} bits a dyadic cell over {opened} opened, {naming} bits: {}",
        reading_of(&least_all, grain),
        laws.len() - 1,
        family_charge(laws.len() - 1),
        if -&least_all.upper > Rat::from_integer(BigInt::from(naming)) {
            "exceeds it"
        } else {
            "does not exceed it: refused"
        }
    );
    let stop_oracle = law_rows
        .iter()
        .map(|(_, gains)| gains[2].clone())
        .min_by(|a, b| a.upper.cmp(&b.upper))
        .expect("a law");
    let stop_choice = decide_law(
        "stop mixture (the best pair's dyadic-cell oracle; the price one bit a dyadic cell opened plus the family charge)",
        &stop_runs,
        stop_charge,
        &stop_oracle,
        &Rat::from_integer(BigInt::from(opened + stop_charge)),
        &tree_code,
        n_dev,
        grain,
    );

    // (c) Fixed-share across epochs: the tree's cell face against each Born member's.
    let clock = Instant::now();
    let shares = u32::try_from(ceil_log2(&BigUint::from(population))).expect("a rung");
    let switch_members: Vec<(usize, u32)> = (0..born.len())
        .flat_map(|m| (1..=shares).map(move |j| (m, j)))
        .collect();
    let exponent = lattice * digits.len() as u64;
    let switch_runs: Vec<(Member, ExactInterval)> = switch_members
        .par_iter()
        .map(|&(m, j)| {
            let (codes, drift) = switching_stream(
                &half_cells,
                &born_codes[m].2,
                &digits,
                lattice,
                Some(j),
                widths_at.carrier,
                &dev_slots,
            );
            let bound = switching_dominance(&half_cells, &born_codes[m].2, exponent, &tree_code, j);
            (
                Member {
                    label: format!("α = 2^(−{j}) with {}", born[m].0.label),
                    bits: bits_of(&codes[0]),
                    note: format!("drift ≤ {} bits", exact(&dyadic_ceiling(&drift))),
                },
                bound,
            )
        })
        .collect();
    let plain: Vec<ExactInterval> = (0..born.len())
        .into_par_iter()
        .map(|m| {
            let (codes, _) = switching_stream(
                &half_cells,
                &born_codes[m].2,
                &digits,
                lattice,
                None,
                widths_at.carrier,
                &dev_slots,
            );
            bits_of(&codes[0])
        })
        .collect();
    let switch_ms = clock.elapsed().as_millis();
    let (switch_runs, bounds): (Vec<Member>, Vec<ExactInterval>) = switch_runs.into_iter().unzip();
    let switch_charge = family_charge(switch_runs.len());
    println!(
        "  (c) across epochs (the switching mixture of the tree's and a Born member's cell faces at α = 2^(−j), j = 1..{shares}; {} members; {switch_ms} ms wall):",
        switch_runs.len()
    );
    for (m, (source, _)) in born.iter().enumerate() {
        let span = m * shares as usize..(m + 1) * shares as usize;
        let (row, _) = least(&switch_runs[span.clone()]);
        let best_bound = bounds[span.clone()]
            .iter()
            .min_by(|a, b| a.upper.cmp(&b.upper))
            .expect("a rate");
        println!(
            "    {}: best {} {} against the tree; Decision 30's plain mixture {}; the dominance bound {}; the cell-grain oracle {}",
            source.label,
            switch_runs[span.start + row].label,
            reading_of(
                &difference_interval(&switch_runs[span.start + row].bits, &tree_code),
                grain
            ),
            reading_of(&difference_interval(&plain[m], &tree_code), grain),
            reading_of(best_bound, grain),
            reading_of(&born_oracles[m][1].0, grain),
        );
    }
    let switch_oracle = born_oracles
        .iter()
        .map(|o| o[1].0.clone())
        .min_by(|a, b| a.upper.cmp(&b.upper))
        .expect("a member");
    let best_bound = bounds
        .iter()
        .min_by(|a, b| a.upper.cmp(&b.upper))
        .expect("a bound");
    let switch_price =
        &best_bound.upper - &switch_oracle.lower + Rat::from_integer(BigInt::from(switch_charge));
    let switch_choice = decide_law(
        "switching (the best Born member's cell-grain oracle; the price the best switching sequence's naming plus the family charge)",
        &switch_runs,
        switch_charge,
        &switch_oracle,
        &switch_price.max(Rat::from_integer(BigInt::from(switch_charge))),
        &tree_code,
        n_dev,
        grain,
    );
    println!("  peak resident so far: {}", resident());
    println!();
    drop(readings);
    drop(best_cells);
    drop(best);

    // ---- 5. The held-out pass, once: the ½ tree and the baselines over the whole passage, the
    // chosen laws beside them.
    println!(
        "5. the held-out pass, once (the whole passage, every cell scored before its own deposit; read on the development cells, the held-out cells, and within them the standing cut's parts):"
    );
    let clock = Instant::now();
    let tree = tree_pass(&cells, &at, &parts, true);
    let (baselines, baselines_ms) = baselines_pass(&cells, alphabet, &parts);
    println!(
        "  the ½ tree's pass {} ms (counted alone), the baselines' {baselines_ms} ms",
        tree.wall
    );
    println!("  the scale checks (the whole passage, {count} cells):");
    scale_readings(
        &format!("the ½ tree at D = {depth}"),
        &tree,
        population,
        grain,
    );
    for (index, name) in BASELINES.iter().enumerate() {
        println!("  {name}:");
        for (slot, part) in SLOTS.iter().enumerate() {
            let bits = bits_of(&baselines[index][slot]);
            println!(
                "    {part} ({} cells): {} a cell; total {}",
                counts[slot],
                per(&bits, counts[slot], grain),
                enclosure(&bits, grain)
            );
        }
    }
    held_out_readings(
        &format!("the ½ tree at D = {depth} (charged its {depth_bits} depth bits)"),
        &tree.codes,
        &counts,
        depth_bits,
        depth_bits,
        None,
        &baselines,
        grain,
    );
    if prior_sweep.chosen != prior_sweep.incumbent {
        let law_at = LandmarkDeclaration {
            depth: chosen_depths.chosen,
            prior: chosen_prior.clone(),
            ..declared.clone()
        };
        let pass = tree_pass(&cells, &law_at, &parts, false);
        scale_readings(
            &format!("Decision 32's choice {chosen_prior}"),
            &pass,
            population,
            grain,
        );
        held_out_readings(
            &format!(
                "Decision 32's choice {chosen_prior} at D = {} (charged {} bits)",
                chosen_depths.chosen,
                prior_sweep.chosen_description()
            ),
            &pass.codes,
            &counts,
            prior_sweep.chosen_description(),
            prior_sweep.chosen_description(),
            Some((&tree.codes, depth_bits)),
            &baselines,
            grain,
        );
    }
    let all_slots = |position: usize| parts.slots(position);
    let chosen = [
        local_choice.map(|i| ("node-local", i)),
        stop_choice.map(|i| ("stop mixture", i)),
        switch_choice.map(|i| ("switching", i)),
    ];
    if born_below {
        println!(
            "  the Born face alone codes below the ½ tree on the development cells (its held-out pass is owed here)"
        );
    }
    if chosen.iter().all(Option::is_none) {
        println!(
            "  no local law codes below the ½ tree on the development cells, charged: no local law is read held out"
        );
    }
    for (name, index) in chosen.into_iter().flatten() {
        let clock_law = Instant::now();
        let (codes, charge, label) = match name {
            "node-local" => {
                let (m, j) = local_members[index];
                let (whole, _) = born_source(&cells, &born_declarations[m]);
                let (codes, _, _) = local_run(
                    &cells,
                    &all_slots,
                    &at,
                    LocalLaw::new(j).expect("a rung"),
                    &whole,
                );
                (codes, local_charge, local_runs[index].label.clone())
            }
            "stop mixture" => {
                let (faces, join, label) = &stop_members[index];
                let codes = mixture_pass(
                    &cells,
                    &at,
                    faces.iter().map(|&k| laws[k].clone()).collect(),
                    join.clone(),
                    &parts,
                );
                let development = bits_of(&codes[0]);
                let joins = &stop_runs[index].bits;
                println!(
                    "    check: the owner's StopMixture meets the joins' development code (one exact product): {}",
                    development.lower <= joins.upper && joins.lower <= development.upper
                );
                (codes, stop_charge, label.clone())
            }
            _ => {
                let (m, j) = switch_members[index];
                let (whole, _) = born_source(&cells, &born_declarations[m]);
                let (whole_tree, whole_digits) = tree_source(&cells, &at);
                let tree_products = cell_products(&whole_tree, &whole_digits, cells.len(), lattice);
                let born_products = cell_products(&whole, &whole_digits, cells.len(), lattice);
                let (codes, _) = switching_stream(
                    &tree_products,
                    &born_products,
                    &whole_digits,
                    lattice,
                    Some(j),
                    widths_at.carrier,
                    &all_slots,
                );
                (codes, switch_charge, switch_runs[index].label.clone())
            }
        };
        println!(
            "  {name}'s held-out pass: {} ms",
            clock_law.elapsed().as_millis()
        );
        held_out_readings(
            &format!(
                "{name}: {label} (charged its family's {charge} bits and the depth's {depth_bits})"
            ),
            &codes,
            &counts,
            charge + depth_bits,
            charge,
            Some((&tree.codes, 0)),
            &baselines,
            grain,
        );
    }
    // Decision 34's adopted law, declared before this cut was read, unless it is the stop choice.
    let (adopted_priors, adopted_join) = adopted_law();
    let is_adopted = |index: usize| {
        let (faces, join, _) = &stop_members[index];
        *join == adopted_join
            && faces.iter().map(|&k| laws[k].clone()).collect::<Vec<_>>() == adopted_priors
    };
    let adopted_index = (0..stop_members.len()).find(|&index| is_adopted(index));
    if stop_choice.is_none_or(|index| !is_adopted(index)) {
        adopted_readings(
            &cells,
            &at,
            &parts,
            &counts,
            depth_bits,
            &tree.codes,
            &baselines,
            adopted_index.map(|index| &stop_runs[index].bits),
            grain,
        );
    }
    println!(
        "  the held-out pass: {} ms wall",
        clock.elapsed().as_millis()
    );
    println!();

    // ---- 6. The standing cut alone, beside the same cells read here.
    let clock = Instant::now();
    let standing_cut = Cut {
        cells: standing_cells.clone(),
        held_out: vec![standing_held.clone()],
    };
    let standing_run = prequential(
        &standing_cut,
        &cell_letters(&standing_cells),
        &standing_declared,
    )
    .expect("the standing cut's own run");
    println!(
        "6. the standing cut alone (its own ½ tree at D = {}, n* = {standing_count}, prequential from its first cell; {} ms), beside the same cells read at the wide cut's standing:",
        standing_declared.depth,
        clock.elapsed().as_millis()
    );
    let rows = [
        (
            "the tree",
            &standing_run.held_out.tree,
            &standing_run.development.tree,
            &tree.codes,
        ),
        (
            "online order-0 KT",
            &standing_run.held_out.order_zero,
            &standing_run.development.order_zero,
            &baselines[1],
        ),
        (
            "online order-1 KT",
            &standing_run.held_out.order_one,
            &standing_run.development.order_one,
            &baselines[2],
        ),
        (
            "PPM order 2",
            &standing_run.held_out.ppm,
            &standing_run.development.ppm,
            &baselines[3],
        ),
    ];
    for (name, alone_held, alone_dev, wide) in rows {
        println!(
            "  {name}: the standing cut's held-out {} cells alone {} a cell, at the wide cut {} a cell; its development {} cells alone {} a cell, at the wide cut {} a cell",
            counts[3],
            per(alone_held, counts[3], grain),
            per(&bits_of(&wide[3]), counts[3], grain),
            counts[2],
            per(alone_dev, counts[2], grain),
            per(&bits_of(&wide[2]), counts[2], grain)
        );
    }
    println!();
    println!(
        "wall time (exterior): the harness {} ms; the process's resident peak {}",
        setup.elapsed().as_millis(),
        resident()
    );
}

fn main() {
    let arguments: Vec<String> = std::env::args().skip(1).collect();
    let path = match arguments.as_slice() {
        [key, value] if key == "cut-file" => value.clone(),
        [key, value, mode] if key == "cut-file" && mode == "letters" => {
            letters_harness(value, false);
            return;
        }
        [key, value, mode] if key == "cut-file" && mode == "prior" => {
            prior_harness(value);
            return;
        }
        [key, value, mode] if key == "cut-file" && mode == "local" => {
            local_harness(value);
            return;
        }
        [key, value, mode, standing] if key == "cut-file" && mode == "wide" => {
            wide_harness(value, standing);
            return;
        }
        [key, value, mode, standing] if key == "cut-file" && mode == "wide-adopted" => {
            wide_adopted_harness(value, standing);
            return;
        }
        [key, value, mode, with]
            if key == "cut-file" && mode == "letters" && with == "contacts" =>
        {
            letters_harness(value, true);
            return;
        }
        _ => {
            println!(
                "usage: hnn_landmark cut-file <path> [letters [contacts] | prior | local | wide <standing cut> | wide-adopted <standing cut>]"
            );
            return;
        }
    };
    let setup = Instant::now();
    let (bytes, count, held) = read_cut(&path);
    let field = Field::declare(FieldDeclaration::campaign_one(count as u64))
        .expect("campaign 1's declared field over the cut");
    let grain = receiver_grain(&field);
    let alphabet = field.alphabet();
    let cut = Cut {
        cells: bytes.iter().map(|&byte| usize::from(byte)).collect(),
        held_out: vec![held.clone()],
    };
    let declared = LandmarkDeclaration {
        alphabet,
        depth: 1,
        forced: 0,
        population: count as u64,
        grain,
        family: LetterFamily::cells(),
        prior: holonics::hnn::StopPrior::half(),
    };
    let setup = setup.elapsed().as_millis();
    let development = (count - held.len()) as u64;
    println!(
        "hnn_landmark: the landmark tree on its declared lattice (Decision 28, count-only) over the cut file {path}"
    );
    println!(
        "cut: {count} cells, |A| = {alphabet}; held out: cells {}..{} ({} cells, from the manifest); development: {development} cells",
        held.start,
        held.end,
        held.len()
    );
    println!(
        "declared: n* = {count}, L_R = {grain} (campaign 1's receiver); per depth D the widths M_p = ⌈log₂(3 B L_R (2n* + 2)(n* D² + 2D + 1))⌉, W = ⌈log₂(12 B L_R n* D²)⌉, C = M_p + W"
    );
    println!("setup: {setup} ms wall");
    println!();

    let clock = Instant::now();
    let letters = cell_letters(&cut.cells);
    let chosen = choose_depth(&cut, &letters, &declared).expect("the sweep");
    let sweep_wall = clock.elapsed().as_millis();
    sweep(&chosen, &declared, development, grain);
    println!("the sweep: {sweep_wall} ms wall");
    println!();

    let at = LandmarkDeclaration {
        depth: chosen.chosen,
        ..declared.clone()
    };
    let clock = Instant::now();
    let run = prequential(&cut, &letters, &at).expect("the prequential measurement");
    let run_wall = clock.elapsed().as_millis();
    let chosen_bits = chosen
        .tried
        .iter()
        .find(|(depth, _)| *depth == chosen.chosen)
        .map(|(_, bits)| bits.clone())
        .expect("the chosen depth was tried");
    println!(
        "check: the run's development code length is the sweep's at the chosen depth: {}",
        run.development.tree == chosen_bits
    );
    println!();
    population("held out", &run.held_out, grain);
    println!();
    population("development", &run.development, grain);
    println!();
    orderings(
        "held out, the orderings",
        &run.held_out,
        chosen.description_bits,
        grain,
    );
    println!();
    orderings(
        "development, the orderings",
        &run.development,
        chosen.description_bits,
        grain,
    );
    println!();
    tree_run(&run.run, grain);
    println!();
    hot_path(&cut, &at, &held);
    println!();

    let clock = Instant::now();
    let cost = oracle_cost(&cut, &letters, &at).expect("the oracle's run");
    let oracle_wall = clock.elapsed().as_millis();
    println!(
        "the oracle's reference width at D = {}: {}",
        at.depth,
        IdealLandmarks::reference_width(&at)
    );
    oracle(&cost, [development, held.len() as u64], grain);
    println!();
    println!(
        "wall time (exterior): setup {setup} ms; the sweep {sweep_wall} ms; the prequential run {run_wall} ms; the oracle's run {oracle_wall} ms"
    );
}

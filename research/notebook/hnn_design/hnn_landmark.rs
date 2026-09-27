//! **The landmark tree on the standing real cut, executed on its declared dyadic lattice**
//! (Decision 28, count-only; Decisions 32, 34, 35 and 37; rebuild step 4, #73): the notebook's
//! receipt of `holonics::compression::landmark::context::{choose_depth, prequential, oracle_cost}` and of the tree
//! stored where paths part, a committed command run once in release, never a test.
//!
//! ```sh
//! cargo run --release -p holonics --example hnn_landmark -- cut-file .local/cuts/standing-real-cut-campaign-1.bin
//! cargo run --release -p holonics --example hnn_landmark -- cut-file .local/cuts/standing-real-cut-campaign-1.bin letters
//! cargo run --release -p holonics --example hnn_landmark -- cut-file .local/cuts/standing-real-cut-campaign-1.bin letters contacts
//! cargo run --release -p holonics --example hnn_landmark -- cut-file .local/cuts/standing-real-cut-campaign-1.bin prior
//! cargo run --release -p holonics --example hnn_landmark -- cut-file .local/cuts/wide-real-cut.bin wide .local/cuts/standing-real-cut-campaign-1.bin
//! cargo run --release -p holonics --example hnn_landmark -- cut-file .local/cuts/wide-real-cut.bin compact
//! cargo run --release -p holonics --example hnn_landmark -- cut-file .local/cuts/wide-real-cut.bin capacity
//! ```
//!
//! [definition; agent-inferred] **A landmark's storage has a capacity** (`capacity`; Decision 39):
//! Decision 37's tree at its chosen `D = 48` (the `½` prior, the cell-only family), each node's count
//! register carried at the ceiling `L = 2^c` (`context::Capacity`: after the deposit that brings
//! `n_0 + n_1` to `L`, `n ← ⌈n/2⌉`, so the face read before the next arrival is KT's on the carried
//! counts, a function of the arrivals so far), on the wide cut.
//! - **0. The family and its charge**, stated before any passage: `c ∈ {∞, 5, 7, 9, 11}`, charged
//!   `⌈log₂ 5⌉` bits; `c = ∞` is Decision 37's tree and carries no capacity bit, so a ceiling is
//!   adopted only when its development code charged lies below `c = ∞`'s by disjoint exact
//!   enclosures; five development passages of about 25 s, each admitted against the 20 GB cap and
//!   the memory the kernel reports available.
//! - **1. The check**: `c = ∞` on the development cells must read Decision 37's recorded development
//!   code `1801940 + 12/16 + ε`; nothing further is read otherwise.
//! - **2. The ceilings** on the development cells, one passage each: the code (exact, at the grain
//!   and a cell), its difference from `c = ∞`, nodes, label letters, allocated and occupied bytes and
//!   wall time.
//! - **3. The choice**: the least ceiling charged against `c = ∞`, and whether it lies below every
//!   other ceiling.
//! - **4. One held-out passage** of the chosen ceiling over the whole cut (none when `c = ∞` stays),
//!   read against Decision 37's recorded held-out tree `258201 + 3/16 + ε` and PPM-2's
//!   `395598 + 8/16 + ε` (each a grain cell `[n + k/16, n + (k + 1)/16]`), in all and a cell.
//!
//! [definition; agent-inferred] **Stored where paths part** (`compact`; Decision 37): Decision 28's
//! `½` tree over the cell-only family, stored at the faces where paths part (`context::Landmarks`,
//! the one storage: a chain with its bottom is one node at the summed rung), on the wide cut. The prior is Decision 28's, so no family is swept again; only the depth is re-chosen,
//! because memory no longer caps it. Decision 36's `converge` mode, which measured founding at the
//! second arrival, is retired with its Rust realization (commit `d137e8a6`; its receipt is in
//! THE_REBUILD's Decision 36).
//! - **0. The family and the budget**, stated before any passage: `D = 6, 12, 24, 48` and the
//!   deepest depth the carriers admit at `n*`, charged `⌈log₂ 5⌉` bits; about two minutes a
//!   passage, the sweep stopped by a passage past four minutes; the a-priori size, `2n − 1` nodes a
//!   tree reached by `n` arrivals at every depth. Before every passage its projected memory (the
//!   a-priori nodes at the bytes a node measured, with its label pool) is checked against Brandon's
//!   20 GB cap and the memory the kernel reports available, and a passage past either is refused.
//! - **1. `D = 6` on the development cells**: Decision 28's tree at its chosen depth, one passage,
//!   its code exact with its certified residuals summed, its nodes, table entries, label letters,
//!   allocated bytes (the counted allocator's growth, the vectors' and the table's capacity) and
//!   occupied bytes (the stored parts at the bytes each occupies), and wall time. [historical] Its
//!   comparison with Decision 28's arena of one node a depth (equal within the sum of their
//!   certificates) was measured at commit `2fb0c1c0` and left with that arena's retirement.
//! - **2. The depth sweep** of the tree on the development cells, doubling from 6 while the code
//!   falls strictly (`DepthSweep::{decreasing, of}`, the owner's rule), every depth's code, nodes,
//!   label letters, allocated and occupied bytes and wall time.
//! - **3. The choice**: the chosen depth's code charged `⌈log₂ 5⌉`, against Decision 28's tree at
//!   `D = 6` charged `⌈log₂ 6⌉` (Decision 35's family on these cells; Decision 36 added one bit for
//!   its founding law, which Decision 37 does not choose), by disjoint exact enclosures.
//! - **4. One held-out passage** of the chosen tree over the whole cut, every cell scored at the
//!   standing before its own deposit, beside Decision 28's tree at `D = 6` and the baselines
//!   (order-0 and order-1 KT, PPM-2), re-read and choosing nothing: each in all and a cell at the
//!   grain, and the orderings by disjoint exact enclosures.
//!
//! [definition; agent-inferred] **The wide cut** (`wide <standing cut>`; Decision 35): the
//! count-only receiver's tree and Decision 34's adopted law read in one prequential passage over a
//! larger cut. The standing cut must be the wide cut's tail (checked), so its cells lie in the wide
//! held-out range. Every code is a population's faces' product enclosed once
//! (`context::PassageCode`). The laws are the standing cut's choices; no family is swept again.
//! - **0. The memory**: the `½` tree's allocated bytes a node and the baselines' a cell, measured on the
//!   standing cut by the harness's counted allocator (each built alone); the resident bound
//!   `3 (n B D + 2^B − 1)` bytes a node `+ n` bytes a cell (the tree and the two-law stop mixture's
//!   two trees at the a-priori node bound, each cell founding at most `D` nodes in each of its `B`
//!   digit trees, and the baselines) at the standing cut's declared depth, for every power of two
//!   the development stream holds; the largest within Brandon's 20 GB cap, which the pinned cut must
//!   be; and at the pinned population the deepest depth within the cap, which bounds the depth sweep.
//! - **1. The depth** on the development cells (`choose_depth_within`), charged `⌈log₂⌉` of the
//!   depths tried.
//! - **2. One prequential passage** over the whole cut at the chosen depth, every cell scored at the
//!   standing before its own deposit, the coders one after another: the `½` tree (its widths,
//!   operand bits, rebases, releases, drift, rule, largest certified residual, founded nodes and live
//!   bytes: the scale checks); Decision 34's adopted law (`½` joined in each digit tree with
//!   `(1, 3)` at `π_½ = ½`, the owner's `StopMixture`), charged `⌈log₂⌉` of the family it was chosen
//!   from on the standing cut and the depth's bits; and the baselines (uniform, order-0 and order-1
//!   KT, PPM-2).
//! - **3. The readings**: each coder on the development cells, the held-out cells, and the standing
//!   cut's two parts within them, in all and a cell at the grain; **4. the orderings** on the
//!   development and held-out cells: the adopted law against the `½` tree (charged and uncharged),
//!   and each against order-0, order-1 and PPM-2.
//!
//! [historical; measured] **Weighing is local** (`local`; Decision 34) **is retired** with the
//! node-local law: on the development cells it measured Decision 34's three local laws (the
//! node-local law, the stop-weight mixture per digit tree and the switching mixture across epochs)
//! and held out the adopted one (commit `d2a2e0db`, its receipt in THE_REBUILD's Decision 34). The
//! harness is at commit `89460425`; the adopted stop-weight mixture is read by `wide`.
//!
//! [definition; agent-inferred] **The stop-prior decision** (`prior`; Decision 32): on the
//! **development cells only** (the manifest's held-out range is cut away before the sweep reads
//! anything), the cell-only tree under every law of the declared family
//! (`compression::landmark::context::prior_family`: the global dyadic ladder `w = 1 − 2^(−j)`, `j = 1, …, J`, then the
//! per-depth pairs `(j_root, j_below)`, `j_root ≠ j_below`; `J = ⌈log₂(n* B)⌉`,
//! `compression::landmark::context::ladder_top`), each law with its own depth sweep (`choose_depth`) and charged
//! `⌈log₂⌉` of its depths tried, the choice charged `⌈log₂⌉` of the laws tried
//! (`compression::landmark::context::choose_prior`):
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
//!   `Compression/Landmark/Context/Address.cell_only_dominance_with_feature_charge`, `passage_join_bound`): at its
//!   chosen depth `D` its executed code is at most the cell-only tree's at `D` plus one bit a dyadic
//!   cell the development cells opened, plus both trees' certified drift (each tree's a-priori rule
//!   a cell, `Landmarks::face_rule`, times the cells), checked by exact enclosures;
//! - the widths each family derives (its path depth `P = D + D(1 + r) + 2`) and its wall time.
//!
//! [definition] **What it runs** (the owner's header, `compression::landmark::context`):
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
use holonics::compression::landmark::context::{
    Capacity, ChartReport, Coded, DepthSweep, Feature, IdealLandmarks, JoinTree,
    LandmarkDeclaration, Landmarks, Letter, LetterFamily, OracleCost, PassageCode, PriorSweep,
    StopMixture, StopPrior, TreeRun, Widths, address, cell_letters, choose_depth,
    choose_depth_within, choose_prior, code_length, development, ladder_top, odometer_digits,
    oracle_cost, prequential, prior_family, tree_prequential,
};
use holonics::hnn::ratio::interval_sum;
use holonics::hnn::receiving::clock_letters;
use holonics::hnn::receiving::landmark_declaration_with;
use holonics::hnn::reference::{Baselines, PPM_ORDER};
use holonics::hnn::{Cut, Field, FieldDeclaration, Reference};
use holonics::navigator::trace::SiteKind;
use holonics::ratio::Rat;
use holonics::ratio::algebraic::ExactInterval;
use num_bigint::BigInt;
use num_bigint::BigUint;
use num_traits::Zero;
use std::collections::BTreeSet;

use exterior::{
    against, difference, enclosure, exact, manifest_number, per, read_cut, reading_of,
    receiver_grain,
};

/// [definition; agent-inferred] **The harness's allocator, counted when asked** (exterior; Decisions
/// 35 and 36's memory readings): the system allocator; while a thread has counting on, the bytes it
/// allocates less the bytes it frees are kept in that thread's counter, so a tree built and dropped
/// on one thread holds the counter's difference across its building, and trees built together on
/// several workers are each counted alone (Decision 36's concurrent sweep). The counters are
/// thread-local and constant-initialized, so the allocator never allocates for them. Counting is
/// off by default.
struct Counted;

thread_local! {
    static COUNTING: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
    static LIVE: std::cell::Cell<isize> = const { std::cell::Cell::new(0) };
}

/// Add `bytes` to this thread's counter when its counting is on.
fn count_bytes(bytes: isize) {
    let _ = COUNTING.try_with(|on| {
        if on.get() {
            let _ = LIVE.try_with(|live| live.set(live.get() + bytes));
        }
    });
}

unsafe impl std::alloc::GlobalAlloc for Counted {
    unsafe fn alloc(&self, layout: std::alloc::Layout) -> *mut u8 {
        let pointer = unsafe { std::alloc::System.alloc(layout) };
        if !pointer.is_null() {
            count_bytes(layout.size() as isize);
        }
        pointer
    }

    unsafe fn dealloc(&self, pointer: *mut u8, layout: std::alloc::Layout) {
        unsafe { std::alloc::System.dealloc(pointer, layout) };
        count_bytes(-(layout.size() as isize));
    }

    unsafe fn realloc(&self, pointer: *mut u8, layout: std::alloc::Layout, size: usize) -> *mut u8 {
        let moved = unsafe { std::alloc::System.realloc(pointer, layout, size) };
        if !moved.is_null() {
            count_bytes(size as isize - layout.size() as isize);
        }
        moved
    }
}

#[global_allocator]
static COUNTED: Counted = Counted;

/// Counting on or off, on this thread.
fn counting(on: bool) {
    COUNTING.with(|counting| counting.set(on));
}

/// This thread's counter: the bytes it allocated less the bytes it freed while counting.
fn live() -> isize {
    LIVE.with(std::cell::Cell::get)
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
        prior: holonics::compression::landmark::context::StopPrior::half(),
        capacity: Capacity::Unbounded,
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
        capacity: Capacity::Unbounded,
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
// the charges

/// A family's charge `⌈log₂ |family|⌉`.
fn family_charge(members: usize) -> u64 {
    ceil_log2(&BigUint::from(members))
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
/// tree at `depth` over the standing cut's cells, its allocated bytes (the counted allocator's, the tree
/// alone on its thread) over its founded nodes; the online baselines' allocated bytes over the cells
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
        "0. memory (the cap {CAP} bytes): on the standing cut ({} cells) the ½ tree at D = {depth} holds {} nodes in {} allocated bytes, {} bytes a node ({} rem {} over {}); the baselines {} allocated bytes, {} bytes a cell ({} rem {} over {})",
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
/// deposit; the faces' products per slot, the tree's chart, stored nodes, stored bits, rule and
/// largest certified residual, its allocated bytes when counted alone, and its wall time.
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
            ", {bytes} allocated bytes ({} rem {} over {} a node)",
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

/// **Decision 34's digit-tree family on the standing cut** (the `local` mode's, from which the
/// adopted law was chosen): `½` against each other law of Decision 32's family at the incumbent's
/// rungs `j = 1..J`, then the balanced global ladder and the balanced whole family. The adopted law
/// is charged `⌈log₂⌉` of it beside the depth's bits.
fn adopted_family(standing: &LandmarkDeclaration) -> usize {
    let top = ladder_top(standing);
    (prior_family(top).len() - 1) * top as usize + 2
}

/// A coder's readings on the parts: each part's bits a cell and in all, at the grain.
fn part_readings(label: &str, codes: &[PassageCode; 4], counts: &[u64; 4], grain: u64) {
    println!("  {label}:");
    for (slot, name) in SLOTS.iter().enumerate() {
        let bits = bits_of(&codes[slot]);
        println!(
            "    {name} ({} cells): {} a cell; total {}",
            counts[slot],
            per(&bits, counts[slot], grain),
            enclosure(&bits, grain)
        );
    }
}

/// **An ordering on the development and held-out cells**: `a` charged `a.1` bits against `b`
/// charged `b.1`, decided by disjoint exact enclosures.
fn part_orderings(
    label: &str,
    a: (&[PassageCode; 4], u64),
    b: (&[PassageCode; 4], u64),
    counts: &[u64; 4],
    grain: u64,
) {
    for (slot, name) in SLOTS.iter().enumerate().take(2) {
        ordering(
            &format!("{name}, {label}"),
            &charged(&bits_of(&a.0[slot]), a.1),
            &charged(&bits_of(&b.0[slot]), b.1),
            counts[slot],
            grain,
        );
    }
}

/// **Decision 35's pass on the wide cut** (`wide <standing cut>`; module header, "The wide cut"):
/// the memory's derivation and depth cap, the depth on the development cells, then one prequential
/// passage over the whole cut of the `½` tree, Decision 34's adopted law and the baselines, each
/// read on the parts and ordered.
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
        "hnn_landmark wide: the count-only receiver on the wide cut (Decision 35), one prequential passage over the cut file {path}"
    );
    println!(
        "cut: {count} cells, |A| = {alphabet}, B = {}; held out: cells {}..{} ({} cells, from the manifest); development: {} cells; n* = {count}, L_R = {grain}; the standing cut ({standing_count} cells, held out {}..{}) is its tail, cells {offset}..{count}",
        odometer_digits(alphabet),
        held.start,
        held.end,
        held.len(),
        dev.len(),
        standing_held.start,
        standing_held.end
    );
    println!();
    let (_, deepest) = memory_derivation(&standing_cells, &standing_declared, count, stream);
    println!();
    let declared = LandmarkDeclaration {
        alphabet,
        depth: 1,
        forced: 0,
        population: count as u64,
        grain,
        family: LetterFamily::cells(),
        prior: StopPrior::half(),
        capacity: Capacity::Unbounded,
    };
    let clock = Instant::now();
    let depth_sweep = choose_depth_within(&dev_cut(&dev), &cell_letters(&dev), &declared, deepest)
        .expect("the depth sweep");
    println!(
        "1. the depth, D = 1..{deepest} at most ({} ms):",
        clock.elapsed().as_millis()
    );
    sweep(&depth_sweep, &declared, dev.len() as u64, grain);
    let (depth, depth_bits) = (depth_sweep.chosen, depth_sweep.description_bits);
    let at = LandmarkDeclaration {
        depth,
        ..declared.clone()
    };
    println!();

    println!(
        "2. one prequential passage over the whole cut at D = {depth}, every cell scored at the standing before its own deposit, each coder read on the parts:"
    );
    let tree = tree_pass(&cells, &at, &parts, true);
    scale_readings(
        &format!("the ½ tree at D = {depth}"),
        &tree,
        count as u64,
        grain,
    );
    let (priors, join) = adopted_law();
    let adopted_label = format!("½ with {} at π_½ = ½", priors[1]);
    let family = adopted_family(&standing_declared);
    let adopted_bits = family_charge(family) + depth_bits;
    println!(
        "  Decision 34's adopted law, {adopted_label} (chosen on the standing cut's development cells from {family} members: charged ⌈log₂ {family}⌉ = {} bits and the depth's {depth_bits}, {adopted_bits} bits):",
        family_charge(family)
    );
    let adopted = mixture_pass(&cells, &at, priors, join, &parts);
    let (baselines, baselines_ms) = baselines_pass(&cells, alphabet, &parts);
    println!(
        "  the baselines ({}): {baselines_ms} ms",
        BASELINES.join(", ")
    );
    println!("  peak resident so far: {}", resident());
    println!();

    println!("3. the readings (bits at L_R = {grain}, uncharged):");
    part_readings(
        &format!("the ½ tree at D = {depth}"),
        &tree.codes,
        &counts,
        grain,
    );
    part_readings(
        &format!("the adopted law {adopted_label}"),
        &adopted,
        &counts,
        grain,
    );
    for (codes, name) in baselines.iter().zip(BASELINES) {
        part_readings(name, codes, &counts, grain);
    }
    println!();

    println!("4. the orderings, each by disjoint exact enclosures:");
    part_orderings(
        &format!(
            "the adopted law charged {adopted_bits} bits against the ½ tree charged {depth_bits}"
        ),
        (&adopted, adopted_bits),
        (&tree.codes, depth_bits),
        &counts,
        grain,
    );
    part_orderings(
        "the adopted law against the ½ tree, both uncharged",
        (&adopted, 0),
        (&tree.codes, 0),
        &counts,
        grain,
    );
    for (index, name) in BASELINES.iter().enumerate().skip(1) {
        part_orderings(
            &format!("the ½ tree charged {depth_bits} bits against {name}"),
            (&tree.codes, depth_bits),
            (&baselines[index], 0),
            &counts,
            grain,
        );
    }
    for (index, name) in BASELINES.iter().enumerate().skip(1) {
        part_orderings(
            &format!("the adopted law charged {adopted_bits} bits against {name}"),
            (&adopted, adopted_bits),
            (&baselines[index], 0),
            &counts,
            grain,
        );
    }
    println!();
    println!(
        "wall time (exterior): the harness {} ms; the process's resident peak {}",
        setup.elapsed().as_millis(),
        resident()
    );
}

// -------------------------------------------------------------------------------------------
// Decision 37: the tree is stored at the faces where paths part (`compact`)

/// Decision 35's depth sweep of the `½` tree on the wide cut's development cells tried `D = 1..6`
/// (its receipt): Decision 28's tree at `D = 6` is charged `⌈log₂ 6⌉` bits.
const DECISION_35_DEPTHS: usize = 6;

/// Decision 35's receipt: the full arena held 178 bytes a node on the wide cut (its a-priori
/// bound  nodes at those bytes projects the full arena's passage).
const DECISION_35_NODE_BYTES: u128 = 178;

/// **The declared doubling family** (Decision 37, stated before any passage): `D = 6, 12, 24, 48`,
/// then the deepest depth the carriers admit at the cut's population.
const DOUBLING: [usize; 4] = [6, 12, 24, 48];

/// **A passage's budget**, stated in advance: about two minutes; a passage past four minutes stops
/// the sweep there, and the depth is chosen among what was measured.
const PASSAGE_STOP_MS: u128 = 240_000;

/// [definition; agent-inferred] **The bytes a stored node occupies on the host** (`compression::landmark::context`,
/// "The arena"): its chart 80, its masses 8, its depth word 4 and its label end 4 in the flat
/// vectors; a child-table entry `(key, child)` 16; a label letter 4.
const NODE_BYTES: u128 = 96;
const ENTRY_BYTES: u128 = 16;
const LETTER_BYTES: u128 = 4;

/// **One passage of a tree over a stream**, its tree counted alone on its thread: the faces'
/// products on `[development, held out]` (cells before and from `development`), the certified
/// per-cell residuals summed on each part (bits, exact), the stored nodes, child-table entries and
/// label letters, the allocated bytes (the counted allocator's growth: capacity, which the vectors
/// and the table reserve by doubling, not occupancy), the widths, chart, rule, largest residual and
/// wall time.
struct Pass {
    depth: usize,
    codes: [PassageCode; 2],
    residuals: [Rat; 2],
    nodes: usize,
    entries: usize,
    held: usize,
    bytes: usize,
    widths: Widths,
    chart: ChartReport,
    rule: Rat,
    largest: Rat,
    wall: u128,
}

fn pass(cells: &[usize], development: usize, declaration: &LandmarkDeclaration) -> Pass {
    let clock = Instant::now();
    counting(true);
    let before = live();
    let mut tree = Landmarks::new(declaration.clone()).expect("a declared tree");
    let mut codes = [PassageCode::new(); 2];
    let mut residuals = [Rat::zero(), Rat::zero()];
    let mut largest = Rat::zero();
    for (position, &class) in cells.iter().enumerate() {
        let reading = tree
            .receive(&address(cells, position, declaration.depth), class)
            .expect("a cell within the declaration");
        let part = usize::from(position >= development);
        codes[part]
            .face(&reading.executed)
            .expect("a positive face");
        residuals[part] += &reading.residual;
        if reading.residual > largest {
            largest = reading.residual;
        }
    }
    let bytes = grown(before);
    counting(false);
    // Every stored node but a root is one child-table entry.
    let roots = tree
        .arena()
        .roots()
        .iter()
        .filter(|&&root| root != u32::MAX)
        .count();
    Pass {
        depth: declaration.depth,
        codes,
        residuals,
        nodes: tree.nodes(),
        entries: tree.nodes() - roots,
        held: tree.held(),
        bytes,
        widths: tree.widths(),
        chart: tree.chart(),
        rule: tree.face_rule(),
        largest,
        wall: clock.elapsed().as_millis(),
    }
}

/// **A passage's occupied bytes**: its stored nodes, child-table entries and label letters at the
/// bytes each occupies ([`NODE_BYTES`], [`ENTRY_BYTES`], [`LETTER_BYTES`]).
fn occupied(pass: &Pass) -> u128 {
    NODE_BYTES * pass.nodes as u128
        + ENTRY_BYTES * pass.entries as u128
        + LETTER_BYTES * pass.held as u128
}

/// A passage's line: its code on a part (exact, at the grain, and a cell), its certified residual,
/// and its stored nodes, label letters, allocated and occupied bytes and wall time.
fn pass_line(pass: &Pass, part: usize, cells: u64, grain: u64) {
    let bits = bits_of(&pass.codes[part]);
    println!(
        "  D = {} ({}): {}; a cell {}",
        pass.depth,
        widths(&pass.widths),
        enclosure(&bits, grain),
        per(&bits, cells, grain)
    );
    println!(
        "    certified residuals summed: at most {} bits; the largest a cell {} bits, {} the rule ({} bits)",
        exact(&dyadic_ceiling(&pass.residuals[part])),
        exact(&dyadic_ceiling(&pass.largest)),
        if pass.largest <= pass.rule {
            "within"
        } else {
            "ABOVE"
        },
        exact(&dyadic_ceiling(&pass.rule))
    );
    println!(
        "    {} nodes stored, {} table entries, {} label letters; {} allocated bytes ({} rem {} over {} a node), {} occupied ({NODE_BYTES} a node, {ENTRY_BYTES} an entry, {LETTER_BYTES} a letter); {} rebases ({} at the most-rebased node), the largest drift ≤ {} bits; {} ms",
        pass.nodes,
        pass.entries,
        pass.held,
        pass.bytes,
        pass.bytes / pass.nodes.max(1),
        pass.bytes % pass.nodes.max(1),
        pass.nodes,
        occupied(pass),
        pass.chart.rebases,
        pass.chart.node_rebases,
        exact(&dyadic_ceiling(&pass.chart.drift)),
        pass.wall
    );
}

/// **The deepest depth the carriers admit** at a declaration's population: the widths' products
/// fit `u128` (`Landmarks::new` refuses past it).
fn deepest_admitted(declared: &LandmarkDeclaration) -> usize {
    let mut depth = 1;
    while Landmarks::new(LandmarkDeclaration {
        depth: depth + 1,
        ..declared.clone()
    })
    .is_ok()
    {
        depth += 1;
    }
    depth
}

/// **A passage's projected memory** (stated before it runs): the compacted tree's a-priori nodes
/// `2 n B` (each arrival founds at most an upper part and a leaf in each of its at most `B` digit
/// trees) at the bytes a node measured on an earlier compacted passage, and its label pool's
/// `n D` letters of 4 bytes; doubled for the vectors' and the table's growth.
fn projected(cells: u128, digits: u128, depth: u128, node_bytes: u128) -> u128 {
    2 * (2 * cells * digits * node_bytes + 4 * cells * depth)
}

/// **Whether a passage may run**: its projection within the cap and within the memory the kernel
/// reports available now (printed), else refused.
fn admitted(label: &str, projection: u128) -> bool {
    let available = exterior::available_memory();
    let fits = projection <= CAP && available.is_none_or(|free| projection <= free);
    println!(
        "  memory before {label}: {} bytes available, the projection {projection} bytes, the cap {CAP}: {}",
        available.map_or_else(|| "unread".to_string(), |free| free.to_string()),
        if fits { "admitted" } else { "REFUSED" }
    );
    fits
}

/// **Decision 37's pass on the wide cut** (`compact`; module header, "Stored where paths part").
#[allow(clippy::too_many_lines)]
fn compact_harness(path: &str) {
    let setup = Instant::now();
    let (bytes, count, held) = read_cut(path);
    let field = Field::declare(FieldDeclaration::campaign_one(count as u64))
        .expect("campaign 1's declared field over the cut");
    let grain = receiver_grain(&field);
    let alphabet = field.alphabet();
    let digits = odometer_digits(alphabet);
    let cells: Vec<usize> = bytes.iter().map(|&byte| usize::from(byte)).collect();
    let cut = Cut {
        cells: cells.clone(),
        held_out: vec![held.clone()],
    };
    let dev = development(&cut);
    assert_eq!(
        dev.as_slice(),
        &cells[..held.start],
        "the held-out range closes the cut"
    );
    let (n_dev, n_held) = (dev.len() as u64, held.len() as u64);
    let declared = LandmarkDeclaration {
        alphabet,
        depth: DECISION_35_DEPTHS,
        forced: 0,
        population: count as u64,
        grain,
        family: LetterFamily::cells(),
        prior: StopPrior::half(),
        capacity: Capacity::Unbounded,
    };
    let at = |depth: usize| LandmarkDeclaration {
        depth,
        ..declared.clone()
    };
    println!(
        "hnn_landmark compact: the tree stored at the faces where paths part (Decision 37), over the cut file {path}"
    );
    println!(
        "cut: {count} cells, |A| = {alphabet}, B = {digits}; held out: cells {}..{} ({n_held} cells, from the manifest); development: {n_dev} cells; n* = {count}, L_R = {grain}; the ½ stop prior, the cell-only family",
        held.start, held.end,
    );
    println!();

    // 0. The family, its charge, and the memory.
    let deepest = deepest_admitted(&declared);
    let family: Vec<usize> = DOUBLING
        .iter()
        .copied()
        .filter(|&depth| depth < deepest)
        .chain([deepest])
        .collect();
    let charge = family_charge(family.len());
    let union = family_charge(DECISION_35_DEPTHS + family.len() - 1);
    let incumbent_charge = family_charge(DECISION_35_DEPTHS);
    println!(
        "0. the declared family, doubling from 6 to the carriers' limit (D ≤ {deepest} at n* = {count}): D = {family:?}, charged ⌈log₂ {}⌉ = {charge} bits; Decision 28's tree at D = 6 was chosen from D = 1..6 on these cells (Decision 35), charged ⌈log₂ 6⌉ = {incumbent_charge} (Decision 36 added its founding law's bit); the union of both families, {} depths, would charge each ⌈log₂ {}⌉ = {union}",
        family.len(),
        DECISION_35_DEPTHS + family.len() - 1,
        DECISION_35_DEPTHS + family.len() - 1,
    );
    println!(
        "  the budget, stated in advance: about two minutes a passage; a passage past {PASSAGE_STOP_MS} ms stops the sweep; at most {} development passages of the compacted tree",
        family.len()
    );
    println!(
        "  the a-priori size at every depth: a tree reached by n arrivals stores at most 2n − 1 nodes, so a passage of n cells at most 2 n B = {} nodes (development), and its label pool at most n D letters",
        2 * u128::from(n_dev) * u128::from(digits)
    );
    println!();

    // 1. D = 6: Decision 28's depth, the development cells only.
    println!(
        "1. D = 6 on the development cells, one passage: Decision 28's tree at its chosen depth, stored where paths part (the same prior and code in ℚ, Lean compacted_is_the_full_tree; the retired arena of one node a depth read it equal within their certificates at commit 2fb0c1c0)"
    );
    let first_bytes = DECISION_35_NODE_BYTES;
    if !admitted(
        "the tree at D = 6",
        projected(u128::from(n_dev), u128::from(digits), 6, first_bytes),
    ) {
        return;
    }
    let first = pass(&dev, dev.len(), &at(6));
    pass_line(&first, 0, n_dev, grain);
    let first_bits = bits_of(&first.codes[0]);
    println!("  peak resident so far: {}", resident());
    println!();

    // 2. The depth sweep of the compacted tree, doubling, until the code rises.
    println!(
        "2. the depth sweep of the compacted tree on the development cells, D = {family:?} until the code rises (DepthSweep's rule), within the budget:"
    );
    let node_bytes = |pass: &Pass| {
        let letters = 4 * pass.held as u128;
        (pass.bytes as u128)
            .saturating_sub(letters)
            .div_ceil(pass.nodes.max(1) as u128)
    };
    let mut tried: Vec<(usize, ExactInterval)> = vec![(6, first_bits.clone())];
    let mut passes = vec![first];
    let mut stopped = None;
    for &depth in &family[1..] {
        let last = passes.last().expect("a passage");
        if !DepthSweep::decreasing(&tried) {
            break;
        }
        if last.wall > PASSAGE_STOP_MS {
            stopped = Some(format!(
                "the passage at D = {} took {} ms, past {PASSAGE_STOP_MS}",
                last.depth, last.wall
            ));
            break;
        }
        let projection = projected(
            u128::from(n_dev),
            u128::from(digits),
            depth as u128,
            node_bytes(last),
        );
        if !admitted(&format!("D = {depth}"), projection) {
            stopped = Some(format!("the projection at D = {depth} was refused"));
            break;
        }
        let run = pass(&dev, dev.len(), &at(depth));
        pass_line(&run, 0, n_dev, grain);
        tried.push((depth, bits_of(&run.codes[0])));
        passes.push(run);
    }
    if let Some(reason) = &stopped {
        println!("  the sweep stopped: {reason}");
    }
    let sweep = DepthSweep::of(tried).expect("at least one depth");
    let chosen = sweep.chosen;
    let chosen_bits = sweep
        .tried
        .iter()
        .find(|(depth, _)| *depth == chosen)
        .map(|(_, bits)| bits.clone())
        .expect("the chosen depth was tried");
    println!(
        "  chosen D = {chosen} of {} tried ({}); peak resident so far: {}",
        sweep.tried.len(),
        if DepthSweep::decreasing(&sweep.tried) {
            "the code fell at every depth tried"
        } else {
            "the last depth's code did not fall below the one before"
        },
        resident()
    );
    println!();

    // 3. The choice against Decision 28's tree at D = 6.
    println!(
        "3. the development cells' choice: the compacted tree at D = {chosen} charged {charge} bits against Decision 28's tree at D = 6 charged {incumbent_charge} (the union charge, {union} each, moves neither):"
    );
    let charged_chosen = charged(&chosen_bits, charge);
    let charged_full = charged(&first_bits, incumbent_charge);
    println!(
        "  the compacted tree at D = {chosen}: {}",
        enclosure(&charged_chosen, grain)
    );
    println!(
        "  Decision 28's tree at D = 6: {}",
        enclosure(&charged_full, grain)
    );
    ordering(
        "the compacted tree against Decision 28's, charged",
        &charged_chosen,
        &charged_full,
        n_dev,
        grain,
    );
    println!();

    // 4. One held-out passage at the chosen depth.
    println!(
        "4. one prequential passage over the whole cut at D = {chosen}, every cell scored at the standing before its own deposit; beside it Decision 28's tree at D = 6 and the baselines re-read (choosing nothing):"
    );
    let projection = passes
        .iter()
        .find(|pass| pass.depth == chosen)
        .map_or(0, |pass| {
            projected(
                count as u128,
                u128::from(digits),
                chosen as u128,
                node_bytes(pass),
            )
        });
    if !admitted(&format!("the held-out passage at D = {chosen}"), projection) {
        return;
    }
    let whole = pass(&cells, held.start, &at(chosen));
    pass_line(&whole, 1, n_held, grain);
    println!(
        "    check: its development code is the sweep's at D = {chosen}: {}",
        bits_of(&whole.codes[0]) == chosen_bits
    );
    let incumbent = pass(&cells, held.start, &at(6));
    pass_line(&incumbent, 1, n_held, grain);
    println!(
        "    check: its development code is step 1's: {}",
        bits_of(&incumbent.codes[0]) == first_bits
    );
    let parts = Parts {
        held: held.clone(),
        standing: count..count,
        standing_held: count..count,
    };
    let (baselines, baselines_ms) = baselines_pass(&cells, alphabet, &parts);
    println!(
        "  the baselines ({}): {baselines_ms} ms",
        BASELINES.join(", ")
    );
    println!();
    println!("  held out ({n_held} cells), bits at L_R = {grain}, uncharged:");
    let rows: Vec<(String, ExactInterval)> = [
        (
            format!("the compacted tree at D = {chosen}"),
            bits_of(&whole.codes[1]),
        ),
        (
            "Decision 28's tree at D = 6".to_string(),
            bits_of(&incumbent.codes[1]),
        ),
    ]
    .into_iter()
    .chain(
        BASELINES
            .iter()
            .enumerate()
            .skip(1)
            .map(|(index, name)| (name.to_string(), bits_of(&baselines[index][1]))),
    )
    .collect();
    for (name, bits) in &rows {
        println!("    {name}: {}", enclosure(bits, grain));
        println!("      a cell {}", per(bits, n_held, grain));
    }
    println!();
    println!("  held out, the orderings, each by disjoint exact enclosures:");
    let chosen_held = charged(&rows[0].1, charge);
    ordering(
        &format!(
            "the compacted tree charged {charge} bits against Decision 28's tree at D = 6 charged {incumbent_charge}"
        ),
        &chosen_held,
        &charged(&rows[1].1, incumbent_charge),
        n_held,
        grain,
    );
    for (name, bits) in rows.iter().skip(2) {
        ordering(
            &format!("the compacted tree charged {charge} bits against {name}"),
            &chosen_held,
            bits,
            n_held,
            grain,
        );
    }
    println!();
    println!(
        "wall time (exterior): the harness {} ms; the process's resident peak {}",
        setup.elapsed().as_millis(),
        resident()
    );
}

// -------------------------------------------------------------------------------------------
// Decision 39: a landmark's storage has a capacity (`capacity`)

/// Decision 37's chosen depth on the wide cut's development cells (its receipt), at which the
/// capacity family is read.
const DECISION_37_DEPTH: usize = 48;

/// **The declared capacity family** (Decision 39, stated before any passage): `c = ∞` (Decision
/// 37's tree) and the ceilings `L = 2^c`, `c = 5, 7, 9, 11`, charged `⌈log₂ 5⌉` bits.
const CEILINGS: [u32; 4] = [5, 7, 9, 11];

/// [established-bounded; measured] **Decision 37's recorded readings on the wide cut** at
/// `L_R = 16` (THE_REBUILD, Decision 37's receipt), each `carry + phase/16 + ε`, `0 ≤ ε < 1/16`: the
/// development code at `D = 48`, which `c = ∞` must reproduce; the held-out tree at `D = 48` and
/// PPM-2 held out, against which the chosen ceiling's one held-out passage is read.
const DECISION_37_DEVELOPMENT: (u64, u64) = (1_801_940, 12);
const DECISION_37_HELD_OUT: (u64, u64) = (258_201, 3);
const PPM_TWO_HELD_OUT: (u64, u64) = (395_598, 8);

/// **A recorded grain reading as an exact enclosure**: `n + k/L + ε`, `0 ≤ ε < 1/L`, lies in
/// `[n + k/L, n + (k + 1)/L]`.
fn recorded(reading: (u64, u64), grain: u64) -> ExactInterval {
    let at = |phase: u64| {
        Rat::from_integer(BigInt::from(reading.0))
            + Rat::new(BigInt::from(phase), BigInt::from(grain))
    };
    ExactInterval {
        lower: at(reading.1),
        upper: at(reading.1 + 1),
    }
}

/// **Whether an enclosure reads a recorded grain cell exactly**: both endpoints in the cell
/// `n + k/L + ε`.
fn reads(interval: &ExactInterval, reading: (u64, u64), grain: u64) -> bool {
    [&interval.lower, &interval.upper].into_iter().all(|value| {
        let cell = holonics::hnn::receiving::GrainCell::of(value, grain);
        cell.carry == BigInt::from(reading.0) && cell.phase == reading.1
    })
}

/// **Decision 39's pass on the wide cut** (`capacity`; module header, "A landmark's storage has a
/// capacity").
#[allow(clippy::too_many_lines)]
fn capacity_harness(path: &str) {
    let setup = Instant::now();
    let (bytes, count, held) = read_cut(path);
    let field = Field::declare(FieldDeclaration::campaign_one(count as u64))
        .expect("campaign 1's declared field over the cut");
    let grain = receiver_grain(&field);
    let alphabet = field.alphabet();
    let digits = odometer_digits(alphabet);
    let cells: Vec<usize> = bytes.iter().map(|&byte| usize::from(byte)).collect();
    let cut = Cut {
        cells: cells.clone(),
        held_out: vec![held.clone()],
    };
    let dev = development(&cut);
    assert_eq!(
        dev.as_slice(),
        &cells[..held.start],
        "the held-out range closes the cut"
    );
    let (n_dev, n_held) = (dev.len() as u64, held.len() as u64);
    let depth = DECISION_37_DEPTH;
    let at = |capacity: Capacity| LandmarkDeclaration {
        alphabet,
        depth,
        forced: 0,
        population: count as u64,
        grain,
        family: LetterFamily::cells(),
        prior: StopPrior::half(),
        capacity,
    };
    let family: Vec<Capacity> = std::iter::once(Capacity::Unbounded)
        .chain(CEILINGS.iter().map(|&c| Capacity::Ceiling(c)))
        .collect();
    let charge = family_charge(family.len());
    let depth_charge = family_charge(5);
    println!(
        "hnn_landmark capacity: a landmark's storage has a capacity (Decision 39), over the cut file {path}"
    );
    println!(
        "cut: {count} cells, |A| = {alphabet}, B = {digits}; held out: cells {}..{} ({n_held} cells, from the manifest); development: {n_dev} cells; n* = {count}, L_R = {grain}; D = {depth} (Decision 37's choice, charged ⌈log₂ 5⌉ = {depth_charge} bits), the ½ stop prior, the cell-only family",
        held.start, held.end,
    );
    println!();

    // 0. The family, its charge and the budget, stated before any passage.
    let names: Vec<String> = family.iter().map(ToString::to_string).collect();
    println!(
        "0. the declared family: {}, charged ⌈log₂ {}⌉ = {charge} bits (c = ∞ is Decision 37's tree and carries no capacity bit: a ceiling is adopted only when its development code charged {charge} bits lies below c = ∞'s by disjoint exact enclosures); the budget, stated in advance: {} development passages of about 25 s, then one held-out passage for the chosen ceiling, none when c = ∞ stays",
        names.join(", "),
        family.len(),
        family.len()
    );
    println!(
        "  the law: each node's counts carry, n ← ⌈n/2⌉, after the deposit that brings n_0 + n_1 to L = 2^c; the face read before the next arrival is KT's on the carried counts (a function of the arrivals so far)"
    );
    println!();

    // 1. The check: c = ∞ reproduces Decision 37's development code.
    let projection = |pass: Option<&Pass>| {
        let node_bytes = pass.map_or(DECISION_35_NODE_BYTES, |pass| {
            (pass.bytes as u128)
                .saturating_sub(4 * pass.held as u128)
                .div_ceil(pass.nodes.max(1) as u128)
        });
        projected(
            u128::from(n_dev),
            u128::from(digits),
            depth as u128,
            node_bytes,
        )
    };
    println!(
        "1. the check: c = ∞ on the development cells, one passage, against Decision 37's recorded {} + {}/{grain} + ε",
        DECISION_37_DEVELOPMENT.0, DECISION_37_DEVELOPMENT.1
    );
    if !admitted("c = ∞", projection(None)) {
        return;
    }
    let unbounded = pass(&dev, dev.len(), &at(Capacity::Unbounded));
    capacity_line(Capacity::Unbounded, &unbounded, 0, n_dev, grain);
    let unbounded_bits = bits_of(&unbounded.codes[0]);
    let reproduced = reads(&unbounded_bits, DECISION_37_DEVELOPMENT, grain);
    println!(
        "  check: c = ∞ reads Decision 37's development code {} + {}/{grain} + ε: {reproduced}",
        DECISION_37_DEVELOPMENT.0, DECISION_37_DEVELOPMENT.1
    );
    if !reproduced {
        println!("  the reproduction failed: nothing further is read");
        return;
    }
    println!();

    // 2. The ceilings on the development cells.
    println!("2. the ceilings on the development cells, one passage each:");
    let mut passes: Vec<(Capacity, Pass)> = Vec::new();
    for &capacity in &family[1..] {
        if !admitted(&capacity.to_string(), projection(Some(&unbounded))) {
            println!("  the family stopped: the projection at {capacity} was refused");
            break;
        }
        let run = pass(&dev, dev.len(), &at(capacity));
        capacity_line(capacity, &run, 0, n_dev, grain);
        let bits = bits_of(&run.codes[0]);
        println!(
            "    against c = ∞, uncharged: {} ({})",
            difference(&bits, &unbounded_bits, grain),
            against(&bits, &unbounded_bits)
        );
        passes.push((capacity, run));
    }
    println!("  peak resident so far: {}", resident());
    println!();

    // 3. The choice.
    let least = passes
        .iter()
        .min_by(|a, b| {
            let (x, y) = (bits_of(&a.1.codes[0]), bits_of(&b.1.codes[0]));
            x.lower.cmp(&y.lower)
        })
        .expect("a ceiling was read");
    let least_bits = bits_of(&least.1.codes[0]);
    let least_charged = charged(&least_bits, charge);
    println!(
        "3. the development cells' choice: the least ceiling's code, {}, charged {charge} bits, against c = ∞ uncharged:",
        least.0
    );
    println!(
        "  {} charged: {}",
        least.0,
        enclosure(&least_charged, grain)
    );
    println!("  c = ∞: {}", enclosure(&unbounded_bits, grain));
    ordering(
        &format!("{} charged {charge} bits against c = ∞", least.0),
        &least_charged,
        &unbounded_bits,
        n_dev,
        grain,
    );
    let adopted = least_charged.upper < unbounded_bits.lower;
    let others_below = passes
        .iter()
        .filter(|(capacity, _)| *capacity != least.0)
        .all(|(_, run)| least_bits.upper < bits_of(&run.codes[0]).lower);
    println!(
        "  the choice: {}; the least ceiling lies below every other ceiling by disjoint enclosures: {others_below}",
        if adopted {
            format!("{} (below c = ∞ charged)", least.0)
        } else {
            "c = ∞ stays: the ceiling is rejected".to_string()
        }
    );
    println!();
    if !adopted {
        println!("4. no held-out passage: the development cells keep c = ∞ (the declared rule)");
        println!();
        println!(
            "wall time (exterior): the harness {} ms; the process's resident peak {}",
            setup.elapsed().as_millis(),
            resident()
        );
        return;
    }

    // 4. One held-out passage at the chosen ceiling.
    let chosen = least.0;
    println!(
        "4. one prequential passage over the whole cut at {chosen}, every cell scored at the standing before its own deposit, read against Decision 37's recorded held-out tree ({} + {}/{grain} + ε) and PPM-2 ({} + {}/{grain} + ε):",
        DECISION_37_HELD_OUT.0, DECISION_37_HELD_OUT.1, PPM_TWO_HELD_OUT.0, PPM_TWO_HELD_OUT.1
    );
    let whole_projection = projected(
        count as u128,
        u128::from(digits),
        depth as u128,
        (least.1.bytes as u128)
            .saturating_sub(4 * least.1.held as u128)
            .div_ceil(least.1.nodes.max(1) as u128),
    );
    if !admitted(
        &format!("the held-out passage at {chosen}"),
        whole_projection,
    ) {
        return;
    }
    let whole = pass(&cells, held.start, &at(chosen));
    capacity_line(chosen, &whole, 1, n_held, grain);
    println!(
        "    check: its development code is step 2's at {chosen}: {}",
        bits_of(&whole.codes[0]) == least_bits
    );
    let held_bits = bits_of(&whole.codes[1]);
    let tree = recorded(DECISION_37_HELD_OUT, grain);
    let ppm = recorded(PPM_TWO_HELD_OUT, grain);
    println!("  held out ({n_held} cells), bits at L_R = {grain}:");
    println!("    {chosen}, uncharged: {}", enclosure(&held_bits, grain));
    println!("      a cell {}", per(&held_bits, n_held, grain));
    println!(
        "    Decision 37's tree (recorded): {}; a cell {}",
        enclosure(&tree, grain),
        per(&tree, n_held, grain)
    );
    println!(
        "    PPM-2 (recorded): {}; a cell {}",
        enclosure(&ppm, grain),
        per(&ppm, n_held, grain)
    );
    println!("  held out, the orderings, each by disjoint exact enclosures:");
    ordering(
        &format!(
            "{chosen} charged {charge} bits against Decision 37's tree (both charged the depth's {depth_charge})"
        ),
        &charged(&held_bits, charge),
        &tree,
        n_held,
        grain,
    );
    ordering(
        &format!("{chosen} uncharged against Decision 37's tree"),
        &held_bits,
        &tree,
        n_held,
        grain,
    );
    ordering(
        &format!(
            "{chosen} charged {} bits (the depth's and the capacity's) against PPM-2",
            depth_charge + charge
        ),
        &charged(&held_bits, depth_charge + charge),
        &ppm,
        n_held,
        grain,
    );
    println!();
    println!(
        "wall time (exterior): the harness {} ms; the process's resident peak {}",
        setup.elapsed().as_millis(),
        resident()
    );
}

/// A capacity's passage line: its capacity, then the passage's readings ([`pass_line`]).
fn capacity_line(capacity: Capacity, pass: &Pass, part: usize, cells: u64, grain: u64) {
    println!("  {capacity}:");
    pass_line(pass, part, cells, grain);
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
        [key, value, mode, standing] if key == "cut-file" && mode == "wide" => {
            wide_harness(value, standing);
            return;
        }
        [key, value, mode] if key == "cut-file" && mode == "compact" => {
            compact_harness(value);
            return;
        }
        [key, value, mode] if key == "cut-file" && mode == "capacity" => {
            capacity_harness(value);
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
                "usage: hnn_landmark cut-file <path> [letters [contacts] | prior | wide <standing cut> | compact | capacity]"
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
        prior: holonics::compression::landmark::context::StopPrior::half(),
        capacity: Capacity::Unbounded,
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

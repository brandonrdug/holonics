//! **`census`: U2's read-only standing census of F0's egg** (`docs/plans/THE_REBUILD.md`, U2;
//! `holonics::compression::landmark::context`, "Which merges and releases are future-sufficient";
//! #73, #148). Included by `hnn_population.rs` as its `f0-census` mode; a committed command run once
//! in release, never a test. It reads counts and bytes only; no text of the cut is printed.
//!
//! ```sh
//! cargo run --release -p holonics --example hnn_population -- f0-census .local/cuts/curated-f4-passage-cut.bin
//! ```
//!
//! [definition; agent-inferred] **What it reads.** F0's byte predictor as it stood before U2's
//! acceptance run, the admitted egg alone with its byte tree at the deepest depth (U2's candidate (0),
//! the unmerged tree; `f0-egg` now declares the adopted depth cut, `curated::F0_BYTE_DEPTH`), built by
//! `curated::admitted_egg` with the hazard
//! partition learned on the choosing families and the same comparison hazards, reads F4's development
//! passage cell by cell (`Family::receive`, the population's own call for its one member). The census
//! is taken after the choosing families, and again after the whole passage, where the recorded
//! standing is 2,653 bytes a cell. At each, the egg's whole standing (its canonical checkpoint's
//! length) is printed, and its byte tree (the typed tree at the deepest depth its carriers admit,
//! which holds almost all of it) is read node by node from its arena (`Landmarks::arena`).
//!
//! [definition; agent-inferred] **The rules, each in bytes of the canonical standing**
//! (`Landmarks::encode_standing`: a node is its depth word 4, its label end 4, its masses 8 and its
//! chart 68, with a 12-byte child-table entry, or 4 for a root; a label letter is 4), each by the
//! branch and the bottom depth of the node in address ticks:
//! - **exact for the declared receiver** (the prequential face at every admitted future,
//!   deposits included): E0 the chart's readings kept beside the state (its two certificates, its
//!   cached stop weight and its rebase count: 44 of a node's 96 bytes, which no face reads); E1 the
//!   boundary contexts, which no continuing address reaches; E2 nodes past the admitted depth (none
//!   are founded); E3 pool letters no label reads (a split's key letter kept where the chain held
//!   it);
//! - **charged coarsenings, not retention**: L1 the depth cut at `6, 12, 24, 48` ticks; L2 the
//!   once-reached leaf chains;
//! - **refused**: siblings with equal present counts merged into one register (the present-face
//!   merge; `Context/Merge.equal_present_faces_do_not_merge`).
//!
//! A label letter is released by a rule exactly when no node the rule keeps covers it.

use std::collections::HashMap;
use std::time::Instant;

use holonics::compression::landmark::context::{Landmarks, SectionChart};
use holonics::receiver::population::{AdmittedEgg, Family, HazardPartition, learn_hazard_partition};

use super::curated::admitted_egg;
use super::exterior::{read_curated, read_incidence, resident_set};

/// The bins of a node's bottom depth, in address ticks (a tick is one cell, or one bundle of the
/// typed tree's `1 + r` letters): `≤ 6`, `≤ 12`, `≤ 24`, `≤ 48`, deeper.
const BINS: [usize; 4] = [6, 12, 24, 48];

/// The top bit of a node's depth word: its branch (the bundle tree).
const BRANCH_BIT: u32 = 1 << 31;

/// A node's encoded bytes beside its label letters and its table entry: its depth word 4, its label
/// end 4, its two half-unit masses 8 and its chart 68 (`Landmarks::encode_standing`).
const NODE_BYTES: u64 = 84;

/// A child-table entry's bytes (its `u64` key and `u32` child); a founded root's entry holds a `u32`.
const CHILD_ENTRY_BYTES: u64 = 12;
const ROOT_ENTRY_BYTES: u64 = 4;

/// The chart's readings kept beside the state, which no face reads: its two certificates (`drift`,
/// `excess`, 16 bytes each), its cached stop weight (8, a function of `β`) and its rebase count (4).
const READING_BYTES: u64 = 44;

/// A label letter's bytes.
const LETTER_BYTES: u64 = 4;

/// One bin's census.
#[derive(Clone, Copy, Default)]
struct Bin {
    nodes: u64,
    node_bytes: u64,
    label_bytes: u64,
    readings: u64,
    boundary: u64,
    once_nodes: u64,
    once: u64,
    alike: u64,
}

fn bin_of(ticks: usize) -> usize {
    BINS.iter()
        .position(|&cap| ticks <= cap)
        .unwrap_or(BINS.len())
}

fn bin_name(k: usize) -> String {
    match k {
        0 => format!("ticks ≤ {}", BINS[0]),
        k if k < BINS.len() => format!("{} < ticks ≤ {}", BINS[k - 1], BINS[k]),
        _ => format!("ticks > {}", BINS[BINS.len() - 1]),
    }
}

/// **One landmark tree's census** (module header).
#[allow(clippy::too_many_lines)]
fn tree_census(tree: &Landmarks, name: &str, cells: u64) {
    let view = tree.arena();
    let words = view.words();
    let ends = view.ends();
    let halves = view.halves();
    let pool = view.labels();
    let roots = view.roots();
    let depths = view.branch_depths();
    let per_tick = (depths[depths.len() - 1] / depths[0]).max(1);
    let n = words.len();
    let slots = 2 * (BINS.len() + 1);
    let ticks_of = |branch: usize, letters: usize| -> usize {
        if branch == 0 {
            letters
        } else {
            letters.div_ceil(per_tick)
        }
    };
    // Parents, key letters and each node's children, from the child table.
    let mut parent = vec![u32::MAX; n];
    let mut key_letter = vec![u32::MAX; n];
    let mut offsets = vec![0u32; n + 1];
    let children = view.children();
    for &(key, child) in &children {
        parent[child as usize] = (key >> 32) as u32;
        key_letter[child as usize] = key as u32;
        offsets[(key >> 32) as usize + 1] += 1;
    }
    for i in 0..n {
        offsets[i + 1] += offsets[i];
    }
    let mut fill = offsets.clone();
    let mut listed = vec![0u32; children.len()];
    for &(key, child) in &children {
        let at = &mut fill[(key >> 32) as usize];
        listed[*at as usize] = child;
        *at += 1;
    }
    drop(children);
    drop(fill);
    let bottom = |i: usize| (words[i] & !BRANCH_BIT) as usize;
    let branch = |i: usize| usize::from(words[i] & BRANCH_BIT != 0);
    let top = |i: usize| match parent[i] {
        u32::MAX => 0,
        p => bottom(p as usize) + 1,
    };
    let label = |i: usize| -> std::ops::Range<usize> {
        let end = ends[i] as usize;
        end - (bottom(i) - top(i))..end
    };
    let arrivals = |i: usize| (u64::from(halves[i][0]) + u64::from(halves[i][1]) - 2) / 2;
    let own = |i: usize| {
        NODE_BYTES
            + if parent[i] == u32::MAX {
                ROOT_ENTRY_BYTES
            } else {
                CHILD_ENTRY_BYTES
            }
    };
    // The boundary contexts: a node is unreached when the context at its top already holds the
    // boundary letter `0` (its key letter, or anywhere in an ancestor's context). A chain holding
    // `0` only inside its own label keeps its register: an address that parts from it above the
    // letter reads it.
    let mut zero_below = vec![false; n];
    let mut boundary = vec![false; n];
    let mut stack: Vec<u32> = roots.iter().copied().filter(|&r| r != u32::MAX).collect();
    while let Some(node) = stack.pop() {
        let i = node as usize;
        let above = parent[i] != u32::MAX && zero_below[parent[i] as usize];
        boundary[i] = above || key_letter[i] == 0;
        zero_below[i] = boundary[i] || pool[label(i)].contains(&0);
        stack.extend(&listed[offsets[i] as usize..offsets[i + 1] as usize]);
    }
    drop(zero_below);
    // Siblings holding equal counts (the present-count merge, refused): all but one of each group.
    let mut alike = vec![false; n];
    for p in 0..n {
        let kids = &listed[offsets[p] as usize..offsets[p + 1] as usize];
        if kids.len() < 2 {
            continue;
        }
        let mut seen: HashMap<[u32; 2], ()> = HashMap::with_capacity(kids.len());
        for &child in kids {
            if seen.insert(halves[child as usize], ()).is_some() {
                alike[child as usize] = true;
            }
        }
    }
    drop(listed);
    drop(offsets);
    // Each pool letter's slot (its branch and the bin of its depth), from a label covering it; a
    // letter no label covers has its own slot.
    let uncovered_slot = slots;
    let mut letter_slot = vec![u8::MAX; pool.len()];
    let mut letter_ticks = vec![u32::MAX; pool.len()];
    for i in 0..n {
        let (b, end) = (bottom(i), ends[i] as usize);
        for j in label(i) {
            let t = ticks_of(branch(i), b + 1 + j - end);
            letter_ticks[j] = t as u32;
            letter_slot[j] = (branch(i) * (BINS.len() + 1) + bin_of(t)) as u8;
        }
    }
    let slot_of = |j: usize| {
        if letter_slot[j] == u8::MAX {
            uncovered_slot
        } else {
            usize::from(letter_slot[j])
        }
    };
    // The label bytes a rule releases, by slot: the letters no kept node covers.
    let released_letters = |keep: &dyn Fn(usize) -> bool| -> Vec<u64> {
        let mut cover = vec![0i32; pool.len() + 1];
        for i in 0..n {
            if keep(i) {
                let range = label(i);
                cover[range.start] += 1;
                cover[range.end] -= 1;
            }
        }
        let mut released = vec![0u64; slots + 1];
        let mut running = 0i32;
        for (j, &step) in cover.iter().take(pool.len()).enumerate() {
            running += step;
            if running == 0 {
                released[slot_of(j)] += LETTER_BYTES;
            }
        }
        released
    };
    let uncovered = released_letters(&|_| true);
    let unreached = released_letters(&|i| !boundary[i]);
    let once_letters = released_letters(&|i| arrivals(i) != 1);
    let mut label_total = vec![0u64; slots + 1];
    for j in 0..pool.len() {
        label_total[slot_of(j)] += LETTER_BYTES;
    }
    let mut bins = [[Bin::default(); BINS.len() + 1]; 2];
    for i in 0..n {
        let b = branch(i);
        let bin = &mut bins[b][bin_of(ticks_of(b, bottom(i)))];
        bin.nodes += 1;
        bin.node_bytes += own(i);
        bin.readings += READING_BYTES;
        if boundary[i] {
            bin.boundary += own(i);
        }
        if arrivals(i) == 1 {
            bin.once_nodes += 1;
            bin.once += own(i);
        }
        if alike[i] {
            bin.alike += NODE_BYTES;
        }
    }
    for (b, row) in bins.iter_mut().enumerate() {
        for (k, bin) in row.iter_mut().enumerate() {
            bin.label_bytes = label_total[b * (BINS.len() + 1) + k];
        }
    }
    let encoded = tree.encode_standing().len() as u64;
    let node_bytes: u64 = bins.iter().flatten().map(|bin| bin.node_bytes).sum();
    let letters = LETTER_BYTES * pool.len() as u64;
    println!(
        "  {name}: {n} stored nodes and {} pool letters; branch depths {depths:?} letters, a bundle tick {per_tick} letters; its standing encodes to {encoded} bytes ({} a cell, remainder {}): nodes {node_bytes}, labels {letters}, roots, joins and header {}",
        pool.len(),
        encoded / cells,
        encoded % cells,
        encoded - node_bytes - letters
    );
    println!(
        "    by branch and bottom depth: nodes | node bytes | label bytes | E0 readings | E1 boundary, nodes + labels | L2 once-reached nodes, bytes + labels | refused: alike siblings' registers"
    );
    for (b, row) in bins.iter().enumerate() {
        for (k, bin) in row.iter().enumerate() {
            if bin.nodes == 0 && bin.label_bytes == 0 {
                continue;
            }
            let slot = b * (BINS.len() + 1) + k;
            println!(
                "    {} {}: {} | {} | {} | {} | {} + {} | {}, {} + {} | {}",
                ["cells", "bundles"][b],
                bin_name(k),
                bin.nodes,
                bin.node_bytes,
                bin.label_bytes,
                bin.readings,
                bin.boundary,
                unreached[slot] - uncovered[slot],
                bin.once_nodes,
                bin.once,
                once_letters[slot] - uncovered[slot],
                bin.alike
            );
        }
    }
    let total = |f: &dyn Fn(&Bin) -> u64| -> u64 { bins.iter().flatten().map(f).sum() };
    let covered = |v: &[u64]| -> u64 { v[..slots].iter().sum::<u64>() };
    let covered_uncovered = covered(&uncovered);
    let rule = |label: &str, bytes: u64| {
        println!(
            "    {label}: {bytes} bytes ({} a cell, remainder {}) of {encoded}",
            bytes / cells,
            bytes % cells
        );
    };
    println!(
        "    exact for the declared receiver (the prequential face at every admitted future, deposits included):"
    );
    rule(
        "E0 the chart's readings beside the state (certificates, cached stop weight, rebase count)",
        total(&|bin| bin.readings),
    );
    rule(
        "E1 the boundary contexts, which no continuing address reaches (nodes, and the labels only they cover)",
        total(&|bin| bin.boundary) + covered(&unreached) - covered_uncovered,
    );
    rule("E2 nodes past the admitted depth (none are founded)", 0);
    rule(
        "E3 pool letters no label reads (a split's key letter, kept where the chain held it)",
        uncovered[uncovered_slot] + covered_uncovered,
    );
    println!(
        "    charged coarsenings (a declared coarser receiver priced by its code-length pair; not retention):"
    );
    rule(
        "L2 once-reached nodes (leaf chains one arrival founded), and the labels only they cover",
        total(&|bin| bin.once) + covered(&once_letters) - covered_uncovered,
    );
    for &cap in &BINS {
        let nodes: u64 = (0..n)
            .filter(|&i| ticks_of(branch(i), top(i)) > cap)
            .map(own)
            .sum();
        let deep_letters = LETTER_BYTES
            * letter_ticks
                .iter()
                .filter(|&&t| t != u32::MAX && t as usize > cap)
                .count() as u64;
        rule(
            &format!(
                "L1 the depth cut at {cap} ticks (the nodes whose top lies deeper, and every label letter deeper)"
            ),
            nodes + deep_letters,
        );
    }
    println!("    refused (not future-sufficient):");
    rule(
        "siblings with equal present counts merged into one register",
        total(&|bin| bin.alike),
    );
}

/// **U2's read-only standing census** (module header).
pub fn standing_census(curated_path: &str) {
    let clock = Instant::now();
    let chart = SectionChart::curated();
    let cut = read_curated(curated_path, &chart);
    let development = cut.held.start;
    let relations = read_incidence(curated_path);
    let (partition, receipt) =
        learn_hazard_partition(chart, &cut.codes[..development]).expect("the learned partition");
    let classes_only = HazardPartition::learned(
        partition.classes().to_vec(),
        std::collections::BTreeMap::new(),
    )
    .expect("the learned classes");
    let other = if receipt.shares_adopted {
        ("learned classes without shares", classes_only)
    } else {
        (
            "learned classes with the refused shares",
            receipt.shared.clone(),
        )
    };
    let comparisons = vec![
        ("declared".to_string(), HazardPartition::declared()),
        (other.0.to_string(), other.1),
    ];
    let mut egg = admitted_egg(
        chart,
        cut.population,
        super::GRAIN,
        partition,
        relations,
        &comparisons,
        0,
    )
    .expect("the admitted egg");
    println!(
        "hnn_population f0-census: U2's standing census of the admitted egg on F4's development passage ({} cells, the first {development} the choosing families); setup {} ms",
        cut.codes.len(),
        clock.elapsed().as_millis()
    );
    let census = |egg: &AdmittedEgg, cells: u64, part: &str| {
        let whole = egg
            .admitted_checkpoint()
            .expect("the admitted egg's checkpoint")
            .expect("an encodable standing")
            .len() as u64;
        println!(
            "{part}: the egg's standing {whole} bytes after {cells} cells ({} a cell, remainder {}); resident set (now, peak) {:?} bytes",
            whole / cells,
            whole % cells,
            resident_set()
        );
        tree_census(
            egg.inner().byte_tree().tree(),
            "its byte tree (typed, the channel slot)",
            cells,
        );
    };
    let passage = Instant::now();
    for &cell in &cut.codes[..development] {
        Family::receive(&mut egg, cell).expect("a choosing cell");
    }
    println!(
        "the choosing families read in {} ms",
        passage.elapsed().as_millis()
    );
    census(&egg, development as u64, "1. after the choosing families");
    let passage = Instant::now();
    for &cell in &cut.codes[development..] {
        Family::receive(&mut egg, cell).expect("a validation cell");
    }
    println!(
        "the validation families read in {} ms",
        passage.elapsed().as_millis()
    );
    census(&egg, cut.codes.len() as u64, "2. after the whole passage");
    println!(
        "wall time in all: {} ms; resident set (now, peak) {:?} bytes",
        clock.elapsed().as_millis(),
        resident_set()
    );
}

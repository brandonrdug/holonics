//! **The landmark tree on the card, stored at the faces where paths part** (campaign 2, stored where
//! paths part, with the register's capacity; #73 with #76; `kernels/tree.cu`).
//!
//! [definition] The receiving parametron's storage, the tree of landmarks
//! (`holonics::compression::landmark::context::Landmarks`), mirrored on the card with the host's exact integer law.
//! The computational object is the helical pair interaction; of the winding guide's objects this
//! realization touches the receiving face (faces and placement: the dyadic digit faces it returns
//! as splits) and the tower thread (the context depth as a restriction chain: a stored chain is a
//! unique gluing, a parting face a plural one), and the helix twice: the β chart's carry and each
//! node's count register carrying at its declared capacity (the register's capacity); the edge ratios of each
//! opened path (the pair) are kept attached. The host's constitution owns the tree and its
//! certificates; the card carries what the reads need, the masses, each node's and each join's
//! `(β, λ̂)`, the topology and the labels, and moves it by the same deposits in the same order.
//!
//! | On the card | On the host |
//! |---|---|
//! | the all-class read: at each splitting dyadic cell, each branch's walk (each stored chain's label compared to the address letter by letter), a parting chain's upper part at its split ratio, the opened path's faces and the join (`hnn_tree_splits`) | the class faces from the splits (`LandmarkFace::of_splits`: the products down the dyadic heap and the grain exponents, whose certified logarithm reads integers past the card's words) |
//! | the opened-path update of each deposit (`hnn_tree_deposit`): the label runs, the β steps with the carrier's rebase, a parting chain's split (both ratios formed exactly and carried at `W` bits), the upper parts and leaves founded at the host's numbers, the relinks, the masses and each register's carry at the declared ceiling (`tree_carry`) | the certificates (the host's tree, `Constitution::deposited`); the ceiling in half-units (`Capacity::ceiling_halves`) |
//! | a window's phases in cell order: the earlier phases' deposits applied with an undo log, the later phase read, the log undone (`hnn_tree_undo`) | the addresses' letters (`LandmarkDeclaration::letters`), the digits each target opens, each branch's summed rungs (`LandmarkDeclaration::rung_sums`) and founding charts (`ArenaView::founding`) |
//!
//! [definition; agent-inferred] **The layout** (the compacted arena, `compression::landmark::context`'s "The arena"):
//! per node its depth word (the bottom depth, the branch in the top bit), its label end, its two
//! half-unit masses and its chart `(β_n, β_d, β_e, λ̂)`, 48 bytes a node; the child table at twice
//! the nodes' capacity, a power of two, 12 bytes a slot (`(parent << 32) | letter` and the child);
//! the label pool, 4 bytes a letter; each join's chart; the counts `(nodes, letters)`. The capacity
//! is the a-priori bound (`compacted_node_bound`): a passage of `n` cells founds at most `2 n B`
//! nodes a branch and holds at most `n D_b` letters, at the declared population plus a window.
//!
//! [definition; agent-inferred] **The register's capacity** (`context::Capacity`;
//! Lean `Compression/Landmark/Context/Capacity.{capCarry, cap_carry_half_units, capped_tree_laws}`). The law's words
//! carry the ceiling in half-units, `2L + 2 = 2^(c+1) + 2` (`u64::MAX` when no total reaches it:
//! `c = ∞` is the KT node), read from the host's declaration; the layout is unchanged. The
//! carry acts where the host's `Law::apply_branch` places it: in the deposit, at every node of the
//! opened path past the forced depths, right after the node's mass of the digit grows, `h_0 + h_1
//! ≥ 2L + 2` carries each `h ← 2⌊(h + 1)/4⌋ + 1`, so the next read (the window's next phase, or
//! the next cell) meets the carried counts. A stored chain is one register; a parting chain's upper
//! part is founded with the chain's register as carried so far, then counts and carries as any
//! node; the lower part is not reached and keeps its register. The undo log holds the masses from
//! before the count, so a window's undo restores the pre-carry register.
//!
//! [definition; agent-inferred] **The realization** (the hardware law, CLAUDE.md). The read is one
//! block per phase with one thread per splitting dyadic cell (`threads` the least power of two
//! covering them, at least a warp, within the entry's and the device's limits): each thread walks its
//! dyadic cell's trees serially (at most `D_b + 1` stored chains, `D_b` letters compared and one
//! split a branch), reads the shared immutable arena and writes its own split, so the regions
//! commute. The update is one block of one warp, a thread per opened digit: the digits of one cell
//! descend different dyadic cells, so they write disjoint trees, nodes, slots and joins; their
//! insertions take distinct keys by `atomicCAS`; their founded numbers are the host's, by a block
//! prefix sum in the host's founding order (digit, then branch, an upper part before a leaf); the
//! label runs are the block's (each branch's least leaf top a block minimum, the letters copied by
//! every thread into disjoint positions). A split's ratios are formed on 512-bit integers within
//! the thread (`5W + 3S + 5` bits, the declaration refused past them). The tree's launches run on
//! the tree's own stream: they read and write only the tree's buffers, disjoint from the word's, so
//! they commute with the word's launches on the card's stream. Every transfer is timed apart from
//! the launches ([`TreeTimes`]).
//!
//! [definition] **Parity** (`src/hnn/tests.rs`, `port_tests.rs`): the card's splits equal the host's
//! (`hnn::receiving::window_splits` over `Landmarks::window`) exactly, window by window, on the cell-only and the enlarged tree,
//! at depths past the stream's recurrence and under declared stop priors, unbounded and at ceilings
//! `c ∈ {1, 2, 3}` where the registers carry and chains holding carried registers split, and after
//! every deposit the card's arena (roots, children, depth words, label ends, masses, charts, joins,
//! labels) equals the host's ([`CardTree::agrees`]); the card's split equals `context::Beta::split`
//! ([`split_ratios`]). In the port's lockstep every deposit is checked at the nodes it wrote and
//! founded and at its joins ([`CardTree::agrees_at`]: their masses, `β`, stop weights, depth words
//! and label ends, gathered by `hnn_tree_gather`), and at the labels it held.

use core::ffi::c_void;
use std::time::{Duration, Instant};

use holonics::compression::landmark::context::{
    ArenaView, ChartWords, LandmarkDeclaration, Landmarks, Letter, Splits, Widths,
};
use holonics::hnn::HnnError;

use crate::cuda::{Dim3, Module, Stream};
use crate::ffi::CUdeviceptr;
use crate::hnn::DeviceError;
use crate::hnn::card::{Card, CardBuffer};

/// The tree's kernels, their own translation unit (`build.rs`).
const IMAGE: &[u8] = include_bytes!(concat!(env!("OUT_DIR"), "/tree.ptx"));

/// An unfounded root, or no child.
const NONE: u32 = u32::MAX;

/// A free slot of the child table.
const EMPTY: u64 = u64::MAX;

/// The deepest branch the kernels' paths hold (`TREE_MAX_DEPTH`).
const MAX_DEPTH: usize = 64;

/// The digits one deposit launch opens at most (`TREE_MAX_DIGITS`: one warp).
const MAX_DIGITS: usize = 32;

/// The split's integers, in bits (`BIG_LIMBS` 64-bit limbs).
const SPLIT_BITS: u64 = 512;

/// The undo log's slots a digit inserts, relinks and roots at most (`LOG_SLOTS`, `LOG_RELINKS`,
/// `LOG_ROOTS`: per branch an upper part's lower link and a leaf; a relinked parent; a root).
const LOG_SLOTS: usize = 4;
const LOG_RELINKS: usize = 2;
const LOG_ROOTS: usize = 2;

/// One chart as the card holds it (`TreeChart`).
#[repr(C)]
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
struct TreeChart {
    numerator: u64,
    denominator: u64,
    exponent: i64,
    stop: u64,
}

impl From<ChartWords> for TreeChart {
    fn from(words: ChartWords) -> Self {
        Self {
            numerator: words.numerator,
            denominator: words.denominator,
            exponent: words.exponent,
            stop: words.stop,
        }
    }
}

/// The law's words as the kernels read them (`TreeLaw`).
#[repr(C)]
#[derive(Clone, Copy, Debug)]
struct TreeLaw {
    table_mask: u64,
    ceiling: u64,
    face: u32,
    carrier: u32,
    rebase: u32,
    branches: u32,
    depth0: u32,
    depth1: u32,
    forced0: u32,
    forced1: u32,
    cells: u32,
    stride: u32,
    log_stride: u32,
    sums_stride: u32,
    unit: u32,
}

/// The arena's device pointers (`TreeArena`).
#[repr(C)]
#[derive(Clone, Copy, Debug)]
struct TreeArena {
    roots: CUdeviceptr,
    keys: CUdeviceptr,
    values: CUdeviceptr,
    words: CUdeviceptr,
    ends: CUdeviceptr,
    halves: CUdeviceptr,
    charts: CUdeviceptr,
    joins: CUdeviceptr,
    pool: CUdeviceptr,
    counts: CUdeviceptr,
    sums: CUdeviceptr,
    founding: CUdeviceptr,
}

/// The undo log's device pointers (`TreeLog`).
#[repr(C)]
#[derive(Clone, Copy, Debug)]
struct TreeLog {
    nodes: CUdeviceptr,
    halves: CUdeviceptr,
    charts: CUdeviceptr,
    slots: CUdeviceptr,
    relinked: CUdeviceptr,
    children: CUdeviceptr,
    trees: CUdeviceptr,
    roots: CUdeviceptr,
    joins: CUdeviceptr,
    counts: CUdeviceptr,
}

/// One undo log's buffers.
struct LogBuffers<'c> {
    nodes: CardBuffer<'c, u32>,
    halves: CardBuffer<'c, u32>,
    charts: CardBuffer<'c, TreeChart>,
    slots: CardBuffer<'c, u64>,
    relinked: CardBuffer<'c, u64>,
    children: CardBuffer<'c, u32>,
    trees: CardBuffer<'c, u32>,
    roots: CardBuffer<'c, u32>,
    joins: CardBuffer<'c, TreeChart>,
    counts: CardBuffer<'c, u32>,
}

impl LogBuffers<'_> {
    fn pointers(&self) -> TreeLog {
        TreeLog {
            nodes: self.nodes.device_ptr(),
            halves: self.halves.device_ptr(),
            charts: self.charts.device_ptr(),
            slots: self.slots.device_ptr(),
            relinked: self.relinked.device_ptr(),
            children: self.children.device_ptr(),
            trees: self.trees.device_ptr(),
            roots: self.roots.device_ptr(),
            joins: self.joins.device_ptr(),
            counts: self.counts.device_ptr(),
        }
    }
}

/// [definition] **The tree's wall time by part** (exterior; no law reads it): the transfers (the
/// letters and digits up, the splits and the parity reads down), the card's reads (the launches to
/// their completion), the host's completion of the class faces from the splits, the combined faces
/// formed at the grain (wave plus tree), and the deposits' updates; with the phases read and the
/// cells deposited.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct TreeTimes {
    pub transfer: Duration,
    pub read: Duration,
    pub complete: Duration,
    pub combine: Duration,
    pub deposit: Duration,
    pub reads: u64,
    pub deposits: u64,
}

/// `(key, child)` placed in an open-addressing table of `2^k` slots by linear probing, with the
/// kernels' hash.
fn hash(key: u64) -> u64 {
    let mut z = key.wrapping_add(0x9E37_79B9_7F4A_7C15);
    z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
    z ^ (z >> 31)
}

fn table(children: &[(u64, u32)], slots: usize) -> (Vec<u64>, Vec<u32>) {
    let mask = slots as u64 - 1;
    let (mut keys, mut values) = (vec![EMPTY; slots], vec![NONE; slots]);
    for &(key, child) in children {
        let mut slot = hash(key) & mask;
        while keys[slot as usize] != EMPTY {
            slot = (slot + 1) & mask;
        }
        keys[slot as usize] = key;
        values[slot as usize] = child;
    }
    (keys, values)
}

fn launch_error(clause: &'static str) -> DeviceError {
    DeviceError::Launch {
        entry: "hnn_tree",
        clause,
    }
}

/// [definition] **The landmark tree mirrored on the card** (module header).
pub struct CardTree<'c> {
    card: &'c Card,
    module: Module,
    stream: Stream,
    declaration: LandmarkDeclaration,
    law: TreeLaw,
    splitting: Vec<usize>,
    splitting_buffer: CardBuffer<'c, u32>,
    capacity: usize,
    pool_capacity: usize,
    per_cell: usize,
    per_cell_letters: usize,
    roots: CardBuffer<'c, u32>,
    keys: CardBuffer<'c, u64>,
    values: CardBuffer<'c, u32>,
    words: CardBuffer<'c, u32>,
    ends: CardBuffer<'c, u32>,
    halves: CardBuffer<'c, u32>,
    charts: CardBuffer<'c, TreeChart>,
    joins: CardBuffer<'c, TreeChart>,
    pool: CardBuffer<'c, u32>,
    counts: CardBuffer<'c, u32>,
    sums: CardBuffer<'c, u32>,
    founding: CardBuffer<'c, TreeChart>,
    letters: CardBuffer<'c, u32>,
    digits: CardBuffer<'c, u32>,
    out: CardBuffer<'c, u64>,
    logs: Vec<LogBuffers<'c>>,
    /// The per-deposit lockstep's gather: the touched nodes and dyadic cells up, their masses,
    /// charts, depth words and label ends and the joins' charts down (`hnn_tree_gather`).
    gather: GatherBuffers<'c>,
    nodes: usize,
    held: usize,
    times: TreeTimes,
    read_threads: u32,
}

/// The per-deposit lockstep's gather buffers, sized for the touched nodes and joins of one deposit
/// of a window's cells.
struct GatherBuffers<'c> {
    nodes: CardBuffer<'c, u32>,
    dyadic: CardBuffer<'c, u32>,
    halves: CardBuffer<'c, u32>,
    charts: CardBuffer<'c, TreeChart>,
    words: CardBuffer<'c, u32>,
    joins: CardBuffer<'c, TreeChart>,
    capacity: usize,
}

impl Drop for CardTree<'_> {
    fn drop(&mut self) {
        // The module and the stream are released in the card's context.
        let _ = self.card.current();
    }
}

impl<'c> CardTree<'c> {
    /// **Mirror a host tree on the card**: its law's words, its branches' summed rungs and its
    /// founding charts, the arena at its current standing, and room for every node and label
    /// letter a passage of the declared population founds (`2B` nodes and `D_b` letters a branch a
    /// cell, the compacted tree's bound), plus `window` cells a window's overlay and a re-read found past
    /// it; the child table at twice the nodes, a power of two. Refused at a branch deeper than the
    /// kernels' paths, at widths past the kernel's single-division operands
    /// (`Widths::single_division_admitted`), or at a split whose integers pass 512 bits
    /// (`5W + 3S + 5`, `S` a branch's summed rung to its depth).
    pub fn mirror(card: &'c Card, tree: &Landmarks, window: usize) -> Result<Self, DeviceError> {
        let declaration = tree.declaration().clone();
        let widths: Widths = tree.widths();
        // The kernel mixes and weighs by single divisions: widths past their `u128` operands
        // (the host's split operands declare wider trees, the wide cut) are refused here.
        if !widths.single_division_admitted(declaration.population) {
            return Err(launch_error(
                "widths whose single-division operands fit u128 (2M + κ + 3 and 2W + M + 3 bits)",
            ));
        }
        let depths = declaration.branch_depths();
        if depths.iter().any(|&depth| depth + 1 > MAX_DEPTH) || depths.len() > 2 {
            return Err(launch_error(
                "a branch within the kernels' path of 64 nodes",
            ));
        }
        let sums = declaration.rung_sums();
        let widest = sums
            .iter()
            .map(|branch| branch.last().copied().unwrap_or(0))
            .max()
            .unwrap_or(0);
        if 5 * widths.carrier + 3 * widest + 5 >= SPLIT_BITS {
            return Err(launch_error(
                "a split whose integers fit 512 bits (5W + 3S + 5)",
            ));
        }
        let digits = widths.digits as usize;
        if digits > MAX_DIGITS {
            return Err(launch_error("a cell of at most 32 odometer digits"));
        }
        let per_cell = 2 * digits * depths.len();
        let per_cell_letters: usize = depths.iter().sum();
        let cells_passed = declaration.population as usize + window + 1;
        let capacity = cells_passed * per_cell;
        let pool_capacity = cells_passed * per_cell_letters;
        let slots = (2 * capacity).next_power_of_two().max(64);
        let stride = depths.iter().copied().max().unwrap_or(1).max(1);
        let log_stride = depths.iter().map(|d| d + 1).sum::<usize>().max(1);
        let sums_stride = stride + 1;
        let cells = 1usize << digits;
        let law = TreeLaw {
            table_mask: slots as u64 - 1,
            ceiling: declaration.capacity.ceiling_halves().unwrap_or(u64::MAX),
            face: widths.face as u32,
            carrier: widths.carrier as u32,
            rebase: widths.rebase as u32,
            branches: depths.len() as u32,
            depth0: depths[0] as u32,
            depth1: depths.get(1).copied().unwrap_or(0) as u32,
            forced0: declaration.forced as u32,
            forced1: 0,
            cells: cells as u32,
            stride: stride as u32,
            log_stride: log_stride as u32,
            sums_stride: sums_stride as u32,
            unit: 1u32 << declaration.mass,
        };
        let mut sum_words = vec![0u32; depths.len() * sums_stride];
        for (branch, branch_sums) in sums.iter().enumerate() {
            for (depth, &sum) in branch_sums.iter().enumerate() {
                sum_words[branch * sums_stride + depth] =
                    u32::try_from(sum).map_err(|_| launch_error("summed rungs within 32 bits"))?;
            }
        }
        let arena = tree.arena();
        let founding: Vec<TreeChart> = (0..=stride)
            .map(|depth| arena.founding(depth).map(TreeChart::from))
            .collect::<Option<_>>()
            .ok_or(launch_error("a founding chart at every depth"))?;
        card.current()?;
        let module = Module::load_ptx(IMAGE)?;
        let stream = Stream::create()?;
        let splitting = declaration.splitting();
        let splitting_words: Vec<u32> = splitting.iter().map(|&h| h as u32).collect();
        let entry = module.function("hnn_tree_splits")?;
        let ceiling = entry.max_threads_per_block()?;
        let covering = (splitting.len() as u32).next_power_of_two().max(32);
        let read_threads = covering
            .min(ceiling)
            .min(card.census().max_threads_per_block);
        let window_phases = window.max(1) + 1;
        let log = |card: &'c Card| -> Result<LogBuffers<'c>, DeviceError> {
            let entries = MAX_DIGITS * log_stride;
            Ok(LogBuffers {
                nodes: card.alloc(entries)?,
                halves: card.alloc(2 * entries)?,
                charts: card.alloc(entries)?,
                slots: card.alloc(MAX_DIGITS * LOG_SLOTS)?,
                relinked: card.alloc(MAX_DIGITS * LOG_RELINKS)?,
                children: card.alloc(MAX_DIGITS * LOG_RELINKS)?,
                trees: card.alloc(MAX_DIGITS * LOG_ROOTS)?,
                roots: card.alloc(MAX_DIGITS * LOG_ROOTS)?,
                joins: card.alloc(MAX_DIGITS)?,
                counts: card.alloc(4 * MAX_DIGITS + 2)?,
            })
        };
        let logs = (0..window.max(1))
            .map(|_| log(card))
            .collect::<Result<Vec<_>, _>>()?;
        let gathered = window_phases * MAX_DIGITS * (log_stride + depths.len());
        let gather = GatherBuffers {
            nodes: card.alloc(gathered)?,
            dyadic: card.alloc(gathered)?,
            halves: card.alloc(2 * gathered)?,
            charts: card.alloc(gathered)?,
            words: card.alloc(2 * gathered)?,
            joins: card.alloc(gathered)?,
            capacity: gathered,
        };
        let mut mirrored = Self {
            card,
            module,
            stream,
            law,
            splitting_buffer: card.upload(&splitting_words)?,
            splitting,
            capacity,
            pool_capacity,
            per_cell,
            per_cell_letters,
            roots: card.alloc(depths.len() * cells)?,
            keys: card.alloc(slots)?,
            values: card.alloc(slots)?,
            words: card.alloc(capacity)?,
            ends: card.alloc(capacity)?,
            halves: card.alloc(2 * capacity)?,
            charts: card.alloc(capacity)?,
            joins: card.alloc(cells)?,
            pool: card.alloc(pool_capacity)?,
            counts: card.alloc(2)?,
            sums: card.upload(&sum_words)?,
            founding: card.upload(&founding)?,
            letters: card.alloc(window_phases * depths.len() * stride)?,
            digits: card.alloc(window_phases * 2 * MAX_DIGITS)?,
            out: card.alloc(window_phases * declaration.splitting().len().max(1))?,
            logs,
            gather,
            nodes: 0,
            held: 0,
            times: TreeTimes::default(),
            read_threads,
            declaration,
        };
        mirrored.upload(&arena)?;
        Ok(mirrored)
    }

    /// **Upload the host's arena whole** (the mount, or a re-mirror).
    pub fn upload(&mut self, arena: &ArenaView<'_>) -> Result<(), DeviceError> {
        let start = Instant::now();
        let halves = arena.halves();
        let labels = arena.labels();
        if halves.len() > self.capacity || labels.len() > self.pool_capacity {
            return Err(launch_error("a tree within the mirror's capacity"));
        }
        let (keys, values) = table(&arena.children(), self.keys.len());
        let flat: Vec<u32> = halves
            .iter()
            .flat_map(|pair| pair.iter().copied())
            .collect();
        let charts: Vec<TreeChart> = arena.charts().into_iter().map(TreeChart::from).collect();
        let mut joins: Vec<TreeChart> = arena.joins().into_iter().map(TreeChart::from).collect();
        joins.resize(self.law.cells as usize, TreeChart::default());
        self.card.write(&self.roots, 0, &arena.roots())?;
        self.card.write(&self.keys, 0, &keys)?;
        self.card.write(&self.values, 0, &values)?;
        self.card.write(&self.words, 0, arena.words())?;
        self.card.write(&self.ends, 0, arena.ends())?;
        self.card.write(&self.halves, 0, &flat)?;
        self.card.write(&self.charts, 0, &charts)?;
        self.card.write(&self.joins, 0, &joins)?;
        self.card.write(&self.pool, 0, labels)?;
        self.card
            .write(&self.counts, 0, &[halves.len() as u32, labels.len() as u32])?;
        self.nodes = halves.len();
        self.held = labels.len();
        self.times.transfer += start.elapsed();
        Ok(())
    }

    /// The tree's wall time by part since the mirror.
    pub fn times(&self) -> TreeTimes {
        self.times
    }

    /// Add the host's completion and combine times of a read.
    pub fn completed(&mut self, complete: Duration, combine: Duration) {
        self.times.complete += complete;
        self.times.combine += combine;
    }

    /// The stored nodes the host tracks the mirror at.
    pub fn nodes(&self) -> usize {
        self.nodes
    }

    /// The label pool's letters the host tracks the mirror at.
    pub fn held(&self) -> usize {
        self.held
    }

    /// The letters of an address, each branch at the stride.
    fn letter_words(&self, address: &[Letter]) -> Vec<u32> {
        let stride = self.law.stride as usize;
        let mut words = vec![0u32; self.law.branches as usize * stride];
        for (branch, letters) in self.declaration.letters(address).iter().enumerate() {
            words[branch * stride..branch * stride + letters.len()].copy_from_slice(letters);
        }
        words
    }

    /// The digits a class opens, as `(h, b)` words.
    fn digit_words(&self, class: usize) -> Vec<u32> {
        self.declaration
            .emitted(class)
            .into_iter()
            .flat_map(|(h, b)| [h as u32, b as u32])
            .collect()
    }

    /// Refused unless `cells` more deposits fit the mirror.
    fn room(&self, cells: usize) -> Result<(), DeviceError> {
        if self.nodes + cells * self.per_cell > self.capacity
            || self.held + cells * self.per_cell_letters > self.pool_capacity
        {
            return Err(launch_error("deposits within the mirror's capacity"));
        }
        Ok(())
    }

    fn arena_pointers(&self) -> TreeArena {
        TreeArena {
            roots: self.roots.device_ptr(),
            keys: self.keys.device_ptr(),
            values: self.values.device_ptr(),
            words: self.words.device_ptr(),
            ends: self.ends.device_ptr(),
            halves: self.halves.device_ptr(),
            charts: self.charts.device_ptr(),
            joins: self.joins.device_ptr(),
            pool: self.pool.device_ptr(),
            counts: self.counts.device_ptr(),
            sums: self.sums.device_ptr(),
            founding: self.founding.device_ptr(),
        }
    }

    fn launch(
        &self,
        entry: &'static str,
        grid: u32,
        block: u32,
        params: &mut [*mut c_void],
    ) -> Result<(), DeviceError> {
        self.card.current()?;
        let function = self.module.function(entry)?;
        function.launch_on_shared(
            &self.stream,
            Dim3 {
                x: grid,
                y: 1,
                z: 1,
            },
            Dim3 {
                x: block,
                y: 1,
                z: 1,
            },
            0,
            params,
        )?;
        Ok(())
    }

    /// Launch the read of `phases` phases whose letters start at phase `from` of the letters
    /// buffer, into the output at the same phases.
    fn launch_read(&self, from: usize, phases: usize) -> Result<(), DeviceError> {
        let mut law = self.law;
        let mut arena = self.arena_pointers();
        let mut splitting = self.splitting_buffer.device_ptr();
        let mut count = self.splitting.len() as u32;
        let phase_words = (self.law.branches * self.law.stride) as u64;
        let mut letters = self.letters.device_ptr() + from as u64 * phase_words * 4;
        let mut out = self.out.device_ptr() + (from * self.splitting.len()) as u64 * 8;
        let mut params: [*mut c_void; 6] = [
            (&mut law as *mut TreeLaw).cast(),
            (&mut arena as *mut TreeArena).cast(),
            (&mut splitting as *mut CUdeviceptr).cast(),
            (&mut count as *mut u32).cast(),
            (&mut letters as *mut CUdeviceptr).cast(),
            (&mut out as *mut CUdeviceptr).cast(),
        ];
        self.launch(
            "hnn_tree_splits",
            phases as u32,
            self.read_threads,
            &mut params,
        )
    }

    /// Launch one cell's deposit at phase `phase` of the letters and digits buffers, logging into
    /// `log` when given.
    fn launch_deposit(
        &self,
        phase: usize,
        digits: usize,
        log: Option<&LogBuffers<'c>>,
    ) -> Result<(), DeviceError> {
        let mut law = self.law;
        let mut arena = self.arena_pointers();
        let phase_words = (self.law.branches * self.law.stride) as u64;
        let mut letters = self.letters.device_ptr() + phase as u64 * phase_words * 4;
        let mut digit_words = self.digits.device_ptr() + (phase * 2 * MAX_DIGITS) as u64 * 4;
        let mut count = digits as u32;
        let mut pointers = log.map_or(
            TreeLog {
                nodes: 0,
                halves: 0,
                charts: 0,
                slots: 0,
                relinked: 0,
                children: 0,
                trees: 0,
                roots: 0,
                joins: 0,
                counts: 0,
            },
            LogBuffers::pointers,
        );
        let mut logging = u32::from(log.is_some());
        let mut params: [*mut c_void; 7] = [
            (&mut law as *mut TreeLaw).cast(),
            (&mut arena as *mut TreeArena).cast(),
            (&mut letters as *mut CUdeviceptr).cast(),
            (&mut digit_words as *mut CUdeviceptr).cast(),
            (&mut count as *mut u32).cast(),
            (&mut pointers as *mut TreeLog).cast(),
            (&mut logging as *mut u32).cast(),
        ];
        self.launch("hnn_tree_deposit", 1, MAX_DIGITS as u32, &mut params)
    }

    /// Launch the undo of one logged deposit at phase `phase` of the digits buffer.
    fn launch_undo(
        &self,
        phase: usize,
        digits: usize,
        log: &LogBuffers<'c>,
    ) -> Result<(), DeviceError> {
        let mut law = self.law;
        let mut arena = self.arena_pointers();
        let mut digit_words = self.digits.device_ptr() + (phase * 2 * MAX_DIGITS) as u64 * 4;
        let mut count = digits as u32;
        let mut pointers = log.pointers();
        let mut params: [*mut c_void; 5] = [
            (&mut law as *mut TreeLaw).cast(),
            (&mut arena as *mut TreeArena).cast(),
            (&mut digit_words as *mut CUdeviceptr).cast(),
            (&mut count as *mut u32).cast(),
            (&mut pointers as *mut TreeLog).cast(),
        ];
        self.launch("hnn_tree_undo", 1, MAX_DIGITS as u32, &mut params)
    }

    fn synchronize(&self) -> Result<(), DeviceError> {
        self.card.current()?;
        Ok(self.stream.synchronize()?)
    }

    /// **A window's splits in cell order** (`hnn::receiving::window_splits` over `Landmarks::window` on the card): phase `j`'s
    /// splits at `addresses[j]`, read after the deposits of the known earlier phases, each applied
    /// with its undo log; the logs are undone in reverse after the last read, so the mirror is
    /// unchanged. Refused at more phases than the mirror's window, or past its capacity.
    pub fn window_splits(
        &mut self,
        addresses: &[Vec<Letter>],
        known: &[usize],
    ) -> Result<Vec<Splits>, DeviceError> {
        let phases = addresses.len();
        if phases == 0 {
            return Ok(Vec::new());
        }
        let deposits = known.len().min(phases.saturating_sub(1));
        if phases > self.logs.len() + 1 || deposits > self.logs.len() {
            return Err(launch_error("a window within the mirror's phases"));
        }
        self.room(deposits)?;
        let start = Instant::now();
        let letters: Vec<u32> = addresses
            .iter()
            .flat_map(|address| self.letter_words(address))
            .collect();
        self.card.write(&self.letters, 0, &letters)?;
        let mut digit_counts = Vec::with_capacity(deposits);
        if deposits > 0 {
            let mut words = vec![0u32; deposits * 2 * MAX_DIGITS];
            for (phase, &class) in known.iter().take(deposits).enumerate() {
                let digits = self.digit_words(class);
                digit_counts.push(digits.len() / 2);
                words[phase * 2 * MAX_DIGITS..phase * 2 * MAX_DIGITS + digits.len()]
                    .copy_from_slice(&digits);
            }
            self.card.write(&self.digits, 0, &words)?;
        }
        let uploaded = start.elapsed();
        let start = Instant::now();
        self.launch_read(0, 1)?;
        for phase in 1..phases {
            if phase <= deposits {
                self.launch_deposit(
                    phase - 1,
                    digit_counts[phase - 1],
                    Some(&self.logs[phase - 1]),
                )?;
            }
            self.launch_read(phase, 1)?;
        }
        for phase in (0..deposits).rev() {
            self.launch_undo(phase, digit_counts[phase], &self.logs[phase])?;
        }
        self.synchronize()?;
        let read = start.elapsed();
        let start = Instant::now();
        let count = self.splitting.len();
        let words = self.card.fetch_range(&self.out, 0, phases * count)?;
        self.times.transfer += uploaded + start.elapsed();
        self.times.read += read;
        self.times.reads += phases as u64;
        let face_bits = u64::from(self.law.face);
        Ok(words
            .chunks(count.max(1))
            .take(phases)
            .map(|numerators| Splits {
                face_bits,
                numerators: numerators.to_vec(),
            })
            .collect())
    }

    /// **Deposit cells on the mirror** (`Landmarks::deposit`'s opened-path update, in order), as the
    /// host's constitution deposits them. Refused past the mirror's capacity.
    pub fn deposit(&mut self, steps: &[(Vec<Letter>, usize)]) -> Result<(), DeviceError> {
        let window = self.logs.len() + 1;
        for chunk in steps.chunks(window) {
            self.room(chunk.len())?;
            let start = Instant::now();
            let letters: Vec<u32> = chunk
                .iter()
                .flat_map(|(address, _)| self.letter_words(address))
                .collect();
            self.card.write(&self.letters, 0, &letters)?;
            let mut words = vec![0u32; chunk.len() * 2 * MAX_DIGITS];
            let mut counts = Vec::with_capacity(chunk.len());
            for (phase, (_, class)) in chunk.iter().enumerate() {
                let digits = self.digit_words(*class);
                counts.push(digits.len() / 2);
                words[phase * 2 * MAX_DIGITS..phase * 2 * MAX_DIGITS + digits.len()]
                    .copy_from_slice(&digits);
            }
            self.card.write(&self.digits, 0, &words)?;
            let uploaded = start.elapsed();
            let start = Instant::now();
            for (phase, &digits) in counts.iter().enumerate() {
                self.launch_deposit(phase, digits, None)?;
            }
            self.synchronize()?;
            self.times.transfer += uploaded;
            self.times.deposit += start.elapsed();
            self.times.deposits += chunk.len() as u64;
            // The counts bound the next chunk's room.
            let start = Instant::now();
            let counted = self.card.fetch_range(&self.counts, 0, 2)?;
            self.nodes = counted[0] as usize;
            self.held = counted[1] as usize;
            self.times.transfer += start.elapsed();
        }
        Ok(())
    }

    /// **The mirror against the host's arena**: the counts, every root, every child (the table
    /// read back as a map), every node's depth word, label end, masses and chart, every join and
    /// the label pool. A parity reading.
    pub fn agrees(&mut self, tree: &Landmarks) -> Result<bool, DeviceError> {
        self.synchronize()?;
        let start = Instant::now();
        let arena = tree.arena();
        let nodes = arena.halves().len();
        let held = arena.labels().len();
        let counted = self.card.fetch_range(&self.counts, 0, 2)?;
        let mut same =
            counted == [nodes as u32, held as u32] && self.nodes == nodes && self.held == held;
        if same {
            same &= self.card.fetch(&self.roots)? == arena.roots();
            same &= self.card.fetch_range(&self.words, 0, nodes)? == arena.words();
            same &= self.card.fetch_range(&self.ends, 0, nodes)? == arena.ends();
            same &= self.card.fetch_range(&self.pool, 0, held)? == arena.labels();
            let halves = self.card.fetch_range(&self.halves, 0, 2 * nodes)?;
            let flat: Vec<u32> = arena
                .halves()
                .iter()
                .flat_map(|p| p.iter().copied())
                .collect();
            same &= halves == flat;
            let charts = self.card.fetch_range(&self.charts, 0, nodes)?;
            let host: Vec<TreeChart> = arena.charts().into_iter().map(TreeChart::from).collect();
            same &= charts == host;
            let joins = self.card.fetch(&self.joins)?;
            let host_joins: Vec<TreeChart> =
                arena.joins().into_iter().map(TreeChart::from).collect();
            same &= joins[..host_joins.len()] == host_joins[..];
            let keys = self.card.fetch(&self.keys)?;
            let values = self.card.fetch(&self.values)?;
            let mut card_children: Vec<(u64, u32)> = keys
                .iter()
                .zip(&values)
                .filter(|(key, _)| **key != EMPTY)
                .map(|(&key, &child)| (key, child))
                .collect();
            let mut host_children = arena.children();
            card_children.sort_unstable();
            host_children.sort_unstable();
            same &= card_children == host_children;
        }
        self.times.transfer += start.elapsed();
        Ok(same)
    }
}

impl CardTree<'_> {
    /// **The mirror against the host's tree at the nodes and joins a deposit wrote** (the
    /// per-deposit lockstep): the counts, each named node's two masses, its chart (`β` and the
    /// stop weight), its depth word and its label end, and each named join's chart, gathered on the
    /// card in one launch (`hnn_tree_gather`) and compared with the host's; and the label pool from
    /// `labels_from` to its end. Chunked at the gather's capacity. The lockstep names the stored
    /// nodes the deposit's walks opened (`Landmarks::touched`, read before it) and the nodes it
    /// founded.
    pub fn agrees_at(
        &mut self,
        tree: &Landmarks,
        nodes: &[u32],
        dyadic: &[usize],
        labels_from: usize,
    ) -> Result<bool, DeviceError> {
        self.synchronize()?;
        let start = Instant::now();
        let arena = tree.arena();
        let host_nodes = arena.halves().len();
        let host_held = arena.labels().len();
        let counted = self.card.fetch_range(&self.counts, 0, 2)?;
        let mut same = counted == [host_nodes as u32, host_held as u32]
            && self.nodes == host_nodes
            && self.held == host_held
            && labels_from <= host_held;
        if same {
            same &= self
                .card
                .fetch_range(&self.pool, labels_from, host_held - labels_from)?
                == arena.labels()[labels_from..];
        }
        let enlarged = self.law.branches > 1;
        let dyadic: Vec<u32> = if enlarged {
            dyadic.iter().map(|&h| h as u32).collect()
        } else {
            Vec::new()
        };
        let chunks = nodes
            .len()
            .max(dyadic.len())
            .div_ceil(self.gather.capacity.max(1));
        for chunk in 0..chunks {
            if !same {
                break;
            }
            let range = |len: usize| {
                let from = (chunk * self.gather.capacity).min(len);
                from..((chunk + 1) * self.gather.capacity).min(len)
            };
            let (node_chunk, dyadic_chunk) =
                (&nodes[range(nodes.len())], &dyadic[range(dyadic.len())]);
            if node_chunk.iter().any(|&node| node as usize >= host_nodes) {
                return Ok(false);
            }
            if !node_chunk.is_empty() {
                self.card.write(&self.gather.nodes, 0, node_chunk)?;
            }
            if !dyadic_chunk.is_empty() {
                self.card.write(&self.gather.dyadic, 0, dyadic_chunk)?;
            }
            let mut arena_pointers = self.arena_pointers();
            let mut gather_nodes = self.gather.nodes.device_ptr();
            let mut node_count = node_chunk.len() as u32;
            let mut gather_dyadic = self.gather.dyadic.device_ptr();
            let mut dyadic_count = dyadic_chunk.len() as u32;
            let mut out_halves = self.gather.halves.device_ptr();
            let mut out_charts = self.gather.charts.device_ptr();
            let mut out_words = self.gather.words.device_ptr();
            let mut out_joins = self.gather.joins.device_ptr();
            let mut params: [*mut c_void; 9] = [
                (&mut arena_pointers as *mut TreeArena).cast(),
                (&mut gather_nodes as *mut CUdeviceptr).cast(),
                (&mut node_count as *mut u32).cast(),
                (&mut gather_dyadic as *mut CUdeviceptr).cast(),
                (&mut dyadic_count as *mut u32).cast(),
                (&mut out_halves as *mut CUdeviceptr).cast(),
                (&mut out_charts as *mut CUdeviceptr).cast(),
                (&mut out_words as *mut CUdeviceptr).cast(),
                (&mut out_joins as *mut CUdeviceptr).cast(),
            ];
            let threads = node_chunk.len().max(dyadic_chunk.len()) as u32;
            let block = threads.next_power_of_two().clamp(32, 256);
            self.launch(
                "hnn_tree_gather",
                threads.div_ceil(block),
                block,
                &mut params,
            )?;
            self.synchronize()?;
            if !node_chunk.is_empty() {
                let halves = self
                    .card
                    .fetch_range(&self.gather.halves, 0, 2 * node_chunk.len())?;
                let charts = self
                    .card
                    .fetch_range(&self.gather.charts, 0, node_chunk.len())?;
                let words = self
                    .card
                    .fetch_range(&self.gather.words, 0, 2 * node_chunk.len())?;
                for (i, &node) in node_chunk.iter().enumerate() {
                    let at = node as usize;
                    let host = arena.halves()[at];
                    same &= halves[2 * i] == host[0] && halves[2 * i + 1] == host[1];
                    same &= arena.chart(node).map(TreeChart::from) == Some(charts[i]);
                    same &=
                        words[2 * i] == arena.words()[at] && words[2 * i + 1] == arena.ends()[at];
                }
            }
            if !dyadic_chunk.is_empty() {
                let joins = self
                    .card
                    .fetch_range(&self.gather.joins, 0, dyadic_chunk.len())?;
                for (i, &h) in dyadic_chunk.iter().enumerate() {
                    same &= arena.join(h as usize).map(TreeChart::from) == Some(joins[i]);
                }
            }
        }
        self.times.transfer += start.elapsed();
        Ok(same)
    }
}

/// **The card's β steps** on operand pairs `(N, D, e)` at width `W`, rebase `R` and lattice `M`
/// (`hnn_tree_beta_steps`, the kernels' `tree_beta_step`): each step's carried `(β_n, β_d, β_e)`
/// and stop weight, for the parity against `context::Beta::step`.
pub fn beta_steps(
    card: &Card,
    operands: &[(u128, u128, i64)],
    width: u64,
    rebase: u64,
    face: u64,
) -> Result<Vec<(u64, u64, i64, u64)>, DeviceError> {
    card.current()?;
    let module = Module::load_ptx(IMAGE)?;
    let stream = Stream::create()?;
    let words: Vec<u64> = operands
        .iter()
        .flat_map(|&(n, d, _)| [(n >> 64) as u64, n as u64, (d >> 64) as u64, d as u64])
        .collect();
    let exponents: Vec<i64> = operands.iter().map(|&(_, _, e)| e).collect();
    let input = card.upload(&words)?;
    let exponent_buffer = card.upload(&exponents)?;
    let out = card.alloc::<TreeChart>(operands.len())?;
    let (mut a, mut b, mut c) = (
        input.device_ptr(),
        exponent_buffer.device_ptr(),
        out.device_ptr(),
    );
    let mut count = operands.len() as u32;
    let (mut w, mut r, mut m) = (width as u32, rebase as u32, face as u32);
    let mut params: [*mut c_void; 7] = [
        (&mut a as *mut CUdeviceptr).cast(),
        (&mut b as *mut CUdeviceptr).cast(),
        (&mut count as *mut u32).cast(),
        (&mut w as *mut u32).cast(),
        (&mut r as *mut u32).cast(),
        (&mut m as *mut u32).cast(),
        (&mut c as *mut CUdeviceptr).cast(),
    ];
    let threads = 128u32;
    let blocks = (operands.len() as u32).div_ceil(threads).max(1);
    module.function("hnn_tree_beta_steps")?.launch_on_shared(
        &stream,
        Dim3 {
            x: blocks,
            y: 1,
            z: 1,
        },
        Dim3 {
            x: threads,
            y: 1,
            z: 1,
        },
        0,
        &mut params,
    )?;
    stream.synchronize()?;
    let charts = card.fetch(&out)?;
    drop(stream);
    drop(module);
    Ok(charts
        .into_iter()
        .map(|chart| {
            (
                chart.numerator,
                chart.denominator,
                chart.exponent,
                chart.stop,
            )
        })
        .collect())
}

/// One split's carried charts as `(β_n, β_d, β_e, λ̂)`: the upper part's, then the lower part's.
pub type SplitWords = [(u64, u64, i64, u64); 2];

/// **The card's split** on charts `(β_n, β_d, β_e)` with rungs `(S_up, S_low)` at width `W` and
/// lattice `M` (`hnn_tree_split_ratios`, the kernels' `tree_split`): each part's carried ratio and
/// stop weight, for the parity against `context::Beta::split`. Refused past the split's 512-bit
/// integers.
pub fn split_ratios(
    card: &Card,
    charts: &[(u64, u64, i64, u64, u64)],
    width: u64,
    face: u64,
) -> Result<Vec<SplitWords>, DeviceError> {
    if charts
        .iter()
        .any(|&(.., upper, lower)| 5 * width + 3 * (upper + lower) + 5 >= SPLIT_BITS)
    {
        return Err(launch_error(
            "a split whose integers fit 512 bits (5W + 3S + 5)",
        ));
    }
    card.current()?;
    let module = Module::load_ptx(IMAGE)?;
    let stream = Stream::create()?;
    let parts: Vec<u64> = charts.iter().flat_map(|&(n, d, ..)| [n, d]).collect();
    let exponents: Vec<i64> = charts.iter().map(|&(_, _, e, ..)| e).collect();
    let rungs: Vec<u32> = charts
        .iter()
        .flat_map(|&(.., upper, lower)| [upper as u32, lower as u32])
        .collect();
    let input = card.upload(&parts)?;
    let exponent_buffer = card.upload(&exponents)?;
    let rung_buffer = card.upload(&rungs)?;
    let out = card.alloc::<TreeChart>(2 * charts.len())?;
    let (mut a, mut b, mut c, mut o) = (
        input.device_ptr(),
        exponent_buffer.device_ptr(),
        rung_buffer.device_ptr(),
        out.device_ptr(),
    );
    let mut count = charts.len() as u32;
    let (mut w, mut m) = (width as u32, face as u32);
    let mut params: [*mut c_void; 7] = [
        (&mut a as *mut CUdeviceptr).cast(),
        (&mut b as *mut CUdeviceptr).cast(),
        (&mut c as *mut CUdeviceptr).cast(),
        (&mut count as *mut u32).cast(),
        (&mut w as *mut u32).cast(),
        (&mut m as *mut u32).cast(),
        (&mut o as *mut CUdeviceptr).cast(),
    ];
    let threads = 64u32;
    let blocks = (charts.len() as u32).div_ceil(threads).max(1);
    module.function("hnn_tree_split_ratios")?.launch_on_shared(
        &stream,
        Dim3 {
            x: blocks,
            y: 1,
            z: 1,
        },
        Dim3 {
            x: threads,
            y: 1,
            z: 1,
        },
        0,
        &mut params,
    )?;
    stream.synchronize()?;
    let words = card.fetch(&out)?;
    drop(stream);
    drop(module);
    let word = |chart: &TreeChart| {
        (
            chart.numerator,
            chart.denominator,
            chart.exponent,
            chart.stop,
        )
    };
    Ok(words
        .chunks(2)
        .map(|pair| [word(&pair[0]), word(&pair[1])])
        .collect())
}

/// Refused as the host refuses: a device error read as the HNN's.
pub fn refused(error: DeviceError) -> HnnError {
    error.into_hnn()
}

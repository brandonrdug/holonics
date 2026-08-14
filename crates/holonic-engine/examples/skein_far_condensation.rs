//! A far population condensed to a compact realizer, and the exact remainder that departure costs.
//!
//! ## What is open here, and what is not
//!
//! `crates/holonic-engine/src/skein.rs` already implements contextual tangle compression and
//! already returns a certified remainder — `ContextVerdict { before, after, remainder }`, naming
//! which grade moved, by how much in free rank, and which torsion appeared or vanished.
//! `derivation_skein` drives it on 58 classes. **The construction is not open. The scale is.**
//! `CLAUDE.md` §11: the organ *"has never been run where the population is far enough that
//! condensation is required rather than incidental."*
//!
//! §11 names the route, and
//! `research/records/2026-08-06_THE_TREE_CONDENSES_FOR_FREE_THE_REMAINDER_IS_THE_DEPARTURE_FROM_A_FOREST.md`
//! carries it: **spanning-tree interval labelling**. On a tree a depth-first order replaces every
//! node's whole descendant population by a two-word interval, exactly, with an empty remainder.
//! Every non-tree edge forces additional intervals, and that forced population is the remainder.
//!
//! ## What this driver does
//!
//! It runs both halves of that on the same grown material and holds them against each other.
//!
//! ```text
//!   grown circuit  ->  declared incidence  ->  a cone from one net  =  the FAR POPULATION
//!
//!   compact realizer A   the depth-first interval (two words)         -- the record's route
//!   compact realizer B   the single 0-cell at the cone's root         -- what skein reads
//!
//!   remainder A   the additional intervals the non-tree edges force  (counted, exhibited)
//!   remainder B   ContextVerdict::remainder                          (counted, exhibited)
//! ```
//!
//! Realizer B is realizer A at its limit: an interval is a compact stand-in for a subtree, and a
//! point is what a subtree is homotopy equivalent to. Condensing a cone to its root is the same
//! move taken all the way, and it is the one `skein::read_substitution` can read, because a
//! substitution needs two fillings of one hole and an interval is not a filling.
//!
//! ## The falsifier, which is the grade
//!
//! A cone is connected by construction, so `b_1 = |E| - |V| + 1` is its cyclomatic number, which is
//! exactly the count of non-tree edges against **any** spanning tree. Condensing it to its root
//! must therefore return
//!
//! ```text
//!   remainder empty                  <=>   the cone is a forest
//!   -betti_change at grade 1          =    non-tree edge count, exactly
//! ```
//!
//! Three independent computations are held to that one number: a depth-first edge classification,
//! an `|E| - |V| + 1` count, and a Smith normal form over `BigInt` inside `skein`. Nothing in the
//! third knows about the first two.
//!
//! **Once 2-cells are admitted, "forest" is no longer the right word** and the falsifier takes the
//! form it generalizes to. A division face fills a loop, so the departure splits exactly:
//!
//! ```text
//!   betti_1  +  filling_rank(grade 1)  =  cyclomatic
//!   |           |
//!   |           what the faces filled
//!   what survives free
//! ```
//!
//! and the torsion at grade 1 is what the filling could not un-deposit. That identity is checked
//! exactly, and it is a **stronger** statement than the 1-dimensional one because it says where the
//! departure went rather than only how large it was.
//!
//! ## The correction this run returns
//!
//! The 2026-08-06 record's sharpening says the interval remainder *"is zero exactly when the
//! incidence is a forest."* The forward direction holds. **The converse is false**, and the witness
//! is four nodes: `a->b, a->c, a->d, b->d`. It is not a forest — `b_1 = 1` — yet a depth-first walk
//! that offers `a`'s successors in ascending order forces **no** additional interval, while the same
//! walk in descending order forces **one**. So the interval remainder moves with the walk order,
//! which is a receiver coordinate, while skein's remainder does not. That is `CLAUDE.md` §0's fourth
//! lesson firing on the record's own proposal, and it is why the falsifier above is stated on
//! skein's remainder and not on the interval count.
//!
//! `CLAUDE.md` §8 asks a gauge to exhibit its own orbit rather than assume one. The walk order is
//! declared with three members and its orbit is measured and printed at every reading; where the
//! orbit is trivial the run says so rather than reading agreement as evidence.
//!
//! ## Cost
//!
//! `CLAUDE.md` §8: *a cost is measured in work, never in elapsed time; a clock may measure, it may
//! never select.* Nothing here is selected by a clock. Every comparison is on exact integer work
//! vectors — word unions, edge inspections, stored words, entries written, bits written — derived
//! from the material and reproducing bit-for-bit on any machine. Wall-clock is printed beside them,
//! in whole milliseconds, as a measurement that decides nothing.
//!
//! ## What it does not claim
//!
//! No complete set of local relations, no terminating or confluent normal form, no cost improvement
//! for `skein` itself. Brittenham–Hermiller's nonadditivity of unknotting number stands as the named
//! warning carried in `skein.rs`. An invariance verdict is relative to the declared context family
//! and to the invariants read. Nothing here bears on the Hodge conjecture.
//!
//! Run: `cargo run --release -p holonic-engine --example skein_far_condensation`

use std::collections::{BTreeMap, BTreeSet};
use std::time::Instant;

use holonic_engine::algebraic::{
    CausalCellId, CausalChain, ComparativeMultiplicity, GradedCausalComplex,
};
use holonic_engine::causal::EventId;
use holonic_engine::grown_cell::{
    ComplexAperture, NetId, Schedule, found_complex, grow, standard_cells,
};
use holonic_engine::rebase_invariants::{
    PivotRule, ReadingSchedule, RebaseInvariants, ReductionWork, rebase_invariants_with_schedule_on,
};
use holonic_engine::skein::{GradeRemainder, SkeinReading, Substitution, read_substitution};

// ===============================================================================================
// declarations

/// Which cells the reading admits. A receiver aperture, exactly as `grown_cell::primitive_section`
/// is one.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Aperture {
    /// Gate pins only: the primitive circuit graph.
    Conduction,
    /// Every arc, so an instance black box at every lineage level is an edge too. Each of those runs
    /// parallel to the path through its own children, which is where the loops come from.
    Lineage,
    /// Every arc **and** the division faces, whose attaching maps come from the lineage. This is the
    /// aperture in which the departure from a forest can be *discharged* rather than only counted.
    LineageWithFaces,
}

impl Aperture {
    fn name(self) -> &'static str {
        match self {
            Self::Conduction => "conduction",
            Self::Lineage => "lineage",
            Self::LineageWithFaces => "lineage+faces",
        }
    }

    fn admits_arc(self, is_pin: bool) -> bool {
        match self {
            Self::Conduction => is_pin,
            Self::Lineage | Self::LineageWithFaces => true,
        }
    }

    fn admits_faces(self) -> bool {
        matches!(self, Self::LineageWithFaces)
    }
}

/// Which way the cone opens from its root.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Flow {
    Downstream,
    Upstream,
}

impl Flow {
    fn name(self) -> &'static str {
        match self {
            Self::Downstream => "downstream",
            Self::Upstream => "upstream",
        }
    }

    fn reversed(self) -> Self {
        match self {
            Self::Downstream => Self::Upstream,
            Self::Upstream => Self::Downstream,
        }
    }
}

/// The order a depth-first walk offers successors in.
///
/// A gauge. It must not move an invariant, and whether its orbit is non-trivial **on the declared
/// material** is a measurement rather than an assumption — `CLAUDE.md` §8.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum WalkOrder {
    Ascending,
    Descending,
    /// Widest successor first, ties to the smaller identifier. A third point, so agreement between
    /// two is not read as agreement among all.
    WidestFirst,
}

impl WalkOrder {
    const ALL: [Self; 3] = [Self::Ascending, Self::Descending, Self::WidestFirst];

    fn name(self) -> &'static str {
        match self {
            Self::Ascending => "ascending",
            Self::Descending => "descending",
            Self::WidestFirst => "widest-first",
        }
    }
}

/// What the material is declared to be. A wrong declaration is a refusal, not a shrug: this check
/// has already fired once in construction, on `ripple-adder w16`, which was declared cyclic and is
/// a forest.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Expectation {
    /// Cyclomatic zero. The remainder must be empty.
    Forest,
    /// Cyclomatic above zero.
    Cyclic,
}

struct Declaration {
    label: &'static str,
    rule: &'static str,
    material: Vec<usize>,
    aperture: Aperture,
    flow: Flow,
    expectation: Expectation,
}

fn declarations() -> Vec<Declaration> {
    vec![
        Declaration {
            label: "parity-tree w256, conduction",
            rule: "parity-tree",
            material: vec![256],
            aperture: Aperture::Conduction,
            flow: Flow::Upstream,
            expectation: Expectation::Forest,
        },
        Declaration {
            label: "ripple-adder w16, conduction",
            rule: "ripple-adder",
            material: vec![16, 16, 1],
            aperture: Aperture::Conduction,
            flow: Flow::Upstream,
            expectation: Expectation::Forest,
        },
        Declaration {
            label: "brent-kung-adder w4, conduction",
            rule: "brent-kung-adder",
            material: vec![4, 4, 1],
            aperture: Aperture::Conduction,
            flow: Flow::Upstream,
            expectation: Expectation::Cyclic,
        },
        Declaration {
            label: "brent-kung-adder w16, conduction",
            rule: "brent-kung-adder",
            material: vec![16, 16, 1],
            aperture: Aperture::Conduction,
            flow: Flow::Upstream,
            expectation: Expectation::Cyclic,
        },
        Declaration {
            label: "brent-kung-adder w64, conduction",
            rule: "brent-kung-adder",
            material: vec![64, 64, 1],
            aperture: Aperture::Conduction,
            flow: Flow::Upstream,
            expectation: Expectation::Cyclic,
        },
        Declaration {
            label: "brent-kung-adder w64, lineage",
            rule: "brent-kung-adder",
            material: vec![64, 64, 1],
            aperture: Aperture::Lineage,
            flow: Flow::Upstream,
            expectation: Expectation::Cyclic,
        },
        Declaration {
            label: "brent-kung-adder w32, lineage+faces",
            rule: "brent-kung-adder",
            material: vec![32, 32, 1],
            aperture: Aperture::LineageWithFaces,
            flow: Flow::Upstream,
            expectation: Expectation::Cyclic,
        },
        Declaration {
            label: "parity-tree w64, lineage+faces",
            rule: "parity-tree",
            material: vec![64],
            aperture: Aperture::LineageWithFaces,
            flow: Flow::Upstream,
            expectation: Expectation::Cyclic,
        },
    ]
}

// ===============================================================================================
// an incidence, abstracted so grown material and hand-built witnesses feed the same code

/// Nodes carrying 0-cells, arcs carrying 1-cells, and optionally faces carrying 2-cells.
struct Incidence {
    label: String,
    node_cell: Vec<CausalCellId>,
    node_name: Vec<String>,
    /// `(tail, head, 1-cell)`. Parallel arcs are separate entries and are meant to be.
    edges: Vec<(usize, usize, CausalCellId)>,
    /// `(2-cell, the 1-cells its boundary names)`. A face joins a support only when every arc it
    /// attaches to is already there, which is what keeps the support closed.
    faces: Vec<(CausalCellId, BTreeSet<CausalCellId>)>,
    /// Which 1-cells are gate pins. The primitive circuit's own arcs, as against the lineage boxes
    /// laid parallel to them. Carried so a cone can be asked for its conduction sub-incidence
    /// without re-deriving a second cone with a second root.
    pin_cells: BTreeSet<CausalCellId>,
}

impl Incidence {
    fn nodes(&self) -> usize {
        self.node_cell.len()
    }

    fn successors(&self, flow: Flow) -> Vec<Vec<usize>> {
        let mut out = vec![Vec::new(); self.nodes()];
        for (tail, head, _) in &self.edges {
            match flow {
                Flow::Downstream => out[*tail].push(*head),
                Flow::Upstream => out[*head].push(*tail),
            }
        }
        out
    }

    /// The cone from `root` in the declared flow: the nodes it reaches and the arcs that carry it.
    fn cone_with(&self, successors: &[Vec<usize>], root: usize, flow: Flow) -> Cone {
        let mut seen = vec![false; self.nodes()];
        let mut stack = vec![root];
        seen[root] = true;
        while let Some(node) = stack.pop() {
            for next in &successors[node] {
                if !seen[*next] {
                    seen[*next] = true;
                    stack.push(*next);
                }
            }
        }
        let members: Vec<usize> = (0..self.nodes()).filter(|node| seen[*node]).collect();
        let local: BTreeMap<usize, usize> = members
            .iter()
            .enumerate()
            .map(|(index, node)| (*node, index))
            .collect();
        // An arc belongs to the cone when its source *in the flow* is in the cone; its target then
        // is too, which is what makes the support closed under boundary.
        let mut edges = Vec::new();
        for (tail, head, cell) in &self.edges {
            let (from, to) = match flow {
                Flow::Downstream => (*tail, *head),
                Flow::Upstream => (*head, *tail),
            };
            if seen[from] {
                edges.push((local[&from], local[&to], *cell));
            }
        }
        Cone {
            root: local[&root],
            members,
            edges,
        }
    }

    fn cone(&self, root: usize, flow: Flow) -> Cone {
        self.cone_with(&self.successors(flow), root, flow)
    }

    fn close_with_faces(&self, mut support: BTreeSet<CausalCellId>) -> BTreeSet<CausalCellId> {
        let arcs: BTreeSet<CausalCellId> = support.iter().copied().collect();
        for (face, attaches) in &self.faces {
            if attaches.is_subset(&arcs) {
                support.insert(*face);
            }
        }
        support
    }

    fn cone_support(&self, cone: &Cone) -> BTreeSet<CausalCellId> {
        let mut support: BTreeSet<CausalCellId> = cone
            .members
            .iter()
            .map(|node| self.node_cell[*node])
            .collect();
        for (_, _, cell) in &cone.edges {
            support.insert(*cell);
        }
        self.close_with_faces(support)
    }

    /// The sub-incidence induced on a node set: every arc with **both** ends inside.
    fn induced_support(&self, nodes: &BTreeSet<usize>) -> BTreeSet<CausalCellId> {
        let mut support: BTreeSet<CausalCellId> =
            nodes.iter().map(|node| self.node_cell[*node]).collect();
        for (tail, head, cell) in &self.edges {
            if nodes.contains(tail) && nodes.contains(head) {
                support.insert(*cell);
            }
        }
        self.close_with_faces(support)
    }
}

/// A far population: the nodes a cone holds, in cone-local indices, and the arcs among them.
struct Cone {
    root: usize,
    /// cone-local index -> incidence index.
    members: Vec<usize>,
    /// `(local tail, local head, 1-cell)`, **in flow direction**.
    edges: Vec<(usize, usize, CausalCellId)>,
}

impl Cone {
    fn size(&self) -> usize {
        self.members.len()
    }

    /// `|E| - |V| + 1`. A cone is connected by construction, so this is `b_1` of its 1-skeleton and
    /// it is exactly the number of non-tree edges against any spanning tree.
    fn cyclomatic(&self) -> i64 {
        self.edges.len() as i64 - self.members.len() as i64 + 1
    }

    /// The same count over the gate pins alone: the departure the *primitive circuit* carries,
    /// with the lineage boxes laid parallel to it removed.
    fn conduction_cyclomatic(&self, pins: &BTreeSet<CausalCellId>) -> i64 {
        let carried = self
            .edges
            .iter()
            .filter(|(_, _, cell)| pins.contains(cell))
            .count() as i64;
        carried - self.members.len() as i64 + 1
    }
}

// ===============================================================================================
// exact work, in work

/// What the direct path costs: the complete reachability relation, materialized.
#[derive(Clone, Copy, Debug, Default)]
struct ClosureWork {
    /// 64-bit word unions performed. The dominating operation.
    word_unions: u64,
    /// Words the answer occupies: `|V| * ceil(|V| / 64)`.
    stored_words: u64,
}

/// What the condensed path costs: one depth-first pass and the intervals it forces.
#[derive(Clone, Copy, Debug, Default)]
struct LabelWork {
    /// Arc ends the walk looked at.
    edge_inspections: u64,
    /// Interval endpoints compared during merges.
    merge_comparisons: u64,
    /// Words the answer occupies: two per node, plus two per forced extra interval.
    stored_words: u64,
}

fn sum_reduction_work(schedule: &ReadingSchedule) -> ReductionWork {
    let mut total = ReductionWork::default();
    for (_, pivot) in &schedule.per_grade {
        total.entries_written += pivot.work.entries_written;
        total.written_bits += pivot.work.written_bits;
        total.peak_entry_bits = total.peak_entry_bits.max(pivot.work.peak_entry_bits);
        total.repairs += pivot.work.repairs;
    }
    total
}

// ===============================================================================================
// the direct path: materialize every cone

/// `reach[v]` = every node reachable from `v` inside the cone, as a bitset over cone-local indices.
///
/// Taken in reverse topological order — which is the depth-first finish order — so this is the
/// cheapest honest form of the direct path and not a strawman.
fn transitive_closure(cone: &Cone, finish_order: &[usize]) -> (Vec<Vec<u64>>, ClosureWork) {
    let size = cone.size();
    let words = size.div_ceil(64);
    let mut successors = vec![Vec::new(); size];
    for (tail, head, _) in &cone.edges {
        successors[*tail].push(*head);
    }
    let mut reach = vec![vec![0u64; words]; size];
    let mut work = ClosureWork {
        word_unions: 0,
        stored_words: (size * words) as u64,
    };
    for node in finish_order {
        reach[*node][node / 64] |= 1u64 << (node % 64);
        for position in 0..successors[*node].len() {
            let next = successors[*node][position];
            for word in 0..words {
                let carried = reach[next][word];
                reach[*node][word] |= carried;
                work.word_unions += 1;
            }
        }
    }
    (reach, work)
}

// ===============================================================================================
// the condensed path: a spanning-tree interval labelling and the intervals it forces

struct Labelling {
    /// cone-local node -> depth-first preorder index.
    enter: Vec<usize>,
    /// One past the preorder index of the node's whole tree subtree.
    exit: Vec<usize>,
    /// Depth-first finish order, which is a reverse topological order on a DAG.
    finish_order: Vec<usize>,
    tree_edges: usize,
    non_tree_edges: usize,
    /// The compact realizer, per node: merged half-open intervals in preorder coordinates. Anything
    /// beyond the first was **forced by a non-tree edge**.
    intervals: Vec<Vec<(usize, usize)>>,
    /// `Σ_v (|intervals[v]| - 1)`. The certified remainder of the record's route.
    forced_intervals: usize,
    work: LabelWork,
}

fn merge_intervals(mut spans: Vec<(usize, usize)>, work: &mut LabelWork) -> Vec<(usize, usize)> {
    spans.sort_unstable();
    let mut merged: Vec<(usize, usize)> = Vec::new();
    for span in spans {
        work.merge_comparisons += 1;
        match merged.last_mut() {
            // Half-open and in preorder coordinates, so adjacency coalesces exactly.
            Some(last) if span.0 <= last.1 => {
                if span.1 > last.1 {
                    last.1 = span.1;
                }
            }
            _ => merged.push(span),
        }
    }
    merged
}

fn label(cone: &Cone, order: WalkOrder) -> Labelling {
    let size = cone.size();
    let mut successors: Vec<Vec<usize>> = vec![Vec::new(); size];
    for (tail, head, _) in &cone.edges {
        successors[*tail].push(*head);
    }
    let fanout: Vec<usize> = successors.iter().map(Vec::len).collect();
    for list in &mut successors {
        match order {
            WalkOrder::Ascending => list.sort_unstable(),
            WalkOrder::Descending => list.sort_unstable_by(|left, right| right.cmp(left)),
            WalkOrder::WidestFirst => {
                list.sort_unstable_by_key(|node| (std::cmp::Reverse(fanout[*node]), *node));
            }
        }
    }

    let mut work = LabelWork::default();
    let mut enter = vec![usize::MAX; size];
    let mut exit = vec![usize::MAX; size];
    let mut finish_order = Vec::with_capacity(size);
    let mut tree_edges = 0usize;
    let mut non_tree_edges = 0usize;
    let mut counter = 0usize;

    enter[cone.root] = counter;
    counter += 1;
    let mut stack: Vec<(usize, usize)> = vec![(cone.root, 0)];
    while let Some((node, cursor)) = stack.last().copied() {
        if cursor < successors[node].len() {
            stack.last_mut().expect("the stack is not empty").1 = cursor + 1;
            let next = successors[node][cursor];
            work.edge_inspections += 1;
            if enter[next] == usize::MAX {
                enter[next] = counter;
                counter += 1;
                tree_edges += 1;
                stack.push((next, 0));
            } else {
                non_tree_edges += 1;
            }
        } else {
            stack.pop();
            exit[node] = counter;
            finish_order.push(node);
        }
    }

    // The forced intervals, in reverse topological order so every successor is settled first.
    let mut intervals: Vec<Vec<(usize, usize)>> = vec![Vec::new(); size];
    for node in &finish_order {
        let mut spans = vec![(enter[*node], exit[*node])];
        for position in 0..successors[*node].len() {
            let next = successors[*node][position];
            spans.extend(intervals[next].iter().copied());
        }
        intervals[*node] = merge_intervals(spans, &mut work);
    }
    let forced_intervals: usize = intervals.iter().map(|list| list.len() - 1).sum();
    work.stored_words = 2 * size as u64 + 2 * forced_intervals as u64;

    Labelling {
        enter,
        exit,
        finish_order,
        tree_edges,
        non_tree_edges,
        intervals,
        forced_intervals,
        work,
    }
}

/// The condensation is exact when the intervals answer the reachability family **exactly** — not
/// approximately and not conservatively. Checked node by node against the materialized closure.
fn certify(cone: &Cone, labelling: &Labelling, reach: &[Vec<u64>]) -> Result<(), String> {
    let size = cone.size();
    for node in 0..size {
        let mut from_intervals: BTreeSet<usize> = BTreeSet::new();
        for (start, end) in &labelling.intervals[node] {
            from_intervals.extend(*start..*end);
        }
        let mut from_closure: BTreeSet<usize> = BTreeSet::new();
        for other in 0..size {
            if reach[node][other / 64] >> (other % 64) & 1 == 1 {
                from_closure.insert(labelling.enter[other]);
            }
        }
        if from_intervals != from_closure {
            let missing: Vec<usize> = from_closure.difference(&from_intervals).copied().collect();
            let spurious: Vec<usize> = from_intervals.difference(&from_closure).copied().collect();
            return Err(format!(
                "node at preorder {}: the intervals do not answer the cone exactly. \
                 missing {missing:?}, spurious {spurious:?}",
                labelling.enter[node]
            ));
        }
    }
    Ok(())
}

// ===============================================================================================
// the skein reading

struct Verdicts {
    reading: SkeinReading,
    before_work: ReductionWork,
    after_work: ReductionWork,
    before_cells: usize,
    after_cells: usize,
    wall_milliseconds: u128,
}

/// Condense the cone to its root and read what any receiver in the declared family can still tell.
///
/// `before` is the whole far population. `after` is the single 0-cell at its root — the compact
/// realizer at its limit. Each declared context meets `before` in exactly the shared boundary, so
/// the union is a wedge at a point and the remainder must not move between them.
fn condense(
    complex: &GradedCausalComplex,
    incidence: &Incidence,
    cone: &Cone,
    contexts: &[BTreeSet<CausalCellId>],
    rule: PivotRule,
) -> Result<Verdicts, String> {
    let root_cell = incidence.node_cell[cone.members[cone.root]];
    let before = incidence.cone_support(cone);
    let after = BTreeSet::from([root_cell]);
    let substitution = Substitution {
        boundary: BTreeSet::from([root_cell]),
        before: before.clone(),
        after: after.clone(),
    };

    let clock = Instant::now();
    let reading = read_substitution(complex, &substitution, contexts, rule)
        .map_err(|refusal| format!("skein refused: {refusal}"))?;
    let wall_milliseconds = clock.elapsed().as_millis();

    // The same two readings `read_substitution` performed internally, re-taken with their schedule
    // so what they cost is legible: same function, same rule, same supports, widest context.
    let widest = contexts
        .iter()
        .max_by_key(|context| context.len())
        .cloned()
        .unwrap_or_default();
    let with_before: BTreeSet<CausalCellId> = widest.union(&before).copied().collect();
    let with_after: BTreeSet<CausalCellId> = widest.union(&after).copied().collect();
    let before_work = sum_reduction_work(
        &rebase_invariants_with_schedule_on(complex, Some(&with_before), rule)
            .map_err(|error| format!("{error}"))?
            .1,
    );
    let after_work = sum_reduction_work(
        &rebase_invariants_with_schedule_on(complex, Some(&with_after), rule)
            .map_err(|error| format!("{error}"))?
            .1,
    );

    Ok(Verdicts {
        reading,
        before_work,
        after_work,
        before_cells: with_before.len(),
        after_cells: with_after.len(),
        wall_milliseconds,
    })
}

// ===============================================================================================
// hand-built witnesses

fn found_graph(
    label: &str,
    names: &[&str],
    arrows: &[(usize, usize)],
) -> (GradedCausalComplex, Incidence) {
    let mut complex = GradedCausalComplex::default();
    let mut counter = 0u64;
    let mut node_cell = Vec::new();
    for name in names {
        counter += 1;
        node_cell.push(
            complex
                .found_cell(
                    (*name).to_owned(),
                    BTreeSet::from([EventId(counter)]),
                    0,
                    CausalChain::default(),
                )
                .expect("a 0-cell founds"),
        );
    }
    let mut edges = Vec::new();
    for (tail, head) in arrows {
        let mut boundary = CausalChain::default();
        boundary.add_term(node_cell[*head], ComparativeMultiplicity::positive(1u32));
        boundary.add_term(node_cell[*tail], ComparativeMultiplicity::negative(1u32));
        counter += 1;
        let cell = complex
            .found_cell(
                format!("{}->{}", names[*tail], names[*head]),
                BTreeSet::from([EventId(counter)]),
                1,
                boundary,
            )
            .expect("a 1-cell founds");
        edges.push((*tail, *head, cell));
    }
    let pin_cells = edges.iter().map(|(_, _, cell)| *cell).collect();
    let incidence = Incidence {
        label: label.to_owned(),
        node_cell,
        node_name: names.iter().map(|name| (*name).to_owned()).collect(),
        edges,
        faces: Vec::new(),
        pin_cells,
    };
    (complex, incidence)
}

/// The witness that the record's biconditional fails: `a->b, a->c, a->d, b->d`.
///
/// Not a forest — `b_1 = 4 - 4 + 1 = 1` — yet `a`'s successors offered ascending puts `d` inside
/// `b`'s subtree and forces nothing, while offered descending it does not. One object, two
/// answers, and the difference is the walk order.
fn shortcut_fan() -> (GradedCausalComplex, Incidence) {
    found_graph(
        "shortcut-fan",
        &["a", "b", "c", "d"],
        &[(0, 1), (0, 2), (0, 3), (1, 3)],
    )
}

/// A vertex, a loop at it, and a face attached to that loop **twice**.
///
/// `CLAUDE.md` §8: a law that returns zero proves nothing about itself. The torsion columns of
/// `GradeRemainder` return empty on every grown reading below, so this is the declared control that
/// makes them return non-zero. It is authored material and is labelled as such.
fn doubly_attached_face() -> (GradedCausalComplex, Incidence) {
    let mut complex = GradedCausalComplex::default();
    let vertex = complex
        .found_cell(
            "v".to_owned(),
            BTreeSet::from([EventId(1)]),
            0,
            CausalChain::default(),
        )
        .expect("a 0-cell founds");
    let mut loop_boundary = CausalChain::default();
    loop_boundary.add_term(vertex, ComparativeMultiplicity::positive(1u32));
    loop_boundary.add_term(vertex, ComparativeMultiplicity::negative(1u32));
    let arc = complex
        .found_cell(
            "e".to_owned(),
            BTreeSet::from([EventId(2)]),
            1,
            loop_boundary,
        )
        .expect("a 1-cell founds");
    let mut face_boundary = CausalChain::default();
    face_boundary.add_term(arc, ComparativeMultiplicity::positive(2u32));
    let face = complex
        .found_cell(
            "f".to_owned(),
            BTreeSet::from([EventId(3)]),
            2,
            face_boundary,
        )
        .expect("a 2-cell founds");
    let incidence = Incidence {
        label: "doubly-attached-face".to_owned(),
        node_cell: vec![vertex],
        node_name: vec!["v".to_owned()],
        edges: vec![(0, 0, arc)],
        faces: vec![(face, BTreeSet::from([arc]))],
        pin_cells: BTreeSet::from([arc]),
    };
    (complex, incidence)
}

// ===============================================================================================
// the run

/// `rebase_invariants` records the measurement this rests on: on the grade-two boundary map of a
/// grown Brent–Kung adder, `FirstNonzero` did not complete in 390 seconds where `SmallestMagnitude`
/// took one millisecond. That is a fact about intermediate entry bit-length — a work quantity — and
/// not a clock preference.
const RULE: PivotRule = PivotRule::SmallestMagnitude;

fn main() {
    let mut refusals: Vec<String> = Vec::new();
    let mut sweep: Vec<(String, i64, bool)> = Vec::new();

    println!("================================================================================");
    println!("THE CONDENSATION MEETS A FAR POPULATION");
    println!("================================================================================");
    println!();
    println!("pivot rule: {RULE:?}   (admitted on work, never on a clock)");
    println!();

    the_witness_that_corrects_the_record(&mut refusals);
    the_torsion_control(&mut refusals);
    the_far_populations(&mut refusals, &mut sweep);

    println!();
    println!("--------------------------------------------------------------------------------");
    println!("4. THE SWEEP — the departure from a forest against the emptiness of the remainder");
    println!("--------------------------------------------------------------------------------");
    println!();
    println!("  {:<38} {:>12}  {}", "reading", "cyclomatic", "remainder");
    for (label, cyclomatic, empty) in &sweep {
        println!(
            "  {label:<38} {cyclomatic:>12}  {}",
            if *empty { "EMPTY" } else { "NON-EMPTY" }
        );
    }
    if !sweep.iter().any(|(_, cyclomatic, _)| *cyclomatic == 0) {
        refusals.push("the sweep holds no forest, so the empty case never fired".to_owned());
    }
    if !sweep.iter().any(|(_, cyclomatic, _)| *cyclomatic > 0) {
        refusals
            .push("the sweep holds no cyclic cone, so the non-empty case never fired".to_owned());
    }

    println!();
    println!("================================================================================");
    if refusals.is_empty() {
        println!("EVERY DECLARED CHECK RETURNED. No refusal.");
    } else {
        println!("REFUSED — {} check(s) did not return:", refusals.len());
        for refusal in &refusals {
            println!("  * {refusal}");
        }
    }
    println!("================================================================================");
    if !refusals.is_empty() {
        std::process::exit(1);
    }
}

fn describe_remainder(moved: &[GradeRemainder]) -> String {
    if moved.is_empty() {
        return "EMPTY".to_owned();
    }
    moved
        .iter()
        .map(|entry| {
            format!(
                "grade {} betti {:+} torsion gained {:?} lost {:?}",
                entry.grade, entry.betti_change, entry.torsion_gained, entry.torsion_lost
            )
        })
        .collect::<Vec<_>>()
        .join(" | ")
}

fn the_witness_that_corrects_the_record(refusals: &mut Vec<String>) {
    println!("--------------------------------------------------------------------------------");
    println!("1. THE INTERVAL REMAINDER IS NOT AN INVARIANT — the witness");
    println!("--------------------------------------------------------------------------------");
    println!();
    println!("The 2026-08-06 record: the forced-interval population \"is zero exactly when the");
    println!("incidence is a forest\". Forest => zero holds. The converse does not.");
    println!();

    let (complex, incidence) = shortcut_fan();
    let cone = incidence.cone(0, Flow::Downstream);
    println!(
        "  {} : {} nodes, {} arcs, cyclomatic |E|-|V|+1 = {}  -> NOT a forest",
        incidence.label,
        cone.size(),
        cone.edges.len(),
        cone.cyclomatic()
    );

    let mut orbit: BTreeSet<usize> = BTreeSet::new();
    for order in WalkOrder::ALL {
        let labelling = label(&cone, order);
        let (reach, _) = transitive_closure(&cone, &labelling.finish_order);
        if let Err(error) = certify(&cone, &labelling, &reach) {
            refusals.push(format!("shortcut-fan / {}: {error}", order.name()));
        }
        orbit.insert(labelling.forced_intervals);
        let shown: Vec<String> = (0..cone.size())
            .map(|node| {
                format!(
                    "{}{:?}",
                    incidence.node_name[cone.members[node]], labelling.intervals[node]
                )
            })
            .collect();
        println!(
            "  walk {:<13} non-tree edges {}   forced intervals {}   {}",
            order.name(),
            labelling.non_tree_edges,
            labelling.forced_intervals,
            shown.join(" ")
        );
    }
    println!();
    println!("  ORBIT of the forced-interval population under the walk-order gauge: {orbit:?}");
    if orbit.len() < 2 {
        refusals.push(
            "the walk-order gauge acts trivially on the witness, so it shows nothing".to_owned(),
        );
    } else {
        println!(
            "  NON-TRIVIAL: the interval remainder is a receiver coordinate, not an invariant."
        );
    }
    if !orbit.contains(&0) {
        refusals.push(
            "no walk order forced zero intervals on the witness, so the converse is not witnessed"
                .to_owned(),
        );
    } else {
        println!("  It contains ZERO on a non-forest, which is the record's converse, falsified.");
    }

    let contexts = vec![BTreeSet::from([incidence.node_cell[0]])];
    match condense(&complex, &incidence, &cone, &contexts, RULE) {
        Ok(verdicts) => {
            let moved = &verdicts.reading.verdicts[0].remainder;
            println!(
                "  skein's remainder on the SAME object: {}",
                describe_remainder(moved)
            );
            let grade_one = betti_change_at(moved, 1);
            if -grade_one != cone.cyclomatic() {
                refusals.push(format!(
                    "shortcut-fan: skein returned betti_change {grade_one} at grade 1, \
                     cyclomatic is {}",
                    cone.cyclomatic()
                ));
            } else {
                println!(
                    "  -betti_change(grade 1) = {} = cyclomatic, under every walk order. \
                     It does not move.",
                    -grade_one
                );
            }
        }
        Err(error) => refusals.push(format!("shortcut-fan: {error}")),
    }
    println!();
}

fn the_torsion_control(refusals: &mut Vec<String>) {
    println!("--------------------------------------------------------------------------------");
    println!("2. THE TORSION CONTROL — declared, authored, and required to return non-zero");
    println!("--------------------------------------------------------------------------------");
    println!();
    let (complex, incidence) = doubly_attached_face();
    let cone = incidence.cone(0, Flow::Downstream);
    let contexts = vec![BTreeSet::from([incidence.node_cell[0]])];
    match condense(&complex, &incidence, &cone, &contexts, RULE) {
        Ok(verdicts) => {
            let moved = &verdicts.reading.verdicts[0].remainder;
            println!("  {} : {}", incidence.label, describe_remainder(moved));
            let names_torsion = moved
                .iter()
                .any(|entry| !entry.torsion_lost.is_empty() || !entry.torsion_gained.is_empty());
            if names_torsion {
                println!(
                    "  The torsion columns of GradeRemainder CAN return non-zero. Every grown \
                     reading below returns them empty, and that is now evidence rather than silence."
                );
            } else {
                refusals.push(
                    "the torsion control returned no torsion, so an empty torsion column below \
                     evidences nothing"
                        .to_owned(),
                );
            }
        }
        Err(error) => refusals.push(format!("torsion control: {error}")),
    }
    println!();
}

fn betti_change_at(moved: &[GradeRemainder], grade: u32) -> i64 {
    moved
        .iter()
        .find(|entry| entry.grade == grade)
        .map_or(0, |entry| entry.betti_change)
}

fn the_far_populations(refusals: &mut Vec<String>, sweep: &mut Vec<(String, i64, bool)>) {
    println!("--------------------------------------------------------------------------------");
    println!("3. THE FAR POPULATIONS");
    println!("--------------------------------------------------------------------------------");

    let table = standard_cells();
    for declaration in declarations() {
        println!();
        println!("### {}", declaration.label);
        let growth = match grow(
            &table,
            declaration.rule,
            &declaration.material,
            Schedule::Instantiation,
        ) {
            Ok(growth) => growth,
            Err(refusal) => {
                refusals.push(format!("{}: growth refused {refusal:?}", declaration.label));
                continue;
            }
        };
        let grown = match found_complex(&growth, ComplexAperture::DIVISION) {
            Ok(grown) => grown,
            Err(refusal) => {
                refusals.push(format!(
                    "{}: complex refused {refusal:?}",
                    declaration.label
                ));
                continue;
            }
        };

        let nets: Vec<NetId> = grown.net_cells.keys().copied().collect();
        let index: BTreeMap<NetId, usize> = nets
            .iter()
            .enumerate()
            .map(|(position, net)| (*net, position))
            .collect();
        let admitted: BTreeSet<CausalCellId> = grown
            .arcs
            .iter()
            .filter(|arc| declaration.aperture.admits_arc(arc.gate.is_some()))
            .map(|arc| arc.cell)
            .collect();
        let edges: Vec<(usize, usize, CausalCellId)> = grown
            .arcs
            .iter()
            .filter(|arc| admitted.contains(&arc.cell))
            .map(|arc| (index[&arc.tail], index[&arc.head], arc.cell))
            .collect();
        let mut faces = Vec::new();
        if declaration.aperture.admits_faces() {
            for cell in grown.complex.cells().values() {
                if cell.grade != 2 {
                    continue;
                }
                let attaches: BTreeSet<CausalCellId> = cell
                    .boundary
                    .coefficients()
                    .iter()
                    .map(|(face, _)| *face)
                    .collect();
                if attaches.is_subset(&admitted) {
                    faces.push((cell.id, attaches));
                }
            }
        }
        let incidence = Incidence {
            label: declaration.label.to_owned(),
            node_cell: nets.iter().map(|net| grown.net_cells[net]).collect(),
            node_name: nets.iter().map(|net| format!("n{}", net.0)).collect(),
            edges,
            faces,
            pin_cells: grown
                .arcs
                .iter()
                .filter(|arc| arc.gate.is_some())
                .map(|arc| arc.cell)
                .collect(),
        };
        println!(
            "  grown: {} nets, {} gates, {} instances, depth {} | complex {} cells, \
             {} division faces, {} with multiplicity above one, largest coefficient {}",
            growth.net_count(),
            growth.gate_count(),
            growth.instance_count(),
            growth.depth(),
            grown.complex.cells().len(),
            grown.division_faces,
            grown.division_faces_with_multiplicity,
            grown.largest_face_coefficient
        );
        println!(
            "  aperture {:<14} {} arcs admitted of {} founded, {} faces admitted",
            declaration.aperture.name(),
            incidence.edges.len(),
            grown.arcs.len(),
            incidence.faces.len()
        );

        // The root: the net whose cone is widest. A measurement, not a choice.
        let successors = incidence.successors(declaration.flow);
        let Some(root) = (0..incidence.nodes()).max_by_key(|node| {
            incidence
                .cone_with(&successors, *node, declaration.flow)
                .size()
        }) else {
            refusals.push(format!("{}: no nets", declaration.label));
            continue;
        };
        let cone = incidence.cone_with(&successors, root, declaration.flow);
        let cyclomatic = cone.cyclomatic();
        println!(
            "  FAR POPULATION: the {} cone at {} — {} nodes, {} arcs, cyclomatic {cyclomatic}",
            declaration.flow.name(),
            incidence.node_name[root],
            cone.size(),
            cone.edges.len()
        );

        // --- the record's route: spanning-tree interval labelling under the declared gauge.
        let mut orbit: BTreeSet<usize> = BTreeSet::new();
        let mut storage_orbit: BTreeSet<u64> = BTreeSet::new();
        let mut closure_work = ClosureWork::default();
        let mut first: Option<Labelling> = None;
        for order in WalkOrder::ALL {
            let labelling = label(&cone, order);
            let (reach, work) = transitive_closure(&cone, &labelling.finish_order);
            closure_work = work;
            if let Err(error) = certify(&cone, &labelling, &reach) {
                refusals.push(format!("{} / {}: {error}", declaration.label, order.name()));
            }
            if labelling.tree_edges != cone.size() - 1 {
                refusals.push(format!(
                    "{} / {}: {} tree edges on {} nodes",
                    declaration.label,
                    order.name(),
                    labelling.tree_edges,
                    cone.size()
                ));
            }
            if labelling.non_tree_edges as i64 != cyclomatic {
                refusals.push(format!(
                    "{} / {}: {} non-tree edges but cyclomatic {cyclomatic}",
                    declaration.label,
                    order.name(),
                    labelling.non_tree_edges
                ));
            }
            println!(
                "    walk {:<13} tree edges {:>5}  non-tree {:>6}  FORCED INTERVALS {:>7}  \
                 stored words {:>8}  (inspections {}, merges {})",
                order.name(),
                labelling.tree_edges,
                labelling.non_tree_edges,
                labelling.forced_intervals,
                labelling.work.stored_words,
                labelling.work.edge_inspections,
                labelling.work.merge_comparisons
            );
            orbit.insert(labelling.forced_intervals);
            storage_orbit.insert(labelling.work.stored_words);
            if first.is_none() {
                first = Some(labelling);
            }
        }
        let labelling = first.expect("three walk orders ran");
        println!(
            "    ORBIT of the forced-interval population: {orbit:?}  — {}",
            if orbit.len() > 1 {
                "NON-TRIVIAL, so the count is a receiver coordinate"
            } else {
                "trivial on this material, so agreement here is not evidence"
            }
        );
        let best = storage_orbit.iter().copied().min().unwrap_or(0);
        let worst = storage_orbit.iter().copied().max().unwrap_or(0);
        println!(
            "    STORAGE, in words: direct closure {} ({} nodes x {} words), \
             condensed labelling {best}..{worst} across the walk-order orbit \
             (2 per node + 2 per forced interval)",
            closure_work.stored_words,
            cone.size(),
            cone.size().div_ceil(64)
        );
        println!(
            "      -> {}",
            if worst < closure_work.stored_words {
                format!(
                    "the condensed form is SMALLER under EVERY declared walk order, by {}..{} \
                     words. Condensation is required here.",
                    closure_work.stored_words - worst,
                    closure_work.stored_words - best
                )
            } else if best < closure_work.stored_words {
                format!(
                    "the verdict DEPENDS ON THE WALK ORDER: smaller by {} words under the best, \
                     larger by {} under the worst. The comparison is not an invariant.",
                    closure_work.stored_words - best,
                    worst - closure_work.stored_words
                )
            } else {
                format!(
                    "the condensed form is LARGER under every declared walk order, by {}..{} \
                     words. At this width the direct closure is the cheaper carrier and the \
                     labelling buys nothing.",
                    best - closure_work.stored_words,
                    worst - closure_work.stored_words
                )
            }
        );
        println!(
            "    the direct path also performed {} word unions to build that table.",
            closure_work.word_unions
        );

        exhibit_forced(&incidence, &cone, &labelling);

        // --- skein's route: condense the cone to its root and read the remainder.
        let cone_interior: BTreeSet<usize> = cone
            .members
            .iter()
            .copied()
            .filter(|node| *node != root)
            .collect();
        let opposite = incidence.cone(root, declaration.flow.reversed());
        let opposite_nodes: BTreeSet<usize> = opposite.members.iter().copied().collect();
        let complement: BTreeSet<usize> = (0..incidence.nodes())
            .filter(|node| !cone_interior.contains(node))
            .collect();
        let contexts = vec![
            BTreeSet::from([incidence.node_cell[root]]),
            incidence.induced_support(&opposite_nodes),
            incidence.induced_support(&complement),
        ];
        println!(
            "    contexts declared, nested and each meeting the cone only at its root: \
             {{root}} {} cells, opposite cone {} cells, complement {} cells",
            contexts[0].len(),
            contexts[1].len(),
            contexts[2].len()
        );

        match condense(&grown.complex, &incidence, &cone, &contexts, RULE) {
            Ok(verdicts) => {
                let empty = verdicts
                    .reading
                    .verdicts
                    .iter()
                    .all(|verdict| verdict.remainder.is_empty());
                sweep.push((declaration.label.to_owned(), cyclomatic, empty));
                let conduction = cone.conduction_cyclomatic(&incidence.pin_cells);
                report(&declaration, &cone, conduction, &verdicts, refusals);
            }
            Err(error) => refusals.push(format!("{}: {error}", declaration.label)),
        }
    }
}

fn exhibit_forced(incidence: &Incidence, cone: &Cone, labelling: &Labelling) {
    let mut carriers: Vec<(usize, usize)> = (0..cone.size())
        .map(|node| (labelling.intervals[node].len() - 1, node))
        .filter(|(extras, _)| *extras > 0)
        .collect();
    carriers.sort_unstable_by(|left, right| right.cmp(left));
    println!(
        "    THE FORCED-INTERVAL POPULATION: {} intervals carried by {} of {} nodes",
        labelling.forced_intervals,
        carriers.len(),
        cone.size()
    );
    if carriers.is_empty() {
        println!("      (empty — the depth-first tree already answers every cone exactly)");
        return;
    }
    for (extras, node) in carriers.iter().take(6) {
        let spans: Vec<String> = labelling.intervals[*node]
            .iter()
            .take(9)
            .map(|(start, end)| format!("[{start},{end})"))
            .collect();
        let elided = labelling.intervals[*node].len().saturating_sub(9);
        println!(
            "      {:<10} tree [{},{})  +{} forced -> {}{}",
            incidence.node_name[cone.members[*node]],
            labelling.enter[*node],
            labelling.exit[*node],
            extras,
            spans.join(" "),
            if elided > 0 {
                format!(" ...+{elided} more")
            } else {
                String::new()
            }
        );
    }
    if carriers.len() > 6 {
        println!("      ... and {} further carriers", carriers.len() - 6);
    }
}

fn report(
    declaration: &Declaration,
    cone: &Cone,
    conduction_cyclomatic: i64,
    verdicts: &Verdicts,
    refusals: &mut Vec<String>,
) {
    let cyclomatic = cone.cyclomatic();
    println!(
        "    skein: removed {} cells, added {} cells, compresses = {}, \
         distinguishing contexts {:?}",
        verdicts.reading.removed_extent,
        verdicts.reading.added_extent,
        verdicts.reading.compresses(),
        verdicts.reading.distinguishing_contexts()
    );
    println!("    THE CERTIFIED REMAINDER, per declared context:");
    let mut carried: Option<String> = None;
    for verdict in &verdicts.reading.verdicts {
        let described = describe_remainder(&verdict.remainder);
        println!("      context {}: {described}", verdict.context);
        match &carried {
            None => carried = Some(described),
            Some(first) if *first != described => refusals.push(format!(
                "{}: the remainder moved between contexts — {first} vs {described}. \
                 The condensation is not local.",
                declaration.label
            )),
            _ => {}
        }
    }

    let Some(verdict) = verdicts.reading.verdicts.first() else {
        refusals.push(format!("{}: no verdict returned", declaration.label));
        return;
    };
    let empty = verdict.remainder.is_empty();
    let grade_one = betti_change_at(&verdict.remainder, 1);

    // --- the declaration is itself checked. A wrong one is a refusal.
    match declaration.expectation {
        Expectation::Forest if cyclomatic != 0 => refusals.push(format!(
            "{}: declared a forest but cyclomatic is {cyclomatic}",
            declaration.label
        )),
        Expectation::Cyclic if cyclomatic <= 0 => refusals.push(format!(
            "{}: declared cyclic but cyclomatic is {cyclomatic}",
            declaration.label
        )),
        _ => {}
    }

    // --- the falsifier
    if declaration.aperture.admits_faces() {
        // With 2-cells present the departure from a forest is discharged rather than only counted,
        // and the identity below says exactly where it went.
        let grade_one_before = verdict.before.grades.iter().find(|entry| entry.grade == 1);
        let Some(entry) = grade_one_before else {
            refusals.push(format!("{}: the reading has no grade 1", declaration.label));
            return;
        };
        let free = entry.betti as i64;
        let filled = entry.filling_rank as i64;
        println!(
            "    THE DEPARTURE, SPLIT: betti_1 {free} + filling_rank {filled} = {} \
             (cyclomatic {cyclomatic}); torsion at grade 1 {:?}",
            free + filled,
            entry.torsion
        );
        if free + filled != cyclomatic {
            refusals.push(format!(
                "{}: betti_1 {free} + filling_rank {filled} = {} but cyclomatic is {cyclomatic}. \
                 The departure did not account for itself.",
                declaration.label,
                free + filled
            ));
        } else {
            println!(
                "    FALSIFIER: the whole departure from a forest is accounted for — {filled} \
                 filled by faces, {free} left free. Held."
            );
        }
        // And what is left free is not an arbitrary residue: it is exactly the departure the
        // PRIMITIVE circuit carries. The lineage boxes are laid parallel to the paths through their
        // own children, and each division face is precisely the 2-cell that fills one of those.
        println!(
            "    WHAT THE FACES DISCHARGED: betti_1 {free} against the conduction sub-incidence's \
             own cyclomatic {conduction_cyclomatic} on the same cone."
        );
        if free != conduction_cyclomatic {
            refusals.push(format!(
                "{}: betti_1 is {free} but the conduction sub-incidence carries \
                 {conduction_cyclomatic}. The faces did not discharge exactly the lineage's \
                 own loops.",
                declaration.label
            ));
        } else {
            println!(
                "      the division faces discharged the lineage aperture's added loops EXACTLY, \
                 leaving the primitive circuit's own reconvergence and nothing else."
            );
        }
        let acyclic = verdict
            .before
            .grades
            .iter()
            .skip(1)
            .all(|entry| entry.betti == 0 && entry.torsion.is_empty());
        if acyclic != empty {
            refusals.push(format!(
                "{}: the remainder is {} but the cone's reduced invariants are {}",
                declaration.label,
                if empty { "empty" } else { "non-empty" },
                if acyclic { "all zero" } else { "not all zero" }
            ));
        }
    } else if cyclomatic == 0 {
        if empty {
            println!("    FALSIFIER: a forest, and the remainder is EMPTY. Held.");
        } else {
            refusals.push(format!(
                "{}: a cyclomatic-zero incidence returned a NON-EMPTY remainder. \
                 The condensation is not certified.",
                declaration.label
            ));
        }
    } else if empty {
        refusals.push(format!(
            "{}: a cyclic incidence returned an EMPTY remainder. \
             The condensation is not certified.",
            declaration.label
        ));
    } else if -grade_one != cyclomatic {
        refusals.push(format!(
            "{}: -betti_change(grade 1) = {} but the departure from a forest is {cyclomatic}. \
             The remainder is not in proportion.",
            declaration.label, -grade_one
        ));
    } else {
        println!(
            "    FALSIFIER: -betti_change(grade 1) = {} = |E|-|V|+1 = the non-tree edge \
             population, exactly. Held.",
            -grade_one
        );
    }

    // --- b_0 must not move: the cone is connected and the point is a point.
    if betti_change_at(&verdict.remainder, 0) != 0 {
        refusals.push(format!(
            "{}: grade 0 moved by {}, so the cone was not connected",
            declaration.label,
            betti_change_at(&verdict.remainder, 0)
        ));
    }

    report_work(verdicts, &verdict.before);
}

fn report_work(verdicts: &Verdicts, before: &RebaseInvariants) {
    let extent: usize = before.grades.iter().map(|grade| grade.cells).sum();
    println!(
        "    WORK — the far population, read: {} cells in support ({extent} in the section), \
         {} entries written, {} bits written, peak entry {} bits, {} divisibility repairs",
        verdicts.before_cells,
        verdicts.before_work.entries_written,
        verdicts.before_work.written_bits,
        verdicts.before_work.peak_entry_bits,
        verdicts.before_work.repairs
    );
    println!(
        "    WORK — the compact realizer, read: {} cells in support, {} entries written, \
         {} bits written, peak entry {} bits, {} divisibility repairs",
        verdicts.after_cells,
        verdicts.after_work.entries_written,
        verdicts.after_work.written_bits,
        verdicts.after_work.peak_entry_bits,
        verdicts.after_work.repairs
    );
    println!(
        "    the condensation removed {} entry-writes and {} written bits. \
         The remainder above is what that cost.",
        verdicts
            .before_work
            .entries_written
            .saturating_sub(verdicts.after_work.entries_written),
        verdicts
            .before_work
            .written_bits
            .saturating_sub(verdicts.after_work.written_bits)
    );
    println!(
        "    clock (measures, decides nothing): {} ms for the whole reading",
        verdicts.wall_milliseconds
    );
}

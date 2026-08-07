//! Dilation: a receiver's horizon declared, and the lineage of what it reached.
//!
//! ## What was wrong
//!
//! The engine already carries a receiver deed vocabulary with exact lineage —
//! `graph_receiver::ReceiverGraphDeed::{Found, Dilate, Traverse, Refine, Coarsen, Retain}`, where
//! `Dilate { upper_horizon }` changes how far a receiver sees and returns `Retained` when the
//! horizon did not actually move. And it carries **ten traversals that bypass that vocabulary
//! entirely**, each a bare `pop_front` with an unbounded horizon nobody declared and no record of
//! what it pivoted off.
//!
//! The sharpest instance is inside the file that defines the vocabulary: `graph_receiver.rs:1858`
//! counts connected components with a raw unbounded walk — no receiver, no horizon, no lineage —
//! in the module whose entire subject is receivers with horizons and lineage.
//!
//! ## Lineage is not authored structure
//!
//! Brandon, 2026-08-06: *"Lineage is not authored structure, it is existing structure to be
//! pivotted off of; there is no objective 'truth' about a dead tree in a forest […] That is what
//! hand-written code is, dead trees, frozen wires entangled and waiting for a current that may or
//! may not ever come."*
//!
//! So a dilation here returns **what it reached, in the order it reached it, and what it had to
//! pivot off to close** — never a bare set. `DilationLineage::closure_added` is exactly the
//! structure the walk did not choose but could not proceed without, and it is retained rather than
//! folded into the result.
//!
//! ## The law, with its condition stated
//!
//! `CLAUDE.md` §12 records the measurement *dilation is a receiver gauge on hull combinatorics;
//! turn is not.* That is true **only above the covering horizon**, and the unconditional form is
//! what makes it untestable:
//!
//! ```text
//!   horizon >= covering   ->  GAUGE.       The section is the whole incidence.
//!                             The chart moves with the walk order; the invariants do not.
//!   horizon <  covering   ->  RESTRICTION. The receiver genuinely sees less.
//!                             The invariants MAY move, and their moving is not a defect.
//! ```
//!
//! Both halves are needed or the law returns zero (`CLAUDE.md` §8). Without the restriction case
//! there is nothing that could have moved the invariants, and "invariant under dilation" would be a
//! statement about a walk that always covered everything.
//!
//! The measurement the §12 correction rests on was taken on the residue-stratum atlas, which is one
//! of the three permanent losses — it resolves at no commit in either repository. So the
//! gauge/non-gauge pair is re-established here on live material rather than cited.

use std::collections::{BTreeMap, BTreeSet, VecDeque};

use serde::{Deserialize, Serialize};

use crate::algebraic::{CausalAlgebraicError, CausalCellId, GradedCausalComplex};

/// How far a receiver sees, in incidence steps from its focus. Never implicit.
///
/// `Unbounded` exists so that the ten sites which currently walk without a horizon can be ported
/// without changing their behavior, and so that "this walk declares no horizon" becomes a value in
/// the record rather than an absence from it.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum Horizon {
    Steps(u32),
    Unbounded,
}

impl Horizon {
    pub const fn admits(self, distance: u32) -> bool {
        match self {
            Self::Steps(limit) => distance <= limit,
            Self::Unbounded => true,
        }
    }
}

/// The order a dilation walks its frontier. A receiver coordinate, and the reason it is named.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum WalkOrder {
    Breadth,
    Depth,
}

impl WalkOrder {
    pub const ALL: [Self; 2] = [Self::Breadth, Self::Depth];

    pub const fn name(self) -> &'static str {
        match self {
            Self::Breadth => "breadth",
            Self::Depth => "depth",
        }
    }
}

/// What a dilation actually did. This is the chart, and it moves.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct DilationLineage {
    pub focus: CausalCellId,
    pub horizon: Horizon,
    pub order: WalkOrder,
    /// Cells in the order the walk reached them. Order-sensitive on purpose: this is the receiver's
    /// chart and two orders must produce two of them.
    pub reached: Vec<CausalCellId>,
    /// Incidence distance from the focus, per reached cell.
    pub distance: BTreeMap<CausalCellId, u32>,
    /// Cells the walk did not choose but could not proceed without: the boundary closure. Existing
    /// structure pivoted off, retained rather than folded into the result.
    pub closure_added: Vec<CausalCellId>,
    /// Cells one step beyond the horizon. Empty exactly when the horizon covered the incidence,
    /// which is what makes `is_gauge` decidable rather than asserted.
    pub open_frontier: Vec<CausalCellId>,
}

impl DilationLineage {
    /// Nothing incident to the section is outside it, so dilating further cannot move anything —
    /// the `Retained` case the receiver deed vocabulary already distinguishes.
    ///
    /// This means the receiver covered **its own component**, not that it holds every cell in the
    /// complex. A disjoint piece is never incident and so never enters the frontier; a receiver at
    /// an unbounded horizon still cannot see across a break in the incidence, and saying otherwise
    /// would make the horizon answer for connectivity.
    pub fn is_covering(&self) -> bool {
        self.open_frontier.is_empty()
    }
}

/// A section: the support a horizon admits, closed under boundary, with its lineage.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct DilatedSection {
    pub support: BTreeSet<CausalCellId>,
    pub lineage: DilationLineage,
}

impl DilatedSection {
    /// The support as `rebase_invariants_on` wants it.
    pub const fn support(&self) -> &BTreeSet<CausalCellId> {
        &self.support
    }
}

/// Two cells are incident when either lies in the other's boundary.
fn incidence(complex: &GradedCausalComplex) -> BTreeMap<CausalCellId, BTreeSet<CausalCellId>> {
    let mut adjacency: BTreeMap<CausalCellId, BTreeSet<CausalCellId>> = BTreeMap::new();
    for cell in complex.cells().values() {
        adjacency.entry(cell.id).or_default();
        for face in cell.boundary.support() {
            adjacency.entry(cell.id).or_default().insert(face);
            adjacency.entry(face).or_default().insert(cell.id);
        }
    }
    adjacency
}

/// Walk out from `focus` to `horizon` under `order`, then close under boundary.
///
/// The closure is what makes the result a genuine subcomplex: without it a face could be missing
/// from the rows of its own boundary matrix and the invariants would describe a structure that does
/// not exist. `is_closed_support` is asserted before returning, so that guarantee is checked rather
/// than argued.
pub fn dilate(
    complex: &GradedCausalComplex,
    focus: CausalCellId,
    horizon: Horizon,
    order: WalkOrder,
) -> Result<DilatedSection, CausalAlgebraicError> {
    complex.cell(focus)?;
    let adjacency = incidence(complex);

    // WHAT the receiver holds is a metric fact and must not depend on how it walked. The first
    // version labelled each cell with its DISCOVERY depth, which under `Depth` is the length of the
    // path the walk happened to take rather than the incidence distance — so changing the walk order
    // changed which cells fell inside the horizon, and dilation was not a gauge. The distance is now
    // always breadth-first, which is what makes it the true distance, and `order` decides only the
    // sequence in which admitted cells are visited.
    let distance = incidence_distance(focus, &adjacency);
    let walked: BTreeSet<CausalCellId> = distance
        .iter()
        .filter(|(_, step)| horizon.admits(**step))
        .map(|(cell, _)| *cell)
        .collect();

    // HOW it walked is the chart, and that is where the order belongs.
    let mut reached = Vec::new();
    let mut seen = BTreeSet::from([focus]);
    let mut pending = VecDeque::from([focus]);
    while let Some(cell) = match order {
        WalkOrder::Breadth => pending.pop_front(),
        WalkOrder::Depth => pending.pop_back(),
    } {
        reached.push(cell);
        for neighbor in adjacency.get(&cell).into_iter().flatten() {
            if walked.contains(neighbor) && seen.insert(*neighbor) {
                pending.push_back(*neighbor);
            }
        }
    }

    let support = complex.closed_hull(walked.iter().copied())?;
    let closure_added: Vec<CausalCellId> = support.difference(&walked).copied().collect();

    // Everything incident to the section that the section does not hold. Empty exactly when the
    // receiver has covered its own component — which is not the same as holding every cell in the
    // complex, because a disconnected piece is never adjacent and never enters the frontier.
    let mut open_frontier = BTreeSet::new();
    for cell in &support {
        for neighbor in adjacency.get(cell).into_iter().flatten() {
            if !support.contains(neighbor) {
                open_frontier.insert(*neighbor);
            }
        }
    }

    debug_assert!(
        complex.is_closed_support(&support)?,
        "a dilated section must be a genuine subcomplex"
    );

    Ok(DilatedSection {
        lineage: DilationLineage {
            focus,
            horizon,
            order,
            reached,
            distance: distance
                .into_iter()
                .filter(|(cell, _)| support.contains(cell))
                .collect(),
            closure_added,
            open_frontier: open_frontier.into_iter().collect(),
        },
        support,
    })
}

/// True incidence distance from `focus`, breadth-first and therefore order-independent.
fn incidence_distance(
    focus: CausalCellId,
    adjacency: &BTreeMap<CausalCellId, BTreeSet<CausalCellId>>,
) -> BTreeMap<CausalCellId, u32> {
    let mut distance = BTreeMap::from([(focus, 0u32)]);
    let mut pending = VecDeque::from([focus]);
    while let Some(cell) = pending.pop_front() {
        let step = distance[&cell];
        for neighbor in adjacency.get(&cell).into_iter().flatten() {
            if !distance.contains_key(neighbor) {
                distance.insert(*neighbor, step + 1);
                pending.push_back(*neighbor);
            }
        }
    }
    distance
}

/// The least horizon at which a dilation from `focus` covers the whole incidence.
///
/// Below it, dilation restricts; at or above it, dilation is a gauge. Computing it is what turns
/// `CLAUDE.md` §12's unconditional claim into one with a stated condition.
pub fn covering_horizon(
    complex: &GradedCausalComplex,
    focus: CausalCellId,
) -> Result<u32, CausalAlgebraicError> {
    let section = dilate(complex, focus, Horizon::Unbounded, WalkOrder::Breadth)?;
    Ok(section.lineage.distance.values().copied().max().unwrap_or(0))
}

/// Betti numbers of a graph-like section by the Euler route, independent of any homology reduction.
///
/// `b0 = components` and `b1 = edges - vertices + components`. This exists because
/// `graph_receiver.rs:1858-1875` already computes exactly these two numbers this way, and nothing
/// in the tree has ever compared them against the integer homology. `CLAUDE.md` §8: *where an
/// independent implementation exists, state both costs.* `CLAUDE.md` §0: *an invariant is only
/// visible across two frames.* This is the second frame, and it was free.
///
/// Returns `None` when the section carries a cell above grade one, where the Euler shortcut does
/// not apply and only the reduction can answer.
pub fn euler_reading(
    complex: &GradedCausalComplex,
    support: Option<&BTreeSet<CausalCellId>>,
) -> Result<Option<(usize, usize)>, CausalAlgebraicError> {
    let admitted = |id: &CausalCellId| support.is_none_or(|support| support.contains(id));

    let mut vertices: BTreeSet<CausalCellId> = BTreeSet::new();
    let mut edges: Vec<(CausalCellId, CausalCellId)> = Vec::new();
    for cell in complex.cells().values() {
        if !admitted(&cell.id) {
            continue;
        }
        match cell.grade {
            0 => {
                vertices.insert(cell.id);
            }
            1 => {
                let ends: Vec<CausalCellId> = cell.boundary.support().into_iter().collect();
                match ends.len() {
                    2 => edges.push((ends[0], ends[1])),
                    // A loop whose two ends coincide contributes an edge from a vertex to itself.
                    1 => edges.push((ends[0], ends[0])),
                    _ => return Ok(None),
                }
            }
            _ => return Ok(None),
        }
    }

    let mut adjacency: BTreeMap<CausalCellId, BTreeSet<CausalCellId>> = vertices
        .iter()
        .map(|vertex| (*vertex, BTreeSet::new()))
        .collect();
    for (left, right) in &edges {
        adjacency.entry(*left).or_default().insert(*right);
        adjacency.entry(*right).or_default().insert(*left);
    }

    let mut unseen = vertices.clone();
    let mut components = 0usize;
    while let Some(root) = unseen.iter().next().copied() {
        components += 1;
        unseen.remove(&root);
        let mut frontier = VecDeque::from([root]);
        while let Some(vertex) = frontier.pop_front() {
            for neighbor in adjacency.get(&vertex).into_iter().flatten() {
                if unseen.remove(neighbor) {
                    frontier.push_back(*neighbor);
                }
            }
        }
    }

    let cycle_rank = edges.len() + components - vertices.len();
    Ok(Some((components, cycle_rank)))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::algebraic::{CausalChain, ComparativeMultiplicity};
    use crate::causal::EventId;
    use crate::rebase_invariants::{rebase_invariants_on, PivotRule};

    fn source() -> BTreeSet<EventId> {
        BTreeSet::from([EventId(1)])
    }

    /// A path of `n` vertices joined by `n - 1` edges. Incidence distance from one end grows, so a
    /// horizon below the covering value genuinely truncates.
    fn path(length: usize) -> (GradedCausalComplex, Vec<CausalCellId>) {
        let mut complex = GradedCausalComplex::default();
        let mut vertices = Vec::new();
        for index in 0..length {
            vertices.push(
                complex
                    .found_cell(format!("v{index}"), source(), 0, CausalChain::default())
                    .expect("a vertex has no boundary"),
            );
        }
        for index in 1..length {
            let mut boundary = CausalChain::default();
            boundary.add_term(vertices[index], ComparativeMultiplicity::positive(1u32));
            boundary.add_term(vertices[index - 1], ComparativeMultiplicity::negative(1u32));
            complex
                .found_cell(format!("e{index}"), source(), 1, boundary)
                .expect("an edge closes");
        }
        (complex, vertices)
    }

    #[test]
    fn a_dilated_section_is_always_a_genuine_subcomplex() {
        let (complex, vertices) = path(6);
        for horizon in [0u32, 1, 2, 3, 4, 20] {
            for order in WalkOrder::ALL {
                let section =
                    dilate(&complex, vertices[0], Horizon::Steps(horizon), order).unwrap();
                assert!(
                    complex.is_closed_support(&section.support).unwrap(),
                    "horizon {horizon} under {order:?} returned a support that is not closed"
                );
            }
        }
    }

    #[test]
    fn the_closure_records_what_the_walk_pivoted_off_rather_than_folding_it_in() {
        let (complex, vertices) = path(4);
        // A horizon of one from a vertex reaches its incident edges; those edges' FAR vertices are
        // not walked, but the section cannot close without them.
        let section = dilate(&complex, vertices[0], Horizon::Steps(1), WalkOrder::Breadth).unwrap();
        assert!(
            !section.lineage.closure_added.is_empty(),
            "an edge was reached whose far vertex was not walked; the closure must record it"
        );
        for added in &section.lineage.closure_added {
            assert!(
                !section.lineage.reached.contains(added),
                "closure and walk must stay distinguishable"
            );
        }
    }

    #[test]
    fn the_open_frontier_is_empty_exactly_when_the_horizon_covers() {
        let (complex, vertices) = path(5);
        let covering = covering_horizon(&complex, vertices[0]).unwrap();
        assert!(covering > 1, "a path of five is not covered in one step");

        let short = dilate(&complex, vertices[0], Horizon::Steps(1), WalkOrder::Breadth).unwrap();
        assert!(!short.lineage.is_covering(), "a short horizon must restrict");

        let full =
            dilate(&complex, vertices[0], Horizon::Steps(covering), WalkOrder::Breadth).unwrap();
        assert!(full.lineage.is_covering(), "the covering horizon must cover");

        let beyond =
            dilate(&complex, vertices[0], Horizon::Steps(covering + 3), WalkOrder::Breadth)
                .unwrap();
        assert_eq!(
            full.support, beyond.support,
            "dilating past covering is the Retained case: nothing moves"
        );
    }

    /// A cycle of `n` vertices. Every vertex has two incident edges, so a walk from any of them
    /// branches immediately and the order genuinely matters.
    ///
    /// This fixture exists because the first version of the gauge test below used `path`, where the
    /// walk never has a choice — breadth and depth produce identical charts and the test compared a
    /// reading against itself. It failed, correctly. **Material that cannot distinguish the
    /// coordinate under test proves nothing about that coordinate**, and this is the second time
    /// that defect appeared today; the first was a uniform aperture making largest-first identical
    /// to breadth in the grown-circuit driver.
    fn cycle(length: usize) -> (GradedCausalComplex, Vec<CausalCellId>) {
        let mut complex = GradedCausalComplex::default();
        let mut vertices = Vec::new();
        for index in 0..length {
            vertices.push(
                complex
                    .found_cell(format!("v{index}"), source(), 0, CausalChain::default())
                    .expect("a vertex has no boundary"),
            );
        }
        for index in 0..length {
            let mut boundary = CausalChain::default();
            boundary.add_term(
                vertices[(index + 1) % length],
                ComparativeMultiplicity::positive(1u32),
            );
            boundary.add_term(vertices[index], ComparativeMultiplicity::negative(1u32));
            complex
                .found_cell(format!("e{index}"), source(), 1, boundary)
                .expect("an edge closes");
        }
        (complex, vertices)
    }

    /// The gauge half. Above the covering horizon the chart moves with the walk order and the
    /// invariants do not.
    #[test]
    fn above_the_covering_horizon_dilation_is_a_gauge() {
        let (complex, vertices) = cycle(7);
        let covering = covering_horizon(&complex, vertices[0]).unwrap();

        let mut charts = BTreeSet::new();
        let mut settled = None;
        for horizon in [covering, covering + 1, covering + 5] {
            for order in WalkOrder::ALL {
                let section =
                    dilate(&complex, vertices[0], Horizon::Steps(horizon), order).unwrap();
                charts.insert(section.lineage.reached.clone());
                let invariants =
                    rebase_invariants_on(&complex, Some(&section.support), PivotRule::FirstNonzero)
                        .unwrap();
                match &settled {
                    None => settled = Some(invariants.betti_vector()),
                    Some(first) => assert_eq!(
                        *first,
                        invariants.betti_vector(),
                        "horizon {horizon} under {order:?} moved the invariants above covering"
                    ),
                }
            }
        }
        assert!(
            charts.len() > 1,
            "the charts must genuinely differ, or the agreement is a self-comparison"
        );
    }

    /// The non-gauge half, without which the gauge half is a law that returns zero.
    #[test]
    fn below_the_covering_horizon_dilation_restricts_and_the_invariants_move() {
        let (complex, vertices) = path(6);
        let covering = covering_horizon(&complex, vertices[0]).unwrap();

        let whole = rebase_invariants_on(&complex, None, PivotRule::FirstNonzero).unwrap();
        let restricted =
            dilate(&complex, vertices[0], Horizon::Steps(2), WalkOrder::Breadth).unwrap();
        let seen =
            rebase_invariants_on(&complex, Some(&restricted.support), PivotRule::FirstNonzero)
                .unwrap();

        assert!(!restricted.lineage.is_covering());
        assert!(restricted.support.len() < complex.cells().len());
        assert_ne!(
            whole.grades[0].cells, seen.grades[0].cells,
            "a restricting horizon must actually hold less, at horizon 2 of covering {covering}"
        );
    }

    /// Disjoint pieces, so that `components` is greater than one somewhere in the material.
    ///
    /// A dilation from a single focus always returns a CONNECTED section, so no sweep over sections
    /// can ever exercise the `components` term of the Euler formula. The first version of the
    /// cross-frame test below was exactly that sweep, and a deliberate corruption of the components
    /// term passed it untouched — the third instance today of a check whose material could not
    /// distinguish what it was checking. This fixture is why the whole-complex case is tested too.
    fn two_pieces() -> GradedCausalComplex {
        let mut complex = GradedCausalComplex::default();
        let mut previous = None;
        for index in 0..7 {
            let vertex = complex
                .found_cell(format!("v{index}"), source(), 0, CausalChain::default())
                .expect("a vertex has no boundary");
            // The break between index 2 and 3 is what makes two pieces rather than one.
            if let Some(earlier) = previous.filter(|_| index != 3) {
                let mut boundary = CausalChain::default();
                boundary.add_term(vertex, ComparativeMultiplicity::positive(1u32));
                boundary.add_term(earlier, ComparativeMultiplicity::negative(1u32));
                complex
                    .found_cell(format!("e{index}"), source(), 1, boundary)
                    .expect("an edge closes");
            }
            previous = Some(vertex);
        }
        complex
    }

    #[test]
    fn the_two_frames_agree_where_the_component_count_is_above_one() {
        let complex = two_pieces();
        let euler = euler_reading(&complex, None).unwrap().expect("graph-like");
        assert_eq!(euler.0, 2, "the fixture must actually be disconnected");
        assert_eq!(euler.1, 0, "two trees carry no loop");

        let reduced = rebase_invariants_on(&complex, None, PivotRule::FirstNonzero).unwrap();
        let betti = reduced.betti_vector();
        assert_eq!(
            (betti[0], betti.get(1).copied().unwrap_or(0)),
            euler,
            "the Euler route and the integer reduction disagree on a disconnected complex"
        );
    }

    /// The second frame, free from `graph_receiver`'s own arithmetic. If these two ever disagree,
    /// one of them is wrong, and nothing in the tree has compared them before.
    #[test]
    fn the_euler_route_and_the_integer_reduction_agree_on_every_section() {
        let (complex, vertices) = path(6);
        for horizon in [0u32, 1, 2, 3, 4, 5, 9] {
            for order in WalkOrder::ALL {
                let section =
                    dilate(&complex, vertices[0], Horizon::Steps(horizon), order).unwrap();
                let reduced =
                    rebase_invariants_on(&complex, Some(&section.support), PivotRule::FirstNonzero)
                        .unwrap();
                let euler = euler_reading(&complex, Some(&section.support))
                    .unwrap()
                    .expect("a path is graph-like");
                let betti = reduced.betti_vector();
                assert_eq!(
                    (betti[0], betti.get(1).copied().unwrap_or(0)),
                    euler,
                    "Euler route and Smith normal form disagree at horizon {horizon} under {order:?}"
                );
            }
        }
    }

    #[test]
    fn the_two_frames_agree_on_a_cycle_where_both_see_a_loop() {
        let mut complex = GradedCausalComplex::default();
        let mut vertices = Vec::new();
        for index in 0..5 {
            vertices.push(
                complex
                    .found_cell(format!("v{index}"), source(), 0, CausalChain::default())
                    .unwrap(),
            );
        }
        for index in 0..5 {
            let mut boundary = CausalChain::default();
            boundary.add_term(vertices[(index + 1) % 5], ComparativeMultiplicity::positive(1u32));
            boundary.add_term(vertices[index], ComparativeMultiplicity::negative(1u32));
            complex
                .found_cell(format!("e{index}"), source(), 1, boundary)
                .unwrap();
        }

        let reduced = rebase_invariants_on(&complex, None, PivotRule::FirstNonzero).unwrap();
        let euler = euler_reading(&complex, None).unwrap().expect("graph-like");
        assert_eq!(euler, (1, 1), "one component, one loop");
        assert_eq!(
            (reduced.betti_vector()[0], reduced.betti_vector()[1]),
            euler
        );
    }

    #[test]
    fn the_euler_route_declines_where_it_does_not_apply() {
        let mut complex = GradedCausalComplex::default();
        let a = complex
            .found_cell("a", source(), 0, CausalChain::default())
            .unwrap();
        let mut boundary = CausalChain::default();
        boundary.add_term(a, ComparativeMultiplicity::positive(1u32));
        boundary.add_term(a, ComparativeMultiplicity::negative(1u32));
        let edge = complex.found_cell("loop", source(), 1, boundary).unwrap();
        let mut face = CausalChain::default();
        face.add_term(edge, ComparativeMultiplicity::positive(2u32));
        complex.found_cell("twice", source(), 2, face).unwrap();

        assert!(
            euler_reading(&complex, None).unwrap().is_none(),
            "a grade-two cell is past the Euler shortcut's aperture and it must say so rather \
             than return a number"
        );
    }
}

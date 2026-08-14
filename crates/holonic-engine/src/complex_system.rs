//! A graded causal complex read as an observed system, so compression and placement can see it.
//!
//! ## The cut this closes
//!
//! `blueprint/THE_ASSEMBLY.md` §1: `CausalCellId(u64)` and `ItemId(u64)` are the same
//! representation, and until now **no function anywhere converted them**. That single missing
//! adapter was the cut line between the engine's condensation half — `algebraic`, `dilation`,
//! `rebase_invariants`, `skein`, all of which speak `CausalCellId` — and its positivity half —
//! `receiver_exact_compression`, `supported_realizers`, `placement`, all of which speak `ItemId`.
//! Neither half could read the other's material, so the compression/realizer/placement triple had
//! never been run on a causal complex at all.
//!
//! The conversion lives **here**, as two local functions, and deliberately not as `impl From` in
//! `algebraic.rs`. A `From<CausalCellId> for ItemId` would put a placement dependency inside the
//! algebraic carrier: the carrier would then know about the organ that reads it, which is the wrong
//! direction and the reason the adapter is written at the seam instead of at either end.
//!
//! ## The seam is one-directional, and that is a declaration rather than an omission
//!
//! `Observation` is documented at its definition as *"an opaque exact token — never a magnitude, so
//! nothing here can be ordered, averaged, or thresholded."* This module honours that in the only way
//! that is checkable: **there is no adapter from `Observation` back to a `ComparativeMultiplicity`,
//! a `CausalChain`, or a coefficient of any kind, and none is to be built.** Cells flow into
//! observations; observations never flow back into the complex.
//!
//! Widening the seam the other way would put an orderable quantity in the conduct path and fire
//! `CLAUDE.md` §13 rule 2 — *no privileged scalar governor inside the body*. An `Observation` that
//! could be re-read as a coefficient is a magnitude wearing a token's name, because the coefficient
//! it became would be comparable.
//!
//! The two readings below make that concrete rather than promised: **one cell carries two different
//! addresses under two readings of one section**, and a third under a second receiver. A number that
//! changes when the receiver's declaration changes, with the cell untouched, is a coordinate and not
//! a property of the cell. Nothing on the conduct path orders these tokens — `Ord` is used only by
//! `Partition::from_keys` to group equal signatures canonically, never to decide anything.
//!
//! ## What a receiver is here, and what it returns
//!
//! A receiver is a [`DilatedSection`] — a declared focus, a declared horizon, a walk order, and the
//! lineage of what it reached. `dilate` returns **an invariant and a chart in one value**, and which
//! of the two a receiver reads is a declaration, [`AddressReading`]:
//!
//! ```text
//!   Metric    inside the section    Observation(1 + incidence distance from the focus)
//!             outside it            Observation(0)
//!
//!   Chart     walked to             Observation(1 + position in lineage.reached)
//!             not walked to         Observation(0)
//! ```
//!
//! Both are receiver-local addresses, the same shape
//! `soma/life/examples/eros_placement_over_real_charts.rs` already uses. Two receivers at different
//! foci return different addresses for one cell, and neither address is a coordinate in the complex —
//! there is no frame in which they agree.
//!
//! **The `1 +` is load-bearing in both readings.** Without it the focus, at distance zero and at walk
//! position zero, would be indistinguishable from everything the receiver cannot see. The offset is
//! what makes "outside my horizon" a value the token can carry rather than an absence it collides
//! with.
//!
//! ## Both fields of the dilation are read, and that is what the second frame is
//!
//! `THE_ASSEMBLY.md`'s holistic constraint names the specific failure: *"an adapter that keeps
//! `.support` and drops `.lineage` deletes the chart and keeps the invariant, which reads as rigour
//! and is the loss of the second frame."* **Keeping `.lineage.distance` and dropping
//! `.lineage.reached` is the same loss with the fields relabelled** — `dilate` computes distance
//! breadth-first whatever order it walked, so an adapter that reads only the distance cannot observe
//! the walk order at all, and a test that then certifies invariance under walk order is comparing a
//! reading against itself. This module was written that way until 2026-08-08 and the invariance was
//! an assumption wearing a test.
//!
//! So all three fields the module could read are read, each by a named site:
//!
//! ```text
//!   section.support            declare      the section must have been measured on THIS complex
//!   section.lineage.distance   Metric       the invariant: order-independent by construction
//!   section.lineage.reached    Chart        the chart: order-dependent by construction
//! ```
//!
//! and the gauge law is then a measurement with two halves that can each fail:
//!
//! ```text
//!   the metric address population is the SAME under Breadth and Depth
//!   the chart  address population is DIFFERENT under Breadth and Depth
//! ```
//!
//! The second half is the one that was missing. Its failure — a chart address that did not move —
//! would mean the adapter is not reading the chart, which is exactly the deletion the constraint
//! forbids. `dilation.rs` states the same law from its own side: *"The chart moves with the walk
//! order; the invariants do not."*
//!
//! **A partition comparison cannot see this and never could.** A walk position is injective over the
//! cells the receiver walked to, so the chart reading returns one singleton per walked cell under
//! either order and the two conduct partitions agree — for a reason that has nothing to do with the
//! chart. That is why the measurement lives on the address population, which is returned whole by
//! [`ComplexSystem::addresses`], and not on the partition.
//!
//! ## The conduct aperture, declared
//!
//! An input is a **1-cell**, and `successor` steps across it:
//!
//! ```text
//!   the cell is an endpoint of the 1-cell, which has two ends   ->  the far end
//!   the cell is the single end of a 1-cell with one end         ->  itself; the loop rests
//!   the cell is not an end of the 1-cell                        ->  None, a declared terminus
//!   the 1-cell has three or more ends                           ->  None: no two-sided crossing
//! ```
//!
//! So conduct runs on the **1-skeleton**, and every cell of grade one or above is a terminus for
//! every input. That is an aperture, it is declared, and it shows up in the returns rather than
//! being hidden by them: on a cycle read from one focus, the conduct refinement separates the
//! mirror-symmetric *vertices* and leaves the mirror-symmetric *edges* merged, because the edges
//! have no crossings to tell them apart. `CLAUDE.md` §8 — *an organ used past its declared aperture
//! is a defect even when it appears to return* — cuts both ways: the aperture has to be legible from
//! the outside, and here it is.
//!
//! **The aperture is forced by the carrier, not chosen here, and that bounds what the returns can
//! testify to.** `algebraic.rs`'s `found_cell` refuses any boundary term whose grade is not exactly
//! one less than the carrier's, so **no 1-cell can ever be an end of a 1-cell in any
//! `GradedCausalComplex`**. Every cell of grade one or above is therefore a terminus for every input
//! in every complex, unconditionally. Consequently "the mirror edges survive the refinement" is a
//! theorem about the carrier's grade law and **cannot fail for any implementation that steps along
//! boundary incidence** — it documents the aperture and is not evidence about this organ. Only the
//! vertex half of that return is refutable.
//!
//! A 1-cell with three or more ends is admissible in this carrier (`found_cell` only checks grades
//! and `boundary(boundary) = 0`, both of which such a cell satisfies) and it is **refused a
//! crossing** rather than resolved by picking one end. Picking would be inventing geometry the
//! complex does not have, the same defect `THE_ASSEMBLY.md` §4 B3 refuses for `Rat -> RatVec3`.
//!
//! `None` is a declared terminus and never an error. Two cells that agree on every observation and
//! disagree on *whether* an input continues are distinguished by that disagreement, which is why the
//! absence is part of the conduct rather than a gap in it.

use std::collections::BTreeSet;

use thiserror::Error;

use crate::algebraic::{CausalCellId, GradedCausalComplex};
use crate::dilation::DilatedSection;
use crate::receiver_exact_compression::{InputId, ItemId, Observation, ObservedSystem, ReceiverId};

/// A cell, named as an item of the population under compression.
///
/// Local on purpose. This is the whole adapter `THE_ASSEMBLY.md` §1 names, and it is deliberately
/// **not** `impl From<CausalCellId> for ItemId` in `algebraic.rs`: the algebraic carrier must not
/// acquire a dependency on the organ that reads it.
pub const fn item(cell: CausalCellId) -> ItemId {
    ItemId(cell.0)
}

/// An item, read back as the cell it names.
///
/// The inverse of [`item`], and equally local. This direction is safe because an `ItemId` in this
/// module's returns *is* a cell identity and carries nothing else — unlike [`Observation`], which is
/// a receiver-local address and has no inverse at all.
pub const fn cell(item: ItemId) -> CausalCellId {
    CausalCellId(item.0)
}

/// Which of the dilation's two fields a receiver reads. Never implicit.
///
/// `dilate` returns an invariant and a chart in one value and says so: `lineage.distance` is
/// breadth-first whatever order the walk took, while `lineage.reached` is *"order-sensitive on
/// purpose: this is the receiver's chart and two orders must produce two of them."* A receiver that
/// could only read the first could not observe its own walk order, and every gauge claim made
/// through it would be a self-comparison.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum AddressReading {
    /// `1 + incidence distance from the focus`, `0` outside the section. The invariant.
    Metric,
    /// `1 + position in `lineage.reached``, `0` for a cell the walk did not reach. The chart.
    ///
    /// Note what this reading hides that the metric one does not: a cell the walk never chose but
    /// the boundary closure had to add — `lineage.closure_added` — has a distance and has no walk
    /// position, so it reads `0` here and nonzero there. The two readings differ in what they can
    /// see, not only in how they number it.
    Chart,
}

/// A declaration this adapter refuses.
#[derive(Clone, Debug, PartialEq, Eq, Error)]
pub enum ComplexSystemError {
    #[error("declared input {0:?} is not a cell of this complex")]
    InputAbsent(CausalCellId),
    #[error("declared input {cell:?} has grade {grade}; conduct steps across 1-cells only")]
    InputNotAOneCell { cell: CausalCellId, grade: u32 },
    #[error("declared input {0:?} appears twice; an input is an admitted step, not a multiset")]
    InputRepeated(CausalCellId),
    #[error("receiver {receiver} is focused at {focus:?}, which is not a cell of this complex")]
    ReceiverFocusAbsent {
        receiver: usize,
        focus: CausalCellId,
    },
    #[error(
        "receiver {receiver} reads {cell:?}, which is not a cell of this complex; the section was \
         measured on another one and its addresses are coordinates from another frame"
    )]
    ReceiverSectionForeign { receiver: usize, cell: CausalCellId },
}

/// A graded causal complex, a declared receiver family, a declared reading, and a declared conduct
/// aperture.
///
/// The complex is borrowed: this is an adapter over existing material, not a second copy of it.
/// Deliberately not serializable — what gets deposited is the compression, the placement, and the
/// dilations, each of which already rests. A serialized adapter would be a second copy of the
/// complex wearing the adapter's name.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ComplexSystem<'a> {
    pub complex: &'a GradedCausalComplex,
    /// Which field of each section the receivers read. A receiver coordinate, declared once for the
    /// family so that two readings of one section are two systems and can be compared.
    pub reading: AddressReading,
    /// One dilated section per receiver. Each carries its own focus, horizon and walk order, so two
    /// receivers genuinely disagree about where a cell is.
    pub receivers: Vec<DilatedSection>,
    /// The 1-cells conduct may step across. A cell absent from this list is not an admitted step,
    /// which is an aperture and not a defect — widening it refines the compression.
    pub inputs: Vec<CausalCellId>,
}

impl<'a> ComplexSystem<'a> {
    /// Declare the system, refusing an aperture the carrier cannot honour.
    ///
    /// A non-1-cell input would be a dead step: `successor` would return `None` for every item, the
    /// compression would count an input that can never separate anything, and the returned round
    /// count would describe a conduct the system does not have. `CLAUDE.md` §8 asks that an organ
    /// read the aperture it is handed rather than appear to return past it, so this refuses.
    ///
    /// **A section is refused unless it was measured on THIS complex.** Checking only the focus —
    /// which is what this did until 2026-08-08 — admits a section measured elsewhere and lets its
    /// distances be reported as addresses in a complex that never produced them. A cell then reads
    /// `Observation(0)`, "outside my horizon", when the receiver's own geometry puts it two steps
    /// away. That is a receiver reporting a coordinate from another frame, admitted by the organ
    /// whose stated job is refusing an aperture the carrier cannot honour. Every field this module
    /// reads is checked: the support, the distance keys, and the walk.
    pub fn declare(
        complex: &'a GradedCausalComplex,
        reading: AddressReading,
        receivers: Vec<DilatedSection>,
        inputs: Vec<CausalCellId>,
    ) -> Result<Self, ComplexSystemError> {
        let mut declared = BTreeSet::new();
        for input in &inputs {
            let body = complex
                .cell(*input)
                .map_err(|_| ComplexSystemError::InputAbsent(*input))?;
            if body.grade != 1 {
                return Err(ComplexSystemError::InputNotAOneCell {
                    cell: *input,
                    grade: body.grade,
                });
            }
            if !declared.insert(*input) {
                return Err(ComplexSystemError::InputRepeated(*input));
            }
        }
        for (index, section) in receivers.iter().enumerate() {
            if complex.cell(section.lineage.focus).is_err() {
                return Err(ComplexSystemError::ReceiverFocusAbsent {
                    receiver: index,
                    focus: section.lineage.focus,
                });
            }
            let read = section
                .support
                .iter()
                .chain(section.lineage.distance.keys())
                .chain(section.lineage.reached.iter());
            if let Some(foreign) = read.copied().find(|held| complex.cell(*held).is_err()) {
                return Err(ComplexSystemError::ReceiverSectionForeign {
                    receiver: index,
                    cell: foreign,
                });
            }
        }
        Ok(Self {
            complex,
            reading,
            receivers,
            inputs,
        })
    }

    /// Every 1-cell of the complex, in identity order — the widest conduct aperture available.
    ///
    /// Offered because the interesting comparison is between apertures: the same complex and the
    /// same receivers read at a narrow aperture and at the full one return different conduct, and
    /// the difference is the population the narrow reading merged.
    ///
    /// The order is part of the return, not incidental to it. `InputId(k)` names position `k` of
    /// this list, and every `distinguishing_word` a compression exhibits is spelled in those
    /// positions — so a caller reading a returned word back into cell names depends on this order
    /// being the complex's own.
    pub fn every_one_cell(complex: &GradedCausalComplex) -> Vec<CausalCellId> {
        complex
            .cells()
            .values()
            .filter(|body| body.grade == 1)
            .map(|body| body.id)
            .collect()
    }

    /// Step from `cell` across the 1-cell `edge`, in the complex's own vocabulary.
    ///
    /// The geometric primitive `successor` is a thin wrapper over. Returned as cells rather than
    /// items so a caller reading the complex never has to hold both namings at once.
    ///
    /// The grade guard is live and not defensive: a 2-cell bounded by two parallel 1-cells has
    /// exactly two ends and would otherwise carry a perfectly well-formed "crossing" from one of its
    /// edges to the other. Conduct runs on the 1-skeleton, and a step between two 1-cells is outside
    /// that aperture however two-sided it looks.
    pub fn crossing(&self, from: CausalCellId, edge: CausalCellId) -> Option<CausalCellId> {
        let body = self.complex.cell(edge).ok()?;
        if body.grade != 1 {
            return None;
        }
        let ends: Vec<CausalCellId> = body.boundary.support().into_iter().collect();
        if !ends.contains(&from) {
            return None;
        }
        match ends.as_slice() {
            // A 1-cell with one end is a loop at that cell; crossing it rests where it is.
            [only] => Some(*only),
            // The two-sided case: the far end, which is the crossing.
            [left, right] => Some(if *left == from { *right } else { *left }),
            // Three or more ends admit no two-sided crossing. Choosing one would invent geometry.
            _ => None,
        }
    }

    /// Every cell of the complex with this receiver's address for it, in identity order.
    ///
    /// The population behind [`ObservedSystem::observation`], returned **whole**. `THE_ASSEMBLY.md`:
    /// *no adapter may reduce one of these structures to a boolean or a scalar on its way to the
    /// next organ.*
    ///
    /// **The cells reading `Observation(0)` are in the return and are the point of it.** This
    /// returned only the receiver's own support until 2026-08-08, which dropped every cell the
    /// receiver cannot see — on a two-component complex, half the population — and the module then
    /// asserted their absence rather than catching it. That outside population is the subject of the
    /// narrow-aperture reading: a far component is one merged block precisely *because* every cell
    /// of it reads zero, and a return that omits them cannot exhibit the block it merged.
    pub fn addresses(&self, receiver: ReceiverId) -> Vec<(CausalCellId, Observation)> {
        self.complex
            .cells()
            .keys()
            .map(|id| (*id, self.observation(item(*id), receiver)))
            .collect()
    }
}

impl ObservedSystem for ComplexSystem<'_> {
    /// The whole cell population, in identity order — the order a caller depositing this return
    /// gets, and therefore part of the artifact rather than incidental to it.
    fn items(&self) -> Vec<ItemId> {
        self.complex.cells().keys().copied().map(item).collect()
    }

    fn receivers(&self) -> Vec<ReceiverId> {
        (0..self.receivers.len() as u64).map(ReceiverId).collect()
    }

    fn inputs(&self) -> Vec<InputId> {
        (0..self.inputs.len() as u64).map(InputId).collect()
    }

    /// The declared reading's address inside the section, `0` outside. Never a magnitude.
    ///
    /// A receiver index past the declared family reads `0` for every cell — it holds nothing, which
    /// is what a receiver that does not exist holds, and it therefore distinguishes nothing. Any
    /// other return would let a caller iterating a wider family than was declared receive a
    /// fabricated signature.
    fn observation(&self, item: ItemId, receiver: ReceiverId) -> Observation {
        let Some(section) = self.receivers.get(receiver.0 as usize) else {
            return Observation(0);
        };
        let target = cell(item);
        match self.reading {
            AddressReading::Metric => section
                .lineage
                .distance
                .get(&target)
                .map_or(Observation(0), |step| Observation(1 + u64::from(*step))),
            AddressReading::Chart => section
                .lineage
                .reached
                .iter()
                .position(|walked| *walked == target)
                .map_or(Observation(0), |place| Observation(1 + place as u64)),
        }
    }

    fn successor(&self, item: ItemId, input: InputId) -> Option<ItemId> {
        let edge = *self.inputs.get(input.0 as usize)?;
        self.crossing(cell(item), edge)
            .map(crate::complex_system::item)
    }
}

#[cfg(test)]
mod tests {
    use num_bigint::BigInt;

    use super::*;
    use crate::algebraic::{CausalChain, ComparativeMultiplicity};
    use crate::causal::EventId;
    use crate::dilation::{Horizon, WalkOrder, dilate};
    use crate::placement::place;
    use crate::receiver_exact_compression::{Partition, compress};
    use crate::supported_realizers::RealizerId;

    fn source() -> BTreeSet<EventId> {
        BTreeSet::from([EventId(1)])
    }

    fn join(
        complex: &mut GradedCausalComplex,
        name: &str,
        tail: CausalCellId,
        head: CausalCellId,
    ) -> CausalCellId {
        let mut boundary = CausalChain::default();
        boundary.add_term(head, ComparativeMultiplicity::positive(1u32));
        boundary.add_term(tail, ComparativeMultiplicity::negative(1u32));
        complex
            .found_cell(name, source(), 1, boundary)
            .expect("an edge closes")
    }

    fn vertices(complex: &mut GradedCausalComplex, count: usize, tag: &str) -> Vec<CausalCellId> {
        (0..count)
            .map(|index| {
                complex
                    .found_cell(format!("{tag}{index}"), source(), 0, CausalChain::default())
                    .expect("a vertex has no boundary")
            })
            .collect()
    }

    /// `n` vertices in a cycle. Every vertex has two incident edges, so a dilation from any of them
    /// branches and the walk order genuinely produces two charts — which is what the gauge test
    /// below needs its material to be able to do.
    fn cycle(length: usize) -> (GradedCausalComplex, Vec<CausalCellId>, Vec<CausalCellId>) {
        let mut complex = GradedCausalComplex::default();
        let points = vertices(&mut complex, length, "v");
        let edges = (0..length)
            .map(|index| {
                join(
                    &mut complex,
                    &format!("e{index}"),
                    points[index],
                    points[(index + 1) % length],
                )
            })
            .collect();
        (complex, points, edges)
    }

    fn path(length: usize) -> (GradedCausalComplex, Vec<CausalCellId>, Vec<CausalCellId>) {
        let mut complex = GradedCausalComplex::default();
        let points = vertices(&mut complex, length, "v");
        let edges = (1..length)
            .map(|index| {
                join(
                    &mut complex,
                    &format!("e{index}"),
                    points[index - 1],
                    points[index],
                )
            })
            .collect();
        (complex, points, edges)
    }

    /// Two disjoint paths. A dilation from one component never reaches the other, so the far
    /// component is genuinely outside every receiver's horizon — which is the only way to exercise
    /// the `Observation(0)` branch and the only way to build a population the receivers merge and
    /// the aperture can then split.
    fn two_pieces() -> (GradedCausalComplex, Vec<CausalCellId>, Vec<CausalCellId>) {
        let mut complex = GradedCausalComplex::default();
        let near = vertices(&mut complex, 3, "a");
        let far = vertices(&mut complex, 3, "b");
        let mut edges = Vec::new();
        for index in 1..3 {
            edges.push(join(
                &mut complex,
                &format!("ea{index}"),
                near[index - 1],
                near[index],
            ));
        }
        for index in 1..3 {
            edges.push(join(
                &mut complex,
                &format!("eb{index}"),
                far[index - 1],
                far[index],
            ));
        }
        let mut all = near;
        all.extend(far);
        (complex, all, edges)
    }

    fn unbounded(complex: &GradedCausalComplex, focus: CausalCellId) -> DilatedSection {
        dilate(complex, focus, Horizon::Unbounded, WalkOrder::Breadth).expect("the focus is a cell")
    }

    fn metric<'a>(
        complex: &'a GradedCausalComplex,
        receivers: Vec<DilatedSection>,
        inputs: Vec<CausalCellId>,
    ) -> ComplexSystem<'a> {
        ComplexSystem::declare(complex, AddressReading::Metric, receivers, inputs)
            .expect("the fixture declares a system this complex can honour")
    }

    fn block_of(partition: &Partition, cell: CausalCellId) -> usize {
        partition
            .block_of(item(cell))
            .expect("every cell of the complex is an item")
    }

    // ---------------------------------------------------------------- the address

    /// The `1 +`, **in both readings**. Without it the focus reads `0` and collides with everything
    /// outside the horizon, and the receiver would be unable to say where it is standing.
    ///
    /// The focus is at distance zero and at walk position zero, so the offset is load-bearing on
    /// exactly the same cell under either reading and the sweep must cover both. It did not until
    /// 2026-08-08 and a mutation dropping the chart offset survived the whole suite: every other
    /// chart assertion is about addresses *differing*, and collapsing the focus into the outside
    /// population leaves all of them intact.
    #[test]
    fn the_focus_is_addressable_and_never_collides_with_what_lies_outside() {
        let (complex, points, _) = path(6);
        for reading in [AddressReading::Metric, AddressReading::Chart] {
            let section =
                dilate(&complex, points[0], Horizon::Steps(2), WalkOrder::Breadth).unwrap();
            let system =
                ComplexSystem::declare(&complex, reading, vec![section], Vec::new()).unwrap();

            let focus = system.observation(item(points[0]), ReceiverId(0));
            let outside = system.observation(item(points[5]), ReceiverId(0));
            assert_eq!(
                focus,
                Observation(1),
                "under {reading:?} the focus sits at address one, not zero"
            );
            assert_eq!(
                outside,
                Observation(0),
                "under {reading:?} v5 is four graph steps away at horizon two"
            );
            assert_ne!(
                focus, outside,
                "under {reading:?} the focus and the unreachable must not share an address"
            );
        }
    }

    /// The two readings differ in **what they can see**, not only in how they number it.
    ///
    /// `dilate` returns `closure_added` — *"cells the walk did not choose but could not proceed
    /// without: the boundary closure"* — and those cells are in `support` and in `distance` but not
    /// in `reached`. So the metric reading gives them an address and the chart reading returns the
    /// outside token for them. That asymmetry is claimed at [`AddressReading::Chart`] and is
    /// measured here, on a fixture whose closure is asserted non-empty first: at horizon one from
    /// `v0`, the walk takes `e1` and is then obliged to close over `v1`, which it never walked to.
    #[test]
    fn the_chart_reading_returns_the_outside_token_for_what_the_walk_only_pivoted_off() {
        let (complex, points, edges) = path(6);
        let section = dilate(&complex, points[0], Horizon::Steps(1), WalkOrder::Breadth).unwrap();
        assert_eq!(
            section.lineage.closure_added,
            vec![points[1]],
            "the fixture must actually pivot off a cell it did not walk to, or neither reading is \
             being distinguished from the other"
        );
        assert_eq!(section.lineage.reached, vec![points[0], edges[0]]);
        assert!(section.support.contains(&points[1]));

        let by_metric = ComplexSystem::declare(
            &complex,
            AddressReading::Metric,
            vec![section.clone()],
            vec![],
        )
        .unwrap();
        let by_chart =
            ComplexSystem::declare(&complex, AddressReading::Chart, vec![section], vec![]).unwrap();

        assert_eq!(
            by_metric.observation(item(points[1]), ReceiverId(0)),
            Observation(3),
            "the metric reading addresses a pivoted-off cell by its distance, two incidence steps"
        );
        assert_eq!(
            by_chart.observation(item(points[1]), ReceiverId(0)),
            Observation(0),
            "and the chart reading cannot see it at all: it holds a walk, and the walk never went \
             there"
        );
        assert_eq!(
            by_chart.observation(item(edges[0]), ReceiverId(0)),
            Observation(2),
            "while a cell the walk did take carries its position"
        );
        assert_eq!(
            by_metric.observation(item(points[5]), ReceiverId(0)),
            by_chart.observation(item(points[5]), ReceiverId(0)),
            "the two readings agree only about what is outside the section entirely"
        );
    }

    /// The two branches must both be populated or the sweep proves nothing about either.
    #[test]
    fn inside_reads_nonzero_and_outside_reads_zero_with_both_populations_nonempty() {
        let (complex, points, _) = path(6);
        let section = dilate(&complex, points[0], Horizon::Steps(3), WalkOrder::Breadth).unwrap();
        let system = metric(&complex, vec![section], Vec::new());

        let mut inside = 0usize;
        let mut outside = 0usize;
        for id in complex.cells().keys() {
            let held = system.receivers[0].support.contains(id);
            let seen = system.observation(item(*id), ReceiverId(0));
            if held {
                inside += 1;
                assert_ne!(
                    seen,
                    Observation(0),
                    "cell {id:?} is held and must have an address"
                );
            } else {
                outside += 1;
                assert_eq!(
                    seen,
                    Observation(0),
                    "cell {id:?} is not held and must read zero"
                );
            }
        }
        assert!(inside > 0, "the restricted section must hold something");
        assert!(
            outside > 0,
            "the horizon must genuinely truncate, or the outside branch is never taken"
        );
    }

    /// The address is receiver-local. If two receivers agreed on every cell the family would be one
    /// receiver wearing two names, and the compression would have a single frame.
    #[test]
    fn two_receivers_return_different_addresses_for_the_same_cell() {
        let (complex, points, _) = path(6);
        let system = metric(
            &complex,
            vec![
                unbounded(&complex, points[0]),
                unbounded(&complex, points[5]),
            ],
            Vec::new(),
        );

        let near = system.observation(item(points[1]), ReceiverId(0));
        let far = system.observation(item(points[1]), ReceiverId(1));
        assert_eq!(
            near,
            Observation(3),
            "one graph step is two incidence steps"
        );
        assert_eq!(far, Observation(9), "four graph steps from the other end");
        assert_ne!(near, far, "the address is not a coordinate in the complex");

        let disagreements = complex
            .cells()
            .keys()
            .filter(|id| {
                system.observation(item(**id), ReceiverId(0))
                    != system.observation(item(**id), ReceiverId(1))
            })
            .count();
        assert!(
            disagreements > 0,
            "the two frames must actually differ somewhere"
        );
    }

    /// `addresses` returns the population whole, **including the cells the receiver cannot see**.
    ///
    /// The population is the artifact. A return restricted to the receiver's own support is the
    /// reduction `THE_ASSEMBLY.md` forbids: the outside block is the thing a narrow reading merges,
    /// and it cannot be exhibited from a return that omits it.
    #[test]
    fn the_address_population_is_whole_and_carries_the_cells_the_receiver_cannot_see() {
        let (complex, points, _) = two_pieces();
        let system = metric(&complex, vec![unbounded(&complex, points[0])], Vec::new());
        let addresses = system.addresses(ReceiverId(0));

        assert_eq!(
            addresses.len(),
            complex.cells().len(),
            "every cell of the complex has an address under this receiver, zero included"
        );
        assert_eq!(
            addresses.iter().map(|(id, _)| *id).collect::<Vec<_>>(),
            complex.cells().keys().copied().collect::<Vec<_>>(),
            "the population is returned in the complex's own identity order"
        );

        let outside: Vec<CausalCellId> = addresses
            .iter()
            .filter(|(_, address)| *address == Observation(0))
            .map(|(id, _)| *id)
            .collect();
        let inside: Vec<CausalCellId> = addresses
            .iter()
            .filter(|(_, address)| *address != Observation(0))
            .map(|(id, _)| *id)
            .collect();
        assert_eq!(
            outside.len(),
            5,
            "five of the ten cells are the far component, which this receiver cannot see: {outside:?}"
        );
        for far in &points[3..6] {
            assert!(
                outside.contains(far),
                "far vertex {far:?} must be IN the return at address zero, not dropped from it"
            );
        }
        assert_eq!(
            inside.len(),
            system.receivers[0].support.len(),
            "exactly the held cells read nonzero"
        );
        assert_eq!(
            inside.len() + outside.len(),
            complex.cells().len(),
            "and the two populations together are the whole complex"
        );
    }

    /// A receiver index past the declared family holds nothing and can distinguish nothing.
    ///
    /// Not defensive bookkeeping: `observation` and `addresses` are public trait surface a caller
    /// can drive with any `ReceiverId`, and a fabricated return here would enter the one-shot
    /// signature as a real distinction nothing in the complex paid for.
    #[test]
    fn an_undeclared_receiver_holds_nothing_and_distinguishes_nothing() {
        let (complex, points, edges) = cycle(5);
        let system = metric(&complex, vec![unbounded(&complex, points[0])], edges);
        let beyond = ReceiverId(system.receivers().len() as u64);

        for id in complex.cells().keys() {
            assert_eq!(
                system.observation(item(*id), beyond),
                Observation(0),
                "cell {id:?} must read zero for a receiver that was never declared"
            );
        }
        let addresses = system.addresses(beyond);
        assert_eq!(
            addresses.len(),
            complex.cells().len(),
            "the population is still whole; it is the addresses that are empty of content"
        );
        assert!(
            addresses
                .iter()
                .all(|(_, address)| *address == Observation(0)),
            "an undeclared receiver must not fabricate a row: {addresses:?}"
        );
        assert_eq!(
            addresses
                .iter()
                .map(|(_, address)| *address)
                .collect::<BTreeSet<_>>()
                .len(),
            1,
            "one address for every cell is no distinction at all"
        );
    }

    // ---------------------------------------------------------------- the crossing

    #[test]
    fn a_crossing_lands_on_the_far_end_and_a_non_incident_one_cell_is_a_terminus() {
        let (complex, points, edges) = path(4);
        let system = metric(&complex, Vec::new(), edges.clone());

        assert_eq!(system.crossing(points[0], edges[0]), Some(points[1]));
        assert_eq!(
            system.crossing(points[1], edges[0]),
            Some(points[0]),
            "a crossing is symmetric; the orientation names the ends, not a direction of travel"
        );
        assert_eq!(system.crossing(points[1], edges[1]), Some(points[2]));
        assert_eq!(
            system.crossing(points[0], edges[2]),
            None,
            "e3 is not incident to v0 and carries no step from it"
        );
        assert_eq!(
            system.crossing(edges[0], edges[1]),
            None,
            "a 1-cell is not an end of a 1-cell; conduct runs on the 1-skeleton"
        );
        assert_eq!(
            system.successor(item(points[0]), InputId(0)),
            Some(item(points[1])),
            "successor is the crossing, renamed"
        );
        assert_eq!(system.successor(item(points[0]), InputId(2)), None);
    }

    /// The grade guard in `crossing`, on the one shape that can fire it.
    ///
    /// Two parallel edges between one pair of vertices bound a 2-cell whose boundary is `[e] - [f]`
    /// — `found_cell` accepts it, since both faces are 1-cells and `boundary(boundary) = 0`. That
    /// 2-cell has **exactly two ends**, so every structural condition for a two-sided crossing holds
    /// and only the declared aperture refuses it. Without the guard this returns `f` from `e`, which
    /// is a step between two 1-cells and off the 1-skeleton entirely.
    #[test]
    fn a_two_cell_with_exactly_two_ends_still_carries_no_crossing() {
        let mut complex = GradedCausalComplex::default();
        let points = vertices(&mut complex, 2, "v");
        let left = join(&mut complex, "e", points[0], points[1]);
        let right = join(&mut complex, "f", points[0], points[1]);

        let mut face = CausalChain::default();
        face.add_term(left, ComparativeMultiplicity::positive(1u32));
        face.add_term(right, ComparativeMultiplicity::negative(1u32));
        let bigon = complex
            .found_cell("d", source(), 2, face)
            .expect("two parallel edges bound a closed 2-cell");

        let body = complex.cell(bigon).unwrap();
        assert_eq!(body.grade, 2);
        assert_eq!(
            body.boundary.support().len(),
            2,
            "the fixture must have exactly two ends, or the guard is not what refuses the crossing"
        );
        assert!(body.boundary.support().contains(&left));

        let system = metric(&complex, Vec::new(), vec![left, right]);
        assert_eq!(
            system.crossing(left, bigon),
            None,
            "a 2-cell is not an admitted step however two-sided it is"
        );
        assert_eq!(system.crossing(right, bigon), None);
        assert_eq!(
            system.crossing(points[0], left),
            Some(points[1]),
            "and the 1-cells of the same fixture still cross, so the refusal is the grade and not \
             the fixture being inert"
        );
    }

    /// A 1-cell whose boundary is `2[a]` has one end. A 1-cell whose boundary is `[a]+[b]-2[c]` has
    /// three, is admissible in this carrier, and must be **refused** a crossing rather than resolved
    /// by picking an end.
    #[test]
    fn a_one_ended_loop_rests_and_a_three_ended_one_cell_carries_no_crossing() {
        let mut complex = GradedCausalComplex::default();
        let points = vertices(&mut complex, 3, "v");

        let mut looped = CausalChain::default();
        looped.add_term(points[0], ComparativeMultiplicity::positive(2u32));
        let loop_cell = complex.found_cell("loop", source(), 1, looped).unwrap();

        let mut forked = CausalChain::default();
        forked.add_term(points[0], ComparativeMultiplicity::positive(1u32));
        forked.add_term(points[1], ComparativeMultiplicity::positive(1u32));
        forked.add_term(points[2], ComparativeMultiplicity::negative(2u32));
        let fork = complex.found_cell("fork", source(), 1, forked).unwrap();

        let mut opposed = CausalChain::default();
        opposed.add_term(points[1], ComparativeMultiplicity::positive(1u32));
        opposed.add_term(points[1], ComparativeMultiplicity::negative(1u32));
        let vanished = complex.found_cell("opposed", source(), 1, opposed).unwrap();

        let system = metric(&complex, Vec::new(), vec![loop_cell, fork, vanished]);

        assert_eq!(
            system.crossing(points[0], loop_cell),
            Some(points[0]),
            "a loop at v0 rests at v0"
        );
        assert_eq!(system.crossing(points[1], loop_cell), None);

        assert_eq!(
            complex.cell(fork).unwrap().boundary.support().len(),
            3,
            "the fixture must actually have three ends or the refusal is untested"
        );
        for end in [points[0], points[1], points[2]] {
            assert_eq!(
                system.crossing(end, fork),
                None,
                "three ends admit no two-sided crossing and must not be resolved by choosing one"
            );
        }

        let opposed_boundary = &complex.cell(vanished).unwrap().boundary;
        assert!(
            !opposed_boundary.is_zero(),
            "a loop at v1 is attached to v1 twice, once each hand — it does not vanish"
        );
        assert!(opposed_boundary.difference_is_zero());
        assert_eq!(
            system.crossing(points[1], vanished),
            Some(points[1]),
            "an opposed pair at v1 is a one-ended cell and rests there, exactly as 2[v0] does — \
             the two loop presentations are indistinguishable to a crossing, which is the point"
        );
    }

    // ---------------------------------------------------------------- the declaration

    #[test]
    fn a_non_one_cell_input_is_refused_rather_than_silently_dead() {
        let (mut complex, points, edges) = cycle(3);
        let mut face = CausalChain::default();
        face.add_term(edges[0], ComparativeMultiplicity::positive(1u32));
        face.add_term(edges[1], ComparativeMultiplicity::positive(1u32));
        face.add_term(edges[2], ComparativeMultiplicity::positive(1u32));
        let disc = complex.found_cell("disc", source(), 2, face).unwrap();

        let declare = |inputs: Vec<CausalCellId>| {
            ComplexSystem::declare(&complex, AddressReading::Metric, Vec::new(), inputs)
        };
        assert_eq!(
            declare(vec![disc]),
            Err(ComplexSystemError::InputNotAOneCell {
                cell: disc,
                grade: 2
            })
        );
        assert_eq!(
            declare(vec![points[0]]),
            Err(ComplexSystemError::InputNotAOneCell {
                cell: points[0],
                grade: 0
            })
        );
        assert_eq!(
            declare(vec![edges[0], edges[0]]),
            Err(ComplexSystemError::InputRepeated(edges[0]))
        );
        assert_eq!(
            declare(vec![CausalCellId(9999)]),
            Err(ComplexSystemError::InputAbsent(CausalCellId(9999)))
        );
        assert!(declare(edges).is_ok());
        assert_eq!(
            ComplexSystem::every_one_cell(&complex).len(),
            3,
            "the disc is grade two and is not an admitted step"
        );
    }

    /// A section measured on **another complex** is refused, in both species.
    ///
    /// This admitted such a section until 2026-08-08, validating only the focus. The consequence was
    /// not cosmetic: a cell of the receiving complex would be addressed by a chart that never
    /// measured it, and could read `Observation(0)` — "outside my horizon" — while the receiving
    /// complex's own geometry puts it two steps from the focus. The disagreement is exhibited below
    /// rather than asserted, so the fixture is proved capable of producing the wrong answer that the
    /// refusal now prevents.
    #[test]
    fn a_section_measured_on_another_complex_is_refused_and_the_frames_provably_disagree() {
        let (elsewhere, elsewhere_points, _) = path(9);
        let (here, here_points, here_edges) = cycle(4);

        // The two complexes were both grown from a fresh carrier, so they name cells from the same
        // identity sequence — which is exactly why a foreign section is silently plausible and has
        // to be refused rather than noticed by luck.
        assert_eq!(
            elsewhere_points[0], here_points[0],
            "the fixture depends on the two complexes sharing an identity, or nothing is admitted \
             to be caught"
        );

        let foreign = unbounded(&elsewhere, elsewhere_points[0]);
        match ComplexSystem::declare(
            &here,
            AddressReading::Metric,
            vec![foreign.clone()],
            here_edges.clone(),
        ) {
            Err(ComplexSystemError::ReceiverSectionForeign { receiver, cell }) => {
                assert_eq!(receiver, 0);
                assert!(
                    elsewhere.cell(cell).is_ok(),
                    "the refusal names a cell of the complex the section was measured on"
                );
                assert!(
                    here.cell(cell).is_err(),
                    "and not one of the complex it was handed to"
                );
            }
            other => panic!("a foreign section must be refused, got {other:?}"),
        }

        let absent = unbounded(&elsewhere, elsewhere_points[8]);
        assert_eq!(
            ComplexSystem::declare(
                &here,
                AddressReading::Metric,
                vec![absent],
                here_edges.clone()
            ),
            Err(ComplexSystemError::ReceiverFocusAbsent {
                receiver: 0,
                focus: elsewhere_points[8],
            }),
            "a focus this complex does not carry is refused by its own species, before the support"
        );

        // The positive control, and the disagreement the refusal prevents.
        let honest = metric(&here, vec![unbounded(&here, here_points[0])], here_edges);
        let disagreeing: Vec<CausalCellId> = here
            .cells()
            .keys()
            .copied()
            .filter(|id| {
                let mine = honest.observation(item(*id), ReceiverId(0));
                let theirs = foreign
                    .lineage
                    .distance
                    .get(id)
                    .map_or(Observation(0), |step| Observation(1 + u64::from(*step)));
                mine != theirs
            })
            .collect();
        assert!(
            !disagreeing.is_empty(),
            "the foreign chart must actually address these cells differently, or the refusal is \
             guarding nothing"
        );
    }

    // ---------------------------------------------------------------- the gauge

    /// The gauge law, with the half that can fail restored.
    ///
    /// `dilate` returns an invariant and a chart. The metric address is built from the invariant and
    /// must not move with the walk order; the chart address is built from the chart and **must**
    /// move with it. Until 2026-08-08 this module read only the invariant, so the second assertion
    /// was not merely absent — it was unstatable, and the first one compared `compress` against
    /// itself on two inputs that were equal in every field the adapter could observe.
    ///
    /// **Note which comparison carries which half.** The address populations differ under the two
    /// orders; the conduct *partitions* do not, under either reading — a walk position is injective
    /// over the walked cells, so the chart reading returns one singleton per walked cell whichever
    /// order produced it. So a partition comparison could never have detected the missing chart, and
    /// asserting the partition equality alone is what let the defect wear a passing result. Both are
    /// asserted here, with the partition equality named for what it is.
    #[test]
    fn the_metric_address_is_a_gauge_and_the_chart_address_is_not() {
        let (complex, points, edges) = cycle(7);
        let mut charts = BTreeSet::new();
        let mut metric_addresses = BTreeSet::new();
        let mut chart_addresses = BTreeSet::new();
        let mut metric_conduct: Option<Partition> = None;
        let mut chart_conduct: Option<Partition> = None;

        for order in WalkOrder::ALL {
            let section = dilate(&complex, points[0], Horizon::Steps(4), order).unwrap();
            charts.insert(section.lineage.reached.clone());

            let by_metric = metric(&complex, vec![section.clone()], edges.clone());
            let by_chart = ComplexSystem::declare(
                &complex,
                AddressReading::Chart,
                vec![section],
                edges.clone(),
            )
            .unwrap();

            metric_addresses.insert(by_metric.addresses(ReceiverId(0)));
            chart_addresses.insert(by_chart.addresses(ReceiverId(0)));

            let by_metric = compress(&by_metric).conduct;
            let by_chart = compress(&by_chart).conduct;
            match &metric_conduct {
                None => metric_conduct = Some(by_metric),
                Some(first) => assert_eq!(
                    *first, by_metric,
                    "the walk order moved the metric conduct classes; the address is not a gauge"
                ),
            }
            match &chart_conduct {
                None => chart_conduct = Some(by_chart),
                Some(first) => assert_eq!(
                    *first, by_chart,
                    "a walk position is injective, so the chart's PARTITION is order-independent \
                     even though its addresses are not — which is precisely why comparing \
                     partitions across orders cannot detect a dropped chart"
                ),
            }
        }

        assert_eq!(
            charts.len(),
            2,
            "breadth and depth must produce two charts, or this fixture cannot vary the property \
             under test at all"
        );
        assert_eq!(
            metric_addresses.len(),
            1,
            "the metric address population must be identical under both orders"
        );
        assert_eq!(
            chart_addresses.len(),
            2,
            "and the chart address population must DIFFER. If this is one, the adapter is not \
             reading `lineage.reached`, the invariance above is a self-comparison, and the second \
             frame has been deleted exactly as THE_ASSEMBLY's holistic constraint describes"
        );

        // The two readings of one section return two conducts, and the discriminator is metric.
        let by_metric = metric_conduct.expect("the sweep ran");
        let by_chart = chart_conduct.expect("the sweep ran");
        assert_ne!(
            by_metric, by_chart,
            "two readings of one section must return two conducts, or the reading is not a \
             coordinate"
        );
        assert_eq!(
            block_of(&by_metric, edges[0]),
            block_of(&by_metric, edges[6]),
            "e0 and e6 are the two 1-cells incident to the focus: one distance, one address, and \
             termini for every input, so the metric reading holds them together"
        );
        assert_ne!(
            block_of(&by_chart, edges[0]),
            block_of(&by_chart, edges[6]),
            "and the chart reading splits them, because a walk position is not a distance"
        );
        assert!(
            by_metric.len() < by_chart.len(),
            "the metric reading merges what the chart keeps apart: {} classes against {}",
            by_metric.len(),
            by_chart.len()
        );
        assert!(
            by_metric.len() < complex.cells().len(),
            "the metric address must merge something, or a discrete partition agrees with itself \
             under any walk order and the gauge claim is vacuous"
        );
    }

    // ---------------------------------------------------------------- the returns

    /// The case the module exists for, and the `CLAUDE.md` §8 control: the collapsed population is
    /// provably **nonzero**, its members are named, and the surviving identification is named too.
    ///
    /// One receiver at `v0` of a six-cycle reads the mirror symmetry `v1 <-> v5`, `v2 <-> v4`,
    /// `e0 <-> e5`, `e1 <-> e4`, `e2 <-> e3` — every mirror pair sits at one incidence distance and
    /// therefore at one address. Conduct separates the **vertex** pairs, because the inputs are
    /// named 1-cells and `e0` continues from `v1` while terminating from `v5`.
    ///
    /// **Only the vertex half is evidence about this organ.** The edge pairs survive because a
    /// 1-cell is a terminus for every input, and that is forced by `found_cell`'s grade law — no
    /// 1-cell can be an end of a 1-cell in any `GradedCausalComplex` — so no implementation that
    /// steps along boundary incidence could separate them. The edge assertions below record the
    /// declared aperture and carry no weight as a control; the load is on the vertex separation, on
    /// the exhibited collapsed population, and on the returned word being a step one side takes and
    /// the other does not.
    #[test]
    fn the_mirror_vertices_are_separated_by_conduct_and_the_mirror_edges_are_not() {
        let (complex, points, edges) = cycle(6);
        let system = metric(
            &complex,
            vec![unbounded(&complex, points[0])],
            edges.clone(),
        );
        let compression = compress(&system);

        assert_eq!(
            compression.one_shot.len(),
            7,
            "v0 | e0,e5 | v1,v5 | e1,e4 | v2,v4 | e2,e3 | v3"
        );
        assert_eq!(
            block_of(&compression.one_shot, points[1]),
            block_of(&compression.one_shot, points[5]),
            "one receiver at v0 cannot tell v1 from v5"
        );
        assert_eq!(
            block_of(&compression.one_shot, edges[1]),
            block_of(&compression.one_shot, edges[4]),
            "nor e1 from e4"
        );

        assert!(!compression.is_exact(), "the reading loses something");
        assert_eq!(
            compression.refinement(),
            2,
            "two vertex pairs split, no edge pair"
        );
        assert_eq!(compression.conduct.len(), 9);

        let separated: BTreeSet<(ItemId, ItemId)> = compression
            .collapsed
            .iter()
            .map(|pair| (pair.left, pair.right))
            .collect();
        assert_eq!(
            separated,
            BTreeSet::from([
                (item(points[1]), item(points[5])),
                (item(points[2]), item(points[4])),
            ]),
            "exactly the mirror vertex pairs, exhibited rather than counted"
        );

        // Aperture documentation, not a control: forced by `found_cell`'s grade law.
        assert_eq!(
            block_of(&compression.conduct, edges[1]),
            block_of(&compression.conduct, edges[4]),
        );
        assert_eq!(
            block_of(&compression.conduct, edges[2]),
            block_of(&compression.conduct, edges[3]),
        );

        let mirror = compression
            .collapsed
            .iter()
            .find(|pair| (pair.left, pair.right) == (item(points[1]), item(points[5])))
            .unwrap();
        assert_eq!(
            mirror.distinguishing_word.len(),
            1,
            "one named edge continues from v1 and terminates from v5"
        );
        assert!(
            mirror.separated_by_terminus,
            "the distinction is a terminus, and must be reported as one rather than as a \
             fabricated observation"
        );
        let step = system.inputs[mirror.distinguishing_word[0].0 as usize];
        assert!(
            system.crossing(points[1], step).is_some()
                != system.crossing(points[5], step).is_some(),
            "the returned word must actually be a step one side takes and the other does not"
        );
    }

    /// Widening the aperture refines, and narrowing it merges — with the same complex and the same
    /// receivers. The zero half and the nonzero half of one law, on one material.
    ///
    /// Every cell of the far component reads `Observation(0)`, so the receiver family merges the
    /// whole component into one block. At the near aperture the far cells are termini for every
    /// input and the block **survives conduct intact**: a genuinely identified population that is
    /// not a loss. Declaring the far component's own 1-cells splits it.
    #[test]
    fn a_population_the_receivers_merge_survives_a_narrow_aperture_and_splits_at_a_wide_one() {
        let (complex, points, edges) = two_pieces();
        let near_aperture = vec![edges[0], edges[1]];
        let wide_aperture = ComplexSystem::every_one_cell(&complex);
        assert_eq!(
            wide_aperture, edges,
            "the widest aperture is the complex's own 1-cells, in the order it founded them"
        );

        let narrow = metric(
            &complex,
            vec![unbounded(&complex, points[0])],
            near_aperture,
        );
        let narrow_reading = compress(&narrow);

        for far in &points[3..6] {
            assert_eq!(
                narrow.observation(item(*far), ReceiverId(0)),
                Observation(0),
                "a dilation from the near component never reaches the far one"
            );
        }
        assert_eq!(
            block_of(&narrow_reading.one_shot, points[3]),
            block_of(&narrow_reading.one_shot, points[5]),
            "the far component is one block to this receiver"
        );
        assert_eq!(
            block_of(&narrow_reading.conduct, points[3]),
            block_of(&narrow_reading.conduct, points[5]),
            "and the narrow aperture has no step that could tell them apart"
        );
        assert!(
            !narrow_reading
                .collapsed
                .iter()
                .any(|pair| pair.left == item(points[3]) && pair.right == item(points[5])),
            "an identification conduct cannot break is not a loss and must not be reported as one"
        );

        let wide = metric(
            &complex,
            vec![unbounded(&complex, points[0])],
            wide_aperture,
        );
        let wide_reading = compress(&wide);
        assert_ne!(
            block_of(&wide_reading.conduct, points[3]),
            block_of(&wide_reading.conduct, points[5]),
            "declaring the far component's own 1-cells separates its ends"
        );
        assert!(
            wide_reading.conduct.len() > narrow_reading.conduct.len(),
            "widening the aperture may only refine: {} -> {}",
            narrow_reading.conduct.len(),
            wide_reading.conduct.len()
        );
        let split = wide_reading
            .collapsed
            .iter()
            .find(|pair| (pair.left, pair.right) == (item(points[3]), item(points[5])))
            .expect("the pair the narrow reading kept is now an exhibited loss");
        assert_eq!(
            split.distinguishing_word.len(),
            1,
            "b0 crosses eb1 and b2 does not"
        );
    }

    /// The triple, end to end: a causal complex compressed, realized, and placed.
    ///
    /// The realizer population is the complex's **1-cells**, each reaching the ends it joins. That
    /// is a second frame and not the receivers' own: the receivers are dilated sections and the
    /// realizers are edges, so the standing/OPEN split is a real reading rather than a section
    /// auditing itself. It is provably nonzero on both sides — the vertices stand, the edges are
    /// OPEN because no edge is an end of an edge.
    ///
    /// **What paid is exhibited, not attested.** `every_standing_class_was_paid_for()` was asserted
    /// here until 2026-08-08 and cannot fail: `place` pushes a `StandingClass` only on the branch
    /// where `reached_by[class]` is non-empty and copies that same vector into `realizers`. The
    /// assertion was a theorem about `place` wearing the look of a measurement. What is measured
    /// instead is *which* realizers paid, against the incidence the fixture built.
    #[test]
    fn placement_through_a_causal_complex_stands_the_vertices_and_leaves_the_edges_open() {
        let (complex, points, edges) = cycle(5);
        let system = metric(
            &complex,
            vec![
                unbounded(&complex, points[0]),
                unbounded(&complex, points[1]),
            ],
            edges.clone(),
        );

        let realizers: Vec<RealizerId> = (0..edges.len() as u64).map(RealizerId).collect();
        let placed = place(&system, &realizers, |realizer| {
            complex
                .cell(edges[realizer.0 as usize])
                .unwrap()
                .boundary
                .support()
                .into_iter()
                .map(item)
                .collect()
        });

        assert!(
            !placed.standing.is_empty(),
            "the vertices are reached by their edges"
        );
        assert!(
            !placed.open.is_empty(),
            "no edge is an end of an edge, so every edge class is OPEN"
        );
        assert!(!placed.closed());

        for (index, vertex) in points.iter().enumerate() {
            let standing = placed
                .standing
                .iter()
                .find(|class| class.members.contains(&item(*vertex)))
                .unwrap_or_else(|| panic!("vertex {vertex:?} must stand"));
            let paid: BTreeSet<CausalCellId> = standing
                .realizers
                .iter()
                .map(|realizer| edges[realizer.0 as usize])
                .collect();
            assert_eq!(
                paid,
                BTreeSet::from([edges[index], edges[(index + edges.len() - 1) % edges.len()]]),
                "vertex {vertex:?} was paid for by exactly the two edges incident to it"
            );
        }

        let standing_cells: BTreeSet<CausalCellId> = placed
            .standing
            .iter()
            .flat_map(|class| class.members.iter().copied().map(cell))
            .collect();
        let open_cells: BTreeSet<CausalCellId> = placed
            .open
            .iter()
            .flat_map(|class| class.members.iter().copied().map(cell))
            .collect();
        assert!(
            standing_cells.is_disjoint(&open_cells),
            "a class stands or is OPEN, never both"
        );
        for vertex in &points {
            assert!(
                standing_cells.contains(vertex),
                "vertex {vertex:?} was reached"
            );
        }
        for edge in &edges {
            assert!(
                open_cells.contains(edge),
                "edge {edge:?} was reached by nothing"
            );
        }
        assert_eq!(
            standing_cells.len() + open_cells.len(),
            complex.cells().len(),
            "every cell of the complex is placed somewhere"
        );
    }

    /// A second frame on the same wiring: `smith_normal_form`, reached through `place`, reports the
    /// **bipartiteness of the complex's 1-skeleton**, and nothing on that path counts parity.
    ///
    /// The unsigned vertex-edge incidence of a connected graph has rank `n` when the graph is not
    /// bipartite and `n - 1` when it is. So a cycle of odd length must return `supported_rank = n`
    /// and one of even length `n - 1`. Both parities are swept, because a law checked on one of them
    /// returns a number that could not have come out otherwise.
    ///
    /// The claim is about the **vertex** columns, so the precondition — that two foci put every
    /// vertex in its own conduct class — is asserted rather than assumed. If it ever failed, two
    /// incidence columns would have been added together and the rank would be right by accident.
    #[test]
    fn the_supported_rank_reads_the_bipartiteness_of_the_one_skeleton_with_no_parity_check() {
        let mut torsion_seen = 0usize;
        let mut torsion_free_seen = 0usize;
        for length in 3..=8usize {
            let (complex, points, edges) = cycle(length);
            let system = metric(
                &complex,
                vec![
                    unbounded(&complex, points[0]),
                    unbounded(&complex, points[1]),
                ],
                edges.clone(),
            );
            let realizers: Vec<RealizerId> = (0..edges.len() as u64).map(RealizerId).collect();
            let placed = place(&system, &realizers, |realizer| {
                complex
                    .cell(edges[realizer.0 as usize])
                    .unwrap()
                    .boundary
                    .support()
                    .into_iter()
                    .map(item)
                    .collect()
            });

            let vertex_classes: BTreeSet<usize> = points
                .iter()
                .map(|vertex| block_of(&placed.compression.conduct, *vertex))
                .collect();
            assert_eq!(
                vertex_classes.len(),
                length,
                "two adjacent foci must separate every vertex of a {length}-cycle, or the rank \
                 claim is about columns that were summed"
            );

            let expected = if length % 2 == 1 { length } else { length - 1 };
            assert_eq!(
                placed.support.supported_rank,
                expected,
                "a {length}-cycle is {}bipartite and must have rank {expected}, got {}",
                if length % 2 == 0 { "" } else { "not " },
                placed.support.supported_rank,
            );
            // `class_extent - free_obstruction() == supported_rank` was asserted here until
            // 2026-08-08. `free_obstruction()` IS `class_extent - supported_rank`, so that read
            // `a - (a - b) == b` and could not fail. What can: exactly the vertex classes stand,
            // and the free obstruction exceeds the unreached population by the bipartite rank
            // deficiency, which is one on an even cycle and zero on an odd one.
            assert_eq!(
                placed.standing.len(),
                length,
                "exactly the {length} vertex classes were paid for; every edge class is unreached"
            );
            assert_eq!(
                placed.support.free_obstruction(),
                placed.open.len() + usize::from(length % 2 == 0),
                "the free obstruction is the unreached classes plus the rank deficiency of a \
                 bipartite incidence"
            );
            // Written first as "no torsion anywhere", which the odd cycles REFUSED. The returned
            // falsification is kept as the claim: an odd cycle's unsigned incidence is an `n x n`
            // integer matrix of determinant +-2, so its invariant factors are `1,...,1,2` and the
            // cokernel carries a `Z/2`. An even cycle is bipartite, drops to rank `n - 1`, and
            // carries none. Half the sweep must return nonzero and half must return empty, which is
            // `CLAUDE.md` §8's control on material where the property genuinely varies.
            let torsion = placed.support.torsion_obstruction();
            if length % 2 == 1 {
                assert_eq!(
                    torsion,
                    vec![BigInt::from(2)],
                    "a {length}-cycle is not bipartite; its incidence has determinant +-2 and the \
                     cokernel must carry Z/2"
                );
                torsion_seen += 1;
            } else {
                assert!(
                    torsion.is_empty(),
                    "a {length}-cycle is bipartite and its incidence is unimodular on its rank, \
                     got {torsion:?}"
                );
                torsion_free_seen += 1;
            }
            // `open.iter().all(|o| o.reached_only_in_multiple.is_none())` was asserted here and is
            // forced: `reaches` hands `place` a boundary SUPPORT, a set, so every landing is one and
            // the per-class gcd cannot exceed one. The reading is exercised where it can be nonzero
            // instead, by `a_class_two_ends_of_one_edge_share_is_reached_only_in_multiple`.
        }
        assert!(
            torsion_seen > 0,
            "the sweep must contain a nonzero torsion obstruction"
        );
        assert!(
            torsion_free_seen > 0,
            "and an empty one, or the comparison proves nothing"
        );
    }

    /// The declared control for `reached_only_in_multiple`, which the sweep above cannot exercise.
    ///
    /// `CLAUDE.md` §8: *a law that returns zero proves nothing about itself — when the declared
    /// material cannot exercise a law, add a declared control that does.* Here the aperture is empty,
    /// so conduct is the one-shot reading and the two mirror vertices of a triangle stay in one
    /// class; the single declared realizer is the edge joining them, which lands on that one class
    /// **twice**. The class is then reachable rationally and not integrally, which is the winding
    /// that cannot be un-deposited, and `place` must return it OPEN with the factor exhibited rather
    /// than standing.
    #[test]
    fn a_class_two_ends_of_one_edge_share_is_reached_only_in_multiple_and_the_factor_is_exhibited()
    {
        let (complex, points, edges) = cycle(3);
        let system = metric(&complex, vec![unbounded(&complex, points[0])], Vec::new());
        let reading = compress(&system);
        assert_eq!(
            block_of(&reading.conduct, points[1]),
            block_of(&reading.conduct, points[2]),
            "the fixture must merge the two ends of e1, or no realizer can land twice"
        );

        let placed = place(&system, &[RealizerId(0)], |_| {
            complex
                .cell(edges[1])
                .unwrap()
                .boundary
                .support()
                .into_iter()
                .map(item)
                .collect()
        });

        let merged = placed
            .open
            .iter()
            .find(|open| open.members.contains(&item(points[1])))
            .expect("the class the realizer reached must be returned");
        assert!(
            merged.members.contains(&item(points[2])),
            "and it must be the merged pair, not a singleton"
        );
        assert_eq!(
            merged.reached_only_in_multiple,
            Some(BigInt::from(2)),
            "reached, and only in multiple two: supported rationally and not integrally"
        );
        assert_eq!(placed.support.torsion_obstruction(), vec![BigInt::from(2)]);
        assert!(
            placed.standing.is_empty(),
            "the one realizer paid for nothing integrally, so nothing stands"
        );
        assert!(
            placed
                .open
                .iter()
                .any(|open| open.reached_only_in_multiple.is_none()),
            "and the other species is present too: classes nothing reached at all"
        );
    }

    /// The other half of the placement control: with no realizers declared, nothing stands. Without
    /// this the test above could be passing because `place` stands everything it is handed.
    #[test]
    fn a_complex_with_no_realizers_leaves_every_class_open() {
        let (complex, points, edges) = cycle(5);
        let system = metric(&complex, vec![unbounded(&complex, points[0])], edges);
        let placed = place(&system, &[], |_| Vec::new());
        assert!(placed.standing.is_empty());
        assert_eq!(placed.open.len(), placed.class_extent);
        assert!(
            placed.class_extent > 1,
            "the classes must be plural or this proves nothing"
        );
    }

    /// The seam is the identity on representations, the round trip is exact, and both returned
    /// populations come back in the complex's own identity order.
    ///
    /// The order is load-bearing downstream even though no partition can see it: `InputId(k)` names
    /// position `k` of the aperture, so a returned `distinguishing_word` is only readable back into
    /// cell names if the aperture is in a declared order, and a deposited `items()` is only
    /// comparable across runs for the same reason.
    #[test]
    fn the_seam_round_trips_and_both_returned_populations_are_in_identity_order() {
        let (complex, points, edges) = cycle(4);
        for id in complex.cells().keys() {
            assert_eq!(cell(item(*id)), *id);
        }
        let system = metric(&complex, Vec::new(), edges.clone());

        let founded: Vec<CausalCellId> = points.iter().chain(edges.iter()).copied().collect();
        assert_eq!(
            system.items(),
            founded.iter().copied().map(item).collect::<Vec<_>>(),
            "the item population is the cell population, in the order the fixture founded it"
        );
        assert_eq!(
            ComplexSystem::every_one_cell(&complex),
            edges,
            "and the widest aperture is the 1-cells in that same order"
        );
        assert_eq!(
            system
                .items()
                .into_iter()
                .map(cell)
                .collect::<BTreeSet<_>>(),
            complex.cells().keys().copied().collect::<BTreeSet<_>>()
        );
        assert_eq!(system.items().len(), points.len() + edges.len());
        assert_eq!(system.inputs().len(), edges.len());
        assert_eq!(system.receivers().len(), 0);
    }
}

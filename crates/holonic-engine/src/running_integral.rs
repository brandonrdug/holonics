//! Integration as an exact running sum, and the disagreement of two paths as a deposited holonomy.
//!
//! The deposit this module implements is
//! `research/records/2026-08-07_THE_INTEGRAL_IS_THE_PAIR_THE_DISAGREEMENT_IS_THE_HOLONOMY.md`,
//! which carries forward `Derive_Integration.lean`:
//!
//! > there is no continuum to subdivide; there is a LINEAGE of discrete events (windings), and
//! > **the area IS the exact running sum of them. No mesh, no limit, no error.**
//!
//! and `Derive_Limit.lean`:
//!
//! > the **PATH-INDEPENDENCE demand** ('every approach agrees') **IS the assumption of trivial
//! > cohomology** — it silently discards the soul.
//!
//! So the integral of a 1-cochain along a path is the running partial sum `I(n) = Σ_(k<n) w(k)`
//! over the oriented 1-cells traversed, and the honest return is **the sum together with its
//! path**. Two paths with the same endpoints are compared *as a pair*: their difference is the sum
//! of the cochain over the cycle they bound, and when that difference stands it is the holonomy.
//! It is returned, never averaged away, never refined away.
//!
//! ## What is exact and what stands
//!
//! Three properties of a 1-cochain `w` on a [`GradedCausalComplex`] are distinguished here, and
//! conflating them is the error this module is built to make impossible:
//!
//! ```text
//!   w is a COBOUNDARY   w = d f for a 0-cochain f   =>  every pair of paths agrees, and
//!                                                       the sum telescopes to f(end) - f(start)
//!   w is CLOSED         d w = 0 on every 2-cell     =>  the sum over any FILLED region vanishes
//!   w STANDS            some pair disagrees         =>  the residual IS the holonomy
//! ```
//!
//! Closed does not imply coboundary. The hollow square in the tests carries a cochain that is
//! closed — it has no 2-cells to obstruct it — and whose holonomy is exactly `1`. That gap is
//! `H^1 != 0`, and it is the whole content of the falsifier the record states:
//!
//! > if two enclosing paths always agree, the construction has assumed trivial cohomology and is
//! > the classical integral wearing new vocabulary.
//!
//! [`found_potential`] is what refuses to assume it. It walks a spanning tree of the 1-skeleton,
//! assigning the only potential the tree admits, and then TESTS every remaining chord. A chord
//! whose declared value disagrees with the potential the tree implies becomes a
//! [`ChordObstruction`] with an exact residual — retained, not repaired, not averaged into the
//! neighbouring assignments. `CLAUDE.md` §11 names this shape directly: the tree condenses for
//! free, subtree equals interval, and **the departure from a forest is the certified remainder**.
//! The chord population is that departure and the disagreeing chords are that remainder.
//!
//! ## Carrier and aperture
//!
//! Every value is a [`BigInt`] and every operation is exact addition, negation and multiplication
//! in `Z`. There is no float, no tolerance, no threshold, no score, and no averaging anywhere in
//! this module. A rational cochain is an integer cochain after clearing denominators, which
//! rescales every returned holonomy by the same cleared factor and moves no zero off zero.
//!
//! The declared aperture is **joinable 1-cells**: a traversed cell must have grade one and a
//! boundary of exactly one `+1` head and one `-1` tail. A self-incident 1-cell has an *empty*
//! boundary in this carrier — `+a` and `-a` cancel in [`ComparativeMultiplicity`] — so the
//! incidence does not retain its base point and a walk cannot join through it. That case is
//! refused by [`RunningIntegralError::UnjoinableCell`] rather than silently skipped, because
//! silently skipping a 1-cell would discard a winding.

use std::collections::{BTreeMap, BTreeSet, VecDeque};

use num_bigint::BigInt;
use num_traits::{One, Zero};
use serde::{Deserialize, Serialize};
use thiserror::Error;

use crate::algebraic::{
    CausalAlgebraicError, CausalCellId, CausalChain, ComparativeMultiplicity, GradedCausalComplex,
};

// ---------------------------------------------------------------------------------------------
// orientation

/// Which way a traversal crosses a 1-cell.
///
/// The cell carries one orientation in the incidence; a walk may cross it either way, and crossing
/// it against its own orientation negates its contribution. That sign is the only place a
/// direction enters the arithmetic.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum Orientation {
    /// From the cell's tail to its head.
    Along,
    /// From the cell's head to its tail.
    Against,
}

impl Orientation {
    pub const fn reversed(self) -> Self {
        match self {
            Self::Along => Self::Against,
            Self::Against => Self::Along,
        }
    }

    /// The coefficient this traversal contributes to a chain.
    pub fn multiplicity(self) -> ComparativeMultiplicity {
        match self {
            Self::Along => ComparativeMultiplicity::positive(1u32),
            Self::Against => ComparativeMultiplicity::negative(1u32),
        }
    }

    fn apply(self, value: BigInt) -> BigInt {
        match self {
            Self::Along => value,
            Self::Against => -value,
        }
    }
}

// ---------------------------------------------------------------------------------------------
// cochains

/// Exact values assigned to the cells of one declared grade.
///
/// An absent cell carries zero, exactly as [`CausalChain`] treats an absent coefficient. A stored
/// zero is removed on assignment so that two cochains are equal precisely when they assign equal
/// values everywhere.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Cochain {
    grade: u32,
    values: BTreeMap<CausalCellId, BigInt>,
}

impl Cochain {
    pub fn new(grade: u32) -> Self {
        Self {
            grade,
            values: BTreeMap::new(),
        }
    }

    /// A cochain from `(cell, value)` pairs at one grade.
    pub fn from_values<I>(grade: u32, values: I) -> Self
    where
        I: IntoIterator<Item = (CausalCellId, BigInt)>,
    {
        let mut cochain = Self::new(grade);
        for (cell, value) in values {
            cochain.set(cell, value);
        }
        cochain
    }

    pub const fn grade(&self) -> u32 {
        self.grade
    }

    pub const fn values(&self) -> &BTreeMap<CausalCellId, BigInt> {
        &self.values
    }

    pub fn value(&self, cell: CausalCellId) -> BigInt {
        self.values.get(&cell).cloned().unwrap_or_else(BigInt::zero)
    }

    pub fn set(&mut self, cell: CausalCellId, value: BigInt) {
        if value.is_zero() {
            self.values.remove(&cell);
        } else {
            self.values.insert(cell, value);
        }
    }

    pub fn support(&self) -> BTreeSet<CausalCellId> {
        self.values.keys().copied().collect()
    }

    pub fn is_zero(&self) -> bool {
        self.values.is_empty()
    }

    pub fn negated(&self) -> Self {
        Self {
            grade: self.grade,
            values: self
                .values
                .iter()
                .map(|(cell, value)| (*cell, -value.clone()))
                .collect(),
        }
    }

    /// Pointwise sum. Refuses two cochains of different grades, since they pair with different
    /// chain groups and their sum names nothing.
    pub fn plus(&self, other: &Self) -> Result<Self, RunningIntegralError> {
        if self.grade != other.grade {
            return Err(RunningIntegralError::CochainGradesDiffer {
                left: self.grade,
                right: other.grade,
            });
        }
        let mut result = self.clone();
        for (cell, value) in &other.values {
            result.set(*cell, result.value(*cell) + value);
        }
        Ok(result)
    }

    pub fn minus(&self, other: &Self) -> Result<Self, RunningIntegralError> {
        self.plus(&other.negated())
    }

    /// The pairing `<cochain, chain>`: the exact sum of `value(cell) * coefficient(cell)`.
    ///
    /// Every cell in the chain must sit at this cochain's grade. That refusal is what keeps a
    /// 1-cochain from being read against a 2-chain and returning a number that means nothing.
    pub fn evaluate(
        &self,
        complex: &GradedCausalComplex,
        chain: &CausalChain,
    ) -> Result<BigInt, RunningIntegralError> {
        let mut total = BigInt::zero();
        for (cell, coefficient) in chain.coefficients() {
            let body = complex.cell(*cell)?;
            if body.grade != self.grade {
                return Err(RunningIntegralError::PairingGrade {
                    cochain: self.grade,
                    cell: body.grade,
                    id: *cell,
                });
            }
            total += self.value(*cell) * coefficient.difference();
        }
        Ok(total)
    }
}

/// The coboundary `d`, defined by `(d w)(c) = w(boundary c)`.
///
/// This is the adjoint of the incidence boundary, so `d d = 0` follows from `boundary boundary = 0`
/// — which the complex already refuses to violate at construction. Every cell one grade above the
/// cochain is visited, so the returned cochain is total on its grade.
pub fn coboundary(
    complex: &GradedCausalComplex,
    cochain: &Cochain,
) -> Result<Cochain, RunningIntegralError> {
    let grade = cochain
        .grade
        .checked_add(1)
        .ok_or(RunningIntegralError::GradeOverflow)?;
    let mut result = Cochain::new(grade);
    for cell in complex.cells().values().filter(|cell| cell.grade == grade) {
        let value = cochain.evaluate(complex, &cell.boundary)?;
        result.set(cell.id, value);
    }
    Ok(result)
}

/// Whether `d w = 0` on this complex.
///
/// Closed is weaker than coboundary. A complex with no cells above the cochain's grade makes every
/// cochain vacuously closed while leaving its holonomy entirely free, which is precisely the case
/// the falsifier is about.
pub fn is_closed(
    complex: &GradedCausalComplex,
    cochain: &Cochain,
) -> Result<bool, RunningIntegralError> {
    Ok(coboundary(complex, cochain)?.is_zero())
}

// ---------------------------------------------------------------------------------------------
// paths

/// One crossing of one 1-cell.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct PathStep {
    pub cell: CausalCellId,
    pub orientation: Orientation,
}

impl PathStep {
    pub const fn along(cell: CausalCellId) -> Self {
        Self {
            cell,
            orientation: Orientation::Along,
        }
    }

    pub const fn against(cell: CausalCellId) -> Self {
        Self {
            cell,
            orientation: Orientation::Against,
        }
    }

    pub const fn reversed(self) -> Self {
        Self {
            cell: self.cell,
            orientation: self.orientation.reversed(),
        }
    }
}

/// An ordered traversal of oriented 1-cells.
///
/// The order is retained because it is the lineage. Two paths whose [`Path::chain`] agree may still
/// be different traversals, and a path that backtracks is not the same object as the path that does
/// not — even though the two return the same total.
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct Path {
    steps: Vec<PathStep>,
}

impl Path {
    pub fn new<I>(steps: I) -> Self
    where
        I: IntoIterator<Item = PathStep>,
    {
        Self {
            steps: steps.into_iter().collect(),
        }
    }

    /// A path crossing every named cell along its own orientation.
    pub fn along<I>(cells: I) -> Self
    where
        I: IntoIterator<Item = CausalCellId>,
    {
        Self::new(cells.into_iter().map(PathStep::along))
    }

    pub fn steps(&self) -> &[PathStep] {
        &self.steps
    }

    pub fn len(&self) -> usize {
        self.steps.len()
    }

    pub fn is_empty(&self) -> bool {
        self.steps.is_empty()
    }

    /// The same traversal walked backwards.
    pub fn reversed(&self) -> Self {
        Self {
            steps: self.steps.iter().rev().map(|step| step.reversed()).collect(),
        }
    }

    /// This traversal followed by another. No join check happens here; the check happens when the
    /// path is walked, which is the only place the incidence is available.
    pub fn then(&self, other: &Self) -> Self {
        let mut steps = self.steps.clone();
        steps.extend_from_slice(&other.steps);
        Self { steps }
    }

    /// The 1-chain this traversal carries. Repetition accumulates and backtracking cancels, because
    /// a chain is a group element and not a list.
    pub fn chain(&self) -> CausalChain {
        let mut chain = CausalChain::default();
        for step in &self.steps {
            chain.add_term(step.cell, step.orientation.multiplicity());
        }
        chain
    }

    /// The vertex the walk departs and the vertex it arrives at, refusing a walk that does not join.
    pub fn endpoints(
        &self,
        complex: &GradedCausalComplex,
    ) -> Result<(CausalCellId, CausalCellId), RunningIntegralError> {
        let mut standing: Option<(CausalCellId, CausalCellId)> = None;
        for (index, step) in self.steps.iter().enumerate() {
            let (departed, arrived) = traversed_ends(complex, *step)?;
            standing = Some(match standing {
                None => (departed, arrived),
                Some((start, at)) if at == departed => (start, arrived),
                Some((_, at)) => {
                    return Err(RunningIntegralError::PathDoesNotJoin {
                        index,
                        standing_at: at,
                        departs: departed,
                    });
                }
            });
        }
        standing.ok_or(RunningIntegralError::EmptyPath)
    }

    pub fn is_closed(
        &self,
        complex: &GradedCausalComplex,
    ) -> Result<bool, RunningIntegralError> {
        let (start, end) = self.endpoints(complex)?;
        Ok(start == end)
    }
}

/// The tail and head of a 1-cell, read from its own boundary.
///
/// `boundary(e) = head - tail` with both coefficients at unit orientation. Anything else is outside
/// this organ's declared aperture and is refused rather than approximated.
fn oriented_edge_ends(
    complex: &GradedCausalComplex,
    cell: CausalCellId,
) -> Result<(CausalCellId, CausalCellId), RunningIntegralError> {
    let body = complex.cell(cell)?;
    if body.grade != 1 {
        return Err(RunningIntegralError::UnjoinableCell(cell));
    }
    let mut tail = None;
    let mut head = None;
    for (vertex, coefficient) in body.boundary.coefficients() {
        if !coefficient.is_unit_orientation() {
            return Err(RunningIntegralError::UnjoinableCell(cell));
        }
        let slot = if coefficient.difference().is_one() {
            &mut head
        } else {
            &mut tail
        };
        if slot.replace(*vertex).is_some() {
            return Err(RunningIntegralError::UnjoinableCell(cell));
        }
    }
    match (tail, head) {
        (Some(tail), Some(head)) => Ok((tail, head)),
        _ => Err(RunningIntegralError::UnjoinableCell(cell)),
    }
}

/// Where one step departs and where it arrives, after its orientation is applied.
fn traversed_ends(
    complex: &GradedCausalComplex,
    step: PathStep,
) -> Result<(CausalCellId, CausalCellId), RunningIntegralError> {
    let (tail, head) = oriented_edge_ends(complex, step.cell)?;
    Ok(match step.orientation {
        Orientation::Along => (tail, head),
        Orientation::Against => (head, tail),
    })
}

// ---------------------------------------------------------------------------------------------
// the running sum

/// One winding of the running sum, with the accumulated value standing after it.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct IntegralStep {
    pub index: usize,
    pub cell: CausalCellId,
    pub orientation: Orientation,
    pub departed: CausalCellId,
    pub arrived: CausalCellId,
    /// The cochain's value on this cell, negated when the crossing is against its orientation.
    pub increment: BigInt,
    /// `I(index + 1)` — the partial sum standing after this winding.
    pub accumulated: BigInt,
}

/// The return of an integration: the accumulated value **together with its path**.
///
/// Collapsing this to `total` alone is exactly the discard the record convicts. The lineage is kept
/// so that two traversals returning the same total remain distinguishable.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct RunningIntegral {
    pub schema: String,
    pub start: CausalCellId,
    pub end: CausalCellId,
    pub steps: Vec<IntegralStep>,
    pub total: BigInt,
}

impl RunningIntegral {
    /// The lineage `[I(0), I(1), ..., I(n)]`, opening at rest.
    pub fn partial_sums(&self) -> Vec<BigInt> {
        std::iter::once(BigInt::zero())
            .chain(self.steps.iter().map(|step| step.accumulated.clone()))
            .collect()
    }

    /// The traversal this integral was taken along, recovered from the return itself.
    pub fn path(&self) -> Path {
        Path::new(self.steps.iter().map(|step| PathStep {
            cell: step.cell,
            orientation: step.orientation,
        }))
    }

    pub fn is_zero(&self) -> bool {
        self.total.is_zero()
    }
}

/// The integral of a 1-cochain along a path: the exact running partial sum of its values on the
/// cells traversed.
///
/// No mesh, no limit, no error term. The walk is refused if it does not join, if a traversed cell
/// is outside the joinable aperture, or if the cochain does not sit at grade one.
pub fn running_sum(
    complex: &GradedCausalComplex,
    cochain: &Cochain,
    path: &Path,
) -> Result<RunningIntegral, RunningIntegralError> {
    if cochain.grade != 1 {
        return Err(RunningIntegralError::NotAOneCochain(cochain.grade));
    }
    if path.is_empty() {
        return Err(RunningIntegralError::EmptyPath);
    }

    let mut steps = Vec::with_capacity(path.len());
    let mut accumulated = BigInt::zero();
    let mut start = None;
    let mut standing: Option<CausalCellId> = None;

    for (index, step) in path.steps.iter().enumerate() {
        let (departed, arrived) = traversed_ends(complex, *step)?;
        match standing {
            None => start = Some(departed),
            Some(at) if at == departed => {}
            Some(at) => {
                return Err(RunningIntegralError::PathDoesNotJoin {
                    index,
                    standing_at: at,
                    departs: departed,
                });
            }
        }
        let increment = step.orientation.apply(cochain.value(step.cell));
        accumulated += &increment;
        steps.push(IntegralStep {
            index,
            cell: step.cell,
            orientation: step.orientation,
            departed,
            arrived,
            increment,
            accumulated: accumulated.clone(),
        });
        standing = Some(arrived);
    }

    Ok(RunningIntegral {
        schema: "holonic-engine.running-integral.v1".to_owned(),
        start: start.ok_or(RunningIntegralError::EmptyPath)?,
        end: standing.ok_or(RunningIntegralError::EmptyPath)?,
        steps,
        total: accumulated,
    })
}

/// The integral around a closed traversal. Refuses a walk that does not return to its departure.
pub fn holonomy(
    complex: &GradedCausalComplex,
    cochain: &Cochain,
    loop_path: &Path,
) -> Result<RunningIntegral, RunningIntegralError> {
    let integral = running_sum(complex, cochain, loop_path)?;
    if integral.start != integral.end {
        return Err(RunningIntegralError::PathIsNotClosed {
            start: integral.start,
            end: integral.end,
        });
    }
    Ok(integral)
}

// ---------------------------------------------------------------------------------------------
// the pair

/// What a compared pair returned.
///
/// `Agreed` is a statement about **this pair on this cochain** and nothing wider. It does not say
/// the cochain is a coboundary, and it must never be read as one; [`found_potential`] is what
/// decides that question over the whole reached component.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum PairReturn {
    /// The two traversals returned the same sum. On this pair the cochain admits a potential.
    Agreed,
    /// The two traversals returned different sums. The difference stands; it is the holonomy of the
    /// cycle they bound, and it is deposited here rather than refined away.
    Holonomy(BigInt),
}

/// Two traversals with common endpoints, compared as a pair, with both lineages retained.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Disagreement {
    pub schema: String,
    pub start: CausalCellId,
    pub end: CausalCellId,
    pub left: RunningIntegral,
    pub right: RunningIntegral,
    /// `chain(left) - chain(right)`. A cycle, because both walks join the same two vertices.
    pub cycle: CausalChain,
    /// `total(left) - total(right)`. The standing residual.
    pub residual: BigInt,
}

impl Disagreement {
    pub fn stands(&self) -> bool {
        !self.residual.is_zero()
    }

    pub fn verdict(&self) -> PairReturn {
        if self.stands() {
            PairReturn::Holonomy(self.residual.clone())
        } else {
            PairReturn::Agreed
        }
    }

    /// Whether the two traversals are distinguishable as chains at all.
    ///
    /// A pair whose cycle is zero cannot disagree on any cochain, so a fixture built from such a
    /// pair is incapable of exercising the property this module exists to test.
    pub fn paths_are_distinct(&self) -> bool {
        !self.cycle.is_zero()
    }
}

/// Compare two traversals sharing both endpoints and return their exact standing residual.
pub fn disagreement(
    complex: &GradedCausalComplex,
    cochain: &Cochain,
    left: &Path,
    right: &Path,
) -> Result<Disagreement, RunningIntegralError> {
    let left_integral = running_sum(complex, cochain, left)?;
    let right_integral = running_sum(complex, cochain, right)?;
    if left_integral.start != right_integral.start || left_integral.end != right_integral.end {
        return Err(RunningIntegralError::EndpointsDiffer {
            left: (left_integral.start, left_integral.end),
            right: (right_integral.start, right_integral.end),
        });
    }

    let cycle = left.chain().minus(&right.chain());
    if !complex.boundary_of_chain(&cycle)?.is_zero() {
        return Err(RunningIntegralError::PairIsNotACycle);
    }

    let residual = left_integral.total.clone() - right_integral.total.clone();
    Ok(Disagreement {
        schema: "holonic-engine.integral-disagreement.v1".to_owned(),
        start: left_integral.start,
        end: left_integral.end,
        left: left_integral,
        right: right_integral,
        cycle,
        residual,
    })
}

/// A compared pair together with a 2-chain whose boundary is exactly the cycle they bound.
///
/// The three integers here are computed three different ways and the theorem is that they agree:
/// the difference of two running sums, the cochain paired with the region's boundary, and the
/// cochain's coboundary paired with the region.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct EnclosedPair {
    pub schema: String,
    pub disagreement: Disagreement,
    pub region: CausalChain,
    pub region_boundary: CausalChain,
    /// `<w, boundary region>` — the sum over the region's boundary.
    pub boundary_residual: BigInt,
    /// `<d w, region>` — the same number reached by building the coboundary first.
    pub coboundary_residual: BigInt,
}

impl EnclosedPair {
    /// All three readings agree. This is a checkable equality, not a definition: the two region
    /// readings traverse different data, so a sign or grade error in either shows up here.
    pub fn readings_agree(&self) -> bool {
        self.disagreement.residual == self.boundary_residual
            && self.boundary_residual == self.coboundary_residual
    }
}

/// Compare a pair and read the same residual off a declared enclosing region.
///
/// The region must be a chain one grade above the cochain whose boundary is *exactly* the cycle the
/// pair bounds. A region that does not enclose is refused, because reading a residual off the wrong
/// region returns a number that answers a different question.
pub fn enclosed_disagreement(
    complex: &GradedCausalComplex,
    cochain: &Cochain,
    left: &Path,
    right: &Path,
    region: &CausalChain,
) -> Result<EnclosedPair, RunningIntegralError> {
    let expected = cochain
        .grade
        .checked_add(1)
        .ok_or(RunningIntegralError::GradeOverflow)?;
    if let Some(grade) = complex.homogeneous_grade(region)?
        && grade != expected
    {
        return Err(RunningIntegralError::RegionGrade {
            region: grade,
            expected,
        });
    }

    let disagreement = disagreement(complex, cochain, left, right)?;
    let region_boundary = complex.boundary_of_chain(region)?;
    if region_boundary != disagreement.cycle {
        return Err(RunningIntegralError::RegionDoesNotEnclose);
    }

    let boundary_residual = cochain.evaluate(complex, &region_boundary)?;
    let coboundary_residual = coboundary(complex, cochain)?.evaluate(complex, region)?;

    Ok(EnclosedPair {
        schema: "holonic-engine.enclosed-integral-pair.v1".to_owned(),
        disagreement,
        region: region.clone(),
        region_boundary,
        boundary_residual,
        coboundary_residual,
    })
}

// ---------------------------------------------------------------------------------------------
// the potential, and the chords it cannot repair

/// A chord whose declared value disagrees with the potential the spanning tree implies.
///
/// The residual is the holonomy of the fundamental cycle that chord closes. It is retained here
/// exactly, with its own address, and nothing in this module ever folds it back into the potential.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ChordObstruction {
    pub cell: CausalCellId,
    pub tail: CausalCellId,
    pub head: CausalCellId,
    /// `w(e)`.
    pub declared: BigInt,
    /// `f(head) - f(tail)` from the tree's potential.
    pub implied: BigInt,
    /// `declared - implied`. Nonzero by construction of this variant.
    pub residual: BigInt,
}

/// The search for a 0-cochain whose coboundary is the given 1-cochain, and the remainder it leaves.
///
/// A spanning tree determines the potential uniquely once a base is fixed. Every remaining chord is
/// then a test that can fail. The chords are the departure from a forest; the failing chords are the
/// certified remainder.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct PotentialSearch {
    pub schema: String,
    pub base: CausalCellId,
    /// Grade-zero, valued zero at the base.
    pub potential: Cochain,
    pub reached: BTreeSet<CausalCellId>,
    pub tree_cells: BTreeSet<CausalCellId>,
    /// Chords whose declared value already matched the tree's potential.
    pub agreeing_chords: BTreeSet<CausalCellId>,
    /// Chords whose declared value did not. Retained, never averaged.
    pub retained_obstructions: Vec<ChordObstruction>,
    /// 1-cells in the complex that this component never touched.
    pub unreached_cells: BTreeSet<CausalCellId>,
}

impl PotentialSearch {
    /// The cochain is a coboundary on the reached component exactly when nothing was retained.
    pub fn admits_a_potential(&self) -> bool {
        self.retained_obstructions.is_empty()
    }

    /// The number of independent cycles the reached component carries: its departure from a tree.
    pub fn cycle_rank(&self) -> usize {
        self.agreeing_chords.len() + self.retained_obstructions.len()
    }

    /// The exact residuals standing after the search, in chord order.
    pub fn standing_residuals(&self) -> Vec<BigInt> {
        self.retained_obstructions
            .iter()
            .map(|chord| chord.residual.clone())
            .collect()
    }
}

/// Walk a spanning tree of the 1-skeleton from `base`, assign the only potential it admits, and
/// test every chord.
///
/// Deterministic: the incidence lists are built in cell-identity order and the frontier is walked
/// breadth-first, so the tree, the chord set and the retained residuals are a function of the
/// complex and the base alone.
pub fn found_potential(
    complex: &GradedCausalComplex,
    cochain: &Cochain,
    base: CausalCellId,
) -> Result<PotentialSearch, RunningIntegralError> {
    if cochain.grade != 1 {
        return Err(RunningIntegralError::NotAOneCochain(cochain.grade));
    }
    if complex.cell(base)?.grade != 0 {
        return Err(RunningIntegralError::BaseIsNotAVertex(base));
    }

    let mut incident: BTreeMap<CausalCellId, Vec<(CausalCellId, CausalCellId, CausalCellId)>> =
        BTreeMap::new();
    let mut every_cell = BTreeSet::new();
    for cell in complex.cells().values().filter(|cell| cell.grade == 1) {
        let (tail, head) = oriented_edge_ends(complex, cell.id)?;
        every_cell.insert(cell.id);
        incident.entry(tail).or_default().push((cell.id, tail, head));
        incident.entry(head).or_default().push((cell.id, tail, head));
    }

    let mut assigned: BTreeMap<CausalCellId, BigInt> = BTreeMap::new();
    assigned.insert(base, BigInt::zero());
    let mut tree_cells = BTreeSet::new();
    let mut agreeing_chords = BTreeSet::new();
    let mut retained_obstructions = Vec::new();
    let mut considered = BTreeSet::new();
    let mut frontier = VecDeque::from([base]);

    while let Some(vertex) = frontier.pop_front() {
        let Some(edges) = incident.get(&vertex) else {
            continue;
        };
        for (cell, tail, head) in edges.clone() {
            if !considered.insert(cell) {
                continue;
            }
            let here = assigned
                .get(&vertex)
                .cloned()
                .ok_or(RunningIntegralError::UnjoinableCell(cell))?;
            let declared = cochain.value(cell);
            // w = d f means w(e) = f(head) - f(tail).
            let (far, implied_there) = if vertex == tail {
                (head, here + &declared)
            } else {
                (tail, here - &declared)
            };
            match assigned.get(&far) {
                None => {
                    assigned.insert(far, implied_there);
                    tree_cells.insert(cell);
                    frontier.push_back(far);
                }
                Some(_) => {
                    let implied = assigned
                        .get(&head)
                        .cloned()
                        .unwrap_or_else(BigInt::zero)
                        - assigned.get(&tail).cloned().unwrap_or_else(BigInt::zero);
                    let residual = declared.clone() - implied.clone();
                    if residual.is_zero() {
                        agreeing_chords.insert(cell);
                    } else {
                        retained_obstructions.push(ChordObstruction {
                            cell,
                            tail,
                            head,
                            declared,
                            implied,
                            residual,
                        });
                    }
                }
            }
        }
    }

    let reached: BTreeSet<CausalCellId> = assigned.keys().copied().collect();
    let potential = Cochain::from_values(0, assigned);
    let unreached_cells = every_cell.difference(&considered).copied().collect();

    Ok(PotentialSearch {
        schema: "holonic-engine.integral-potential-search.v1".to_owned(),
        base,
        potential,
        reached,
        tree_cells,
        agreeing_chords,
        retained_obstructions,
        unreached_cells,
    })
}

// ---------------------------------------------------------------------------------------------
// refusals

#[derive(Debug, Error)]
pub enum RunningIntegralError {
    #[error(transparent)]
    Incidence(#[from] CausalAlgebraicError),
    #[error("this organ integrates along one-cells; the supplied cochain has grade {0}")]
    NotAOneCochain(u32),
    #[error("a grade-{cochain} cochain cannot be paired with grade-{cell} cell {id:?}")]
    PairingGrade {
        cochain: u32,
        cell: u32,
        id: CausalCellId,
    },
    #[error("cochains of grade {left} and {right} pair with different chain groups")]
    CochainGradesDiffer { left: u32, right: u32 },
    #[error(
        "cell {0:?} is not a joinable one-cell: it must carry exactly one +1 head and one -1 tail"
    )]
    UnjoinableCell(CausalCellId),
    #[error("step {index} departs {departs:?} while the walk stands at {standing_at:?}")]
    PathDoesNotJoin {
        index: usize,
        standing_at: CausalCellId,
        departs: CausalCellId,
    },
    #[error("an empty traversal has no endpoints and returns nothing to compare")]
    EmptyPath,
    #[error("the traversal departs {start:?} and arrives {end:?}; it is not closed")]
    PathIsNotClosed {
        start: CausalCellId,
        end: CausalCellId,
    },
    #[error("the compared traversals have different endpoints: {left:?} against {right:?}")]
    EndpointsDiffer {
        left: (CausalCellId, CausalCellId),
        right: (CausalCellId, CausalCellId),
    },
    #[error("the compared pair does not bound a cycle; the traversal joining is inconsistent")]
    PairIsNotACycle,
    #[error("the declared region has grade {region}, not {expected}")]
    RegionGrade { region: u32, expected: u32 },
    #[error("the declared region's boundary is not the cycle the compared pair bounds")]
    RegionDoesNotEnclose,
    #[error("a cochain grade exceeded its carrier")]
    GradeOverflow,
    #[error("the base cell {0:?} is not a grade-zero cell")]
    BaseIsNotAVertex(CausalCellId),
}

// ---------------------------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::causal::EventId;
    use num_traits::Signed;

    fn source() -> BTreeSet<EventId> {
        BTreeSet::from([EventId(1)])
    }

    fn vertex(complex: &mut GradedCausalComplex, name: &str) -> CausalCellId {
        complex
            .found_cell(name, source(), 0, CausalChain::default())
            .expect("a vertex carries no boundary")
    }

    fn edge(
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

    fn big(value: i64) -> BigInt {
        BigInt::from(value)
    }

    /// The fixture the falsifier needs. Four vertices, four edges, no filling:
    ///
    /// ```text
    ///        ab          bc
    ///   a --------> b --------> c
    ///   |                       ^
    ///   | ad                    | dc
    ///   v                       |
    ///   d ----------------------+
    /// ```
    ///
    /// Two traversals from `a` to `c` that are genuinely distinct as chains, and a hole between
    /// them. A single-path complex could not exercise path dependence at all; this one can, and
    /// `the_fixture_returns_both_verdicts` is what holds it to that.
    struct Square {
        complex: GradedCausalComplex,
        a: CausalCellId,
        b: CausalCellId,
        c: CausalCellId,
        d: CausalCellId,
        ab: CausalCellId,
        bc: CausalCellId,
        ad: CausalCellId,
        dc: CausalCellId,
    }

    impl Square {
        fn hollow() -> Self {
            let mut complex = GradedCausalComplex::default();
            let a = vertex(&mut complex, "a");
            let b = vertex(&mut complex, "b");
            let c = vertex(&mut complex, "c");
            let d = vertex(&mut complex, "d");
            let ab = edge(&mut complex, "ab", a, b);
            let bc = edge(&mut complex, "bc", b, c);
            let ad = edge(&mut complex, "ad", a, d);
            let dc = edge(&mut complex, "dc", d, c);
            Self {
                complex,
                a,
                b,
                c,
                d,
                ab,
                bc,
                ad,
                dc,
            }
        }

        /// The same square with the hole filled by one 2-cell whose boundary is the cycle the pair
        /// bounds: `ab + bc - dc - ad`.
        fn filled() -> (Self, CausalCellId) {
            let mut square = Self::hollow();
            let mut boundary = CausalChain::default();
            boundary.add_term(square.ab, ComparativeMultiplicity::positive(1u32));
            boundary.add_term(square.bc, ComparativeMultiplicity::positive(1u32));
            boundary.add_term(square.dc, ComparativeMultiplicity::negative(1u32));
            boundary.add_term(square.ad, ComparativeMultiplicity::negative(1u32));
            let face = square
                .complex
                .found_cell("face", source(), 2, boundary)
                .expect("the square's boundary closes");
            (square, face)
        }

        /// `a -> b -> c`.
        fn left(&self) -> Path {
            Path::along([self.ab, self.bc])
        }

        /// `a -> d -> c`.
        fn right(&self) -> Path {
            Path::along([self.ad, self.dc])
        }

        /// The cycle `a -> b -> c -> d -> a`.
        fn cycle(&self) -> Path {
            self.left().then(&self.right().reversed())
        }

        /// A cochain that is NOT a coboundary: one unit on `ab` and nothing else. On the hollow
        /// square it is closed and its holonomy stands.
        fn standing(&self) -> Cochain {
            Cochain::from_values(1, [(self.ab, big(1))])
        }

        /// `f(a) = 0, f(b) = 3, f(c) = 7, f(d) = -2`, as a grade-zero cochain.
        fn potential(&self) -> Cochain {
            Cochain::from_values(
                0,
                [
                    (self.a, big(0)),
                    (self.b, big(3)),
                    (self.c, big(7)),
                    (self.d, big(-2)),
                ],
            )
        }

        /// `d f` for the potential above: `ab: 3, bc: 4, ad: -2, dc: 9`.
        fn exact(&self) -> Cochain {
            coboundary(&self.complex, &self.potential()).expect("the potential has a coboundary")
        }
    }

    // -----------------------------------------------------------------------------------------
    // the running sum itself

    #[test]
    fn a_coboundary_telescopes_to_the_difference_of_its_potential() {
        let square = Square::hollow();
        let f = square.potential();
        let w = square.exact();
        assert_eq!(
            w.values(),
            &BTreeMap::from([
                (square.ab, big(3)),
                (square.bc, big(4)),
                (square.ad, big(-2)),
                (square.dc, big(9)),
            ]),
            "d f is f(head) - f(tail) on every edge"
        );

        let forward = running_sum(&square.complex, &w, &square.left()).unwrap();
        assert_eq!(
            forward.total,
            f.value(square.c) - f.value(square.a),
            "the discrete fundamental theorem: the running sum is f(end) - f(start)"
        );
        assert_eq!(forward.total, big(7), "and that difference is nonzero");

        let backward = running_sum(&square.complex, &w, &square.left().reversed()).unwrap();
        assert_eq!(
            backward.total,
            f.value(square.a) - f.value(square.c),
            "walked backwards it telescopes the other way"
        );
        assert_eq!(backward.total, big(-7));
    }

    #[test]
    fn the_return_carries_its_lineage_and_not_only_its_total() {
        let square = Square::hollow();
        let w = square.exact();
        let left = running_sum(&square.complex, &w, &square.left()).unwrap();
        let right = running_sum(&square.complex, &w, &square.right()).unwrap();

        assert_eq!(left.total, right.total, "both reach c from a");
        assert_eq!(left.partial_sums(), vec![big(0), big(3), big(7)]);
        assert_eq!(right.partial_sums(), vec![big(0), big(-2), big(7)]);
        assert_ne!(
            left.partial_sums(),
            right.partial_sums(),
            "equal totals, different lineages — collapsing to the scalar discards the path"
        );
        assert_eq!(left.path(), square.left(), "the path is recoverable");
        assert_eq!(
            left.steps.last().unwrap().accumulated,
            left.total,
            "the last partial sum is the total"
        );
    }

    #[test]
    fn crossing_against_the_orientation_negates_the_increment() {
        let square = Square::hollow();
        let w = square.exact();
        let against = Path::new([PathStep::against(square.ab)]);
        let integral = running_sum(&square.complex, &w, &against).unwrap();
        assert_eq!(integral.total, big(-3), "w(ab) = 3, crossed backwards");
        assert_eq!(integral.start, square.b);
        assert_eq!(integral.end, square.a);
        assert!(!integral.is_zero(), "a nonzero control, not a vacuous one");
    }

    // -----------------------------------------------------------------------------------------
    // the falsifier

    /// The nonzero control. If this ever returned zero the module would be the classical integral
    /// wearing new vocabulary, which is exactly what the record's falsifier names.
    #[test]
    fn two_traversals_around_the_hole_disagree_and_the_residual_stands() {
        let square = Square::hollow();
        let w = square.standing();
        let pair = disagreement(&square.complex, &w, &square.left(), &square.right()).unwrap();

        assert_eq!(pair.left.total, big(1));
        assert_eq!(pair.right.total, big(0));
        assert_eq!(pair.residual, big(1), "the disagreement is exactly one");
        assert!(pair.stands(), "and it is not zero");
        assert_eq!(pair.verdict(), PairReturn::Holonomy(big(1)));
        assert!(
            pair.paths_are_distinct(),
            "the pair must be able to disagree at all"
        );
        assert_eq!(pair.start, square.a);
        assert_eq!(pair.end, square.c);
    }

    #[test]
    fn the_same_pair_agrees_when_the_cochain_is_a_coboundary() {
        let square = Square::hollow();
        let w = square.exact();
        let pair = disagreement(&square.complex, &w, &square.left(), &square.right()).unwrap();

        assert_eq!(pair.residual, big(0));
        assert!(!pair.stands());
        assert_eq!(pair.verdict(), PairReturn::Agreed);
        assert!(
            pair.paths_are_distinct(),
            "agreement here is a property of the cochain, not of a degenerate pair"
        );
        assert!(
            !pair.left.total.is_zero(),
            "and the agreed value itself is nonzero, so the agreement is not vacuous"
        );
    }

    /// The material-variation guard. One complex, one pair of traversals, both verdicts reachable.
    #[test]
    fn the_fixture_returns_both_verdicts() {
        let square = Square::hollow();
        let left = square.left();
        let right = square.right();

        assert_ne!(left.chain(), right.chain(), "the traversals differ as chains");
        assert_eq!(
            left.endpoints(&square.complex).unwrap(),
            right.endpoints(&square.complex).unwrap(),
            "and they share both endpoints"
        );

        let standing = disagreement(&square.complex, &square.standing(), &left, &right).unwrap();
        let exact = disagreement(&square.complex, &square.exact(), &left, &right).unwrap();
        assert_eq!(standing.verdict(), PairReturn::Holonomy(big(1)));
        assert_eq!(exact.verdict(), PairReturn::Agreed);
        assert_eq!(
            standing.cycle, exact.cycle,
            "the same cycle carries both returns, so the cochain is the variable"
        );
    }

    /// Closed is not coboundary, and the gap is the whole point. On the hollow square there are no
    /// 2-cells, so every 1-cochain is vacuously closed — and one of them still winds.
    #[test]
    fn the_standing_cochain_is_closed_and_still_returns_a_holonomy() {
        let square = Square::hollow();
        let w = square.standing();
        assert!(
            is_closed(&square.complex, &w).unwrap(),
            "no 2-cell can obstruct it"
        );

        let around = holonomy(&square.complex, &w, &square.cycle()).unwrap();
        assert_eq!(around.total, big(1), "closed, and yet it winds: H^1 != 0");
        assert!(!around.is_zero());
        assert_eq!(around.start, around.end);
    }

    #[test]
    fn a_coboundary_returns_zero_around_every_closed_traversal() {
        let square = Square::hollow();
        let w = square.exact();
        let around = holonomy(&square.complex, &w, &square.cycle()).unwrap();
        assert_eq!(around.total, big(0));
        assert_eq!(
            around.partial_sums(),
            vec![big(0), big(3), big(7), big(-2), big(0)],
            "it passes through nonzero partial sums and returns to rest"
        );
    }

    #[test]
    fn winding_twice_doubles_the_holonomy_and_reversing_negates_it() {
        let square = Square::hollow();
        let w = square.standing();
        let once = square.cycle();
        let twice = once.then(&once);

        assert_eq!(holonomy(&square.complex, &w, &twice).unwrap().total, big(2));
        assert_eq!(
            holonomy(&square.complex, &w, &once.reversed()).unwrap().total,
            big(-1)
        );
        assert_eq!(
            holonomy(&square.complex, &w, &once.then(&once.reversed()))
                .unwrap()
                .total,
            big(0),
            "and a winding undone deposits nothing"
        );
    }

    // -----------------------------------------------------------------------------------------
    // the region

    #[test]
    fn the_disagreement_equals_the_sum_over_the_enclosed_region_boundary() {
        let (square, face) = Square::filled();
        let w = square.standing();
        let region = CausalChain::single(face, ComparativeMultiplicity::positive(1u32));
        let enclosed =
            enclosed_disagreement(&square.complex, &w, &square.left(), &square.right(), &region)
                .unwrap();

        assert_eq!(enclosed.disagreement.residual, big(1));
        assert_eq!(enclosed.boundary_residual, big(1));
        assert_eq!(enclosed.coboundary_residual, big(1));
        assert!(
            enclosed.readings_agree(),
            "three independent readings of one residual"
        );
        assert!(
            !enclosed.boundary_residual.is_zero(),
            "the nonzero control: this law is exercised, not vacuous"
        );
    }

    #[test]
    fn a_coboundary_encloses_a_zero_region_residual() {
        let (square, face) = Square::filled();
        let w = square.exact();
        let region = CausalChain::single(face, ComparativeMultiplicity::positive(1u32));
        let enclosed =
            enclosed_disagreement(&square.complex, &w, &square.left(), &square.right(), &region)
                .unwrap();

        assert_eq!(enclosed.disagreement.residual, big(0));
        assert_eq!(enclosed.boundary_residual, big(0));
        assert_eq!(enclosed.coboundary_residual, big(0));
        assert!(enclosed.readings_agree());
    }

    #[test]
    fn filling_the_hole_makes_the_standing_cochain_no_longer_closed() {
        let (square, face) = Square::filled();
        let w = square.standing();
        let d_w = coboundary(&square.complex, &w).unwrap();

        assert_eq!(d_w.grade(), 2);
        assert_eq!(d_w.value(face), big(1), "the winding now has a witness");
        assert!(
            !is_closed(&square.complex, &w).unwrap(),
            "closedness is a property of the complex the cochain sits on, not of the cochain alone"
        );
    }

    #[test]
    fn the_coboundary_of_a_coboundary_is_zero() {
        let (square, _face) = Square::filled();
        let d_f = coboundary(&square.complex, &square.potential()).unwrap();
        assert!(!d_f.is_zero(), "d f itself is nonzero, so this is not vacuous");
        let d_d_f = coboundary(&square.complex, &d_f).unwrap();
        assert!(
            d_d_f.is_zero(),
            "d d = 0 follows from boundary boundary = 0: {d_d_f:?}"
        );
    }

    #[test]
    fn a_region_that_does_not_enclose_the_pair_is_refused() {
        let (square, face) = Square::filled();
        let w = square.standing();
        let doubled = CausalChain::single(face, ComparativeMultiplicity::positive(2u32));
        let error =
            enclosed_disagreement(&square.complex, &w, &square.left(), &square.right(), &doubled)
                .unwrap_err();
        assert!(
            matches!(error, RunningIntegralError::RegionDoesNotEnclose),
            "a doubled region bounds twice the cycle: {error:?}"
        );

        let wrong_grade = CausalChain::single(square.ab, ComparativeMultiplicity::positive(1u32));
        let error = enclosed_disagreement(
            &square.complex,
            &w,
            &square.left(),
            &square.right(),
            &wrong_grade,
        )
        .unwrap_err();
        assert!(
            matches!(
                error,
                RunningIntegralError::RegionGrade {
                    region: 1,
                    expected: 2
                }
            ),
            "a 1-chain is not a region for a 1-cochain: {error:?}"
        );
    }

    // -----------------------------------------------------------------------------------------
    // the potential and its retained remainder

    #[test]
    fn a_potential_is_recovered_exactly_when_no_chord_disagrees() {
        let square = Square::hollow();
        let w = square.exact();
        let search = found_potential(&square.complex, &w, square.a).unwrap();

        assert!(search.admits_a_potential());
        assert!(search.retained_obstructions.is_empty());
        assert_eq!(search.cycle_rank(), 1, "the square has one independent cycle");
        assert_eq!(search.agreeing_chords.len(), 1, "and its chord agreed");
        assert_eq!(search.tree_cells.len(), 3, "four vertices, three tree cells");
        assert_eq!(search.reached.len(), 4);
        assert!(search.unreached_cells.is_empty());

        assert_eq!(
            search.potential,
            square.potential(),
            "the tree recovers f exactly, base-normalized at a"
        );
        assert_eq!(
            coboundary(&square.complex, &search.potential).unwrap(),
            w,
            "and its coboundary is the cochain it came from"
        );
    }

    /// The deposit. The chord that disagrees is retained with an exact residual; nothing repairs
    /// the potential, and nothing averages the two readings.
    #[test]
    fn the_chord_that_disagrees_is_retained_and_not_averaged() {
        let square = Square::hollow();
        let w = square.standing();
        let search = found_potential(&square.complex, &w, square.a).unwrap();

        assert!(!search.admits_a_potential());
        assert_eq!(search.cycle_rank(), 1);
        assert_eq!(search.retained_obstructions.len(), 1);
        assert!(search.agreeing_chords.is_empty());

        let chord = &search.retained_obstructions[0];
        assert_eq!(chord.cell, square.dc, "dc closes the fundamental cycle");
        assert_eq!(chord.declared, big(0), "w(dc) = 0");
        assert_eq!(chord.implied, big(1), "but the tree implies f(c) - f(d) = 1");
        assert_eq!(chord.residual, big(-1));
        assert!(!chord.residual.is_zero(), "the remainder is nonzero");

        let pair = disagreement(&square.complex, &w, &square.left(), &square.right()).unwrap();
        assert_eq!(
            chord.residual.abs(),
            pair.residual.abs(),
            "the retained chord residual is the holonomy of the cycle it closes"
        );
        assert_eq!(
            chord.residual,
            -pair.residual.clone(),
            "with the sign the chord's own direction around that cycle gives"
        );

        assert_ne!(
            coboundary(&square.complex, &search.potential).unwrap(),
            w,
            "the reconstruction genuinely fails; the failure is the return"
        );
    }

    #[test]
    fn the_search_refuses_a_base_that_is_not_a_vertex() {
        let square = Square::hollow();
        let error = found_potential(&square.complex, &square.standing(), square.ab).unwrap_err();
        assert!(matches!(
            error,
            RunningIntegralError::BaseIsNotAVertex(_)
        ));
    }

    // -----------------------------------------------------------------------------------------
    // guards: material that cannot vary the property

    /// A tree is the fixture that would have proved nothing. Two genuinely different traversals of
    /// `a -> c` exist there, but only by backtracking, and backtracking cancels in the chain — so
    /// the residual is forced to zero for EVERY cochain, including the nonzero ones checked here.
    /// This is why the square, and not a path, is the fixture that carries the falsifier.
    #[test]
    fn a_tree_cannot_falsify_which_is_why_the_square_is_the_fixture() {
        let mut complex = GradedCausalComplex::default();
        let a = vertex(&mut complex, "a");
        let b = vertex(&mut complex, "b");
        let c = vertex(&mut complex, "c");
        let ab = edge(&mut complex, "ab", a, b);
        let bc = edge(&mut complex, "bc", b, c);

        let direct = Path::along([ab, bc]);
        let detoured = Path::new([
            PathStep::along(ab),
            PathStep::along(bc),
            PathStep::against(bc),
            PathStep::along(bc),
        ]);
        assert_ne!(direct.steps(), detoured.steps(), "different traversals");
        assert_eq!(
            direct.chain(),
            detoured.chain(),
            "identical chains — the backtrack cancelled"
        );

        for values in [
            vec![(ab, big(5)), (bc, big(-3))],
            vec![(ab, big(1)), (bc, big(1))],
            vec![(ab, big(-9)), (bc, big(0))],
        ] {
            let w = Cochain::from_values(1, values);
            let pair = disagreement(&complex, &w, &direct, &detoured).unwrap();
            assert!(
                !pair.paths_are_distinct(),
                "the tree admits no cycle for the pair to bound"
            );
            assert_eq!(
                pair.residual,
                big(0),
                "forced to zero by the material, not by the law"
            );
            assert!(
                !pair.left.total.is_zero() || w.is_zero(),
                "and the totals themselves are nonzero, so this is not a zero-cochain artefact"
            );

            let search = found_potential(&complex, &w, a).unwrap();
            assert_eq!(search.cycle_rank(), 0, "a tree has no chords");
            assert!(search.admits_a_potential());
            assert_eq!(coboundary(&complex, &search.potential).unwrap(), w);
        }
    }

    // -----------------------------------------------------------------------------------------
    // refusals

    #[test]
    fn a_traversal_whose_steps_do_not_join_is_refused() {
        let square = Square::hollow();
        let broken = Path::along([square.ab, square.dc]);
        let error = running_sum(&square.complex, &square.standing(), &broken).unwrap_err();
        assert!(
            matches!(
                error,
                RunningIntegralError::PathDoesNotJoin { index: 1, .. }
            ),
            "ab arrives at b and dc departs d: {error:?}"
        );
    }

    #[test]
    fn traversals_with_different_endpoints_cannot_be_compared() {
        let square = Square::hollow();
        let error = disagreement(
            &square.complex,
            &square.standing(),
            &square.left(),
            &Path::along([square.ad]),
        )
        .unwrap_err();
        assert!(matches!(
            error,
            RunningIntegralError::EndpointsDiffer { .. }
        ));
    }

    #[test]
    fn a_grade_mismatched_pairing_is_refused() {
        let square = Square::hollow();
        let error = square
            .potential()
            .evaluate(&square.complex, &square.left().chain())
            .unwrap_err();
        assert!(
            matches!(
                error,
                RunningIntegralError::PairingGrade {
                    cochain: 0,
                    cell: 1,
                    ..
                }
            ),
            "a 0-cochain cannot be integrated over 1-cells: {error:?}"
        );

        let error =
            running_sum(&square.complex, &square.potential(), &square.left()).unwrap_err();
        assert!(matches!(error, RunningIntegralError::NotAOneCochain(0)));
    }

    #[test]
    fn an_empty_traversal_is_refused_rather_than_returning_a_baseless_zero() {
        let square = Square::hollow();
        let error = running_sum(&square.complex, &square.standing(), &Path::default()).unwrap_err();
        assert!(matches!(error, RunningIntegralError::EmptyPath));
    }

    /// The declared aperture, stated as a refusal. A self-incident 1-cell has an empty boundary in
    /// this carrier, so its base point is not recoverable and a walk cannot join through it. It is
    /// refused rather than skipped, because skipping it would discard a winding.
    #[test]
    fn a_self_incident_cell_has_no_recoverable_ends_and_is_refused() {
        let mut complex = GradedCausalComplex::default();
        let a = vertex(&mut complex, "a");
        let mut boundary = CausalChain::default();
        boundary.add_term(a, ComparativeMultiplicity::positive(1u32));
        boundary.add_term(a, ComparativeMultiplicity::negative(1u32));
        assert!(boundary.is_zero(), "the two ends cancelled in the carrier");
        let self_loop = complex.found_cell("loop", source(), 1, boundary).unwrap();

        let w = Cochain::from_values(1, [(self_loop, big(4))]);
        let error = running_sum(&complex, &w, &Path::along([self_loop])).unwrap_err();
        assert!(matches!(
            error,
            RunningIntegralError::UnjoinableCell(cell) if cell == self_loop
        ));

        let error = found_potential(&complex, &w, a).unwrap_err();
        assert!(matches!(error, RunningIntegralError::UnjoinableCell(_)));
    }

    #[test]
    fn cochain_arithmetic_refuses_a_grade_mismatch_and_is_exact_otherwise() {
        let square = Square::hollow();
        let w = square.standing();
        let f = square.potential();
        assert!(matches!(
            w.plus(&f).unwrap_err(),
            RunningIntegralError::CochainGradesDiffer { left: 1, right: 0 }
        ));

        let doubled = w.plus(&w).unwrap();
        assert_eq!(doubled.value(square.ab), big(2));
        assert!(w.minus(&w).unwrap().is_zero(), "exact cancellation");

        let pair = disagreement(&square.complex, &doubled, &square.left(), &square.right()).unwrap();
        assert_eq!(
            pair.residual,
            big(2),
            "the holonomy is linear in the cochain"
        );
    }
}

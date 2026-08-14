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
//! ## The coefficient group is the caller's, and `Z` is not a neutral choice
//!
//! A chord residual is the pairing of the cochain with the fundamental cycle that chord closes, so
//! the chord population **is** the homomorphism `H_1(1-skeleton) -> G` in the fundamental-cycle
//! basis, split into its kernel (the agreeing chords) and its complement (the retained
//! obstructions). Which `G` that is decides what the instrument can see, and it is a theorem that
//! `Z` cannot see everything:
//!
//! ```text
//!   Hom(Z/n, Z) = 0            an integer-valued holonomy kills every torsion class
//!   Hom(Z/n, Z/m) = Z/gcd(n,m) a cyclic-valued one sees exactly the part the modulus shares
//! ```
//!
//! `crates/holonic-engine/src/rebase_invariants.rs` computes integral homology **with** torsion in
//! this same crate, and returned `Z/2` on the wound grown circuit. Until 2026-08-10 this module
//! hard-wired all three arms of [`ChordObstruction`] to [`BigInt`], so the tree's holonomy
//! instrument was provably blind to the class the tree's invariant instrument had just found.
//! `canon/TABLET_THE_FLOW.md` §6 states the defect and §"Why this is today's finding under another
//! name" states the construction: *give `running_integral`'s chord obstruction the same two-arm
//! shape, with a coefficient group the caller declares.*
//!
//! [`CoefficientGroup`] is that declaration. **This organ never authors a modulus, never defaults
//! to one, and never reads one off the material** — `found_potential` remains `Z` and
//! [`found_potential_in`] takes the group as an argument. A caller that wants `Z/2` because
//! `rebase_invariants` reported a `Z/2` is reading the level off the material and declaring it,
//! which is the lawful direction; the organ doing that for it would not be.
//!
//! And the reduction is a **reading**. Every [`ChordObstruction`] retains `declared`, `implied` and
//! `residual` exactly in `Z` whatever group was declared, because a carrier that reduces on
//! construction has decided for every consumer it will ever have which distinctions are invisible.
//! Only the *split* — agreeing against retained — consults the group.
//!
//! One consequence is worth stating because it bounds what the orbit can ever be: `Z -> Z/n` is a
//! homomorphism, so a residual that vanishes in `Z` vanishes in `Z/n`. **The retained population
//! over `Z/n` is always a subset of the one over `Z`**; reduction can turn an obstruction into an
//! agreement and never the reverse.
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
use num_traits::{One, Signed, Zero};
use serde::{Deserialize, Serialize};
use thiserror::Error;

use crate::causal_body::CausalTransportHand;

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
/// An absent cell carries zero, exactly as [`CausalChain`] treats an absent coefficient. **A cell
/// assigned zero is not an absent cell.** Until 2026-08-08 [`Cochain::set`] removed the key on a
/// zero deposit, so founding zero founded nothing and the spanning tree's own base — the one vertex
/// whose potential is fixed by declaration — vanished from the cochain that carried it. That is
/// `CLAUDE.md` §2b at the level of a carrier: the reading was kept and the deposit discarded.
///
/// Two predicates split rather than the data, exactly as they do on
/// [`crate::algebraic::ComparativeMultiplicity`]:
///
/// | predicate | means |
/// |---|---|
/// | [`Cochain::assigns_nothing`] | no value was deposited on any cell |
/// | [`Cochain::is_zero`] | every deposited value is zero — the cochain *is* the zero cochain |
///
/// and two populations likewise: [`Cochain::assigned`] is the domain the receiver declared, and
/// [`Cochain::support`] is the algebraic support, the cells carrying a nonzero value. Every cocycle,
/// coboundary and closure reading wants `support`/`is_zero`; a reading that asks *where has this
/// cochain been defined* wants `assigned`/`assigns_nothing`.
///
/// Equality is structural, on the deposits. Two cochains that assign the same values on different
/// domains are compared with [`Cochain::assigns_the_same_values`].
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

    /// Deposit a value on one cell. **A zero deposit is a deposit.** It enters
    /// [`Cochain::assigned`] and leaves [`Cochain::support`] alone, which is the whole distinction
    /// between *the receiver said nothing here* and *the receiver said nothing is here*.
    pub fn set(&mut self, cell: CausalCellId, value: BigInt) {
        self.values.insert(cell, value);
    }

    /// The cells carrying a **nonzero** value: the algebraic support.
    pub fn support(&self) -> BTreeSet<CausalCellId> {
        self.values
            .iter()
            .filter(|(_, value)| !value.is_zero())
            .map(|(cell, _)| *cell)
            .collect()
    }

    /// Every cell a value was deposited on, zero or not: the declared domain.
    pub fn assigned(&self) -> BTreeSet<CausalCellId> {
        self.values.keys().copied().collect()
    }

    /// Every deposited value is zero — this *is* the zero cochain. Distinct from
    /// [`Cochain::assigns_nothing`], and this is the predicate every closure reading wants.
    pub fn is_zero(&self) -> bool {
        self.values.values().all(BigInt::is_zero)
    }

    /// Nothing was deposited anywhere. A cochain that assigned zero to one cell is not this.
    pub fn assigns_nothing(&self) -> bool {
        self.values.is_empty()
    }

    /// The two cochains assign equal values on every cell of the same grade, whatever their declared
    /// domains. This is the extensional reading; `==` compares the deposits.
    pub fn assigns_the_same_values(&self, other: &Self) -> bool {
        if self.grade != other.grade {
            return false;
        }
        self.values
            .keys()
            .chain(other.values.keys())
            .all(|cell| self.value(*cell) == other.value(*cell))
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
/// cochain is visited, so the returned cochain is total on its grade: its [`Cochain::assigned`] is
/// exactly that grade's cell population, including the cells the coboundary sends to zero. That
/// sentence was written before 2026-08-08 and was false until then, because [`Cochain::set`] deleted
/// the vanishing cells and left a return that could not say where `d w` had been evaluated.
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
            steps: self
                .steps
                .iter()
                .rev()
                .map(|step| step.reversed())
                .collect(),
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

    pub fn is_closed(&self, complex: &GradedCausalComplex) -> Result<bool, RunningIntegralError> {
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
    /// The two traversals differ as *cycles*, not merely as passages.
    ///
    /// A backtrack deposits opposed terms on one carrier; those are retained
    /// by `CausalChain` and are two passages, so the chains genuinely differ.
    /// They are the same cycle, and it is the cycle this predicate reports.
    pub fn paths_are_distinct(&self) -> bool {
        !self.cycle.difference_is_zero()
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
    if !complex.boundary_of_chain(&cycle)?.difference_is_zero() {
        return Err(RunningIntegralError::PairIsNotACycle);
    }

    let residual = &left_integral.total - &right_integral.total;
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
// the coefficient group

/// The group a chord test is read in — **declared by the caller, never by this organ.**
///
/// The residuals themselves are computed in `Z` and retained in `Z` whatever is declared here. What
/// the declaration decides is the single question *does this residual vanish*, which is what splits
/// the chord population into agreeing and retained. That is the whole of the coupling, and it is
/// deliberately that narrow: the spanning tree, the walk order, the potential and the exact
/// residuals are functions of the complex, the cochain and the base alone.
///
/// The two groups are not interchangeable and the difference is a theorem rather than a
/// convenience. A chord residual pairs the cochain with a fundamental cycle, so the population is a
/// homomorphism out of `H_1`, and `Hom(Z/n, Z) = 0`: **an integer holonomy annihilates every
/// torsion class by construction.** `Hom(Z/n, Z/m) = Z/gcd(n, m)`, so a declared modulus sees a
/// torsion class exactly to the extent that it shares a factor with it — declaring `Z/3` against a
/// `Z/2` is as blind as declaring `Z`.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum CoefficientGroup {
    /// `Z`. Nothing is reduced; every residual is its own exact self.
    Integers,
    /// `Z/modulus`, for a modulus the caller supplies.
    Cyclic { modulus: BigInt },
}

impl CoefficientGroup {
    /// `Z/modulus` for a positive modulus.
    ///
    /// A modulus of zero is refused rather than silently read as `Z`, and a negative one is refused
    /// rather than silently read as its magnitude: both are a receiver's word about which group it
    /// wants, and quietly repairing the word would be this organ choosing the group. `Z` is
    /// declared as [`CoefficientGroup::Integers`].
    ///
    /// `Z/1` is admitted. It is the trivial group, in which every chord agrees vacuously — a
    /// receiver that cannot tell anything apart is a lawful receiver whose return says so, and
    /// refusing it here would be an authored floor.
    pub fn cyclic(modulus: BigInt) -> Result<Self, RunningIntegralError> {
        if !modulus.is_positive() {
            return Err(RunningIntegralError::ModulusIsNotPositive(modulus));
        }
        Ok(Self::Cyclic { modulus })
    }

    /// The declared modulus, or `None` for `Z`.
    pub fn modulus(&self) -> Option<&BigInt> {
        match self {
            Self::Integers => None,
            Self::Cyclic { modulus } => Some(modulus),
        }
    }

    /// The canonical representative of `value`: `value` itself over `Z`, and the least non-negative
    /// residue in `Z/n`.
    pub fn reduce(&self, value: &BigInt) -> BigInt {
        match self {
            Self::Integers => value.clone(),
            Self::Cyclic { modulus } => {
                let residue = value % modulus;
                if residue.is_negative() {
                    residue + modulus
                } else {
                    residue
                }
            }
        }
    }

    /// Whether `value` is this group's zero: zero in `Z`, a multiple of the modulus in `Z/n`.
    pub fn vanishes(&self, value: &BigInt) -> bool {
        match self {
            Self::Integers => value.is_zero(),
            Self::Cyclic { modulus } => (value % modulus).is_zero(),
        }
    }
}

// ---------------------------------------------------------------------------------------------
// the potential, and the chords it cannot repair

/// A chord whose declared value disagrees with the potential the spanning tree implies.
///
/// The residual is the holonomy of the fundamental cycle that chord closes. It is retained here
/// exactly, with its own address, and nothing in this module ever folds it back into the potential.
///
/// **All three arms stay in `Z` whatever group the search declared.** The reduction is offered by
/// [`ChordObstruction::residual_in`] and lives in the reading, never in the constructor: a carrier
/// that reduces on construction has decided, for every consumer it will ever have, which
/// distinctions are invisible.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ChordObstruction {
    pub cell: CausalCellId,
    pub tail: CausalCellId,
    pub head: CausalCellId,
    /// `w(e)`, exact in `Z`.
    pub declared: BigInt,
    /// `f(head) - f(tail)` from the tree's potential, exact in `Z`.
    pub implied: BigInt,
    /// `declared - implied`, exact in `Z`. Nonzero **in the group the search declared** — and
    /// therefore nonzero in `Z` too, since `Z -> Z/n` sends zero to zero.
    pub residual: BigInt,
}

impl ChordObstruction {
    /// The residual read in a declared group.
    pub fn residual_in(&self, group: &CoefficientGroup) -> BigInt {
        group.reduce(&self.residual)
    }

    /// Whether this chord agrees in a declared group.
    ///
    /// `false` for the group the search itself declared, by construction of this variant. It can be
    /// `true` for a coarser one, and that difference is the orbit worth exhibiting.
    pub fn agrees_in(&self, group: &CoefficientGroup) -> bool {
        group.vanishes(&self.residual)
    }
}

/// **How one vertex was reached: from where, carried by what, crossed which way.**
///
/// A pointer is not an address, it is a relative orientation — *from here, that way* — and the same
/// species as `opposite`/`adjacent` at a chosen vertex of a triangle. Which one is "the parent" is
/// decided by where the base was put, exactly as which side is "opposite" is decided by which angle
/// you stand at. Relabel the standpoint and the relation permutes; the tree does not move.
///
/// The hand is [`crate::causal_body::CausalTransportHand`] rather than a second spelling of it,
/// because it is the same object: `Reverse` is the half turn, and
/// `causal_body::RootedTreeIndex::path` reverses exactly this on the ascending leg when it climbs
/// to a least common ancestor.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ReachedBy {
    /// The vertex this one was reached from — the tail of the step. Its own [`ReachedBy`]
    /// continues the route.
    pub from: CausalCellId,
    /// The vertex reached — the head of the step, and the key this entry is stored under.
    ///
    /// Both ends are named because both are the relation. Storing only the tail and recovering the
    /// head from the key works until the route is reversed, and a route between two vertices is
    /// half reversed by construction.
    pub to: CausalCellId,
    /// The 1-cell that carried the step. It is a member of [`PotentialSearch::tree_cells`].
    pub carrier: CausalCellId,
    /// `Forward` when the walk crossed tail to head, `Reverse` when head to tail — which is the
    /// sign the potential took: `w = df` means `w(e) = f(head) − f(tail)`, so a reversed crossing
    /// subtracts where a forward one adds.
    pub hand: CausalTransportHand,
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
    /// The coefficient group the caller declared.
    ///
    /// The tree, the walk order, the potential and every exact residual are independent of it. The
    /// **split** between [`PotentialSearch::agreeing_chords`] and
    /// [`PotentialSearch::retained_obstructions`] is not, and that is the whole of what it decides.
    pub group: CoefficientGroup,
    /// Grade-zero, valued zero at the base, exact in `Z` whatever group was declared.
    pub potential: Cochain,
    pub reached: BTreeSet<CausalCellId>,
    /// **How each reached vertex was reached** — the vertex it came from, the 1-cell that carried
    /// it, and the hand that cell was crossed with.
    ///
    /// This is the head/tail relation of the spanning tree, and the search computes every part of
    /// it in order to walk at all. [`PotentialSearch::reached`] is this map's keys and
    /// [`PotentialSearch::tree_cells`] is its carriers; **both are faces of this, and until
    /// 2026-08-14 only the two faces were returned.** The base is the one reached vertex with no
    /// entry here, which is what makes it the base.
    pub parents: BTreeMap<CausalCellId, ReachedBy>,
    pub tree_cells: BTreeSet<CausalCellId>,
    /// Chords whose declared value already matched the tree's potential.
    pub agreeing_chords: BTreeSet<CausalCellId>,
    /// Chords whose declared value did not. Retained, never averaged.
    pub retained_obstructions: Vec<ChordObstruction>,
    /// 1-cells in the complex that this component never touched.
    pub unreached_cells: BTreeSet<CausalCellId>,
}

impl PotentialSearch {
    /// The cochain is a coboundary on the reached component **in the declared group** exactly when
    /// nothing was retained.
    pub fn admits_a_potential(&self) -> bool {
        self.retained_obstructions.is_empty()
    }

    /// **The route from `vertex` back to the base**, as ordered steps, read off the relation the
    /// walk already built.
    ///
    /// `None` when the vertex was never reached, which is a different return from an empty route:
    /// the base itself is reached and its route is empty, because it is where routes end. `None`
    /// also returns for a **malformed** parent relation — one carrying a cycle, which a spanning
    /// tree cannot — rather than walking it forever.
    ///
    /// This costs one step per hop and no search. Before the parent relation was kept, a caller
    /// wanting this had to re-walk a tree the search had already walked — the whole defect in one
    /// sentence.
    pub fn route_to_base(&self, vertex: CausalCellId) -> Option<Vec<ReachedBy>> {
        if !self.reached.contains(&vertex) {
            return None;
        }
        let mut route = Vec::new();
        let mut at = vertex;
        // Bounded by the relation's own size, and the bound is exact rather than authored: a tree
        // with `k` parent entries has depth at most `k`, so a walk that takes more than `k` steps
        // has entered a cycle and the relation is not a tree. `PotentialSearch` derives
        // `Deserialize` and carries public fields, so a malformed map is reachable from outside
        // this module — and without this the walk does not fail, it hangs. Measured 2026-08-14 by
        // deliberately swapping head and tail at the founding site: the test process did not
        // assert, it was killed.
        while let Some(step) = self.parents.get(&at) {
            if route.len() == self.parents.len() {
                return None;
            }
            route.push(*step);
            at = step.from;
        }
        Some(route)
    }

    /// The route between **two** reached vertices, through their least common ancestor in the
    /// spanning tree, with the hand reversed on the ascending leg.
    ///
    /// `None` when either endpoint is unreached — the two are then in different components of the
    /// walked terrain and no route exists, which is a returned fact rather than an empty vector.
    ///
    /// The reversal is the content: traversing a relation backwards is the half turn, so a route
    /// between two entities is a composition of forward and reversed transports and the reversal
    /// **is** a sign. `causal_body::RootedTreeIndex::path` does the same climb over a different
    /// standing; this is that reading made available wherever a potential was founded.
    pub fn route_between(
        &self,
        source: CausalCellId,
        target: CausalCellId,
    ) -> Option<Vec<ReachedBy>> {
        let up = self.route_to_base(source)?;
        let down = self.route_to_base(target)?;
        // Both routes end at the base, so their common suffix — compared from the base end — is the
        // shared ascent. What remains of each is its own leg, and the meeting point is the least
        // common ancestor.
        let shared = up
            .iter()
            .rev()
            .zip(down.iter().rev())
            .take_while(|(left, right)| left.carrier == right.carrier)
            .count();
        let mut route = Vec::with_capacity(up.len() + down.len() - 2 * shared);
        // **The ascending leg is the reversed one.** A parent entry reads *this vertex was reached
        // from that one*, which points away from the base; climbing towards the base traverses it
        // backwards, and traversing a relation backwards is the half turn.
        for step in &up[..up.len() - shared] {
            route.push(ReachedBy {
                from: step.to,
                to: step.from,
                carrier: step.carrier,
                hand: match step.hand {
                    CausalTransportHand::Forward => CausalTransportHand::Reverse,
                    CausalTransportHand::Reverse => CausalTransportHand::Forward,
                },
            });
        }
        // The descending leg already points away from the base, which is the direction of travel
        // once the ancestor is passed. Only the order reverses.
        for step in down[..down.len() - shared].iter().rev() {
            route.push(*step);
        }
        Some(route)
    }

    /// The number of independent cycles the reached component carries: its departure from a tree.
    ///
    /// Group-independent. Only the split of these chords between the two arms moves.
    pub fn cycle_rank(&self) -> usize {
        self.agreeing_chords.len() + self.retained_obstructions.len()
    }

    /// The exact `Z` residuals standing after the search, in chord order.
    pub fn standing_residuals(&self) -> Vec<BigInt> {
        self.retained_obstructions
            .iter()
            .map(|chord| chord.residual.clone())
            .collect()
    }

    /// The same residuals read in the group this search declared.
    pub fn residuals_in_group(&self) -> impl Iterator<Item = BigInt> + '_ {
        self.retained_obstructions
            .iter()
            .map(|chord| chord.residual_in(&self.group))
    }

    /// The potential read in the declared group. The exact `Z` potential is retained beside it.
    pub fn potential_in_group(&self) -> Cochain {
        Cochain::from_values(
            self.potential.grade(),
            self.potential
                .values()
                .iter()
                .map(|(cell, value)| (*cell, self.group.reduce(value))),
        )
    }

    /// Chords exist and every one of them agreed: the ant walked the loops and the spider deposited
    /// nothing.
    ///
    /// This is [`crate::running_integral`]'s reading of `RayCrossings::cancels` in
    /// `relational-geometry`, and it separates the two cases a bare `admits_a_potential` conflates —
    /// a structure with no cycles at all, which closes for free and evidences nothing, and one whose
    /// cycles were tested and agreed.
    pub fn closes_over_a_live_cycle_population(&self) -> bool {
        self.cycle_rank() > 0 && self.retained_obstructions.is_empty()
    }
}

/// Walk a spanning tree of the 1-skeleton from `base`, assign the only potential it admits, and
/// test every chord **over `Z`**.
///
/// Deterministic: the incidence lists are built in cell-identity order and the frontier is walked
/// breadth-first, so the tree, the chord set and the retained residuals are a function of the
/// complex and the base alone.
///
/// This is [`found_potential_in`] with [`CoefficientGroup::Integers`] declared, and it is what every
/// caller that has not thought about the coefficient group should keep calling. It is also, by the
/// theorem in this module's header, the reading that cannot see a torsion class.
pub fn found_potential(
    complex: &GradedCausalComplex,
    cochain: &Cochain,
    base: CausalCellId,
) -> Result<PotentialSearch, RunningIntegralError> {
    found_potential_in(complex, cochain, base, CoefficientGroup::Integers)
}

/// The same search with the coefficient group **declared by the caller**.
///
/// The walk is identical and the residuals are identical: only the test `residual vanishes` is
/// asked in `group` rather than in `Z`. Over [`CoefficientGroup::Integers`] this is
/// [`found_potential`] exactly, which is why adding the group moved no existing caller.
pub fn found_potential_in(
    complex: &GradedCausalComplex,
    cochain: &Cochain,
    base: CausalCellId,
    group: CoefficientGroup,
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
        incident
            .entry(tail)
            .or_default()
            .push((cell.id, tail, head));
        incident
            .entry(head)
            .or_default()
            .push((cell.id, tail, head));
    }

    let mut assigned: BTreeMap<CausalCellId, BigInt> = BTreeMap::new();
    assigned.insert(base, BigInt::zero());
    let mut parents: BTreeMap<CausalCellId, ReachedBy> = BTreeMap::new();
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
                    // The head/tail relation, kept. At this instant the walk knows all three parts
                    // — which vertex `far` was reached FROM, which 1-cell carried it, and which way
                    // that cell was crossed — because it needed all three to compute the potential
                    // one line above. Until 2026-08-14 all three were dropped here and the search
                    // returned two populations instead: `reached`, the potential map's keys
                    // collected into a set, and `tree_cells`, the carrying cells collected into
                    // another. A caller wanting the route from a vertex back to the base had to
                    // re-search a tree that had already been walked.
                    parents.insert(
                        far,
                        ReachedBy {
                            from: vertex,
                            to: far,
                            carrier: cell,
                            hand: if vertex == tail {
                                CausalTransportHand::Forward
                            } else {
                                CausalTransportHand::Reverse
                            },
                        },
                    );
                    frontier.push_back(far);
                }
                Some(_) => {
                    let implied = assigned.get(&head).cloned().unwrap_or_else(BigInt::zero)
                        - assigned.get(&tail).cloned().unwrap_or_else(BigInt::zero);
                    let residual = &declared - &implied;
                    if group.vanishes(&residual) {
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
        schema: "holonic-engine.integral-potential-search.v2".to_owned(),
        base,
        group,
        potential,
        reached,
        parents,
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
    #[error(
        "a modulus is a positive integer and {0} is not one; `Z` is declared as \
         `CoefficientGroup::Integers`, not as a modulus of zero"
    )]
    ModulusIsNotPositive(BigInt),
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
    // the declared control for the zero deposit

    /// THE DECLARED CONTROL for [`Cochain::set`] (`CLAUDE.md` §2b). Until 2026-08-08 a zero deposit
    /// removed the key, so three different things were one thing: a cell never spoken of, a cell the
    /// receiver assigned zero, and a cell where an exact computation *returned* zero.
    ///
    /// The three readings this separates are load-bearing, not cosmetic:
    ///
    /// 1. `found_potential` fixes `f(base) = 0` **by declaration** — that is the gauge choice the
    ///    whole search rests on — and the old carrier deleted it from the cochain it returned. The
    ///    search's own `reached` set kept it, so the return contradicted itself.
    /// 2. `coboundary`'s doc promised a return total on its grade. It was not: every 2-cell where
    ///    `d w` vanished was dropped, so the return could not say where `d w` had been evaluated,
    ///    which is exactly the difference between *closed here* and *not looked at here*.
    /// 3. `temper::found_on(w, cell, 0)` founded nothing at all.
    ///
    /// Against the old carrier every `assigned()` assertion below collapses onto `support()` and
    /// fails.
    #[test]
    fn a_cell_assigned_zero_is_not_a_cell_that_was_never_assigned() {
        // The bare carrier reading first: same values everywhere, different declared domains.
        let square = Square::hollow();
        let silent = Cochain::new(1);
        let spoken = Cochain::from_values(1, [(square.ab, big(0))]);
        assert!(
            silent.is_zero() && spoken.is_zero(),
            "both are zero cochains"
        );
        assert!(
            silent.assigns_the_same_values(&spoken),
            "and they pair identically against every chain"
        );
        assert_ne!(silent, spoken, "one spoke about `ab` and the other did not");
        assert!(silent.assigns_nothing() && !spoken.assigns_nothing());
        assert_eq!(spoken.support(), BTreeSet::new(), "nothing stands on `ab`");
        assert_eq!(
            spoken.assigned(),
            BTreeSet::from([square.ab]),
            "and `ab` is nonetheless where this cochain has been defined"
        );

        // 1. The gauge the search declares survives into the cochain it returns, and so does every
        //    other vertex the tree happens to send back to zero.
        let mut complex = GradedCausalComplex::default();
        let a = vertex(&mut complex, "a");
        let b = vertex(&mut complex, "b");
        let c = vertex(&mut complex, "c");
        let ab = edge(&mut complex, "ab", a, b);
        let bc = edge(&mut complex, "bc", b, c);
        // f(a) = 0 by declaration, f(b) = 1, f(c) = 0 by cancellation. Two different zeros.
        let w = Cochain::from_values(1, [(ab, big(1)), (bc, big(-1))]);
        let search = found_potential(&complex, &w, a).unwrap();
        assert!(search.admits_a_potential());
        assert_eq!(search.reached, BTreeSet::from([a, b, c]));
        assert_eq!(
            search.potential.support(),
            BTreeSet::from([b]),
            "only `b` carries a nonzero potential"
        );
        assert_eq!(
            search.potential.assigned(),
            search.reached,
            "the potential is defined on exactly what the walk reached, base included"
        );
        assert_eq!(search.potential.value(a), big(0));
        assert_eq!(search.potential.value(c), big(0));
        assert!(
            !search.potential.assigns_nothing() && !search.potential.is_zero(),
            "a live control: this potential is not the zero cochain"
        );

        // 2. The coboundary is total on its grade, and says so by its domain.
        let (filled, face) = Square::filled();
        let exact = filled.exact();
        let d_exact = coboundary(&filled.complex, &exact).unwrap();
        assert!(d_exact.is_zero(), "d d f = 0");
        assert_eq!(
            d_exact.assigned(),
            BTreeSet::from([face]),
            "`d d f` was evaluated on the face and returned zero there; that is not the same \
             return as never having been evaluated"
        );
        assert_eq!(d_exact.support(), BTreeSet::new());
        let d_standing = coboundary(&filled.complex, &filled.standing()).unwrap();
        assert_eq!(
            d_standing.assigned(),
            d_exact.assigned(),
            "the same aperture was swept either way"
        );
        assert_eq!(
            d_standing.support(),
            BTreeSet::from([face]),
            "and here it returned non-zero, which is why the domain is not the support"
        );
        assert_ne!(d_standing, d_exact, "the two coboundaries differ");

        // 3. Nothing above changed any integer reading. This is the invariance contract.
        assert_eq!(
            running_sum(&complex, &w, &Path::along([ab, bc]))
                .unwrap()
                .total,
            big(0)
        );
        assert!(is_closed(&filled.complex, &exact).unwrap());
        assert!(!is_closed(&filled.complex, &filled.standing()).unwrap());
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

        assert_ne!(
            left.chain(),
            right.chain(),
            "the traversals differ as chains"
        );
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
            holonomy(&square.complex, &w, &once.reversed())
                .unwrap()
                .total,
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
        let enclosed = enclosed_disagreement(
            &square.complex,
            &w,
            &square.left(),
            &square.right(),
            &region,
        )
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
        let enclosed = enclosed_disagreement(
            &square.complex,
            &w,
            &square.left(),
            &square.right(),
            &region,
        )
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
        assert!(
            !d_f.is_zero(),
            "d f itself is nonzero, so this is not vacuous"
        );
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
        let error = enclosed_disagreement(
            &square.complex,
            &w,
            &square.left(),
            &square.right(),
            &doubled,
        )
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
        assert_eq!(
            search.cycle_rank(),
            1,
            "the square has one independent cycle"
        );
        assert_eq!(search.agreeing_chords.len(), 1, "and its chord agreed");
        assert_eq!(
            search.tree_cells.len(),
            3,
            "four vertices, three tree cells"
        );
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
        assert_eq!(
            chord.implied,
            big(1),
            "but the tree implies f(c) - f(d) = 1"
        );
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
        assert!(matches!(error, RunningIntegralError::BaseIsNotAVertex(_)));
    }

    // -----------------------------------------------------------------------------------------
    // the declared coefficient group

    /// **The orbit.** One complex, one cochain, three declared groups, three different chord
    /// populations — and the modulus is what separates them.
    ///
    /// `dc` is the square's only chord and its residual is `2`. Over `Z` it obstructs. Over `Z/2`
    /// it agrees, because `2` is the group's zero. Over `Z/3` it obstructs again, which is the
    /// **The falsifier for the parent relation.** A route is only the route if walking it
    /// reproduces the potential the same search returned: summing each carried value with the
    /// hand's sign must land exactly on the vertex's potential. A fabricated, stale, or
    /// wrongly-handed parent map fails this at the first vertex deeper than one step.
    #[test]
    fn every_route_to_base_reproduces_the_potential_it_was_walked_beside() {
        // **The walk must cross at least one edge against its orientation, or this test cannot
        // fail.** `cb` points c -> b, so reaching c from b traverses it head-to-tail and stores
        // `Reverse`. Measured 2026-08-14 on the hollow square, whose every edge the walk crosses
        // tail-to-head: pinning the stored hand to `Forward` left the entire module green. The
        // fixture was the defect, not the assertion.
        let mut complex = GradedCausalComplex::default();
        let a = vertex(&mut complex, "a");
        let b = vertex(&mut complex, "b");
        let c = vertex(&mut complex, "c");
        let d = vertex(&mut complex, "d");
        let ab = edge(&mut complex, "ab", a, b);
        let cb = edge(&mut complex, "cb", c, b);
        let ad = edge(&mut complex, "ad", a, d);
        let w = Cochain::from_values(1, [(ab, big(3)), (cb, big(5)), (ad, big(2))]);
        let search = found_potential(&complex, &w, a).unwrap();

        let hands: Vec<CausalTransportHand> =
            search.parents.values().map(|step| step.hand).collect();
        assert!(hands.contains(&CausalTransportHand::Forward));
        assert!(
            hands.contains(&CausalTransportHand::Reverse),
            "the material must exercise both hands or the sign below is never read"
        );
        assert!(search.reached.len() > 2, "and must reach past one step");

        for vertex in &search.reached {
            let route = search
                .route_to_base(*vertex)
                .expect("a reached vertex has a route");
            let mut carried = BigInt::zero();
            for step in &route {
                match step.hand {
                    CausalTransportHand::Forward => carried += w.value(step.carrier),
                    CausalTransportHand::Reverse => carried -= w.value(step.carrier),
                }
            }
            assert_eq!(
                carried,
                search.potential.value(*vertex),
                "route for {vertex:?} does not carry its own potential"
            );
        }
        // c sits behind a reversed crossing, so its potential is the one a Forward-only reading
        // would get wrong: 3 - 5, not 3 + 5.
        assert_eq!(search.potential.value(c), big(-2));

        // Reached-with-an-empty-route and never-reached are different returns, and the base is the
        // one vertex that is the first.
        assert!(search.route_to_base(a).unwrap().is_empty());
        assert_eq!(
            search.route_to_base(ad),
            None,
            "a 1-cell was never a reached vertex"
        );

        // And the two populations that used to be returned alone are faces of this one.
        let carriers: BTreeSet<CausalCellId> =
            search.parents.values().map(|step| step.carrier).collect();
        assert_eq!(
            carriers, search.tree_cells,
            "tree_cells is the carrier face"
        );
        let mut keys: BTreeSet<CausalCellId> = search.parents.keys().copied().collect();
        keys.insert(search.base);
        assert_eq!(
            keys, search.reached,
            "reached is the key face, plus the base"
        );
        let _ = d;
    }

    /// A route between two vertices climbs to their least common ancestor and comes back down, and
    /// **the ascending leg carries the opposite hand** — the half turn, which is the whole content
    /// of a route being a composition of transports rather than a list of vertices.
    #[test]
    fn a_route_between_two_vertices_reverses_the_hand_on_the_ascending_leg() {
        let square = Square::hollow();
        let w = Cochain::from_values(1, [(square.ab, big(3)), (square.bc, big(5))]);
        let search = found_potential(&square.complex, &w, square.a).unwrap();

        let route = search
            .route_between(square.c, square.d)
            .expect("both are reached");
        // c climbs to b, then to the base a, then descends to d. Three steps, and only the last is
        // travelled in the direction its parent entry was recorded in.
        assert_eq!(route.len(), 3);
        assert_eq!(route[0].hand, CausalTransportHand::Reverse);
        assert_eq!(route[1].hand, CausalTransportHand::Reverse);
        assert_eq!(route[2].hand, CausalTransportHand::Forward);
        assert_eq!(route[2].carrier, square.ad);

        // The steps chain end to end, which is what makes it a route and not a set of edges.
        assert_eq!(route[0].from, square.c);
        for pair in route.windows(2) {
            assert_eq!(pair[0].to, pair[1].from, "the route breaks");
        }
        assert_eq!(route[route.len() - 1].to, square.d);

        // Reversing the endpoints reverses every hand and the order.
        let back = search.route_between(square.d, square.c).unwrap();
        assert_eq!(back.len(), route.len());
        for (there, here) in route.iter().rev().zip(&back) {
            assert_eq!(there.carrier, here.carrier);
            assert_ne!(there.hand, here.hand, "the return trip is the other hand");
        }
    }

    /// Two vertices in different components return **no route**, by name, rather than an empty one.
    #[test]
    fn an_unreached_endpoint_returns_no_route_rather_than_an_empty_one() {
        let mut complex = GradedCausalComplex::default();
        let a = vertex(&mut complex, "a");
        let b = vertex(&mut complex, "b");
        let island = vertex(&mut complex, "island");
        let ab = edge(&mut complex, "ab", a, b);
        let w = Cochain::from_values(1, [(ab, big(1))]);
        let search = found_potential(&complex, &w, a).unwrap();

        assert!(search.reached.contains(&b));
        assert!(!search.reached.contains(&island));
        assert_eq!(search.route_between(b, island), None);
        assert_eq!(search.route_between(island, b), None);
        assert_eq!(search.route_to_base(island), None);
        assert!(
            search.route_between(a, b).is_some(),
            "and the reachable pair still routes"
        );
    }

    /// point that makes this a gauge rather than a switch: a modulus is not a knob that always
    /// weakens the test, it sees exactly the part of the residual it shares a factor with.
    #[test]
    fn a_declared_modulus_moves_a_chord_between_the_two_arms() {
        let square = Square::hollow();
        let w = Cochain::from_values(1, [(square.dc, big(2))]);
        let two = CoefficientGroup::cyclic(big(2)).unwrap();
        let three = CoefficientGroup::cyclic(big(3)).unwrap();

        let over_z = found_potential(&square.complex, &w, square.a).unwrap();
        assert_eq!(over_z.cycle_rank(), 1);
        assert!(!over_z.admits_a_potential());
        assert_eq!(over_z.retained_obstructions[0].cell, square.dc);
        assert_eq!(over_z.retained_obstructions[0].residual, big(2));

        let over_two = found_potential_in(&square.complex, &w, square.a, two.clone()).unwrap();
        assert_eq!(over_two.cycle_rank(), 1, "the same chord is still tested");
        assert!(
            over_two.admits_a_potential(),
            "2 is the zero of Z/2, so the residual no longer stands"
        );
        assert!(over_two.agreeing_chords.contains(&square.dc));
        assert!(
            over_two.closes_over_a_live_cycle_population(),
            "and it closed over a chord that exists, not over an empty cycle population"
        );

        let over_three = found_potential_in(&square.complex, &w, square.a, three).unwrap();
        assert!(
            !over_three.admits_a_potential(),
            "gcd(2, 3) = 1: Z/3 is exactly as blind to this residual as Z is"
        );
        assert_eq!(over_three.retained_obstructions[0].residual, big(2));
        assert_eq!(
            over_three.retained_obstructions[0].residual_in(&two),
            big(0),
            "and the same retained obstruction reads as agreeing in the other group"
        );
    }

    /// The exact `Z` arms survive a declared reduction. The reduction is a reading and the carrier
    /// still holds what it held.
    #[test]
    fn the_exact_integer_arms_are_retained_under_a_declared_reduction() {
        let square = Square::hollow();
        let w = Cochain::from_values(1, [(square.dc, big(3))]);
        let two = CoefficientGroup::cyclic(big(2)).unwrap();
        let search = found_potential_in(&square.complex, &w, square.a, two.clone()).unwrap();

        let chord = &search.retained_obstructions[0];
        assert_eq!(chord.declared, big(3), "w(dc) = 3, exactly, in Z");
        assert_eq!(
            chord.implied,
            big(0),
            "and the tree implied 0, exactly, in Z"
        );
        assert_eq!(chord.residual, big(3), "the residual is retained in Z");
        assert_eq!(chord.residual_in(&two), big(1), "and read as 1 in Z/2");
        assert!(!chord.agrees_in(&two));
        assert!(chord.agrees_in(&CoefficientGroup::cyclic(big(3)).unwrap()));
        assert_eq!(search.group, two);
        assert_eq!(search.residuals_in_group().count(), 1);
        assert_eq!(search.residuals_in_group().next(), Some(big(1)));
        assert_eq!(search.standing_residuals(), [big(3)], "and Z beside it");
    }

    /// `Z -> Z/n` is a homomorphism, so a residual that vanished in `Z` vanishes in `Z/n`. The
    /// retained population can only shrink, never grow, and this is the assertion that would catch
    /// a reduction wired in the wrong direction.
    ///
    /// The declared control is the second half: on this material the two populations must actually
    /// **differ** for one of the cochains, or the check above is comparing a thing with itself.
    #[test]
    fn the_reduced_population_is_a_subset_of_the_integer_one_and_the_material_can_separate_them() {
        let square = Square::hollow();
        let two = CoefficientGroup::cyclic(big(2)).unwrap();
        let mut separated = false;
        for value in [-4i64, -3, -2, -1, 0, 1, 2, 3, 4, 6] {
            let w = Cochain::from_values(1, [(square.dc, big(value))]);
            let over_z = found_potential(&square.complex, &w, square.a).unwrap();
            let over_two = found_potential_in(&square.complex, &w, square.a, two.clone()).unwrap();
            assert!(
                over_two.retained_obstructions.iter().all(|reduced| {
                    over_z
                        .retained_obstructions
                        .iter()
                        .any(|exact| exact.cell == reduced.cell)
                }),
                "reduction turned an agreement into an obstruction at w(dc) = {value}"
            );
            if over_two.retained_obstructions.len() < over_z.retained_obstructions.len() {
                separated = true;
            }
        }
        assert!(
            separated,
            "no declared cochain separated the two groups, so the subset assertion above is \
             comparing one population with itself"
        );
    }

    /// The group decides the split and nothing else. Same tree, same chords, same potential.
    #[test]
    fn the_declared_group_moves_neither_the_tree_nor_the_potential() {
        let square = Square::hollow();
        let w = Cochain::from_values(1, [(square.ab, big(4)), (square.dc, big(2))]);
        let over_z = found_potential(&square.complex, &w, square.a).unwrap();
        let over_two = found_potential_in(
            &square.complex,
            &w,
            square.a,
            CoefficientGroup::cyclic(big(2)).unwrap(),
        )
        .unwrap();

        assert_eq!(over_z.tree_cells, over_two.tree_cells);
        assert_eq!(over_z.reached, over_two.reached);
        assert_eq!(
            over_z.potential, over_two.potential,
            "exact in Z either way"
        );
        assert_eq!(over_z.cycle_rank(), over_two.cycle_rank());
        assert_ne!(
            over_z.agreeing_chords, over_two.agreeing_chords,
            "and the split is the one thing that did move"
        );
        assert_eq!(
            over_two.potential_in_group().value(square.b),
            big(0),
            "f(b) = 4 in Z reads as 0 in Z/2, and the reading is where that happens"
        );
        assert_eq!(over_two.potential.value(square.b), big(4));
    }

    /// A modulus is the caller's word and a bad one is refused rather than repaired.
    #[test]
    fn a_modulus_that_is_not_positive_is_refused() {
        for bad in [0i64, -2] {
            let error = CoefficientGroup::cyclic(big(bad)).unwrap_err();
            assert!(matches!(
                error,
                RunningIntegralError::ModulusIsNotPositive(_)
            ));
        }
        assert!(CoefficientGroup::cyclic(big(1)).is_ok(), "Z/1 is a group");
        assert_eq!(CoefficientGroup::Integers.modulus(), None);
        assert_eq!(
            CoefficientGroup::cyclic(big(5)).unwrap().reduce(&big(-3)),
            big(2),
            "the least non-negative residue, not the machine remainder"
        );
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
        assert_ne!(
            direct.chain(),
            detoured.chain(),
            "the backtrack is two more passages over `bc` and the chain retains both"
        );
        assert!(
            direct.chain().minus(&detoured.chain()).difference_is_zero(),
            "they differ by a cancelling pair, so they are one cycle and carry one integral"
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

        let error = running_sum(&square.complex, &square.potential(), &square.left()).unwrap_err();
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
        assert!(
            !boundary.is_zero(),
            "both ends stay attached to `a`; the cancellation is in the difference, not the record"
        );
        assert!(boundary.difference_is_zero());
        assert_eq!(
            boundary.support(),
            BTreeSet::from([a]),
            "the carrier's face relation still names `a`, which is what makes closure decidable"
        );
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

        let pair =
            disagreement(&square.complex, &doubled, &square.left(), &square.right()).unwrap();
        assert_eq!(
            pair.residual,
            big(2),
            "the holonomy is linear in the cochain"
        );
    }
}

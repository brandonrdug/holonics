//! Dimension-independent causal incidence with exact algebraic receivers.
//!
//! This module is the engine's algebraic source presentation. It does not
//! generalize `ReceiverFace`, `SimplicialComplex`, or `LocalStarStanding` in
//! place: those remain concrete realizations. The source carried here is:
//!
//! - an unfolded [`EvolutionShape`];
//! - arbitrary-rank oriented incidence with `boundary(boundary) = 0`;
//! - local finitely presented homogeneous coordinate algebras;
//! - opposed causal ends compared inside one declared region; and
//! - receiver morphisms whose finite observed sections remain quotients of
//!   their source fibers.
//!
//! Counts are primary. Signed coefficients are their exact group completion,
//! represented as a pair of nonnegative populations. Rational evaluations
//! and terminal faces are derived only when a receiver asks for them.

use std::cmp::min;
use std::collections::{BTreeMap, BTreeSet};

use num_bigint::{BigInt, BigUint, Sign};
use num_traits::{One, Zero};
use relational_geometry::{Rat, ReceiverId};
use serde::{Deserialize, Serialize};
use thiserror::Error;

use crate::{
    ConicCellId, ConicError, Edge, EventId, EventSuccessor, EvolutionError, EvolutionShape,
    ExactEventLaw, FaceId, HingeId, HomogeneousConic, NativeConicPopulation, SimplicialComplex,
    VertexId,
};

/// An oriented coefficient held as two nonnegative occurrence counts.
///
/// **The two arms never cancel.** `(positive, negative)` and
/// `(positive + common, negative + common)` share a `difference()` and are
/// nonetheless different coefficients: the second records `common` more
/// passages each way. A loop edge attaches to its vertex twice, once each
/// hand, and its boundary coefficient there is `(1, 1)` — not the absence of
/// an attachment. Deleting the common population would keep the magnitude and
/// discard the turn, which is what a sign does and what this body refuses.
///
/// `difference()` is the group completion to the integers and is what a
/// boundary *map* means; it is a reading of the pair and never replaces it.
/// This mirrors `soma::body::channel::OrientedWinding` and
/// `phase_current::ExactSignedPhasePopulation`, which keep their arms apart for
/// the same reason.
#[derive(Clone, Debug, Default, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct ComparativeMultiplicity {
    positive: BigUint,
    negative: BigUint,
}

impl ComparativeMultiplicity {
    pub fn new(positive: BigUint, negative: BigUint) -> Self {
        Self { positive, negative }
    }

    /// The common population removed — the smallest pair with this difference.
    ///
    /// This is a *reading*, taken by a receiver that has declared it cannot
    /// tell `(p + c, n + c)` from `(p, n)`. Nothing in the complex stores it.
    pub fn reduced(&self) -> Self {
        let common = min(self.positive.clone(), self.negative.clone());
        Self {
            positive: &self.positive - &common,
            negative: &self.negative - &common,
        }
    }

    pub fn positive(count: impl Into<BigUint>) -> Self {
        Self::new(count.into(), BigUint::zero())
    }

    pub fn negative(count: impl Into<BigUint>) -> Self {
        Self::new(BigUint::zero(), count.into())
    }

    pub fn from_hand(hand: i8, count: impl Into<BigUint>) -> Result<Self, CausalAlgebraicError> {
        let count = count.into();
        match hand {
            1 => Ok(Self::positive(count)),
            -1 => Ok(Self::negative(count)),
            _ => Err(CausalAlgebraicError::InvalidOrientationHand(hand)),
        }
    }

    pub fn from_bigint(value: BigInt) -> Self {
        match value.sign() {
            Sign::Plus => Self::positive(value.magnitude().clone()),
            Sign::Minus => Self::negative(value.magnitude().clone()),
            Sign::NoSign => Self::default(),
        }
    }

    pub fn positive_count(&self) -> &BigUint {
        &self.positive
    }

    pub fn negative_count(&self) -> &BigUint {
        &self.negative
    }

    pub fn difference(&self) -> BigInt {
        BigInt::from(self.positive.clone()) - BigInt::from(self.negative.clone())
    }

    /// No passage either way. Distinct from [`Self::difference_is_zero`].
    pub fn is_zero(&self) -> bool {
        self.positive.is_zero() && self.negative.is_zero()
    }

    /// The passages cancel under the group completion.
    ///
    /// `(1, 1)` returns `true` here and `false` from [`Self::is_zero`]: two
    /// passages were taken and the boundary map cannot see them apart. Every
    /// `boundary(boundary) = 0` and cycle check wants *this* predicate; a check
    /// that wants "nothing is attached here" wants `is_zero`.
    pub fn difference_is_zero(&self) -> bool {
        self.positive == self.negative
    }

    pub fn is_unit_orientation(&self) -> bool {
        (self.positive.is_one() && self.negative.is_zero())
            || (self.negative.is_one() && self.positive.is_zero())
    }

    pub fn plus(&self, other: &Self) -> Self {
        Self::new(
            &self.positive + &other.positive,
            &self.negative + &other.negative,
        )
    }

    pub fn negated(&self) -> Self {
        Self {
            positive: self.negative.clone(),
            negative: self.positive.clone(),
        }
    }

    pub fn minus(&self, other: &Self) -> Self {
        self.plus(&other.negated())
    }

    /// The tensor of two arm-pairs, taken on the arms rather than on their
    /// differences: like hands compose to `positive`, unlike hands to
    /// `negative`. `difference()` of the result is the product of the
    /// differences, so every integer reading is unchanged, but a passage
    /// scaled by a cancelling coefficient stays two passages.
    pub fn times(&self, other: &Self) -> Self {
        Self {
            positive: &self.positive * &other.positive + &self.negative * &other.negative,
            negative: &self.positive * &other.negative + &self.negative * &other.positive,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct CausalCellId(pub u64);

/// One finite oriented chain over a [`GradedCausalComplex`].
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct CausalChain {
    coefficients: BTreeMap<CausalCellId, ComparativeMultiplicity>,
}

impl CausalChain {
    pub fn single(cell: CausalCellId, coefficient: ComparativeMultiplicity) -> Self {
        let mut chain = Self::default();
        chain.add_term(cell, coefficient);
        chain
    }

    pub fn coefficients(&self) -> &BTreeMap<CausalCellId, ComparativeMultiplicity> {
        &self.coefficients
    }

    pub fn coefficient(&self, cell: CausalCellId) -> ComparativeMultiplicity {
        self.coefficients.get(&cell).cloned().unwrap_or_default()
    }

    pub fn support(&self) -> BTreeSet<CausalCellId> {
        self.coefficients.keys().copied().collect()
    }

    /// Nothing is deposited on any cell.
    ///
    /// This is the *structural* reading and it is what `support()` reports.
    /// A chain carrying `(1, 1)` on one cell is not zero here: that cell is
    /// attached, twice, once each hand.
    pub fn is_zero(&self) -> bool {
        self.coefficients.is_empty()
    }

    /// Every deposited coefficient cancels under the group completion.
    ///
    /// This is the *algebraic* reading and it is what `boundary(boundary) = 0`
    /// and every cycle condition mean.
    pub fn difference_is_zero(&self) -> bool {
        self.coefficients
            .values()
            .all(ComparativeMultiplicity::difference_is_zero)
    }

    pub fn add_term(&mut self, cell: CausalCellId, coefficient: ComparativeMultiplicity) {
        if coefficient.is_zero() {
            return;
        }
        let next = self
            .coefficients
            .get(&cell)
            .map_or(coefficient.clone(), |current| current.plus(&coefficient));
        // `next` cannot be `is_zero` here — both arms are monotone under
        // `plus` and `coefficient` carried at least one — so the attachment is
        // always retained. Opposed terms on one cell accumulate to `(c, c)`
        // rather than deleting the key, which is what keeps `support()` a
        // face relation instead of a reduced-boundary artifact.
        self.coefficients.insert(cell, next);
    }

    pub fn plus(&self, other: &Self) -> Self {
        let mut result = self.clone();
        for (cell, coefficient) in &other.coefficients {
            result.add_term(*cell, coefficient.clone());
        }
        result
    }

    pub fn negated(&self) -> Self {
        Self {
            coefficients: self
                .coefficients
                .iter()
                .map(|(cell, coefficient)| (*cell, coefficient.negated()))
                .collect(),
        }
    }

    pub fn minus(&self, other: &Self) -> Self {
        self.plus(&other.negated())
    }

    pub fn scaled(&self, factor: &ComparativeMultiplicity) -> Self {
        let mut result = Self::default();
        for (cell, coefficient) in &self.coefficients {
            result.add_term(*cell, coefficient.times(factor));
        }
        result
    }

    pub fn validate(&self) -> Result<(), CausalAlgebraicError> {
        for coefficient in self.coefficients.values() {
            if coefficient.is_zero() {
                return Err(CausalAlgebraicError::StoredZeroCoefficient);
            }
        }
        Ok(())
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CausalCell {
    pub id: CausalCellId,
    pub name: String,
    /// Chain degree. No ambient coordinate dimension is implied.
    pub grade: u32,
    /// All source occurrences contributing to this incidence.
    pub source_events: BTreeSet<EventId>,
    pub boundary: CausalChain,
}

/// Arbitrary-rank oriented incidence with exact group-completed coefficients.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct GradedCausalComplex {
    pub schema: String,
    cells: BTreeMap<CausalCellId, CausalCell>,
    next_cell: u64,
}

impl Default for GradedCausalComplex {
    fn default() -> Self {
        Self {
            schema: "holonic-engine.graded-causal-complex.v1".to_owned(),
            cells: BTreeMap::new(),
            next_cell: 1,
        }
    }
}

impl GradedCausalComplex {
    pub fn cells(&self) -> &BTreeMap<CausalCellId, CausalCell> {
        &self.cells
    }

    pub fn cell(&self, id: CausalCellId) -> Result<&CausalCell, CausalAlgebraicError> {
        self.cells
            .get(&id)
            .ok_or(CausalAlgebraicError::MissingCausalCell(id))
    }

    pub fn dimension(&self) -> Option<u32> {
        self.cells.values().map(|cell| cell.grade).max()
    }

    pub fn f_vector(&self) -> BTreeMap<u32, usize> {
        let mut result = BTreeMap::new();
        for cell in self.cells.values() {
            *result.entry(cell.grade).or_default() += 1;
        }
        result
    }

    pub fn found_cell(
        &mut self,
        name: impl Into<String>,
        source_events: BTreeSet<EventId>,
        grade: u32,
        boundary: CausalChain,
    ) -> Result<CausalCellId, CausalAlgebraicError> {
        if source_events.is_empty() {
            return Err(CausalAlgebraicError::UncausedCell);
        }
        boundary.validate()?;
        if grade == 0 && !boundary.is_zero() {
            return Err(CausalAlgebraicError::VertexHasBoundary);
        }
        for boundary_cell in boundary.support() {
            let cell = self.cell(boundary_cell)?;
            if cell.grade.checked_add(1) != Some(grade) {
                return Err(CausalAlgebraicError::BoundaryGrade {
                    cell: boundary_cell,
                    boundary_grade: cell.grade,
                    carrier_grade: grade,
                });
            }
        }
        let squared = self.boundary_of_chain(&boundary)?;
        if !squared.difference_is_zero() {
            return Err(CausalAlgebraicError::BoundarySquaredNonzero(squared));
        }

        let id = CausalCellId(self.next_cell);
        self.next_cell += 1;
        self.cells.insert(
            id,
            CausalCell {
                id,
                name: name.into(),
                grade,
                source_events,
                boundary,
            },
        );
        Ok(id)
    }

    pub fn boundary_of_chain(
        &self,
        chain: &CausalChain,
    ) -> Result<CausalChain, CausalAlgebraicError> {
        chain.validate()?;
        let mut result = CausalChain::default();
        for (cell, coefficient) in chain.coefficients() {
            let body = self.cell(*cell)?;
            for (boundary_cell, boundary_coefficient) in body.boundary.coefficients() {
                result.add_term(*boundary_cell, coefficient.times(boundary_coefficient));
            }
        }
        Ok(result)
    }

    pub fn homogeneous_grade(
        &self,
        chain: &CausalChain,
    ) -> Result<Option<u32>, CausalAlgebraicError> {
        let mut grade = None;
        for cell in chain.support() {
            let candidate = self.cell(cell)?.grade;
            match grade {
                None => grade = Some(candidate),
                Some(existing) if existing == candidate => {}
                Some(_) => return Err(CausalAlgebraicError::MixedChainGrades),
            }
        }
        Ok(grade)
    }

    pub fn is_closed_support(
        &self,
        support: &BTreeSet<CausalCellId>,
    ) -> Result<bool, CausalAlgebraicError> {
        for cell in support {
            let body = self.cell(*cell)?;
            if !body.boundary.support().is_subset(support) {
                return Ok(false);
            }
        }
        Ok(true)
    }

    pub fn closed_hull<I>(&self, seeds: I) -> Result<BTreeSet<CausalCellId>, CausalAlgebraicError>
    where
        I: IntoIterator<Item = CausalCellId>,
    {
        let mut result = seeds.into_iter().collect::<BTreeSet<_>>();
        let mut frontier = result.iter().copied().collect::<Vec<_>>();
        while let Some(cell) = frontier.pop() {
            for boundary in self.cell(cell)?.boundary.support() {
                if result.insert(boundary) {
                    frontier.push(boundary);
                }
            }
        }
        Ok(result)
    }

    pub fn validate(&self) -> Result<(), CausalAlgebraicError> {
        for (id, cell) in &self.cells {
            if *id != cell.id {
                return Err(CausalAlgebraicError::CausalCellIdentityMismatch {
                    key: *id,
                    body: cell.id,
                });
            }
            if cell.source_events.is_empty() {
                return Err(CausalAlgebraicError::UncausedCell);
            }
            cell.boundary.validate()?;
            if cell.grade == 0 && !cell.boundary.is_zero() {
                return Err(CausalAlgebraicError::VertexHasBoundary);
            }
            for boundary_cell in cell.boundary.support() {
                let boundary = self.cell(boundary_cell)?;
                if boundary.grade.checked_add(1) != Some(cell.grade) {
                    return Err(CausalAlgebraicError::BoundaryGrade {
                        cell: boundary_cell,
                        boundary_grade: boundary.grade,
                        carrier_grade: cell.grade,
                    });
                }
            }
            let squared = self.boundary_of_chain(&cell.boundary)?;
            if !squared.difference_is_zero() {
                return Err(CausalAlgebraicError::BoundarySquaredNonzero(squared));
            }
        }
        if self
            .cells
            .keys()
            .next_back()
            .is_some_and(|id| id.0 >= self.next_cell)
        {
            return Err(CausalAlgebraicError::InvalidNextCellIdentity);
        }
        Ok(())
    }
}

/// Exact incidence of one oriented simplex of arbitrary finite dimension.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct SimplexIncidenceReceipt {
    pub schema: String,
    pub name: String,
    pub dimension: u32,
    pub vertices: Vec<CausalCellId>,
    /// Nonempty ordered vertex subsets name every simplex cell.
    pub cells_by_vertices: BTreeMap<Vec<usize>, CausalCellId>,
    pub apex: CausalCellId,
}

impl SimplexIncidenceReceipt {
    pub fn cell(&self, vertices: &[usize]) -> Option<CausalCellId> {
        self.cells_by_vertices.get(vertices).copied()
    }

    pub fn closure(&self, vertices: &[usize]) -> BTreeSet<CausalCellId> {
        self.cells_by_vertices
            .iter()
            .filter_map(|(candidate, cell)| {
                candidate
                    .iter()
                    .all(|vertex| vertices.contains(vertex))
                    .then_some(*cell)
            })
            .collect()
    }
}

impl GradedCausalComplex {
    /// Atomically found every oriented face of one simplex.
    pub fn found_simplex<I, S>(
        &mut self,
        name: impl Into<String>,
        source_event: EventId,
        vertex_names: I,
    ) -> Result<SimplexIncidenceReceipt, CausalAlgebraicError>
    where
        I: IntoIterator<Item = S>,
        S: Into<String>,
    {
        let name = name.into();
        let vertex_names = vertex_names.into_iter().map(Into::into).collect::<Vec<_>>();
        if vertex_names.is_empty() {
            return Err(CausalAlgebraicError::EmptySimplex);
        }
        let mut candidate = self.clone();
        let receipt = candidate.found_simplex_inner(name, source_event, vertex_names)?;
        candidate.validate()?;
        *self = candidate;
        Ok(receipt)
    }

    fn found_simplex_inner(
        &mut self,
        name: String,
        source_event: EventId,
        vertex_names: Vec<String>,
    ) -> Result<SimplexIncidenceReceipt, CausalAlgebraicError> {
        let mut cells_by_vertices = BTreeMap::new();
        let source_events = BTreeSet::from([source_event]);
        for size in 1..=vertex_names.len() {
            for vertices in combinations(vertex_names.len(), size) {
                let boundary = if size == 1 {
                    CausalChain::default()
                } else {
                    let mut boundary = CausalChain::default();
                    for removed in 0..vertices.len() {
                        let mut face = vertices.clone();
                        face.remove(removed);
                        let face_cell = cells_by_vertices[&face];
                        boundary.add_term(
                            face_cell,
                            ComparativeMultiplicity::from_hand(
                                if removed % 2 == 0 { 1 } else { -1 },
                                1_u8,
                            )?,
                        );
                    }
                    boundary
                };
                let labels = vertices
                    .iter()
                    .map(|index| vertex_names[*index].as_str())
                    .collect::<Vec<_>>()
                    .join(",");
                let cell = self.found_cell(
                    format!("{name}[{labels}]"),
                    source_events.clone(),
                    u32::try_from(size - 1)
                        .map_err(|_| CausalAlgebraicError::ArithmeticOverflow)?,
                    boundary,
                )?;
                cells_by_vertices.insert(vertices, cell);
            }
        }
        let all_vertices = (0..vertex_names.len()).collect::<Vec<_>>();
        let apex = cells_by_vertices[&all_vertices];
        let vertices = (0..vertex_names.len())
            .map(|index| cells_by_vertices[&vec![index]])
            .collect();
        Ok(SimplexIncidenceReceipt {
            schema: "holonic-engine.simplex-incidence-receipt.v1".to_owned(),
            name,
            dimension: u32::try_from(vertex_names.len() - 1)
                .map_err(|_| CausalAlgebraicError::ArithmeticOverflow)?,
            vertices,
            cells_by_vertices,
            apex,
        })
    }
}

fn combinations(population: usize, size: usize) -> Vec<Vec<usize>> {
    fn visit(
        population: usize,
        remaining: usize,
        next: usize,
        prefix: &mut Vec<usize>,
        result: &mut Vec<Vec<usize>>,
    ) {
        if remaining == 0 {
            result.push(prefix.clone());
            return;
        }
        let final_start = population.saturating_sub(remaining);
        for member in next..=final_start {
            prefix.push(member);
            visit(population, remaining - 1, member + 1, prefix, result);
            prefix.pop();
        }
    }

    let mut result = Vec::new();
    visit(
        population,
        size,
        0,
        &mut Vec::with_capacity(size),
        &mut result,
    );
    result
}

/// Identity-preserving incidence migration of the engine's current
/// two-dimensional simplicial realization.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct SimplicialIncidenceReceipt {
    pub schema: String,
    pub incidence: GradedCausalComplex,
    pub vertices: BTreeMap<VertexId, CausalCellId>,
    pub edges: BTreeMap<Edge, CausalCellId>,
    pub faces: BTreeMap<FaceId, CausalCellId>,
    /// A hinge remains a physical relation at its existing edge; it is not
    /// fabricated as a second incidence cell.
    pub hinges: BTreeMap<HingeId, CausalCellId>,
}

impl SimplicialIncidenceReceipt {
    pub fn realize(source: &SimplicialComplex) -> Result<Self, CausalAlgebraicError> {
        for (id, vertex) in &source.vertices {
            if *id != vertex.id {
                return Err(CausalAlgebraicError::SimplicialVertexIdentityMismatch);
            }
        }
        for (id, face) in &source.faces {
            if *id != face.id {
                return Err(CausalAlgebraicError::SimplicialFaceIdentityMismatch);
            }
            if face.vertices[0] == face.vertices[1]
                || face.vertices[1] == face.vertices[2]
                || face.vertices[2] == face.vertices[0]
            {
                return Err(CausalAlgebraicError::CollapsedMigratedFace(face.id));
            }
            for vertex in face.vertices {
                if !source.vertices.contains_key(&vertex) {
                    return Err(CausalAlgebraicError::MigratedFaceMissingVertex {
                        face: face.id,
                        vertex,
                    });
                }
            }
        }
        for (id, hinge) in &source.hinges {
            if *id != hinge.id {
                return Err(CausalAlgebraicError::SimplicialHingeIdentityMismatch);
            }
            let expected = source.edge_cofaces(hinge.edge);
            if expected.as_slice() != hinge.cofaces {
                return Err(CausalAlgebraicError::InvalidMigratedHinge(hinge.id));
            }
        }

        let mut incidence = GradedCausalComplex::default();
        let mut vertices = BTreeMap::new();
        for vertex in source.vertices.values() {
            let cell = incidence.found_cell(
                vertex.name.clone(),
                BTreeSet::from([vertex.source_event]),
                0,
                CausalChain::default(),
            )?;
            vertices.insert(vertex.id, cell);
        }

        let all_edges = source
            .faces
            .values()
            .flat_map(|face| face.boundary().map(|(edge, _)| edge))
            .collect::<BTreeSet<_>>();
        let mut edges = BTreeMap::new();
        for edge in all_edges {
            let mut source_events = BTreeSet::from([
                source.vertices[&edge.lower].source_event,
                source.vertices[&edge.upper].source_event,
            ]);
            source_events.extend(
                source
                    .faces
                    .values()
                    .filter(|face| {
                        face.boundary()
                            .iter()
                            .any(|(candidate, _)| *candidate == edge)
                    })
                    .map(|face| face.source_event),
            );
            source_events.extend(
                source
                    .hinges
                    .values()
                    .filter(|hinge| hinge.edge == edge)
                    .map(|hinge| hinge.source_event),
            );
            let mut boundary = CausalChain::default();
            boundary.add_term(
                vertices[&edge.upper],
                ComparativeMultiplicity::positive(1_u8),
            );
            boundary.add_term(
                vertices[&edge.lower],
                ComparativeMultiplicity::negative(1_u8),
            );
            let cell = incidence.found_cell(
                format!("edge({:?},{:?})", edge.lower, edge.upper),
                source_events,
                1,
                boundary,
            )?;
            edges.insert(edge, cell);
        }

        let mut faces = BTreeMap::new();
        for face in source.faces.values() {
            let mut boundary = CausalChain::default();
            for (edge, hand) in face.boundary() {
                boundary.add_term(
                    edges[&edge],
                    ComparativeMultiplicity::from_hand(hand, 1_u8)?,
                );
            }
            let cell = incidence.found_cell(
                face.name.clone(),
                BTreeSet::from([face.source_event]),
                2,
                boundary,
            )?;
            faces.insert(face.id, cell);
        }

        let hinges = source
            .hinges
            .iter()
            .map(|(id, hinge)| Ok((*id, edges[&hinge.edge])))
            .collect::<Result<BTreeMap<_, _>, CausalAlgebraicError>>()?;
        incidence.validate()?;
        Ok(Self {
            schema: "holonic-engine.simplicial-incidence-receipt.v1".to_owned(),
            incidence,
            vertices,
            edges,
            faces,
            hinges,
        })
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct AlgebraGeneratorId(pub u64);

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct AlgebraRelationId(pub u64);

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct AlgebraGenerator {
    pub id: AlgebraGeneratorId,
    pub name: String,
    /// Positive grading weight. It is comparative degree, not a coordinate
    /// value assigned to the generator.
    pub weight: u32,
    pub source_events: BTreeSet<EventId>,
}

/// One commutative monomial in a finite named generator population.
#[derive(Clone, Debug, Default, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct AlgebraMonomial {
    exponents: BTreeMap<AlgebraGeneratorId, u32>,
}

impl AlgebraMonomial {
    pub fn one() -> Self {
        Self::default()
    }

    pub fn new<I>(exponents: I) -> Self
    where
        I: IntoIterator<Item = (AlgebraGeneratorId, u32)>,
    {
        Self {
            exponents: exponents
                .into_iter()
                .filter(|(_, exponent)| *exponent != 0)
                .collect(),
        }
    }

    pub fn variable(generator: AlgebraGeneratorId) -> Self {
        Self::new([(generator, 1)])
    }

    pub fn exponents(&self) -> &BTreeMap<AlgebraGeneratorId, u32> {
        &self.exponents
    }

    pub fn weighted_degree(
        &self,
        generators: &BTreeMap<AlgebraGeneratorId, AlgebraGenerator>,
    ) -> Result<u32, CausalAlgebraicError> {
        let mut degree = 0_u32;
        for (generator, exponent) in &self.exponents {
            let weight = generators
                .get(generator)
                .ok_or(CausalAlgebraicError::MissingAlgebraGenerator(*generator))?
                .weight;
            degree = degree
                .checked_add(
                    weight
                        .checked_mul(*exponent)
                        .ok_or(CausalAlgebraicError::ArithmeticOverflow)?,
                )
                .ok_or(CausalAlgebraicError::ArithmeticOverflow)?;
        }
        Ok(degree)
    }

    pub fn evaluate(
        &self,
        point: &BTreeMap<AlgebraGeneratorId, Rat>,
    ) -> Result<Rat, CausalAlgebraicError> {
        let mut result = Rat::one();
        for (generator, exponent) in &self.exponents {
            let value = point
                .get(generator)
                .ok_or(CausalAlgebraicError::MissingGeneratorValue(*generator))?;
            for _ in 0..*exponent {
                result *= value;
            }
        }
        Ok(result)
    }
}

/// An exact polynomial whose coefficients remain visibly derived from
/// oriented occurrence populations.
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct HomogeneousPolynomial {
    terms: BTreeMap<AlgebraMonomial, ComparativeMultiplicity>,
}

impl HomogeneousPolynomial {
    pub fn terms(&self) -> &BTreeMap<AlgebraMonomial, ComparativeMultiplicity> {
        &self.terms
    }

    pub fn add_term(&mut self, monomial: AlgebraMonomial, coefficient: ComparativeMultiplicity) {
        if coefficient.is_zero() {
            return;
        }
        let next = self
            .terms
            .get(&monomial)
            .map_or(coefficient.clone(), |current| current.plus(&coefficient));
        if next.is_zero() {
            self.terms.remove(&monomial);
        } else {
            self.terms.insert(monomial, next);
        }
    }

    pub fn is_zero(&self) -> bool {
        self.terms.is_empty()
    }

    pub fn homogeneous_degree(
        &self,
        generators: &BTreeMap<AlgebraGeneratorId, AlgebraGenerator>,
    ) -> Result<Option<u32>, CausalAlgebraicError> {
        let mut degree = None;
        for monomial in self.terms.keys() {
            let candidate = monomial.weighted_degree(generators)?;
            match degree {
                None => degree = Some(candidate),
                Some(existing) if existing == candidate => {}
                Some(_) => return Err(CausalAlgebraicError::InhomogeneousRelation),
            }
        }
        Ok(degree)
    }

    pub fn evaluate(
        &self,
        point: &BTreeMap<AlgebraGeneratorId, Rat>,
    ) -> Result<Rat, CausalAlgebraicError> {
        let mut result = Rat::zero();
        for (monomial, coefficient) in &self.terms {
            result += Rat::from_integer(coefficient.difference()) * monomial.evaluate(point)?;
        }
        Ok(result)
    }

    fn linear_coefficient(&self, generator: AlgebraGeneratorId) -> BigInt {
        self.terms
            .iter()
            .filter(|(monomial, _)| {
                monomial.exponents.len() == 1
                    && monomial.exponents.get(&generator).copied() == Some(1)
            })
            .map(|(_, coefficient)| coefficient.difference())
            .fold(BigInt::zero(), |sum, coefficient| sum + coefficient)
    }

    pub fn validate(
        &self,
        generators: &BTreeMap<AlgebraGeneratorId, AlgebraGenerator>,
    ) -> Result<u32, CausalAlgebraicError> {
        if self.is_zero() {
            return Err(CausalAlgebraicError::ZeroAlgebraRelation);
        }
        let degree = self
            .homogeneous_degree(generators)?
            .ok_or(CausalAlgebraicError::ZeroAlgebraRelation)?;
        if degree == 0 {
            return Err(CausalAlgebraicError::ConstantAlgebraRelation);
        }
        Ok(degree)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct AlgebraRelation {
    pub id: AlgebraRelationId,
    pub name: String,
    pub source_events: BTreeSet<EventId>,
    pub degree: u32,
    pub polynomial: HomogeneousPolynomial,
}

/// A finite exact presentation of a graded commutative coordinate algebra.
///
/// This is deliberately not encoded through `ExactValue::Expression`: the
/// generators, ideal relations, grading, and causal provenance are structural
/// and must remain independently inspectable.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct GradedAlgebraPresentation {
    pub schema: String,
    generators: BTreeMap<AlgebraGeneratorId, AlgebraGenerator>,
    relations: BTreeMap<AlgebraRelationId, AlgebraRelation>,
    next_generator: u64,
    next_relation: u64,
}

impl Default for GradedAlgebraPresentation {
    fn default() -> Self {
        Self {
            schema: "holonic-engine.graded-algebra-presentation.v1".to_owned(),
            generators: BTreeMap::new(),
            relations: BTreeMap::new(),
            next_generator: 1,
            next_relation: 1,
        }
    }
}

impl GradedAlgebraPresentation {
    pub fn generators(&self) -> &BTreeMap<AlgebraGeneratorId, AlgebraGenerator> {
        &self.generators
    }

    pub fn relations(&self) -> &BTreeMap<AlgebraRelationId, AlgebraRelation> {
        &self.relations
    }

    pub fn add_generator(
        &mut self,
        name: impl Into<String>,
        weight: u32,
        source_events: BTreeSet<EventId>,
    ) -> Result<AlgebraGeneratorId, CausalAlgebraicError> {
        if weight == 0 {
            return Err(CausalAlgebraicError::ZeroGeneratorWeight);
        }
        if source_events.is_empty() {
            return Err(CausalAlgebraicError::UncausedAlgebraMember);
        }
        let id = AlgebraGeneratorId(self.next_generator);
        self.next_generator += 1;
        self.generators.insert(
            id,
            AlgebraGenerator {
                id,
                name: name.into(),
                weight,
                source_events,
            },
        );
        Ok(id)
    }

    pub fn add_relation(
        &mut self,
        name: impl Into<String>,
        source_events: BTreeSet<EventId>,
        polynomial: HomogeneousPolynomial,
    ) -> Result<AlgebraRelationId, CausalAlgebraicError> {
        if source_events.is_empty() {
            return Err(CausalAlgebraicError::UncausedAlgebraMember);
        }
        let degree = polynomial.validate(&self.generators)?;
        let id = AlgebraRelationId(self.next_relation);
        self.next_relation += 1;
        self.relations.insert(
            id,
            AlgebraRelation {
                id,
                name: name.into(),
                source_events,
                degree,
                polynomial,
            },
        );
        Ok(id)
    }

    pub fn evaluate_relations(
        &self,
        point: &BTreeMap<AlgebraGeneratorId, Rat>,
    ) -> Result<BTreeMap<AlgebraRelationId, Rat>, CausalAlgebraicError> {
        for generator in self.generators.keys() {
            if !point.contains_key(generator) {
                return Err(CausalAlgebraicError::MissingGeneratorValue(*generator));
            }
        }
        self.relations
            .iter()
            .map(|(id, relation)| Ok((*id, relation.polynomial.evaluate(point)?)))
            .collect()
    }

    /// Exact dimension of the Zariski tangent carrier at the homogeneous
    /// origin, obtained as nullity of the exact linearized relation matrix.
    pub fn tangent_dimension_at_homogeneous_origin(&self) -> usize {
        let generators = self.generators.keys().copied().collect::<Vec<_>>();
        let mut matrix = self
            .relations
            .values()
            .map(|relation| {
                generators
                    .iter()
                    .map(|generator| {
                        Rat::from_integer(relation.polynomial.linear_coefficient(*generator))
                    })
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();
        generators.len() - exact_rational_rank(&mut matrix)
    }

    /// Sound bounded dimension testimony. General ideal dimension is kept
    /// open until an exact Gröbner/Hilbert certificate is supplied.
    pub fn dimension_certificate(&self) -> AlgebraDimensionCertificate {
        let generator_count = self.generators.len();
        match self.relations.len() {
            0 => AlgebraDimensionCertificate::AffineSpace {
                affine_dimension: generator_count,
                projective_horizon_dimension: generator_count.checked_sub(1),
            },
            1 => AlgebraDimensionCertificate::PrincipalHypersurface {
                affine_dimension: generator_count.saturating_sub(1),
                projective_horizon_dimension: generator_count.checked_sub(2),
            },
            relation_count => AlgebraDimensionCertificate::Open {
                generator_count,
                relation_count,
            },
        }
    }

    pub fn center_horizon(&self) -> CenterHorizonReceipt {
        CenterHorizonReceipt {
            schema: "holonic-engine.center-horizon-receipt.v1".to_owned(),
            generator_weights: self
                .generators
                .iter()
                .map(|(id, generator)| (*id, generator.weight))
                .collect(),
            homogeneous_relations: self.relations.keys().copied().collect(),
            tangent_dimension_at_center: self.tangent_dimension_at_homogeneous_origin(),
            dimension: self.dimension_certificate(),
        }
    }

    pub fn validate(&self) -> Result<(), CausalAlgebraicError> {
        for (id, generator) in &self.generators {
            if *id != generator.id {
                return Err(CausalAlgebraicError::AlgebraGeneratorIdentityMismatch);
            }
            if generator.weight == 0 {
                return Err(CausalAlgebraicError::ZeroGeneratorWeight);
            }
            if generator.source_events.is_empty() {
                return Err(CausalAlgebraicError::UncausedAlgebraMember);
            }
        }
        for (id, relation) in &self.relations {
            if *id != relation.id {
                return Err(CausalAlgebraicError::AlgebraRelationIdentityMismatch);
            }
            if relation.source_events.is_empty() {
                return Err(CausalAlgebraicError::UncausedAlgebraMember);
            }
            if relation.polynomial.validate(&self.generators)? != relation.degree {
                return Err(CausalAlgebraicError::RelationDegreeMismatch);
            }
        }
        if self
            .generators
            .keys()
            .next_back()
            .is_some_and(|id| id.0 >= self.next_generator)
            || self
                .relations
                .keys()
                .next_back()
                .is_some_and(|id| id.0 >= self.next_relation)
        {
            return Err(CausalAlgebraicError::InvalidNextAlgebraIdentity);
        }
        Ok(())
    }
}

fn exact_rational_rank(matrix: &mut [Vec<Rat>]) -> usize {
    if matrix.is_empty() {
        return 0;
    }
    let rows = matrix.len();
    let columns = matrix[0].len();
    let mut rank = 0;
    for column in 0..columns {
        let Some(pivot) = (rank..rows).find(|row| !matrix[*row][column].is_zero()) else {
            continue;
        };
        matrix.swap(rank, pivot);
        let pivot_value = matrix[rank][column].clone();
        for value in matrix[rank].iter_mut().skip(column) {
            *value /= &pivot_value;
        }
        let pivot_row = matrix[rank].clone();
        for (row_index, row) in matrix.iter_mut().enumerate() {
            if row_index == rank || row[column].is_zero() {
                continue;
            }
            let factor = row[column].clone();
            for (value, pivot_value) in row.iter_mut().zip(&pivot_row).skip(column) {
                *value -= &factor * pivot_value;
            }
        }
        rank += 1;
        if rank == rows {
            break;
        }
    }
    rank
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum AlgebraDimensionCertificate {
    AffineSpace {
        affine_dimension: usize,
        projective_horizon_dimension: Option<usize>,
    },
    PrincipalHypersurface {
        affine_dimension: usize,
        projective_horizon_dimension: Option<usize>,
    },
    Open {
        generator_count: usize,
        relation_count: usize,
    },
}

/// Exact directional algebra at a homogeneous center.
///
/// This receipt is the projectivized tangent-cone presentation already
/// justified by homogeneous data. It does not claim a general Rees-algebra
/// blow-up for an arbitrary nonhomogeneous ideal.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CenterHorizonReceipt {
    pub schema: String,
    pub generator_weights: BTreeMap<AlgebraGeneratorId, u32>,
    pub homogeneous_relations: BTreeSet<AlgebraRelationId>,
    pub tangent_dimension_at_center: usize,
    pub dimension: AlgebraDimensionCertificate,
}

/// Algebraic migration testimony for one native homogeneous conic.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ConicAlgebraReceipt {
    pub schema: String,
    pub conic: ConicCellId,
    pub generators: [AlgebraGeneratorId; 3],
    pub relation: AlgebraRelationId,
    /// Multiplying the native rational equation by this nonzero integer gives
    /// the stored comparative polynomial.
    pub clearing_factor: BigInt,
    pub algebra: GradedAlgebraPresentation,
}

impl ConicAlgebraReceipt {
    pub fn realize(
        conic: ConicCellId,
        name: &str,
        source_event: EventId,
        form: &HomogeneousConic,
    ) -> Result<Self, CausalAlgebraicError> {
        let mut algebra = GradedAlgebraPresentation::default();
        let source_events = BTreeSet::from([source_event]);
        let x = algebra.add_generator("x", 1, source_events.clone())?;
        let y = algebra.add_generator("y", 1, source_events.clone())?;
        let w = algebra.add_generator("w", 1, source_events.clone())?;
        let coefficients = form.coefficients();
        let clearing_factor = coefficients
            .iter()
            .fold(BigInt::one(), |factor, coefficient| {
                factor * coefficient.denom()
            });
        let monomials = [
            AlgebraMonomial::new([(x, 2)]),
            AlgebraMonomial::new([(x, 1), (y, 1)]),
            AlgebraMonomial::new([(y, 2)]),
            AlgebraMonomial::new([(x, 1), (w, 1)]),
            AlgebraMonomial::new([(y, 1), (w, 1)]),
            AlgebraMonomial::new([(w, 2)]),
        ];
        let mut polynomial = HomogeneousPolynomial::default();
        for (monomial, coefficient) in monomials.into_iter().zip(coefficients) {
            let cleared = coefficient * Rat::from_integer(clearing_factor.clone());
            if !cleared.denom().is_one() {
                return Err(CausalAlgebraicError::FailedToClearDenominators);
            }
            polynomial.add_term(
                monomial,
                ComparativeMultiplicity::from_bigint(cleared.numer().clone()),
            );
        }
        let relation =
            algebra.add_relation(format!("{name} homogeneous law"), source_events, polynomial)?;
        algebra.validate()?;
        Ok(Self {
            schema: "holonic-engine.conic-algebra-receipt.v1".to_owned(),
            conic,
            generators: [x, y, w],
            relation,
            clearing_factor,
            algebra,
        })
    }

    pub fn evaluate(&self, point: [Rat; 3]) -> Result<Rat, CausalAlgebraicError> {
        let values = self
            .generators
            .iter()
            .copied()
            .zip(point)
            .collect::<BTreeMap<_, _>>();
        self.algebra.relations[&self.relation]
            .polynomial
            .evaluate(&values)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct LocalAlgebraId(pub u64);

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct CausalRegionId(pub u64);

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct CausalEndId(pub u64);

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct LocalCoordinateAlgebra {
    pub id: LocalAlgebraId,
    pub name: String,
    pub source_event: EventId,
    pub presentation: GradedAlgebraPresentation,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CausalRegion {
    pub id: CausalRegionId,
    pub name: String,
    /// Boundary-closed incidence carried by this local holon.
    pub support: BTreeSet<CausalCellId>,
    pub local_algebras: BTreeSet<LocalAlgebraId>,
    pub source_event: EventId,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum CausalEndHand {
    Incoming,
    Outgoing,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CausalEnd {
    pub id: CausalEndId,
    pub name: String,
    pub region: CausalRegionId,
    pub hand: CausalEndHand,
    pub section: CausalChain,
    pub source_event: EventId,
}

/// One dimension-independent causal algebraic source presentation.
///
/// Its chronology, incidence, local coordinate algebras, regions, and ends
/// are co-validated. A receiver face may be realized from this source but is
/// never stored as its standing authority.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CausalAlgebraicPresentation {
    pub schema: String,
    pub evolution: EvolutionShape,
    pub incidence: GradedCausalComplex,
    local_algebras: BTreeMap<LocalAlgebraId, LocalCoordinateAlgebra>,
    regions: BTreeMap<CausalRegionId, CausalRegion>,
    ends: BTreeMap<CausalEndId, CausalEnd>,
    next_local_algebra: u64,
    next_region: u64,
    next_end: u64,
}

impl CausalAlgebraicPresentation {
    pub fn new(
        evolution: EvolutionShape,
        incidence: GradedCausalComplex,
    ) -> Result<Self, CausalAlgebraicError> {
        let result = Self {
            schema: "holonic-engine.causal-algebraic-presentation.v1".to_owned(),
            evolution,
            incidence,
            local_algebras: BTreeMap::new(),
            regions: BTreeMap::new(),
            ends: BTreeMap::new(),
            next_local_algebra: 1,
            next_region: 1,
            next_end: 1,
        };
        result.validate()?;
        Ok(result)
    }

    pub fn local_algebras(&self) -> &BTreeMap<LocalAlgebraId, LocalCoordinateAlgebra> {
        &self.local_algebras
    }

    pub fn regions(&self) -> &BTreeMap<CausalRegionId, CausalRegion> {
        &self.regions
    }

    pub fn ends(&self) -> &BTreeMap<CausalEndId, CausalEnd> {
        &self.ends
    }

    pub fn local_algebra(
        &self,
        id: LocalAlgebraId,
    ) -> Result<&LocalCoordinateAlgebra, CausalAlgebraicError> {
        self.local_algebras
            .get(&id)
            .ok_or(CausalAlgebraicError::MissingLocalAlgebra(id))
    }

    pub fn region(&self, id: CausalRegionId) -> Result<&CausalRegion, CausalAlgebraicError> {
        self.regions
            .get(&id)
            .ok_or(CausalAlgebraicError::MissingCausalRegion(id))
    }

    pub fn end(&self, id: CausalEndId) -> Result<&CausalEnd, CausalAlgebraicError> {
        self.ends
            .get(&id)
            .ok_or(CausalAlgebraicError::MissingCausalEnd(id))
    }

    pub fn add_local_algebra(
        &mut self,
        name: impl Into<String>,
        source_event: EventId,
        mut presentation: GradedAlgebraPresentation,
    ) -> Result<LocalAlgebraId, CausalAlgebraicError> {
        self.require_event(source_event)?;
        for generator in presentation.generators.values_mut() {
            generator.source_events.insert(source_event);
        }
        for relation in presentation.relations.values_mut() {
            relation.source_events.insert(source_event);
        }
        presentation.validate()?;
        self.validate_algebra_events(&presentation)?;
        let id = LocalAlgebraId(self.next_local_algebra);
        self.next_local_algebra += 1;
        self.local_algebras.insert(
            id,
            LocalCoordinateAlgebra {
                id,
                name: name.into(),
                source_event,
                presentation,
            },
        );
        Ok(id)
    }

    pub fn found_region(
        &mut self,
        name: impl Into<String>,
        support: BTreeSet<CausalCellId>,
        local_algebras: BTreeSet<LocalAlgebraId>,
        source_event: EventId,
    ) -> Result<CausalRegionId, CausalAlgebraicError> {
        self.require_event(source_event)?;
        if support.is_empty() {
            return Err(CausalAlgebraicError::EmptyCausalRegion);
        }
        if !self.incidence.is_closed_support(&support)? {
            return Err(CausalAlgebraicError::RegionSupportNotClosed);
        }
        for algebra in &local_algebras {
            self.local_algebra(*algebra)?;
        }
        let id = CausalRegionId(self.next_region);
        self.next_region += 1;
        self.regions.insert(
            id,
            CausalRegion {
                id,
                name: name.into(),
                support,
                local_algebras,
                source_event,
            },
        );
        Ok(id)
    }

    pub fn found_end(
        &mut self,
        name: impl Into<String>,
        region: CausalRegionId,
        hand: CausalEndHand,
        section: CausalChain,
        source_event: EventId,
    ) -> Result<CausalEndId, CausalAlgebraicError> {
        self.require_event(source_event)?;
        section.validate()?;
        let region_body = self.region(region)?;
        if !section.support().is_subset(&region_body.support) {
            return Err(CausalAlgebraicError::SectionOutsideRegion);
        }
        self.incidence.homogeneous_grade(&section)?;
        let id = CausalEndId(self.next_end);
        self.next_end += 1;
        self.ends.insert(
            id,
            CausalEnd {
                id,
                name: name.into(),
                region,
                hand,
                section,
                source_event,
            },
        );
        Ok(id)
    }

    /// Compare opposed ends only after transporting them into one declared
    /// local region. The result is an exact chain receipt, not a stored scalar.
    pub fn compare_opposed_ends(
        &self,
        query: &RelativeBoundaryQuery,
    ) -> Result<RelativeBoundaryReceipt, CausalAlgebraicError> {
        let region = self.region(query.region)?;
        let incoming = self.end(query.incoming)?;
        let outgoing = self.end(query.outgoing)?;
        if incoming.region != query.region || outgoing.region != query.region {
            return Err(CausalAlgebraicError::EndRegionMismatch);
        }
        if incoming.hand != CausalEndHand::Incoming || outgoing.hand != CausalEndHand::Outgoing {
            return Err(CausalAlgebraicError::OpposedEndHandMismatch);
        }
        if !query.boundary.support().is_subset(&region.support) {
            return Err(CausalAlgebraicError::SectionOutsideRegion);
        }
        let boundary_grade = self.incidence.homogeneous_grade(&query.boundary)?;
        let incoming_grade = self.incidence.homogeneous_grade(&incoming.section)?;
        let outgoing_grade = self.incidence.homogeneous_grade(&outgoing.section)?;
        if boundary_grade != incoming_grade || boundary_grade != outgoing_grade {
            return Err(CausalAlgebraicError::RelativeBoundaryGradeMismatch);
        }
        let residual = query
            .boundary
            .minus(&outgoing.section)
            .plus(&incoming.section);
        Ok(RelativeBoundaryReceipt {
            schema: "holonic-engine.relative-boundary-receipt.v1".to_owned(),
            region: query.region,
            boundary: query.boundary.clone(),
            incoming: incoming.section.clone(),
            outgoing: outgoing.section.clone(),
            residual,
        })
    }

    pub fn validate(&self) -> Result<(), CausalAlgebraicError> {
        self.evolution.validate()?;
        self.incidence.validate()?;
        for cell in self.incidence.cells.values() {
            for event in &cell.source_events {
                self.require_event(*event)?;
            }
        }
        for (id, algebra) in &self.local_algebras {
            if *id != algebra.id {
                return Err(CausalAlgebraicError::LocalAlgebraIdentityMismatch);
            }
            self.require_event(algebra.source_event)?;
            algebra.presentation.validate()?;
            self.validate_algebra_events(&algebra.presentation)?;
        }
        for (id, region) in &self.regions {
            if *id != region.id {
                return Err(CausalAlgebraicError::CausalRegionIdentityMismatch);
            }
            self.require_event(region.source_event)?;
            if region.support.is_empty() {
                return Err(CausalAlgebraicError::EmptyCausalRegion);
            }
            if !self.incidence.is_closed_support(&region.support)? {
                return Err(CausalAlgebraicError::RegionSupportNotClosed);
            }
            for algebra in &region.local_algebras {
                self.local_algebra(*algebra)?;
            }
        }
        for (id, end) in &self.ends {
            if *id != end.id {
                return Err(CausalAlgebraicError::CausalEndIdentityMismatch);
            }
            self.require_event(end.source_event)?;
            let region = self.region(end.region)?;
            if !end.section.support().is_subset(&region.support) {
                return Err(CausalAlgebraicError::SectionOutsideRegion);
            }
            self.incidence.homogeneous_grade(&end.section)?;
        }
        if self
            .local_algebras
            .keys()
            .next_back()
            .is_some_and(|id| id.0 >= self.next_local_algebra)
            || self
                .regions
                .keys()
                .next_back()
                .is_some_and(|id| id.0 >= self.next_region)
            || self
                .ends
                .keys()
                .next_back()
                .is_some_and(|id| id.0 >= self.next_end)
        {
            return Err(CausalAlgebraicError::InvalidNextPresentationIdentity);
        }
        Ok(())
    }

    fn require_event(&self, event: EventId) -> Result<(), CausalAlgebraicError> {
        if !self.evolution.occurrences.contains_key(&event) {
            return Err(CausalAlgebraicError::MissingSourceOccurrence(event));
        }
        Ok(())
    }

    fn validate_algebra_events(
        &self,
        algebra: &GradedAlgebraPresentation,
    ) -> Result<(), CausalAlgebraicError> {
        for event in algebra
            .generators
            .values()
            .flat_map(|generator| &generator.source_events)
            .chain(
                algebra
                    .relations
                    .values()
                    .flat_map(|relation| &relation.source_events),
            )
        {
            self.require_event(*event)?;
        }
        Ok(())
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct RelativeBoundaryQuery {
    pub region: CausalRegionId,
    pub boundary: CausalChain,
    pub incoming: CausalEndId,
    pub outgoing: CausalEndId,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct RelativeBoundaryReceipt {
    pub schema: String,
    pub region: CausalRegionId,
    pub boundary: CausalChain,
    pub incoming: CausalChain,
    pub outgoing: CausalChain,
    pub residual: CausalChain,
}

/// A chain morphism restricted to one exact boundary-closed source section.
///
/// Each source cell may map to a chain or vanish. Boundary commutation is
/// verified for every admitted cell, so a top face cannot be received without
/// its actual lower-dimensional closure.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CausalSectionMorphism {
    pub schema: String,
    pub name: String,
    source_support: BTreeSet<CausalCellId>,
    images: BTreeMap<CausalCellId, CausalChain>,
}

impl CausalSectionMorphism {
    pub fn new(
        name: impl Into<String>,
        source: &GradedCausalComplex,
        target: &GradedCausalComplex,
        source_support: BTreeSet<CausalCellId>,
        images: BTreeMap<CausalCellId, CausalChain>,
    ) -> Result<Self, CausalAlgebraicError> {
        let result = Self {
            schema: "holonic-engine.causal-section-morphism.v1".to_owned(),
            name: name.into(),
            source_support,
            images,
        };
        result.validate(source, target)?;
        Ok(result)
    }

    pub fn source_support(&self) -> &BTreeSet<CausalCellId> {
        &self.source_support
    }

    pub fn images(&self) -> &BTreeMap<CausalCellId, CausalChain> {
        &self.images
    }

    pub fn map_chain(
        &self,
        source: &GradedCausalComplex,
        chain: &CausalChain,
    ) -> Result<CausalChain, CausalAlgebraicError> {
        source.homogeneous_grade(chain)?;
        if !chain.support().is_subset(&self.source_support) {
            return Err(CausalAlgebraicError::ChainOutsideReceiverSection);
        }
        let mut result = CausalChain::default();
        for (cell, coefficient) in chain.coefficients() {
            let image = self
                .images
                .get(cell)
                .ok_or(CausalAlgebraicError::MissingMorphismImage(*cell))?;
            result = result.plus(&image.scaled(coefficient));
        }
        Ok(result)
    }

    pub fn validate(
        &self,
        source: &GradedCausalComplex,
        target: &GradedCausalComplex,
    ) -> Result<(), CausalAlgebraicError> {
        source.validate()?;
        target.validate()?;
        if !source.is_closed_support(&self.source_support)? {
            return Err(CausalAlgebraicError::ReceiverSectionNotClosed);
        }
        if self.images.keys().copied().collect::<BTreeSet<_>>() != self.source_support {
            return Err(CausalAlgebraicError::MorphismImageDomainMismatch);
        }
        for source_cell in &self.source_support {
            let body = source.cell(*source_cell)?;
            let image = &self.images[source_cell];
            let image_grade = target.homogeneous_grade(image)?;
            if !image.is_zero() && image_grade != Some(body.grade) {
                return Err(CausalAlgebraicError::MorphismGradeMismatch {
                    source_cell: *source_cell,
                    source_grade: body.grade,
                    image_grade,
                });
            }
            let boundary_of_image = target.boundary_of_chain(image)?;
            let image_of_boundary = self.map_chain(source, &body.boundary)?;
            if boundary_of_image != image_of_boundary {
                return Err(CausalAlgebraicError::MorphismBoundaryMismatch {
                    source_cell: *source_cell,
                    boundary_of_image,
                    image_of_boundary,
                });
            }
        }
        Ok(())
    }
}

/// One receiver is a declared exact morphism, not an absolute camera.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct AlgebraicReceiver {
    pub schema: String,
    pub id: ReceiverId,
    pub morphism: CausalSectionMorphism,
}

impl AlgebraicReceiver {
    pub fn receive(
        &self,
        source: &GradedCausalComplex,
        target: &GradedCausalComplex,
        section: &CausalChain,
    ) -> Result<AlgebraicReceiverReceipt, CausalAlgebraicError> {
        self.morphism.validate(source, target)?;
        let observed = self.morphism.map_chain(source, section)?;
        let mut source_fibers = BTreeMap::<CausalCellId, BTreeSet<CausalCellId>>::new();
        for source_cell in section.support() {
            for target_cell in self.morphism.images[&source_cell].support() {
                source_fibers
                    .entry(target_cell)
                    .or_default()
                    .insert(source_cell);
            }
        }
        Ok(AlgebraicReceiverReceipt {
            schema: "holonic-engine.algebraic-receiver-receipt.v1".to_owned(),
            receiver: self.id,
            source_section: section.clone(),
            observed,
            source_fibers,
        })
    }
}

/// Engine-minted observation testimony. The observed quotient and its source
/// fibers are intentionally inseparable.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct AlgebraicReceiverReceipt {
    schema: String,
    receiver: ReceiverId,
    source_section: CausalChain,
    observed: CausalChain,
    source_fibers: BTreeMap<CausalCellId, BTreeSet<CausalCellId>>,
}

impl AlgebraicReceiverReceipt {
    pub fn schema(&self) -> &str {
        &self.schema
    }

    pub fn receiver(&self) -> ReceiverId {
        self.receiver
    }

    pub fn source_section(&self) -> &CausalChain {
        &self.source_section
    }

    pub fn observed(&self) -> &CausalChain {
        &self.observed
    }

    pub fn source_fibers(&self) -> &BTreeMap<CausalCellId, BTreeSet<CausalCellId>> {
        &self.source_fibers
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct BoundConicAlgebra {
    pub local_algebra: LocalAlgebraId,
    pub generators: [AlgebraGeneratorId; 3],
    pub relation: AlgebraRelationId,
    pub clearing_factor: BigInt,
    pub face: FaceId,
}

/// Exact migration of the current tetrahedral/conic engine into one
/// dimension-independent presentation. The caller must declare every
/// conic-to-face attachment; the adapter never invents support from proximity.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct SimplicialConicAlgebraicReceipt {
    pub schema: String,
    pub presentation: CausalAlgebraicPresentation,
    pub vertices: BTreeMap<VertexId, CausalCellId>,
    pub edges: BTreeMap<Edge, CausalCellId>,
    pub faces: BTreeMap<FaceId, CausalCellId>,
    pub hinges: BTreeMap<HingeId, CausalCellId>,
    pub face_regions: BTreeMap<FaceId, CausalRegionId>,
    pub conics: BTreeMap<ConicCellId, BoundConicAlgebra>,
}

impl SimplicialConicAlgebraicReceipt {
    pub fn realize(
        evolution: EvolutionShape,
        simplicial: &SimplicialComplex,
        conics: &NativeConicPopulation,
        bindings: &BTreeMap<ConicCellId, FaceId>,
    ) -> Result<Self, CausalAlgebraicError> {
        conics.validate_sources(&evolution)?;
        for conic in conics.cells.keys() {
            if !bindings.contains_key(conic) {
                return Err(CausalAlgebraicError::MissingConicFaceBinding(*conic));
            }
        }
        for (conic, face) in bindings {
            if !conics.cells.contains_key(conic) {
                return Err(CausalAlgebraicError::UnknownBoundConic(*conic));
            }
            if !simplicial.faces.contains_key(face) {
                return Err(CausalAlgebraicError::UnknownBoundFace(*face));
            }
        }

        let simplicial_receipt = SimplicialIncidenceReceipt::realize(simplicial)?;
        let mut presentation =
            CausalAlgebraicPresentation::new(evolution, simplicial_receipt.incidence.clone())?;
        let mut bound_conics = BTreeMap::new();
        let mut algebras_by_face = BTreeMap::<FaceId, BTreeSet<LocalAlgebraId>>::new();
        for cell in conics.cells.values() {
            let receipt =
                ConicAlgebraReceipt::realize(cell.id, &cell.name, cell.source_event, &cell.form)?;
            let local_algebra = presentation.add_local_algebra(
                format!("{} local coordinate algebra", cell.name),
                cell.source_event,
                receipt.algebra,
            )?;
            let face = bindings[&cell.id];
            algebras_by_face
                .entry(face)
                .or_default()
                .insert(local_algebra);
            bound_conics.insert(
                cell.id,
                BoundConicAlgebra {
                    local_algebra,
                    generators: receipt.generators,
                    relation: receipt.relation,
                    clearing_factor: receipt.clearing_factor,
                    face,
                },
            );
        }

        let mut face_regions = BTreeMap::new();
        for (face, local_algebras) in algebras_by_face {
            let source_face = &simplicial.faces[&face];
            let face_cell = simplicial_receipt.faces[&face];
            let support = presentation.incidence.closed_hull([face_cell])?;
            let region = presentation.found_region(
                format!("{} caused local region", source_face.name),
                support,
                local_algebras,
                source_face.source_event,
            )?;
            face_regions.insert(face, region);
        }
        presentation.validate()?;
        Ok(Self {
            schema: "holonic-engine.simplicial-conic-algebraic-receipt.v1".to_owned(),
            presentation,
            vertices: simplicial_receipt.vertices,
            edges: simplicial_receipt.edges,
            faces: simplicial_receipt.faces,
            hinges: simplicial_receipt.hinges,
            face_regions,
            conics: bound_conics,
        })
    }
}

/// Primitive deeds admitted by the production algebraic transition.
///
/// Deeds carry proposed structure, while the law supplies occurrence
/// provenance, validates all contemporary references, and atomically commits
/// the complete presentation.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum CausalAlgebraicDeed {
    FoundCell {
        name: String,
        grade: u32,
        boundary: CausalChain,
    },
    AddLocalAlgebra {
        name: String,
        presentation: GradedAlgebraPresentation,
    },
    FoundRegion {
        name: String,
        support: BTreeSet<CausalCellId>,
        local_algebras: BTreeSet<LocalAlgebraId>,
    },
    FoundEnd {
        name: String,
        region: CausalRegionId,
        hand: CausalEndHand,
        section: CausalChain,
    },
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CausalAlgebraicEvent {
    pub occurrence: EventId,
    pub deeds: Vec<CausalAlgebraicDeed>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum CausalAlgebraicRadiation {
    CellFounded(CausalCellId),
    LocalAlgebraFounded(LocalAlgebraId),
    RegionFounded(CausalRegionId),
    EndFounded(CausalEndId),
}

#[derive(Clone, Copy, Debug, Default)]
pub struct CausalAlgebraicLaw;

impl ExactEventLaw for CausalAlgebraicLaw {
    type Standing = CausalAlgebraicPresentation;
    type Event = CausalAlgebraicEvent;
    type Radiation = CausalAlgebraicRadiation;
    type Error = CausalAlgebraicError;

    fn enact(
        &self,
        standing_before: &Self::Standing,
        event: &Self::Event,
    ) -> Result<EventSuccessor<Self::Standing, Self::Radiation>, Self::Error> {
        standing_before.require_event(event.occurrence)?;
        let mut standing_after = standing_before.clone();
        let mut radiation = Vec::with_capacity(event.deeds.len());
        for deed in &event.deeds {
            let emitted = match deed {
                CausalAlgebraicDeed::FoundCell {
                    name,
                    grade,
                    boundary,
                } => CausalAlgebraicRadiation::CellFounded(standing_after.incidence.found_cell(
                    name.clone(),
                    BTreeSet::from([event.occurrence]),
                    *grade,
                    boundary.clone(),
                )?),
                CausalAlgebraicDeed::AddLocalAlgebra { name, presentation } => {
                    CausalAlgebraicRadiation::LocalAlgebraFounded(
                        standing_after.add_local_algebra(
                            name.clone(),
                            event.occurrence,
                            presentation.clone(),
                        )?,
                    )
                }
                CausalAlgebraicDeed::FoundRegion {
                    name,
                    support,
                    local_algebras,
                } => CausalAlgebraicRadiation::RegionFounded(standing_after.found_region(
                    name.clone(),
                    support.clone(),
                    local_algebras.clone(),
                    event.occurrence,
                )?),
                CausalAlgebraicDeed::FoundEnd {
                    name,
                    region,
                    hand,
                    section,
                } => CausalAlgebraicRadiation::EndFounded(standing_after.found_end(
                    name.clone(),
                    *region,
                    *hand,
                    section.clone(),
                    event.occurrence,
                )?),
            };
            radiation.push(emitted);
        }
        standing_after.validate()?;
        Ok(EventSuccessor {
            standing_after,
            radiation,
            logical_resources: None,
            physical_resources: None,
        })
    }
}

#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum CausalAlgebraicError {
    #[error("orientation hand must be +1 or -1, received {0}")]
    InvalidOrientationHand(i8),
    #[error("a zero chain coefficient was stored explicitly")]
    StoredZeroCoefficient,
    #[error("causal cell {0:?} is absent")]
    MissingCausalCell(CausalCellId),
    #[error("an incidence cell must retain at least one source occurrence")]
    UncausedCell,
    #[error("a grade-zero incidence cell cannot have a boundary")]
    VertexHasBoundary,
    #[error(
        "boundary cell {cell:?} has grade {boundary_grade}, not one below carrier grade {carrier_grade}"
    )]
    BoundaryGrade {
        cell: CausalCellId,
        boundary_grade: u32,
        carrier_grade: u32,
    },
    #[error("boundary squared is nonzero: {0:?}")]
    BoundarySquaredNonzero(CausalChain),
    #[error("one chain contains cells of different grades")]
    MixedChainGrades,
    #[error("causal cell map key and body identity differ")]
    CausalCellIdentityMismatch {
        key: CausalCellId,
        body: CausalCellId,
    },
    #[error("the next causal cell identity does not follow the extant population")]
    InvalidNextCellIdentity,
    #[error("a simplex requires at least one vertex")]
    EmptySimplex,
    #[error("finite construction arithmetic overflowed its carrier")]
    ArithmeticOverflow,
    #[error("algebra generator {0:?} is absent")]
    MissingAlgebraGenerator(AlgebraGeneratorId),
    #[error("receiver point supplies no value for generator {0:?}")]
    MissingGeneratorValue(AlgebraGeneratorId),
    #[error("a proposed ideal relation is not homogeneous in the declared grading")]
    InhomogeneousRelation,
    #[error("a zero polynomial does not found an algebra relation")]
    ZeroAlgebraRelation,
    #[error("a nonzero constant relation would collapse the complete algebra")]
    ConstantAlgebraRelation,
    #[error("a graded algebra generator requires a positive weight")]
    ZeroGeneratorWeight,
    #[error("an algebra generator or relation must retain source occurrence")]
    UncausedAlgebraMember,
    #[error("algebra generator map key and body identity differ")]
    AlgebraGeneratorIdentityMismatch,
    #[error("algebra relation map key and body identity differ")]
    AlgebraRelationIdentityMismatch,
    #[error("stored algebra relation degree differs from its exact polynomial")]
    RelationDegreeMismatch,
    #[error("the next algebra identity does not follow its extant population")]
    InvalidNextAlgebraIdentity,
    #[error("rational homogeneous coefficients could not be cleared exactly")]
    FailedToClearDenominators,
    #[error("simplicial vertex map key and body identity differ")]
    SimplicialVertexIdentityMismatch,
    #[error("simplicial face map key and body identity differ")]
    SimplicialFaceIdentityMismatch,
    #[error("simplicial hinge map key and body identity differ")]
    SimplicialHingeIdentityMismatch,
    #[error("simplicial face {0:?} is collapsed and cannot migrate")]
    CollapsedMigratedFace(FaceId),
    #[error("simplicial face {face:?} references absent vertex {vertex:?}")]
    MigratedFaceMissingVertex { face: FaceId, vertex: VertexId },
    #[error("simplicial hinge {0:?} does not match its contemporary edge cofaces")]
    InvalidMigratedHinge(HingeId),
    #[error("local coordinate algebra {0:?} is absent")]
    MissingLocalAlgebra(LocalAlgebraId),
    #[error("causal region {0:?} is absent")]
    MissingCausalRegion(CausalRegionId),
    #[error("causal end {0:?} is absent")]
    MissingCausalEnd(CausalEndId),
    #[error("a caused local region cannot have empty incidence")]
    EmptyCausalRegion,
    #[error("a local region omits part of the boundary of its admitted incidence")]
    RegionSupportNotClosed,
    #[error("a section reaches outside its declared local region")]
    SectionOutsideRegion,
    #[error("source occurrence {0:?} is absent from the evolution shape")]
    MissingSourceOccurrence(EventId),
    #[error("local algebra map key and body identity differ")]
    LocalAlgebraIdentityMismatch,
    #[error("causal region map key and body identity differ")]
    CausalRegionIdentityMismatch,
    #[error("causal end map key and body identity differ")]
    CausalEndIdentityMismatch,
    #[error("the next presentation identity does not follow its extant population")]
    InvalidNextPresentationIdentity,
    #[error("the two causal ends were not transported into the queried region")]
    EndRegionMismatch,
    #[error("an opposed comparison requires one incoming and one outgoing end")]
    OpposedEndHandMismatch,
    #[error("boundary and opposed end sections do not inhabit one chain grade")]
    RelativeBoundaryGradeMismatch,
    #[error("a receiver section must contain the boundary closure of every admitted cell")]
    ReceiverSectionNotClosed,
    #[error("receiver morphism images do not exactly cover its declared source section")]
    MorphismImageDomainMismatch,
    #[error("receiver morphism has no image for source cell {0:?}")]
    MissingMorphismImage(CausalCellId),
    #[error("a queried chain leaves the receiver's declared source section")]
    ChainOutsideReceiverSection,
    #[error(
        "source cell {source_cell:?} has grade {source_grade}, but its nonzero image has grade {image_grade:?}"
    )]
    MorphismGradeMismatch {
        source_cell: CausalCellId,
        source_grade: u32,
        image_grade: Option<u32>,
    },
    #[error(
        "receiver morphism does not commute with the boundary at {source_cell:?}: d(image)={boundary_of_image:?}, image(d)={image_of_boundary:?}"
    )]
    MorphismBoundaryMismatch {
        source_cell: CausalCellId,
        boundary_of_image: CausalChain,
        image_of_boundary: CausalChain,
    },
    #[error("native conic {0:?} has no declared incident face")]
    MissingConicFaceBinding(ConicCellId),
    #[error("conic binding names absent native conic {0:?}")]
    UnknownBoundConic(ConicCellId),
    #[error("conic binding names absent simplicial face {0:?}")]
    UnknownBoundFace(FaceId),
    #[error(transparent)]
    Evolution(#[from] EvolutionError),
    #[error(transparent)]
    Conic(#[from] ConicError),
}

#[cfg(test)]
mod tests {
    use relational_geometry::{FrameId, RatVec3};

    use super::*;
    use crate::{CausalWorld, ConicChart};

    fn evolution_with_event() -> (EvolutionShape, EventId) {
        let mut evolution = EvolutionShape::default();
        let boundary = evolution.add_boundary("causal material");
        let law = evolution
            .add_law("emit algebraic material", Vec::new(), vec![boundary])
            .unwrap();
        let event = evolution.add_occurrence(law).unwrap();
        (evolution, event)
    }

    #[test]
    fn oriented_coefficients_are_group_completed_occurrence_counts() {
        let left = ComparativeMultiplicity::new(7_u8.into(), 3_u8.into());
        assert_eq!(
            (left.positive_count(), left.negative_count()),
            (&BigUint::from(7_u8), &BigUint::from(3_u8)),
            "ten passages were taken and all ten are retained"
        );
        assert_eq!(left.difference(), BigInt::from(4_u8));
        assert_eq!(left.reduced().positive_count(), &BigUint::from(4_u8));
        assert!(
            left.reduced().negative_count().is_zero(),
            "the reduction is available as a reading and is not what is stored"
        );
        let right = ComparativeMultiplicity::negative(4_u8);
        let sum = left.plus(&right);
        assert!(
            !sum.is_zero(),
            "seven one way and seven the other is fourteen passages, not an absence"
        );
        assert!(sum.difference_is_zero());
        assert_eq!(
            (sum.positive_count(), sum.negative_count()),
            (&BigUint::from(7_u8), &BigUint::from(7_u8))
        );
        let opposed = ComparativeMultiplicity::new(1_u8.into(), 1_u8.into());
        assert_eq!(
            opposed.times(&opposed),
            ComparativeMultiplicity::new(2_u8.into(), 2_u8.into()),
            "a cancelling coefficient squared is four passages, not zero"
        );
        assert_eq!(
            ComparativeMultiplicity::negative(3_u8)
                .times(&ComparativeMultiplicity::negative(2_u8))
                .difference(),
            BigInt::from(6)
        );
    }

    #[test]
    fn a_four_simplex_is_a_grade_four_source_with_exact_boundary_squared_zero() {
        let (_, event) = evolution_with_event();
        let mut incidence = GradedCausalComplex::default();
        let simplex = incidence
            .found_simplex("four-simplex", event, ["a", "b", "c", "d", "e"])
            .unwrap();
        assert_eq!(simplex.dimension, 4);
        assert_eq!(incidence.dimension(), Some(4));
        assert_eq!(
            incidence.f_vector(),
            BTreeMap::from([(0, 5), (1, 10), (2, 10), (3, 5), (4, 1)])
        );
        let first_boundary = incidence
            .boundary_of_chain(&CausalChain::single(
                simplex.apex,
                ComparativeMultiplicity::positive(1_u8),
            ))
            .unwrap();
        assert!(!first_boundary.is_zero());
        assert!(
            incidence
                .boundary_of_chain(&first_boundary)
                .unwrap()
                .difference_is_zero()
        );
    }

    #[test]
    fn a_receiver_cannot_admit_a_face_without_its_boundary_closure() {
        let (_, event) = evolution_with_event();
        let mut source = GradedCausalComplex::default();
        let source_triangle = source
            .found_simplex("source", event, ["a", "b", "c"])
            .unwrap();
        let mut target = GradedCausalComplex::default();
        let target_triangle = target
            .found_simplex("target", event, ["x", "y", "z"])
            .unwrap();
        assert_eq!(
            CausalSectionMorphism::new(
                "false face-only section",
                &source,
                &target,
                BTreeSet::from([source_triangle.apex]),
                BTreeMap::from([(
                    source_triangle.apex,
                    CausalChain::single(
                        target_triangle.apex,
                        ComparativeMultiplicity::positive(1_u8),
                    ),
                )]),
            ),
            Err(CausalAlgebraicError::ReceiverSectionNotClosed)
        );
    }

    fn oriented_face_morphism(
        name: &str,
        source: &GradedCausalComplex,
        source_simplex: &SimplexIncidenceReceipt,
        source_vertices: [usize; 3],
        target: &GradedCausalComplex,
        target_triangle: &SimplexIncidenceReceipt,
    ) -> CausalSectionMorphism {
        let mut images = BTreeMap::new();
        for size in 1..=3 {
            for local_vertices in combinations(3, size) {
                let source_subset = local_vertices
                    .iter()
                    .map(|index| source_vertices[*index])
                    .collect::<Vec<_>>();
                let source_cell = source_simplex.cell(&source_subset).unwrap();
                let target_cell = target_triangle.cell(&local_vertices).unwrap();
                images.insert(
                    source_cell,
                    CausalChain::single(target_cell, ComparativeMultiplicity::positive(1_u8)),
                );
            }
        }
        let support = images.keys().copied().collect();
        CausalSectionMorphism::new(name, source, target, support, images).unwrap()
    }

    #[test]
    fn equal_planar_quotients_retain_distinct_higher_source_fibers() {
        let (_, event) = evolution_with_event();
        let mut source = GradedCausalComplex::default();
        let four_simplex = source
            .found_simplex("four-simplex", event, ["a", "b", "c", "d", "e"])
            .unwrap();
        let mut target = GradedCausalComplex::default();
        let triangle = target
            .found_simplex("terminal triangle", event, ["x", "y", "z"])
            .unwrap();

        let left_morphism = oriented_face_morphism(
            "left face quotient",
            &source,
            &four_simplex,
            [0, 1, 2],
            &target,
            &triangle,
        );
        let right_morphism = oriented_face_morphism(
            "right face quotient",
            &source,
            &four_simplex,
            [0, 3, 4],
            &target,
            &triangle,
        );
        let left_face = four_simplex.cell(&[0, 1, 2]).unwrap();
        let right_face = four_simplex.cell(&[0, 3, 4]).unwrap();
        let left = AlgebraicReceiver {
            schema: "test.receiver.v1".to_owned(),
            id: ReceiverId(1),
            morphism: left_morphism,
        }
        .receive(
            &source,
            &target,
            &CausalChain::single(left_face, ComparativeMultiplicity::positive(1_u8)),
        )
        .unwrap();
        let right = AlgebraicReceiver {
            schema: "test.receiver.v1".to_owned(),
            id: ReceiverId(2),
            morphism: right_morphism,
        }
        .receive(
            &source,
            &target,
            &CausalChain::single(right_face, ComparativeMultiplicity::positive(1_u8)),
        )
        .unwrap();

        assert_eq!(left.observed(), right.observed());
        assert_eq!(
            left.observed(),
            &CausalChain::single(triangle.apex, ComparativeMultiplicity::positive(1_u8))
        );
        assert_eq!(
            left.source_fibers()[&triangle.apex],
            BTreeSet::from([left_face])
        );
        assert_eq!(
            right.source_fibers()[&triangle.apex],
            BTreeSet::from([right_face])
        );
        assert_ne!(left.source_section(), right.source_section());
    }

    #[test]
    fn opposed_ends_derive_a_zero_relative_boundary_without_storing_a_scalar() {
        let (evolution, event) = evolution_with_event();
        let mut incidence = GradedCausalComplex::default();
        let interval = incidence
            .found_simplex("interval", event, ["past", "future"])
            .unwrap();
        let mut standing = CausalAlgebraicPresentation::new(evolution, incidence).unwrap();
        let support = standing.incidence.closed_hull([interval.apex]).unwrap();
        let region = standing
            .found_region("one causal interval", support, BTreeSet::new(), event)
            .unwrap();
        let incoming_section = CausalChain::single(
            interval.vertices[0],
            ComparativeMultiplicity::positive(1_u8),
        );
        let outgoing_section = CausalChain::single(
            interval.vertices[1],
            ComparativeMultiplicity::positive(1_u8),
        );
        let incoming = standing
            .found_end(
                "originating end",
                region,
                CausalEndHand::Incoming,
                incoming_section.clone(),
                event,
            )
            .unwrap();
        let outgoing = standing
            .found_end(
                "contemporary end",
                region,
                CausalEndHand::Outgoing,
                outgoing_section.clone(),
                event,
            )
            .unwrap();
        let boundary = outgoing_section.minus(&incoming_section);
        let receipt = standing
            .compare_opposed_ends(&RelativeBoundaryQuery {
                region,
                boundary,
                incoming,
                outgoing,
            })
            .unwrap();
        assert!(receipt.residual.difference_is_zero());
    }

    #[test]
    fn a_singular_quadratic_cone_has_distinct_tangent_and_dimension_receipts() {
        let (_, event) = evolution_with_event();
        let mut algebra = GradedAlgebraPresentation::default();
        let source = BTreeSet::from([event]);
        let x = algebra.add_generator("x", 1, source.clone()).unwrap();
        let y = algebra.add_generator("y", 1, source.clone()).unwrap();
        let z = algebra.add_generator("z", 1, source.clone()).unwrap();
        let w = algebra.add_generator("w", 1, source.clone()).unwrap();
        let mut relation = HomogeneousPolynomial::default();
        relation.add_term(
            AlgebraMonomial::new([(x, 1), (y, 1)]),
            ComparativeMultiplicity::positive(1_u8),
        );
        relation.add_term(
            AlgebraMonomial::new([(z, 1), (w, 1)]),
            ComparativeMultiplicity::negative(1_u8),
        );
        algebra.add_relation("xy - zw", source, relation).unwrap();
        assert_eq!(algebra.tangent_dimension_at_homogeneous_origin(), 4);
        assert_eq!(
            algebra.dimension_certificate(),
            AlgebraDimensionCertificate::PrincipalHypersurface {
                affine_dimension: 3,
                projective_horizon_dimension: Some(2),
            }
        );
        let horizon = algebra.center_horizon();
        assert_eq!(horizon.tangent_dimension_at_center, 4);
    }

    #[test]
    fn the_current_tetrahedral_surface_migrates_as_one_grade_two_realization() {
        let (_, event) = evolution_with_event();
        let mut complex = SimplicialComplex::default();
        let vertices = (0..4)
            .map(|index| complex.found_vertex(format!("v{index}"), event))
            .collect::<Vec<_>>();
        for (name, face) in [
            ("opposite-0", [vertices[1], vertices[2], vertices[3]]),
            ("opposite-1", [vertices[0], vertices[3], vertices[2]]),
            ("opposite-2", [vertices[0], vertices[1], vertices[3]]),
            ("opposite-3", [vertices[0], vertices[2], vertices[1]]),
        ] {
            complex.found_face(name, event, face).unwrap();
        }
        let receipt = SimplicialIncidenceReceipt::realize(&complex).unwrap();
        assert_eq!(
            receipt.incidence.f_vector(),
            BTreeMap::from([(0, 4), (1, 6), (2, 4)])
        );
        assert_eq!(receipt.incidence.dimension(), Some(2));
    }

    #[test]
    fn a_native_conic_and_its_coordinate_algebra_evaluate_identically_up_to_clearing() {
        let (_, event) = evolution_with_event();
        let form = HomogeneousConic::new([
            Rat::from_integer(2.into()),
            Rat::from_integer((-3).into()),
            Rat::from_integer(5.into()),
            Rat::from_integer(7.into()),
            Rat::from_integer(11.into()),
            Rat::from_integer((-13).into()),
        ])
        .unwrap();
        let receipt =
            ConicAlgebraReceipt::realize(ConicCellId(9), "native conic", event, &form).unwrap();
        let point = [
            Rat::from_integer(2.into()),
            Rat::from_integer((-1).into()),
            Rat::from_integer(3.into()),
        ];
        assert_eq!(
            receipt.evaluate(point.clone()).unwrap(),
            Rat::from_integer(receipt.clearing_factor) * form.evaluate(&point)
        );
    }

    #[test]
    fn an_invalid_algebraic_event_cannot_leave_partial_standing() {
        let (evolution, event) = evolution_with_event();
        let mut incidence = GradedCausalComplex::default();
        let interval = incidence
            .found_simplex("interval", event, ["a", "b"])
            .unwrap();
        let standing = CausalAlgebraicPresentation::new(evolution, incidence).unwrap();
        let before = standing.clone();
        let mut world = CausalWorld::new(CausalAlgebraicLaw, standing);
        let result = world.receive(&CausalAlgebraicEvent {
            occurrence: event,
            deeds: vec![CausalAlgebraicDeed::FoundCell {
                name: "invalid two-cell".to_owned(),
                grade: 2,
                boundary: CausalChain::single(
                    interval.apex,
                    ComparativeMultiplicity::positive(1_u8),
                ),
            }],
        });
        assert!(matches!(
            result,
            Err(CausalAlgebraicError::BoundarySquaredNonzero(_))
        ));
        assert_eq!(world.standing(), &before);
    }

    #[test]
    fn combined_migration_requires_and_retains_explicit_conic_face_incidence() {
        let (evolution, event) = evolution_with_event();
        let mut simplicial = SimplicialComplex::default();
        let a = simplicial.found_vertex("a", event);
        let b = simplicial.found_vertex("b", event);
        let c = simplicial.found_vertex("c", event);
        let face = simplicial
            .found_face("carrier face", event, [a, b, c])
            .unwrap();
        let chart = ConicChart::new(
            RatVec3::from_i64(0, 0, 0),
            RatVec3::from_i64(1, 0, 0),
            RatVec3::from_i64(0, 1, 0),
        )
        .unwrap();
        let form = HomogeneousConic::new([
            Rat::one(),
            Rat::zero(),
            Rat::one(),
            Rat::zero(),
            Rat::zero(),
            Rat::from_integer((-1).into()),
        ])
        .unwrap();
        let mut conics = NativeConicPopulation::default();
        let conic = conics.found("circle", event, FrameId(1), chart, form);

        assert_eq!(
            SimplicialConicAlgebraicReceipt::realize(
                evolution.clone(),
                &simplicial,
                &conics,
                &BTreeMap::new(),
            ),
            Err(CausalAlgebraicError::MissingConicFaceBinding(conic))
        );
        let receipt = SimplicialConicAlgebraicReceipt::realize(
            evolution,
            &simplicial,
            &conics,
            &BTreeMap::from([(conic, face)]),
        )
        .unwrap();
        assert_eq!(receipt.conics[&conic].face, face);
        let region = receipt.face_regions[&face];
        assert!(
            receipt.presentation.regions[&region]
                .local_algebras
                .contains(&receipt.conics[&conic].local_algebra)
        );
    }
}

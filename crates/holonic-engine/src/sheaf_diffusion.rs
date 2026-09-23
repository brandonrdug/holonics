//! Exact linear sheaves and deterministic diffusion on causal incidence.
//!
//! A scalar graph is only the grade-zero, rank-one case.  Here every causal
//! cell owns a finite rational stalk, every immediate face relation owns an
//! exact restriction map, and the cellular coboundary is assembled from those
//! maps and the complex's oriented incidence.  One completed diffusion event
//! solves
//!
//! `(M + tau * Delta_k) phi_after = content_before + source`
//! `content_after = M phi_after`
//!
//! exactly, where `Delta_k` is the full cellular-sheaf Hodge operator at the
//! selected grade.  The operator inverse and its exact identity residual are
//! retained as a reusable certificate.  No tolerance, random walk, display
//! adjacency, or floating-point convergence criterion enters the law.
//!
//! # One carrier
//!
//! Every linear map this law holds — a restriction, a coboundary, a Hodge operator and each map
//! of a certificate — is `exact_linear::ExactRatMatrix`. Until 2026-08-15 this module carried its
//! own `invert_exact`, which built the inverse **one column at a time** — `O(n^4)` — through a
//! `solve_exact` that shared 26 lines verbatim with `diffusion`'s; both went then. Until
//! September 22 it also carried a second storage type, `ExactLinearMap`, whose operations already
//! routed through the shared carrier; it is now a name for that carrier. What stays this law's own
//! is its refusal vocabulary ([`SheafLinearMap`]) and its serialized row shape
//! ([`linear_map_rows`]), which every wire written before the replacement still reads.
//!
//! The `inverse_residual` this module has always computed and retained is untouched, and it is
//! worth being exact about why it is not redundant: `compile_certificate` already refused a
//! nonzero residual, so this inverse was verified — downstream, by the caller. The residual is
//! what a later reader of the serialized certificate has; the carrier's check is what a future
//! caller who does not write one will have.

use std::collections::{BTreeMap, BTreeSet};
use std::sync::{Arc, RwLock};

use num_traits::{One, Signed, Zero};
use relational_geometry::Rat;
use serde::{Deserialize, Serialize};
use thiserror::Error;

use crate::diffusion::DiffusionEnergyBalance;
use crate::exact_linear::{ExactLinearError, ExactRatMatrix};
use crate::{
    CausalAlgebraicError, CausalCellId, EventSuccessor, ExactEventLaw, GradedCausalComplex,
};

// The sheaf law as a core Holon and a `HolonLaw` (plan phase 3).
mod holon;
pub use holon::SheafDiffusionHolonLaw;

/// **The sheaf law's linear map is the shared exact carrier.**
///
/// [definition] A finite exact linear map, rows the target coordinates and columns the source
/// coordinates. Until September 22 this was a second carrier with its own `Vec<Vec<Rat>>`
/// storage; it is now [`ExactRatMatrix`] itself, so a restriction, a coboundary and a certificate
/// operator are the same object every other exact owner reads. The name is kept for its callers.
/// The law's own refusal vocabulary lives on [`SheafLinearMap`], and its serialized
/// `{rows, columns, entries: [[Rat]]}` shape on [`linear_map_rows`].
pub type ExactLinearMap = ExactRatMatrix;

/// **Composition and sum in the sheaf law's own refusal vocabulary.**
///
/// The dimension refusals are raised before the carrier is reached, so a caller sees
/// `LinearCompositionDimension`/`LinearAdditionDimension`/`MalformedLinearMap` and never a
/// foreign shape error.
pub trait SheafLinearMap: Sized {
    /// A map of the declared shape; a ragged or misshapen population is `MalformedLinearMap`.
    fn declared(
        rows: usize,
        columns: usize,
        entries: Vec<Vec<Rat>>,
    ) -> Result<Self, SheafDiffusionError>;
    /// Compose `self: A -> B` followed by `next: B -> C`.
    fn then(&self, next: &Self) -> Result<Self, SheafDiffusionError>;
    /// The sum of two maps of one shape.
    fn plus(&self, other: &Self) -> Result<Self, SheafDiffusionError>;
}

impl SheafLinearMap for ExactRatMatrix {
    fn declared(
        rows: usize,
        columns: usize,
        entries: Vec<Vec<Rat>>,
    ) -> Result<Self, SheafDiffusionError> {
        if entries.len() != rows || entries.iter().any(|row| row.len() != columns) {
            return Err(SheafDiffusionError::MalformedLinearMap {
                expected_rows: rows,
                expected_columns: columns,
            });
        }
        Ok(ExactRatMatrix::shaped(rows, columns, entries)?)
    }

    fn then(&self, next: &Self) -> Result<Self, SheafDiffusionError> {
        if self.rows() != next.columns() {
            return Err(SheafDiffusionError::LinearCompositionDimension {
                first_rows: self.rows(),
                next_columns: next.columns(),
            });
        }
        Ok(next.multiply(self)?)
    }

    fn plus(&self, other: &Self) -> Result<Self, SheafDiffusionError> {
        if self.rows() != other.rows() || self.columns() != other.columns() {
            return Err(SheafDiffusionError::LinearAdditionDimension);
        }
        Ok(self.add(other)?)
    }
}

/// **The serialized presentation of a sheaf-law linear map: `{rows, columns, entries: [[Rat]]}`.**
///
/// [definition] The wire this law has always written, kept unchanged now that the value is an
/// [`ExactRatMatrix`] (whose own serde shape is flat). A field of that type carries
/// `#[serde(with = "linear_map_rows")]`; a restriction table carries
/// `#[serde(with = "linear_map_rows::by_incidence")]`. A misshapen row population refuses at
/// deserialization, where the previous carrier admitted it and refused on first validation.
pub mod linear_map_rows {
    use std::collections::BTreeMap;

    use relational_geometry::Rat;
    use serde::{Deserialize, Deserializer, Serialize, Serializer};

    use crate::CausalCellId;
    use crate::exact_linear::ExactRatMatrix;

    #[derive(Serialize)]
    struct RowsRef {
        rows: usize,
        columns: usize,
        entries: Vec<Vec<Rat>>,
    }

    #[derive(Deserialize)]
    struct Rows {
        rows: usize,
        columns: usize,
        entries: Vec<Vec<Rat>>,
    }

    fn presented(map: &ExactRatMatrix) -> RowsRef {
        RowsRef {
            rows: map.rows(),
            columns: map.columns(),
            entries: map.to_rows(),
        }
    }

    fn admitted<E: serde::de::Error>(rows: Rows) -> Result<ExactRatMatrix, E> {
        ExactRatMatrix::shaped(rows.rows, rows.columns, rows.entries).map_err(|_| {
            E::custom(format!(
                "linear map entries do not have the declared {} by {} shape",
                rows.rows, rows.columns
            ))
        })
    }

    pub fn serialize<S: Serializer>(
        map: &ExactRatMatrix,
        serializer: S,
    ) -> Result<S::Ok, S::Error> {
        presented(map).serialize(serializer)
    }

    pub fn deserialize<'de, D: Deserializer<'de>>(
        deserializer: D,
    ) -> Result<ExactRatMatrix, D::Error> {
        admitted(Rows::deserialize(deserializer)?)
    }

    /// The same presentation for a restriction table keyed by its incidence.
    pub mod by_incidence {
        use super::*;

        pub fn serialize<S: Serializer>(
            maps: &BTreeMap<(CausalCellId, CausalCellId), ExactRatMatrix>,
            serializer: S,
        ) -> Result<S::Ok, S::Error> {
            maps.iter()
                .map(|(key, map)| (*key, presented(map)))
                .collect::<BTreeMap<_, _>>()
                .serialize(serializer)
        }

        pub fn deserialize<'de, D: Deserializer<'de>>(
            deserializer: D,
        ) -> Result<BTreeMap<(CausalCellId, CausalCellId), ExactRatMatrix>, D::Error> {
            BTreeMap::<(CausalCellId, CausalCellId), Rows>::deserialize(deserializer)?
                .into_iter()
                .map(|(key, rows)| Ok((key, admitted(rows)?)))
                .collect()
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CellularRestriction {
    pub lower: CausalCellId,
    pub upper: CausalCellId,
    #[serde(with = "linear_map_rows")]
    pub map: ExactRatMatrix,
}

/// A finite-dimensional rational cellular sheaf on one exact causal complex.
///
/// Restriction maps point from a face stalk into a coface stalk.  All maps
/// along every composable incidence path are checked for exact equality.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ExactCellularSheaf {
    pub schema: String,
    complex: GradedCausalComplex,
    stalk_dimensions: BTreeMap<CausalCellId, usize>,
    #[serde(with = "linear_map_rows::by_incidence")]
    restrictions: BTreeMap<(CausalCellId, CausalCellId), ExactRatMatrix>,
}

impl ExactCellularSheaf {
    pub fn new(
        complex: GradedCausalComplex,
        stalk_dimensions: BTreeMap<CausalCellId, usize>,
        restrictions: impl IntoIterator<Item = CellularRestriction>,
    ) -> Result<Self, SheafDiffusionError> {
        let mut indexed = BTreeMap::new();
        for restriction in restrictions {
            let key = (restriction.lower, restriction.upper);
            if indexed.insert(key, restriction.map).is_some() {
                return Err(SheafDiffusionError::DuplicateRestriction {
                    lower: key.0,
                    upper: key.1,
                });
            }
        }
        let sheaf = Self {
            schema: "holonic-engine.exact-cellular-sheaf.v1".to_owned(),
            complex,
            stalk_dimensions,
            restrictions: indexed,
        };
        sheaf.validate()?;
        Ok(sheaf)
    }

    pub fn complex(&self) -> &GradedCausalComplex {
        &self.complex
    }

    pub fn stalk_dimensions(&self) -> &BTreeMap<CausalCellId, usize> {
        &self.stalk_dimensions
    }

    pub fn stalk_dimension(&self, cell: CausalCellId) -> Result<usize, SheafDiffusionError> {
        self.stalk_dimensions
            .get(&cell)
            .copied()
            .ok_or(SheafDiffusionError::MissingStalk(cell))
    }

    pub fn restrictions(&self) -> &BTreeMap<(CausalCellId, CausalCellId), ExactRatMatrix> {
        &self.restrictions
    }

    pub fn restriction(
        &self,
        lower: CausalCellId,
        upper: CausalCellId,
    ) -> Result<&ExactRatMatrix, SheafDiffusionError> {
        self.restrictions
            .get(&(lower, upper))
            .ok_or(SheafDiffusionError::MissingRestriction { lower, upper })
    }

    pub fn coordinates(&self, grade: u32) -> Vec<SheafCoordinate> {
        let mut coordinates = Vec::new();
        for (cell, body) in self.complex.cells() {
            if body.grade == grade {
                for coordinate in 0..self.stalk_dimensions[cell] {
                    coordinates.push(SheafCoordinate {
                        cell: *cell,
                        coordinate,
                    });
                }
            }
        }
        coordinates
    }

    /// The exact cellular coboundary `delta_grade`.
    pub fn coboundary(&self, grade: u32) -> Result<ExactRatMatrix, SheafDiffusionError> {
        let source = self.coordinates(grade);
        let target = self.coordinates(grade.saturating_add(1));
        let source_offsets = coordinate_offsets(&source);
        let target_offsets = coordinate_offsets(&target);
        let mut entries = vec![vec![Rat::zero(); source.len()]; target.len()];

        for (upper, upper_body) in self.complex.cells() {
            if upper_body.grade != grade.saturating_add(1) {
                continue;
            }
            let Some(&target_offset) = target_offsets.get(upper) else {
                continue;
            };
            for (lower, coefficient) in upper_body.boundary.coefficients() {
                let Some(&source_offset) = source_offsets.get(lower) else {
                    continue;
                };
                let restriction = self.restriction(*lower, *upper)?;
                let incidence = Rat::from_integer(coefficient.difference());
                for row in 0..restriction.rows() {
                    for column in 0..restriction.columns() {
                        entries[target_offset + row][source_offset + column] +=
                            &incidence * restriction.get(row, column)?;
                    }
                }
            }
        }
        ExactRatMatrix::declared(target.len(), source.len(), entries)
    }

    /// The exact Hodge operator
    /// `Delta_k = delta_(k-1) delta_(k-1)^T + delta_k^T delta_k`.
    pub fn hodge_laplacian(&self, grade: u32) -> Result<ExactRatMatrix, SheafDiffusionError> {
        let extent = self.coordinates(grade).len();
        let upper = self.coboundary(grade)?;
        let upper_term = upper.then(&upper.transpose()?)?;
        let lower_term = if grade == 0 {
            ExactRatMatrix::zero(extent, extent)?
        } else {
            let lower = self.coboundary(grade - 1)?;
            lower.transpose()?.then(&lower)?
        };
        lower_term.plus(&upper_term)
    }

    pub fn validate(&self) -> Result<(), SheafDiffusionError> {
        self.complex.validate()?;
        let cells = self
            .complex
            .cells()
            .keys()
            .copied()
            .collect::<BTreeSet<_>>();
        let stalks = self
            .stalk_dimensions
            .keys()
            .copied()
            .collect::<BTreeSet<_>>();
        if let Some(cell) = cells.difference(&stalks).next() {
            return Err(SheafDiffusionError::MissingStalk(*cell));
        }
        if let Some(cell) = stalks.difference(&cells).next() {
            return Err(SheafDiffusionError::UnknownStalk(*cell));
        }

        let mut expected = BTreeSet::new();
        for (upper, body) in self.complex.cells() {
            for lower in body.boundary.support() {
                expected.insert((lower, *upper));
            }
        }
        let supplied = self.restrictions.keys().copied().collect::<BTreeSet<_>>();
        if let Some((lower, upper)) = expected.difference(&supplied).next() {
            return Err(SheafDiffusionError::MissingRestriction {
                lower: *lower,
                upper: *upper,
            });
        }
        if let Some((lower, upper)) = supplied.difference(&expected).next() {
            return Err(SheafDiffusionError::NonincidentRestriction {
                lower: *lower,
                upper: *upper,
            });
        }
        for ((lower, upper), map) in &self.restrictions {
            let expected_rows = self.stalk_dimensions[upper];
            let expected_columns = self.stalk_dimensions[lower];
            if map.rows() != expected_rows || map.columns() != expected_columns {
                return Err(SheafDiffusionError::RestrictionDimension {
                    lower: *lower,
                    upper: *upper,
                    expected_rows,
                    expected_columns,
                    supplied_rows: map.rows(),
                    supplied_columns: map.columns(),
                });
            }
        }

        self.validate_path_independence()?;
        if let Some(dimension) = self.complex.dimension() {
            for grade in 0..dimension {
                let first = self.coboundary(grade)?;
                let second = self.coboundary(grade.saturating_add(1))?;
                let squared = first.then(&second)?;
                if squared.entries().iter().any(|value| !value.is_zero()) {
                    return Err(SheafDiffusionError::CoboundarySquaredNonzero { grade });
                }
            }
        }
        Ok(())
    }

    fn validate_path_independence(&self) -> Result<(), SheafDiffusionError> {
        let mut upper_neighbors = BTreeMap::<CausalCellId, Vec<CausalCellId>>::new();
        for (lower, upper) in self.restrictions.keys() {
            upper_neighbors.entry(*lower).or_default().push(*upper);
        }
        for neighbors in upper_neighbors.values_mut() {
            neighbors.sort_by_key(|cell| (self.complex.cells()[cell].grade, cell.0));
        }

        let mut sources = self.complex.cells().keys().copied().collect::<Vec<_>>();
        sources.sort_by_key(|cell| (self.complex.cells()[cell].grade, cell.0));
        for source in sources {
            let mut composites = BTreeMap::from([(
                source,
                ExactRatMatrix::identity(self.stalk_dimensions[&source])?,
            )]);
            let mut reachable = vec![source];
            let mut cursor = 0;
            while cursor < reachable.len() {
                let lower = reachable[cursor];
                cursor += 1;
                let inherited = composites[&lower].clone();
                for upper in upper_neighbors.get(&lower).into_iter().flatten() {
                    let candidate = inherited.then(self.restriction(lower, *upper)?)?;
                    if let Some(existing) = composites.get(upper) {
                        if existing != &candidate {
                            return Err(SheafDiffusionError::PathDependentRestriction {
                                origin: source,
                                target: *upper,
                            });
                        }
                    } else {
                        composites.insert(*upper, candidate);
                        reachable.push(*upper);
                    }
                }
            }
        }
        Ok(())
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct SheafCoordinate {
    pub cell: CausalCellId,
    pub coordinate: usize,
}

fn coordinate_offsets(coordinates: &[SheafCoordinate]) -> BTreeMap<CausalCellId, usize> {
    let mut result = BTreeMap::new();
    for (ordinal, coordinate) in coordinates.iter().enumerate() {
        result.entry(coordinate.cell).or_insert(ordinal);
    }
    result
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ExactSheafCochain {
    pub schema: String,
    pub grade: u32,
    pub values: BTreeMap<CausalCellId, Vec<Rat>>,
}

impl ExactSheafCochain {
    pub fn zero(sheaf: &ExactCellularSheaf, grade: u32) -> Self {
        Self {
            schema: "holonic-engine.exact-sheaf-cochain.v1".to_owned(),
            grade,
            values: sheaf
                .complex
                .cells()
                .iter()
                .filter(|(_, body)| body.grade == grade)
                .map(|(cell, _)| (*cell, vec![Rat::zero(); sheaf.stalk_dimensions[cell]]))
                .collect(),
        }
    }

    pub fn new(
        sheaf: &ExactCellularSheaf,
        grade: u32,
        values: BTreeMap<CausalCellId, Vec<Rat>>,
    ) -> Result<Self, SheafDiffusionError> {
        let result = Self {
            schema: "holonic-engine.exact-sheaf-cochain.v1".to_owned(),
            grade,
            values,
        };
        result.validate(sheaf)?;
        Ok(result)
    }

    pub fn validate(&self, sheaf: &ExactCellularSheaf) -> Result<(), SheafDiffusionError> {
        let expected = sheaf
            .complex
            .cells()
            .iter()
            .filter_map(|(cell, body)| (body.grade == self.grade).then_some(*cell))
            .collect::<BTreeSet<_>>();
        let supplied = self.values.keys().copied().collect::<BTreeSet<_>>();
        if let Some(cell) = expected.difference(&supplied).next() {
            return Err(SheafDiffusionError::MissingCochainCell(*cell));
        }
        if let Some(cell) = supplied.difference(&expected).next() {
            return Err(SheafDiffusionError::WrongGradeCochainCell {
                cell: *cell,
                grade: self.grade,
            });
        }
        for (cell, values) in &self.values {
            let expected = sheaf.stalk_dimensions[cell];
            if values.len() != expected {
                return Err(SheafDiffusionError::CochainDimension {
                    cell: *cell,
                    expected,
                    supplied: values.len(),
                });
            }
        }
        Ok(())
    }

    fn flattened(&self, sheaf: &ExactCellularSheaf) -> Result<Vec<Rat>, SheafDiffusionError> {
        self.validate(sheaf)?;
        Ok(sheaf
            .coordinates(self.grade)
            .iter()
            .map(|coordinate| self.values[&coordinate.cell][coordinate.coordinate].clone())
            .collect())
    }

    fn from_flattened(
        sheaf: &ExactCellularSheaf,
        grade: u32,
        values: Vec<Rat>,
    ) -> Result<Self, SheafDiffusionError> {
        let coordinates = sheaf.coordinates(grade);
        if values.len() != coordinates.len() {
            return Err(SheafDiffusionError::FlatCochainDimension {
                expected: coordinates.len(),
                supplied: values.len(),
            });
        }
        let mut by_cell = sheaf
            .complex
            .cells()
            .iter()
            .filter(|(_, body)| body.grade == grade)
            .map(|(cell, _)| (*cell, vec![Rat::zero(); sheaf.stalk_dimensions[cell]]))
            .collect::<BTreeMap<_, _>>();
        for (coordinate, value) in coordinates.into_iter().zip(values) {
            by_cell.get_mut(&coordinate.cell).expect("coordinate cell")[coordinate.coordinate] =
                value;
        }
        Self::new(sheaf, grade, by_cell)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct SheafDiffusionStanding {
    pub schema: String,
    pub content: ExactSheafCochain,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct SheafDiffusionEvent {
    pub interval: Rat,
    /// A sparse exact deed on stalk coordinates at the law's selected grade.
    pub source: BTreeMap<CausalCellId, Vec<Rat>>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct SheafDiffusionCertificate {
    pub schema: String,
    pub grade: u32,
    pub coordinates: Vec<SheafCoordinate>,
    pub capacities: Vec<Rat>,
    #[serde(with = "linear_map_rows")]
    pub coboundary_below: ExactRatMatrix,
    #[serde(with = "linear_map_rows")]
    pub coboundary_above: ExactRatMatrix,
    #[serde(with = "linear_map_rows")]
    pub hodge_laplacian: ExactRatMatrix,
    #[serde(with = "linear_map_rows")]
    pub operator: ExactRatMatrix,
    #[serde(with = "linear_map_rows")]
    pub inverse: ExactRatMatrix,
    #[serde(with = "linear_map_rows")]
    pub inverse_residual: ExactRatMatrix,
    pub harmonic_dimension: usize,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct SheafDiffusionReceipt {
    pub schema: String,
    pub interval: Rat,
    pub potential_before: ExactSheafCochain,
    pub potential_after: ExactSheafCochain,
    pub compatibility_before: ExactSheafCochain,
    pub compatibility_after: ExactSheafCochain,
    pub balance_residual: ExactSheafCochain,
    pub stored_energy_before: Rat,
    pub stored_energy_after: Rat,
    pub energy_departed: Rat,
    pub compatibility_energy_before: Rat,
    pub compatibility_energy_after: Rat,
    pub reused_factorization: bool,
    pub certificate: SheafDiffusionCertificate,
}

#[derive(Clone, Debug)]
pub struct ExactSheafDiffusionLaw {
    sheaf: ExactCellularSheaf,
    grade: u32,
    capacities: BTreeMap<CausalCellId, Vec<Rat>>,
    atlas: Arc<RwLock<BTreeMap<Rat, SheafDiffusionCertificate>>>,
}

impl ExactSheafDiffusionLaw {
    pub fn new(
        sheaf: ExactCellularSheaf,
        grade: u32,
        capacities: BTreeMap<CausalCellId, Vec<Rat>>,
    ) -> Result<Self, SheafDiffusionError> {
        sheaf.validate()?;
        validate_capacities(&sheaf, grade, &capacities)?;
        Ok(Self {
            sheaf,
            grade,
            capacities,
            atlas: Arc::new(RwLock::new(BTreeMap::new())),
        })
    }

    pub fn sheaf(&self) -> &ExactCellularSheaf {
        &self.sheaf
    }

    pub fn grade(&self) -> u32 {
        self.grade
    }

    pub fn capacities(&self) -> &BTreeMap<CausalCellId, Vec<Rat>> {
        &self.capacities
    }

    pub fn transfer_cache_entries(&self) -> usize {
        self.atlas
            .read()
            .expect("the exact sheaf transfer atlas is not poisoned")
            .len()
    }

    pub fn initial_standing(
        &self,
        content: ExactSheafCochain,
    ) -> Result<SheafDiffusionStanding, SheafDiffusionError> {
        if content.grade != self.grade {
            return Err(SheafDiffusionError::LawGradeMismatch {
                expected: self.grade,
                supplied: content.grade,
            });
        }
        content.validate(&self.sheaf)?;
        Ok(SheafDiffusionStanding {
            schema: "holonic-engine.sheaf-diffusion-standing.v1".to_owned(),
            content,
        })
    }

    pub fn enact(
        &self,
        standing: &SheafDiffusionStanding,
        event: &SheafDiffusionEvent,
    ) -> Result<(SheafDiffusionStanding, SheafDiffusionReceipt), SheafDiffusionError> {
        if !event.interval.is_positive() {
            return Err(SheafDiffusionError::NonpositiveInterval);
        }
        if standing.content.grade != self.grade {
            return Err(SheafDiffusionError::LawGradeMismatch {
                expected: self.grade,
                supplied: standing.content.grade,
            });
        }
        standing.content.validate(&self.sheaf)?;
        let source = self.validate_and_flatten_source(&event.source)?;
        let content_before = standing.content.flattened(&self.sheaf)?;
        let capacities = self.flattened_capacities();
        let potential_before = content_before
            .iter()
            .zip(&capacities)
            .map(|(content, capacity)| content / capacity)
            .collect::<Vec<_>>();

        let (certificate, reused_factorization) = self.certificate(&event.interval)?;
        let right = content_before
            .iter()
            .zip(&source)
            .map(|(content, source)| content + source)
            .collect::<Vec<_>>();
        let potential_after = certificate.inverse.apply(&right)?;
        let operator_check = certificate.operator.apply(&potential_after)?;
        if operator_check != right {
            return Err(SheafDiffusionError::SolveResidualNonzero);
        }
        let content_after = potential_after
            .iter()
            .zip(&capacities)
            .map(|(potential, capacity)| potential * capacity)
            .collect::<Vec<_>>();

        let hodge_after = certificate.hodge_laplacian.apply(&potential_after)?;
        let balance = content_after
            .iter()
            .zip(&content_before)
            .zip(&source)
            .zip(&hodge_after)
            .map(|(((after, before), source), hodge)| {
                after - before - source + &event.interval * hodge
            })
            .collect::<Vec<_>>();
        if balance.iter().any(|value| !value.is_zero()) {
            return Err(SheafDiffusionError::BalanceResidualNonzero);
        }

        let compatibility_before = certificate.coboundary_above.apply(&potential_before)?;
        let compatibility_after = certificate.coboundary_above.apply(&potential_after)?;
        let stored_energy_before = diagonal_energy(&potential_before, &capacities);
        let stored_energy_after = diagonal_energy(&potential_after, &capacities);
        let energy_departed = &stored_energy_before - &stored_energy_after;
        if source.iter().all(Zero::is_zero) && energy_departed.is_negative() {
            return Err(SheafDiffusionError::EnergyIncreased);
        }
        let compatibility_energy_before = euclidean_energy(&compatibility_before);
        let compatibility_energy_after = euclidean_energy(&compatibility_after);

        let potential_before =
            ExactSheafCochain::from_flattened(&self.sheaf, self.grade, potential_before)?;
        let potential_after_cochain =
            ExactSheafCochain::from_flattened(&self.sheaf, self.grade, potential_after)?;
        let compatibility_before = ExactSheafCochain::from_flattened(
            &self.sheaf,
            self.grade.saturating_add(1),
            compatibility_before,
        )?;
        let compatibility_after = ExactSheafCochain::from_flattened(
            &self.sheaf,
            self.grade.saturating_add(1),
            compatibility_after,
        )?;
        let balance_residual = ExactSheafCochain::from_flattened(&self.sheaf, self.grade, balance)?;
        let content_after =
            ExactSheafCochain::from_flattened(&self.sheaf, self.grade, content_after)?;
        let standing_after = SheafDiffusionStanding {
            schema: standing.schema.clone(),
            content: content_after,
        };
        let receipt = SheafDiffusionReceipt {
            schema: "holonic-engine.sheaf-diffusion-receipt.v1".to_owned(),
            interval: event.interval.clone(),
            potential_before,
            potential_after: potential_after_cochain,
            compatibility_before,
            compatibility_after,
            balance_residual,
            stored_energy_before,
            stored_energy_after,
            energy_departed,
            compatibility_energy_before,
            compatibility_energy_after,
            reused_factorization,
            certificate,
        };
        let energy = self.energy_balance(&receipt, event)?;
        if !energy.exact_residual.is_zero() {
            return Err(SheafDiffusionError::SolveResidualNonzero);
        }
        Ok((standing_after, receipt))
    }

    /// Recover the complete finite-step energy pairing for one exact sheaf event.
    ///
    /// The Hodge term uses the full cellular Laplacian, hence both the lower and upper
    /// coboundary contributions.  The returned `energy_departed` field remains only a stored
    /// endpoint difference; this method separates signed source work, conductive dissipation,
    /// and the backward-Euler step defect without choosing a thermal receiver.
    pub fn energy_balance(
        &self,
        receipt: &SheafDiffusionReceipt,
        event: &SheafDiffusionEvent,
    ) -> Result<DiffusionEnergyBalance, SheafDiffusionError> {
        if !event.interval.is_positive() || !receipt.interval.is_positive() {
            return Err(SheafDiffusionError::NonpositiveInterval);
        }
        if event.interval != receipt.interval {
            return Err(SheafDiffusionError::SolveResidualNonzero);
        }
        for potential in [&receipt.potential_before, &receipt.potential_after] {
            if potential.grade != self.grade {
                return Err(SheafDiffusionError::LawGradeMismatch {
                    expected: self.grade,
                    supplied: potential.grade,
                });
            }
        }
        // Equal dimensions do not identify a sheaf's restriction maps or Hodge action.
        // Reuse this law's cached certificate to bind the receiving calculation to its source.
        let (expected, _) = self.certificate(&event.interval)?;
        if receipt.certificate != expected {
            return Err(SheafDiffusionError::TransferCertificateFailure);
        }
        let source = self.validate_and_flatten_source(&event.source)?;
        let before = receipt.potential_before.flattened(&self.sheaf)?;
        let after = receipt.potential_after.flattened(&self.sheaf)?;
        let hodge = receipt.certificate.hodge_laplacian.apply(&after)?;
        let mut source_work = Rat::zero();
        let mut conductive_dissipation = Rat::zero();
        let mut implicit_step_defect = Rat::zero();
        let two = Rat::from_integer(2.into());
        for (((after, before), source), (capacity, hodge)) in after
            .iter()
            .zip(&before)
            .zip(&source)
            .zip(receipt.certificate.capacities.iter().zip(&hodge))
        {
            source_work += after * source;
            conductive_dissipation += event.interval.clone() * after * hodge;
            implicit_step_defect += capacity * (after - before) * (after - before) / &two;
        }
        let exact_residual =
            &receipt.stored_energy_after - &receipt.stored_energy_before - &source_work
                + &conductive_dissipation
                + &implicit_step_defect;
        Ok(DiffusionEnergyBalance {
            source_work,
            conductive_dissipation,
            implicit_step_defect,
            exact_residual,
        })
    }

    fn flattened_capacities(&self) -> Vec<Rat> {
        self.sheaf
            .coordinates(self.grade)
            .iter()
            .map(|coordinate| self.capacities[&coordinate.cell][coordinate.coordinate].clone())
            .collect()
    }

    fn validate_and_flatten_source(
        &self,
        source: &BTreeMap<CausalCellId, Vec<Rat>>,
    ) -> Result<Vec<Rat>, SheafDiffusionError> {
        for (cell, values) in source {
            let body = self
                .sheaf
                .complex
                .cells()
                .get(cell)
                .ok_or(SheafDiffusionError::UnknownSourceCell(*cell))?;
            if body.grade != self.grade {
                return Err(SheafDiffusionError::WrongGradeSourceCell {
                    cell: *cell,
                    expected: self.grade,
                    supplied: body.grade,
                });
            }
            let expected = self.sheaf.stalk_dimensions[cell];
            if values.len() != expected {
                return Err(SheafDiffusionError::SourceDimension {
                    cell: *cell,
                    expected,
                    supplied: values.len(),
                });
            }
        }
        Ok(self
            .sheaf
            .coordinates(self.grade)
            .iter()
            .map(|coordinate| {
                source
                    .get(&coordinate.cell)
                    .map_or_else(Rat::zero, |values| values[coordinate.coordinate].clone())
            })
            .collect())
    }

    fn certificate(
        &self,
        interval: &Rat,
    ) -> Result<(SheafDiffusionCertificate, bool), SheafDiffusionError> {
        if let Some(certificate) = self
            .atlas
            .read()
            .map_err(|_| SheafDiffusionError::TransferAtlasPoisoned)?
            .get(interval)
            .cloned()
        {
            return Ok((certificate, true));
        }
        let compiled = self.compile_certificate(interval)?;
        let mut atlas = self
            .atlas
            .write()
            .map_err(|_| SheafDiffusionError::TransferAtlasPoisoned)?;
        if let Some(certificate) = atlas.get(interval) {
            return Ok((certificate.clone(), true));
        }
        atlas.insert(interval.clone(), compiled.clone());
        Ok((compiled, false))
    }

    fn compile_certificate(
        &self,
        interval: &Rat,
    ) -> Result<SheafDiffusionCertificate, SheafDiffusionError> {
        let coordinates = self.sheaf.coordinates(self.grade);
        let capacities = self.flattened_capacities();
        let coboundary_below = if self.grade == 0 {
            ExactRatMatrix::zero(coordinates.len(), 0)?
        } else {
            self.sheaf.coboundary(self.grade - 1)?
        };
        let coboundary_above = self.sheaf.coboundary(self.grade)?;
        let hodge_laplacian = self.sheaf.hodge_laplacian(self.grade)?;
        let mut operator = hodge_laplacian
            .to_rows()
            .iter()
            .map(|row| row.iter().map(|value| interval * value).collect::<Vec<_>>())
            .collect::<Vec<_>>();
        for (ordinal, capacity) in capacities.iter().enumerate() {
            operator[ordinal][ordinal] += capacity;
        }
        let operator = ExactRatMatrix::declared(coordinates.len(), coordinates.len(), operator)?;
        let inverse = operator.inverse()?;
        let inverse_residual = inverse
            .then(&operator)?
            .plus(&scaled_identity(coordinates.len(), -Rat::one())?)?;
        if inverse_residual
            .entries()
            .iter()
            .any(|value| !value.is_zero())
        {
            return Err(SheafDiffusionError::TransferCertificateFailure);
        }
        let harmonic_dimension = coordinates.len() - exact_rank(hodge_laplacian.to_rows());
        Ok(SheafDiffusionCertificate {
            schema: "holonic-engine.sheaf-diffusion-certificate.v1".to_owned(),
            grade: self.grade,
            coordinates,
            capacities,
            coboundary_below,
            coboundary_above,
            hodge_laplacian,
            operator,
            inverse,
            inverse_residual,
            harmonic_dimension,
        })
    }
}

impl ExactEventLaw for ExactSheafDiffusionLaw {
    type Standing = SheafDiffusionStanding;
    type Event = SheafDiffusionEvent;
    type Radiation = SheafDiffusionReceipt;
    type Error = SheafDiffusionError;

    fn enact(
        &self,
        standing_before: &Self::Standing,
        event: &Self::Event,
    ) -> Result<EventSuccessor<Self::Standing, Self::Radiation>, Self::Error> {
        let (standing_after, receipt) =
            ExactSheafDiffusionLaw::enact(self, standing_before, event)?;
        Ok(EventSuccessor {
            standing_after,
            radiation: vec![receipt],
            logical_resources: None,
            physical_resources: None,
        })
    }
}

fn validate_capacities(
    sheaf: &ExactCellularSheaf,
    grade: u32,
    capacities: &BTreeMap<CausalCellId, Vec<Rat>>,
) -> Result<(), SheafDiffusionError> {
    let expected = sheaf
        .complex
        .cells()
        .iter()
        .filter_map(|(cell, body)| (body.grade == grade).then_some(*cell))
        .collect::<BTreeSet<_>>();
    let supplied = capacities.keys().copied().collect::<BTreeSet<_>>();
    if let Some(cell) = expected.difference(&supplied).next() {
        return Err(SheafDiffusionError::MissingCapacity(*cell));
    }
    if let Some(cell) = supplied.difference(&expected).next() {
        return Err(SheafDiffusionError::WrongGradeCapacity { cell: *cell, grade });
    }
    for (cell, values) in capacities {
        let expected = sheaf.stalk_dimensions[cell];
        if values.len() != expected {
            return Err(SheafDiffusionError::CapacityDimension {
                cell: *cell,
                expected,
                supplied: values.len(),
            });
        }
        if values.iter().any(|value| !value.is_positive()) {
            return Err(SheafDiffusionError::NonpositiveCapacity(*cell));
        }
    }
    Ok(())
}

fn scaled_identity(extent: usize, scale: Rat) -> Result<ExactRatMatrix, SheafDiffusionError> {
    Ok(ExactRatMatrix::identity(extent)?.scaled(&scale))
}

/// Every refusal the shared exact carrier raises, named in this law's own vocabulary, so no
/// foreign error variant reaches a caller of this module.
impl From<ExactLinearError> for SheafDiffusionError {
    fn from(error: ExactLinearError) -> Self {
        match error {
            ExactLinearError::SingularMatrix => SheafDiffusionError::SingularLaw,
            ExactLinearError::InverseCertificateFailure
            | ExactLinearError::RankFactorizationCertificateFailure => {
                SheafDiffusionError::TransferCertificateFailure
            }
            ExactLinearError::RaggedMatrix
            | ExactLinearError::NonsquareMatrix
            | ExactLinearError::AddressOutside
            | ExactLinearError::ExtentOverflow
            | ExactLinearError::ShapeMismatch
            | ExactLinearError::DifferentProductCores => SheafDiffusionError::NonsquareOperator,
        }
    }
}

/// The exact inverse, **with the shared carrier's multiplication certificate in force**.
///
/// Before 2026-08-15 this built the inverse one column at a time through a private forward solve
/// — `O(n^4)` — and left the verification to its caller. The rationals are the same.
///
/// The declared extent is passed rather than inferred: a grade with no coordinates is a lawful
/// `0 x 0` operator, and `Vec<Vec<Rat>>` carries no column count when it has no rows.
fn exact_rank(mut matrix: Vec<Vec<Rat>>) -> usize {
    let rows = matrix.len();
    let columns = matrix.first().map_or(0, Vec::len);
    let mut pivot_row = 0;
    for column in 0..columns {
        let Some(pivot) = (pivot_row..rows).find(|row| !matrix[*row][column].is_zero()) else {
            continue;
        };
        matrix.swap(pivot_row, pivot);
        let divisor = matrix[pivot_row][column].clone();
        for entry in &mut matrix[pivot_row][column..] {
            *entry /= &divisor;
        }
        let row = matrix[pivot_row].clone();
        for (candidate, candidate_row) in matrix.iter_mut().enumerate() {
            if candidate == pivot_row || candidate_row[column].is_zero() {
                continue;
            }
            let factor = candidate_row[column].clone();
            for (entry, pivot_entry) in candidate_row[column..].iter_mut().zip(&row[column..]) {
                *entry -= &factor * pivot_entry;
            }
        }
        pivot_row += 1;
        if pivot_row == rows {
            break;
        }
    }
    pivot_row
}

fn diagonal_energy(values: &[Rat], weights: &[Rat]) -> Rat {
    let two = Rat::from_integer(2.into());
    values
        .iter()
        .zip(weights)
        .fold(Rat::zero(), |sum, (value, weight)| {
            sum + weight * value * value / &two
        })
}

fn euclidean_energy(values: &[Rat]) -> Rat {
    let two = Rat::from_integer(2.into());
    values
        .iter()
        .fold(Rat::zero(), |sum, value| sum + value * value / &two)
}

#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum SheafDiffusionError {
    #[error(
        "linear map entries do not have the declared {expected_rows} by {expected_columns} shape"
    )]
    MalformedLinearMap {
        expected_rows: usize,
        expected_columns: usize,
    },
    #[error(
        "linear maps cannot compose: the first target has {first_rows} coordinates and the next source has {next_columns}"
    )]
    LinearCompositionDimension {
        first_rows: usize,
        next_columns: usize,
    },
    #[error("linear maps with different dimensions cannot be added")]
    LinearAdditionDimension,
    #[error("linear map expected {expected} source coordinates, received {supplied}")]
    LinearApplicationDimension { expected: usize, supplied: usize },
    #[error("causal cell {0:?} has no declared sheaf stalk")]
    MissingStalk(CausalCellId),
    #[error("a sheaf stalk was declared for absent causal cell {0:?}")]
    UnknownStalk(CausalCellId),
    #[error("restriction {lower:?} -> {upper:?} was supplied more than once")]
    DuplicateRestriction {
        lower: CausalCellId,
        upper: CausalCellId,
    },
    #[error("incidence {lower:?} -> {upper:?} has no sheaf restriction")]
    MissingRestriction {
        lower: CausalCellId,
        upper: CausalCellId,
    },
    #[error("restriction {lower:?} -> {upper:?} does not follow immediate causal incidence")]
    NonincidentRestriction {
        lower: CausalCellId,
        upper: CausalCellId,
    },
    #[error(
        "restriction {lower:?} -> {upper:?} expected {expected_rows} by {expected_columns}, received {supplied_rows} by {supplied_columns}"
    )]
    RestrictionDimension {
        lower: CausalCellId,
        upper: CausalCellId,
        expected_rows: usize,
        expected_columns: usize,
        supplied_rows: usize,
        supplied_columns: usize,
    },
    #[error(
        "restriction transport from {origin:?} to {target:?} depends on the selected incidence path"
    )]
    PathDependentRestriction {
        origin: CausalCellId,
        target: CausalCellId,
    },
    #[error("cellular sheaf coboundary squared is nonzero beginning at grade {grade}")]
    CoboundarySquaredNonzero { grade: u32 },
    #[error("cochain omits causal cell {0:?}")]
    MissingCochainCell(CausalCellId),
    #[error("cochain cell {cell:?} does not inhabit grade {grade}")]
    WrongGradeCochainCell { cell: CausalCellId, grade: u32 },
    #[error("cochain at {cell:?} expected {expected} values, received {supplied}")]
    CochainDimension {
        cell: CausalCellId,
        expected: usize,
        supplied: usize,
    },
    #[error("flat cochain expected {expected} values, received {supplied}")]
    FlatCochainDimension { expected: usize, supplied: usize },
    #[error("diffusion capacity is absent at causal cell {0:?}")]
    MissingCapacity(CausalCellId),
    #[error("diffusion capacity at {cell:?} does not inhabit grade {grade}")]
    WrongGradeCapacity { cell: CausalCellId, grade: u32 },
    #[error("capacity at {cell:?} expected {expected} values, received {supplied}")]
    CapacityDimension {
        cell: CausalCellId,
        expected: usize,
        supplied: usize,
    },
    #[error("all diffusion capacities at causal cell {0:?} must be positive")]
    NonpositiveCapacity(CausalCellId),
    #[error("the diffusion law acts at grade {expected}, but standing supplied grade {supplied}")]
    LawGradeMismatch { expected: u32, supplied: u32 },
    #[error("source deed names absent causal cell {0:?}")]
    UnknownSourceCell(CausalCellId),
    #[error("source deed at {cell:?} has grade {supplied}, but this law acts at grade {expected}")]
    WrongGradeSourceCell {
        cell: CausalCellId,
        expected: u32,
        supplied: u32,
    },
    #[error("source deed at {cell:?} expected {expected} values, received {supplied}")]
    SourceDimension {
        cell: CausalCellId,
        expected: usize,
        supplied: usize,
    },
    #[error("a completed sheaf-diffusion event requires a positive exact interval")]
    NonpositiveInterval,
    #[error("the exact sheaf diffusion operator is not square")]
    NonsquareOperator,
    #[error("the exact sheaf diffusion law is singular")]
    SingularLaw,
    #[error("the exact sheaf diffusion transfer atlas was poisoned")]
    TransferAtlasPoisoned,
    #[error("the exact sheaf diffusion inverse failed its identity certificate")]
    TransferCertificateFailure,
    #[error("the exact sheaf diffusion solve retained a nonzero operator residual")]
    SolveResidualNonzero,
    #[error("the exact sheaf diffusion event retained a nonzero balance residual")]
    BalanceResidualNonzero,
    #[error("a closed source-free sheaf diffusion event increased stored energy")]
    EnergyIncreased,
    #[error(transparent)]
    Algebraic(#[from] CausalAlgebraicError),
    /// The Holon core refused (a Dirac, resistance or step certificate).
    #[error(transparent)]
    Holon(Box<holonic_core::holon::HolonError>),
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeSet;

    use relational_geometry::integer;

    use super::*;
    use crate::{CausalChain, ComparativeMultiplicity, EventId};

    fn interval_complex() -> (
        GradedCausalComplex,
        CausalCellId,
        CausalCellId,
        CausalCellId,
    ) {
        let mut complex = GradedCausalComplex::default();
        let events = BTreeSet::from([EventId(1)]);
        let left = complex
            .found_cell("left", events.clone(), 0, CausalChain::default())
            .unwrap();
        let right = complex
            .found_cell("right", events.clone(), 0, CausalChain::default())
            .unwrap();
        let mut boundary = CausalChain::default();
        boundary.add_term(left, ComparativeMultiplicity::negative(1_u8));
        boundary.add_term(right, ComparativeMultiplicity::positive(1_u8));
        let edge = complex.found_cell("edge", events, 1, boundary).unwrap();
        (complex, left, right, edge)
    }

    fn constant_interval_sheaf() -> (ExactCellularSheaf, CausalCellId, CausalCellId, CausalCellId) {
        let (complex, left, right, edge) = interval_complex();
        let dimensions = complex
            .cells()
            .keys()
            .map(|cell| (*cell, 1_usize))
            .collect();
        let sheaf = ExactCellularSheaf::new(
            complex,
            dimensions,
            [
                CellularRestriction {
                    lower: left,
                    upper: edge,
                    map: ExactRatMatrix::identity(1).unwrap(),
                },
                CellularRestriction {
                    lower: right,
                    upper: edge,
                    map: ExactRatMatrix::identity(1).unwrap(),
                },
            ],
        )
        .unwrap();
        (sheaf, left, right, edge)
    }

    #[test]
    fn rank_one_interval_reproduces_exact_scalar_diffusion() {
        let (sheaf, left, right, _) = constant_interval_sheaf();
        let law = ExactSheafDiffusionLaw::new(
            sheaf.clone(),
            0,
            BTreeMap::from([(left, vec![integer(1)]), (right, vec![integer(1)])]),
        )
        .unwrap();
        let standing = law
            .initial_standing(
                ExactSheafCochain::new(
                    &sheaf,
                    0,
                    BTreeMap::from([(left, vec![integer(1)]), (right, vec![integer(0)])]),
                )
                .unwrap(),
            )
            .unwrap();
        let (after, receipt) = law
            .enact(
                &standing,
                &SheafDiffusionEvent {
                    interval: integer(1),
                    source: BTreeMap::new(),
                },
            )
            .unwrap();
        assert_eq!(after.content.values[&left], vec![integer(2) / integer(3)]);
        assert_eq!(after.content.values[&right], vec![integer(1) / integer(3)]);
        assert_eq!(receipt.compatibility_after.values.len(), 1);
        assert_eq!(receipt.certificate.harmonic_dimension, 1);
        assert!(receipt
            .balance_residual
            .values
            .values()
            .flatten()
            .all(Zero::is_zero));
        let energy = law
            .energy_balance(
                &receipt,
                &SheafDiffusionEvent {
                    interval: integer(1),
                    source: BTreeMap::new(),
                },
            )
            .unwrap();
        assert_eq!(energy.source_work, integer(0));
        assert_eq!(energy.conductive_dissipation, integer(1) / integer(9));
        assert_eq!(energy.implicit_step_defect, integer(1) / integer(9));
        assert_eq!(energy.exact_residual, integer(0));
        assert!(!receipt.reused_factorization);
        let (_, second) = law
            .enact(
                &after,
                &SheafDiffusionEvent {
                    interval: integer(1),
                    source: BTreeMap::new(),
                },
            )
            .unwrap();
        assert!(second.reused_factorization);
        assert_eq!(law.transfer_cache_entries(), 1);
    }

    #[test]
    fn constant_sections_are_exactly_compatible() {
        let (sheaf, left, right, _) = constant_interval_sheaf();
        let section = ExactSheafCochain::new(
            &sheaf,
            0,
            BTreeMap::from([(left, vec![integer(7)]), (right, vec![integer(7)])]),
        )
        .unwrap();
        let residual = sheaf
            .coboundary(0)
            .unwrap()
            .apply(&section.flattened(&sheaf).unwrap())
            .unwrap();
        assert!(residual.iter().all(Zero::is_zero));

        let law = ExactSheafDiffusionLaw::new(
            sheaf.clone(),
            0,
            BTreeMap::from([(left, vec![integer(1)]), (right, vec![integer(1)])]),
        )
        .unwrap();
        let standing = law.initial_standing(section.clone()).unwrap();
        let (after, receipt) = law
            .enact(
                &standing,
                &SheafDiffusionEvent {
                    interval: integer(1),
                    source: BTreeMap::new(),
                },
            )
            .unwrap();
        assert_eq!(after.content, standing.content);
        let energy = law
            .energy_balance(
                &receipt,
                &SheafDiffusionEvent {
                    interval: integer(1),
                    source: BTreeMap::new(),
                },
            )
            .unwrap();
        assert_eq!(energy.conductive_dissipation, integer(0));
        assert_eq!(energy.implicit_step_defect, integer(0));
        assert_eq!(energy.exact_residual, integer(0));
    }

    #[test]
    fn source_work_can_overcome_diffusion_and_step_defect() {
        let (sheaf, left, right, _) = constant_interval_sheaf();
        let law = ExactSheafDiffusionLaw::new(
            sheaf.clone(),
            0,
            BTreeMap::from([(left, vec![integer(1)]), (right, vec![integer(1)])]),
        )
        .unwrap();
        let standing = law
            .initial_standing(
                ExactSheafCochain::new(
                    &sheaf,
                    0,
                    BTreeMap::from([(left, vec![integer(1)]), (right, vec![integer(0)])]),
                )
                .unwrap(),
            )
            .unwrap();
        let event = SheafDiffusionEvent {
            interval: integer(1),
            source: BTreeMap::from([(left, vec![integer(1)])]),
        };
        let (after, receipt) = law.enact(&standing, &event).unwrap();
        assert_eq!(after.content.values[&left], vec![integer(4) / integer(3)]);
        assert_eq!(after.content.values[&right], vec![integer(2) / integer(3)]);
        let energy = law.energy_balance(&receipt, &event).unwrap();
        assert_eq!(energy.source_work, integer(4) / integer(3));
        assert_eq!(energy.conductive_dissipation, integer(4) / integer(9));
        assert_eq!(energy.implicit_step_defect, integer(5) / integer(18));
        assert_eq!(energy.exact_residual, integer(0));
        assert_eq!(receipt.energy_departed, -(integer(11) / integer(18)));
    }

    #[test]
    fn grade_one_energy_retains_lower_coboundary_and_the_actual_source_law() {
        let (sheaf, _, _, edge) = constant_interval_sheaf();
        let law = ExactSheafDiffusionLaw::new(
            sheaf.clone(),
            1,
            BTreeMap::from([(edge, vec![integer(1)])]),
        )
        .unwrap();
        let standing = law
            .initial_standing(
                ExactSheafCochain::new(&sheaf, 1, BTreeMap::from([(edge, vec![integer(1)])]))
                    .unwrap(),
            )
            .unwrap();
        let event = SheafDiffusionEvent {
            interval: integer(1),
            source: BTreeMap::new(),
        };
        let (_, receipt) = law.enact(&standing, &event).unwrap();
        let energy = law.energy_balance(&receipt, &event).unwrap();
        assert!(receipt.compatibility_energy_after.is_zero());
        assert_eq!(energy.conductive_dissipation, integer(2) / integer(9));
        assert_eq!(energy.implicit_step_defect, integer(2) / integer(9));
        assert!(energy.exact_residual.is_zero());
        let mut other_operator = receipt.clone();
        let laplacian = &other_operator.certificate.hodge_laplacian;
        let (extent, mut rows) = (laplacian.rows(), laplacian.to_rows());
        rows[0][0] = integer(0);
        other_operator.certificate.hodge_laplacian =
            ExactRatMatrix::declared(extent, extent, rows).unwrap();
        assert_eq!(
            law.energy_balance(&other_operator, &event),
            Err(SheafDiffusionError::TransferCertificateFailure)
        );
    }

    /// **The replaced carrier's wire is unchanged.** A restriction and a certificate map serialize
    /// exactly as the retired `ExactRatMatrix { rows, columns, entries: Vec<Vec<Rat>> }` did, and
    /// that wire deserializes back to the same `ExactRatMatrix`; a misshapen row population
    /// refuses at deserialization.
    #[test]
    fn the_linear_map_wire_keeps_its_row_shape() {
        #[derive(Serialize)]
        struct RetiredMap {
            rows: usize,
            columns: usize,
            entries: Vec<Vec<Rat>>,
        }
        #[derive(Serialize)]
        struct RetiredRestriction {
            lower: CausalCellId,
            upper: CausalCellId,
            map: RetiredMap,
        }
        let entries = vec![vec![integer(1), Rat::new(2.into(), 3.into())]];
        let restriction = CellularRestriction {
            lower: CausalCellId(1),
            upper: CausalCellId(2),
            map: ExactRatMatrix::declared(1, 2, entries.clone()).unwrap(),
        };
        let written = serde_json::to_string(&restriction).unwrap();
        let retired = serde_json::to_string(&RetiredRestriction {
            lower: CausalCellId(1),
            upper: CausalCellId(2),
            map: RetiredMap {
                rows: 1,
                columns: 2,
                entries,
            },
        })
        .unwrap();
        assert_eq!(written, retired);
        let read: CellularRestriction = serde_json::from_str(&retired).unwrap();
        assert_eq!(read, restriction);

        let (complex, left, right, edge) = interval_complex();
        let sheaf = ExactCellularSheaf::new(
            complex,
            BTreeMap::from([(left, 1), (right, 1), (edge, 1)]),
            [
                CellularRestriction {
                    lower: left,
                    upper: edge,
                    map: ExactRatMatrix::identity(1).unwrap(),
                },
                CellularRestriction {
                    lower: right,
                    upper: edge,
                    map: ExactRatMatrix::identity(1).unwrap(),
                },
            ],
        )
        .unwrap();
        // The restriction table is keyed by an incidence pair, which JSON cannot key; RON can.
        let wire = ron::to_string(&sheaf).unwrap();
        assert_eq!(wire.matches("entries:[[").count(), 2, "{wire}");
        let read: ExactCellularSheaf = ron::from_str(&wire).unwrap();
        assert_eq!(read, sheaf);

        let ragged = retired.replacen("\"columns\":2", "\"columns\":3", 1);
        assert!(serde_json::from_str::<CellularRestriction>(&ragged).is_err());
    }

    #[test]
    fn heterogeneous_vector_stalks_are_not_collapsed_to_node_scalars() {
        let (complex, left, right, edge) = interval_complex();
        let sheaf = ExactCellularSheaf::new(
            complex,
            BTreeMap::from([(left, 2), (right, 2), (edge, 1)]),
            [
                CellularRestriction {
                    lower: left,
                    upper: edge,
                    map: ExactRatMatrix::declared(1, 2, vec![vec![integer(1), integer(0)]])
                        .unwrap(),
                },
                CellularRestriction {
                    lower: right,
                    upper: edge,
                    map: ExactRatMatrix::declared(1, 2, vec![vec![integer(0), integer(1)]])
                        .unwrap(),
                },
            ],
        )
        .unwrap();
        let compatible = ExactSheafCochain::new(
            &sheaf,
            0,
            BTreeMap::from([
                (left, vec![integer(3), integer(9)]),
                (right, vec![integer(5), integer(3)]),
            ]),
        )
        .unwrap();
        assert!(sheaf
            .coboundary(0)
            .unwrap()
            .apply(&compatible.flattened(&sheaf).unwrap())
            .unwrap()
            .iter()
            .all(Zero::is_zero));
        let law = ExactSheafDiffusionLaw::new(
            sheaf.clone(),
            0,
            BTreeMap::from([
                (left, vec![integer(1), integer(1)]),
                (right, vec![integer(1), integer(1)]),
            ]),
        )
        .unwrap();
        let standing = law.initial_standing(compatible).unwrap();
        let (_, receipt) = law
            .enact(
                &standing,
                &SheafDiffusionEvent {
                    interval: integer(1),
                    source: BTreeMap::new(),
                },
            )
            .unwrap();
        assert_eq!(receipt.certificate.coordinates.len(), 4);
        assert_eq!(receipt.certificate.harmonic_dimension, 3);
        assert!(receipt.compatibility_after.values[&edge][0].is_zero());
    }

    #[test]
    fn path_dependent_transport_across_a_triangle_is_refused() {
        let mut complex = GradedCausalComplex::default();
        let simplex = complex
            .found_simplex("triangle", EventId(1), ["a", "b", "c"])
            .unwrap();
        let dimensions = complex
            .cells()
            .keys()
            .map(|cell| (*cell, 1_usize))
            .collect::<BTreeMap<_, _>>();
        let apex = simplex.apex;
        let mut restrictions = Vec::new();
        let first_apex_face = complex.cells()[&apex]
            .boundary
            .support()
            .into_iter()
            .next()
            .unwrap();
        for (upper, body) in complex.cells() {
            for lower in body.boundary.support() {
                let scale = if *upper == apex && lower == first_apex_face {
                    integer(2)
                } else {
                    integer(1)
                };
                restrictions.push(CellularRestriction {
                    lower,
                    upper: *upper,
                    map: ExactRatMatrix::declared(1, 1, vec![vec![scale]]).unwrap(),
                });
            }
        }
        assert!(matches!(
            ExactCellularSheaf::new(complex, dimensions, restrictions),
            Err(SheafDiffusionError::PathDependentRestriction { .. })
        ));
    }
}

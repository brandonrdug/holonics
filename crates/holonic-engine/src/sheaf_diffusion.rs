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
//! # Two carriers, and which one owns what
//!
//! `ExactLinearMap` below is this law's own **typed and serialized** carrier: it names its source
//! and target coordinates, it is what a certificate is written in, and it stays. What does not
//! stay is the private dense algebra that sat underneath it. Until 2026-08-15 this module carried
//! its own `invert_exact`, which built the inverse **one column at a time** — `O(n^4)` — through a
//! `solve_exact` that shared 26 lines verbatim with `diffusion`'s (32 lines against 36; the rest
//! is a squareness guard, the error variant, and two rebindings). Both are gone: the inverse runs
//! through `exact_linear::ExactRatMatrix`, whose multiplication certificate is in force, and the
//! duplicated forward solve had no caller but that inverse. `then`, `plus` and `apply` route
//! through the same carrier, so this module contains no dense elimination or product of its own.
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

use crate::exact_linear::{ExactLinearError, ExactRatMatrix};
use crate::{
    CausalAlgebraicError, CausalCellId, EventSuccessor, ExactEventLaw, GradedCausalComplex,
};

/// A finite exact linear map.  Rows are target coordinates and columns are
/// source coordinates.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ExactLinearMap {
    rows: usize,
    columns: usize,
    entries: Vec<Vec<Rat>>,
}

impl ExactLinearMap {
    pub fn new(
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
        Ok(Self {
            rows,
            columns,
            entries,
        })
    }

    pub fn zero(rows: usize, columns: usize) -> Self {
        Self {
            rows,
            columns,
            entries: vec![vec![Rat::zero(); columns]; rows],
        }
    }

    pub fn identity(extent: usize) -> Self {
        let mut result = Self::zero(extent, extent);
        for diagonal in 0..extent {
            result.entries[diagonal][diagonal] = Rat::one();
        }
        result
    }

    pub fn rows(&self) -> usize {
        self.rows
    }

    pub fn columns(&self) -> usize {
        self.columns
    }

    pub fn entries(&self) -> &[Vec<Rat>] {
        &self.entries
    }

    /// This map's entries presented to the shared exact carrier, against the shape this map
    /// **declares** rather than one inferred from its rows. A map with no rows still has a
    /// column count and a zero-dimensional stalk is lawful, so inference would lose it.
    fn carrier(&self) -> Result<ExactRatMatrix, SheafDiffusionError> {
        Ok(ExactRatMatrix::shaped(
            self.rows,
            self.columns,
            self.entries.clone(),
        )?)
    }

    fn from_carrier(carrier: &ExactRatMatrix) -> Self {
        Self {
            rows: carrier.rows(),
            columns: carrier.columns(),
            entries: carrier.to_rows(),
        }
    }

    pub fn transpose(&self) -> Self {
        let mut entries = vec![vec![Rat::zero(); self.rows]; self.columns];
        for (row, values) in self.entries.iter().enumerate() {
            for (column, value) in values.iter().enumerate() {
                entries[column][row] = value.clone();
            }
        }
        Self {
            rows: self.columns,
            columns: self.rows,
            entries,
        }
    }

    /// Compose `self: A -> B` followed by `next: B -> C`.
    ///
    /// The dimension refusal is this law's own and is raised before the carrier is reached, so a
    /// caller sees `LinearCompositionDimension` and never a foreign shape error.
    pub fn then(&self, next: &Self) -> Result<Self, SheafDiffusionError> {
        if self.rows != next.columns {
            return Err(SheafDiffusionError::LinearCompositionDimension {
                first_rows: self.rows,
                next_columns: next.columns,
            });
        }
        Ok(Self::from_carrier(
            &next.carrier()?.multiply(&self.carrier()?)?,
        ))
    }

    pub fn plus(&self, other: &Self) -> Result<Self, SheafDiffusionError> {
        if self.rows != other.rows || self.columns != other.columns {
            return Err(SheafDiffusionError::LinearAdditionDimension);
        }
        Ok(Self::from_carrier(&self.carrier()?.add(&other.carrier()?)?))
    }

    pub fn apply(&self, source: &[Rat]) -> Result<Vec<Rat>, SheafDiffusionError> {
        if source.len() != self.columns {
            return Err(SheafDiffusionError::LinearApplicationDimension {
                expected: self.columns,
                supplied: source.len(),
            });
        }
        Ok(self.carrier()?.apply(source)?)
    }

    fn validate(&self) -> Result<(), SheafDiffusionError> {
        if self.entries.len() != self.rows
            || self.entries.iter().any(|row| row.len() != self.columns)
        {
            return Err(SheafDiffusionError::MalformedLinearMap {
                expected_rows: self.rows,
                expected_columns: self.columns,
            });
        }
        Ok(())
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CellularRestriction {
    pub lower: CausalCellId,
    pub upper: CausalCellId,
    pub map: ExactLinearMap,
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
    restrictions: BTreeMap<(CausalCellId, CausalCellId), ExactLinearMap>,
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

    pub fn restrictions(&self) -> &BTreeMap<(CausalCellId, CausalCellId), ExactLinearMap> {
        &self.restrictions
    }

    pub fn restriction(
        &self,
        lower: CausalCellId,
        upper: CausalCellId,
    ) -> Result<&ExactLinearMap, SheafDiffusionError> {
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
    pub fn coboundary(&self, grade: u32) -> Result<ExactLinearMap, SheafDiffusionError> {
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
                for row in 0..restriction.rows {
                    for column in 0..restriction.columns {
                        entries[target_offset + row][source_offset + column] +=
                            &incidence * &restriction.entries[row][column];
                    }
                }
            }
        }
        ExactLinearMap::new(target.len(), source.len(), entries)
    }

    /// The exact Hodge operator
    /// `Delta_k = delta_(k-1) delta_(k-1)^T + delta_k^T delta_k`.
    pub fn hodge_laplacian(&self, grade: u32) -> Result<ExactLinearMap, SheafDiffusionError> {
        let extent = self.coordinates(grade).len();
        let upper = self.coboundary(grade)?;
        let upper_term = upper.then(&upper.transpose())?;
        let lower_term = if grade == 0 {
            ExactLinearMap::zero(extent, extent)
        } else {
            let lower = self.coboundary(grade - 1)?;
            lower.transpose().then(&lower)?
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
            map.validate()?;
            let expected_rows = self.stalk_dimensions[upper];
            let expected_columns = self.stalk_dimensions[lower];
            if map.rows != expected_rows || map.columns != expected_columns {
                return Err(SheafDiffusionError::RestrictionDimension {
                    lower: *lower,
                    upper: *upper,
                    expected_rows,
                    expected_columns,
                    supplied_rows: map.rows,
                    supplied_columns: map.columns,
                });
            }
        }

        self.validate_path_independence()?;
        if let Some(dimension) = self.complex.dimension() {
            for grade in 0..dimension {
                let first = self.coboundary(grade)?;
                let second = self.coboundary(grade.saturating_add(1))?;
                let squared = first.then(&second)?;
                if squared
                    .entries
                    .iter()
                    .flatten()
                    .any(|value| !value.is_zero())
                {
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
                ExactLinearMap::identity(self.stalk_dimensions[&source]),
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
    pub coboundary_below: ExactLinearMap,
    pub coboundary_above: ExactLinearMap,
    pub hodge_laplacian: ExactLinearMap,
    pub operator: ExactLinearMap,
    pub inverse: ExactLinearMap,
    pub inverse_residual: ExactLinearMap,
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
        Ok((
            standing_after,
            SheafDiffusionReceipt {
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
            },
        ))
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
            ExactLinearMap::zero(coordinates.len(), 0)
        } else {
            self.sheaf.coboundary(self.grade - 1)?
        };
        let coboundary_above = self.sheaf.coboundary(self.grade)?;
        let hodge_laplacian = self.sheaf.hodge_laplacian(self.grade)?;
        let mut operator = hodge_laplacian
            .entries
            .iter()
            .map(|row| row.iter().map(|value| interval * value).collect::<Vec<_>>())
            .collect::<Vec<_>>();
        for (ordinal, capacity) in capacities.iter().enumerate() {
            operator[ordinal][ordinal] += capacity;
        }
        let operator = ExactLinearMap::new(coordinates.len(), coordinates.len(), operator)?;
        let inverse = ExactLinearMap::new(
            coordinates.len(),
            coordinates.len(),
            invert_exact(operator.entries.clone())?,
        )?;
        let inverse_residual = inverse
            .then(&operator)?
            .plus(&scaled_identity(coordinates.len(), -Rat::one()))?;
        if inverse_residual
            .entries
            .iter()
            .flatten()
            .any(|value| !value.is_zero())
        {
            return Err(SheafDiffusionError::TransferCertificateFailure);
        }
        let harmonic_dimension = coordinates.len() - exact_rank(hodge_laplacian.entries.clone());
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

fn scaled_identity(extent: usize, scale: Rat) -> ExactLinearMap {
    let mut result = ExactLinearMap::zero(extent, extent);
    for diagonal in 0..extent {
        result.entries[diagonal][diagonal] = scale.clone();
    }
    result
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
            | ExactLinearError::ShapeMismatch => SheafDiffusionError::NonsquareOperator,
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
fn invert_exact(matrix: Vec<Vec<Rat>>) -> Result<Vec<Vec<Rat>>, SheafDiffusionError> {
    let extent = matrix.len();
    Ok(ExactRatMatrix::shaped(extent, extent, matrix)?
        .inverse()?
        .to_rows())
}

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
                    map: ExactLinearMap::identity(1),
                },
                CellularRestriction {
                    lower: right,
                    upper: edge,
                    map: ExactLinearMap::identity(1),
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
        assert!(
            receipt
                .balance_residual
                .values
                .values()
                .flatten()
                .all(Zero::is_zero)
        );
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
                    map: ExactLinearMap::new(1, 2, vec![vec![integer(1), integer(0)]]).unwrap(),
                },
                CellularRestriction {
                    lower: right,
                    upper: edge,
                    map: ExactLinearMap::new(1, 2, vec![vec![integer(0), integer(1)]]).unwrap(),
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
        assert!(
            sheaf
                .coboundary(0)
                .unwrap()
                .apply(&compatible.flattened(&sheaf).unwrap())
                .unwrap()
                .iter()
                .all(Zero::is_zero)
        );
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
                    map: ExactLinearMap::new(1, 1, vec![vec![scale]]).unwrap(),
                });
            }
        }
        assert!(matches!(
            ExactCellularSheaf::new(complex, dimensions, restrictions),
            Err(SheafDiffusionError::PathDependentRestriction { .. })
        ));
    }
}

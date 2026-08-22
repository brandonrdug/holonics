//! Exact diffusion through a finite oriented incidence complex.
//!
//! This is one source-declared physical law, not a universal smoothing
//! policy. Nodes carry exact capacity and content. Oriented branches carry
//! exact nonnegative conductance magnitudes; the sign of a realized current
//! emerges from the endpoint potential difference. One completed event solves
//! the implicit finite transport relation
//!
//! `M phi_after = n_before + source + tau * partial(j_after)`
//! `j_after(e) = c(e) * (phi_after(source)-phi_after(target))`.
//!
//! The solve is exact rational elimination. No continuous PDE, floating point,
//! pixel adjacency, authored probability, or convergence tolerance enters.
//!
//! # Where the algebra lives
//!
//! The dense exact algebra is `exact_linear::ExactRatMatrix` and not this module's own. It was
//! this module's own until 2026-08-15, which cost one measured thing: `invert_exact` built the
//! inverse **one column at a time**, running a full forward solve per column — `O(n^4)`, where
//! the shared carrier's augmented elimination runs once. Routing through the carrier closes it;
//! the Schur elimination below is unchanged and returns the same rationals it always did.
//!
//! It also puts the carrier's multiplication certificate in force inside the operation. That is
//! a smaller change here than elsewhere and the record should say so: `compile_diffusion_transfer`
//! has always computed `interior_inverse_residual` and `boundary_inverse_residual` and refused on
//! either, so this inverse was **already** checked — downstream, by the caller, rather than at
//! construction. Those residuals stay; they are what a later reader of the retained certificate
//! has, and the carrier's check is what a future caller who forgets to write one will have.
//!
//! What did **not** move is `solve_exact`, which now stands only as this module's independent
//! forward solve for the cross-check in `tests`. Routing that through the same carrier would
//! have left the Schur path compared against itself.

use std::collections::{BTreeMap, BTreeSet};
use std::sync::{Arc, RwLock};

use num_traits::{Signed, Zero};
use relational_geometry::Rat;
use serde::{Deserialize, Serialize};
use thiserror::Error;

use crate::exact_linear::{ExactLinearError, ExactRatMatrix};
use crate::{CurrentBranchId, CurrentNodeId};

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct DiffusionNode {
    pub node: CurrentNodeId,
    /// Positive local content per unit potential.
    pub capacity: Rat,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct DiffusionBranch {
    pub branch: CurrentBranchId,
    pub source: CurrentNodeId,
    pub target: CurrentNodeId,
    /// Nonnegative magnitude. Current orientation is derived, not declared.
    pub conductance: Rat,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct DiffusionComplex {
    pub schema: String,
    nodes: BTreeMap<CurrentNodeId, DiffusionNode>,
    branches: BTreeMap<CurrentBranchId, DiffusionBranch>,
}

impl DiffusionComplex {
    pub fn new(
        nodes: impl IntoIterator<Item = DiffusionNode>,
        branches: impl IntoIterator<Item = DiffusionBranch>,
    ) -> Result<Self, DiffusionError> {
        let mut indexed_nodes = BTreeMap::new();
        for node in nodes {
            let id = node.node;
            if indexed_nodes.insert(id, node).is_some() {
                return Err(DiffusionError::DuplicateNode(id));
            }
        }
        let nodes = indexed_nodes;
        if nodes.is_empty() {
            return Err(DiffusionError::EmptyComplex);
        }
        for node in nodes.values() {
            if !node.capacity.is_positive() {
                return Err(DiffusionError::NonpositiveCapacity(node.node));
            }
        }
        let mut indexed_branches = BTreeMap::new();
        for branch in branches {
            let id = branch.branch;
            if indexed_branches.insert(id, branch).is_some() {
                return Err(DiffusionError::DuplicateBranch(id));
            }
        }
        let branches = indexed_branches;
        for branch in branches.values() {
            if !nodes.contains_key(&branch.source) {
                return Err(DiffusionError::MissingNode(branch.source));
            }
            if !nodes.contains_key(&branch.target) {
                return Err(DiffusionError::MissingNode(branch.target));
            }
            if branch.source == branch.target {
                return Err(DiffusionError::DegenerateBranch(branch.branch));
            }
            if branch.conductance.is_negative() {
                return Err(DiffusionError::NegativeConductance(branch.branch));
            }
        }
        Ok(Self {
            schema: "holonic-engine.diffusion-complex.v1".to_owned(),
            nodes,
            branches,
        })
    }

    pub fn nodes(&self) -> &BTreeMap<CurrentNodeId, DiffusionNode> {
        &self.nodes
    }

    pub fn branches(&self) -> &BTreeMap<CurrentBranchId, DiffusionBranch> {
        &self.branches
    }

    fn validate(&self) -> Result<(), DiffusionError> {
        let reconstructed = Self::new(
            self.nodes.values().cloned(),
            self.branches.values().cloned(),
        )?;
        if reconstructed.nodes != self.nodes || reconstructed.branches != self.branches {
            return Err(DiffusionError::MalformedComplex);
        }
        Ok(())
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct DiffusionStanding {
    pub schema: String,
    pub content: BTreeMap<CurrentNodeId, Rat>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct DiffusionEvent {
    /// Exact duration of this completed event grain.
    pub interval: Rat,
    /// Signed boundary deed at each named node.
    pub source: BTreeMap<CurrentNodeId, Rat>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct DiffusionCurrent {
    pub branch: CurrentBranchId,
    pub source: CurrentNodeId,
    pub target: CurrentNodeId,
    /// Positive means source-to-target; negative means the opposite hand.
    pub current: Rat,
    /// Current integrated across this event interval.
    pub transferred: Rat,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct DiffusionNodeBalance {
    pub node: CurrentNodeId,
    pub content_before: Rat,
    pub source: Rat,
    /// Incoming minus outgoing integrated branch current.
    pub boundary_transfer: Rat,
    pub content_after: Rat,
    pub exact_residual: Rat,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct DiffusionReceipt {
    pub schema: String,
    pub interval: Rat,
    pub potential_before: BTreeMap<CurrentNodeId, Rat>,
    pub potential_after: BTreeMap<CurrentNodeId, Rat>,
    pub currents: Vec<DiffusionCurrent>,
    pub balances: Vec<DiffusionNodeBalance>,
    pub total_before: Rat,
    pub total_source: Rat,
    pub total_after: Rat,
    pub conservation_residual: Rat,
    pub stored_energy_before: Rat,
    pub stored_energy_after: Rat,
    /// Exact change in stored quadratic energy. It is nonnegative for the
    /// closed source-free law declared here.
    pub energy_departed: Rat,
    pub transfer: DiffusionBoundaryTransferReceipt,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct DiffusionBoundaryTransferCertificate {
    pub schema: String,
    pub interval: Rat,
    pub boundary: Vec<CurrentNodeId>,
    pub interior: Vec<CurrentNodeId>,
    pub node_order: Vec<CurrentNodeId>,
    pub capacities: Vec<(CurrentNodeId, Rat)>,
    pub oriented_branches: Vec<(CurrentBranchId, CurrentNodeId, CurrentNodeId, Rat)>,
    pub operator: Vec<Vec<Rat>>,
    pub interior_inverse: Vec<Vec<Rat>>,
    pub schur_boundary_operator: Vec<Vec<Rat>>,
    pub boundary_inverse: Vec<Vec<Rat>>,
    pub interior_inverse_residual: Vec<Vec<Rat>>,
    pub boundary_inverse_residual: Vec<Vec<Rat>>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct DiffusionBoundaryTransferReceipt {
    pub reused_factorization: bool,
    pub certificate: DiffusionBoundaryTransferCertificate,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct DiffusionTransferKey {
    interval: Rat,
    boundary: Vec<CurrentNodeId>,
}

#[derive(Clone, Debug)]
struct CertifiedDiffusionTransfer {
    certificate: DiffusionBoundaryTransferCertificate,
    boundary_ordinals: Vec<usize>,
    interior_ordinals: Vec<usize>,
    boundary_interior: Vec<Vec<Rat>>,
    interior_boundary: Vec<Vec<Rat>>,
}

#[derive(Clone, Debug)]
pub struct ExactDiffusionLaw {
    complex: DiffusionComplex,
    boundary: Vec<CurrentNodeId>,
    transfer_atlas: Arc<RwLock<BTreeMap<DiffusionTransferKey, CertifiedDiffusionTransfer>>>,
}

impl ExactDiffusionLaw {
    pub fn new(complex: DiffusionComplex) -> Result<Self, DiffusionError> {
        let boundary = complex.nodes.keys().copied().collect::<Vec<_>>();
        Self::with_boundary(complex, boundary)
    }

    pub fn with_boundary(
        complex: DiffusionComplex,
        boundary: impl IntoIterator<Item = CurrentNodeId>,
    ) -> Result<Self, DiffusionError> {
        complex.validate()?;
        let boundary = boundary.into_iter().collect::<BTreeSet<_>>();
        if let Some(node) = boundary
            .iter()
            .find(|node| !complex.nodes.contains_key(node))
        {
            return Err(DiffusionError::MissingNode(*node));
        }
        Ok(Self {
            complex,
            boundary: boundary.into_iter().collect(),
            transfer_atlas: Arc::new(RwLock::new(BTreeMap::new())),
        })
    }

    pub fn complex(&self) -> &DiffusionComplex {
        &self.complex
    }

    pub fn boundary(&self) -> &[CurrentNodeId] {
        &self.boundary
    }

    pub fn transfer_cache_entries(&self) -> usize {
        self.transfer_atlas
            .read()
            .expect("the exact diffusion transfer atlas is not poisoned")
            .len()
    }

    fn boundary_transfer(
        &self,
        interval: &Rat,
    ) -> Result<(CertifiedDiffusionTransfer, bool), DiffusionError> {
        let key = DiffusionTransferKey {
            interval: interval.clone(),
            boundary: self.boundary.clone(),
        };
        if let Some(transfer) = self
            .transfer_atlas
            .read()
            .map_err(|_| DiffusionError::TransferAtlasPoisoned)?
            .get(&key)
            .cloned()
        {
            return Ok((transfer, true));
        }
        let compiled = compile_diffusion_transfer(&self.complex, interval, &self.boundary)?;
        let mut atlas = self
            .transfer_atlas
            .write()
            .map_err(|_| DiffusionError::TransferAtlasPoisoned)?;
        if let Some(transfer) = atlas.get(&key) {
            return Ok((transfer.clone(), true));
        }
        atlas.insert(key, compiled.clone());
        Ok((compiled, false))
    }

    pub fn initial_standing(
        &self,
        content: BTreeMap<CurrentNodeId, Rat>,
    ) -> Result<DiffusionStanding, DiffusionError> {
        validate_population(self.complex.nodes.keys().copied(), &content)?;
        Ok(DiffusionStanding {
            schema: "holonic-engine.diffusion-standing.v1".to_owned(),
            content,
        })
    }

    pub fn enact(
        &self,
        standing: &DiffusionStanding,
        event: &DiffusionEvent,
    ) -> Result<(DiffusionStanding, DiffusionReceipt), DiffusionError> {
        if !event.interval.is_positive() {
            return Err(DiffusionError::NonpositiveInterval);
        }
        validate_population(self.complex.nodes.keys().copied(), &standing.content)?;
        for node in event.source.keys() {
            if !self.complex.nodes.contains_key(node) {
                return Err(DiffusionError::MissingNode(*node));
            }
        }

        let (transfer, reused_factorization) = self.boundary_transfer(&event.interval)?;
        let order = &transfer.certificate.node_order;
        let extent = order.len();
        let mut right = vec![Rat::zero(); extent];
        let mut potential_before = BTreeMap::new();

        for (ordinal, node) in order.iter().enumerate() {
            let capacity = &self.complex.nodes[node].capacity;
            right[ordinal] =
                &standing.content[node] + event.source.get(node).cloned().unwrap_or_else(Rat::zero);
            potential_before.insert(*node, &standing.content[node] / capacity);
        }

        let solved = solve_with_transfer(&transfer, &right)?;
        let potential_after = order
            .iter()
            .copied()
            .zip(solved.iter().cloned())
            .collect::<BTreeMap<_, _>>();
        let content_after = order
            .iter()
            .map(|node| {
                (
                    *node,
                    &self.complex.nodes[node].capacity * &potential_after[node],
                )
            })
            .collect::<BTreeMap<_, _>>();

        let currents = self
            .complex
            .branches
            .values()
            .map(|branch| {
                let current = &branch.conductance
                    * (&potential_after[&branch.source] - &potential_after[&branch.target]);
                DiffusionCurrent {
                    branch: branch.branch,
                    source: branch.source,
                    target: branch.target,
                    transferred: &event.interval * &current,
                    current,
                }
            })
            .collect::<Vec<_>>();

        let mut balances = Vec::with_capacity(extent);
        for node in order {
            let boundary_transfer = currents.iter().fold(Rat::zero(), |sum, branch| {
                if branch.target == *node {
                    sum + &branch.transferred
                } else if branch.source == *node {
                    sum - &branch.transferred
                } else {
                    sum
                }
            });
            let source = event.source.get(node).cloned().unwrap_or_else(Rat::zero);
            let exact_residual =
                &content_after[node] - &standing.content[node] - &source - &boundary_transfer;
            if !exact_residual.is_zero() {
                return Err(DiffusionError::BalanceFailure(*node));
            }
            balances.push(DiffusionNodeBalance {
                node: *node,
                content_before: standing.content[node].clone(),
                source,
                boundary_transfer,
                content_after: content_after[node].clone(),
                exact_residual,
            });
        }

        let total_before = sum_values(standing.content.values());
        let total_source = sum_values(event.source.values());
        let total_after = sum_values(content_after.values());
        let conservation_residual = &total_after - &total_before - &total_source;
        if !conservation_residual.is_zero() {
            return Err(DiffusionError::ConservationFailure);
        }
        let stored_energy_before = stored_energy(&self.complex, &potential_before);
        let stored_energy_after = stored_energy(&self.complex, &potential_after);
        let energy_departed = &stored_energy_before - &stored_energy_after;
        if event.source.values().all(Zero::is_zero) && energy_departed.is_negative() {
            return Err(DiffusionError::EnergyIncreased);
        }

        Ok((
            DiffusionStanding {
                schema: standing.schema.clone(),
                content: content_after,
            },
            DiffusionReceipt {
                schema: "holonic-engine.diffusion-receipt.v1".to_owned(),
                interval: event.interval.clone(),
                potential_before,
                potential_after,
                currents,
                balances,
                total_before,
                total_source,
                total_after,
                conservation_residual,
                stored_energy_before,
                stored_energy_after,
                energy_departed,
                transfer: DiffusionBoundaryTransferReceipt {
                    reused_factorization,
                    certificate: transfer.certificate,
                },
            },
        ))
    }
}

fn compile_diffusion_transfer(
    complex: &DiffusionComplex,
    interval: &Rat,
    boundary: &[CurrentNodeId],
) -> Result<CertifiedDiffusionTransfer, DiffusionError> {
    let node_order = complex.nodes.keys().copied().collect::<Vec<_>>();
    let ordinals = node_order
        .iter()
        .enumerate()
        .map(|(ordinal, node)| (*node, ordinal))
        .collect::<BTreeMap<_, _>>();
    let boundary_nodes = boundary.iter().copied().collect::<BTreeSet<_>>();
    let boundary_ordinals = boundary
        .iter()
        .map(|node| ordinals[node])
        .collect::<Vec<_>>();
    let interior_ordinals = node_order
        .iter()
        .enumerate()
        .filter_map(|(ordinal, node)| (!boundary_nodes.contains(node)).then_some(ordinal))
        .collect::<Vec<_>>();
    let interior = interior_ordinals
        .iter()
        .map(|ordinal| node_order[*ordinal])
        .collect::<Vec<_>>();

    let extent = node_order.len();
    let mut operator = vec![vec![Rat::zero(); extent]; extent];
    for (ordinal, node) in node_order.iter().enumerate() {
        operator[ordinal][ordinal] = complex.nodes[node].capacity.clone();
    }
    for branch in complex.branches.values() {
        let source = ordinals[&branch.source];
        let target = ordinals[&branch.target];
        let coupling = interval * &branch.conductance;
        operator[source][source] += &coupling;
        operator[target][target] += &coupling;
        operator[source][target] -= &coupling;
        operator[target][source] -= &coupling;
    }

    let boundary_boundary = matrix_section(&operator, &boundary_ordinals, &boundary_ordinals);
    let boundary_interior = matrix_section(&operator, &boundary_ordinals, &interior_ordinals);
    let interior_boundary = matrix_section(&operator, &interior_ordinals, &boundary_ordinals);
    let interior_interior = matrix_section(&operator, &interior_ordinals, &interior_ordinals);
    let interior_inverse = invert_exact(interior_interior.clone())?;
    let schur_correction = if interior_ordinals.is_empty() {
        vec![vec![Rat::zero(); boundary_ordinals.len()]; boundary_ordinals.len()]
    } else {
        matrix_multiply(
            &matrix_multiply(&boundary_interior, &interior_inverse)?,
            &interior_boundary,
        )?
    };
    let schur_boundary_operator = matrix_subtract(&boundary_boundary, &schur_correction)?;
    let boundary_inverse = invert_exact(schur_boundary_operator.clone())?;
    let interior_inverse_residual = matrix_subtract(
        &matrix_multiply(&interior_inverse, &interior_interior)?,
        &identity_matrix(interior_ordinals.len())?,
    )?;
    let boundary_inverse_residual = matrix_subtract(
        &matrix_multiply(&boundary_inverse, &schur_boundary_operator)?,
        &identity_matrix(boundary_ordinals.len())?,
    )?;
    if interior_inverse_residual
        .iter()
        .flatten()
        .chain(boundary_inverse_residual.iter().flatten())
        .any(|value| !value.is_zero())
    {
        return Err(DiffusionError::TransferCertificateFailure);
    }

    Ok(CertifiedDiffusionTransfer {
        certificate: DiffusionBoundaryTransferCertificate {
            schema: "holonic-engine.diffusion-boundary-transfer.v1".to_owned(),
            interval: interval.clone(),
            boundary: boundary.to_vec(),
            interior,
            node_order,
            capacities: complex
                .nodes
                .values()
                .map(|node| (node.node, node.capacity.clone()))
                .collect(),
            oriented_branches: complex
                .branches
                .values()
                .map(|branch| {
                    (
                        branch.branch,
                        branch.source,
                        branch.target,
                        branch.conductance.clone(),
                    )
                })
                .collect(),
            operator,
            interior_inverse,
            schur_boundary_operator,
            boundary_inverse,
            interior_inverse_residual,
            boundary_inverse_residual,
        },
        boundary_ordinals,
        interior_ordinals,
        boundary_interior,
        interior_boundary,
    })
}

fn solve_with_transfer(
    transfer: &CertifiedDiffusionTransfer,
    right: &[Rat],
) -> Result<Vec<Rat>, DiffusionError> {
    if right.len() != transfer.certificate.node_order.len() {
        return Err(DiffusionError::TransferPopulationMismatch);
    }
    let boundary_right = transfer
        .boundary_ordinals
        .iter()
        .map(|ordinal| right[*ordinal].clone())
        .collect::<Vec<_>>();
    let interior_right = transfer
        .interior_ordinals
        .iter()
        .map(|ordinal| right[*ordinal].clone())
        .collect::<Vec<_>>();
    let interior_free = matrix_vector(&transfer.certificate.interior_inverse, &interior_right)?;
    let reduced_boundary = vector_subtract(
        &boundary_right,
        &matrix_vector(&transfer.boundary_interior, &interior_free)?,
    );
    let boundary_potential =
        matrix_vector(&transfer.certificate.boundary_inverse, &reduced_boundary)?;
    let interior_potential = vector_subtract(
        &interior_free,
        &matrix_vector(
            &transfer.certificate.interior_inverse,
            &matrix_vector(&transfer.interior_boundary, &boundary_potential)?,
        )?,
    );
    let mut solved = vec![Rat::zero(); right.len()];
    for (ordinal, value) in transfer.boundary_ordinals.iter().zip(boundary_potential) {
        solved[*ordinal] = value;
    }
    for (ordinal, value) in transfer.interior_ordinals.iter().zip(interior_potential) {
        solved[*ordinal] = value;
    }
    Ok(solved)
}

fn matrix_section(matrix: &[Vec<Rat>], rows: &[usize], columns: &[usize]) -> Vec<Vec<Rat>> {
    rows.iter()
        .map(|row| {
            columns
                .iter()
                .map(|column| matrix[*row][*column].clone())
                .collect()
        })
        .collect()
}

/// Every shape refusal the shared carrier raises, named in this law's own vocabulary.
///
/// The error type does not cross the boundary: a caller of this module never sees an
/// `ExactLinearError`. `SingularMatrix` is the one refusal the declared material can cause —
/// a diffusion operator with a dependent row — and it lands on the variant that already meant
/// exactly that.
impl From<ExactLinearError> for DiffusionError {
    fn from(error: ExactLinearError) -> Self {
        match error {
            ExactLinearError::SingularMatrix => DiffusionError::SingularLaw,
            ExactLinearError::InverseCertificateFailure => {
                DiffusionError::TransferCertificateFailure
            }
            ExactLinearError::RaggedMatrix
            | ExactLinearError::AddressOutside
            | ExactLinearError::ExtentOverflow
            | ExactLinearError::ShapeMismatch
            | ExactLinearError::NonsquareMatrix => DiffusionError::MalformedOperator,
        }
    }
}

/// Present dense rows to the shared carrier against a **declared** column count.
///
/// The column count is declared rather than inferred because a boundary transfer reaches
/// genuinely empty populations — the default law puts every node on the boundary, so the
/// interior is empty and `interior_boundary` is a lawful `0 x |boundary|` operator whose rows
/// carry no column count at all. Inferring there would turn a lawful empty product into a
/// refusal.
fn carrier(matrix: &[Vec<Rat>], columns: usize) -> Result<ExactRatMatrix, DiffusionError> {
    Ok(ExactRatMatrix::shaped(
        matrix.len(),
        columns,
        matrix.to_vec(),
    )?)
}

fn identity_matrix(extent: usize) -> Result<Vec<Vec<Rat>>, DiffusionError> {
    Ok(ExactRatMatrix::identity(extent)?.to_rows())
}

/// The exact inverse, **with the shared carrier's multiplication certificate in force**.
///
/// Before 2026-08-15 this ran a full forward solve per column — `O(n^4)` — and left the
/// verification to its caller. The rationals are the same; the cost is one elimination rather
/// than `n`, and the identity check now happens before the value is returned rather than after.
fn invert_exact(matrix: Vec<Vec<Rat>>) -> Result<Vec<Vec<Rat>>, DiffusionError> {
    let extent = matrix.len();
    Ok(carrier(&matrix, extent)?.inverse()?.to_rows())
}

fn matrix_multiply(left: &[Vec<Rat>], right: &[Vec<Rat>]) -> Result<Vec<Vec<Rat>>, DiffusionError> {
    // The inner dimension is the right operand's row count, which is carried even when the left
    // operand has no rows to read it off.
    let inner = right.len();
    let columns = right.first().map_or(0, Vec::len);
    Ok(carrier(left, inner)?
        .multiply(&carrier(right, columns)?)?
        .to_rows())
}

fn matrix_vector(matrix: &[Vec<Rat>], vector: &[Rat]) -> Result<Vec<Rat>, DiffusionError> {
    Ok(carrier(matrix, vector.len())?.apply(vector)?)
}

fn matrix_subtract(left: &[Vec<Rat>], right: &[Vec<Rat>]) -> Result<Vec<Vec<Rat>>, DiffusionError> {
    let columns = left.first().or_else(|| right.first()).map_or(0, Vec::len);
    Ok(carrier(left, columns)?
        .subtract(&carrier(right, columns)?)?
        .to_rows())
}

fn vector_subtract(left: &[Rat], right: &[Rat]) -> Vec<Rat> {
    debug_assert_eq!(left.len(), right.len());
    left.iter()
        .zip(right)
        .map(|(left, right)| left - right)
        .collect()
}

fn validate_population(
    nodes: impl Iterator<Item = CurrentNodeId>,
    values: &BTreeMap<CurrentNodeId, Rat>,
) -> Result<(), DiffusionError> {
    let nodes = nodes.collect::<BTreeSet<_>>();
    let supplied = values.keys().copied().collect::<BTreeSet<_>>();
    if let Some(missing) = nodes.difference(&supplied).next() {
        return Err(DiffusionError::MissingContent(*missing));
    }
    if let Some(unknown) = supplied.difference(&nodes).next() {
        return Err(DiffusionError::MissingNode(*unknown));
    }
    Ok(())
}

/// This module's own forward elimination, retained **only** as the independent oracle the
/// Schur-complement path is cross-checked against.
///
/// It solved the inverse column by column until 2026-08-15. It no longer does, and that is what
/// keeps the cross-check in `tests` honest: the boundary-transfer path now runs through
/// `exact_linear`, so comparing it against this is comparing two implementations rather than one
/// implementation against itself.
#[cfg(test)]
fn solve_exact(mut matrix: Vec<Vec<Rat>>, mut right: Vec<Rat>) -> Result<Vec<Rat>, DiffusionError> {
    let extent = right.len();
    for column in 0..extent {
        let pivot = (column..extent)
            .find(|row| !matrix[*row][column].is_zero())
            .ok_or(DiffusionError::SingularLaw)?;
        if pivot != column {
            matrix.swap(pivot, column);
            right.swap(pivot, column);
        }
        let divisor = matrix[column][column].clone();
        for entry in &mut matrix[column][column..] {
            *entry /= &divisor;
        }
        right[column] /= divisor;
        let pivot_row = matrix[column].clone();
        let pivot_right = right[column].clone();
        for row in 0..extent {
            if row == column || matrix[row][column].is_zero() {
                continue;
            }
            let factor = matrix[row][column].clone();
            for (entry, pivot_entry) in matrix[row][column..].iter_mut().zip(&pivot_row[column..]) {
                let elimination = &factor * pivot_entry;
                *entry -= elimination;
            }
            let elimination = factor * &pivot_right;
            right[row] -= elimination;
        }
    }
    Ok(right)
}

fn sum_values<'a>(values: impl Iterator<Item = &'a Rat>) -> Rat {
    values.fold(Rat::zero(), |sum, value| sum + value)
}

fn stored_energy(complex: &DiffusionComplex, potential: &BTreeMap<CurrentNodeId, Rat>) -> Rat {
    let two = Rat::from_integer(2.into());
    complex.nodes.values().fold(Rat::zero(), |sum, node| {
        sum + &node.capacity * &potential[&node.node] * &potential[&node.node] / &two
    })
}

#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum DiffusionError {
    #[error("an exact diffusion complex requires at least one node")]
    EmptyComplex,
    #[error("diffusion node {0:?} was supplied more than once")]
    DuplicateNode(CurrentNodeId),
    #[error("diffusion branch {0:?} was supplied more than once")]
    DuplicateBranch(CurrentBranchId),
    #[error("a serialized diffusion complex does not reproduce its validated incidence")]
    MalformedComplex,
    #[error("node {0:?} is absent from the diffusion complex")]
    MissingNode(CurrentNodeId),
    #[error("node {0:?} has no standing content")]
    MissingContent(CurrentNodeId),
    #[error("node {0:?} requires a positive capacity magnitude")]
    NonpositiveCapacity(CurrentNodeId),
    #[error("branch {0:?} has identical endpoints")]
    DegenerateBranch(CurrentBranchId),
    #[error("branch {0:?} cannot carry a negative conductance magnitude")]
    NegativeConductance(CurrentBranchId),
    #[error("a completed diffusion event requires a positive exact interval")]
    NonpositiveInterval,
    #[error("the declared diffusion relation is singular")]
    SingularLaw,
    /// A shape refusal from the shared exact carrier, reported in this law's own vocabulary.
    ///
    /// Unreachable from the declared material: every operator this module hands the carrier is
    /// built by `matrix_section` over ordinal populations and is rectangular and square by
    /// construction. It is named rather than unwrapped because a caller must never receive a
    /// panic where a refusal is available, and because silently mapping a shape fault onto
    /// `SingularLaw` would report a property of the material that the material does not have.
    #[error("an exact diffusion operator did not compose in the shared exact carrier")]
    MalformedOperator,
    #[error("the exact diffusion boundary-transfer atlas was poisoned")]
    TransferAtlasPoisoned,
    #[error("an exact diffusion boundary-transfer certificate failed its inverse identity")]
    TransferCertificateFailure,
    #[error("a boundary transfer was applied to a different node population")]
    TransferPopulationMismatch,
    #[error("node {0:?} failed its exact completed-event balance")]
    BalanceFailure(CurrentNodeId),
    #[error("the closed diffusion complex failed exact total conservation")]
    ConservationFailure,
    #[error("a closed source-free diffusion event increased stored energy")]
    EnergyIncreased,
}

#[cfg(test)]
mod tests {
    use relational_geometry::integer;

    use super::*;

    #[test]
    fn two_node_diffusion_transports_and_conserves_exactly() {
        let left = CurrentNodeId(1);
        let right = CurrentNodeId(2);
        let complex = DiffusionComplex::new(
            [
                DiffusionNode {
                    node: left,
                    capacity: integer(1),
                },
                DiffusionNode {
                    node: right,
                    capacity: integer(1),
                },
            ],
            [DiffusionBranch {
                branch: CurrentBranchId(1),
                source: left,
                target: right,
                conductance: integer(1),
            }],
        )
        .unwrap();
        let law = ExactDiffusionLaw::new(complex).unwrap();
        let standing = law
            .initial_standing(BTreeMap::from([(left, integer(1)), (right, integer(0))]))
            .unwrap();
        let (after, receipt) = law
            .enact(
                &standing,
                &DiffusionEvent {
                    interval: integer(1),
                    source: BTreeMap::new(),
                },
            )
            .unwrap();

        assert_eq!(after.content[&left], integer(2) / integer(3));
        assert_eq!(after.content[&right], integer(1) / integer(3));
        assert_eq!(receipt.currents[0].current, integer(1) / integer(3));
        assert_eq!(receipt.currents[0].transferred, integer(1) / integer(3));
        assert!(
            receipt
                .balances
                .iter()
                .all(|balance| balance.exact_residual.is_zero())
        );
        assert!(receipt.conservation_residual.is_zero());
        assert_eq!(receipt.stored_energy_before, integer(1) / integer(2));
        assert_eq!(receipt.stored_energy_after, integer(5) / integer(18));
        assert_eq!(receipt.energy_departed, integer(2) / integer(9));
    }

    #[test]
    fn current_sign_emerges_when_the_declared_branch_is_reoriented() {
        let left = CurrentNodeId(1);
        let right = CurrentNodeId(2);
        let complex = DiffusionComplex::new(
            [
                DiffusionNode {
                    node: left,
                    capacity: integer(1),
                },
                DiffusionNode {
                    node: right,
                    capacity: integer(1),
                },
            ],
            [DiffusionBranch {
                branch: CurrentBranchId(1),
                source: right,
                target: left,
                conductance: integer(1),
            }],
        )
        .unwrap();
        let law = ExactDiffusionLaw::new(complex).unwrap();
        let standing = law
            .initial_standing(BTreeMap::from([(left, integer(1)), (right, integer(0))]))
            .unwrap();
        let (_, receipt) = law
            .enact(
                &standing,
                &DiffusionEvent {
                    interval: integer(1),
                    source: BTreeMap::new(),
                },
            )
            .unwrap();

        assert_eq!(receipt.currents[0].current, -integer(1) / integer(3));
        assert_eq!(receipt.balances[0].content_after, integer(2) / integer(3));
    }

    #[test]
    fn certified_schur_transfer_matches_direct_solve_and_reuses_structure() {
        let left = CurrentNodeId(1);
        let middle = CurrentNodeId(2);
        let right = CurrentNodeId(3);
        let complex = DiffusionComplex::new(
            [
                DiffusionNode {
                    node: left,
                    capacity: integer(1),
                },
                DiffusionNode {
                    node: middle,
                    capacity: integer(2),
                },
                DiffusionNode {
                    node: right,
                    capacity: integer(3),
                },
            ],
            [
                DiffusionBranch {
                    branch: CurrentBranchId(1),
                    source: left,
                    target: middle,
                    conductance: integer(2),
                },
                DiffusionBranch {
                    branch: CurrentBranchId(2),
                    source: middle,
                    target: right,
                    conductance: integer(1),
                },
            ],
        )
        .unwrap();
        let law = ExactDiffusionLaw::with_boundary(complex, [left, right]).unwrap();
        let standing = law
            .initial_standing(BTreeMap::from([
                (left, integer(4)),
                (middle, integer(1)),
                (right, integer(0)),
            ]))
            .unwrap();
        let event = DiffusionEvent {
            interval: integer(1) / integer(2),
            source: BTreeMap::from([(middle, integer(1) / integer(3))]),
        };
        let (after, first) = law.enact(&standing, &event).unwrap();
        assert!(!first.transfer.reused_factorization);
        assert_eq!(law.transfer_cache_entries(), 1);
        assert_eq!(first.transfer.certificate.boundary, vec![left, right]);
        assert_eq!(first.transfer.certificate.interior, vec![middle]);
        assert!(
            first
                .transfer
                .certificate
                .interior_inverse_residual
                .iter()
                .flatten()
                .all(Zero::is_zero)
        );
        assert!(
            first
                .transfer
                .certificate
                .boundary_inverse_residual
                .iter()
                .flatten()
                .all(Zero::is_zero)
        );

        let right_hand = first
            .transfer
            .certificate
            .node_order
            .iter()
            .map(|node| {
                &standing.content[node] + event.source.get(node).cloned().unwrap_or_else(Rat::zero)
            })
            .collect::<Vec<_>>();
        let direct = solve_exact(first.transfer.certificate.operator.clone(), right_hand).unwrap();
        assert_eq!(
            first.potential_after,
            first
                .transfer
                .certificate
                .node_order
                .iter()
                .copied()
                .zip(direct)
                .collect()
        );

        let (_, second) = law
            .enact(
                &after,
                &DiffusionEvent {
                    interval: event.interval.clone(),
                    source: BTreeMap::from([(left, integer(-1) / integer(5))]),
                },
            )
            .unwrap();
        assert!(second.transfer.reused_factorization);
        assert_eq!(law.transfer_cache_entries(), 1);

        let _ = law
            .enact(
                &after,
                &DiffusionEvent {
                    interval: integer(2) / integer(3),
                    source: BTreeMap::new(),
                },
            )
            .unwrap();
        assert_eq!(law.transfer_cache_entries(), 2);
    }

    #[test]
    fn duplicate_diffusion_identities_are_refused_before_indexing() {
        let node = CurrentNodeId(1);
        assert_eq!(
            DiffusionComplex::new(
                [
                    DiffusionNode {
                        node,
                        capacity: integer(1),
                    },
                    DiffusionNode {
                        node,
                        capacity: integer(2),
                    },
                ],
                std::iter::empty::<DiffusionBranch>(),
            ),
            Err(DiffusionError::DuplicateNode(node))
        );
    }
}

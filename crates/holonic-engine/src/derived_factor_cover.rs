//! Exact support-indexed factor covers founded by returned defect sections.
//!
//! This owner closes the passage between ExactRatMatrix and the resident factorized contraction.
//! It does not train, score, cluster, or select a rank. A local defect carries its addressed
//! parent, receiver/history support, chart and two declared metrics. Exact pivot-column
//! factorization derives the atom population. Every atom retains an ablation address and exact
//! withdrawal, while every singular section retains its full zero-preimage fibre and open exterior.
//!
//! Pairwise overlap is not insertion order. Equal restrictions glue through the declared identity
//! chart. Disjoint supports receive interchange only when both complete matrix words agree.
//! Incompatible overlaps retain their cocycle, and noncommuting words retain both orientations and
//! their commutator as holonomy.

use std::collections::BTreeSet;

use num_traits::Zero;
use relational_geometry::Rat;
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use thiserror::Error;

use crate::exact_linear::{
    ExactLinearError, ExactRankFactorization, ExactRatMatrix, RebaseReceipt,
};
use crate::exact_work::ExactWork;

/// The nondegenerate receiver metrics declared at one local defect chart.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct DefectMetrics {
    pub domain: ExactRatMatrix,
    pub codomain: ExactRatMatrix,
}

/// One addressed defect section. Support ordinals are ambient chart addresses, not identities.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct SupportedDefectSection {
    pub address: String,
    pub parent_candidate: String,
    pub receiver: String,
    pub successor_word: Vec<String>,
    pub chart: String,
    pub ambient_rows: usize,
    pub ambient_columns: usize,
    pub support_rows: Vec<usize>,
    pub support_columns: Vec<usize>,
    pub supported: ExactRatMatrix,
    pub metrics: DefectMetrics,
}

/// The deterministic image-basis representative used by one factorization.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct PivotColumnGauge {
    pub local_columns: Vec<usize>,
    pub ambient_columns: Vec<usize>,
}

/// A targeted inverse deposit. Applying delta after its factor removes precisely that atom.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct WithdrawalStep {
    pub factor_address: String,
    pub delta: ExactRatMatrix,
}

/// One derived rank-one atom inside a local section.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct LocalFactorAtom {
    pub address: String,
    pub parent_defect: String,
    pub ordinal: usize,
    pub support_rows: Vec<usize>,
    pub support_columns: Vec<usize>,
    pub left: Vec<Rat>,
    pub right: Vec<Rat>,
    pub reconstruction: ExactRatMatrix,
    pub ablation_address: String,
    pub ablated_remainder: ExactRatMatrix,
    pub withdrawal: WithdrawalStep,
}

/// Rank zero is a returned no-change obstruction, not one zero-valued atom.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum FactorDisposition {
    NoChange,
    DerivedAtoms,
}

/// Complete local return: factorization, gauge, metric adjoint, fibres and exact atom population.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct LocalFactorReceipt {
    pub section: SupportedDefectSection,
    pub disposition: FactorDisposition,
    pub derived_rank: usize,
    pub gauge: PivotColumnGauge,
    pub factorization: ExactRankFactorization,
    pub metric_adjoint: ExactRatMatrix,
    /// ker(Delta), the complete zero-preimage affine fibre directions.
    pub radical_fibre: Vec<Vec<Rat>>,
    /// Covectors annihilating the image: consequence still outside this local passage.
    pub open_exterior: Vec<Vec<Rat>>,
    pub factors: Vec<LocalFactorAtom>,
    /// Reverse causal order, so exact withdrawal restores the immediate predecessor.
    pub withdrawal_word: Vec<WithdrawalStep>,
    pub reconstructed_defect: ExactRatMatrix,
    pub work: ExactWork,
}

/// Both restrictions over one nonempty overlap and their exact oriented difference.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct OverlapPatch {
    pub rows: Vec<usize>,
    pub columns: Vec<usize>,
    pub left: ExactRatMatrix,
    pub right: ExactRatMatrix,
    pub cocycle: ExactRatMatrix,
}

/// The returned relation between two local sections.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum OverlapKind {
    /// Equal restrictions form one higher compatibility cell.
    CompatibleGlue { glued: SupportedDefectSection },
    /// Disjoint support and both complete orders agree exactly.
    DisjointInterchange {
        right_after_left: ExactRatMatrix,
        left_after_right: ExactRatMatrix,
    },
    /// The overlap differs, but its two complete words commute. The cocycle remains retained.
    CommutingCocycle {
        right_after_left: ExactRatMatrix,
        left_after_right: ExactRatMatrix,
    },
    /// Order remains causal data. The commutator is the loop return/holonomy.
    PathOrderedHolonomy {
        right_after_left: ExactRatMatrix,
        left_after_right: ExactRatMatrix,
        commutator: ExactRatMatrix,
        forward_word: Vec<String>,
        reverse_word: Vec<String>,
    },
    /// A chart or shape did not found either gluing or composition.
    Open { reason: String },
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct OverlapReceipt {
    pub left: String,
    pub right: String,
    pub chart_transition: Option<String>,
    pub patch: Option<OverlapPatch>,
    pub kind: OverlapKind,
}

/// One exact local morphology cover. Its order is source order and therefore remains causal data.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct DerivedFactorCover {
    pub schema: String,
    pub locals: Vec<LocalFactorReceipt>,
    pub overlaps: Vec<OverlapReceipt>,
    pub factor_order: Vec<String>,
    pub withdrawal_word: Vec<WithdrawalStep>,
    pub exact_work: ExactWork,
}

impl DerivedFactorCover {
    pub fn derive(sections: Vec<SupportedDefectSection>) -> Result<Self, FactorCoverError> {
        let mut addresses = BTreeSet::new();
        let mut locals = Vec::with_capacity(sections.len());
        let mut exact_work = ExactWork::nothing();
        for section in sections {
            if !addresses.insert(section.address.clone()) {
                return Err(FactorCoverError::DuplicateAddress(section.address));
            }
            let local = section.derive()?;
            exact_work = exact_work.then(&local.work);
            locals.push(local);
        }
        let mut overlaps = Vec::new();
        for left in 0..locals.len() {
            for right in left + 1..locals.len() {
                overlaps.push(compare_sections(
                    &locals[left].section,
                    &locals[right].section,
                )?);
            }
        }
        let factor_order = locals
            .iter()
            .flat_map(|local| local.factors.iter().map(|factor| factor.address.clone()))
            .collect::<Vec<_>>();
        let withdrawal_word = locals
            .iter()
            .rev()
            .flat_map(|local| local.withdrawal_word.iter().cloned())
            .collect();
        Ok(Self {
            schema: "holonic-engine.derived-factor-cover.v1".to_owned(),
            locals,
            overlaps,
            factor_order,
            withdrawal_word,
            exact_work,
        })
    }
}

impl SupportedDefectSection {
    pub fn derive(self) -> Result<LocalFactorReceipt, FactorCoverError> {
        self.validate()?;
        let factorization = self.supported.rank_factorization()?;
        let metric_adjoint = self
            .supported
            .metric_adjoint(&self.metrics.domain, &self.metrics.codomain)?;
        let gauge = PivotColumnGauge {
            local_columns: factorization.pivot_columns.clone(),
            ambient_columns: factorization
                .pivot_columns
                .iter()
                .map(|column| self.support_columns[*column])
                .collect(),
        };
        let mut reconstructed =
            ExactRatMatrix::zero(self.supported.rows(), self.supported.columns())?;
        let mut factors = Vec::with_capacity(factorization.derived_rank);
        for ordinal in 0..factorization.derived_rank {
            let left = (0..factorization.left.rows())
                .map(|row| factorization.left.get(row, ordinal).cloned())
                .collect::<Result<Vec<_>, _>>()?;
            let right = factorization.right.row(ordinal)?.to_vec();
            let atom = ExactRatMatrix::new(
                left.iter()
                    .map(|left| right.iter().map(|right| left * right).collect())
                    .collect(),
            )?;
            reconstructed = reconstructed.add(&atom)?;
            let address = factor_address(&self, ordinal, &left, &right);
            let withdrawal_delta =
                ExactRatMatrix::zero(atom.rows(), atom.columns())?.subtract(&atom)?;
            factors.push(LocalFactorAtom {
                address: address.clone(),
                parent_defect: self.address.clone(),
                ordinal,
                support_rows: self.support_rows.clone(),
                support_columns: self.support_columns.clone(),
                left,
                right,
                reconstruction: atom.clone(),
                ablation_address: format!("{address}/ablation"),
                ablated_remainder: self.supported.subtract(&atom)?,
                withdrawal: WithdrawalStep {
                    factor_address: address,
                    delta: withdrawal_delta,
                },
            });
        }
        if reconstructed != self.supported || reconstructed != factorization.reconstruction {
            return Err(FactorCoverError::ReconstructionFailure(self.address));
        }
        let withdrawal_word = factors
            .iter()
            .rev()
            .map(|factor| factor.withdrawal.clone())
            .collect();
        Ok(LocalFactorReceipt {
            disposition: if factorization.derived_rank == 0 {
                FactorDisposition::NoChange
            } else {
                FactorDisposition::DerivedAtoms
            },
            derived_rank: factorization.derived_rank,
            gauge,
            metric_adjoint,
            radical_fibre: factorization.linear.kernel.clone(),
            open_exterior: factorization.linear.cokernel_annihilator.clone(),
            factors,
            withdrawal_word,
            reconstructed_defect: reconstructed,
            work: factorization.work.clone(),
            factorization,
            section: self,
        })
    }

    fn validate(&self) -> Result<(), FactorCoverError> {
        if self.address.is_empty()
            || self.parent_candidate.is_empty()
            || self.receiver.is_empty()
            || self.chart.is_empty()
        {
            return Err(FactorCoverError::UnaddressedSection);
        }
        if !valid_support(self.ambient_rows, &self.support_rows)
            || !valid_support(self.ambient_columns, &self.support_columns)
            || self.supported.rows() != self.support_rows.len()
            || self.supported.columns() != self.support_columns.len()
        {
            return Err(FactorCoverError::SupportShape(self.address.clone()));
        }
        if self.metrics.domain.rows() != self.supported.columns()
            || self.metrics.domain.columns() != self.supported.columns()
            || self.metrics.codomain.rows() != self.supported.rows()
            || self.metrics.codomain.columns() != self.supported.rows()
        {
            return Err(FactorCoverError::MetricShape(self.address.clone()));
        }
        for (name, metric) in [
            ("domain", &self.metrics.domain),
            ("codomain", &self.metrics.codomain),
        ] {
            if !matches!(metric.rebase_receipt()?, RebaseReceipt::Rebase { .. }) {
                return Err(FactorCoverError::DegenerateMetric {
                    section: self.address.clone(),
                    metric: name,
                });
            }
        }
        Ok(())
    }

    pub fn ambient_matrix(&self) -> Result<ExactRatMatrix, FactorCoverError> {
        let mut rows = vec![vec![Rat::zero(); self.ambient_columns]; self.ambient_rows];
        for (local_row, ambient_row) in self.support_rows.iter().enumerate() {
            for (local_column, ambient_column) in self.support_columns.iter().enumerate() {
                rows[*ambient_row][*ambient_column] =
                    self.supported.get(local_row, local_column)?.clone();
            }
        }
        Ok(ExactRatMatrix::shaped(
            self.ambient_rows,
            self.ambient_columns,
            rows,
        )?)
    }
}

fn compare_sections(
    left: &SupportedDefectSection,
    right: &SupportedDefectSection,
) -> Result<OverlapReceipt, FactorCoverError> {
    if left.chart != right.chart
        || left.ambient_rows != right.ambient_rows
        || left.ambient_columns != right.ambient_columns
    {
        return Ok(OverlapReceipt {
            left: left.address.clone(),
            right: right.address.clone(),
            chart_transition: None,
            patch: None,
            kind: OverlapKind::Open {
                reason: "no declared chart transition carries both local sections".to_owned(),
            },
        });
    }
    let chart_transition = Some(format!("identity:{}", left.chart));
    let overlap_rows = intersection(&left.support_rows, &right.support_rows);
    let overlap_columns = intersection(&left.support_columns, &right.support_columns);
    let disjoint = overlap_rows.is_empty() || overlap_columns.is_empty();
    let patch = if disjoint {
        None
    } else {
        let left_restriction = restrict(left, &overlap_rows, &overlap_columns)?;
        let right_restriction = restrict(right, &overlap_rows, &overlap_columns)?;
        Some(OverlapPatch {
            rows: overlap_rows,
            columns: overlap_columns,
            cocycle: left_restriction.subtract(&right_restriction)?,
            left: left_restriction,
            right: right_restriction,
        })
    };
    if patch
        .as_ref()
        .is_some_and(|patch| patch.cocycle.entries().iter().all(Rat::is_zero))
    {
        return Ok(OverlapReceipt {
            left: left.address.clone(),
            right: right.address.clone(),
            chart_transition,
            patch,
            kind: OverlapKind::CompatibleGlue {
                glued: glue(left, right)?,
            },
        });
    }
    if left.ambient_rows != left.ambient_columns {
        return Ok(OverlapReceipt {
            left: left.address.clone(),
            right: right.address.clone(),
            chart_transition,
            patch,
            kind: OverlapKind::Open {
                reason: "the common chart is rectangular, so no endomorphism word was declared"
                    .to_owned(),
            },
        });
    }
    let left_map = left.ambient_matrix()?;
    let right_map = right.ambient_matrix()?;
    let right_after_left = right_map.multiply(&left_map)?;
    let left_after_right = left_map.multiply(&right_map)?;
    let kind = if right_after_left == left_after_right {
        if disjoint {
            OverlapKind::DisjointInterchange {
                right_after_left,
                left_after_right,
            }
        } else {
            OverlapKind::CommutingCocycle {
                right_after_left,
                left_after_right,
            }
        }
    } else {
        OverlapKind::PathOrderedHolonomy {
            commutator: right_after_left.subtract(&left_after_right)?,
            right_after_left,
            left_after_right,
            forward_word: vec![left.address.clone(), right.address.clone()],
            reverse_word: vec![right.address.clone(), left.address.clone()],
        }
    };
    Ok(OverlapReceipt {
        left: left.address.clone(),
        right: right.address.clone(),
        chart_transition,
        patch,
        kind,
    })
}

fn restrict(
    section: &SupportedDefectSection,
    rows: &[usize],
    columns: &[usize],
) -> Result<ExactRatMatrix, FactorCoverError> {
    ExactRatMatrix::new(
        rows.iter()
            .map(|row| {
                let local_row = section
                    .support_rows
                    .binary_search(row)
                    .map_err(|_| FactorCoverError::SupportShape(section.address.clone()))?;
                columns
                    .iter()
                    .map(|column| {
                        let local_column = section
                            .support_columns
                            .binary_search(column)
                            .map_err(|_| FactorCoverError::SupportShape(section.address.clone()))?;
                        Ok(section.supported.get(local_row, local_column)?.clone())
                    })
                    .collect::<Result<Vec<_>, FactorCoverError>>()
            })
            .collect::<Result<Vec<_>, FactorCoverError>>()?,
    )
    .map_err(Into::into)
}

fn glue(
    left: &SupportedDefectSection,
    right: &SupportedDefectSection,
) -> Result<SupportedDefectSection, FactorCoverError> {
    let support_rows = union(&left.support_rows, &right.support_rows);
    let support_columns = union(&left.support_columns, &right.support_columns);
    let domain_metric = glue_metric(
        left,
        &left.metrics.domain,
        &left.support_columns,
        right,
        &right.metrics.domain,
        &right.support_columns,
        &support_columns,
    )?;
    let codomain_metric = glue_metric(
        left,
        &left.metrics.codomain,
        &left.support_rows,
        right,
        &right.metrics.codomain,
        &right.support_rows,
        &support_rows,
    )?;
    let mut values = vec![vec![Rat::zero(); support_columns.len()]; support_rows.len()];
    let mut present = vec![vec![false; support_columns.len()]; support_rows.len()];
    for section in [left, right] {
        for (local_row, ambient_row) in section.support_rows.iter().enumerate() {
            let row = support_rows
                .binary_search(ambient_row)
                .expect("union contains row");
            for (local_column, ambient_column) in section.support_columns.iter().enumerate() {
                let column = support_columns
                    .binary_search(ambient_column)
                    .expect("union contains column");
                let value = section.supported.get(local_row, local_column)?.clone();
                if present[row][column] && values[row][column] != value {
                    return Err(FactorCoverError::IncompatibleGlue {
                        left: left.address.clone(),
                        right: right.address.clone(),
                    });
                }
                values[row][column] = value;
                present[row][column] = true;
            }
        }
    }
    Ok(SupportedDefectSection {
        address: format!("glue:{}+{}", left.address, right.address),
        parent_candidate: format!("{}+{}", left.parent_candidate, right.parent_candidate),
        receiver: format!("{}+{}", left.receiver, right.receiver),
        successor_word: left
            .successor_word
            .iter()
            .chain(&right.successor_word)
            .cloned()
            .collect(),
        chart: left.chart.clone(),
        ambient_rows: left.ambient_rows,
        ambient_columns: left.ambient_columns,
        support_rows,
        support_columns,
        supported: ExactRatMatrix::new(values)?,
        metrics: DefectMetrics {
            domain: domain_metric,
            codomain: codomain_metric,
        },
    })
}

fn glue_metric(
    left_section: &SupportedDefectSection,
    left: &ExactRatMatrix,
    left_support: &[usize],
    right_section: &SupportedDefectSection,
    right: &ExactRatMatrix,
    right_support: &[usize],
    union_support: &[usize],
) -> Result<ExactRatMatrix, FactorCoverError> {
    let mut values = vec![vec![Rat::zero(); union_support.len()]; union_support.len()];
    let mut present = vec![vec![false; union_support.len()]; union_support.len()];
    for (metric, support) in [(left, left_support), (right, right_support)] {
        for (local_row, ambient_row) in support.iter().enumerate() {
            let row = union_support
                .binary_search(ambient_row)
                .expect("union contains metric row");
            for (local_column, ambient_column) in support.iter().enumerate() {
                let column = union_support
                    .binary_search(ambient_column)
                    .expect("union contains metric column");
                let value = metric.get(local_row, local_column)?.clone();
                if present[row][column] && values[row][column] != value {
                    return Err(FactorCoverError::MetricTransitionAbsent {
                        left: left_section.address.clone(),
                        right: right_section.address.clone(),
                    });
                }
                values[row][column] = value;
                present[row][column] = true;
            }
        }
    }
    Ok(ExactRatMatrix::new(values)?)
}

fn factor_address(
    section: &SupportedDefectSection,
    ordinal: usize,
    left: &[Rat],
    right: &[Rat],
) -> String {
    let mut bytes = Vec::new();
    frame(&mut bytes, b"holonic-engine.local-factor-address.v1");
    frame(&mut bytes, section.address.as_bytes());
    bytes.extend_from_slice(&(ordinal as u64).to_le_bytes());
    for population in [left, right] {
        bytes.extend_from_slice(&(population.len() as u64).to_le_bytes());
        for value in population {
            frame(&mut bytes, value.to_string().as_bytes());
        }
    }
    format!("factor:{:x}", Sha256::digest(bytes))
}

fn frame(bytes: &mut Vec<u8>, value: &[u8]) {
    bytes.extend_from_slice(&(value.len() as u64).to_le_bytes());
    bytes.extend_from_slice(value);
}

fn valid_support(ambient: usize, support: &[usize]) -> bool {
    support.iter().all(|index| *index < ambient) && support.windows(2).all(|pair| pair[0] < pair[1])
}

fn intersection(left: &[usize], right: &[usize]) -> Vec<usize> {
    left.iter()
        .filter(|value| right.binary_search(value).is_ok())
        .copied()
        .collect()
}

fn union(left: &[usize], right: &[usize]) -> Vec<usize> {
    left.iter()
        .chain(right)
        .copied()
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect()
}

#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum FactorCoverError {
    #[error("a local defect section lacks addressed parent/receiver/chart lineage")]
    UnaddressedSection,
    #[error("duplicate local defect address {0}")]
    DuplicateAddress(String),
    #[error("local defect {0} has an invalid support chart")]
    SupportShape(String),
    #[error("local defect {0} has a metric of the wrong shape")]
    MetricShape(String),
    #[error("local defect {section} has a degenerate {metric} metric")]
    DegenerateMetric {
        section: String,
        metric: &'static str,
    },
    #[error("local defect {0} did not reconstruct from its exact atom population")]
    ReconstructionFailure(String),
    #[error("sections {left} and {right} disagree on a claimed compatible overlap")]
    IncompatibleGlue { left: String, right: String },
    #[error("sections {left} and {right} have no declared metric transition for their glue")]
    MetricTransitionAbsent { left: String, right: String },
    #[error(transparent)]
    ExactLinear(#[from] ExactLinearError),
}

#[cfg(test)]
mod tests;

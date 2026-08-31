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

/// Both receiver-constitutive restrictions on a shared support.
///
/// Equal transport coordinates do not imply equal physical response.  When the section cocycle
/// vanishes but either pulled metric differs, the overlap retains this constitutive cocycle rather
/// than forcing a false glue or returning an untyped metric error.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ConstitutiveOverlapPatch {
    pub left_domain: ExactRatMatrix,
    pub right_domain: ExactRatMatrix,
    pub domain_cocycle: ExactRatMatrix,
    pub left_codomain: ExactRatMatrix,
    pub right_codomain: ExactRatMatrix,
    pub codomain_cocycle: ExactRatMatrix,
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
    /// The transported section agrees but the receiver constitutive forms differ on the overlap.
    /// Both restrictions and their oriented difference remain available to the later return.
    ConstitutiveCocycle {
        constitutive: ConstitutiveOverlapPatch,
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

/// An exact family receipt for pairwise-independent local sections.
///
/// Listing every pair in a disjoint cover is an exterior quadratic expansion of one support law.
/// This receipt retains the complete member population and the proof-bearing coordinate axis on
/// which supports are pairwise disjoint.  The pair population is derived, never caller supplied.
/// Addition of the corresponding local deltas is therefore an exact interchange law even when the
/// common ambient chart is rectangular and endomorphism composition is not defined.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CompactInterchangeFamilyReceipt {
    pub chart: String,
    pub ambient_rows: usize,
    pub ambient_columns: usize,
    pub members: Vec<String>,
    pub disjoint_support_axis: String,
    pub pair_population: u64,
    pub interchange_law: String,
}

/// One exact local morphology cover. Its order is source order and therefore remains causal data.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct DerivedFactorCover {
    pub schema: String,
    pub locals: Vec<LocalFactorReceipt>,
    pub overlaps: Vec<OverlapReceipt>,
    pub compact_interchange_families: Vec<CompactInterchangeFamilyReceipt>,
    pub complete_pair_population: u64,
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
        let complete_pair_population = pair_population(locals.len())?;
        let mut overlaps = Vec::new();
        let mut compact_interchange_families = Vec::new();
        if let Some(family) = compact_column_interchange_family(&locals)? {
            compact_interchange_families.push(family);
        } else {
            for left in 0..locals.len() {
                for right in left + 1..locals.len() {
                    overlaps.push(compare_sections(
                        &locals[left].section,
                        &locals[right].section,
                    )?);
                }
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
        let cover = Self {
            schema: "holonic-engine.derived-factor-cover.v3".to_owned(),
            locals,
            overlaps,
            compact_interchange_families,
            complete_pair_population,
            factor_order,
            withdrawal_word,
            exact_work,
        };
        cover.validate()?;
        Ok(cover)
    }

    /// Reopen the complete cover from its local receipts and compact pair-family testimony.
    pub fn validate(&self) -> Result<(), FactorCoverError> {
        if self.schema != "holonic-engine.derived-factor-cover.v3" {
            return Err(FactorCoverError::CoverSchema(self.schema.clone()));
        }
        let expected_pairs = pair_population(self.locals.len())?;
        if self.complete_pair_population != expected_pairs {
            return Err(FactorCoverError::PairPopulation);
        }
        let mut reconstructed_work = ExactWork::nothing();
        for local in &self.locals {
            let reconstructed = local.section.clone().derive()?;
            if reconstructed != *local {
                return Err(FactorCoverError::LocalReceipt(
                    local.section.address.clone(),
                ));
            }
            reconstructed_work = reconstructed_work.then(&local.work);
        }
        if reconstructed_work != self.exact_work {
            return Err(FactorCoverError::CoverWork);
        }
        let local_addresses = self
            .locals
            .iter()
            .map(|local| local.section.address.as_str())
            .collect::<BTreeSet<_>>();
        if local_addresses.len() != self.locals.len() {
            return Err(FactorCoverError::PairPopulation);
        }
        let factor_order = self
            .locals
            .iter()
            .flat_map(|local| local.factors.iter().map(|factor| factor.address.clone()))
            .collect::<Vec<_>>();
        let withdrawal_word = self
            .locals
            .iter()
            .rev()
            .flat_map(|local| local.withdrawal_word.iter().cloned())
            .collect::<Vec<_>>();
        if self.factor_order != factor_order || self.withdrawal_word != withdrawal_word {
            return Err(FactorCoverError::CoverOrder);
        }
        let compact_pairs =
            self.compact_interchange_families
                .iter()
                .try_fold(0_u64, |sum, family| {
                    validate_compact_family(family, &self.locals)?;
                    sum.checked_add(family.pair_population)
                        .ok_or(FactorCoverError::PairPopulation)
                })?;
        let explicit_pairs =
            u64::try_from(self.overlaps.len()).map_err(|_| FactorCoverError::PairPopulation)?;
        if explicit_pairs
            .checked_add(compact_pairs)
            .ok_or(FactorCoverError::PairPopulation)?
            != expected_pairs
        {
            return Err(FactorCoverError::PairPopulation);
        }
        Ok(())
    }
}

fn compact_column_interchange_family(
    locals: &[LocalFactorReceipt],
) -> Result<Option<CompactInterchangeFamilyReceipt>, FactorCoverError> {
    if locals.len() < 2 {
        return Ok(None);
    }
    let first = &locals[0].section;
    if locals.iter().any(|local| {
        local.section.chart != first.chart
            || local.section.ambient_rows != first.ambient_rows
            || local.section.ambient_columns != first.ambient_columns
    }) {
        return Ok(None);
    }
    let mut occupied = BTreeSet::new();
    for local in locals {
        for column in &local.section.support_columns {
            if !occupied.insert(*column) {
                return Ok(None);
            }
        }
    }
    Ok(Some(CompactInterchangeFamilyReceipt {
        chart: first.chart.clone(),
        ambient_rows: first.ambient_rows,
        ambient_columns: first.ambient_columns,
        members: locals
            .iter()
            .map(|local| local.section.address.clone())
            .collect(),
        disjoint_support_axis: "columns".to_owned(),
        pair_population: pair_population(locals.len())?,
        interchange_law: "additive-local-delta-interchange".to_owned(),
    }))
}

fn validate_compact_family(
    family: &CompactInterchangeFamilyReceipt,
    locals: &[LocalFactorReceipt],
) -> Result<(), FactorCoverError> {
    if family.disjoint_support_axis != "columns"
        || family.interchange_law != "additive-local-delta-interchange"
        || family.members.len() < 2
        || family.pair_population != pair_population(family.members.len())?
    {
        return Err(FactorCoverError::CompactInterchange);
    }
    let by_address = locals
        .iter()
        .map(|local| (local.section.address.as_str(), &local.section))
        .collect::<std::collections::BTreeMap<_, _>>();
    let mut members = BTreeSet::new();
    let mut occupied = BTreeSet::new();
    for address in &family.members {
        let section = by_address
            .get(address.as_str())
            .ok_or(FactorCoverError::CompactInterchange)?;
        if !members.insert(address.as_str())
            || section.chart != family.chart
            || section.ambient_rows != family.ambient_rows
            || section.ambient_columns != family.ambient_columns
            || section
                .support_columns
                .iter()
                .any(|column| !occupied.insert(*column))
        {
            return Err(FactorCoverError::CompactInterchange);
        }
    }
    Ok(())
}

fn pair_population(population: usize) -> Result<u64, FactorCoverError> {
    let population = u64::try_from(population).map_err(|_| FactorCoverError::PairPopulation)?;
    population
        .checked_mul(population.saturating_sub(1))
        .and_then(|value| value.checked_div(2))
        .ok_or(FactorCoverError::PairPopulation)
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
            rows: overlap_rows.clone(),
            columns: overlap_columns.clone(),
            cocycle: left_restriction.subtract(&right_restriction)?,
            left: left_restriction,
            right: right_restriction,
        })
    };
    if patch
        .as_ref()
        .is_some_and(|patch| patch.cocycle.entries().iter().all(Rat::is_zero))
    {
        let constitutive = constitutive_overlap(left, right, &overlap_rows, &overlap_columns)?;
        let constitutive_agrees = constitutive
            .domain_cocycle
            .entries()
            .iter()
            .chain(constitutive.codomain_cocycle.entries())
            .all(Rat::is_zero);
        return Ok(OverlapReceipt {
            left: left.address.clone(),
            right: right.address.clone(),
            chart_transition,
            patch,
            kind: if constitutive_agrees {
                OverlapKind::CompatibleGlue {
                    glued: glue(left, right)?,
                }
            } else {
                OverlapKind::ConstitutiveCocycle { constitutive }
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

fn constitutive_overlap(
    left: &SupportedDefectSection,
    right: &SupportedDefectSection,
    rows: &[usize],
    columns: &[usize],
) -> Result<ConstitutiveOverlapPatch, FactorCoverError> {
    let left_domain = restrict_metric(
        &left.metrics.domain,
        &left.support_columns,
        columns,
        &left.address,
    )?;
    let right_domain = restrict_metric(
        &right.metrics.domain,
        &right.support_columns,
        columns,
        &right.address,
    )?;
    let left_codomain = restrict_metric(
        &left.metrics.codomain,
        &left.support_rows,
        rows,
        &left.address,
    )?;
    let right_codomain = restrict_metric(
        &right.metrics.codomain,
        &right.support_rows,
        rows,
        &right.address,
    )?;
    Ok(ConstitutiveOverlapPatch {
        domain_cocycle: left_domain.subtract(&right_domain)?,
        codomain_cocycle: left_codomain.subtract(&right_codomain)?,
        left_domain,
        right_domain,
        left_codomain,
        right_codomain,
    })
}

fn restrict_metric(
    metric: &ExactRatMatrix,
    local_support: &[usize],
    overlap_support: &[usize],
    address: &str,
) -> Result<ExactRatMatrix, FactorCoverError> {
    ExactRatMatrix::new(
        overlap_support
            .iter()
            .map(|ambient_row| {
                let local_row = local_support
                    .binary_search(ambient_row)
                    .map_err(|_| FactorCoverError::SupportShape(address.to_owned()))?;
                overlap_support
                    .iter()
                    .map(|ambient_column| {
                        let local_column = local_support
                            .binary_search(ambient_column)
                            .map_err(|_| FactorCoverError::SupportShape(address.to_owned()))?;
                        Ok(metric.get(local_row, local_column)?.clone())
                    })
                    .collect::<Result<Vec<_>, FactorCoverError>>()
            })
            .collect::<Result<Vec<_>, FactorCoverError>>()?,
    )
    .map_err(Into::into)
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
    #[error("derived factor cover has unknown schema {0}")]
    CoverSchema(String),
    #[error("derived factor cover has an incomplete or overflowing pair population")]
    PairPopulation,
    #[error("derived factor cover does not retain its causal factor/withdrawal order")]
    CoverOrder,
    #[error("local factor receipt {0} does not reconstruct from its supported defect")]
    LocalReceipt(String),
    #[error("derived factor cover has incorrect exact-work testimony")]
    CoverWork,
    #[error("compact interchange testimony does not reconstruct from pairwise-disjoint support")]
    CompactInterchange,
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

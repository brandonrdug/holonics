//! Same-body deposition of returned factor covers into the Phoenix projection morphology.
//!
//! The categorical cover remains complete.  A realization only states which of its addressed
//! atoms have a founded vocabulary/hidden chart; every other atom stays in the open fibre.  The
//! effective resident map is reconstructed from the inherited factor plus the active ordered
//! realization prefix, then rank-factorized exactly.  Consequently the CUDA junction extent is
//! the image cardinality of the contemporary map and never a caller capacity.

use std::collections::{BTreeMap, BTreeSet};

use num_bigint::{BigInt, BigUint};
use num_traits::{One, ToPrimitive, Zero};
use relational_geometry::Rat;
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use thiserror::Error;

use crate::{
    cultivated_rest::{AlignedFactor, MorphologyPayload},
    derived_factor_cover::{DerivedFactorCover, LocalFactorReceipt},
    embedding_fiber::{AlignedMaterial, ResidentReadout},
    exact_linear::{ExactLinearError, ExactRatMatrix},
    resident_section::{Dyadic, ResidentGrain, ResidentSurface, TransferCensus},
};

use super::streamed::cultivation_overlay::{
    DerivedRankDerivationReceipt, FactorDerivationReceipt, SeparatingReceiver, SparseDefect,
};

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct TowerFactorRealization {
    pub address: String,
    pub source_factor_addresses: Vec<String>,
    pub target_row: u32,
    pub selector_coordinate: u32,
    pub delta_entry: i64,
    pub selector_entry: i64,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct SessionFactorComplexIdentity {
    pub cover_sha256: String,
    pub predecessor_factor_sha256: String,
    pub active_prefix: usize,
    pub realization_population: usize,
    pub ablated_realizations: Vec<String>,
    pub derived_rank: usize,
    pub current_factor_sha256: String,
    pub complete_sha256: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct FactorMutationReceipt {
    pub predecessor_sha256: String,
    pub successor_sha256: String,
    pub active_prefix: usize,
    pub ablated_realizations: Vec<String>,
    pub derived_rank: usize,
    pub exact_withdrawal: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct ResidentFactorCurrentReturn {
    pub factor_parent: String,
    pub derived_rank: usize,
    pub input: Vec<String>,
    pub returned_intervals: Vec<(i64, i64)>,
    pub exact_expected: Vec<String>,
    pub exact_reconstruction: bool,
    pub coarse_total_before: String,
    pub coarse_total_after: String,
    pub graded_changed: bool,
    pub device: String,
    pub ptx_sha256: String,
    pub census: TransferCensus,
    pub cpu_semantic_replay_after_device: bool,
}

/// One continuing local morphology word. Deliberately not `Clone`.
pub struct SessionFactorComplex {
    cover: DerivedFactorCover,
    cover_sha256: String,
    predecessor: AlignedFactor,
    predecessor_factor_sha256: String,
    realizations: Vec<TowerFactorRealization>,
    open_factor_addresses: Vec<String>,
    active_prefix: usize,
    ablated: BTreeSet<String>,
}

impl SessionFactorComplex {
    pub fn found(
        cover: DerivedFactorCover,
        predecessor: AlignedFactor,
        mut realizations: Vec<TowerFactorRealization>,
        open_factor_addresses: Vec<String>,
    ) -> Result<Self, SessionFactorRefusal> {
        if cover.schema != "holonic-engine.derived-factor-cover.v1"
            || predecessor.rank == 0
            || predecessor.left.len()
                != predecessor.rows as usize * predecessor.rank as usize
            || predecessor.right.len()
                != predecessor.rank as usize * predecessor.columns as usize
        {
            return Err(SessionFactorRefusal::Shape);
        }
        let order = cover
            .factor_order
            .iter()
            .enumerate()
            .map(|(at, address)| (address.as_str(), at))
            .collect::<BTreeMap<_, _>>();
        let known = order.keys().copied().collect::<BTreeSet<_>>();
        let mut claimed = BTreeSet::new();
        let mut realization_addresses = BTreeSet::new();
        for realization in &realizations {
            if realization.address.is_empty()
                || !realization_addresses.insert(realization.address.as_str())
                || realization.source_factor_addresses.is_empty()
                || realization.delta_entry == 0
                || realization.selector_entry == 0
                || realization.target_row >= predecessor.rows
                || realization.selector_coordinate >= predecessor.columns
                || realization
                    .source_factor_addresses
                    .iter()
                    .any(|address| {
                        !known.contains(address.as_str()) || !claimed.insert(address.as_str())
                    })
            {
                return Err(SessionFactorRefusal::Address);
            }
        }
        for address in &open_factor_addresses {
            if !known.contains(address.as_str()) || !claimed.insert(address.as_str()) {
                return Err(SessionFactorRefusal::Address);
            }
        }
        if claimed.len() != cover.factor_order.len() {
            return Err(SessionFactorRefusal::IncompleteCover);
        }
        realizations.sort_by_key(|realization| {
            realization
                .source_factor_addresses
                .iter()
                .filter_map(|address| order.get(address.as_str()))
                .copied()
                .min()
                .unwrap_or(usize::MAX)
        });
        let cover_sha256 = digest_json(&cover)?;
        let predecessor_factor_sha256 = factor_digest(&predecessor)?;
        let active_prefix = realizations.len();
        let complex = Self {
            cover,
            cover_sha256,
            predecessor,
            predecessor_factor_sha256,
            realizations,
            open_factor_addresses,
            active_prefix,
            ablated: BTreeSet::new(),
        };
        complex.current_factor()?;
        Ok(complex)
    }

    pub fn cover(&self) -> &DerivedFactorCover {
        &self.cover
    }

    pub fn open_factor_addresses(&self) -> &[String] {
        &self.open_factor_addresses
    }

    pub fn realizations(&self) -> &[TowerFactorRealization] {
        &self.realizations
    }

    pub fn active_prefix(&self) -> usize {
        self.active_prefix
    }

    pub fn current_factor(
        &self,
    ) -> Result<(AlignedFactor, FactorDerivationReceipt), SessionFactorRefusal> {
        let mut entries = BTreeMap::<(usize, usize), Rat>::new();
        let has_active_realization = self.realizations[..self.active_prefix]
            .iter()
            .any(|realization| !self.ablated.contains(&realization.address));
        let rows = self.predecessor.rows as usize;
        let columns = self.predecessor.columns as usize;
        let inherited_rank = self.predecessor.rank as usize;
        for row in 0..rows {
            for rank in 0..inherited_rank {
                let left = scale(
                    self.predecessor.left[row * inherited_rank + rank],
                    self.predecessor.left_exponent,
                );
                if left.is_zero() {
                    continue;
                }
                for column in 0..columns {
                    let right = scale(
                        self.predecessor.right[rank * columns + column],
                        self.predecessor.right_exponent,
                    );
                    if !right.is_zero() {
                        *entries.entry((row, column)).or_insert_with(Rat::zero) += &left * &right;
                    }
                }
            }
        }
        for realization in self.realizations[..self.active_prefix].iter().filter(|realization| {
            !self.ablated.contains(&realization.address)
        }) {
            let value = scale(realization.delta_entry, self.predecessor.left_exponent)
                * scale(realization.selector_entry, self.predecessor.right_exponent);
            *entries
                .entry((
                    realization.target_row as usize,
                    realization.selector_coordinate as usize,
                ))
                .or_insert_with(Rat::zero) += value;
        }
        entries.retain(|_, value| !value.is_zero());
        let support_rows = entries
            .keys()
            .map(|(row, _)| *row)
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect::<Vec<_>>();
        let support_columns = entries
            .keys()
            .map(|(_, column)| *column)
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect::<Vec<_>>();
        if support_rows.is_empty() || support_columns.is_empty() {
            return Err(SessionFactorRefusal::RankZero);
        }
        let supported = ExactRatMatrix::new(
            support_rows
                .iter()
                .map(|row| {
                    support_columns
                        .iter()
                        .map(|column| {
                            entries
                                .get(&(*row, *column))
                                .cloned()
                                .unwrap_or_else(Rat::zero)
                        })
                        .collect()
                })
                .collect(),
        )?;
        let factorization = supported.rank_factorization()?;
        if factorization.derived_rank == 0 {
            return Err(SessionFactorRefusal::RankZero);
        }
        let (left_values, left_exponent) = dyadic_entries(&factorization.left)?;
        let (right_values, right_exponent) = dyadic_entries(&factorization.right)?;
        let rank = factorization.derived_rank;
        let mut left = vec![0i64; rows * rank];
        for (local_row, ambient_row) in support_rows.iter().enumerate() {
            for at in 0..rank {
                left[*ambient_row * rank + at] = left_values[local_row * rank + at];
            }
        }
        let mut right = vec![0i64; rank * columns];
        for at in 0..rank {
            for (local_column, ambient_column) in support_columns.iter().enumerate() {
                right[at * columns + *ambient_column] =
                    right_values[at * support_columns.len() + local_column];
            }
        }
        let separator_ordinal = supported
            .entries()
            .iter()
            .position(|entry| !entry.is_zero())
            .ok_or(SessionFactorRefusal::RankZero)?;
        let separator_row = separator_ordinal / supported.columns();
        let separator_column = separator_ordinal % supported.columns();
        let zero = ExactRatMatrix::zero(supported.rows(), supported.columns())?;
        let receipt = DerivedRankDerivationReceipt {
            defect: SparseDefect {
                ambient_rows: rows,
                ambient_columns: columns,
                support_rows: support_rows.clone(),
                support_columns: support_columns.clone(),
                supported: supported.clone(),
            },
            factorization,
            zero_rank_foil: SparseDefect {
                ambient_rows: rows,
                ambient_columns: columns,
                support_rows: support_rows.clone(),
                support_columns: support_columns.clone(),
                supported: zero,
            },
            separator: SeparatingReceiver {
                target: (
                    support_rows[separator_row],
                    support_columns[separator_column],
                ),
                predecessor: Rat::zero(),
                candidate: supported.get(separator_row, separator_column)?.clone(),
            },
        };
        let factor = if has_active_realization {
            AlignedFactor {
                rows: self.predecessor.rows,
                columns: self.predecessor.columns,
                rank: u32::try_from(rank).map_err(|_| SessionFactorRefusal::Carrier)?,
                resident_grain: self.predecessor.resident_grain,
                left_exponent,
                right_exponent,
                entry_octets: 8,
                left,
                right,
            }
        } else {
            // Exact withdrawal returns the retained predecessor realization itself. Re-pivoting
            // the equal map would change its gauge and therefore would not recover the same
            // computational object even when every downstream receiver happened to agree.
            self.predecessor.clone()
        };
        Ok((factor, FactorDerivationReceipt::Derived(receipt)))
    }

    pub fn identity(&self) -> Result<SessionFactorComplexIdentity, SessionFactorRefusal> {
        let (factor, _) = self.current_factor()?;
        let current_factor_sha256 = factor_digest(&factor)?;
        let ablated_realizations = self.ablated.iter().cloned().collect::<Vec<_>>();
        let complete_sha256 = digest_json(&(
            &self.cover_sha256,
            &self.predecessor_factor_sha256,
            self.active_prefix,
            &ablated_realizations,
            factor.rank,
            &current_factor_sha256,
        ))?;
        Ok(SessionFactorComplexIdentity {
            cover_sha256: self.cover_sha256.clone(),
            predecessor_factor_sha256: self.predecessor_factor_sha256.clone(),
            active_prefix: self.active_prefix,
            realization_population: self.realizations.len(),
            ablated_realizations,
            derived_rank: factor.rank as usize,
            current_factor_sha256,
            complete_sha256,
        })
    }

    pub fn withdraw_to_prefix(
        &mut self,
        prefix: usize,
    ) -> Result<FactorMutationReceipt, SessionFactorRefusal> {
        if prefix >= self.active_prefix {
            return Err(SessionFactorRefusal::WithdrawalOrder);
        }
        let predecessor_sha256 = self.identity()?.complete_sha256;
        self.active_prefix = prefix;
        self.ablated.retain(|address| {
            self.realizations[..prefix]
                .iter()
                .any(|realization| &realization.address == address)
        });
        let successor = self.identity()?;
        Ok(FactorMutationReceipt {
            predecessor_sha256,
            successor_sha256: successor.complete_sha256,
            active_prefix: prefix,
            ablated_realizations: successor.ablated_realizations,
            derived_rank: successor.derived_rank,
            exact_withdrawal: true,
        })
    }

    pub fn ablate(
        &mut self,
        realization_address: &str,
    ) -> Result<FactorMutationReceipt, SessionFactorRefusal> {
        let predecessor_sha256 = self.identity()?.complete_sha256;
        if !self.realizations[..self.active_prefix]
            .iter()
            .any(|realization| realization.address == realization_address)
            || !self.ablated.insert(realization_address.to_owned())
        {
            return Err(SessionFactorRefusal::Address);
        }
        let successor = self.identity()?;
        Ok(FactorMutationReceipt {
            predecessor_sha256,
            successor_sha256: successor.complete_sha256,
            active_prefix: self.active_prefix,
            ablated_realizations: successor.ablated_realizations,
            derived_rank: successor.derived_rank,
            exact_withdrawal: false,
        })
    }

    pub fn restore_ablation(
        &mut self,
        realization_address: &str,
    ) -> Result<FactorMutationReceipt, SessionFactorRefusal> {
        let predecessor_sha256 = self.identity()?.complete_sha256;
        if !self.ablated.remove(realization_address) {
            return Err(SessionFactorRefusal::Address);
        }
        let successor = self.identity()?;
        Ok(FactorMutationReceipt {
            predecessor_sha256,
            successor_sha256: successor.complete_sha256,
            active_prefix: self.active_prefix,
            ablated_realizations: successor.ablated_realizations,
            derived_rank: successor.derived_rank,
            exact_withdrawal: false,
        })
    }
}

/// Conduct one exact local section on the same resident owner used by the Phoenix session.  The
/// input is an exterior BF16 apparatus face; it is decoded to exact dyadics only for the returned
/// reconstruction check after the GPU deed has completed.
pub fn conduct_factor_current(
    readout: &ResidentReadout,
    local: &LocalFactorReceipt,
    input_words: &[u16],
) -> Result<ResidentFactorCurrentReturn, SessionFactorRefusal> {
    if local.derived_rank == 0 || input_words.len() != local.factorization.columns {
        return Err(SessionFactorRefusal::Shape);
    }
    let surface = ResidentSurface::on(readout)
        .map_err(|error| SessionFactorRefusal::Apparatus(error.to_string()))?;
    let before = surface.census();
    let (left_entries, left_exponent) = dyadic_entries(&local.factorization.left)?;
    let (right_entries, right_exponent) = dyadic_entries(&local.factorization.right)?;
    let left = readout
        .mount(
            &aligned(left_entries, left_exponent),
            local.factorization.left.columns(),
        )
        .map_err(|error| SessionFactorRefusal::Apparatus(format!("left mount: {error:?}")))?;
    let right = readout
        .mount(
            &aligned(right_entries, right_exponent),
            local.factorization.right.columns(),
        )
        .map_err(|error| SessionFactorRefusal::Apparatus(format!("right mount: {error:?}")))?;
    let grain = ResidentGrain(0);
    let staged = surface
        .stage_words(input_words, 1, input_words.len())
        .map_err(|error| SessionFactorRefusal::Apparatus(error.to_string()))?;
    let enter_shape = surface
        .shape_enter(1, input_words.len(), Dyadic::ONE, grain, input_words)
        .map_err(|error| SessionFactorRefusal::Apparatus(error.to_string()))?;
    let factor_shape = surface
        .shape_factorized_contract(
            1,
            input_words.len(),
            enter_shape.needed,
            &left,
            &right,
            local.derived_rank,
        )
        .map_err(|error| SessionFactorRefusal::Apparatus(error.to_string()))?;
    let input = surface
        .fresh_section(1, input_words.len(), grain)
        .map_err(|error| SessionFactorRefusal::Apparatus(error.to_string()))?;
    let output = surface
        .fresh_section(1, local.factorization.rows, grain)
        .map_err(|error| SessionFactorRefusal::Apparatus(error.to_string()))?;
    let mut builder = surface
        .begin_passage(&[vec![], vec![0]])
        .map_err(|error| SessionFactorRefusal::Apparatus(error.to_string()))?;
    let entering = builder
        .open(0, &[])
        .map_err(|error| SessionFactorRefusal::Apparatus(error.to_string()))?;
    surface
        .record_enter(&entering, &staged, Dyadic::ONE, &input)
        .map_err(|error| SessionFactorRefusal::Apparatus(error.to_string()))?;
    builder
        .close(0, &input, enter_shape.needed)
        .map_err(|error| SessionFactorRefusal::Apparatus(error.to_string()))?;
    let contracting = builder
        .open(1, &[0])
        .map_err(|error| SessionFactorRefusal::Apparatus(error.to_string()))?;
    surface
        .record_factorized_contract(
            &contracting,
            &input,
            &left,
            &right,
            &factor_shape,
            &output,
        )
        .map_err(|error| SessionFactorRefusal::Apparatus(error.to_string()))?;
    builder
        .close(1, &output, factor_shape.needed)
        .map_err(|error| SessionFactorRefusal::Apparatus(error.to_string()))?;
    let passage = builder
        .finish()
        .map_err(|error| SessionFactorRefusal::Apparatus(error.to_string()))?;
    let returned = passage
        .launch()
        .map_err(|error| SessionFactorRefusal::Apparatus(error.to_string()))?;
    if !returned.obstruction.refusals.is_empty() {
        return Err(SessionFactorRefusal::Apparatus(format!(
            "resident factor current returned {:?}",
            returned.obstruction.refusals
        )));
    }
    let returned_intervals = surface
        .read_out(&output)
        .map_err(|error| SessionFactorRefusal::Apparatus(error.to_string()))?;
    let input_exact = input_words
        .iter()
        .map(|word| {
            Dyadic::of_bfloat16_bits(*word)
                .map(|value| value.value())
                .map_err(|error| SessionFactorRefusal::Apparatus(error.to_string()))
        })
        .collect::<Result<Vec<_>, _>>()?;
    let exact_expected = local.section.supported.apply(&input_exact)?;
    let exact_reconstruction = returned_intervals
        .iter()
        .zip(&exact_expected)
        .all(|((lower, upper), expected)| {
            expected.denom() == &BigInt::one()
                && expected.numer().to_i64() == Some(*lower)
                && lower == upper
        });
    let coarse_total_after = exact_expected.iter().fold(Rat::zero(), |sum, value| sum + value);
    let after = surface.census();
    Ok(ResidentFactorCurrentReturn {
        factor_parent: local.section.address.clone(),
        derived_rank: local.derived_rank,
        input: input_exact.iter().map(ToString::to_string).collect(),
        returned_intervals,
        exact_expected: exact_expected.iter().map(ToString::to_string).collect(),
        exact_reconstruction,
        coarse_total_before: Rat::zero().to_string(),
        coarse_total_after: coarse_total_after.to_string(),
        graded_changed: exact_expected.iter().any(|value| !value.is_zero()),
        device: surface.device_name().to_owned(),
        ptx_sha256: surface.ptx_sha256().to_owned(),
        census: census_delta(&before, &after),
        cpu_semantic_replay_after_device: false,
    })
}

fn aligned(entries: Vec<i64>, exponent: i32) -> AlignedMaterial {
    AlignedMaterial {
        entry_octaves: entries
            .iter()
            .map(|value| i64::BITS - value.unsigned_abs().leading_zeros())
            .max()
            .unwrap_or(0),
        negatives: entries.iter().filter(|value| **value < 0).count() as u64,
        entries,
        exponent,
    }
}

fn census_delta(before: &TransferCensus, after: &TransferCensus) -> TransferCensus {
    TransferCensus {
        ingress_octets: after.ingress_octets.saturating_sub(before.ingress_octets),
        egress_section_octets: after
            .egress_section_octets
            .saturating_sub(before.egress_section_octets),
        egress_receipt_octets: after
            .egress_receipt_octets
            .saturating_sub(before.egress_receipt_octets),
        device_to_device_octets: after
            .device_to_device_octets
            .saturating_sub(before.device_to_device_octets),
        captured_launches: after
            .captured_launches
            .saturating_sub(before.captured_launches),
        deed_launches: after.deed_launches.saturating_sub(before.deed_launches),
        control_launches: after
            .control_launches
            .saturating_sub(before.control_launches),
        synchronizations: after
            .synchronizations
            .saturating_sub(before.synchronizations),
        allocations: after.allocations.saturating_sub(before.allocations),
        resident_octets_now: after.resident_octets_now,
        resident_octets_peak: after.resident_octets_peak,
        section_read_outs: after
            .section_read_outs
            .saturating_sub(before.section_read_outs),
    }
}

fn factor_digest(factor: &AlignedFactor) -> Result<String, SessionFactorRefusal> {
    MorphologyPayload::AlignedFactor(factor.clone())
        .canonical_digest()
        .map_err(|error| SessionFactorRefusal::Wire(error.to_string()))
}

fn scale(value: i64, exponent: i32) -> Rat {
    if exponent >= 0 {
        Rat::from_integer(BigInt::from(value) * (BigInt::one() << exponent as usize))
    } else {
        Rat::new(BigInt::from(value), BigInt::one() << (-exponent) as usize)
    }
}

fn dyadic_entries(matrix: &ExactRatMatrix) -> Result<(Vec<i64>, i32), SessionFactorRefusal> {
    let mut greatest = 0u32;
    for value in matrix.entries() {
        let denominator = value
            .denom()
            .to_biguint()
            .ok_or(SessionFactorRefusal::NonDyadic)?;
        if denominator.is_zero()
            || denominator != (BigUint::one() << denominator.bits().saturating_sub(1) as usize)
        {
            return Err(SessionFactorRefusal::NonDyadic);
        }
        greatest = greatest.max(denominator.bits().saturating_sub(1) as u32);
    }
    let entries = matrix
        .entries()
        .iter()
        .map(|value| {
            let denominator = value
                .denom()
                .to_biguint()
                .ok_or(SessionFactorRefusal::NonDyadic)?;
            let power = denominator.bits().saturating_sub(1) as u32;
            let shifted = value.numer() << (greatest - power) as usize;
            shifted.to_i64().ok_or(SessionFactorRefusal::Carrier)
        })
        .collect::<Result<Vec<_>, _>>()?;
    let exponent = i32::try_from(greatest)
        .ok()
        .and_then(i32::checked_neg)
        .ok_or(SessionFactorRefusal::Carrier)?;
    Ok((entries, exponent))
}

fn digest_json(value: &impl Serialize) -> Result<String, SessionFactorRefusal> {
    let bytes = serde_json::to_vec(value)
        .map_err(|error| SessionFactorRefusal::Wire(error.to_string()))?;
    Ok(format!("{:x}", Sha256::digest(bytes)))
}

#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum SessionFactorRefusal {
    #[error("the predecessor or returned factor cover has an incompatible shape")]
    Shape,
    #[error("the factor realization has an unknown, duplicated or invalid address")]
    Address,
    #[error("the realization/open-fibre partition does not cover every returned atom")]
    IncompleteCover,
    #[error("the contemporary factor map has rank zero")]
    RankZero,
    #[error("the exact factorization left the resident dyadic carrier")]
    NonDyadic,
    #[error("the exact factorization exceeds the resident integer carrier")]
    Carrier,
    #[error("withdrawal must remove a nonempty ordered suffix")]
    WithdrawalOrder,
    #[error("factor-complex wire refused: {0}")]
    Wire(String),
    #[error("resident factor-complex apparatus refused: {0}")]
    Apparatus(String),
    #[error(transparent)]
    Exact(#[from] ExactLinearError),
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::derived_factor_cover::{DefectMetrics, SupportedDefectSection};

    fn rat(value: i64) -> Rat {
        Rat::from_integer(BigInt::from(value))
    }

    fn cover() -> DerivedFactorCover {
        DerivedFactorCover::derive(vec![SupportedDefectSection {
            address: "returned-defect".to_owned(),
            parent_candidate: "sealed-candidate".to_owned(),
            receiver: "graded-receiver".to_owned(),
            successor_word: vec!["later-return".to_owned()],
            chart: "receiver-chart".to_owned(),
            ambient_rows: 2,
            ambient_columns: 2,
            support_rows: vec![0, 1],
            support_columns: vec![0, 1],
            supported: ExactRatMatrix::new(vec![vec![rat(1), rat(0)], vec![rat(0), rat(1)]])
                .expect("defect"),
            metrics: DefectMetrics {
                domain: ExactRatMatrix::identity(2).expect("domain metric"),
                codomain: ExactRatMatrix::identity(2).expect("codomain metric"),
            },
        }])
        .expect("cover")
    }

    fn predecessor() -> AlignedFactor {
        AlignedFactor {
            rows: 3,
            columns: 3,
            rank: 1,
            resident_grain: 1,
            left_exponent: 0,
            right_exponent: 0,
            entry_octets: 8,
            left: vec![6, 0, 0],
            right: vec![0, -2, 0],
        }
    }

    #[test]
    fn factor_word_changes_one_body_and_exact_prefix_withdrawal_recovers_it() {
        let cover = cover();
        let addresses = cover.factor_order.clone();
        let base = predecessor();
        let base_sha = factor_digest(&base).expect("base identity");
        let mut complex = SessionFactorComplex::found(
            cover,
            base,
            vec![
                TowerFactorRealization {
                    address: "realization-b".to_owned(),
                    source_factor_addresses: vec![addresses[1].clone()],
                    target_row: 2,
                    selector_coordinate: 2,
                    delta_entry: 1,
                    selector_entry: 1,
                },
                TowerFactorRealization {
                    address: "realization-a".to_owned(),
                    source_factor_addresses: vec![addresses[0].clone()],
                    target_row: 1,
                    selector_coordinate: 0,
                    delta_entry: 1,
                    selector_entry: 1,
                },
            ],
            Vec::new(),
        )
        .expect("factor complex");
        assert_eq!(complex.realizations()[0].address, "realization-a");
        assert_eq!(complex.realizations()[1].address, "realization-b");
        assert_eq!(complex.identity().expect("full").derived_rank, 3);
        let full = complex.identity().expect("full").complete_sha256;
        complex.ablate("realization-b").expect("ablate");
        assert_eq!(complex.identity().expect("ablated").derived_rank, 2);
        complex
            .restore_ablation("realization-b")
            .expect("restore");
        assert_eq!(complex.identity().expect("restored").complete_sha256, full);
        complex.withdraw_to_prefix(1).expect("withdraw suffix");
        assert_eq!(complex.identity().expect("prefix one").derived_rank, 2);
        complex.withdraw_to_prefix(0).expect("withdraw all");
        let predecessor = complex.identity().expect("predecessor");
        assert_eq!(predecessor.derived_rank, 1);
        assert_eq!(predecessor.current_factor_sha256, base_sha);
    }
}

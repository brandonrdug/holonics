//! The L1 dependent product of exchange receiver-history occurrences and actual K3 passages.
//!
//! Support is the product of a receiver/history native fibre and an addressed K3 serial pullback.
//! Source ordinals remain reconstruction lineage.  Opaque observations name free-module faces but
//! are never converted into numbers or currents.  Current enters by tensoring the oriented face
//! incidence with the actual candidate/successor K3 Complex-Parametron current.

use std::collections::{BTreeMap, BTreeSet};

use holonic_engine::{
    derived_factor_cover::{
        DefectMetrics, DerivedFactorCover, OverlapKind, SupportedDefectSection,
    },
    native_spool::{
        NativeCollapsedFibre, NativeMutualConstitutiveResponse, NativePullbackOccurrence,
    },
    receiver_exact_compression::{InputId, ItemId, ReceiverId},
    receiver_history_compression::{NativeStateId, ReceiverHistoryCompression, SourceTransport},
    EventId, ExactComplexWaveCurrent, ExactRatMatrix, OccurrencePort,
};
use num_bigint::BigInt;
use num_rational::BigRational as Rat;
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use thiserror::Error;

mod support;

use support::{generator_receipts, mixed_interactions, situated_local, validate_mixed_interaction};

use super::{
    AthenaNativeConsequence, AthenaNativeRest, CausalAdjointStepInput,
    CompleteExchangeNativeRealizationPassage, ComplexParametronDifference,
    DependentDifferenceChart, ExchangeDefectBasisFace, NativeConductedSection,
    NativeSectionAddress, ReturnedExchangeSection, SituatedDifferenceInput,
    SituatedDifferenceSection,
};

pub const EXCHANGE_SITUATED_PRODUCT_SCHEMA: &str = "soma-life.exchange-situated-product.v2";

/// Exterior lineage needed to reconnect the sealed candidate with its actual later return.
/// `source` never enters support, contact, coefficient, or native identity.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ExchangeCandidateLineage {
    pub source: ItemId,
    pub seal_sha256: String,
}

/// The source-neutral material face accepted by the L1 owner.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ExchangeProductMaterial {
    pub predecessor_rest_wire_sha256: String,
    pub native: ReceiverHistoryCompression,
    pub candidate_lineage: Vec<ExchangeCandidateLineage>,
    pub returned: Vec<ReturnedExchangeSection>,
    pub open_exterior: Vec<String>,
}

impl ExchangeProductMaterial {
    pub fn from_passage(
        passage: &CompleteExchangeNativeRealizationPassage,
    ) -> Result<Self, String> {
        passage.validate()?;
        let material = Self {
            predecessor_rest_wire_sha256: passage.candidate.predecessor_rest_wire_sha256.clone(),
            native: passage.native.clone(),
            candidate_lineage: passage
                .candidate
                .sections
                .iter()
                .map(|section| ExchangeCandidateLineage {
                    source: section.history.source,
                    seal_sha256: section.seal_sha256.clone(),
                })
                .collect(),
            returned: passage.returned.clone(),
            open_exterior: passage.open_exterior.clone(),
        };
        material.validate()?;
        Ok(material)
    }

    pub fn validate(&self) -> Result<(), String> {
        self.native.validate().map_err(display)?;
        if !is_digest(&self.predecessor_rest_wire_sha256)
            || self.candidate_lineage.len() != self.native.source_population.len()
            || self.returned.len() != self.native.source_population.len()
            || self.open_exterior.is_empty()
            || self.open_exterior.iter().any(String::is_empty)
        {
            return Err("the exchange product material is incomplete".to_owned());
        }
        let expected = self
            .native
            .source_population
            .iter()
            .copied()
            .collect::<BTreeSet<_>>();
        let lineage = self
            .candidate_lineage
            .iter()
            .map(|entry| entry.source)
            .collect::<BTreeSet<_>>();
        let returned = self
            .returned
            .iter()
            .map(|entry| entry.source)
            .collect::<BTreeSet<_>>();
        if lineage != expected
            || returned != expected
            || self
                .candidate_lineage
                .iter()
                .any(|entry| !is_digest(&entry.seal_sha256))
            || self.returned.iter().any(|entry| {
                entry.candidate_event == entry.return_event
                    || entry.receiver_faces.is_empty()
                    || self.native.encode(entry.source).ok() != Some(entry.native)
            })
        {
            return Err(
                "exchange lineage does not reconstruct the receiver/history passage".to_owned(),
            );
        }
        Ok(())
    }
}

/// One actual serial K3 word used by every exchange fibre.  Both sections are immutable testimony
/// from the sole rest; locals retain this branch index rather than cloning them.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct K3PullbackBranch {
    pub address: String,
    pub candidate: NativeConductedSection,
    pub returned: NativeConductedSection,
    pub pullback: NativePullbackOccurrence,
}

/// The complete receiver constitutive form over the admitted K3 branch population.
/// Diagonal entries are exact squared moduli of the carried complex response; off-diagonal entries
/// are the exact mutual storage already owned by K3.  Its factorization retains any radical.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NativeReceiverConstitutiveForm {
    pub receiver: ReceiverId,
    pub branch_addresses: Vec<String>,
    pub form: ExactRatMatrix,
    pub factorization: holonic_engine::LinearFactorization,
    pub mutual_responses: Vec<NativeMutualConstitutiveResponse>,
}

impl NativeReceiverConstitutiveForm {
    fn found(branches: &[K3PullbackBranch]) -> Result<Self, ExchangeSituatedProductError> {
        let Some(first) = branches.first() else {
            return Err(ExchangeSituatedProductError::K3(
                "the K3 pullback population is empty".to_owned(),
            ));
        };
        let receiver = first.returned.receiver;
        if branches.iter().any(|branch| {
            branch.candidate.receiver != receiver
                || branch.returned.receiver != receiver
                || branch.returned.constitutive_response.stored == ExactComplexWaveCurrent::zero()
        }) {
            return Err(ExchangeSituatedProductError::Constitutive(
                "one branch lacks a nonzero receiver constitutive response".to_owned(),
            ));
        }
        let mut mutual = branches
            .iter()
            .flat_map(|branch| {
                branch
                    .candidate
                    .mutual_constitutive_responses
                    .iter()
                    .chain(&branch.returned.mutual_constitutive_responses)
            })
            .filter(|response| response.receiver == receiver)
            .cloned()
            .collect::<Vec<_>>();
        mutual.sort_by_key(|response| (response.left_occurrence, response.right_occurrence));
        mutual.dedup();
        let mut rows = vec![vec![rat(0); branches.len()]; branches.len()];
        for (at, branch) in branches.iter().enumerate() {
            rows[at][at] = branch.returned.constitutive_response.stored.norm_square();
        }
        for left in 0..branches.len() {
            for right in left + 1..branches.len() {
                let left_event = branches[left].returned.address.occurrence;
                let right_event = branches[right].returned.address.occurrence;
                if let Some(response) = mutual.iter().find(|response| {
                    (response.left_occurrence == left_event
                        && response.right_occurrence == right_event)
                        || (response.left_occurrence == right_event
                            && response.right_occurrence == left_event)
                }) {
                    rows[left][right] = response.storage.clone();
                    rows[right][left] = response.storage.clone();
                }
            }
        }
        let form = ExactRatMatrix::new(rows).map_err(linear)?;
        let factorization = form.factorization().map_err(linear)?;
        Ok(Self {
            receiver,
            branch_addresses: branches
                .iter()
                .map(|branch| branch.address.clone())
                .collect(),
            form,
            factorization,
            mutual_responses: mutual,
        })
    }

    fn local_metric(&self, branch: usize) -> Result<Rat, ExchangeSituatedProductError> {
        let value = self.form.get(branch, branch).map_err(linear)?.clone();
        if value == rat(0) {
            return Err(ExchangeSituatedProductError::Constitutive(
                "a local receiver metric is degenerate".to_owned(),
            ));
        }
        Ok(value)
    }
}

/// One exchange face tensored with the actual K3 complex current that crossed it.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ExactExchangeFaceCurrent {
    pub face: ExchangeDefectBasisFace,
    pub orientation: i64,
    pub current: ExactComplexWaveCurrent,
}

/// Actual returned native material before it is compressed into one local L0 receipt.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ExchangeReturnedNativeSection {
    pub native: NativeStateId,
    pub branch: usize,
    pub candidate_event: EventId,
    pub return_event: EventId,
    pub members: Vec<ReturnedExchangeSection>,
    pub source_reconstruction_fibre: BTreeSet<ItemId>,
    pub event_reconstruction_fibre: BTreeSet<EventId>,
    pub candidate_face: ExchangeDefectBasisFace,
    pub returned_faces: Vec<ExchangeDefectBasisFace>,
    pub oriented_currents: Vec<ExactExchangeFaceCurrent>,
    pub candidate_current: ExactComplexWaveCurrent,
    pub returned_current: ExactComplexWaveCurrent,
    pub difference_current: ExactComplexWaveCurrent,
}

/// L0 compressed through a shared K3 branch table.  `reconstruct` returns the complete
/// `SituatedDifferenceSection`; no K3 body is duplicated in the wire.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct CompressedSituatedDifference {
    pub candidate_event: EventId,
    pub return_event: EventId,
    pub occurrence_fibres: Vec<NativeCollapsedFibre>,
    pub chart: DependentDifferenceChart,
    pub complex_difference: ComplexParametronDifference,
    pub causal_adjoint: super::CausalAdjointWord,
    pub open_deposition_boundary: String,
    pub open_exterior: Vec<String>,
    pub identity_sha256: String,
}

impl CompressedSituatedDifference {
    fn from_full(full: &SituatedDifferenceSection) -> Self {
        Self {
            candidate_event: full.candidate.address.occurrence,
            return_event: full.returned.address.occurrence,
            occurrence_fibres: full.occurrence_fibres.clone(),
            chart: full.chart.clone(),
            complex_difference: full.complex_difference.clone(),
            causal_adjoint: full.causal_adjoint.clone(),
            open_deposition_boundary: full.open_deposition_boundary.clone(),
            open_exterior: full.open_exterior.clone(),
            identity_sha256: full.identity_sha256.clone(),
        }
    }

    fn reconstruct(
        &self,
        branch: &K3PullbackBranch,
    ) -> Result<SituatedDifferenceSection, ExchangeSituatedProductError> {
        let event_fibre = self
            .occurrence_fibres
            .iter()
            .flat_map(|fibre| fibre.occurrences.iter().copied())
            .collect::<BTreeSet<_>>();
        let candidate = readdress_section(
            &branch.candidate,
            self.candidate_event,
            branch.candidate.predecessor,
            event_fibre.clone(),
        );
        let returned = readdress_section(
            &branch.returned,
            self.return_event,
            Some(self.candidate_event),
            event_fibre,
        );
        let full = SituatedDifferenceSection::found(SituatedDifferenceInput {
            candidate,
            returned,
            carrying_occurrence: NativePullbackOccurrence {
                left: self.candidate_event,
                right: self.return_event,
                joining_native: branch.pullback.joining_native,
            },
            occurrence_fibres: self.occurrence_fibres.clone(),
            source_transport: self.chart.source_transport.clone(),
            rebased_transport: self.chart.rebased_transport.clone(),
            source_chart: self.chart.source_chart.clone(),
            target_chart: self.chart.target_chart.clone(),
            candidate_coordinates: self.chart.candidate_coordinates.clone(),
            returned_coordinates: self.chart.returned_coordinates.clone(),
            adjoint_steps: self
                .causal_adjoint
                .steps
                .iter()
                .map(|step| CausalAdjointStepInput {
                    name: step.name.clone(),
                    forward: step.forward.clone(),
                    domain_metric: step.domain_metric.clone(),
                    codomain_metric: step.codomain_metric.clone(),
                })
                .collect(),
            terminal_covector: self.causal_adjoint.terminal_covector.clone(),
            native_obstructions: Vec::new(),
            open_deposition_boundary: self.open_deposition_boundary.clone(),
            open_exterior: self.open_exterior.clone(),
        })?;
        if full.chart != self.chart
            || full.complex_difference != self.complex_difference
            || full.causal_adjoint != self.causal_adjoint
            || full.identity_sha256 != self.identity_sha256
        {
            return Err(ExchangeSituatedProductError::Wire(
                "the compressed situated difference does not reconstruct".to_owned(),
            ));
        }
        Ok(full)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ExchangeProductAddress {
    pub native: NativeStateId,
    pub branch: usize,
    pub k3_candidate: NativeSectionAddress,
    pub k3_return: NativeSectionAddress,
    pub exchange_candidate: EventId,
    pub exchange_return: EventId,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ExchangeGeneratorSquareReceipt {
    pub exchange_generator: InputId,
    pub native_start: NativeStateId,
    pub native_end: NativeStateId,
    pub source_edges: Vec<SourceTransport>,
    pub k3_branch: usize,
    pub k3_word: Vec<InputId>,
    pub exchange_square_commutes: bool,
    pub k3_pullback_word_admitted: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ExchangeSituatedLocal {
    pub address: ExchangeProductAddress,
    pub returned_native: ExchangeReturnedNativeSection,
    pub situated: CompressedSituatedDifference,
    pub generator_squares: Vec<ExchangeGeneratorSquareReceipt>,
    pub support_identity_sha256: String,
    pub open_exterior: Vec<String>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NativeStateExchangeCover {
    pub native: NativeStateId,
    pub source_reconstruction_fibre: BTreeSet<ItemId>,
    pub locals: Vec<ExchangeSituatedLocal>,
    pub cover: DerivedFactorCover,
}

/// Compact exact finite-Leibniz interaction over every receiver-history support pair carried by
/// one pair of K3 branches.  The family law replaces a quadratic receipt enumeration.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct MixedConstitutiveInteractionFamily {
    pub left_branch: usize,
    pub right_branch: usize,
    pub storage: Rat,
    pub candidate_left: ExactComplexWaveCurrent,
    pub candidate_right: ExactComplexWaveCurrent,
    pub returned_left: ExactComplexWaveCurrent,
    pub returned_right: ExactComplexWaveCurrent,
    pub left_difference: ExactComplexWaveCurrent,
    pub right_difference: ExactComplexWaveCurrent,
    pub candidate_product: ExactComplexWaveCurrent,
    pub source_linear_terms: ExactComplexWaveCurrent,
    pub mixed_remainder: ExactComplexWaveCurrent,
    pub reconstructed_returned_product: ExactComplexWaveCurrent,
    pub returned_product: ExactComplexWaveCurrent,
    pub native_support: Vec<NativeStateId>,
    pub pair_population: u64,
}

/// A later-return intervention measured against the already sealed candidate.
///
/// The factor projection may remain unchanged when only addressed return lineage changes.  The
/// complete situated difference must nevertheless change because its occurrence fibre changed.
/// This receipt makes that distinction explicit instead of promoting the scalar factor shadow to
/// equality of the loss holon.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ReturnEventInterventionLocal {
    pub branch: usize,
    pub candidate_event_before: EventId,
    pub candidate_event_after: EventId,
    pub return_event_before: EventId,
    pub return_event_after: EventId,
    pub situated_identity_before: String,
    pub situated_identity_after: String,
    pub factor_projection_unchanged: bool,
    pub complete_situated_difference_changed: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ReturnEventInterventionReceipt {
    pub source: ItemId,
    pub native: NativeStateId,
    pub sealed_candidate_sha256: String,
    pub replacement_return_event: EventId,
    pub sealed_candidate_unchanged: bool,
    pub affected_locals: Vec<ReturnEventInterventionLocal>,
    pub unaffected_native_support_identity_sha256: String,
}

#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ExchangeSituatedProduct {
    pub schema: String,
    pub predecessor_rest_wire_sha256: String,
    pub native_action: ReceiverHistoryCompression,
    pub candidate_lineage: Vec<ExchangeCandidateLineage>,
    pub codomain_basis: Vec<ExchangeDefectBasisFace>,
    pub k3_branches: Vec<K3PullbackBranch>,
    pub constitutive_form: NativeReceiverConstitutiveForm,
    pub native_covers: Vec<NativeStateExchangeCover>,
    pub mixed_interactions: Vec<MixedConstitutiveInteractionFamily>,
    pub open_exterior: Vec<String>,
    pub identity_sha256: String,
}

impl ExchangeSituatedProduct {
    pub fn found(
        rest: &AthenaNativeRest,
        material: ExchangeProductMaterial,
    ) -> Result<Self, ExchangeSituatedProductError> {
        material
            .validate()
            .map_err(ExchangeSituatedProductError::Exchange)?;
        rest.validate()
            .map_err(|error| ExchangeSituatedProductError::K3(error.to_string()))?;
        let rest_wire = rest
            .wire_sha256()
            .map_err(|error| ExchangeSituatedProductError::K3(error.to_string()))?;
        if material.predecessor_rest_wire_sha256 != rest_wire {
            return Err(ExchangeSituatedProductError::K3(
                "the exchange candidate was sealed against a different K3 rest".to_owned(),
            ));
        }
        let branches = k3_pullback_branches(rest)?;
        let constitutive_form = NativeReceiverConstitutiveForm::found(&branches)?;
        let codomain_basis = codomain_basis(&material, &branches)?;
        let basis_index = codomain_basis
            .iter()
            .enumerate()
            .map(|(row, face)| (face.clone(), row))
            .collect::<BTreeMap<_, _>>();
        let native_columns = material
            .native
            .native_population
            .iter()
            .copied()
            .enumerate()
            .map(|(column, native)| (native, column))
            .collect::<BTreeMap<_, _>>();
        let returned_by_source = material
            .returned
            .iter()
            .map(|section| (section.source, section.clone()))
            .collect::<BTreeMap<_, _>>();
        let seals = material
            .candidate_lineage
            .iter()
            .map(|entry| (entry.source, entry.seal_sha256.clone()))
            .collect::<BTreeMap<_, _>>();
        let mut native_covers = Vec::with_capacity(material.native.native_population.len());
        for fibre in &material.native.reconstruction_fibres {
            let members = fibre
                .sources
                .iter()
                .map(|source| returned_by_source[source].clone())
                .collect::<Vec<_>>();
            let receiver_faces = common_receiver_faces(&members)?;
            let mut locals = Vec::with_capacity(branches.len());
            let mut supported = Vec::with_capacity(branches.len());
            for branch in 0..branches.len() {
                let returned_native = returned_native_section(
                    fibre.native,
                    branch,
                    &branches[branch],
                    members.clone(),
                    &receiver_faces,
                )?;
                let (full, section) = situated_local(
                    &returned_native,
                    &branches[branch],
                    &constitutive_form,
                    &basis_index,
                    codomain_basis.len(),
                    native_columns.len(),
                    native_columns[&fibre.native],
                    &material.native,
                    &seals,
                )?;
                let address = ExchangeProductAddress {
                    native: fibre.native,
                    branch,
                    k3_candidate: branches[branch].candidate.address.clone(),
                    k3_return: branches[branch].returned.address.clone(),
                    exchange_candidate: returned_native.candidate_event,
                    exchange_return: returned_native.return_event,
                };
                let support_identity_sha256 = digest_json(&(
                    "exchange-k3-support/v1",
                    fibre.native,
                    &branches[branch].address,
                    &section.support_rows,
                    &section.support_columns,
                    &constitutive_form.form,
                ))?;
                supported.push(section.clone());
                locals.push(ExchangeSituatedLocal {
                    address,
                    generator_squares: generator_receipts(
                        fibre.native,
                        branch,
                        &branches[branch],
                        &material.native,
                        &fibre.sources,
                    )?,
                    returned_native,
                    situated: CompressedSituatedDifference::from_full(&full),
                    support_identity_sha256,
                    open_exterior: vec!["morphology deposition remains open until L2".to_owned()],
                });
            }
            let cover = DerivedFactorCover::derive(supported).map_err(factor_error)?;
            if !cover.compact_interchange_families.is_empty()
                || cover.overlaps.len() != pair_population(branches.len())? as usize
                || cover.overlaps.iter().any(|overlap| {
                    overlap.patch.is_none()
                        || matches!(
                            &overlap.kind,
                            OverlapKind::DisjointInterchange { .. } | OverlapKind::Open { .. }
                        )
                })
            {
                return Err(ExchangeSituatedProductError::Cover(
                    "the receiver-history/K3 product collapsed back into private interchange"
                        .to_owned(),
                ));
            }
            for local in &locals {
                if !cover
                    .locals
                    .iter()
                    .any(|receipt| receipt.section.address == local_address(&local.address))
                {
                    return Err(ExchangeSituatedProductError::Cover(
                        "a local is absent from its native-state cover".to_owned(),
                    ));
                }
            }
            native_covers.push(NativeStateExchangeCover {
                native: fibre.native,
                source_reconstruction_fibre: fibre.sources.clone(),
                locals,
                cover,
            });
        }
        native_covers.sort_by_key(|cover| cover.native);
        let mixed_interactions = mixed_interactions(
            &branches,
            &constitutive_form,
            &material.native.native_population,
            receiver_family_size(&material.native)?,
        )?;
        if mixed_interactions
            .iter()
            .all(|interaction| interaction.mixed_remainder == ExactComplexWaveCurrent::zero())
        {
            return Err(ExchangeSituatedProductError::Constitutive(
                "all shared-support mixed interaction vanished".to_owned(),
            ));
        }
        let mut product = Self {
            schema: EXCHANGE_SITUATED_PRODUCT_SCHEMA.to_owned(),
            predecessor_rest_wire_sha256: rest_wire,
            native_action: material.native,
            candidate_lineage: material.candidate_lineage,
            codomain_basis,
            k3_branches: branches,
            constitutive_form,
            native_covers,
            mixed_interactions,
            open_exterior: vec![
                "the exact causal-adjoint deposits have not yet changed continuing morphology"
                    .to_owned(),
                "receiver and successor-history families outside this exchange remain open"
                    .to_owned(),
            ],
            identity_sha256: String::new(),
        };
        product.identity_sha256 = product.rederived_identity()?;
        Ok(product)
    }

    pub fn validate(&self) -> Result<(), ExchangeSituatedProductError> {
        self.native_action
            .validate()
            .map_err(|error| ExchangeSituatedProductError::Exchange(error.to_string()))?;
        if self.schema != EXCHANGE_SITUATED_PRODUCT_SCHEMA
            || !is_digest(&self.predecessor_rest_wire_sha256)
            || self.k3_branches.is_empty()
            || self.native_covers.len() != self.native_action.native_population.len()
            || self.open_exterior.is_empty()
            || self.open_exterior.iter().any(String::is_empty)
            || self.identity_sha256 != self.rederived_identity()?
        {
            return Err(ExchangeSituatedProductError::Wire(
                "the exchange situated product is malformed".to_owned(),
            ));
        }
        if self.constitutive_form != NativeReceiverConstitutiveForm::found(&self.k3_branches)? {
            return Err(ExchangeSituatedProductError::Constitutive(
                "the K3 receiver constitutive form does not rederive".to_owned(),
            ));
        }
        let expected_natives = self
            .native_action
            .native_population
            .iter()
            .copied()
            .collect::<BTreeSet<_>>();
        let actual_natives = self
            .native_covers
            .iter()
            .map(|cover| cover.native)
            .collect::<BTreeSet<_>>();
        if expected_natives != actual_natives {
            return Err(ExchangeSituatedProductError::Cover(
                "the native-state cover is not total".to_owned(),
            ));
        }
        for cover in &self.native_covers {
            cover.cover.validate().map_err(factor_error)?;
            if cover.locals.len() != self.k3_branches.len()
                || cover.cover.locals.len() != cover.locals.len()
                || !cover.cover.compact_interchange_families.is_empty()
            {
                return Err(ExchangeSituatedProductError::Cover(
                    "one native-state cover is incomplete or privately interchanged".to_owned(),
                ));
            }
            for local in &cover.locals {
                let factor = cover
                    .cover
                    .locals
                    .iter()
                    .find(|factor| factor.section.address == local_address(&local.address))
                    .ok_or_else(|| {
                        ExchangeSituatedProductError::Cover(
                            "one dependent local is absent from its factor cover".to_owned(),
                        )
                    })?;
                if local.address.native != cover.native
                    || local.address.branch >= self.k3_branches.len()
                    || local.returned_native.source_reconstruction_fibre
                        != cover.source_reconstruction_fibre
                    || factor.section.support_rows.is_empty()
                    || local
                        .situated
                        .reconstruct(&self.k3_branches[local.address.branch])?
                        .identity_sha256
                        != local.situated.identity_sha256
                    || local.generator_squares.iter().any(|square| {
                        !square.exchange_square_commutes || !square.k3_pullback_word_admitted
                    })
                {
                    return Err(ExchangeSituatedProductError::Cover(
                        "one dependent local fails reconstruction or naturality".to_owned(),
                    ));
                }
            }
        }
        for interaction in &self.mixed_interactions {
            validate_mixed_interaction(interaction)?;
        }
        Ok(())
    }

    pub fn canonical_bytes(&self) -> Result<Vec<u8>, ExchangeSituatedProductError> {
        self.validate_founded_envelope()?;
        serde_json::to_vec(self)
            .map_err(|error| ExchangeSituatedProductError::Wire(error.to_string()))
    }

    pub fn read(bytes: &[u8]) -> Result<Self, ExchangeSituatedProductError> {
        let product: Self = serde_json::from_slice(bytes)
            .map_err(|error| ExchangeSituatedProductError::Wire(error.to_string()))?;
        product.validate()?;
        Ok(product)
    }

    pub fn rederived_identity(&self) -> Result<String, ExchangeSituatedProductError> {
        digest_json(&(
            &self.schema,
            &self.predecessor_rest_wire_sha256,
            &self.native_action,
            &self.candidate_lineage,
            &self.codomain_basis,
            &self.k3_branches,
            &self.constitutive_form,
            &self.native_covers,
            &self.mixed_interactions,
            &self.open_exterior,
        ))
    }

    /// Re-derive the complete local loss sections after one addressed later-return occurrence is
    /// replaced.  The sealed candidate, native quotient, K3 branch table and every other native
    /// support remain fixed.  Nothing is deposited; L2 owns that return.
    pub fn intervene_return_event(
        &self,
        source: ItemId,
        replacement_return_event: EventId,
    ) -> Result<ReturnEventInterventionReceipt, ExchangeSituatedProductError> {
        self.validate_founded_envelope()?;
        let cover = self
            .native_covers
            .iter()
            .find(|cover| cover.source_reconstruction_fibre.contains(&source))
            .ok_or_else(|| {
                ExchangeSituatedProductError::Exchange(
                    "the intervened source is outside the receiver-history reconstruction fibres"
                        .to_owned(),
                )
            })?;
        let baseline_return = cover
            .locals
            .first()
            .and_then(|local| {
                local
                    .returned_native
                    .members
                    .iter()
                    .find(|member| member.source == source)
            })
            .ok_or_else(|| {
                ExchangeSituatedProductError::Exchange(
                    "the intervened source has no retained later-return occurrence".to_owned(),
                )
            })?;
        if replacement_return_event == baseline_return.return_event
            || replacement_return_event == baseline_return.candidate_event
        {
            return Err(ExchangeSituatedProductError::Exchange(
                "the replacement return does not separate the candidate and prior return"
                    .to_owned(),
            ));
        }
        let seals = self
            .candidate_lineage
            .iter()
            .map(|entry| (entry.source, entry.seal_sha256.clone()))
            .collect::<BTreeMap<_, _>>();
        let basis = self
            .codomain_basis
            .iter()
            .enumerate()
            .map(|(row, face)| (face.clone(), row))
            .collect::<BTreeMap<_, _>>();
        let native_columns = self
            .native_action
            .native_population
            .iter()
            .copied()
            .enumerate()
            .map(|(column, native)| (native, column))
            .collect::<BTreeMap<_, _>>();
        let mut affected_locals = Vec::with_capacity(cover.locals.len());
        for baseline in &cover.locals {
            let branch = baseline.address.branch;
            let mut members = baseline.returned_native.members.clone();
            members
                .iter_mut()
                .find(|member| member.source == source)
                .ok_or_else(|| {
                    ExchangeSituatedProductError::Exchange(
                        "one local omitted the intervened reconstruction member".to_owned(),
                    )
                })?
                .return_event = replacement_return_event;
            let returned_faces = common_receiver_faces(&members)?;
            let returned_native = returned_native_section(
                cover.native,
                branch,
                &self.k3_branches[branch],
                members,
                &returned_faces,
            )?;
            let (changed, changed_supported) = situated_local(
                &returned_native,
                &self.k3_branches[branch],
                &self.constitutive_form,
                &basis,
                self.codomain_basis.len(),
                native_columns.len(),
                native_columns[&cover.native],
                &self.native_action,
                &seals,
            )?;
            let baseline_supported = cover
                .cover
                .locals
                .iter()
                .find(|factor| factor.section.address == local_address(&baseline.address))
                .ok_or_else(|| {
                    ExchangeSituatedProductError::Cover(
                        "the intervened local is absent from its factor cover".to_owned(),
                    )
                })?;
            let baseline_full = baseline.situated.reconstruct(&self.k3_branches[branch])?;
            affected_locals.push(ReturnEventInterventionLocal {
                branch,
                candidate_event_before: baseline_full.candidate.address.occurrence,
                candidate_event_after: changed.candidate.address.occurrence,
                return_event_before: baseline_full.returned.address.occurrence,
                return_event_after: changed.returned.address.occurrence,
                situated_identity_before: baseline_full.identity_sha256.clone(),
                situated_identity_after: changed.identity_sha256.clone(),
                factor_projection_unchanged: baseline_supported.section == changed_supported,
                complete_situated_difference_changed: baseline_full.identity_sha256
                    != changed.identity_sha256,
            });
        }
        let sealed_candidate_sha256 = seals.get(&source).cloned().ok_or_else(|| {
            ExchangeSituatedProductError::Exchange(
                "the intervened source has no sealed-candidate lineage".to_owned(),
            )
        })?;
        let unaffected_native_support_identity_sha256 = digest_json(
            &self
                .native_covers
                .iter()
                .filter(|candidate| candidate.native != cover.native)
                .flat_map(|candidate| {
                    candidate
                        .locals
                        .iter()
                        .map(|local| &local.support_identity_sha256)
                })
                .collect::<Vec<_>>(),
        )?;
        let receipt = ReturnEventInterventionReceipt {
            source,
            native: cover.native,
            sealed_candidate_sha256,
            replacement_return_event,
            sealed_candidate_unchanged: affected_locals
                .iter()
                .all(|local| local.candidate_event_before == local.candidate_event_after),
            affected_locals,
            unaffected_native_support_identity_sha256,
        };
        if !receipt.sealed_candidate_unchanged
            || receipt.affected_locals.is_empty()
            || receipt
                .affected_locals
                .iter()
                .any(|local| !local.complete_situated_difference_changed)
        {
            return Err(ExchangeSituatedProductError::Exchange(
                "the later-return intervention did not change only the complete loss lineage"
                    .to_owned(),
            ));
        }
        Ok(receipt)
    }

    /// Construction-side envelope check. Exact constituent owners already certified every local
    /// during `found`; untrusted serialized material takes the full `read -> validate` route.
    fn validate_founded_envelope(&self) -> Result<(), ExchangeSituatedProductError> {
        if self.schema != EXCHANGE_SITUATED_PRODUCT_SCHEMA
            || !is_digest(&self.predecessor_rest_wire_sha256)
            || !is_digest(&self.identity_sha256)
            || self.k3_branches.is_empty()
            || self.native_covers.len() != self.native_action.native_population.len()
            || self.open_exterior.is_empty()
            || self.open_exterior.iter().any(String::is_empty)
        {
            return Err(ExchangeSituatedProductError::Wire(
                "the founded exchange situated envelope is malformed".to_owned(),
            ));
        }
        Ok(())
    }
}

#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum ExchangeSituatedProductError {
    #[error("K3 dependent passage refused: {0}")]
    K3(String),
    #[error("exchange receiver/history passage refused: {0}")]
    Exchange(String),
    #[error("receiver constitutive form refused: {0}")]
    Constitutive(String),
    #[error("dependent factor cover refused: {0}")]
    Cover(String),
    #[error("situated difference refused: {0}")]
    Situated(String),
    #[error("exchange situated wire refused: {0}")]
    Wire(String),
}

impl From<super::SituatedDifferenceError> for ExchangeSituatedProductError {
    fn from(error: super::SituatedDifferenceError) -> Self {
        Self::Situated(error.to_string())
    }
}

fn k3_pullback_branches(
    rest: &AthenaNativeRest,
) -> Result<Vec<K3PullbackBranch>, ExchangeSituatedProductError> {
    let receiver = *rest
        .realization
        .receiver_family
        .iter()
        .next()
        .ok_or_else(|| ExchangeSituatedProductError::K3("K3 has no receiver".to_owned()))?;
    let mut branches = Vec::new();
    for ingress in &rest.realization.ingress_sections {
        let candidate = match rest
            .conduct(ingress, receiver)
            .map_err(|error| ExchangeSituatedProductError::K3(error.to_string()))?
        {
            AthenaNativeConsequence::Returned(passage) => passage.section,
            AthenaNativeConsequence::Insufficient(insufficiency) => {
                return Err(ExchangeSituatedProductError::K3(format!(
                    "an admitted ingress returned {insufficiency:?}"
                )));
            }
        };
        if candidate.successor_sections.is_empty() {
            return Err(ExchangeSituatedProductError::K3(
                "an ingress has no actual successor section".to_owned(),
            ));
        }
        for successor in &candidate.successor_sections {
            let returned = match rest
                .conduct(successor, receiver)
                .map_err(|error| ExchangeSituatedProductError::K3(error.to_string()))?
            {
                AthenaNativeConsequence::Returned(passage) => passage.section,
                AthenaNativeConsequence::Insufficient(insufficiency) => {
                    return Err(ExchangeSituatedProductError::K3(format!(
                        "an admitted successor returned {insufficiency:?}"
                    )));
                }
            };
            let pullback = rest
                .ecology
                .spools
                .iter()
                .flat_map(|spool| &spool.serial_pullbacks)
                .flat_map(|serial| &serial.occurrences)
                .find(|occurrence| {
                    occurrence.left == candidate.address.occurrence
                        && occurrence.right == returned.address.occurrence
                })
                .copied()
                .ok_or_else(|| {
                    ExchangeSituatedProductError::K3(
                        "candidate and successor lack an actual K3 pullback occurrence".to_owned(),
                    )
                })?;
            let address = digest_json(&(
                "k3-pullback-branch/v1",
                &candidate.address,
                &returned.address,
                pullback,
            ))?;
            branches.push(K3PullbackBranch {
                address,
                candidate: candidate.clone(),
                returned,
                pullback,
            });
        }
    }
    branches.sort_by(|left, right| left.address.cmp(&right.address));
    if branches.is_empty() {
        return Err(ExchangeSituatedProductError::K3(
            "K3 returned no serial pullback branches".to_owned(),
        ));
    }
    Ok(branches)
}

fn codomain_basis(
    material: &ExchangeProductMaterial,
    branches: &[K3PullbackBranch],
) -> Result<Vec<ExchangeDefectBasisFace>, ExchangeSituatedProductError> {
    let mut basis = BTreeSet::new();
    for branch in branches {
        basis.insert(candidate_face(&branch.candidate));
    }
    for factor in &material.native.receiver_factors {
        basis.insert(ExchangeDefectBasisFace::ReturnedReceiver {
            receiver: factor.receiver,
            observation: factor.observation,
        });
    }
    if basis.is_empty() {
        return Err(ExchangeSituatedProductError::Cover(
            "the common returned-difference basis is empty".to_owned(),
        ));
    }
    Ok(basis.into_iter().collect())
}

fn common_receiver_faces(
    members: &[ReturnedExchangeSection],
) -> Result<Vec<ExchangeDefectBasisFace>, ExchangeSituatedProductError> {
    let Some(first) = members.first() else {
        return Err(ExchangeSituatedProductError::Exchange(
            "a native receiver/history fibre has no source occurrences".to_owned(),
        ));
    };
    if members
        .iter()
        .any(|member| member.receiver_faces != first.receiver_faces)
    {
        return Err(ExchangeSituatedProductError::Exchange(
            "receiver faces do not factor through the declared native state".to_owned(),
        ));
    }
    let mut faces = first
        .receiver_faces
        .iter()
        .map(|factor| ExchangeDefectBasisFace::ReturnedReceiver {
            receiver: factor.receiver,
            observation: factor.observation,
        })
        .collect::<Vec<_>>();
    faces.sort();
    faces.dedup();
    if faces.is_empty() {
        return Err(ExchangeSituatedProductError::Exchange(
            "the returned receiver family is empty".to_owned(),
        ));
    }
    Ok(faces)
}

fn returned_native_section(
    native: NativeStateId,
    branch: usize,
    k3: &K3PullbackBranch,
    mut members: Vec<ReturnedExchangeSection>,
    returned_faces: &[ExchangeDefectBasisFace],
) -> Result<ExchangeReturnedNativeSection, ExchangeSituatedProductError> {
    members.sort_by_key(|member| member.source);
    let source_reconstruction_fibre = members.iter().map(|member| member.source).collect();
    let mut event_reconstruction_fibre = members
        .iter()
        .flat_map(|member| [member.candidate_event, member.return_event])
        .collect::<BTreeSet<_>>();
    let candidate_event = addressed_event(&(
        "exchange-condensed-candidate/v1",
        native,
        branch,
        members
            .iter()
            .map(|member| member.candidate_event)
            .collect::<Vec<_>>(),
        &k3.address,
    ))?;
    let return_event = addressed_event(&(
        "exchange-condensed-return/v1",
        native,
        branch,
        members
            .iter()
            .map(|member| member.return_event)
            .collect::<Vec<_>>(),
        &k3.address,
    ))?;
    if candidate_event == return_event {
        return Err(ExchangeSituatedProductError::Exchange(
            "condensed candidate and return events collided".to_owned(),
        ));
    }
    event_reconstruction_fibre.extend([candidate_event, return_event]);
    let candidate_face = candidate_face(&k3.candidate);
    let candidate_current = k3.candidate.emitting_current.clone();
    let returned_current = returned_faces
        .iter()
        .fold(ExactComplexWaveCurrent::zero(), |sum, _| {
            sum.add(&k3.returned.emitting_current)
        });
    let difference_current = returned_current.subtract(&candidate_current);
    let mut oriented_currents = vec![ExactExchangeFaceCurrent {
        face: candidate_face.clone(),
        orientation: -1,
        current: candidate_current.negated(),
    }];
    oriented_currents.extend(
        returned_faces
            .iter()
            .cloned()
            .map(|face| ExactExchangeFaceCurrent {
                face,
                orientation: 1,
                current: k3.returned.emitting_current.clone(),
            }),
    );
    let aggregate = oriented_currents
        .iter()
        .fold(ExactComplexWaveCurrent::zero(), |sum, face| {
            sum.add(&face.current)
        });
    if aggregate != difference_current {
        return Err(ExchangeSituatedProductError::Exchange(
            "the face-current population does not reconstruct its oriented difference".to_owned(),
        ));
    }
    Ok(ExchangeReturnedNativeSection {
        native,
        branch,
        candidate_event,
        return_event,
        members,
        source_reconstruction_fibre,
        event_reconstruction_fibre,
        candidate_face,
        returned_faces: returned_faces.to_vec(),
        oriented_currents,
        candidate_current,
        returned_current,
        difference_current,
    })
}

fn readdress_section(
    template: &NativeConductedSection,
    event: EventId,
    predecessor: Option<EventId>,
    reconstruction_fibre: BTreeSet<EventId>,
) -> NativeConductedSection {
    let mut section = template.clone();
    section.address.occurrence = event;
    section.predecessor = predecessor;
    section.entering_port = OccurrencePort::input(event, template.entering_port.ordinal);
    section.emitting_port = OccurrencePort::output(event, template.emitting_port.ordinal);
    section.incidence.occurrence = event;
    section.reconstruction_fibre = reconstruction_fibre;
    section
}

fn candidate_face(section: &NativeConductedSection) -> ExchangeDefectBasisFace {
    ExchangeDefectBasisFace::SealedCandidate {
        seed_section: section.address.clone(),
        entering_native: section.entering_native,
        emitting_native: section.emitting_native,
        receiver: section.receiver,
        observation: section.observation,
    }
}

fn receiver_family_size(
    native: &ReceiverHistoryCompression,
) -> Result<usize, ExchangeSituatedProductError> {
    let Some(first) = native.native_population.first() else {
        return Err(ExchangeSituatedProductError::Exchange(
            "the receiver/history native population is empty".to_owned(),
        ));
    };
    let population = native
        .receiver_factors
        .iter()
        .filter(|factor| factor.native == *first)
        .count();
    if population == 0 {
        return Err(ExchangeSituatedProductError::Exchange(
            "the receiver family is empty".to_owned(),
        ));
    }
    Ok(population)
}

fn pair_population(population: usize) -> Result<u64, ExchangeSituatedProductError> {
    let n = u64::try_from(population)
        .map_err(|_| ExchangeSituatedProductError::Cover("pair population overflow".to_owned()))?;
    n.checked_mul(n.saturating_sub(1))
        .and_then(|value| value.checked_div(2))
        .ok_or_else(|| ExchangeSituatedProductError::Cover("pair population overflow".to_owned()))
}

fn local_address(address: &ExchangeProductAddress) -> String {
    format!("exchange-k3-local/{}/{}", address.native.0, address.branch)
}

fn addressed_event(value: &impl Serialize) -> Result<EventId, ExchangeSituatedProductError> {
    let bytes = serde_json::to_vec(value)
        .map_err(|error| ExchangeSituatedProductError::Wire(error.to_string()))?;
    let digest = Sha256::digest(bytes);
    Ok(EventId(u64::from_le_bytes(
        digest[..8].try_into().expect("eight digest octets"),
    )))
}

fn digest_json(value: &impl Serialize) -> Result<String, ExchangeSituatedProductError> {
    let bytes = serde_json::to_vec(value)
        .map_err(|error| ExchangeSituatedProductError::Wire(error.to_string()))?;
    Ok(Sha256::digest(bytes)
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect())
}

fn rat(value: i64) -> Rat {
    Rat::from_integer(BigInt::from(value))
}

fn linear(error: impl std::fmt::Display) -> ExchangeSituatedProductError {
    ExchangeSituatedProductError::Constitutive(error.to_string())
}

fn factor_error(error: impl std::fmt::Display) -> ExchangeSituatedProductError {
    ExchangeSituatedProductError::Cover(error.to_string())
}

fn display(error: impl std::fmt::Display) -> String {
    error.to_string()
}

use holonic_engine::is_sha256_digest as is_digest;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn mixed_remainder_is_required_by_the_exact_product_difference() {
        let storage = rat(3);
        let candidate_left = ExactComplexWaveCurrent::new(rat(2), rat(1));
        let candidate_right = ExactComplexWaveCurrent::new(rat(1), rat(-1));
        let returned_left = ExactComplexWaveCurrent::new(rat(5), rat(2));
        let returned_right = ExactComplexWaveCurrent::new(rat(4), rat(1));
        let left_difference = returned_left.subtract(&candidate_left);
        let right_difference = returned_right.subtract(&candidate_right);
        let candidate_product = candidate_left.multiply(&candidate_right).scaled(&storage);
        let linear = candidate_left
            .multiply(&right_difference)
            .add(&left_difference.multiply(&candidate_right))
            .scaled(&storage);
        let mixed = left_difference.multiply(&right_difference).scaled(&storage);
        let returned = returned_left.multiply(&returned_right).scaled(&storage);
        assert_eq!(candidate_product.add(&linear).add(&mixed), returned);
        assert_ne!(candidate_product.add(&linear), returned);
    }

    #[test]
    fn support_identity_uses_native_fibre_and_k3_incidence_not_source_ordinal() {
        let rows = vec![1usize, 4, 9];
        let columns = vec![2usize];
        let form = ExactRatMatrix::new(vec![vec![rat(7)]]).unwrap();
        let left = digest_json(&(
            "exchange-k3-support/v1",
            NativeStateId(3),
            "branch",
            &rows,
            &columns,
            &form,
        ))
        .unwrap();
        let renamed_source = ItemId(999);
        let right = digest_json(&(
            "exchange-k3-support/v1",
            NativeStateId(3),
            "branch",
            &rows,
            &columns,
            &form,
        ))
        .unwrap();
        assert_eq!(left, right);
        assert_eq!(
            renamed_source,
            ItemId(999),
            "source remains exterior lineage"
        );
    }
}

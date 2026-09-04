//! The complete returned difference of two addressed native sections.
//!
//! This module adds no trainer or scalar objective.  It composes standing native incidence,
//! exact-linear chart transport, Complex-Parametron current, receiver constitution, addressed
//! lineage, and reconstruction owners into the one L0 carrier.  Chart coordinates remain
//! presentations of the same situated body; a noncommuting chart returns its exact defect.

use holonic_engine::{
    cross_chart::{cross_chart_defect, CrossChartDefect},
    native_spool::{NativeCollapsedFibre, NativePullbackOccurrence, NativeThreadObstruction},
    ExactComplexWaveCurrent, ExactRatMatrix,
};
use num_rational::BigRational as Rat;
use num_traits::Zero;
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use thiserror::Error;

use super::types::NativeConductedSection;

pub const SITUATED_DIFFERENCE_SCHEMA: &str = "soma-life.situated-difference-section.v1";

/// One affine reconstruction fibre of a linear return.  `particular + span(kernel)` is retained
/// instead of choosing the particular point as if it were an inverse.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct AffineReconstructionFibre {
    pub particular: Vec<Rat>,
    pub kernel: Vec<Vec<Rat>>,
}

/// One forward differential and the receiver constitutive forms which determine its adjoint.
/// Metrics are mandatory: a bare transpose is not silently promoted to the causal return.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct CausalAdjointStepInput {
    pub name: String,
    pub forward: ExactRatMatrix,
    pub domain_metric: ExactRatMatrix,
    pub codomain_metric: ExactRatMatrix,
}

/// The exact return through one member of an addressed forward word.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct CausalAdjointStep {
    pub name: String,
    pub forward: ExactRatMatrix,
    pub domain_metric: ExactRatMatrix,
    pub codomain_metric: ExactRatMatrix,
    pub adjoint: ExactRatMatrix,
    pub forward_factorization: holonic_engine::LinearFactorization,
    pub adjoint_factorization: holonic_engine::LinearFactorization,
}

/// One covector current as it crosses a named step in reverse order.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ReturnedCovectorSection {
    pub step: String,
    pub entering_covector: Vec<Rat>,
    pub returned_covector: Vec<Rat>,
    pub reconstruction_fibre: AffineReconstructionFibre,
    pub obstruction: Option<Vec<Rat>>,
}

/// The inverse question is retained beside, and never substituted for, the adjoint return.
/// The engine's rebase receipt carries a static diagnostic string; this owned wire face keeps the
/// same exact factorization while permitting source-detached serialization.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "status", rename_all = "kebab-case", deny_unknown_fields)]
pub enum InverseTransportReceipt {
    Rebase {
        inverse: ExactRatMatrix,
        forward_identity: bool,
        backward_identity: bool,
    },
    Refused {
        factorization: holonic_engine::LinearFactorization,
        reason: String,
    },
}

impl InverseTransportReceipt {
    fn from_engine(receipt: holonic_engine::RebaseReceipt) -> Self {
        match receipt {
            holonic_engine::RebaseReceipt::Rebase {
                inverse,
                forward_identity,
                backward_identity,
            } => Self::Rebase {
                inverse: *inverse,
                forward_identity,
                backward_identity,
            },
            holonic_engine::RebaseReceipt::Refused {
                factorization,
                reason,
            } => Self::Refused {
                factorization: *factorization,
                reason: reason.to_owned(),
            },
        }
    }
}

/// The actual finite forward word and its reverse-order causal-adjoint return.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct CausalAdjointWord {
    pub forward_order: Vec<String>,
    pub reverse_order: Vec<String>,
    pub steps: Vec<CausalAdjointStep>,
    pub composite_forward: ExactRatMatrix,
    pub composite_adjoint: ExactRatMatrix,
    pub reverse_composite_adjoint: ExactRatMatrix,
    pub terminal_covector: Vec<Rat>,
    pub returned_sections: Vec<ReturnedCovectorSection>,
    pub returned_source_covector: Vec<Rat>,
    pub radical: Vec<Vec<Rat>>,
    pub reconstruction_fibre: AffineReconstructionFibre,
    pub obstruction: Option<Vec<Rat>>,
    pub inverse_transport: InverseTransportReceipt,
}

impl CausalAdjointWord {
    pub fn found(
        inputs: Vec<CausalAdjointStepInput>,
        terminal_covector: Vec<Rat>,
    ) -> Result<Self, SituatedDifferenceError> {
        let word = build_causal_adjoint(inputs, terminal_covector)?;
        word.validate()?;
        Ok(word)
    }

    pub fn validate(&self) -> Result<(), SituatedDifferenceError> {
        let inputs = self
            .steps
            .iter()
            .map(|step| CausalAdjointStepInput {
                name: step.name.clone(),
                forward: step.forward.clone(),
                domain_metric: step.domain_metric.clone(),
                codomain_metric: step.codomain_metric.clone(),
            })
            .collect();
        let expected = build_causal_adjoint(inputs, self.terminal_covector.clone())?;
        if &expected != self {
            return Err(SituatedDifferenceError::Adjoint(
                "the causal-adjoint word is not its exact recomputed return".to_owned(),
            ));
        }
        Ok(())
    }
}

/// The chart presentation and exact naturality receipt of one dependent returned difference.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct DependentDifferenceChart {
    pub source_transport: ExactRatMatrix,
    pub rebased_transport: ExactRatMatrix,
    pub source_chart: ExactRatMatrix,
    pub target_chart: ExactRatMatrix,
    pub candidate_coordinates: Vec<Rat>,
    pub returned_coordinates: Vec<Rat>,
    pub transported_candidate: Vec<Rat>,
    pub oriented_difference: Vec<Rat>,
    pub rebased_candidate: Vec<Rat>,
    pub rebased_return: Vec<Rat>,
    pub rebased_transported_candidate: Vec<Rat>,
    pub rebased_difference: Vec<Rat>,
    pub transported_difference: Vec<Rat>,
    pub chart_square: CrossChartDefect,
}

/// The Complex-Parametron current difference before any scalar or binary receiver.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ComplexParametronDifference {
    pub entering_section: ExactComplexWaveCurrent,
    pub entering_current: ExactComplexWaveCurrent,
    pub emitting_section: ExactComplexWaveCurrent,
    pub emitting_current: ExactComplexWaveCurrent,
}

/// Construction input.  It contains the declared chart and adjoint data but no scalar objective.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct SituatedDifferenceInput {
    pub candidate: NativeConductedSection,
    pub returned: NativeConductedSection,
    pub carrying_occurrence: NativePullbackOccurrence,
    pub occurrence_fibres: Vec<NativeCollapsedFibre>,
    pub source_transport: ExactRatMatrix,
    pub rebased_transport: ExactRatMatrix,
    pub source_chart: ExactRatMatrix,
    pub target_chart: ExactRatMatrix,
    pub candidate_coordinates: Vec<Rat>,
    pub returned_coordinates: Vec<Rat>,
    pub adjoint_steps: Vec<CausalAdjointStepInput>,
    pub terminal_covector: Vec<Rat>,
    pub native_obstructions: Vec<NativeThreadObstruction>,
    pub open_deposition_boundary: String,
    pub open_exterior: Vec<String>,
}

/// The L0 carrier.  It ends at an open deposition boundary; morphology application is L2.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct SituatedDifferenceSection {
    pub schema: String,
    pub candidate: NativeConductedSection,
    pub returned: NativeConductedSection,
    pub carrying_occurrence: NativePullbackOccurrence,
    pub occurrence_fibres: Vec<NativeCollapsedFibre>,
    pub chart: DependentDifferenceChart,
    pub complex_difference: ComplexParametronDifference,
    pub causal_adjoint: CausalAdjointWord,
    pub native_obstructions: Vec<NativeThreadObstruction>,
    pub open_deposition_boundary: String,
    pub open_exterior: Vec<String>,
    pub identity_sha256: String,
}

impl SituatedDifferenceSection {
    pub fn found(input: SituatedDifferenceInput) -> Result<Self, SituatedDifferenceError> {
        let section = situated_difference_body(input)?;
        section.validate()?;
        Ok(section)
    }

    pub fn validate(&self) -> Result<(), SituatedDifferenceError> {
        if self.schema != SITUATED_DIFFERENCE_SCHEMA
            || self.open_deposition_boundary.is_empty()
            || self.open_exterior.iter().any(String::is_empty)
            || self.occurrence_fibres.is_empty()
        {
            return Err(SituatedDifferenceError::Malformed(
                "schema, fibre, deposition boundary, or open exterior is malformed".to_owned(),
            ));
        }
        let input = SituatedDifferenceInput {
            candidate: self.candidate.clone(),
            returned: self.returned.clone(),
            carrying_occurrence: self.carrying_occurrence,
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
            native_obstructions: self.native_obstructions.clone(),
            open_deposition_boundary: self.open_deposition_boundary.clone(),
            open_exterior: self.open_exterior.clone(),
        };
        validate_native_pair(&input)?;
        self.causal_adjoint.validate()?;
        let expected =
            situated_difference_body_with_adjoint(input, Some(self.causal_adjoint.clone()))?;
        if self.chart != expected.chart
            || self.complex_difference != expected.complex_difference
            || self.identity_sha256 != self.rederived_identity()?
        {
            return Err(SituatedDifferenceError::Malformed(
                "the situated difference is not its exact recomputed return".to_owned(),
            ));
        }
        Ok(())
    }

    pub fn canonical_bytes(&self) -> Result<Vec<u8>, SituatedDifferenceError> {
        self.validate()?;
        serde_json::to_vec(self).map_err(|error| SituatedDifferenceError::Wire(error.to_string()))
    }

    pub fn read(bytes: &[u8]) -> Result<Self, SituatedDifferenceError> {
        let section: Self = serde_json::from_slice(bytes)
            .map_err(|error| SituatedDifferenceError::Wire(error.to_string()))?;
        section.validate()?;
        Ok(section)
    }

    /// Chart-normalized identity.  The chart receipt remains on the wire, while identity is
    /// carried by the addressed physical section and its pre-rebase difference.  A lawful change
    /// of coordinates therefore preserves identity; changing constitution or lineage does not.
    pub fn rederived_identity(&self) -> Result<String, SituatedDifferenceError> {
        let body = serde_json::to_vec(&(
            &self.schema,
            &self.candidate,
            &self.returned,
            &self.carrying_occurrence,
            &self.occurrence_fibres,
            &self.chart.source_transport,
            &self.chart.candidate_coordinates,
            &self.chart.returned_coordinates,
            &self.chart.oriented_difference,
            &self.complex_difference,
            &self.causal_adjoint,
            &self.native_obstructions,
            &self.open_deposition_boundary,
            &self.open_exterior,
        ))
        .map_err(|error| SituatedDifferenceError::Wire(error.to_string()))?;
        Ok(Sha256::digest(body)
            .iter()
            .map(|byte| format!("{byte:02x}"))
            .collect())
    }
}

#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum SituatedDifferenceError {
    #[error("exact linear transport refused: {0}")]
    Linear(String),
    #[error("dependent chart refused: {0}")]
    Chart(String),
    #[error("the perspective square does not commute: {0:?}")]
    NoncommutingChart(Box<CrossChartDefect>),
    #[error("causal adjoint refused: {0}")]
    Adjoint(String),
    #[error("situated difference malformed: {0}")]
    Malformed(String),
    #[error("situated difference wire refused: {0}")]
    Wire(String),
}

fn validate_native_pair(input: &SituatedDifferenceInput) -> Result<(), SituatedDifferenceError> {
    let candidate = &input.candidate;
    let returned = &input.returned;
    if candidate.address.spool.is_empty()
        || candidate.address.thread.is_empty()
        || returned.address.spool.is_empty()
        || returned.address.thread.is_empty()
        || candidate.address.occurrence == returned.address.occurrence
        || candidate.ordered_word.is_empty()
        || returned.ordered_word.is_empty()
        || candidate.reconstruction_fibre.is_empty()
        || returned.reconstruction_fibre.is_empty()
        || candidate.incidence.coefficient == 0
        || returned.incidence.coefficient == 0
        || candidate.incidence.occurrence != candidate.address.occurrence
        || returned.incidence.occurrence != returned.address.occurrence
        || input.carrying_occurrence.left != candidate.address.occurrence
        || input.carrying_occurrence.right != returned.address.occurrence
        || input.carrying_occurrence.joining_native != candidate.emitting_native
        || input.carrying_occurrence.joining_native != returned.entering_native
        || input.open_deposition_boundary.is_empty()
        || input.occurrence_fibres.is_empty()
    {
        return Err(SituatedDifferenceError::Malformed(
            "the candidate/return span lost address, incidence, word, fibre, or pullback join"
                .to_owned(),
        ));
    }
    let carries_both = input.occurrence_fibres.iter().any(|fibre| {
        fibre.occurrences.contains(&candidate.address.occurrence)
            && fibre.occurrences.contains(&returned.address.occurrence)
    });
    if !carries_both {
        return Err(SituatedDifferenceError::Malformed(
            "no reconstruction fibre retains both caused occurrences".to_owned(),
        ));
    }
    for section in [candidate, returned] {
        if section.entering_port.event != section.address.occurrence
            || section.emitting_port.event != section.address.occurrence
            || section.constitutive_response.native != section.emitting_native
            || section.constitutive_response.receiver != section.receiver
            || section.constitutive_response.presented != section.emitting_section
            || section.constitutive_response.stored != section.emitting_current
            || section.open_exterior.iter().any(String::is_empty)
        {
            return Err(SituatedDifferenceError::Malformed(
                "a K3 native section lost its port or constitutive relation".to_owned(),
            ));
        }
    }
    Ok(())
}

fn vector_subtract(left: &[Rat], right: &[Rat]) -> Result<Vec<Rat>, SituatedDifferenceError> {
    if left.len() != right.len() {
        return Err(SituatedDifferenceError::Chart(
            "the returned and transported sections inhabit different fibres".to_owned(),
        ));
    }
    Ok(left
        .iter()
        .zip(right)
        .map(|(left, right)| left - right)
        .collect())
}

fn linear_error(error: impl std::fmt::Display) -> SituatedDifferenceError {
    SituatedDifferenceError::Linear(error.to_string())
}

fn build_causal_adjoint(
    inputs: Vec<CausalAdjointStepInput>,
    terminal_covector: Vec<Rat>,
) -> Result<CausalAdjointWord, SituatedDifferenceError> {
    if inputs.is_empty() || inputs.iter().any(|step| step.name.is_empty()) {
        return Err(SituatedDifferenceError::Adjoint(
            "the causal adjoint requires a named nonempty forward word".to_owned(),
        ));
    }
    for pair in inputs.windows(2) {
        if pair[0].forward.rows() != pair[1].forward.columns()
            || pair[0].codomain_metric != pair[1].domain_metric
        {
            return Err(SituatedDifferenceError::Adjoint(
                "successive differentials do not share one declared intermediate fibre".to_owned(),
            ));
        }
    }
    if terminal_covector.len() != inputs.last().expect("nonempty").forward.rows() {
        return Err(SituatedDifferenceError::Adjoint(
            "the terminal covector does not inhabit the terminal fibre".to_owned(),
        ));
    }
    // A causal word commonly carries one constitutive metric across several local steps.  Keep
    // inverses lazy and share each one if a genuinely noncentral differential requests it.  A
    // central map cI satisfies g(cIx, y) = g(x, cIy) directly; eagerly inverting g before taking
    // that branch would turn an exact pairing identity into repeated apparatus work.
    let mut metric_inverses = Vec::<(ExactRatMatrix, ExactRatMatrix)>::new();
    let mut steps = Vec::with_capacity(inputs.len());
    for input in inputs {
        let adjoint = if input.domain_metric == input.codomain_metric
            && scalar_identity_coefficient(&input.forward)?.is_some()
        {
            // For a certified nondegenerate common metric G and a central scalar map cI,
            // G^{-1}(cI)^T G = cI. Preserve the exact metric as testimony, but do not enact its
            // cancellation as two enormous rational matrix products at every local step.
            input.forward.clone()
        } else {
            cached_metric_inverse(&mut metric_inverses, &input.domain_metric)?
                .multiply(&input.forward.transpose().map_err(linear_error)?)
                .and_then(|pulled| pulled.multiply(&input.codomain_metric))
                .map_err(linear_error)?
        };
        steps.push(CausalAdjointStep {
            name: input.name,
            forward_factorization: input.forward.factorization().map_err(linear_error)?,
            adjoint_factorization: adjoint.factorization().map_err(linear_error)?,
            forward: input.forward,
            domain_metric: input.domain_metric,
            codomain_metric: input.codomain_metric,
            adjoint,
        });
    }
    let mut composite_forward = steps[0].forward.clone();
    for step in steps.iter().skip(1) {
        composite_forward = step
            .forward
            .multiply(&composite_forward)
            .map_err(linear_error)?;
    }
    let first_metric = &steps.first().expect("nonempty").domain_metric;
    let last_metric = &steps.last().expect("nonempty").codomain_metric;
    let composite_adjoint = if first_metric == last_metric
        && scalar_identity_coefficient(&composite_forward)?.is_some()
    {
        composite_forward.clone()
    } else {
        cached_metric_inverse(&mut metric_inverses, first_metric)?
            .multiply(&composite_forward.transpose().map_err(linear_error)?)
            .and_then(|pulled| pulled.multiply(last_metric))
            .map_err(linear_error)?
    };
    let mut reverse_composite_adjoint = steps[0].adjoint.clone();
    for step in steps.iter().skip(1) {
        reverse_composite_adjoint = reverse_composite_adjoint
            .multiply(&step.adjoint)
            .map_err(linear_error)?;
    }
    if composite_adjoint != reverse_composite_adjoint {
        return Err(SituatedDifferenceError::Adjoint(
            "the metric adjoint did not compose in reverse forward-word order".to_owned(),
        ));
    }
    let mut current = terminal_covector.clone();
    let mut returned_sections = Vec::with_capacity(steps.len());
    for step in steps.iter().rev() {
        let returned = step.adjoint.apply(&current).map_err(linear_error)?;
        let fibre = step
            .adjoint
            .preimage_fibre(&returned)
            .map_err(linear_error)?
            .ok_or_else(|| SituatedDifferenceError::Adjoint("missing adjoint fibre".to_owned()))?;
        returned_sections.push(ReturnedCovectorSection {
            step: step.name.clone(),
            entering_covector: current,
            returned_covector: returned.clone(),
            reconstruction_fibre: AffineReconstructionFibre {
                particular: fibre.0,
                kernel: fibre.1,
            },
            obstruction: step
                .adjoint
                .preimage_obstruction(&returned)
                .map_err(linear_error)?,
        });
        current = returned;
    }
    let returned_source_covector = current;
    let whole_fibre = composite_adjoint
        .preimage_fibre(&returned_source_covector)
        .map_err(linear_error)?
        .ok_or_else(|| SituatedDifferenceError::Adjoint("missing composite fibre".to_owned()))?;
    Ok(CausalAdjointWord {
        forward_order: steps.iter().map(|step| step.name.clone()).collect(),
        reverse_order: steps.iter().rev().map(|step| step.name.clone()).collect(),
        inverse_transport: InverseTransportReceipt::from_engine(
            composite_forward.rebase_receipt().map_err(linear_error)?,
        ),
        radical: composite_adjoint.kernel_basis().map_err(linear_error)?,
        reconstruction_fibre: AffineReconstructionFibre {
            particular: whole_fibre.0,
            kernel: whole_fibre.1,
        },
        obstruction: composite_adjoint
            .preimage_obstruction(&returned_source_covector)
            .map_err(linear_error)?,
        steps,
        composite_forward,
        composite_adjoint,
        reverse_composite_adjoint,
        terminal_covector,
        returned_sections,
        returned_source_covector,
    })
}

fn cached_metric_inverse(
    cache: &mut Vec<(ExactRatMatrix, ExactRatMatrix)>,
    metric: &ExactRatMatrix,
) -> Result<ExactRatMatrix, SituatedDifferenceError> {
    if let Some((_, inverse)) = cache.iter().find(|(known, _)| known == metric) {
        return Ok(inverse.clone());
    }
    let inverse = metric.inverse().map_err(linear_error)?;
    cache.push((metric.clone(), inverse.clone()));
    Ok(inverse)
}

fn scalar_identity_coefficient(
    matrix: &ExactRatMatrix,
) -> Result<Option<Rat>, SituatedDifferenceError> {
    if !matrix.is_square() || matrix.rows() == 0 {
        return Ok(None);
    }
    let coefficient = matrix.get(0, 0).map_err(linear_error)?.clone();
    for row in 0..matrix.rows() {
        for column in 0..matrix.columns() {
            let expected = if row == column {
                &coefficient
            } else {
                // Borrowing a local zero would be awkward; compare directly below.
                if !matrix.get(row, column).map_err(linear_error)?.is_zero() {
                    return Ok(None);
                }
                continue;
            };
            if matrix.get(row, column).map_err(linear_error)? != expected {
                return Ok(None);
            }
        }
    }
    Ok(Some(coefficient))
}

fn situated_difference_body(
    input: SituatedDifferenceInput,
) -> Result<SituatedDifferenceSection, SituatedDifferenceError> {
    situated_difference_body_with_adjoint(input, None)
}

fn situated_difference_body_with_adjoint(
    input: SituatedDifferenceInput,
    admitted_causal_adjoint: Option<CausalAdjointWord>,
) -> Result<SituatedDifferenceSection, SituatedDifferenceError> {
    // Rebuild through the public constructor's equations without calling validation again.
    validate_native_pair(&input)?;
    let chart_square = cross_chart_defect(
        "situated-returned-difference-rebase",
        &input.target_chart,
        &input.source_transport,
        &input.rebased_transport,
        &input.source_chart,
        &[],
    )
    .map_err(|error| SituatedDifferenceError::Linear(error.to_string()))?;
    if !chart_square.is_zero {
        return Err(SituatedDifferenceError::NoncommutingChart(Box::new(
            chart_square,
        )));
    }
    let transported_candidate = input
        .source_transport
        .apply(&input.candidate_coordinates)
        .map_err(linear_error)?;
    let oriented_difference = vector_subtract(&input.returned_coordinates, &transported_candidate)?;
    let rebased_candidate = input
        .source_chart
        .apply(&input.candidate_coordinates)
        .map_err(linear_error)?;
    let rebased_return = input
        .target_chart
        .apply(&input.returned_coordinates)
        .map_err(linear_error)?;
    let rebased_transported_candidate = input
        .rebased_transport
        .apply(&rebased_candidate)
        .map_err(linear_error)?;
    let rebased_difference = vector_subtract(&rebased_return, &rebased_transported_candidate)?;
    let transported_difference = input
        .target_chart
        .apply(&oriented_difference)
        .map_err(linear_error)?;
    if rebased_difference != transported_difference {
        return Err(SituatedDifferenceError::Chart(
            "the oriented difference did not travel through the lawful chart square".to_owned(),
        ));
    }
    let complex_difference = ComplexParametronDifference {
        entering_section: input
            .returned
            .entering_section
            .subtract(&input.candidate.entering_section),
        entering_current: input
            .returned
            .entering_current
            .subtract(&input.candidate.entering_current),
        emitting_section: input
            .returned
            .emitting_section
            .subtract(&input.candidate.emitting_section),
        emitting_current: input
            .returned
            .emitting_current
            .subtract(&input.candidate.emitting_current),
    };
    let causal_adjoint = match admitted_causal_adjoint {
        Some(adjoint) => adjoint,
        None => build_causal_adjoint(input.adjoint_steps, input.terminal_covector)?,
    };
    let mut section = SituatedDifferenceSection {
        schema: SITUATED_DIFFERENCE_SCHEMA.to_owned(),
        candidate: input.candidate,
        returned: input.returned,
        carrying_occurrence: input.carrying_occurrence,
        occurrence_fibres: input.occurrence_fibres,
        chart: DependentDifferenceChart {
            source_transport: input.source_transport,
            rebased_transport: input.rebased_transport,
            source_chart: input.source_chart,
            target_chart: input.target_chart,
            candidate_coordinates: input.candidate_coordinates,
            returned_coordinates: input.returned_coordinates,
            transported_candidate,
            oriented_difference,
            rebased_candidate,
            rebased_return,
            rebased_transported_candidate,
            rebased_difference,
            transported_difference,
            chart_square,
        },
        complex_difference,
        causal_adjoint,
        native_obstructions: input.native_obstructions,
        open_deposition_boundary: input.open_deposition_boundary,
        open_exterior: input.open_exterior,
        identity_sha256: String::new(),
    };
    section.identity_sha256 = section.rederived_identity()?;
    Ok(section)
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeSet;

    use holonic_engine::{
        native_spool::{NativeConstitutiveResponse, NativeIncidenceTerm, NativeThreadHand},
        receiver_exact_compression::{InputId, Observation, ReceiverId},
        receiver_history_compression::NativeStateId,
        BoundaryId, EventId, ExactUnitConicPhase, OccurrencePort,
    };
    use num_bigint::BigInt;

    use super::*;
    use crate::native_intelligence::NativeSectionAddress;

    fn q(numerator: i64, denominator: i64) -> Rat {
        Rat::new(BigInt::from(numerator), BigInt::from(denominator))
    }

    fn matrix(rows: &[&[(i64, i64)]]) -> ExactRatMatrix {
        ExactRatMatrix::new(
            rows.iter()
                .map(|row| row.iter().map(|&(n, d)| q(n, d)).collect())
                .collect(),
        )
        .unwrap()
    }

    fn current(real: i64, imaginary: i64) -> ExactComplexWaveCurrent {
        ExactComplexWaveCurrent::new(q(real, 1), q(imaginary, 1))
    }

    fn section(event: u64, from: u64, to: u64, value: i64) -> NativeConductedSection {
        let occurrence = EventId(event);
        let emitting_section = current(value, 1);
        let emitting_current = current(value + 1, -1);
        NativeConductedSection {
            address: NativeSectionAddress {
                spool: "k3-common-spool".to_owned(),
                thread: format!("native-thread-{event}"),
                occurrence,
            },
            predecessor: (event > 1).then_some(EventId(event - 1)),
            entering_boundary: BoundaryId(event),
            emitting_boundary: BoundaryId(event + 1),
            entering_port: OccurrencePort::input(occurrence, 0),
            emitting_port: OccurrencePort::output(occurrence, 0),
            entering_native: NativeStateId(from),
            emitting_native: NativeStateId(to),
            incidence: NativeIncidenceTerm {
                occurrence,
                from: NativeStateId(from),
                to: NativeStateId(to),
                coefficient: 1,
            },
            entering_section: current(value - 1, 0),
            entering_current: current(value, 0),
            emitting_section: emitting_section.clone(),
            emitting_current: emitting_current.clone(),
            relative_phase: ExactUnitConicPhase::identity(),
            hand: NativeThreadHand::Along,
            constitutive_response: NativeConstitutiveResponse {
                native: NativeStateId(to),
                receiver: ReceiverId(7),
                presented: emitting_section,
                stored: emitting_current,
            },
            mutual_constitutive_responses: Vec::new(),
            ordered_word: vec![InputId(event)],
            receiver: ReceiverId(7),
            observation: Observation(42),
            reconstruction_fibre: BTreeSet::from([occurrence]),
            successor_sections: Vec::new(),
            open_exterior: vec![format!("open-after-{event}")],
        }
    }

    fn lawful_input() -> SituatedDifferenceInput {
        let source_transport = matrix(&[&[(1, 1), (1, 1)], &[(0, 1), (1, 1)]]);
        let source_chart = matrix(&[&[(2, 1), (0, 1)], &[(0, 1), (1, 1)]]);
        let target_chart = matrix(&[&[(1, 1), (0, 1)], &[(0, 1), (3, 1)]]);
        let rebased_transport = matrix(&[&[(1, 2), (1, 1)], &[(0, 1), (3, 1)]]);
        let middle_metric = matrix(&[&[(3, 1), (0, 1)], &[(0, 1), (1, 1)]]);
        SituatedDifferenceInput {
            candidate: section(1, 10, 11, 2),
            returned: section(2, 11, 12, 5),
            carrying_occurrence: NativePullbackOccurrence {
                left: EventId(1),
                right: EventId(2),
                joining_native: NativeStateId(11),
            },
            occurrence_fibres: vec![NativeCollapsedFibre {
                native: NativeStateId(11),
                occurrences: BTreeSet::from([EventId(1), EventId(2)]),
            }],
            source_transport,
            rebased_transport,
            source_chart,
            target_chart,
            candidate_coordinates: vec![q(1, 1), q(2, 1)],
            returned_coordinates: vec![q(5, 1), q(7, 1)],
            adjoint_steps: vec![
                CausalAdjointStepInput {
                    name: "candidate-to-overlap".to_owned(),
                    forward: matrix(&[&[(1, 1), (1, 1)], &[(0, 1), (1, 1)]]),
                    domain_metric: matrix(&[&[(2, 1), (0, 1)], &[(0, 1), (1, 1)]]),
                    codomain_metric: middle_metric.clone(),
                },
                CausalAdjointStepInput {
                    name: "overlap-to-return".to_owned(),
                    forward: matrix(&[&[(1, 1), (0, 1)], &[(1, 1), (1, 1)]]),
                    domain_metric: middle_metric,
                    codomain_metric: matrix(&[&[(1, 1), (0, 1)], &[(0, 1), (2, 1)]]),
                },
            ],
            terminal_covector: vec![q(1, 1), q(2, 1)],
            native_obstructions: Vec::new(),
            open_deposition_boundary: "L2-morphology-deposition-not-yet-applied".to_owned(),
            open_exterior: vec!["future-receiver-family".to_owned()],
        }
    }

    #[test]
    fn lawful_rebase_roundtrips_and_preserves_chart_normalized_identity() {
        let section = SituatedDifferenceSection::found(lawful_input()).unwrap();
        assert_eq!(section.chart.oriented_difference, vec![q(2, 1), q(5, 1)]);
        assert_eq!(
            section.chart.transported_difference,
            vec![q(2, 1), q(15, 1)]
        );
        assert_eq!(
            section.chart.rebased_difference,
            section.chart.transported_difference
        );
        let wire = section.canonical_bytes().unwrap();
        assert_eq!(SituatedDifferenceSection::read(&wire).unwrap(), section);

        let mut changed_chart = lawful_input();
        changed_chart.source_chart = ExactRatMatrix::identity(2).unwrap();
        changed_chart.target_chart = matrix(&[&[(0, 1), (1, 1)], &[(1, 1), (0, 1)]]);
        changed_chart.rebased_transport = changed_chart
            .target_chart
            .multiply(&changed_chart.source_transport)
            .unwrap();
        let rebased = SituatedDifferenceSection::found(changed_chart).unwrap();
        assert_eq!(section.identity_sha256, rebased.identity_sha256);
        assert_ne!(section.chart, rebased.chart);
    }

    #[test]
    fn noncommuting_chart_returns_the_exact_defect_sample() {
        let mut input = lawful_input();
        input.rebased_transport = ExactRatMatrix::identity(2).unwrap();
        let SituatedDifferenceError::NoncommutingChart(defect) =
            SituatedDifferenceSection::found(input).unwrap_err()
        else {
            panic!("expected the exact chart obstruction")
        };
        assert!(!defect.is_zero);
        assert!(defect.rank() > 0);
        assert!(defect.sample.is_some());
    }

    #[test]
    fn constitution_changes_identity_while_equal_receiver_faces_do_not_collapse_occurrences() {
        let original = SituatedDifferenceSection::found(lawful_input()).unwrap();
        assert_eq!(
            original.candidate.observation,
            original.returned.observation
        );
        assert_ne!(original.candidate.address, original.returned.address);
        let mut intervention = lawful_input();
        let changed = current(19, -3);
        intervention.returned.emitting_current = changed.clone();
        intervention.returned.constitutive_response.stored = changed;
        let intervened = SituatedDifferenceSection::found(intervention).unwrap();
        assert_ne!(original.identity_sha256, intervened.identity_sha256);
    }

    #[test]
    fn adjoint_is_reverse_order_and_is_not_inverse_transport() {
        let section = SituatedDifferenceSection::found(lawful_input()).unwrap();
        let a = &section.causal_adjoint.steps[0].adjoint;
        let b = &section.causal_adjoint.steps[1].adjoint;
        assert_eq!(
            a.multiply(b).unwrap(),
            section.causal_adjoint.composite_adjoint
        );
        assert_ne!(
            b.multiply(a).unwrap(),
            section.causal_adjoint.composite_adjoint
        );

        let scale = matrix(&[&[(2, 1)]]);
        let adjoint = scale
            .metric_adjoint(
                &ExactRatMatrix::identity(1).unwrap(),
                &ExactRatMatrix::identity(1).unwrap(),
            )
            .unwrap();
        let inverse = scale.inverse().unwrap();
        assert_eq!(adjoint, matrix(&[&[(2, 1)]]));
        assert_eq!(inverse, matrix(&[&[(1, 2)]]));
        assert_ne!(adjoint, inverse);
    }

    #[test]
    fn rectangular_forward_keeps_adjoint_radical_and_fibre_while_inverse_refuses() {
        let rectangular = matrix(&[&[(1, 1), (0, 1), (1, 1)], &[(0, 1), (1, 1), (1, 1)]]);
        let word = CausalAdjointWord::found(
            vec![CausalAdjointStepInput {
                name: "rectangular".to_owned(),
                forward: rectangular,
                domain_metric: ExactRatMatrix::identity(3).unwrap(),
                codomain_metric: ExactRatMatrix::identity(2).unwrap(),
            }],
            vec![q(2, 1), q(3, 1)],
        )
        .unwrap();
        assert_eq!(word.composite_adjoint.rows(), 3);
        assert_eq!(word.composite_adjoint.columns(), 2);
        assert!(matches!(
            word.inverse_transport,
            InverseTransportReceipt::Refused { .. }
        ));
        assert!(word.obstruction.is_none());
        assert!(!word.reconstruction_fibre.particular.is_empty());
    }

    #[test]
    fn wire_refuses_tampered_adjoint_missing_fibre_lineage_and_scalar_only_input() {
        let section = SituatedDifferenceSection::found(lawful_input()).unwrap();

        let mut tampered = section.clone();
        tampered.causal_adjoint.composite_adjoint = ExactRatMatrix::identity(2).unwrap();
        let bytes = serde_json::to_vec(&tampered).unwrap();
        assert!(SituatedDifferenceSection::read(&bytes).is_err());

        let mut fibreless = section.clone();
        fibreless.occurrence_fibres.clear();
        let bytes = serde_json::to_vec(&fibreless).unwrap();
        assert!(SituatedDifferenceSection::read(&bytes).is_err());

        let mut lineage_free = section;
        lineage_free.candidate.ordered_word.clear();
        let bytes = serde_json::to_vec(&lineage_free).unwrap();
        assert!(SituatedDifferenceSection::read(&bytes).is_err());
        assert!(SituatedDifferenceSection::read(br#"{"loss": 0}"#).is_err());
    }
}

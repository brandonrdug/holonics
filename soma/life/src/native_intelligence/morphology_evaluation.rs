//! Configuration-indexed evaluation of the complete native morphology lifecycle.

use std::collections::BTreeSet;

use holonic_engine::{
    native_ecology::holonic_intelligence::{
        conduct_repeated_inference, Bf16ExcitationDismantling, BinaryEmissionCodec,
        ExteriorEmissionCodec, ExteriorModality, ForeignBf16Excitation, InferenceCirculation,
        NativeContinuationDecision, NativeContinuationReceiver, NativeCycleDisposition,
        NativeInferenceAddress, NativeInferenceRequest, NativeTerminationReason,
        NativeVariableGrainEmission, UniqueActualSuccessorReceiver, Utf8InspectionCodec,
    },
    receiver_exact_compression::ReceiverId,
    soulkiller::dismantle,
    BoundaryId, EventId, ExactComplexWaveCurrent,
};
use num_rational::BigRational as Rat;
use serde::Serialize;
use thiserror::Error;

use super::{
    consume_dismantling_return, derive_morphology_anatomy, InferenceConfigurationAddress,
    MorphologyAnatomyManifest, RestedMorphology, ReturnedScaffoldInteraction,
    ScaffoldCultivatedConsequence, ScaffoldCultivatedRest,
};

#[derive(Clone, Debug)]
pub struct MorphologyExperimentInput {
    pub aperture: String,
    pub excitations: Vec<ForeignBf16Excitation>,
    pub receiver: ReceiverId,
    pub exterior_current: ExactComplexWaveCurrent,
    pub storage: Rat,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct StableMorphologyExperimentConsequence {
    pub configuration: InferenceConfigurationAddress,
    pub native_thread_order: Vec<EventId>,
    pub before_withdrawal: ScaffoldCultivatedConsequence,
    pub after_source_detached_remount: ScaffoldCultivatedConsequence,
    pub anatomy: MorphologyAnatomyManifest,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct MorphologyExperimentReceipt {
    pub aperture: String,
    pub cold_modality_order: Vec<ExteriorModality>,
    pub exterior_occurrence_order: Vec<EventId>,
    pub native_thread_order: Vec<EventId>,
    pub chronology_preserved: bool,
    pub cultivation_cut_population: usize,
    pub termination_cut_population: usize,
    pub termination_reason: NativeTerminationReason,
    pub emitted_grain_population: usize,
    pub utf8_surface_octets: usize,
    pub binary_surface_octets: usize,
    pub surfaces_route_native_conduct: bool,
    pub local_causal_cone_population: usize,
    pub outside_cone_morphology_unchanged: bool,
    pub final_hot_thread_population: usize,
    pub package_and_export_controls_separate: bool,
    pub qualitative_surface_is_probe: bool,
    pub stable: StableMorphologyExperimentConsequence,
}

#[derive(Debug, Error)]
pub enum MorphologyEvaluationError {
    #[error("the experiment input is empty or malformed")]
    Input,
    #[error("the morphology lifecycle refused: {0}")]
    Lifecycle(String),
}

struct CultivateReturnedInteraction {
    occurrence: EventId,
    boundary: BoundaryId,
    exterior_current: ExactComplexWaveCurrent,
    storage: Rat,
}

impl NativeContinuationReceiver<ReturnedScaffoldInteraction> for CultivateReturnedInteraction {
    fn receive(
        &self,
        emission: &NativeVariableGrainEmission,
        _successors: &[NativeInferenceRequest],
    ) -> NativeContinuationDecision<ReturnedScaffoldInteraction> {
        let returned = ReturnedScaffoldInteraction::found(
            emission.address.clone(),
            self.occurrence,
            self.boundary,
            self.exterior_current.clone(),
            self.storage.clone(),
            BTreeSet::new(),
        )
        .expect("validated experiment return");
        NativeContinuationDecision::Cultivate {
            returned_occurrence: returned.occurrence,
            returned,
        }
    }
}

pub fn evaluate_morphology_configuration(
    input: MorphologyExperimentInput,
) -> Result<MorphologyExperimentReceipt, MorphologyEvaluationError> {
    if input.aperture.is_empty()
        || input.excitations.is_empty()
        || input.exterior_current.is_zero()
        || input.storage == Rat::from_integer(0.into())
    {
        return Err(MorphologyEvaluationError::Input);
    }
    let cold_modality_order = input
        .excitations
        .iter()
        .map(|excitation| excitation.exterior_modality)
        .collect::<Vec<_>>();
    let exterior_occurrence_order = input
        .excitations
        .iter()
        .map(|excitation| excitation.event)
        .collect::<Vec<_>>();
    let returned_occurrence = EventId(
        exterior_occurrence_order
            .iter()
            .map(|event| event.0)
            .max()
            .ok_or(MorphologyEvaluationError::Input)?
            .checked_add(1)
            .ok_or(MorphologyEvaluationError::Input)?,
    );
    let lifted = dismantle(Bf16ExcitationDismantling {
        receiver: input.receiver,
        excitations: input.excitations,
    })
    .map_err(|error| MorphologyEvaluationError::Lifecycle(error.to_string()))?;
    let native_thread_order = lifted.native.spools[0]
        .threads
        .iter()
        .flat_map(|thread| &thread.occurrences)
        .map(|occurrence| occurrence.occurrence)
        .collect::<Vec<_>>();
    let chronology_preserved = native_thread_order == exterior_occurrence_order;
    if !chronology_preserved {
        return Err(MorphologyEvaluationError::Lifecycle(
            "native lift changed the supplied occurrence order".to_owned(),
        ));
    }
    let source = NativeInferenceAddress {
        spool: lifted.native.spools[0].address.clone(),
        thread: lifted.native.spools[0].threads[0].address.clone(),
        occurrence: lifted.native.spools[0].threads[0].occurrences[0].occurrence,
    };
    let request = NativeInferenceRequest {
        address: source.clone(),
        receiver: input.receiver,
    };
    let termination = conduct_repeated_inference::<(), _>(
        &lifted.native,
        request.clone(),
        &UniqueActualSuccessorReceiver,
    )
    .map_err(|error| MorphologyEvaluationError::Lifecycle(error.to_string()))?;
    let termination_reason = match termination.dispositions.last() {
        Some(NativeCycleDisposition::Terminate { reason, .. }) => *reason,
        Some(NativeCycleDisposition::Obstruct { .. }) => NativeTerminationReason::ReceiverClosed,
        _ => {
            return Err(MorphologyEvaluationError::Lifecycle(
                "the structural termination receiver did not close".to_owned(),
            ));
        }
    };
    let termination_cut_population = termination.cuts.len();
    drop(termination);

    let cultivation = conduct_repeated_inference(
        &lifted.native,
        request,
        &CultivateReturnedInteraction {
            occurrence: returned_occurrence,
            boundary: BoundaryId(returned_occurrence.0.saturating_mul(2)),
            exterior_current: input.exterior_current,
            storage: input.storage,
        },
    )
    .map_err(|error| MorphologyEvaluationError::Lifecycle(error.to_string()))?;
    let cultivation_cut_population = cultivation.cuts.len();
    let emitted_grain_population = cultivation
        .emissions
        .iter()
        .map(|emission| emission.grains.len())
        .sum();
    let face = cultivation
        .cuts
        .first()
        .ok_or(MorphologyEvaluationError::Input)?
        .face();
    let utf8_surface = Utf8InspectionCodec
        .render(face)
        .map_err(|error| MorphologyEvaluationError::Lifecycle(error.to_string()))?;
    let binary_surface = BinaryEmissionCodec
        .render(face)
        .map_err(|error| MorphologyEvaluationError::Lifecycle(error.to_string()))?;
    let returned = match cultivation.dispositions.as_slice() {
        [NativeCycleDisposition::Cultivate { returned, .. }] => returned.clone(),
        _ => {
            return Err(MorphologyEvaluationError::Lifecycle(
                "the returned-interaction receiver did not cultivate".to_owned(),
            ));
        }
    };
    drop(cultivation);
    let (hot, _departed) = consume_dismantling_return(lifted)
        .map_err(|error| MorphologyEvaluationError::Lifecycle(error.to_string()))?;
    let released = ScaffoldCultivatedRest::cultivate(hot, source, returned)
        .and_then(ScaffoldCultivatedRest::release)
        .map_err(|error| MorphologyEvaluationError::Lifecycle(error.to_string()))?;
    let configuration = InferenceConfigurationAddress {
        ingress_aperture: input.aperture.clone(),
        occurrence: exterior_occurrence_order[0],
        receiver: input.receiver,
        continuation_receiver: "returned-local-interaction".to_owned(),
        world_return_law: "emission-indexed-reciprocal-local-current".to_owned(),
        emission_codec: "utf8-and-binary-inspection".to_owned(),
        apparatus: "resident-native-word-and-current".to_owned(),
        stochastic_current: None,
    };
    let before_withdrawal = released.receipt.before_withdrawal.clone();
    let after_source_detached_remount = released.receipt.after_source_detached_remount.clone();
    let local_causal_cone_population = released.receipt.causal_cone_population;
    let outside_cone_morphology_unchanged = released.receipt.outside_cone_morphology_unchanged;
    let final_hot_thread_population = released
        .hot
        .native()
        .spools
        .iter()
        .map(|spool| spool.threads.len())
        .sum();
    let rested = RestedMorphology::situated(released.hot)
        .map_err(|error| MorphologyEvaluationError::Lifecycle(error.to_string()))?;
    let anatomy = derive_morphology_anatomy(&rested)
        .map_err(|error| MorphologyEvaluationError::Lifecycle(error.to_string()))?;
    let stable = StableMorphologyExperimentConsequence {
        configuration,
        native_thread_order: native_thread_order.clone(),
        before_withdrawal,
        after_source_detached_remount,
        anatomy,
    };
    Ok(MorphologyExperimentReceipt {
        aperture: input.aperture,
        cold_modality_order,
        exterior_occurrence_order,
        native_thread_order,
        chronology_preserved,
        cultivation_cut_population,
        termination_cut_population,
        termination_reason,
        emitted_grain_population,
        utf8_surface_octets: utf8_surface.len(),
        binary_surface_octets: binary_surface.len(),
        surfaces_route_native_conduct: false,
        local_causal_cone_population,
        outside_cone_morphology_unchanged,
        final_hot_thread_population,
        package_and_export_controls_separate: true,
        qualitative_surface_is_probe: true,
        stable,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use num_bigint::BigInt;

    fn excitation(
        event: u64,
        modality: ExteriorModality,
        entering: u16,
        returned: u16,
    ) -> ForeignBf16Excitation {
        ForeignBf16Excitation {
            event: EventId(event),
            predecessor: None,
            entering_boundary: BoundaryId(event * 2),
            emitting_boundary: BoundaryId(event * 2 + 1),
            source_occurrence: format!("cold/{event}"),
            exterior_modality: modality,
            entering_codewords: vec![entering],
            returned_codewords: vec![returned],
            interventions: BTreeSet::from([format!("intervention/{event}")]),
            receiver_consequences: BTreeSet::from([format!("consequence/{event}")]),
        }
    }

    #[test]
    fn one_configuration_returns_complete_scope_package_and_export_receipts() {
        let input = MorphologyExperimentInput {
            aperture: "text-control".to_owned(),
            excitations: vec![
                excitation(2, ExteriorModality::Text, 0x3f80, 0x4000),
                excitation(1, ExteriorModality::Image, 0x4040, 0x4080),
            ],
            receiver: ReceiverId(7),
            exterior_current: ExactComplexWaveCurrent::new(
                Rat::from_integer(BigInt::from(1)),
                Rat::from_integer(BigInt::from(1)),
            ),
            storage: Rat::from_integer(BigInt::from(1)),
        };
        let left = evaluate_morphology_configuration(input.clone()).expect("left");
        let right = evaluate_morphology_configuration(input).expect("right");
        assert_eq!(left.stable, right.stable);
        assert!(left.chronology_preserved);
        assert!(!left.surfaces_route_native_conduct);
        assert!(left.package_and_export_controls_separate);
        assert!(left.qualitative_surface_is_probe);
    }
}

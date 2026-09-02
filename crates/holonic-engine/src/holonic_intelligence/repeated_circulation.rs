use std::collections::BTreeSet;

use serde::{Deserialize, Serialize};
use thiserror::Error;

use crate::native_spool::NativeTransportScaffold;
use crate::{EventId, receiver_history_compression::NativeStateId};

use super::{
    InferenceCirculation, NativeEmissionAddress, NativeFutureFace, NativeInferenceAddress,
    NativeInferenceCirculation, NativeInferenceError, NativeInferenceRequest,
    conduct_native_inference,
};

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct NativeEmissionGrain {
    pub future: NativeFutureFace,
    pub occurrences: BTreeSet<EventId>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct NativeVariableGrainEmission {
    pub address: NativeEmissionAddress,
    pub grains: Vec<NativeEmissionGrain>,
    pub selected_grain: usize,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
#[serde(rename_all = "kebab-case")]
pub enum NativeTerminationReason {
    NoActualSuccessor,
    ReceiverClosed,
    CycleClosed,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum NativeContinuationDecision<Returned> {
    Continue(NativeInferenceAddress),
    Terminate(NativeTerminationReason),
    Cultivate {
        returned_occurrence: EventId,
        returned: Returned,
    },
    Obstruct,
}

pub trait NativeContinuationReceiver<Returned> {
    fn receive(
        &self,
        emission: &NativeVariableGrainEmission,
        successors: &[NativeInferenceRequest],
    ) -> NativeContinuationDecision<Returned>;
}

#[derive(Clone, Copy, Debug, Default)]
pub struct UniqueActualSuccessorReceiver;

impl NativeContinuationReceiver<()> for UniqueActualSuccessorReceiver {
    fn receive(
        &self,
        _emission: &NativeVariableGrainEmission,
        successors: &[NativeInferenceRequest],
    ) -> NativeContinuationDecision<()> {
        match successors {
            [] => NativeContinuationDecision::Terminate(NativeTerminationReason::NoActualSuccessor),
            [successor] => NativeContinuationDecision::Continue(successor.address.clone()),
            _ => NativeContinuationDecision::Obstruct,
        }
    }
}

#[derive(Debug)]
pub struct RepeatedNativeInference<'a, Returned> {
    pub morphology: &'a NativeTransportScaffold,
    pub cuts: Vec<NativeInferenceCirculation<'a>>,
    pub emissions: Vec<NativeVariableGrainEmission>,
    pub dispositions: Vec<NativeCycleDisposition<Returned>>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum NativeCycleDisposition<Returned> {
    Continue {
        from: NativeInferenceAddress,
        to: NativeInferenceAddress,
    },
    Terminate {
        at: NativeInferenceAddress,
        reason: NativeTerminationReason,
    },
    Cultivate {
        at: NativeInferenceAddress,
        emitted: NativeEmissionAddress,
        returned_occurrence: EventId,
        returned: Returned,
    },
    Obstruct {
        at: NativeInferenceAddress,
        actual_successors: Vec<NativeInferenceAddress>,
        retained_grains: Vec<NativeEmissionGrain>,
    },
}

#[derive(Debug, Error, PartialEq, Eq)]
pub enum RepeatedInferenceError {
    #[error("one native inference cut refused: {0}")]
    Cut(#[from] NativeInferenceError),
    #[error("the continuation receiver selected a non-successor")]
    FalseSuccessor,
    #[error("a cultivation return reused or preceded its emission occurrence")]
    NonLaterReturn,
    #[error("the variable-grain emission lost a future or its complete occurrence fibre")]
    Grain,
}

pub fn conduct_repeated_inference<'a, Returned: Clone, Receiver>(
    morphology: &'a NativeTransportScaffold,
    first: NativeInferenceRequest,
    receiver: &Receiver,
) -> Result<RepeatedNativeInference<'a, Returned>, RepeatedInferenceError>
where
    Receiver: NativeContinuationReceiver<Returned>,
{
    let mut visited = BTreeSet::new();
    let mut request = first;
    let mut cuts = Vec::new();
    let mut emissions = Vec::new();
    let mut dispositions = Vec::new();
    loop {
        if !visited.insert(request.address.clone()) {
            return Err(RepeatedInferenceError::FalseSuccessor);
        }
        let at = request.address.clone();
        let cut = conduct_native_inference(morphology, request)?;
        let emission = variable_grain(&cut)?;
        let decision = receiver.receive(&emission, cut.successor_requests());
        match decision {
            NativeContinuationDecision::Continue(next) => {
                let Some(successor) = cut
                    .successor_requests()
                    .iter()
                    .find(|successor| successor.address == next)
                    .cloned()
                else {
                    return Err(RepeatedInferenceError::FalseSuccessor);
                };
                if visited.contains(&next) {
                    dispositions.push(NativeCycleDisposition::Terminate {
                        at,
                        reason: NativeTerminationReason::CycleClosed,
                    });
                    cuts.push(cut);
                    emissions.push(emission);
                    break;
                }
                dispositions.push(NativeCycleDisposition::Continue { from: at, to: next });
                cuts.push(cut);
                emissions.push(emission);
                request = successor;
            }
            NativeContinuationDecision::Terminate(reason) => {
                dispositions.push(NativeCycleDisposition::Terminate { at, reason });
                cuts.push(cut);
                emissions.push(emission);
                break;
            }
            NativeContinuationDecision::Cultivate {
                returned_occurrence,
                returned,
            } => {
                if morphology.spools.iter().any(|spool| {
                    spool
                        .threads
                        .iter()
                        .flat_map(|thread| &thread.occurrences)
                        .any(|occurrence| occurrence.occurrence == returned_occurrence)
                }) {
                    return Err(RepeatedInferenceError::NonLaterReturn);
                }
                dispositions.push(NativeCycleDisposition::Cultivate {
                    at,
                    emitted: cut.emitted_occurrence().clone(),
                    returned_occurrence,
                    returned,
                });
                cuts.push(cut);
                emissions.push(emission);
                break;
            }
            NativeContinuationDecision::Obstruct => {
                dispositions.push(NativeCycleDisposition::Obstruct {
                    at,
                    actual_successors: cut
                        .successor_requests()
                        .iter()
                        .map(|successor| successor.address.clone())
                        .collect(),
                    retained_grains: emission.grains.clone(),
                });
                cuts.push(cut);
                emissions.push(emission);
                break;
            }
        }
    }
    Ok(RepeatedNativeInference {
        morphology,
        cuts,
        emissions,
        dispositions,
    })
}

fn variable_grain(
    cut: &NativeInferenceCirculation<'_>,
) -> Result<NativeVariableGrainEmission, RepeatedInferenceError> {
    let face = cut.face();
    let mut grains = Vec::with_capacity(face.plural_futures.len());
    for future in &face.plural_futures {
        let occurrences = cut
            .reconstruction()
            .fibres
            .iter()
            .filter(|fibre| fibre.native == future.to)
            .flat_map(|fibre| fibre.occurrences.iter().copied())
            .collect::<BTreeSet<_>>();
        if occurrences.is_empty() {
            return Err(RepeatedInferenceError::Grain);
        }
        grains.push(NativeEmissionGrain {
            future: *future,
            occurrences,
        });
    }
    if grains.len() != face.plural_futures.len()
        || face.emitted_future >= grains.len()
        || grains
            .iter()
            .map(|grain| grain.future.from)
            .collect::<BTreeSet<NativeStateId>>()
            .len()
            != grains.len()
    {
        return Err(RepeatedInferenceError::Grain);
    }
    Ok(NativeVariableGrainEmission {
        address: cut.emitted_occurrence().clone(),
        grains,
        selected_grain: face.emitted_future,
    })
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeSet;

    use crate::BoundaryId;
    use crate::native_ecology::holonic_intelligence::{
        Bf16ExcitationDismantling, ExteriorModality, ForeignBf16Excitation,
    };
    use crate::receiver_exact_compression::ReceiverId;
    use crate::soulkiller::dismantle;

    use super::*;

    fn excitation(
        event: u64,
        predecessor: Option<u64>,
        entering: u16,
        returned: u16,
    ) -> ForeignBf16Excitation {
        ForeignBf16Excitation {
            event: EventId(event),
            predecessor: predecessor.map(EventId),
            entering_boundary: BoundaryId(event),
            emitting_boundary: BoundaryId(event + 1),
            source_occurrence: format!("cold/{event}"),
            exterior_modality: ExteriorModality::Text,
            entering_codewords: vec![entering],
            returned_codewords: vec![returned],
            interventions: BTreeSet::from([format!("withdraw/{event}")]),
            receiver_consequences: BTreeSet::from([format!("return/{event}")]),
        }
    }

    #[test]
    fn actual_successors_form_a_repeated_variable_grain_circulation() {
        let returned = dismantle(Bf16ExcitationDismantling {
            receiver: ReceiverId(7),
            excitations: vec![
                excitation(1, None, 0x3f80, 0x4000),
                excitation(2, Some(1), 0x4000, 0x4040),
                excitation(3, Some(2), 0x4040, 0x4080),
            ],
        })
        .expect("lift");
        let first = NativeInferenceRequest {
            address: NativeInferenceAddress {
                spool: returned.native.spools[0].address.clone(),
                thread: returned.native.spools[0].threads[0].address.clone(),
                occurrence: EventId(1),
            },
            receiver: ReceiverId(7),
        };
        let repeated = conduct_repeated_inference::<(), _>(
            &returned.native,
            first,
            &UniqueActualSuccessorReceiver,
        )
        .expect("repeated circulation");
        assert_eq!(repeated.cuts.len(), 3);
        assert_eq!(repeated.emissions.len(), 3);
        assert!(matches!(
            repeated.dispositions.last(),
            Some(NativeCycleDisposition::Terminate {
                reason: NativeTerminationReason::NoActualSuccessor,
                ..
            })
        ));
        for pair in repeated.cuts.windows(2) {
            assert_eq!(
                pair[0].emitted_occurrence().entering_occurrence,
                pair[1]
                    .entering_occurrence()
                    .predecessor
                    .expect("predecessor")
            );
        }
    }

    struct CultivationReceiver;

    impl NativeContinuationReceiver<u64> for CultivationReceiver {
        fn receive(
            &self,
            emission: &NativeVariableGrainEmission,
            _successors: &[NativeInferenceRequest],
        ) -> NativeContinuationDecision<u64> {
            NativeContinuationDecision::Cultivate {
                returned_occurrence: EventId(emission.address.entering_occurrence.0 + 100),
                returned: 9,
            }
        }
    }

    #[test]
    fn receiver_can_return_cultivation_without_a_length_or_surface_gate() {
        let returned = dismantle(Bf16ExcitationDismantling {
            receiver: ReceiverId(7),
            excitations: vec![excitation(1, None, 0x3f80, 0x4000)],
        })
        .expect("lift");
        let first = NativeInferenceRequest {
            address: NativeInferenceAddress {
                spool: returned.native.spools[0].address.clone(),
                thread: returned.native.spools[0].threads[0].address.clone(),
                occurrence: EventId(1),
            },
            receiver: ReceiverId(7),
        };
        let repeated = conduct_repeated_inference(&returned.native, first, &CultivationReceiver)
            .expect("cultivation disposition");
        assert!(matches!(
            repeated.dispositions.as_slice(),
            [NativeCycleDisposition::Cultivate { returned: 9, .. }]
        ));
    }

    #[test]
    fn a_plural_actual_successor_family_obstructs_without_selecting_a_surface_branch() {
        let returned = dismantle(Bf16ExcitationDismantling {
            receiver: ReceiverId(7),
            excitations: vec![
                excitation(1, None, 0x3f80, 0x4000),
                excitation(2, Some(1), 0x4000, 0x4040),
                excitation(3, Some(1), 0x4000, 0x4080),
            ],
        })
        .expect("branch lift");
        let first = NativeInferenceRequest {
            address: NativeInferenceAddress {
                spool: returned.native.spools[0].address.clone(),
                thread: returned.native.spools[0].threads[0].address.clone(),
                occurrence: EventId(1),
            },
            receiver: ReceiverId(7),
        };
        let repeated = conduct_repeated_inference::<(), _>(
            &returned.native,
            first,
            &UniqueActualSuccessorReceiver,
        )
        .expect("plural obstruction");
        match repeated.dispositions.as_slice() {
            [
                NativeCycleDisposition::Obstruct {
                    actual_successors,
                    retained_grains,
                    ..
                },
            ] => {
                assert_eq!(actual_successors.len(), 2);
                assert!(!retained_grains.is_empty());
            }
            other => panic!("unexpected disposition {other:?}"),
        }
    }
}

use std::collections::{BTreeMap, BTreeSet};

use crate::native_spool::{
    NativeCollapsedFibre, NativeConstitutiveResponse, NativeGeneratorDescent, NativeIncidenceTerm,
    NativeMutualConstitutiveResponse, NativeOccurrenceSection, NativeParametronCell,
    NativeReceiverConsequence, NativeSerialPullback, NativeSpoolComposition, NativeSpoolRefusal,
    NativeThread, NativeThreadObstruction, NativeThreadOccurrence, NativeTransportScaffold,
};
use crate::receiver_history_compression::{NativeStateId, ReceiverFactor};
use crate::{BoundaryId, EventId};

use super::{
    CarrierRank, CycleRank, DimensionFace, DimensionObstruction, DismantlingBoundaryReturn,
    ExteriorDegree, GeneratorExtent, IncidenceNullity, IncidenceRank, IntrinsicHolonDimensions,
    ReceiverExtent, ReconstructionExtent, RepresentationRank, TopologicalDegree,
};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct BoundaryFacet<'a> {
    pub entering: BoundaryId,
    pub emitting: BoundaryId,
    pub entering_carrier: &'a str,
    pub emitting_carrier: &'a str,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct IncidenceFacet<'a> {
    pub terms: &'a [NativeIncidenceTerm],
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CarrierFacet<'a> {
    pub native_support: &'a BTreeSet<NativeStateId>,
    pub parametrons: &'a [NativeParametronCell],
    pub sections: &'a [NativeOccurrenceSection],
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TransportFacet<'a> {
    pub occurrences: &'a [NativeThreadOccurrence],
    pub chronology: &'a [crate::receiver_exact_compression::InputId],
    pub generator_descents: Vec<&'a NativeGeneratorDescent>,
    pub serial_pullbacks: Vec<&'a NativeSerialPullback>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ConstitutiveFacet<'a> {
    pub local: &'a [NativeConstitutiveResponse],
    pub mutual: Vec<&'a NativeMutualConstitutiveResponse>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReceiverFacet<'a> {
    pub consequences: &'a [NativeReceiverConsequence],
    pub factors: Vec<&'a ReceiverFactor>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReconstructionFacet<'a> {
    pub occurrence_fibre: &'a BTreeSet<EventId>,
    pub collapsed_fibres: Vec<&'a NativeCollapsedFibre>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum OpenScope {
    Thread,
    Spool,
    Scaffold,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct OpenObligation<'a> {
    pub scope: OpenScope,
    pub testimony: &'a str,
}

/// A borrowed intrinsic profile. Every load-bearing facet remains owned by the native scaffold.
#[derive(Debug, PartialEq, Eq)]
pub struct IntrinsicNativeHolonProfile<'a> {
    pub spool_address: &'a str,
    pub thread_address: &'a str,
    pub dimensions: IntrinsicHolonDimensions,
    pub boundary: BoundaryFacet<'a>,
    pub incidence: IncidenceFacet<'a>,
    pub carrier: CarrierFacet<'a>,
    pub transport: TransportFacet<'a>,
    pub constitutive: ConstitutiveFacet<'a>,
    pub receiver: ReceiverFacet<'a>,
    pub morphology: &'a NativeThread,
    pub reconstruction: ReconstructionFacet<'a>,
    pub obstruction: Option<&'a NativeThreadObstruction>,
    pub open_obligations: Vec<OpenObligation<'a>>,
}

/// The complete borrowed profile of one native ecology owner.
#[derive(Debug, PartialEq, Eq)]
pub struct NativeEcologyProfile<'a> {
    pub scaffold_address: &'a str,
    pub holons: Vec<IntrinsicNativeHolonProfile<'a>>,
    pub compositions: &'a [NativeSpoolComposition],
    pub open_obligations: Vec<OpenObligation<'a>>,
}

/// One dismantling return with its productive native holons profiled in place.
#[derive(Debug)]
pub struct ProfiledDismantlingReturn<'a, Return>
where
    Return: DismantlingBoundaryReturn<Productive = NativeTransportScaffold>,
{
    pub returned: &'a Return,
    pub productive_profile: NativeEcologyProfile<'a>,
}

pub fn profile_dismantling_return<Return>(
    returned: &Return,
) -> Result<ProfiledDismantlingReturn<'_, Return>, NativeSpoolRefusal>
where
    Return: DismantlingBoundaryReturn<Productive = NativeTransportScaffold>,
{
    Ok(ProfiledDismantlingReturn {
        productive_profile: returned.productive().intrinsic_holon_profile()?,
        returned,
    })
}

impl NativeTransportScaffold {
    pub fn intrinsic_holon_profile(&self) -> Result<NativeEcologyProfile<'_>, NativeSpoolRefusal> {
        self.validate()?;
        let mut holons = Vec::new();
        for spool in &self.spools {
            for thread in &spool.threads {
                let occurrence_ids = thread
                    .occurrences
                    .iter()
                    .map(|occurrence| occurrence.occurrence)
                    .collect::<BTreeSet<_>>();
                let generator_descents = spool
                    .generator_descents
                    .iter()
                    .filter(|descent| {
                        descent
                            .steps
                            .iter()
                            .any(|step| step.thread == thread.address)
                    })
                    .collect();
                let serial_pullbacks = spool
                    .serial_pullbacks
                    .iter()
                    .filter(|pullback| {
                        pullback.left_thread == thread.address
                            || pullback.right_thread == thread.address
                    })
                    .collect();
                let mutual = spool
                    .mutual_constitutive_responses
                    .iter()
                    .filter(|response| {
                        occurrence_ids.contains(&response.left_occurrence)
                            || occurrence_ids.contains(&response.right_occurrence)
                    })
                    .collect();
                let factors = spool
                    .receiver_factors
                    .iter()
                    .filter(|factor| thread.native_support.contains(&factor.native))
                    .collect();
                let collapsed_fibres = spool
                    .reconstruction_fibres
                    .iter()
                    .filter(|fibre| thread.native_support.contains(&fibre.native))
                    .collect();
                let mut open_obligations = thread
                    .open_exterior
                    .iter()
                    .map(|testimony| OpenObligation {
                        scope: OpenScope::Thread,
                        testimony: testimony.as_str(),
                    })
                    .collect::<Vec<_>>();
                open_obligations.extend(spool.open_exterior.iter().map(|testimony| {
                    OpenObligation {
                        scope: OpenScope::Spool,
                        testimony: testimony.as_str(),
                    }
                }));
                open_obligations.extend(self.open_exterior.iter().map(|testimony| {
                    OpenObligation {
                        scope: OpenScope::Scaffold,
                        testimony: testimony.as_str(),
                    }
                }));
                holons.push(IntrinsicNativeHolonProfile {
                    spool_address: &spool.address,
                    thread_address: &thread.address,
                    dimensions: dimensions(thread),
                    boundary: BoundaryFacet {
                        entering: thread.entering_boundary,
                        emitting: thread.emitting_boundary,
                        entering_carrier: &thread.entering_carrier,
                        emitting_carrier: &thread.emitting_carrier,
                    },
                    incidence: IncidenceFacet {
                        terms: &thread.incidence,
                    },
                    carrier: CarrierFacet {
                        native_support: &thread.native_support,
                        parametrons: &thread.parametrons,
                        sections: &thread.sections,
                    },
                    transport: TransportFacet {
                        occurrences: &thread.occurrences,
                        chronology: &thread.chronology,
                        generator_descents,
                        serial_pullbacks,
                    },
                    constitutive: ConstitutiveFacet {
                        local: &thread.constitutive_responses,
                        mutual,
                    },
                    receiver: ReceiverFacet {
                        consequences: &thread.receiver_consequences,
                        factors,
                    },
                    morphology: thread,
                    reconstruction: ReconstructionFacet {
                        occurrence_fibre: &thread.reconstruction_fibre,
                        collapsed_fibres,
                    },
                    obstruction: thread.obstruction.as_ref(),
                    open_obligations,
                });
            }
        }
        let open_obligations = self
            .open_exterior
            .iter()
            .map(|testimony| OpenObligation {
                scope: OpenScope::Scaffold,
                testimony: testimony.as_str(),
            })
            .collect();
        Ok(NativeEcologyProfile {
            scaffold_address: &self.address,
            holons,
            compositions: &self.compositions,
            open_obligations,
        })
    }
}

fn dimensions(thread: &NativeThread) -> IntrinsicHolonDimensions {
    let (incidence_rank, incidence_nullity, cycle_rank) = graph_dimensions(thread);
    let receiver_extent = thread
        .receiver_consequences
        .iter()
        .map(|consequence| consequence.receiver)
        .collect::<BTreeSet<_>>()
        .len();
    IntrinsicHolonDimensions {
        topological_degree: DimensionFace::Exact(TopologicalDegree(1)),
        incidence_rank: DimensionFace::Exact(IncidenceRank(incidence_rank)),
        incidence_nullity: DimensionFace::Exact(IncidenceNullity(incidence_nullity)),
        cycle_rank: DimensionFace::Exact(CycleRank(cycle_rank)),
        carrier_rank: DimensionFace::Exact(CarrierRank(thread.native_support.len())),
        exterior_degree: DimensionFace::Exact(ExteriorDegree(1)),
        representation_rank: DimensionFace::Exact(RepresentationRank(2)),
        generator_extent: DimensionFace::Exact(GeneratorExtent(thread.chronology.len())),
        receiver_extent: DimensionFace::Exact(ReceiverExtent(receiver_extent)),
        reconstruction_extent: DimensionFace::Exact(ReconstructionExtent(
            thread.reconstruction_fibre.len(),
        )),
        scale_extent: DimensionFace::Open(DimensionObstruction::ScaleChartOutsideNativeThread),
        apparatus_work: DimensionFace::Open(DimensionObstruction::ApparatusWorkOutsideNativeRest),
    }
}

fn graph_dimensions(thread: &NativeThread) -> (usize, usize, usize) {
    let states = thread.native_support.iter().copied().collect::<Vec<_>>();
    let positions = states
        .iter()
        .enumerate()
        .map(|(position, state)| (*state, position))
        .collect::<BTreeMap<_, _>>();
    let mut parent = (0..states.len()).collect::<Vec<_>>();
    for term in &thread.incidence {
        union(&mut parent, positions[&term.from], positions[&term.to]);
    }
    let components = (0..states.len())
        .map(|position| root(&mut parent, position))
        .collect::<BTreeSet<_>>()
        .len();
    let rank = states.len().saturating_sub(components);
    let nullity = thread.incidence.len().saturating_sub(rank);
    (rank, nullity, nullity)
}

fn root(parent: &mut [usize], position: usize) -> usize {
    if parent[position] != position {
        parent[position] = root(parent, parent[position]);
    }
    parent[position]
}

fn union(parent: &mut [usize], left: usize, right: usize) {
    let left = root(parent, left);
    let right = root(parent, right);
    if left != right {
        parent[right] = left;
    }
}

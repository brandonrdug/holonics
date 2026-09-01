//! Architecture-neutral dismantling of one admitted exterior realization section.
//!
//! The boundary consumes already-returned exterior testimony: an addressed reachable section,
//! its receiver/history anatomy, and the apparatus/realization witness for the closed excitation
//! session. It does not execute a model and does not assume any particular attention, recurrence,
//! diffusion, state-space, cache, layer, or tensor factorization. The return is physically split:
//! neutral native spools, cold exterior testimony, and a native receiver insufficiency.

use std::collections::{BTreeMap, BTreeSet};

use num_bigint::BigInt;
use num_traits::{One, Zero};
use relational_geometry::Rat;
use sha2::{Digest, Sha256};
use thiserror::Error;

use crate::{
    BoundaryId, EventId, ExactComplexWaveCurrent, ExactUnitConicPhase, OccurrencePort,
    native_anatomy::NativeAnatomyRest,
    native_spool::{
        NATIVE_SPOOL_SCHEMA, NATIVE_THREAD_SCHEMA, NATIVE_TRANSPORT_SCAFFOLD_SCHEMA,
        NativeCollapsedFibre, NativeConstitutiveResponse, NativeGeneratorDescent,
        NativeGeneratorStep, NativeIncidenceTerm, NativeMutualConstitutiveResponse,
        NativeParametronCell, NativePullbackOccurrence, NativeReceiverConsequence,
        NativeSerialPullback, NativeSpool, NativeSpoolRefusal, NativeThread, NativeThreadHand,
        NativeThreadObstruction, NativeThreadOccurrence, NativeTransportScaffold,
        RECEIVER_INSUFFICIENCY_SCHEMA, ReceiverInsufficiency, ReceiverInsufficiencyCause,
    },
    receiver_exact_compression::{InputId, Observation, ReceiverId},
    receiver_history_compression::{NativeStateId, ReceiverFactor},
    soulkiller_witness::{
        ExteriorSoulkillerWitness, ExteriorSoulkillerWitnessRefusal, ForeignExecutionTestimony,
        ForeignFragmentTestimony, ForeignRealizationTestimony, ForeignShortestSeparator,
        SpoolCondensationWitness, ThreadExtractionWitness,
    },
};

use super::{
    foreign_section_descent::ForeignReachableSectionRest,
    receiver_restricted_transport::{
        ExteriorNativeAnatomyWitness, ReceiverRestrictedFactorRefusal,
    },
};

/// The one-way boundary return. None of its members contains a callable exterior executor.
#[derive(Debug, PartialEq, Eq)]
pub struct SoulkillerScrapyardReturn {
    pub native: NativeTransportScaffold,
    pub exterior: ExteriorSoulkillerWitness,
    pub insufficiency: ReceiverInsufficiency,
}

impl crate::native_ecology::holonic_intelligence::DismantlingBoundaryReturn
    for SoulkillerScrapyardReturn
{
    type Productive = NativeTransportScaffold;
    type ColdWitness = ExteriorSoulkillerWitness;
    type Insufficiency = ReceiverInsufficiency;

    fn productive(&self) -> &Self::Productive {
        &self.native
    }

    fn cold_witness(&self) -> &Self::ColdWitness {
        &self.exterior
    }

    fn insufficiency(&self) -> &Self::Insufficiency {
        &self.insufficiency
    }
}

#[derive(Debug, Error)]
pub enum SoulkillerScrapyardRefusal {
    #[error("the admitted exterior section refused: {0}")]
    Section(String),
    #[error("the exterior anatomy refused: {0}")]
    Anatomy(#[from] ReceiverRestrictedFactorRefusal),
    #[error("the native spool return refused: {0}")]
    Native(#[from] NativeSpoolRefusal),
    #[error("the exterior Soulkiller witness refused: {0}")]
    Witness(#[from] ExteriorSoulkillerWitnessRefusal),
    #[error("the exterior anatomy cannot found one total native generator family")]
    Generator,
    #[error("an exterior lineage address collided inside the bounded native address chart")]
    AddressCollision,
}

/// The admitted terminal receiver address is derived from the exterior section identity, never
/// from a source operator name, source width, operator factorization, or retained-state convention.
pub fn admitted_receiver(section: &ForeignReachableSectionRest) -> ReceiverId {
    ReceiverId(addressed_u64(
        "native-terminal-receiver",
        &section.identity_sha256,
    ))
}

/// Dismantle one admitted exterior section into an architecture-neutral native transport scaffold.
///
/// The two lanes arise from the exact two-member reconstruction fibre carried by every admitted
/// native anatomy class in the present bounded realization. They are plural occurrence populations,
/// not authored layers. A richer or differently populated witness returns `Generator` instead of
/// silently choosing representatives or padding a caller capacity.
pub fn dismantle_reachable_section(
    section: &ForeignReachableSectionRest,
    anatomy: &NativeAnatomyRest,
    exterior_anatomy: &ExteriorNativeAnatomyWitness,
    realization: ForeignRealizationTestimony,
    execution: ForeignExecutionTestimony,
    unexcited_capability: BTreeSet<String>,
) -> Result<SoulkillerScrapyardReturn, SoulkillerScrapyardRefusal> {
    section
        .validate()
        .map_err(|error| SoulkillerScrapyardRefusal::Section(error.to_string()))?;
    anatomy
        .validate()
        .map_err(|error| SoulkillerScrapyardRefusal::Section(error.to_string()))?;
    exterior_anatomy.validate(anatomy)?;

    let receiver = admitted_receiver(section);
    if !execution.admitted_receiver_family.contains(&receiver) {
        return Err(SoulkillerScrapyardRefusal::Generator);
    }
    let exterior_classes = exterior_anatomy
        .classes
        .iter()
        .map(|class| (class.native, class))
        .collect::<BTreeMap<_, _>>();
    if exterior_classes.len() != anatomy.native_population.len() {
        return Err(SoulkillerScrapyardRefusal::Generator);
    }
    let lane_population = exterior_classes
        .values()
        .map(|class| class.occurrences.len())
        .collect::<BTreeSet<_>>();
    let Some(&lanes) = lane_population.iter().next() else {
        return Err(SoulkillerScrapyardRefusal::Generator);
    };
    if lane_population.len() != 1 || lanes < 2 {
        return Err(SoulkillerScrapyardRefusal::Generator);
    }

    let occurrence_testimony = exterior_anatomy
        .occurrences
        .iter()
        .map(|occurrence| (occurrence.occurrence.as_str(), occurrence))
        .collect::<BTreeMap<_, _>>();
    let native_classes = anatomy
        .classes
        .iter()
        .map(|class| (class.native, class))
        .collect::<BTreeMap<_, _>>();
    let native_population = anatomy
        .native_population
        .iter()
        .copied()
        .collect::<BTreeSet<_>>();
    let receiver_factors = anatomy
        .classes
        .iter()
        .map(|class| ReceiverFactor {
            native: class.native,
            receiver,
            observation: Observation(u64::from(class.emitted_native_address)),
        })
        .collect::<Vec<_>>();

    let mut depth_by_native = BTreeMap::<NativeStateId, usize>::new();
    while depth_by_native.len() < native_population.len() {
        let before = depth_by_native.len();
        for class in &anatomy.classes {
            if depth_by_native.contains_key(&class.native)
                || class
                    .predecessor_classes
                    .iter()
                    .any(|predecessor| !depth_by_native.contains_key(predecessor))
            {
                continue;
            }
            let depth = class
                .predecessor_classes
                .iter()
                .map(|predecessor| depth_by_native[predecessor] + 1)
                .max()
                .unwrap_or(0);
            depth_by_native.insert(class.native, depth);
        }
        if depth_by_native.len() == before {
            return Err(SoulkillerScrapyardRefusal::Generator);
        }
    }
    let stages = depth_by_native.values().copied().max().unwrap_or(0) + 1;
    let boundaries = (0..=stages)
        .map(|stage| {
            BoundaryId(addressed_u64(
                "native-section-boundary",
                &format!("{}:{stage}", section.identity_sha256),
            ))
        })
        .collect::<Vec<_>>();

    let mut event_addresses = BTreeMap::<EventId, String>::new();
    let mut event_nodes = BTreeMap::<EventId, (NativeStateId, usize)>::new();
    let mut threads = Vec::with_capacity(lanes * stages);
    let mut lane_threads = Vec::with_capacity(lanes);
    let mut generators = Vec::with_capacity(lanes);
    for lane in 0..lanes {
        let generator_address = format!("native-spool/generator/{lane}");
        let generator = InputId(addressed_u64("native-spool-generator", &generator_address));
        generators.push(generator);
        let mut owned_threads = Vec::with_capacity(stages);
        for stage in 0..stages {
            let address = format!("native-spool/thread/{lane}/section/{stage}");
            let entering_natives = anatomy
                .native_population
                .iter()
                .copied()
                .filter(|native| depth_by_native[native] == stage)
                .collect::<Vec<_>>();
            if entering_natives.is_empty() {
                return Err(SoulkillerScrapyardRefusal::Generator);
            }
            let mut occurrences = Vec::with_capacity(entering_natives.len());
            let mut incidence = Vec::with_capacity(entering_natives.len());
            let mut support = BTreeSet::new();
            let mut reconstruction_fibre = BTreeSet::new();
            let mut obstructed = BTreeSet::new();

            for native in &entering_natives {
                let native_class = native_classes[native];
                let exterior_class = exterior_classes[native];
                let occurrence_address = exterior_class
                    .occurrences
                    .get(lane)
                    .ok_or(SoulkillerScrapyardRefusal::Generator)?;
                let occurrence = occurrence_testimony
                    .get(occurrence_address.as_str())
                    .copied()
                    .ok_or(SoulkillerScrapyardRefusal::Generator)?;
                let event = EventId(addressed_u64(
                    "native-lineage-occurrence",
                    occurrence_address,
                ));
                if let Some(existing) = event_addresses.insert(event, occurrence_address.clone()) {
                    if existing != *occurrence_address {
                        return Err(SoulkillerScrapyardRefusal::AddressCollision);
                    }
                }
                if event_nodes
                    .insert(event, (*native, occurrence.coefficient_node))
                    .is_some()
                {
                    return Err(SoulkillerScrapyardRefusal::AddressCollision);
                }
                let predecessor = occurrence
                    .predecessor_occurrence
                    .as_deref()
                    .map(|address| EventId(addressed_u64("native-lineage-occurrence", address)));
                let to = match native_class.successor_classes.len() {
                    0 => {
                        obstructed.insert(*native);
                        *native
                    }
                    1 => *native_class
                        .successor_classes
                        .iter()
                        .next()
                        .expect("one successor"),
                    _ => return Err(SoulkillerScrapyardRefusal::Generator),
                };
                occurrences.push(NativeThreadOccurrence {
                    occurrence: event,
                    predecessor,
                    entering_port: OccurrencePort::input(event, occurrence.coefficient_node),
                    emitting_port: OccurrencePort::output(event, occurrence.coefficient_node),
                    entering_native: *native,
                    emitting_native: to,
                });
                incidence.push(NativeIncidenceTerm {
                    occurrence: event,
                    from: *native,
                    to,
                    coefficient: 1,
                });
                support.extend([*native, to]);
                reconstruction_fibre.insert(event);
            }

            let mut parametrons = Vec::with_capacity(support.len());
            let mut constitutive_responses = Vec::with_capacity(support.len());
            let mut receiver_consequences = Vec::with_capacity(support.len());
            for native in &support {
                let native_class = native_classes[native];
                let exterior_class = exterior_classes[native];
                let occurrence_address = exterior_class
                    .occurrences
                    .get(lane)
                    .ok_or(SoulkillerScrapyardRefusal::Generator)?;
                let occurrence = occurrence_testimony
                    .get(occurrence_address.as_str())
                    .copied()
                    .ok_or(SoulkillerScrapyardRefusal::Generator)?;
                let stored = exact_node_current(section, occurrence.coefficient_node)?;
                let hand = if stored.imaginary < Rat::zero() {
                    NativeThreadHand::Against
                } else {
                    NativeThreadHand::Along
                };
                let presented = ExactComplexWaveCurrent::one();
                parametrons.push(NativeParametronCell {
                    native: *native,
                    section: presented.clone(),
                    current: stored.clone(),
                    relative_phase: ExactUnitConicPhase::identity(),
                    hand,
                });
                constitutive_responses.push(NativeConstitutiveResponse {
                    native: *native,
                    receiver,
                    presented: presented.clone(),
                    stored,
                });
                receiver_consequences.push(NativeReceiverConsequence {
                    native: *native,
                    receiver,
                    observation: Observation(u64::from(native_class.emitted_native_address)),
                });
            }

            let thread_position = threads.len();
            threads.push(NativeThread {
                schema: NATIVE_THREAD_SCHEMA.to_owned(),
                address,
                entering_boundary: boundaries[stage],
                emitting_boundary: boundaries[stage + 1],
                entering_carrier: "native-complex-parametron-section".to_owned(),
                emitting_carrier: "native-complex-parametron-section".to_owned(),
                occurrences,
                native_support: support,
                incidence,
                parametrons,
                constitutive_responses,
                chronology: vec![generator],
                receiver_consequences,
                obstruction: (!obstructed.is_empty()).then_some(NativeThreadObstruction {
                    boundary: boundaries[stage + 1],
                    receiver: Some(receiver),
                    reason: "the admitted section ends before these native successors return"
                        .to_owned(),
                    retained_native_fibre: obstructed,
                }),
                open_exterior: vec![
                    "successor outside the admitted receiver/history family".to_owned(),
                ],
                reconstruction_fibre,
            });
            owned_threads.push(thread_position);
        }
        lane_threads.push(owned_threads);
    }

    let mut serial_pullbacks = Vec::new();
    for lane in &lane_threads {
        for pair in lane.windows(2) {
            let left = &threads[pair[0]];
            let right = &threads[pair[1]];
            serial_pullbacks.push(NativeSerialPullback {
                left_thread: left.address.clone(),
                right_thread: right.address.clone(),
                joining_boundary: left.emitting_boundary,
                occurrences: complete_pullback(left, right),
            });
        }
    }
    let mut generator_descents = Vec::with_capacity(generators.len());
    for (lane, generator) in lane_threads.iter().zip(&generators) {
        let mut steps = Vec::with_capacity(native_population.len());
        for position in lane {
            let thread = &threads[*position];
            for occurrence in &thread.occurrences {
                steps.push(NativeGeneratorStep {
                    from: occurrence.entering_native,
                    to: occurrence.emitting_native,
                    thread: thread.address.clone(),
                });
            }
        }
        generator_descents.push(NativeGeneratorDescent {
            generator: *generator,
            steps,
        });
    }
    let mut fibres = BTreeMap::<NativeStateId, BTreeSet<EventId>>::new();
    for occurrence in threads.iter().flat_map(|thread| &thread.occurrences) {
        fibres
            .entry(occurrence.emitting_native)
            .or_default()
            .insert(occurrence.occurrence);
    }
    let reconstruction_fibres = fibres
        .into_iter()
        .map(|(native, occurrences)| NativeCollapsedFibre {
            native,
            occurrences,
        })
        .collect::<Vec<_>>();
    let event_nodes = event_nodes.into_iter().collect::<Vec<_>>();
    let mut mutual_constitutive_responses = Vec::new();
    for left in 0..event_nodes.len() {
        for right in left + 1..event_nodes.len() {
            let (left_occurrence, (left_native, left_node)) = event_nodes[left];
            let (right_occurrence, (right_native, right_node)) = event_nodes[right];
            let storage = exact_mutual_storage(section, left_node, right_node)?;
            if storage == Rat::zero() {
                continue;
            }
            mutual_constitutive_responses.push(NativeMutualConstitutiveResponse {
                left_occurrence,
                right_occurrence,
                left_native,
                right_native,
                receiver,
                storage,
            });
        }
    }
    let spool_address = "native-spool/reachable-parametron-section".to_owned();
    let spool = NativeSpool {
        schema: NATIVE_SPOOL_SCHEMA.to_owned(),
        address: spool_address.clone(),
        native_population,
        receiver_family: BTreeSet::from([receiver]),
        generator_family: generators.iter().copied().collect(),
        threads,
        serial_pullbacks,
        generator_descents,
        receiver_factors,
        mutual_constitutive_responses,
        reconstruction_fibres,
        shortest_separators: Vec::new(),
        interchanges: Vec::new(),
        open_exterior: vec!["receiver/history outside the dismantled section".to_owned()],
    };
    let scaffold = NativeTransportScaffold {
        schema: NATIVE_TRANSPORT_SCAFFOLD_SCHEMA.to_owned(),
        address: "native-transport-scaffold/reachable-parametron-section".to_owned(),
        spools: vec![spool],
        compositions: Vec::new(),
        open_exterior: vec!["compatible native spools not yet admitted".to_owned()],
    };
    scaffold.validate()?;

    let fragments = exterior_anatomy
        .occurrences
        .iter()
        .map(|occurrence| ForeignFragmentTestimony {
            address: occurrence.occurrence.clone(),
            coordinates: BTreeMap::from([
                (
                    "coefficient-node".to_owned(),
                    occurrence.coefficient_node.to_string(),
                ),
                (
                    "receiver-class".to_owned(),
                    occurrence.foreign_receiver_class.to_string(),
                ),
                (
                    "history-state".to_owned(),
                    occurrence.inherited_history_state.to_string(),
                ),
                ("section-word".to_owned(), section.identity_sha256.clone()),
            ]),
            interventions: occurrence.realization_addresses.clone(),
        })
        .collect::<Vec<_>>();
    let thread_extractions = scaffold.spools[0]
        .threads
        .iter()
        .map(|thread| ThreadExtractionWitness {
            native_thread: thread.address.clone(),
            founding_fragments: thread
                .occurrences
                .iter()
                .map(|occurrence| event_addresses[&occurrence.occurrence].clone())
                .collect(),
            checked_generator_word: thread.chronology.clone(),
            receiver_family: BTreeSet::from([receiver]),
        })
        .collect::<Vec<_>>();
    let collapsed_fragment_fibres = exterior_anatomy
        .classes
        .iter()
        .map(|class| class.occurrences.iter().cloned().collect::<BTreeSet<_>>())
        .filter(|fibre| fibre.len() > 1)
        .collect::<Vec<_>>();
    let shortest_separators = exterior_anatomy
        .foreign_only_distinctions
        .iter()
        .map(|separator| ForeignShortestSeparator {
            left_fragment: separator.left_occurrence.clone(),
            right_fragment: separator.right_occurrence.clone(),
            receiver,
            word: vec![generators[0]],
        })
        .collect::<Vec<_>>();
    let founding_fragments = fragments
        .iter()
        .map(|fragment| fragment.address.clone())
        .collect::<BTreeSet<_>>();
    let spool_condensations = vec![SpoolCondensationWitness {
        native_spool: spool_address,
        native_threads: thread_extractions
            .iter()
            .map(|extraction| extraction.native_thread.clone())
            .collect(),
        founding_fragments: founding_fragments.clone(),
        collapsed_fragment_fibres,
        shortest_separators,
    }];
    let mut reconstruction_fibre = founding_fragments;
    reconstruction_fibre.extend(unexcited_capability.iter().cloned());
    let exterior = ExteriorSoulkillerWitness::seal(
        &scaffold,
        realization,
        execution,
        fragments,
        thread_extractions,
        spool_condensations,
        reconstruction_fibre,
        unexcited_capability,
        vec!["a later excitation may enlarge the admitted receiver family".to_owned()],
    )?;

    let first_occurrence = scaffold.spools[0].threads[0].occurrences[0].occurrence;
    let first_native = anatomy.native_population[0];
    let retained_fibre = scaffold.spools[0]
        .threads
        .iter()
        .flat_map(|thread| &thread.occurrences)
        .filter(|occurrence| occurrence.entering_native == first_native)
        .map(|occurrence| occurrence.occurrence)
        .collect::<BTreeSet<_>>();
    let requested = ReceiverId(addressed_u64(
        "native-richer-terminal-receiver",
        &section.identity_sha256,
    ));
    let insufficiency = ReceiverInsufficiency {
        schema: RECEIVER_INSUFFICIENCY_SCHEMA.to_owned(),
        at_occurrence: first_occurrence,
        native: first_native,
        retained_fibre,
        cause: ReceiverInsufficiencyCause::ReceiverOutsideFamily {
            requested,
            admitted: BTreeSet::from([receiver]),
        },
        open_exterior: vec!["the richer receiver reopens the retained occurrence fibre".to_owned()],
    };
    insufficiency.validate()?;
    Ok(SoulkillerScrapyardReturn {
        native: scaffold,
        exterior,
        insufficiency,
    })
}

fn exact_node_current(
    section: &ForeignReachableSectionRest,
    node: usize,
) -> Result<ExactComplexWaveCurrent, SoulkillerScrapyardRefusal> {
    if section
        .sections
        .iter()
        .any(|carrier| node >= carrier.columns)
    {
        return Err(SoulkillerScrapyardRefusal::Generator);
    }
    let mut terminal_standing = BigInt::zero();
    let mut turn = BigInt::zero();
    for carrier in &section.sections {
        let first = carrier.entries[node];
        let last = carrier.entries[(carrier.rows - 1) * carrier.columns + node];
        terminal_standing += BigInt::from(last);
        turn += BigInt::from(last) - BigInt::from(first);
    }
    Ok(ExactComplexWaveCurrent::new(
        Rat::from_integer(terminal_standing),
        Rat::from_integer(turn),
    ))
}

/// Pull back the declared identity branch-storage receiver through every captured carrier section.
/// A nonzero off-diagonal entry is the exact mutual constitutive response between the two
/// coefficient occurrences. Grain is retained in the denominator; no floating coordinate or
/// correlation threshold decides contact.
fn exact_mutual_storage(
    section: &ForeignReachableSectionRest,
    left: usize,
    right: usize,
) -> Result<Rat, SoulkillerScrapyardRefusal> {
    let mut total = Rat::zero();
    for carrier in &section.sections {
        if left >= carrier.columns || right >= carrier.columns {
            return Err(SoulkillerScrapyardRefusal::Generator);
        }
        let mut numerator = BigInt::zero();
        for row in 0..carrier.rows {
            numerator += BigInt::from(carrier.entries[row * carrier.columns + left])
                * BigInt::from(carrier.entries[row * carrier.columns + right]);
        }
        let denominator = BigInt::one() << (2 * carrier.grain as usize);
        total += Rat::new(numerator, denominator);
    }
    Ok(total)
}

fn complete_pullback(
    left: &NativeThread,
    right: &NativeThread,
) -> BTreeSet<NativePullbackOccurrence> {
    left.occurrences
        .iter()
        .flat_map(|left_occurrence| {
            right
                .occurrences
                .iter()
                .filter_map(move |right_occurrence| {
                    (left_occurrence.emitting_native == right_occurrence.entering_native).then_some(
                        NativePullbackOccurrence {
                            left: left_occurrence.occurrence,
                            right: right_occurrence.occurrence,
                            joining_native: left_occurrence.emitting_native,
                        },
                    )
                })
        })
        .collect()
}

fn addressed_u64(domain: &str, material: &str) -> u64 {
    let mut digest = Sha256::new();
    digest.update((domain.len() as u64).to_le_bytes());
    digest.update(domain.as_bytes());
    digest.update((material.len() as u64).to_le_bytes());
    digest.update(material.as_bytes());
    let bytes = digest.finalize();
    u64::from_le_bytes(bytes[..8].try_into().expect("eight digest octets"))
}

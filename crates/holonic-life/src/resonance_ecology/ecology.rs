use super::*;

/// One direct conditioned ecology. The receptor registry is a world-owned population of exact
/// continuing receiver capabilities, not an association table: it contains no pair of informants,
/// target, score, or returned deed. Standing and Swing remain the only persistent relation owner.
pub struct ResonanceEcology {
    machine: LiveCurrentMachine,
    receptors: GrowingKeyAtlas<ResonanceReceptorKey, Option<NativeRelationOrgan>>,
}

impl ResonanceEcology {
    pub fn new(machine: LiveCurrentMachine) -> Self {
        Self {
            machine,
            receptors: GrowingKeyAtlas::new(),
        }
    }

    pub const fn machine(&self) -> &LiveCurrentMachine {
        &self.machine
    }

    /// Declare the chronology a standing factor must cross the seam closure's aperture within.
    ///
    /// Forwarded to the live machine, which rebuilds its aperture under the new declaration. The
    /// inherited setting admits every factor whole; see `LiveCurrentMachine::declare_traversal_horizon`.
    pub fn declare_traversal_horizon(&mut self, horizon: u64) {
        self.machine.declare_traversal_horizon(horizon);
    }

    pub fn rest_image(&self) -> Result<ResonanceEcologyRestImage, ResonanceEcologyError> {
        Ok(ResonanceEcologyRestImage {
            machine: self.machine.rest_image()?,
            receptors: self
                .receptors
                .iter()
                .map(|(key, organ)| {
                    (
                        key.clone(),
                        organ
                            .as_ref()
                            .expect("a resting resonance ecology retains every receptor organ")
                            .checkpoint(),
                    )
                })
                .collect(),
        })
    }

    pub fn from_rest_image(
        image: ResonanceEcologyRestImage,
    ) -> Result<Self, ResonanceEcologyError> {
        let ResonanceEcologyRestImage {
            machine: machine_image,
            receptors: receptor_images,
        } = image;
        let machine = LiveCurrentMachine::from_rest_image(machine_image)?;
        let mut receptors = GrowingKeyAtlas::new();
        receptors.try_reserve_new_keys(receptor_images.len())?;
        for (key, image) in receptor_images {
            let organ = NativeRelationOrgan::recover(image, &machine)
                .map_err(ResonanceEcologyError::from)?;
            if receptors.try_insert(key, Some(organ))?.is_some() {
                return Err(ResonanceEcologyError::MalformedRadiation);
            }
        }
        Ok(Self { machine, receptors })
    }

    pub fn receive(
        &mut self,
        occurrence: &ResonanceOccurrence,
        action: ActionCurrent,
    ) -> Result<ResonanceRadiation, ResonanceEcologyError> {
        let mut cpu = CpuLiveCurrentExecutor;
        self.receive_with(occurrence, action, &mut cpu)
    }

    pub fn receive_with(
        &mut self,
        occurrence: &ResonanceOccurrence,
        action: ActionCurrent,
        executor: &mut dyn LiveCurrentExecutor,
    ) -> Result<ResonanceRadiation, ResonanceEcologyError> {
        let configuration =
            self.receive_configuration_with(std::slice::from_ref(occurrence), action, executor)?;
        let ResonanceConfigurationRadiation { source, reads } = configuration;
        if source.regional().len() != 1 {
            return Err(ResonanceEcologyError::MalformedRadiation);
        }
        let read = reads
            .into_iter()
            .next()
            .ok_or(ResonanceEcologyError::MalformedRadiation)?
            .constituent;
        Ok(ResonanceRadiation { source, read })
    }

    /// Receive a continuation question and return every exact successor germ exposed by its
    /// terminal boundary. Candidate discovery follows the production aperture into the returned
    /// constituent; it does not enumerate vocabulary, corpus rows, or receptor population.
    pub fn receive_and_emanate(
        &mut self,
        occurrence: &ResonanceOccurrence,
        action: ActionCurrent,
    ) -> Result<ResonanceEmanation, ResonanceEcologyError> {
        let mut cpu = CpuLiveCurrentExecutor;
        self.receive_and_emanate_with(occurrence, action, &mut cpu)
    }

    pub fn receive_and_emanate_with(
        &mut self,
        occurrence: &ResonanceOccurrence,
        action: ActionCurrent,
        executor: &mut dyn LiveCurrentExecutor,
    ) -> Result<ResonanceEmanation, ResonanceEcologyError> {
        if !occurrence.continuation_exposure {
            return Err(ResonanceEcologyError::ContinuationNotExposed);
        }
        let radiation = self.receive_with(occurrence, action, executor)?;
        let mut targets = BTreeMap::<ReceiverFiberIdentity, BTreeSet<ReceiverFiberIdentity>>::new();
        for leader in &occurrence.continuation_leaders {
            for target in radiation
                .read
                .continuations_after(&leader.identity)
                .into_iter()
                .flatten()
            {
                targets
                    .entry(target.clone())
                    .or_default()
                    .insert(leader.identity.clone());
            }
        }
        let mut branches = Vec::new();
        for (target, supporting_leaders) in targets {
            let supporting_leaders = Arc::new(supporting_leaders);
            let lower = ResonanceReceptorKey {
                role: GERM_RECEPTOR,
                identity: target.clone(),
                phase: [0; COG_WORDS],
            };
            let upper = ResonanceReceptorKey {
                role: GERM_RECEPTOR,
                identity: target,
                phase: [u32::MAX; COG_WORDS],
            };
            for (key, _) in self.receptors.range_inclusive(&lower, &upper) {
                let phase = RelationAtom::from_words(key.phase)
                    .ok_or(ResonanceEcologyError::MalformedRadiation)?;
                branches.push(ResonanceEmanatedBranch {
                    germ: ResonanceGerm::new(key.identity.clone(), phase),
                    supporting_leaders: Arc::clone(&supporting_leaders),
                });
            }
        }
        Ok(ResonanceEmanation {
            radiation,
            prefix: occurrence.germs.clone(),
            branches,
        })
    }

    /// Receive independently delivered informants as one caused configuration. Their slice order
    /// is not promoted to chronology; each occurrence's own ordered boundary remains physical.
    pub fn receive_configuration(
        &mut self,
        occurrences: &[ResonanceOccurrence],
        action: ActionCurrent,
    ) -> Result<ResonanceConfigurationRadiation, ResonanceEcologyError> {
        let mut cpu = CpuLiveCurrentExecutor;
        self.receive_configuration_with(occurrences, action, &mut cpu)
    }

    /// Execute one co-present configuration through a caller-retained physical executor.
    pub fn receive_configuration_with(
        &mut self,
        occurrences: &[ResonanceOccurrence],
        action: ActionCurrent,
        executor: &mut dyn LiveCurrentExecutor,
    ) -> Result<ResonanceConfigurationRadiation, ResonanceEcologyError> {
        if occurrences.is_empty() {
            return Err(ResonanceEcologyError::EmptyConfiguration);
        }
        let capacity_atom = RelationAtom::new(Cog::lit(CAPACITY_ATOM))
            .ok_or(ResonanceEcologyError::CarrierExtent)?;
        let mut charts = Vec::new();
        let mut chart_by_informant = BTreeMap::new();
        for (occurrence_at, occurrence) in occurrences.iter().enumerate() {
            let phases = occurrence
                .germs
                .iter()
                .map(ResonanceGerm::phase)
                .collect::<Vec<_>>();
            charts.push(NativePathChart::new(&phases)?);
            if let Some(identity) = occurrence.identity.as_ref() {
                if chart_by_informant.insert(identity, occurrence_at).is_some() {
                    return Err(ResonanceEcologyError::DuplicateInformant);
                }
            }
        }
        let mut active_keys = BTreeSet::new();
        for occurrence in occurrences {
            active_keys.extend(occurrence.germs.iter().map(ResonanceReceptorKey::from));
            active_keys.extend(
                occurrence
                    .continuation_leaders
                    .iter()
                    .map(ResonanceReceptorKey::from),
            );
            if let Some(identity) = occurrence.identity.as_ref() {
                active_keys.insert(informant_receptor_key(
                    INFORMANT_MARKER_RECEPTOR,
                    identity,
                    capacity_atom,
                ));
                active_keys.insert(informant_receptor_key(
                    INFORMANT_CAPACITY_RECEPTOR,
                    identity,
                    capacity_atom,
                ));
            }
        }
        let key_indices = active_keys
            .iter()
            .cloned()
            .enumerate()
            .map(|(at, key)| (key, at))
            .collect::<BTreeMap<_, _>>();
        let ephemeral_count = occurrences
            .iter()
            .filter(|occurrence| occurrence.identity.is_none())
            .count();
        let persistent_count = active_keys.len();
        let mut layouts = Vec::new();
        let mut ephemeral_charts = Vec::new();
        let mut next_ephemeral = persistent_count;
        for (occurrence_at, occurrence) in occurrences.iter().enumerate() {
            let (informant, center) = match occurrence.identity.as_ref() {
                Some(identity) => {
                    let marker = key_indices
                        .get(&informant_receptor_key(
                            INFORMANT_MARKER_RECEPTOR,
                            identity,
                            capacity_atom,
                        ))
                        .copied()
                        .ok_or(ResonanceEcologyError::MalformedRadiation)?;
                    let center = key_indices
                        .get(&informant_receptor_key(
                            INFORMANT_CAPACITY_RECEPTOR,
                            identity,
                            capacity_atom,
                        ))
                        .copied()
                        .ok_or(ResonanceEcologyError::MalformedRadiation)?;
                    (Some((marker, identity)), center)
                }
                None => {
                    let center = next_ephemeral;
                    next_ephemeral += 1;
                    ephemeral_charts.push(occurrence_at);
                    (None, center)
                }
            };
            let exposed_slot = u32::try_from(occurrence.germs.len().saturating_sub(2))
                .map_err(|_| ResonanceEcologyError::CarrierExtent)?;
            layouts.push((informant, center, exposed_slot));
        }
        let total_currents = persistent_count
            .checked_add(ephemeral_count)
            .ok_or(ResonanceEcologyError::CarrierExtent)?;
        if next_ephemeral != total_currents || ephemeral_charts.len() != ephemeral_count {
            return Err(ResonanceEcologyError::CarrierExtent);
        }

        let new_receptors = active_keys
            .iter()
            .filter(|key| !self.receptors.contains(*key))
            .count();
        self.receptors.try_reserve_new_keys(new_receptors)?;
        let mut active_organs = Vec::with_capacity(active_keys.len());
        for key in active_keys.iter().cloned() {
            let organ = self
                .receptors
                .get_mut(&key)
                .map(|slot| {
                    slot.take()
                        .expect("a resting resonance receptor cannot already be in flight")
                })
                .unwrap_or_else(NativeRelationOrgan::new);
            active_organs.push((key, organ));
        }
        let mut ephemeral_organs = (0..ephemeral_count)
            .map(|_| NativeRelationOrgan::new())
            .collect::<Vec<_>>();
        let source_result = (|| -> Result<ContemporaryRadiation, ResonanceEcologyError> {
            let mut currents = Vec::new();
            currents
                .try_reserve_exact(total_currents)
                .map_err(|_| ResonanceEcologyError::CarrierExtent)?;
            for (key, organ) in &mut active_organs {
                if key.role == INFORMANT_CAPACITY_RECEPTOR {
                    let chart = chart_by_informant
                        .get(&key.identity)
                        .and_then(|at| charts.get(*at))
                        .ok_or(ResonanceEcologyError::MalformedRadiation)?;
                    currents.push(NativeEventCurrent::continuing_complex(
                        organ,
                        chart.complex(),
                        action,
                    ));
                } else {
                    let phase = RelationAtom::from_words(key.phase)
                        .ok_or(ResonanceEcologyError::CarrierExtent)?;
                    currents.push(NativeEventCurrent::continuing(organ, phase, action));
                }
            }
            for (organ, chart_at) in ephemeral_organs.iter_mut().zip(&ephemeral_charts) {
                let chart = charts
                    .get(*chart_at)
                    .ok_or(ResonanceEcologyError::MalformedRadiation)?;
                currents.push(NativeEventCurrent::ending_complex(
                    organ,
                    chart.complex(),
                    action,
                ));
            }

            let mut arcs_by_occurrence = Vec::new();
            for (occurrence, (informant, center, exposed_slot)) in occurrences.iter().zip(&layouts)
            {
                let consequent_order = occurrence
                    .source_order
                    .checked_add(1)
                    .ok_or(ResonanceEcologyError::Chronology)?;
                let mut fibers = Vec::new();
                if let Some((at, identity)) = informant {
                    fibers.push((*at, (*identity).clone(), role_fiber(INFORMANT_ROLE_WORD)));
                }
                for germ in &occurrence.germs {
                    let key = ResonanceReceptorKey::from(germ);
                    let at = key_indices
                        .get(&key)
                        .copied()
                        .ok_or(ResonanceEcologyError::MalformedRadiation)?;
                    fibers.push((at, germ.identity.clone(), role_fiber(GERM_ROLE_WORD)));
                }
                if occurrence.continuation_exposure {
                    let first = occurrence
                        .germs
                        .first()
                        .ok_or(ResonanceEcologyError::EmptyOccurrence)?;
                    let first_at = key_indices
                        .get(&ResonanceReceptorKey::from(first))
                        .copied()
                        .ok_or(ResonanceEcologyError::MalformedRadiation)?;
                    fibers.push((
                        first_at,
                        first.identity.clone(),
                        role_fiber(origin_role_word(occurrence.origin)),
                    ));
                    if occurrence.path_continuations {
                        for adjacent in occurrence.germs.windows(2) {
                            let source = &adjacent[0];
                            let target = &adjacent[1];
                            let source_at = key_indices
                                .get(&ResonanceReceptorKey::from(source))
                                .copied()
                                .ok_or(ResonanceEcologyError::MalformedRadiation)?;
                            let target_at = key_indices
                                .get(&ResonanceReceptorKey::from(target))
                                .copied()
                                .ok_or(ResonanceEcologyError::MalformedRadiation)?;
                            fibers.push((
                                source_at,
                                source.identity.clone(),
                                role_fiber(CONTINUATION_SOURCE_ROLE_WORD),
                            ));
                            fibers.push((
                                target_at,
                                target.identity.clone(),
                                continuation_target_role(&source.identity)?,
                            ));
                        }
                    }
                    for (source, target) in &occurrence.explicit_continuations {
                        let source_at = key_indices
                            .get(&ResonanceReceptorKey::from(source))
                            .copied()
                            .ok_or(ResonanceEcologyError::MalformedRadiation)?;
                        let target_at = key_indices
                            .get(&ResonanceReceptorKey::from(target))
                            .copied()
                            .ok_or(ResonanceEcologyError::MalformedRadiation)?;
                        fibers.push((
                            source_at,
                            source.identity.clone(),
                            role_fiber(CONTINUATION_SOURCE_ROLE_WORD),
                        ));
                        fibers.push((
                            target_at,
                            target.identity.clone(),
                            continuation_target_role(&source.identity)?,
                        ));
                    }
                    if let Some(testimony) = &occurrence.routed_testimony {
                        let leader = occurrence
                            .germs
                            .first()
                            .ok_or(ResonanceEcologyError::EmptyOccurrence)?;
                        let leader_at = key_indices
                            .get(&ResonanceReceptorKey::from(leader))
                            .copied()
                            .ok_or(ResonanceEcologyError::MalformedRadiation)?;
                        fibers.push((
                            leader_at,
                            testimony.clone(),
                            role_fiber(INFORMANT_ROLE_WORD),
                        ));
                    }
                    for (source, target) in &occurrence.routed_continuations {
                        let source_at = key_indices
                            .get(&ResonanceReceptorKey::from(source))
                            .copied()
                            .ok_or(ResonanceEcologyError::MalformedRadiation)?;
                        fibers.push((
                            source_at,
                            source.identity.clone(),
                            role_fiber(CONTINUATION_SOURCE_ROLE_WORD),
                        ));
                        fibers.push((
                            source_at,
                            target.clone(),
                            continuation_target_role(&source.identity)?,
                        ));
                    }
                    for leader in &occurrence.continuation_leaders {
                        let leader_at = key_indices
                            .get(&ResonanceReceptorKey::from(leader))
                            .copied()
                            .ok_or(ResonanceEcologyError::MalformedRadiation)?;
                        fibers.push((
                            leader_at,
                            leader.identity.clone(),
                            role_fiber(CONTINUATION_SOURCE_ROLE_WORD),
                        ));
                    }
                }
                let arcs = fibers
                    .into_iter()
                    .enumerate()
                    .map(|(slot, (from, antecedent_fiber, consequent_fiber))| {
                        let passage = ReceiverCausalPassage::with_fiber(
                            soma_membrane::ReceiverChartIdentity::new(GERM_RECEIVER_CHART),
                            antecedent_fiber,
                            occurrence.source_order,
                            soma_membrane::ReceiverChartIdentity::new(CAPACITIVE_RECEIVER_CHART),
                            consequent_fiber,
                            consequent_order,
                        )
                        .map_err(|_| ResonanceEcologyError::Chronology)?;
                        Ok(NativeRegionalArc::from_receiver_passage(
                            from,
                            CurrentBoundaryPort::Cell,
                            *center,
                            CurrentBoundaryPort::Exposed(*exposed_slot),
                            passage,
                            u32::try_from(slot)
                                .map_err(|_| ResonanceEcologyError::CarrierExtent)?,
                            0,
                            IncidenceHand::Against,
                        ))
                    })
                    .collect::<Result<Vec<_>, ResonanceEcologyError>>()?;
                arcs_by_occurrence.push(arcs);
            }
            let regional = arcs_by_occurrence
                .iter()
                .zip(&layouts)
                .map(|(arcs, (_, center, _))| NativeRegionalRelation::new(*center, arcs))
                .collect::<Vec<_>>();
            Ok(present_native_event_with_regional(
                &mut self.machine,
                executor,
                &mut currents,
                &[],
                &regional,
            )?)
        })();
        for (key, organ) in active_organs {
            if let Some(slot) = self.receptors.get_mut(&key) {
                assert!(
                    slot.replace(organ).is_none(),
                    "a receptor cannot return twice"
                );
            } else {
                assert!(
                    self.receptors
                        .try_insert(key, Some(organ))
                        .expect("the receptor population was pre-reserved")
                        .is_none(),
                    "a new receptor key cannot already be standing"
                );
            }
        }
        let source = source_result?;
        assert_eq!(
            source.regional().len(),
            occurrences.len(),
            "the live regional membrane must return one constituent per admitted occurrence"
        );
        let mut reads = LocalSequence::with_capacity(source.regional().len());
        for (occurrence, returned) in occurrences.iter().zip(source.regional()) {
            assert!(
                !returned.support_transitions().is_empty()
                    && returned
                        .support_transitions()
                        .iter()
                        .all(|transitions| !transitions.is_empty()),
                "an admitted live constituent must expose its complete support transition"
            );
            let constituent = ResonanceConstituentRead::from_constituent(returned.constituent())?;
            // The occurrence's declared germ ports are its exact constitutive interface family.
            // Informant markers and any other co-present pins remain in the constituent receipt,
            // but cannot complete this conduct merely because one of them happened to ride.
            let germ_role = role_fiber(GERM_ROLE_WORD);
            let mut required = LocalSet::new();
            for identity in &occurrence.required_germ_ports {
                required.try_insert(ResonancePinPort {
                    antecedent: identity.clone(),
                    consequent: germ_role.clone(),
                })?;
            }
            let mut returned_interfaces = LocalSet::new();
            let mut carried_ports = LocalSet::new();
            for interface in constituent.interfaces() {
                let port = ResonancePinPort {
                    antecedent: interface.antecedent().clone(),
                    consequent: interface.consequent().clone(),
                };
                if !required.contains(&port) {
                    continue;
                }
                returned_interfaces.try_insert(interface.clone())?;
                if interface.conduct() == ResonancePinConduct::Riding {
                    carried_ports.try_insert(port)?;
                }
            }
            let complete = required.iter().all(|port| carried_ports.contains(port));
            let conduct = if complete {
                ResonanceOccurrenceConduct::Complete {
                    required,
                    returned: returned_interfaces,
                }
            } else {
                ResonanceOccurrenceConduct::Open {
                    required,
                    returned: returned_interfaces,
                }
            };
            reads.push(ResonanceOccurrenceRead {
                occurrence: occurrence.identity().cloned(),
                constituent,
                conduct,
            });
        }
        Ok(ResonanceConfigurationRadiation { source, reads })
    }
}

use super::*;

#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct BoundaryBucket {
    starts: Vec<usize>,
    ends: Vec<usize>,
}

#[derive(Clone, Debug)]
struct TransportedCell {
    section: usize,
    cell: usize,
    begin: ExactOccurrenceTime,
    end: ExactOccurrenceTime,
}

#[derive(Clone, Debug)]
pub(super) struct OwnedEventComplex {
    cells: Vec<EventCell>,
    incidences: Vec<OrientedIncidence>,
    ports: Vec<EventPort>,
}

#[derive(Clone, Copy, Debug)]
struct ReceiverCellPort {
    current: usize,
    port: CurrentBoundaryPort,
}

impl OwnedEventComplex {
    fn view(&self) -> Result<EventComplex<'_>, SynchronizedOccurrenceError> {
        EventComplex::new(&self.cells, &self.incidences, &self.ports)
            .map_err(|_| SynchronizedOccurrenceError::MalformedOccurrence)
    }
}

#[derive(Clone, Debug)]
pub(super) struct OwnedRelation {
    pub(super) receiver: usize,
    pub(super) arcs: Vec<NativeRegionalArc>,
    pub(super) support_slots: Vec<Vec<u32>>,
    contact: Option<SynchronizedContactOccurrence>,
}

#[derive(Clone, Debug)]
pub(super) struct DerivedOccurrence {
    pub(super) receiver_complexes: Vec<OwnedEventComplex>,
    pub(super) horizons: Vec<(ExactOccurrenceTime, ExactOccurrenceTime)>,
    directed: Vec<NativeEventRelation>,
    pub(super) relations: Vec<OwnedRelation>,
    pub(super) elementary_intervals: u64,
    local_sequence_relations: u64,
}

/// Source-neutral synchronized occurrence chart over the production Swing.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct SynchronizedOccurrenceChart;

impl SynchronizedOccurrenceChart {
    pub fn new() -> Self {
        Self
    }

    pub fn observe(
        &mut self,
        machine: &mut LiveCurrentMachine,
        occurrence: &ExactSynchronizedOccurrence,
        action: ActionCurrent,
    ) -> Result<SynchronizedOccurrenceRadiation, SynchronizedOccurrenceError> {
        let mut cpu = CpuLiveCurrentExecutor;
        self.observe_with(machine, &mut cpu, occurrence, action)
    }

    pub fn observe_with(
        &mut self,
        machine: &mut LiveCurrentMachine,
        executor: &mut dyn LiveCurrentExecutor,
        occurrence: &ExactSynchronizedOccurrence,
        action: ActionCurrent,
    ) -> Result<SynchronizedOccurrenceRadiation, SynchronizedOccurrenceError> {
        occurrence.validate()?;
        let derived = derive_occurrence(occurrence, self)?;

        let current_count = derived
            .receiver_complexes
            .len()
            .checked_add(derived.horizons.len())
            .ok_or(SynchronizedOccurrenceError::CarrierOverflow)?;
        let mut organs = Vec::new();
        organs
            .try_reserve_exact(current_count)
            .map_err(|_| SynchronizedOccurrenceError::CarrierOverflow)?;
        organs.resize_with(current_count, NativeRelationOrgan::new);

        let receiver_views = derived
            .receiver_complexes
            .iter()
            .map(OwnedEventComplex::view)
            .collect::<Result<Vec<_>, _>>()?;
        let (receiver_organs, horizon_organs) =
            organs.split_at_mut(derived.receiver_complexes.len());
        let mut currents = Vec::new();
        currents
            .try_reserve_exact(current_count)
            .map_err(|_| SynchronizedOccurrenceError::CarrierOverflow)?;
        for (organ, complex) in receiver_organs.iter_mut().zip(receiver_views) {
            currents.push(NativeEventCurrent::ending_complex(organ, complex, action));
        }
        for organ in horizon_organs {
            currents.push(NativeEventCurrent::ending(
                organ,
                occurrence.horizon_material,
                action,
            ));
        }

        let support = derived
            .relations
            .iter()
            .map(|relation| {
                relation
                    .support_slots
                    .iter()
                    .map(|slots| RegionalSupportSection::new(slots))
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();
        let regional = derived
            .relations
            .iter()
            .zip(&support)
            .map(|(relation, support)| {
                NativeRegionalRelation::with_support_sections(
                    relation.receiver,
                    &relation.arcs,
                    support,
                )
            })
            .collect::<Vec<_>>();

        let source = present_native_event_with_regional(
            machine,
            executor,
            &mut currents,
            &derived.directed,
            &regional,
        )?;
        // The direct membrane has already checked executor population equality before committing.
        // This is an implementation invariant, not a second fallible observer verdict after the
        // live body changed.
        assert_eq!(
            source.regional().len(),
            derived.relations.len(),
            "the committed direct radiation retains one row per presented regional relation"
        );

        let mut contacts = Vec::new();
        for (relation, radiation) in derived.relations.iter().zip(source.regional()) {
            let Some(contact) = relation.contact.clone() else {
                continue;
            };
            let boundary_transitions = radiation
                .support_transitions()
                .iter()
                .flatten()
                .copied()
                .collect::<Vec<_>>();
            assert!(
                !boundary_transitions.is_empty(),
                "a committed synchronized contact retains at least one support transition"
            );
            let formed_ride = boundary_transitions.contains(&LiveBoundaryTransition::Ride);
            let formed_found = boundary_transitions.contains(&LiveBoundaryTransition::Found);
            let open = boundary_transitions.contains(&LiveBoundaryTransition::Open);
            contacts.push(SynchronizedContactRadiation {
                contact,
                boundary_transitions,
                formed_ride,
                formed_found,
                open,
            });
        }

        Ok(SynchronizedOccurrenceRadiation {
            occurrence: occurrence.occurrence,
            source,
            contacts,
            elementary_intervals: derived.elementary_intervals,
            local_sequence_relations: derived.local_sequence_relations,
        })
    }

    pub fn contacts(
        &self,
        occurrence: &ExactSynchronizedOccurrence,
    ) -> Result<Vec<SynchronizedContactOccurrence>, SynchronizedOccurrenceError> {
        occurrence.validate()?;
        let mut chart = self.clone();
        Ok(derive_occurrence(occurrence, &mut chart)?
            .relations
            .into_iter()
            .filter_map(|relation| relation.contact)
            .collect())
    }

    pub(super) fn receive_section_fiber(
        &mut self,
        face: &SynchronizedSectionFace,
    ) -> Result<ReceiverFiberIdentity, SynchronizedOccurrenceError> {
        const SYNCHRONIZED_SECTION_FACE_SCHEMA: u64 = 0x5359_4e43_4641_4345;
        const FACET_WORDS: usize = 2 + COG_WORDS + 1;

        let extent = face
            .0
            .len()
            .checked_mul(FACET_WORDS)
            .and_then(|words| words.checked_add(2))
            .ok_or(SynchronizedOccurrenceError::CarrierOverflow)?;
        let count = u64::try_from(face.0.len())
            .map_err(|_| SynchronizedOccurrenceError::CarrierOverflow)?;
        let mut words = Vec::new();
        words
            .try_reserve_exact(extent)
            .map_err(|_| SynchronizedOccurrenceError::CarrierOverflow)?;
        words.extend([count as u32, (count >> 32) as u32]);
        for facet in &face.0 {
            words.extend([facet.chart as u32, (facet.chart >> 32) as u32]);
            words.extend(facet.material.0);
            words.push(facet.stage);
        }
        debug_assert_eq!(words.len(), extent);
        Ok(ReceiverFiberIdentity::new(
            SYNCHRONIZED_SECTION_FACE_SCHEMA,
            words,
        ))
    }
}

pub(super) fn derive_occurrence(
    occurrence: &ExactSynchronizedOccurrence,
    chart: &mut SynchronizedOccurrenceChart,
) -> Result<DerivedOccurrence, SynchronizedOccurrenceError> {
    let mut transported = Vec::new();
    let mut boundaries = BTreeMap::<ExactOccurrenceTime, BoundaryBucket>::new();

    for (section_at, section) in occurrence.sections.iter().enumerate() {
        for (cell_at, cell) in section.cells.iter().enumerate() {
            let begin = section.clock.transport(&cell.local_begin);
            let end = section.clock.transport(&cell.local_end);
            if begin >= end {
                return Err(SynchronizedOccurrenceError::EmptyCellInterval(cell.id));
            }
            let transported_at = transported.len();
            transported.push(TransportedCell {
                section: section_at,
                cell: cell_at,
                begin: begin.clone(),
                end: end.clone(),
            });
            boundaries
                .entry(begin)
                .or_default()
                .starts
                .push(transported_at);
            boundaries.entry(end).or_default().ends.push(transported_at);
        }
    }

    let (receiver_complexes, receiver_cell_ports, directed, local_sequence_relations) =
        derive_receiver_complexes(occurrence, &transported)?;
    let mut relations = Vec::new();

    let times = boundaries.keys().cloned().collect::<Vec<_>>();
    let mut active = vec![BTreeSet::<usize>::new(); occurrence.sections.len()];
    let mut horizons = Vec::new();
    let mut elementary_intervals = 0_u64;
    let order_stride = u64::from(occurrence.horizon_stage)
        .checked_add(2)
        .ok_or(SynchronizedOccurrenceError::ChronologyOverflow)?;

    for (interval_at, window) in times.windows(2).enumerate() {
        let begin = &window[0];
        let end = &window[1];
        let bucket = boundaries
            .get(begin)
            .ok_or(SynchronizedOccurrenceError::MalformedOccurrence)?;
        for transported_at in &bucket.ends {
            active[transported[*transported_at].section].remove(transported_at);
        }
        for transported_at in &bucket.starts {
            active[transported[*transported_at].section].insert(*transported_at);
        }
        if begin >= end {
            return Err(SynchronizedOccurrenceError::MalformedOccurrence);
        }

        let mut meetings = Vec::new();
        for interaction in &occurrence.interactions {
            let left_section = occurrence.section_index(interaction.left)?;
            let right_section = occurrence.section_index(interaction.right)?;
            if !active[left_section].is_empty() && !active[right_section].is_empty() {
                meetings.push((
                    left_section,
                    right_section,
                    active[left_section].iter().copied().collect::<Vec<_>>(),
                    active[right_section].iter().copied().collect::<Vec<_>>(),
                ));
            }
        }
        if meetings.is_empty() {
            continue;
        }

        elementary_intervals = elementary_intervals
            .checked_add(1)
            .ok_or(SynchronizedOccurrenceError::CarrierOverflow)?;

        let interval_ordinal = u64::try_from(interval_at)
            .map_err(|_| SynchronizedOccurrenceError::ChronologyOverflow)?;
        let order_base = interval_ordinal
            .checked_mul(order_stride)
            .ok_or(SynchronizedOccurrenceError::ChronologyOverflow)?;
        let horizon_order = order_base
            .checked_add(u64::from(occurrence.horizon_stage))
            .and_then(|value| value.checked_add(1))
            .ok_or(SynchronizedOccurrenceError::ChronologyOverflow)?;

        for (left_section, right_section, left_active, right_active) in meetings {
            // A shared clock slice juxtaposes these declared interactions; it does not make them
            // one contact. Each interaction therefore receives its own local horizon lineage
            // while retaining the common interval as immediate occurrence testimony.
            let horizon = receiver_complexes
                .len()
                .checked_add(horizons.len())
                .ok_or(SynchronizedOccurrenceError::CarrierOverflow)?;
            horizons.push((begin.clone(), end.clone()));
            let left_receiver = occurrence.sections[left_section].receiver;
            let right_receiver = occurrence.sections[right_section].receiver;
            let left_cells = active_cells(occurrence, &transported, &left_active);
            let right_cells = active_cells(occurrence, &transported, &right_active);
            let left_face = section_face(&left_cells);
            let right_face = section_face(&right_cells);
            let left_collective_fiber = chart.receive_section_fiber(&left_face)?;
            let right_collective_fiber = chart.receive_section_fiber(&right_face)?;
            let mut arc_specs = BTreeMap::new();
            // One overlap remains one plural receiver contact and one holistic constituent.
            // Each caused facet meeting is nevertheless one independently reusable local germ
            // inside that face. The production support-family carrier retains later joins as a
            // factor DAG; this world membrane does not enumerate combinations of those germs.
            let mut support_factors = BTreeSet::<Vec<ReceiverArcKey>>::new();
            for left_at in &left_active {
                for right_at in &right_active {
                    let left_transport = &transported[*left_at];
                    let right_transport = &transported[*right_at];
                    let left =
                        &occurrence.sections[left_transport.section].cells[left_transport.cell];
                    let right =
                        &occurrence.sections[right_transport.section].cells[right_transport.cell];
                    let left_port = receiver_cell_ports[*left_at];
                    let right_port = receiver_cell_ports[*right_at];
                    let left_order = order_base
                        .checked_add(u64::from(left.arrival_stage))
                        .and_then(|value| value.checked_add(1))
                        .ok_or(SynchronizedOccurrenceError::ChronologyOverflow)?;
                    let right_order = order_base
                        .checked_add(u64::from(right.arrival_stage))
                        .and_then(|value| value.checked_add(1))
                        .ok_or(SynchronizedOccurrenceError::ChronologyOverflow)?;

                    let mut factor = Vec::new();
                    if left_order < right_order {
                        let direct = insert_receiver_arc(
                            &mut arc_specs,
                            left_port.current,
                            left_port.port,
                            left.chart,
                            &left_collective_fiber,
                            left_order,
                            right_port.current,
                            right_port.port,
                            right.chart,
                            &right_collective_fiber,
                            right_order,
                            IncidenceHand::Against,
                        )?;
                        let consequent = insert_receiver_arc(
                            &mut arc_specs,
                            right_port.current,
                            right_port.port,
                            right.chart,
                            &left_collective_fiber,
                            right_order,
                            horizon,
                            CurrentBoundaryPort::Cell,
                            occurrence.horizon_chart,
                            &right_collective_fiber,
                            horizon_order,
                            IncidenceHand::Against,
                        )?;
                        let direct_horizon = insert_receiver_arc(
                            &mut arc_specs,
                            left_port.current,
                            left_port.port,
                            left.chart,
                            &left_collective_fiber,
                            left_order,
                            horizon,
                            CurrentBoundaryPort::Cell,
                            occurrence.horizon_chart,
                            &right_collective_fiber,
                            horizon_order,
                            IncidenceHand::With,
                        )?;
                        factor.extend([direct, consequent, direct_horizon]);
                    } else if right_order < left_order {
                        let direct = insert_receiver_arc(
                            &mut arc_specs,
                            right_port.current,
                            right_port.port,
                            right.chart,
                            &right_collective_fiber,
                            right_order,
                            left_port.current,
                            left_port.port,
                            left.chart,
                            &left_collective_fiber,
                            left_order,
                            IncidenceHand::Against,
                        )?;
                        let consequent = insert_receiver_arc(
                            &mut arc_specs,
                            left_port.current,
                            left_port.port,
                            left.chart,
                            &right_collective_fiber,
                            left_order,
                            horizon,
                            CurrentBoundaryPort::Cell,
                            occurrence.horizon_chart,
                            &left_collective_fiber,
                            horizon_order,
                            IncidenceHand::Against,
                        )?;
                        let direct_horizon = insert_receiver_arc(
                            &mut arc_specs,
                            right_port.current,
                            right_port.port,
                            right.chart,
                            &right_collective_fiber,
                            right_order,
                            horizon,
                            CurrentBoundaryPort::Cell,
                            occurrence.horizon_chart,
                            &left_collective_fiber,
                            horizon_order,
                            IncidenceHand::With,
                        )?;
                        factor.extend([direct, consequent, direct_horizon]);
                    } else {
                        let left_horizon = insert_receiver_arc(
                            &mut arc_specs,
                            left_port.current,
                            left_port.port,
                            left.chart,
                            &left_collective_fiber,
                            left_order,
                            horizon,
                            CurrentBoundaryPort::Cell,
                            occurrence.horizon_chart,
                            &right_collective_fiber,
                            horizon_order,
                            IncidenceHand::Against,
                        )?;
                        let right_horizon = insert_receiver_arc(
                            &mut arc_specs,
                            right_port.current,
                            right_port.port,
                            right.chart,
                            &left_collective_fiber,
                            right_order,
                            horizon,
                            CurrentBoundaryPort::Cell,
                            occurrence.horizon_chart,
                            &right_collective_fiber,
                            horizon_order,
                            IncidenceHand::With,
                        )?;
                        factor.extend([left_horizon, right_horizon]);
                    }
                    factor.sort();
                    factor.dedup();
                    if factor.is_empty() {
                        return Err(SynchronizedOccurrenceError::MalformedOccurrence);
                    }
                    support_factors.insert(factor);
                }
            }

            let (arcs, slot_by_key) = materialize_receiver_arcs(arc_specs)?;
            let support_slots = support_factors
                .into_iter()
                .map(|factor| {
                    factor
                        .into_iter()
                        .map(|key| {
                            slot_by_key
                                .get(&key)
                                .copied()
                                .ok_or(SynchronizedOccurrenceError::MalformedOccurrence)
                        })
                        .collect::<Result<Vec<_>, _>>()
                })
                .collect::<Result<Vec<_>, _>>()?;
            let signature = SynchronizedAssociationSignature {
                left_receiver,
                left_face,
                right_receiver,
                right_face,
                horizon_chart: occurrence.horizon_chart.identity(),
            };
            relations.push(OwnedRelation {
                receiver: horizon,
                arcs,
                support_slots,
                contact: Some(SynchronizedContactOccurrence {
                    occurrence: occurrence.occurrence,
                    interval_begin: begin.clone(),
                    interval_end: end.clone(),
                    left_cells: left_cells.iter().map(|cell| cell.id).collect(),
                    right_cells: right_cells.iter().map(|cell| cell.id).collect(),
                    left_origins: left_cells.iter().map(|cell| cell.origin).collect(),
                    right_origins: right_cells.iter().map(|cell| cell.origin).collect(),
                    signature,
                }),
            });
        }
    }

    Ok(DerivedOccurrence {
        receiver_complexes,
        horizons,
        directed,
        relations,
        elementary_intervals,
        local_sequence_relations,
    })
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct ReceiverArcKey {
    from: usize,
    from_port_species: u8,
    from_port_slot: u32,
    from_chart: u64,
    from_fiber: ReceiverFiberIdentity,
    from_order: u64,
    to: usize,
    to_port_species: u8,
    to_port_slot: u32,
    to_chart: u64,
    to_fiber: ReceiverFiberIdentity,
    to_order: u64,
    hand: i64,
}
type ReceiverArcSpec = (
    usize,
    CurrentBoundaryPort,
    ReceiverChartIdentity,
    ReceiverFiberIdentity,
    u64,
    usize,
    CurrentBoundaryPort,
    ReceiverChartIdentity,
    ReceiverFiberIdentity,
    u64,
    IncidenceHand,
);

#[allow(clippy::too_many_arguments)]
fn insert_receiver_arc(
    arcs: &mut BTreeMap<ReceiverArcKey, ReceiverArcSpec>,
    from: usize,
    from_port: CurrentBoundaryPort,
    from_chart: ReceiverChartIdentity,
    from_fiber: &ReceiverFiberIdentity,
    from_order: u64,
    to: usize,
    to_port: CurrentBoundaryPort,
    to_chart: ReceiverChartIdentity,
    to_fiber: &ReceiverFiberIdentity,
    to_order: u64,
    hand: IncidenceHand,
) -> Result<ReceiverArcKey, SynchronizedOccurrenceError> {
    ReceiverCausalPassage::with_fiber(
        from_chart,
        from_fiber.clone(),
        from_order,
        to_chart,
        to_fiber.clone(),
        to_order,
    )
    .map_err(|_| SynchronizedOccurrenceError::NonIncreasingCausalStage)?;
    let key = ReceiverArcKey {
        from,
        from_port_species: boundary_port_key(from_port).0,
        from_port_slot: boundary_port_key(from_port).1,
        from_chart: from_chart.identity(),
        from_fiber: from_fiber.clone(),
        from_order,
        to,
        to_port_species: boundary_port_key(to_port).0,
        to_port_slot: boundary_port_key(to_port).1,
        to_chart: to_chart.identity(),
        to_fiber: to_fiber.clone(),
        to_order,
        hand: hand.coefficient(),
    };
    arcs.entry(key.clone()).or_insert((
        from,
        from_port,
        from_chart,
        from_fiber.clone(),
        from_order,
        to,
        to_port,
        to_chart,
        to_fiber.clone(),
        to_order,
        hand,
    ));
    Ok(key)
}

const fn boundary_port_key(port: CurrentBoundaryPort) -> (u8, u32) {
    match port {
        CurrentBoundaryPort::Cell => (0, 0),
        CurrentBoundaryPort::Ingress(slot) => (1, slot),
        CurrentBoundaryPort::Exposed(slot) => (2, slot),
    }
}

fn materialize_receiver_arcs(
    specs: BTreeMap<ReceiverArcKey, ReceiverArcSpec>,
) -> Result<(Vec<NativeRegionalArc>, BTreeMap<ReceiverArcKey, u32>), SynchronizedOccurrenceError> {
    let mut arcs = Vec::new();
    let mut slots = BTreeMap::new();
    for (
        boundary_slot,
        (
            key,
            (
                from,
                from_port,
                from_chart,
                from_fiber,
                from_order,
                to,
                to_port,
                to_chart,
                to_fiber,
                to_order,
                hand,
            ),
        ),
    ) in specs.into_iter().enumerate()
    {
        let passage = ReceiverCausalPassage::with_fiber(
            from_chart, from_fiber, from_order, to_chart, to_fiber, to_order,
        )
        .map_err(|_| SynchronizedOccurrenceError::NonIncreasingCausalStage)?;
        let boundary_slot = u32::try_from(boundary_slot)
            .map_err(|_| SynchronizedOccurrenceError::CarrierOverflow)?;
        arcs.push(NativeRegionalArc::from_receiver_passage(
            from,
            from_port,
            to,
            to_port,
            passage,
            boundary_slot,
            0,
            hand,
        ));
        slots.insert(key, boundary_slot);
    }
    Ok((arcs, slots))
}

fn active_cells<'a>(
    occurrence: &'a ExactSynchronizedOccurrence,
    transported: &[TransportedCell],
    active: &[usize],
) -> Vec<&'a TimedReceiverCell> {
    let mut cells = active
        .iter()
        .map(|at| {
            let body = &transported[*at];
            &occurrence.sections[body.section].cells[body.cell]
        })
        .collect::<Vec<_>>();
    cells.sort_by_key(|cell| cell.id);
    cells
}

pub(super) fn section_face(cells: &[&TimedReceiverCell]) -> SynchronizedSectionFace {
    let mut facets = cells
        .iter()
        .map(|cell| SynchronizedSectionFacet {
            chart: cell.chart.identity(),
            material: cell.material.into(),
            stage: cell.arrival_stage,
        })
        .collect::<Vec<_>>();
    facets.sort();
    SynchronizedSectionFace(facets)
}

fn derive_receiver_complexes(
    occurrence: &ExactSynchronizedOccurrence,
    transported: &[TransportedCell],
) -> Result<
    (
        Vec<OwnedEventComplex>,
        Vec<ReceiverCellPort>,
        Vec<NativeEventRelation>,
        u64,
    ),
    SynchronizedOccurrenceError,
> {
    let mut complexes = Vec::new();
    let mut cell_ports = vec![None; transported.len()];
    let mut sequence_arcs = 0_u64;
    for (section_at, section) in occurrence.sections.iter().enumerate() {
        let mut section_transport = transported
            .iter()
            .enumerate()
            .filter(|(_, body)| body.section == section_at)
            .collect::<Vec<_>>();
        if section_transport.len() != section.cells.len() {
            return Err(SynchronizedOccurrenceError::MalformedOccurrence);
        }
        section_transport.sort_by(|left, right| {
            left.1
                .begin
                .cmp(&right.1.begin)
                .then_with(|| left.1.end.cmp(&right.1.end))
                .then_with(|| left.1.cell.cmp(&right.1.cell))
        });
        let mut overlap_components: Vec<Vec<usize>> = Vec::new();
        let mut component_end = None::<ExactOccurrenceTime>;
        for (transported_at, body) in section_transport.iter().copied() {
            let starts_new = component_end.as_ref().is_some_and(|end| body.begin >= *end);
            if overlap_components.is_empty() || starts_new {
                overlap_components.push(Vec::new());
                component_end = Some(body.end.clone());
            } else if component_end.as_ref().is_some_and(|end| body.end > *end) {
                component_end = Some(body.end.clone());
            }
            overlap_components
                .last_mut()
                .ok_or(SynchronizedOccurrenceError::MalformedOccurrence)?
                .push(transported_at);
        }
        for mut component in overlap_components {
            component.sort_by_key(|at| transported[*at].cell);
            let current = complexes.len();
            let mut cells = Vec::new();
            let mut ports = Vec::new();
            for (local, transported_at) in component.iter().copied().enumerate() {
                let body = &transported[transported_at];
                let cell = &section.cells[body.cell];
                let id = EventCellId::new(
                    u64::try_from(local)
                        .map_err(|_| SynchronizedOccurrenceError::CarrierOverflow)?,
                );
                cells.push(EventCell::situated(id, 0, 0, 0, cell.material.cog()));
                let slot = u32::try_from(local)
                    .map_err(|_| SynchronizedOccurrenceError::CarrierOverflow)?;
                if local == 0 {
                    ports.push(EventPort::ingress(id, IncidenceHand::Against, 0));
                }
                ports.push(EventPort::exposed(id, IncidenceHand::With, slot));
                cell_ports[transported_at] = Some(ReceiverCellPort {
                    current,
                    port: CurrentBoundaryPort::Exposed(slot),
                });
            }
            let complex = OwnedEventComplex {
                cells,
                incidences: Vec::new(),
                ports,
            };
            complex.view()?;
            complexes.push(complex);
        }
    }

    let cell_ports = cell_ports
        .into_iter()
        .collect::<Option<Vec<_>>>()
        .ok_or(SynchronizedOccurrenceError::MalformedOccurrence)?;
    let mut directed = BTreeSet::new();
    for (section_at, section) in occurrence.sections.iter().enumerate() {
        let mut streams =
            BTreeMap::<u64, Vec<(ExactOccurrenceTime, ExactOccurrenceTime, usize)>>::new();
        for (transported_at, body) in transported.iter().enumerate() {
            if body.section != section_at {
                continue;
            }
            let cell = &section.cells[body.cell];
            streams.entry(cell.chart.identity()).or_default().push((
                body.begin.clone(),
                body.end.clone(),
                transported_at,
            ));
        }
        for stream in streams.values_mut() {
            stream.sort_by(|left, right| {
                left.0
                    .cmp(&right.0)
                    .then_with(|| left.1.cmp(&right.1))
                    .then_with(|| left.2.cmp(&right.2))
            });
            for pair in stream.windows(2) {
                if pair[0].1 > pair[1].0 {
                    continue;
                }
                let from = cell_ports[pair[0].2].current;
                let to = cell_ports[pair[1].2].current;
                if from == to {
                    continue;
                }
                directed.insert((from, to));
                sequence_arcs = sequence_arcs
                    .checked_add(1)
                    .ok_or(SynchronizedOccurrenceError::CarrierOverflow)?;
            }
        }
    }
    Ok((
        complexes,
        cell_ports,
        directed
            .into_iter()
            .map(|(from, to)| NativeEventRelation::new(from, to))
            .collect(),
        sequence_arcs,
    ))
}

use super::*;

struct CardContactPopulation {
    incidences: Vec<EventIncidenceRadiation>,
    directed: Vec<(usize, ExecutedDirectedRelation)>,
    regional: Vec<(usize, ExecutedRegionalRelation)>,
    formed_incidences: u64,
}

impl CudaLiveCurrentExecutor {
    fn form_card_contact_population(
        &mut self,
        standing_axis: u32,
        standing: &DeviceBuffer<u32>,
        standing_len: usize,
        request: CurrentExecutionRequest<'_>,
        relations: &[DirectedExecutionRequest],
        regional: &[RegionalExecutionRequest<'_>],
    ) -> Result<CardContactPopulation, LiveCurrentError> {
        let source_grain = request.event().geometry().source_grain()?;
        let receiver = request
            .mount()
            .event_receiver_at_source_grain(source_grain)
            .ok_or(LiveCurrentError::ExecutionMismatch(request.lineage()))?;
        let mut pairs = BTreeMap::new();
        let incidences = if let Some(complex) = request.event().geometry().complex() {
            canonical_event_incidences(complex)?
        } else {
            Vec::new()
        };
        if request.event().geometry().complex().is_some() {
            let nodes = request
                .event_nodes()
                .ok_or(LiveCurrentError::UnsupportedEventComplex)?;
            for incidence in &incidences {
                let (from, to) = nodes.incidence_nodes(*incidence)?;
                let row = cuda::DirectedEventRow::new(from.place, to.place);
                pairs.insert(row.words(), (from.place, to.place));
            }
        }
        for relation in relations {
            if relation.relation().to() == request.lineage() {
                let row = cuda::DirectedEventRow::new(relation.from(), relation.to());
                pairs.insert(row.words(), (relation.from(), relation.to()));
            }
        }
        for cell in regional {
            if cell.receiver() != request.lineage() {
                continue;
            }
            for (from, to) in regional_contact_pairs(cell)? {
                let row = cuda::DirectedEventRow::new(from, to);
                pairs.insert(row.words(), (from, to));
            }
        }

        let mut contacts = BTreeMap::new();
        if !pairs.is_empty() {
            let receiver_host = cuda::ReceiverRow::new(receiver).words();
            let receiver_device = upload(&receiver_host)?;
            let mut directed_host = Vec::new();
            directed_host
                .try_reserve_exact(pairs.len() * cuda::DIRECTED_EVENT_WORDS)
                .map_err(|_| LiveCurrentError::ResourceReservation)?;
            for words in pairs.keys() {
                directed_host.extend_from_slice(words);
            }
            let directed_device = upload(&directed_host)?;
            let contact_extent = checked_mul(pairs.len(), cuda::DIRECTED_CONTACT_WORDS)?;
            let contact_device =
                DeviceBuffer::<u32>::alloc_zeroed(contact_extent).map_err(substrate)?;
            let status_device =
                DeviceBuffer::<u32>::alloc_zeroed(pairs.len()).map_err(substrate)?;
            self.module
                .regional_contacts()
                .map_err(substrate)?
                .launch(RegionalContactArguments {
                    standing: LiveEventSpan::prefix(standing, standing_len).map_err(substrate)?,
                    standing_axis,
                    receiver: LiveEventSpan::whole(&receiver_device),
                    directed_events: LiveEventSpan::whole(&directed_device),
                    directed_contacts: LiveEventSpan::whole(&contact_device),
                    statuses: LiveEventSpan::whole(&status_device),
                })
                .map_err(substrate)?;
            self.context.synchronize().map_err(substrate)?;
            self.launches = self
                .launches
                .checked_add(1)
                .ok_or(LiveCurrentError::ResourceReservation)?;
            self.contact_launches = self
                .contact_launches
                .checked_add(1)
                .ok_or(LiveCurrentError::ResourceReservation)?;
            self.parallel_contact_lanes = self
                .parallel_contact_lanes
                .checked_add(
                    u64::try_from(pairs.len())
                        .map_err(|_| LiveCurrentError::ResourceReservation)?,
                )
                .ok_or(LiveCurrentError::ResourceReservation)?;

            let mut statuses = vec![0u32; pairs.len()];
            status_device
                .copy_to_slice(&mut statuses)
                .map_err(substrate)?;
            if statuses
                .iter()
                .any(|status| *status != cuda::REGIONAL_STATUS_COMPLETE)
            {
                return Err(LiveCurrentError::ExecutionMismatchAt(
                    request.lineage(),
                    "regional-contact-status",
                ));
            }
            let mut contact_words = vec![0u32; contact_extent];
            contact_device
                .copy_to_slice(&mut contact_words)
                .map_err(substrate)?;
            for (ordinal, key) in pairs.keys().copied().enumerate() {
                let at = ordinal * cuda::DIRECTED_CONTACT_WORDS;
                let row: [u32; cuda::DIRECTED_CONTACT_WORDS] = contact_words
                    [at..at + cuda::DIRECTED_CONTACT_WORDS]
                    .try_into()
                    .map_err(|_| LiveCurrentError::ExecutionMismatch(request.lineage()))?;
                let contact = cuda::DirectedContactRow::from_words(row)
                    .ok_or(LiveCurrentError::ExecutionMismatch(request.lineage()))?
                    .contact();
                contacts.insert(key, contact);
            }
        }

        let lookup = |from, to| {
            contacts
                .get(&cuda::DirectedEventRow::new(from, to).words())
                .copied()
                .ok_or(LiveCurrentError::ExecutionMismatch(request.lineage()))
        };
        let mut incidence_results = Vec::new();
        incidence_results
            .try_reserve_exact(incidences.len())
            .map_err(|_| LiveCurrentError::ResourceReservation)?;
        if request.event().geometry().complex().is_some() {
            let nodes = request
                .event_nodes()
                .ok_or(LiveCurrentError::UnsupportedEventComplex)?;
            for incidence in incidences {
                let (from, to) = nodes.incidence_nodes(incidence)?;
                incidence_results.push(EventIncidenceRadiation::new(
                    incidence,
                    lookup(from.place, to.place)?,
                ));
            }
        }
        let formed_incidences = u64::try_from(
            incidence_results
                .iter()
                .filter(|radiation| radiation.contact().emission.is_some())
                .count(),
        )
        .map_err(|_| LiveCurrentError::ResourceReservation)?;

        let mut directed_results = Vec::new();
        for (at, relation) in relations.iter().copied().enumerate() {
            if relation.relation().to() == request.lineage() {
                directed_results.push((
                    at,
                    ExecutedDirectedRelation::new(
                        relation.relation(),
                        lookup(relation.from(), relation.to())?,
                    ),
                ));
            }
        }
        let mut regional_results = Vec::new();
        for (at, cell) in regional.iter().enumerate() {
            if cell.receiver() == request.lineage() {
                regional_results.push((
                    at,
                    form_executed_regional_relation(source_grain, cell, lookup)?,
                ));
            }
        }
        self.directed_contacts = self
            .directed_contacts
            .checked_add(
                u64::try_from(directed_results.len())
                    .map_err(|_| LiveCurrentError::ResourceReservation)?,
            )
            .ok_or(LiveCurrentError::ResourceReservation)?;
        Ok(CardContactPopulation {
            incidences: incidence_results,
            directed: directed_results,
            regional: regional_results,
            formed_incidences,
        })
    }

    fn enact_one(
        &mut self,
        standing_axis: u32,
        standing: &DeviceBuffer<u32>,
        standing_len: usize,
        request: CurrentExecutionRequest<'_>,
        resident: Option<&ResidentCarrier>,
        directed: &[(usize, DirectedExecutionRequest)],
        incidence_radiation: &[EventIncidenceRadiation],
        formed_incidences: u64,
    ) -> Result<
        (
            ExecutedLiveCurrent,
            Vec<(usize, ExecutedDirectedRelation)>,
            ResidentCarrier,
        ),
        LiveCurrentError,
    > {
        let prior = request.mount().carrier();
        let prior_depth = prior.depth();
        let prior_overflow = (0..prior_depth)
            .map(|depth| prior.co_present_overflow(depth).map_or(0, <[_]>::len))
            .max()
            .unwrap_or(0);
        let mut own_capacity = resident.map_or(32, |resident| resident.own_capacity.max(32));
        let mut max_depth = resident
            .map_or(prior_depth, |resident| resident.max_depth.max(prior_depth))
            .max(1);
        let mut overflow_capacity = resident
            .map_or(prior_overflow, |resident| {
                resident.overflow_capacity.max(prior_overflow)
            })
            .max(1);
        let mut emission_capacity =
            resident.map_or(32, |resident| resident.emission_capacity.max(32));
        let source_grain = request.event().geometry().source_grain()?;
        let (relation_count, relation_extent, relation_host) = match request.event().geometry() {
            CurrentGeometry::Cell(relation) => (1usize, COG_WORDS, relation.words().to_vec()),
            CurrentGeometry::Complex(_) => (0usize, 0usize, vec![0u32]),
        };

        loop {
            self.ensure_live_event_stack(source_grain, max_depth)?;
            let carrier_extent = checked_mul(max_depth, ENCLOSURE_WORDS)?;
            let overflow_extent =
                checked_mul(checked_mul(max_depth, overflow_capacity)?, NODE_WORDS)?;
            let emission_extent = checked_mul(emission_capacity, DEED_WORDS)?;
            let directed_event_extent = checked_mul(directed.len(), cuda::DIRECTED_EVENT_WORDS)?;
            let directed_contact_extent =
                checked_mul(directed.len(), cuda::DIRECTED_CONTACT_WORDS)?;
            let mut control = vec![0u32; cuda::CONTROL_WORDS];
            let params = cuda::CONTROL_PARAMS;
            control[params + cuda::PARAM_VERSION] = cuda::LAYOUT_VERSION;
            control[params + cuda::PARAM_STANDING_AXIS] = standing_axis;
            control[params + cuda::PARAM_MOUNT] = request.mount().header().is_some() as u32;
            control[params + cuda::PARAM_WHOLE_DARK] = request.wholly_dark() as u32;
            control[params + cuda::PARAM_ENDING] = request.event().ends_lineage() as u32;
            control[params + cuda::PARAM_OWN_CAPACITY] =
                u32::try_from(own_capacity).map_err(|_| LiveCurrentError::ResourceReservation)?;
            control[params + cuda::PARAM_CARRIER_DEPTH] =
                u32::try_from(prior_depth).map_err(|_| LiveCurrentError::ResourceReservation)?;
            control[params + cuda::PARAM_CARRIER_MAX_DEPTH] =
                u32::try_from(max_depth).map_err(|_| LiveCurrentError::ResourceReservation)?;
            control[params + cuda::PARAM_OVERFLOW_CAPACITY] = u32::try_from(overflow_capacity)
                .map_err(|_| LiveCurrentError::ResourceReservation)?;
            control[params + cuda::PARAM_EMISSION_CAPACITY] = u32::try_from(emission_capacity)
                .map_err(|_| LiveCurrentError::ResourceReservation)?;
            control[params + cuda::PARAM_RELATIONS] = relation_count as u32;
            control[params + cuda::PARAM_DIRECTED_EVENTS] =
                u32::try_from(directed.len()).map_err(|_| LiveCurrentError::ResourceReservation)?;
            control[params + cuda::PARAM_SOURCE_GRAIN] = source_grain;
            control[params + cuda::PARAM_COMPLEX] =
                request.event().geometry().complex().is_some() as u32;
            for (lo, hi, value) in [
                (
                    cuda::PARAM_EVENT_CELLS_LO,
                    cuda::PARAM_EVENT_CELLS_HI,
                    request.event().geometry().cells(),
                ),
                (
                    cuda::PARAM_EVENT_INCIDENCES_LO,
                    cuda::PARAM_EVENT_INCIDENCES_HI,
                    request.event().geometry().incidences(),
                ),
                (
                    cuda::PARAM_EVENT_RESOLVING_LO,
                    cuda::PARAM_EVENT_RESOLVING_HI,
                    request.event().geometry().resolving_cells(),
                ),
                (
                    cuda::PARAM_EVENT_COMPOUNDS_LO,
                    cuda::PARAM_EVENT_COMPOUNDS_HI,
                    request.event().geometry().compounds(),
                ),
                (
                    cuda::PARAM_EVENT_FORMED_LO,
                    cuda::PARAM_EVENT_FORMED_HI,
                    formed_incidences,
                ),
            ] {
                control[params + lo] = value as u32;
                control[params + hi] = (value >> 32) as u32;
            }
            let event = cuda::EventRow::new(
                request.face(),
                request
                    .mount()
                    .seed_anchor()
                    .unwrap_or(request.face().place),
                request.event().action().cog(),
                request.pending_dark(),
            )
            .ok_or(LiveCurrentError::ExecutionMismatch(request.lineage()))?;
            control[cuda::CONTROL_EVENT..cuda::CONTROL_EVENT + cuda::EVENT_WORDS]
                .copy_from_slice(&event.words());
            if let Some(header) = request.mount().header() {
                control[cuda::CONTROL_HEADER..cuda::CONTROL_HEADER + CARRIER_HEADER_WORDS]
                    .copy_from_slice(header.words());
            }

            let owns_host = vec![SparseOwnCell::EMPTY; own_capacity];
            let mut carrier_host = vec![0u32; carrier_extent];
            let mut overflow_host = vec![0u32; overflow_extent];
            let mut overflow_count_host = vec![0u32; max_depth];
            let emissions_host = vec![0u32; emission_extent];
            let emanation_host = vec![0u32; cuda::EMANATION_WORDS];
            let mut directed_event_host = vec![0u32; directed_event_extent.max(1)];
            let directed_contact_host = vec![0u32; directed_contact_extent.max(1)];
            for (ordinal, (_, relation)) in directed.iter().copied().enumerate() {
                if relation.relation().to() != request.lineage() {
                    return Err(LiveCurrentError::ExecutionMismatch(request.lineage()));
                }
                let row = cuda::DirectedEventRow::new(relation.from(), relation.to());
                let at = ordinal * cuda::DIRECTED_EVENT_WORDS;
                directed_event_host[at..at + cuda::DIRECTED_EVENT_WORDS]
                    .copy_from_slice(&row.words());
            }

            let control_device = upload(&control)?;
            let relations_device = upload(&relation_host)?;
            let owns_device = upload(&owns_host)?;
            let (carriers_device, overflow_device, overflow_counts_device) =
                if let Some(resident) = resident {
                    if resident.depth != prior_depth
                        || resident.max_depth < prior_depth
                        || resident.overflow_counts.len() != prior_depth
                    {
                        return Err(LiveCurrentError::ExecutionMismatch(request.lineage()));
                    }
                    let carriers_device =
                        DeviceBuffer::alloc_zeroed(carrier_extent).map_err(substrate)?;
                    let overflow_device =
                        DeviceBuffer::alloc_zeroed(overflow_extent).map_err(substrate)?;
                    let overflow_counts_device =
                        DeviceBuffer::alloc_zeroed(max_depth).map_err(substrate)?;
                    let active_carrier = checked_mul(prior_depth, ENCLOSURE_WORDS)?;
                    carriers_device
                        .copy_range_from_buffer(0, &resident.carrier, 0, active_carrier)
                        .map_err(substrate)?;
                    overflow_counts_device
                        .copy_range_from_buffer(0, &resident.counts, 0, prior_depth)
                        .map_err(substrate)?;
                    let mut copied_words = active_carrier
                        .checked_add(prior_depth)
                        .ok_or(LiveCurrentError::ResourceReservation)?;
                    for row in 0..prior_depth {
                        let count = resident.overflow_counts[row];
                        if count > resident.overflow_capacity {
                            return Err(LiveCurrentError::ExecutionMismatch(request.lineage()));
                        }
                        let words = checked_mul(count, NODE_WORDS)?;
                        if words != 0 {
                            overflow_device
                                .copy_range_from_buffer(
                                    checked_mul(checked_mul(row, overflow_capacity)?, NODE_WORDS)?,
                                    &resident.overflow,
                                    checked_mul(
                                        checked_mul(row, resident.overflow_capacity)?,
                                        NODE_WORDS,
                                    )?,
                                    words,
                                )
                                .map_err(substrate)?;
                        }
                        copied_words = copied_words
                            .checked_add(words)
                            .ok_or(LiveCurrentError::ResourceReservation)?;
                    }
                    add_words(&mut self.carrier_device_words, copied_words)?;
                    (carriers_device, overflow_device, overflow_counts_device)
                } else {
                    put_prior_carrier(
                        request,
                        max_depth,
                        overflow_capacity,
                        &mut carrier_host,
                        &mut overflow_host,
                        &mut overflow_count_host,
                    )?;
                    let carriers_device = upload(&carrier_host)?;
                    let overflow_device = upload(&overflow_host)?;
                    let overflow_counts_device = upload(&overflow_count_host)?;
                    self.carrier_full_mounts = self
                        .carrier_full_mounts
                        .checked_add(1)
                        .ok_or(LiveCurrentError::ResourceReservation)?;
                    let mounted_words = carrier_extent
                        .checked_add(overflow_extent)
                        .and_then(|value| value.checked_add(max_depth))
                        .ok_or(LiveCurrentError::ResourceReservation)?;
                    add_words(&mut self.carrier_host_words, mounted_words)?;
                    (carriers_device, overflow_device, overflow_counts_device)
                };
            let directed_events_device = upload(&directed_event_host)?;
            let directed_contacts_device = upload(&directed_contact_host)?;
            let emissions_device = upload(&emissions_host)?;
            let emanation_device = upload(&emanation_host)?;
            self.module
                .lineage_event()
                .map_err(substrate)?
                .launch(LiveEventArguments {
                    standing: LiveEventSpan::prefix(standing, standing_len).map_err(substrate)?,
                    control: LiveEventSpan::whole(&control_device),
                    relations: LiveEventSpan::prefix(&relations_device, relation_extent)
                        .map_err(substrate)?,
                    owns: LiveEventSpan::whole(&owns_device),
                    carriers: LiveEventSpan::whole(&carriers_device),
                    overflow_nodes: LiveEventSpan::whole(&overflow_device),
                    overflow_counts: LiveEventSpan::whole(&overflow_counts_device),
                    directed_events: LiveEventSpan::prefix(
                        &directed_events_device,
                        directed_event_extent,
                    )
                    .map_err(substrate)?,
                    directed_contacts: LiveEventSpan::prefix(
                        &directed_contacts_device,
                        directed_contact_extent,
                    )
                    .map_err(substrate)?,
                    emissions: LiveEventSpan::whole(&emissions_device),
                    emanation: LiveEventSpan::whole(&emanation_device),
                })
                .map_err(substrate)?;
            self.context.synchronize().map_err(substrate)?;
            self.launches = self
                .launches
                .checked_add(1)
                .ok_or(LiveCurrentError::ResourceReservation)?;
            control_device
                .copy_to_slice(&mut control)
                .map_err(substrate)?;
            let status = cuda::CONTROL_STATUS;
            match control[status + cuda::STATUS_KIND] {
                cuda::STATUS_RESOURCE => {
                    let required_own = control[status + cuda::STATUS_REQUIRED_OWN] as usize;
                    let required_depth = cuda::join_u64(
                        &control,
                        status + cuda::STATUS_REQUIRED_DEPTH_LO,
                        status + cuda::STATUS_REQUIRED_DEPTH_HI,
                    );
                    let required_depth = usize::try_from(required_depth)
                        .map_err(|_| LiveCurrentError::ResourceReservation)?;
                    let required_overflow =
                        control[status + cuda::STATUS_REQUIRED_OVERFLOW] as usize;
                    let required_emissions =
                        control[status + cuda::STATUS_REQUIRED_EMISSIONS] as usize;
                    let before = (
                        own_capacity,
                        max_depth,
                        overflow_capacity,
                        emission_capacity,
                    );
                    if required_own > own_capacity {
                        own_capacity = next_capacity(own_capacity, required_own)?;
                    }
                    if required_depth > max_depth {
                        max_depth = next_capacity(max_depth, required_depth)?;
                    }
                    if required_overflow > overflow_capacity {
                        overflow_capacity = next_capacity(overflow_capacity, required_overflow)?;
                    }
                    if required_emissions > emission_capacity {
                        emission_capacity = next_capacity(emission_capacity, required_emissions)?;
                    }
                    if before
                        == (
                            own_capacity,
                            max_depth,
                            overflow_capacity,
                            emission_capacity,
                        )
                    {
                        return Err(LiveCurrentError::ExecutionMismatch(request.lineage()));
                    }
                    self.resource_retries = self
                        .resource_retries
                        .checked_add(1)
                        .ok_or(LiveCurrentError::ResourceReservation)?;
                    continue;
                }
                cuda::STATUS_COMPLETE => {}
                _ => {
                    return Err(LiveCurrentError::ExecutionMismatchStatus(
                        request.lineage(),
                        "lineage-kernel-status",
                        control[status + cuda::STATUS_KIND],
                    ))
                }
            }

            let state = cuda::CONTROL_STATE;
            let own_axis = control[state + cuda::STATE_OWN_AXIS];
            let own_live = control[state + cuda::STATE_OWN_LIVE] as usize;
            let depth = control[state + cuda::STATE_CARRIER_DEPTH] as usize;
            let emitted = control[state + cuda::STATE_EMISSIONS] as usize;
            if own_axis == 0
                || !own_axis.is_power_of_two()
                || own_live > own_capacity
                || depth == 0
                || depth > max_depth
                || emitted > emission_capacity
            {
                return Err(LiveCurrentError::ExecutionMismatch(request.lineage()));
            }

            let mut owns_read = vec![SparseOwnCell::EMPTY; own_capacity];
            owns_device
                .copy_to_slice(&mut owns_read)
                .map_err(substrate)?;
            let rank = own_axis.trailing_zeros() as u64;
            let mut contributions = Vec::new();
            contributions
                .try_reserve_exact(own_live)
                .map_err(|_| LiveCurrentError::ResourceReservation)?;
            for cell in owns_read.into_iter().take(own_live) {
                let cell = RankedOwnCell::from_flat_at_rank(rank, cell)
                    .map_err(|_| LiveCurrentError::ExecutionMismatch(request.lineage()))?;
                contributions.push((cell.founder(), cell.form()));
            }

            carriers_device
                .copy_to_slice(&mut carrier_host)
                .map_err(substrate)?;
            overflow_device
                .copy_to_slice(&mut overflow_host)
                .map_err(substrate)?;
            overflow_counts_device
                .copy_to_slice(&mut overflow_count_host)
                .map_err(substrate)?;
            let mut overflow = Vec::new();
            overflow
                .try_reserve_exact(depth)
                .map_err(|_| LiveCurrentError::ResourceReservation)?;
            for row in 0..depth {
                let count = overflow_count_host[row] as usize;
                if count > overflow_capacity {
                    return Err(LiveCurrentError::ExecutionMismatch(request.lineage()));
                }
                let mut nodes = Vec::new();
                nodes
                    .try_reserve_exact(count)
                    .map_err(|_| LiveCurrentError::ResourceReservation)?;
                for ordinal in 0..count {
                    let at = (row * overflow_capacity + ordinal) * NODE_WORDS;
                    if !body::manifold::packed_node_is_canonical(&overflow_host, at) {
                        return Err(LiveCurrentError::ExecutionMismatch(request.lineage()));
                    }
                    nodes.push(body::manifold::unpack_node(&overflow_host, at));
                }
                overflow.push(nodes);
            }
            let header = cuda::header_from_control(&control)
                .ok_or(LiveCurrentError::ExecutionMismatch(request.lineage()))?;
            let next = LiveCarrierSnapshot::from_substrate_parts(
                header,
                carrier_host[..depth * ENCLOSURE_WORDS].to_vec(),
                overflow,
            )
            .map_err(LiveCurrentError::Carrier)?;
            let mut event_words = [0u32; cuda::EVENT_WORDS];
            event_words.copy_from_slice(
                &control[cuda::CONTROL_EVENT..cuda::CONTROL_EVENT + cuda::EVENT_WORDS],
            );
            let pending_dark = cuda::EventRow::from_words(event_words)
                .ok_or(LiveCurrentError::ExecutionMismatch(request.lineage()))?
                .pending_dark();

            let mut emission_read = vec![0u32; emission_extent];
            emissions_device
                .copy_to_slice(&mut emission_read)
                .map_err(substrate)?;
            let mut emissions = Vec::new();
            emissions
                .try_reserve_exact(emitted)
                .map_err(|_| LiveCurrentError::ResourceReservation)?;
            for ordinal in 0..emitted {
                let at = ordinal * DEED_WORDS;
                let row: [u32; DEED_WORDS] = emission_read[at..at + DEED_WORDS]
                    .try_into()
                    .map_err(|_| LiveCurrentError::ExecutionMismatch(request.lineage()))?;
                let emission = DeedEmission::from_words(row)
                    .ok_or(LiveCurrentError::ExecutionMismatch(request.lineage()))?;
                emissions.push(emission.felt_emission());
            }
            let mut emanation_read = vec![0u32; cuda::EMANATION_WORDS];
            emanation_device
                .copy_to_slice(&mut emanation_read)
                .map_err(substrate)?;
            let emanation_row: [u32; cuda::EMANATION_WORDS] = emanation_read
                .try_into()
                .map_err(|_| LiveCurrentError::ExecutionMismatch(request.lineage()))?;
            let consequence = cuda::EmanationRow::from_words(emanation_row)
                .ok_or(LiveCurrentError::ExecutionMismatch(request.lineage()))?
                .emanation();
            let mut directed_contact_read = vec![0u32; directed_contact_extent.max(1)];
            directed_contacts_device
                .copy_to_slice(&mut directed_contact_read)
                .map_err(substrate)?;
            let mut directed_results = Vec::new();
            directed_results
                .try_reserve_exact(directed.len())
                .map_err(|_| LiveCurrentError::ResourceReservation)?;
            for (ordinal, (event_at, relation)) in directed.iter().copied().enumerate() {
                let at = ordinal * cuda::DIRECTED_CONTACT_WORDS;
                let words: [u32; cuda::DIRECTED_CONTACT_WORDS] = directed_contact_read
                    [at..at + cuda::DIRECTED_CONTACT_WORDS]
                    .try_into()
                    .map_err(|_| LiveCurrentError::ExecutionMismatch(request.lineage()))?;
                let contact = cuda::DirectedContactRow::from_words(words)
                    .ok_or(LiveCurrentError::ExecutionMismatch(request.lineage()))?
                    .contact();
                directed_results.push((
                    event_at,
                    ExecutedDirectedRelation::new(relation.relation(), contact),
                ));
            }
            self.directed_contacts = self
                .directed_contacts
                .checked_add(
                    u64::try_from(directed_results.len())
                        .map_err(|_| LiveCurrentError::ResourceReservation)?,
                )
                .ok_or(LiveCurrentError::ResourceReservation)?;
            let witness = carrier_witness(Some(header), next.carrier())?;
            let overflow_counts = overflow_count_host[..depth]
                .iter()
                .map(|count| *count as usize)
                .collect();
            let resident = ResidentCarrier {
                witness,
                depth,
                max_depth,
                own_capacity,
                emission_capacity,
                overflow_capacity,
                overflow_counts,
                carrier: carriers_device,
                overflow: overflow_device,
                counts: overflow_counts_device,
            };
            return Ok((
                ExecutedLiveCurrent::new(
                    request.lineage(),
                    next,
                    pending_dark,
                    consequence,
                    emissions,
                    incidence_radiation.to_vec(),
                    contributions,
                ),
                directed_results,
                resident,
            ));
        }
    }
}

impl LiveCurrentExecutor for CudaLiveCurrentExecutor {
    fn enact(
        &mut self,
        physical_revision: u64,
        standing: &SparseStandingSurface,
        currents: &[CurrentExecutionRequest<'_>],
        relations: &[DirectedExecutionRequest],
        regional: &[RegionalExecutionRequest<'_>],
    ) -> Result<ExecutedContemporaryEvent, LiveCurrentError> {
        self.context.make_current().map_err(substrate)?;
        self.staged = None;
        let body_key = standing as *const SparseStandingSurface as usize;
        if self.resident_body_key != Some(body_key)
            || self.resident_revision != Some(physical_revision)
        {
            self.resident_standing = None;
            self.resident_lineages.clear();
            self.resident_body_key = Some(body_key);
            self.resident_revision = Some(physical_revision);
        } else if self
            .resident_standing
            .as_ref()
            .is_some_and(|resident| &resident.logical != standing)
        {
            // A physical revision is only a cache hint. Exact logical disagreement always wins.
            self.resident_standing = None;
            self.resident_lineages.clear();
        }
        if self.resident_standing.is_none() {
            self.resident_standing = Some(self.mount_standing(standing)?);
        }
        let resident_standing = self
            .resident_standing
            .take()
            .ok_or(LiveCurrentError::PhysicalSettlement)?;
        let result = (|| {
            let mut enacted = Vec::new();
            enacted
                .try_reserve_exact(currents.len())
                .map_err(|_| LiveCurrentError::ResourceReservation)?;
            let mut relation_results = Vec::new();
            relation_results
                .try_reserve_exact(relations.len())
                .map_err(|_| LiveCurrentError::ResourceReservation)?;
            relation_results.resize_with(relations.len(), || None);
            let mut regional_results = Vec::new();
            regional_results
                .try_reserve_exact(regional.len())
                .map_err(|_| LiveCurrentError::ResourceReservation)?;
            regional_results.resize_with(regional.len(), || None);
            let mut staged_lineages = BTreeMap::new();

            // **The contemporary population crosses ONCE, one lane per current.**
            //
            // Until 2026-08-10 this was `for current in currents { ... enact_one(...) }`, so a
            // population of `n` cost up to `2n` crossings of a kernel launched at `Dim3::x(1)` --
            // the card ran as a single core. The currents of one contemporary event are
            // independent, and their regions on the card are disjoint, so the whole population is
            // one crossing.
            let mut contacts = Vec::new();
            contacts
                .try_reserve_exact(currents.len())
                .map_err(|_| LiveCurrentError::ResourceReservation)?;
            for current in currents {
                contacts.push(self.form_card_contact_population(
                    resident_standing.axis,
                    &resident_standing.device,
                    resident_standing.words,
                    *current,
                    relations,
                    regional,
                )?);
            }

            let mut priors = Vec::new();
            priors
                .try_reserve_exact(currents.len())
                .map_err(|_| LiveCurrentError::ResourceReservation)?;
            let mut matched = Vec::new();
            matched
                .try_reserve_exact(currents.len())
                .map_err(|_| LiveCurrentError::ResourceReservation)?;
            for current in currents {
                let witness = carrier_witness(current.mount().header(), current.mount().carrier())?;
                let prior = self.resident_lineages.remove(&current.lineage());
                let matches = prior
                    .as_ref()
                    .is_some_and(|resident| resident.witness == witness);
                matched.push(matches);
                priors.push(prior);
            }

            let exact: Vec<Option<&ResidentCarrier>> = priors
                .iter()
                .zip(&matched)
                .map(|(prior, matched)| if *matched { prior.as_ref() } else { None })
                .collect();
            let outcome = self.enact_population(
                resident_standing.axis,
                &resident_standing.device,
                resident_standing.words,
                currents,
                &exact,
                &contacts,
            );
            for (current, prior) in currents.iter().zip(priors) {
                if let Some(prior) = prior {
                    self.resident_lineages.insert(current.lineage(), prior);
                }
            }
            let population = outcome?;

            for ((current, contact), (enacted_current, next_resident)) in
                currents.iter().zip(contacts).zip(population)
            {
                enacted.push(enacted_current);
                let staged = if current.event().ends_lineage() {
                    StagedCarrier::Departed
                } else {
                    StagedCarrier::Continuing(next_resident)
                };
                if staged_lineages.insert(current.lineage(), staged).is_some() {
                    return Err(LiveCurrentError::ExecutionMismatch(current.lineage()));
                }
                for (at, relation) in contact.directed {
                    if relation_results[at].replace(relation).is_some() {
                        return Err(LiveCurrentError::ExecutionMismatch(current.lineage()));
                    }
                }
                for (at, relation) in contact.regional {
                    if regional_results[at].replace(relation).is_some() {
                        return Err(LiveCurrentError::ExecutionMismatch(current.lineage()));
                    }
                }
            }
            let mut completed_relations = Vec::new();
            completed_relations
                .try_reserve_exact(relation_results.len())
                .map_err(|_| LiveCurrentError::ResourceReservation)?;
            for (request, result) in relations.iter().zip(relation_results) {
                completed_relations.push(
                    result.ok_or(LiveCurrentError::ExecutionMismatch(request.relation().to()))?,
                );
            }
            let mut completed_regional = Vec::new();
            completed_regional
                .try_reserve_exact(regional_results.len())
                .map_err(|_| LiveCurrentError::ResourceReservation)?;
            for (request, result) in regional.iter().zip(regional_results) {
                completed_regional
                    .push(result.ok_or(LiveCurrentError::ExecutionMismatch(request.receiver()))?);
            }
            self.staged = Some(StagedEvent {
                body_key,
                revision: physical_revision,
                lineages: staged_lineages,
            });
            Ok(ExecutedContemporaryEvent::with_regional(
                enacted,
                completed_relations,
                completed_regional,
            ))
        })();
        self.resident_standing = Some(resident_standing);
        if result.is_err() {
            self.staged = None;
        }
        result
    }

    fn settle_physical_successor(
        &mut self,
        physical_revision: u64,
        successor: &SparseStandingSurface,
    ) -> Result<(), LiveCurrentError> {
        self.context.make_current().map_err(substrate)?;
        let staged = self
            .staged
            .take()
            .ok_or(LiveCurrentError::PhysicalSettlement)?;
        if staged.body_key
            != self
                .resident_body_key
                .ok_or(LiveCurrentError::PhysicalSettlement)?
            || staged.revision != physical_revision
            || self.resident_revision != Some(physical_revision)
        {
            return Err(LiveCurrentError::PhysicalSettlement);
        }
        let before = self
            .resident_standing
            .take()
            .ok_or(LiveCurrentError::PhysicalSettlement)?;
        let after = if &before.logical == successor {
            before
        } else {
            match self.prepare_standing_successor(&before, successor) {
                Ok(after) => after,
                Err(error) => {
                    self.resident_standing = Some(before);
                    return Err(error);
                }
            }
        };
        for (lineage, state) in staged.lineages {
            match state {
                StagedCarrier::Continuing(carrier) => {
                    self.resident_lineages.insert(lineage, carrier);
                }
                StagedCarrier::Departed => {
                    self.resident_lineages.remove(&lineage);
                }
            }
        }
        self.resident_standing = Some(after);
        self.resident_revision = Some(physical_revision.wrapping_add(1));
        Ok(())
    }
}

// -------------------------------------------------------------------------------------------------
// The co-present population: one crossing, one lane per current
// -------------------------------------------------------------------------------------------------

/// One current's host-side region, staged at the population's uniform capacities.
struct StagedCurrent {
    control: Vec<u32>,
    relation: Vec<u32>,
    owns: Vec<SparseOwnCell>,
    carrier: Vec<u32>,
    overflow: Vec<u32>,
    overflow_counts: Vec<u32>,
    prior_depth: usize,
    resident: bool,
}

/// The population's uniform mouth. Every region is this wide for every current, because the kernel
/// derives each lane's stride as `len / count` and a ragged buffer would put one current's carrier
/// inside another's.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct PopulationCapacities {
    own: usize,
    max_depth: usize,
    overflow: usize,
    emission: usize,
}

impl CudaLiveCurrentExecutor {
    /// Enact a whole contemporary population in **one** crossing, one lane per current.
    ///
    /// **Why this is exact, structurally rather than by hope.** The kernel body is
    /// `enact_one_lineage`, unchanged and shared with the single-current shell. Each lane calls it
    /// with its own disjoint region, so a lane computes exactly what a single-current crossing
    /// would compute — there is no reduction, no shared accumulator and no atomic on this path.
    ///
    /// The one substantive difference from `enact_one` is that regions are sized by the **widest**
    /// current rather than by each current's own need. That cannot move a result, and the committed
    /// code already relies on it: the resource-retry loop grows capacities and keeps the answer, and
    /// a resident current already runs at a wider capacity than a fresh one. If an enactment
    /// depended on its buffer extents rather than being bounded by them, both of those would already
    /// be wrong.
    fn enact_population(
        &mut self,
        standing_axis: u32,
        standing: &DeviceBuffer<u32>,
        standing_len: usize,
        requests: &[CurrentExecutionRequest<'_>],
        residents: &[Option<&ResidentCarrier>],
        contacts: &[CardContactPopulation],
    ) -> Result<Vec<(ExecutedLiveCurrent, ResidentCarrier)>, LiveCurrentError> {
        let count = requests.len();
        debug_assert_eq!(count, residents.len());
        debug_assert_eq!(count, contacts.len());

        // The population's mouth opens at the widest current's own starting need. Read off the
        // material; nothing here is authored beyond the two floors `enact_one` already declares.
        let mut caps = PopulationCapacities {
            own: 32,
            max_depth: 1,
            overflow: 1,
            emission: 32,
        };
        for (request, resident) in requests.iter().zip(residents) {
            let prior = request.mount().carrier();
            let prior_depth = prior.depth();
            let prior_overflow = (0..prior_depth)
                .map(|depth| prior.co_present_overflow(depth).map_or(0, <[_]>::len))
                .max()
                .unwrap_or(0);
            caps.own = caps.own.max(resident.map_or(32, |r| r.own_capacity.max(32)));
            caps.max_depth = caps.max_depth.max(
                resident
                    .map_or(prior_depth, |r| r.max_depth.max(prior_depth))
                    .max(1),
            );
            caps.overflow = caps.overflow.max(
                resident
                    .map_or(prior_overflow, |r| r.overflow_capacity.max(prior_overflow))
                    .max(1),
            );
            caps.emission = caps
                .emission
                .max(resident.map_or(32, |r| r.emission_capacity.max(32)));
        }

        loop {
            let carrier_extent = checked_mul(caps.max_depth, ENCLOSURE_WORDS)?;
            let overflow_extent =
                checked_mul(checked_mul(caps.max_depth, caps.overflow)?, NODE_WORDS)?;
            let emission_extent = checked_mul(caps.emission, DEED_WORDS)?;

            let mut widest_grain = 0u32;
            let mut staged = Vec::new();
            staged
                .try_reserve_exact(count)
                .map_err(|_| LiveCurrentError::ResourceReservation)?;
            for ((request, resident), contact) in
                requests.iter().zip(residents).zip(contacts)
            {
                let source_grain = request.event().geometry().source_grain()?;
                widest_grain = widest_grain.max(source_grain);
                staged.push(self.stage_one(
                    standing_axis,
                    *request,
                    *resident,
                    contact,
                    caps,
                    carrier_extent,
                    overflow_extent,
                )?);
            }
            self.ensure_live_event_stack(widest_grain, caps.max_depth)?;

            // Concatenate. Every buffer is `count` regions of one uniform extent, which is what
            // makes `len / count` an exact stride inside the kernel.
            let control_flat: Vec<u32> =
                staged.iter().flat_map(|s| s.control.iter().copied()).collect();
            let relation_flat: Vec<u32> =
                staged.iter().flat_map(|s| s.relation.iter().copied()).collect();
            let owns_flat: Vec<SparseOwnCell> =
                staged.iter().flat_map(|s| s.owns.iter().copied()).collect();
            let emissions_flat = vec![0u32; checked_mul(count, emission_extent)?];
            let emanation_flat = vec![0u32; checked_mul(count, cuda::EMANATION_WORDS)?];

            let control_device = upload(&control_flat)?;
            let relations_device = upload(&relation_flat)?;
            let owns_device = upload(&owns_flat)?;
            let emissions_device = upload(&emissions_flat)?;
            let emanation_device = upload(&emanation_flat)?;
            let directed_device = DeviceBuffer::alloc_zeroed(count.max(1)).map_err(substrate)?;
            let contacts_device = DeviceBuffer::alloc_zeroed(count.max(1)).map_err(substrate)?;

            let carriers_device =
                DeviceBuffer::alloc_zeroed(checked_mul(count, carrier_extent)?).map_err(substrate)?;
            let overflow_device = DeviceBuffer::alloc_zeroed(checked_mul(count, overflow_extent)?)
                .map_err(substrate)?;
            let counts_device = DeviceBuffer::alloc_zeroed(checked_mul(count, caps.max_depth)?)
                .map_err(substrate)?;

            for (lane, (stage, resident)) in staged.iter().zip(residents).enumerate() {
                let carrier_at = checked_mul(lane, carrier_extent)?;
                let overflow_at = checked_mul(lane, overflow_extent)?;
                let counts_at = checked_mul(lane, caps.max_depth)?;
                if stage.resident {
                    // The lane's prior carrier already lives on the card. Copy it into this lane's
                    // own region device-to-device rather than round-tripping it through the host.
                    let resident = resident.expect("a resident stage names a resident");
                    let active = checked_mul(stage.prior_depth, ENCLOSURE_WORDS)?;
                    carriers_device
                        .copy_range_from_buffer(carrier_at, &resident.carrier, 0, active)
                        .map_err(substrate)?;
                    counts_device
                        .copy_range_from_buffer(counts_at, &resident.counts, 0, stage.prior_depth)
                        .map_err(substrate)?;
                    let mut copied = active
                        .checked_add(stage.prior_depth)
                        .ok_or(LiveCurrentError::ResourceReservation)?;
                    for row in 0..stage.prior_depth {
                        let held = resident.overflow_counts[row];
                        if held > resident.overflow_capacity {
                            return Err(LiveCurrentError::ExecutionMismatch(
                                requests[lane].lineage(),
                            ));
                        }
                        let words = checked_mul(held, NODE_WORDS)?;
                        if words != 0 {
                            overflow_device
                                .copy_range_from_buffer(
                                    overflow_at
                                        + checked_mul(checked_mul(row, caps.overflow)?, NODE_WORDS)?,
                                    &resident.overflow,
                                    checked_mul(
                                        checked_mul(row, resident.overflow_capacity)?,
                                        NODE_WORDS,
                                    )?,
                                    words,
                                )
                                .map_err(substrate)?;
                        }
                        copied = copied
                            .checked_add(words)
                            .ok_or(LiveCurrentError::ResourceReservation)?;
                    }
                    add_words(&mut self.carrier_device_words, copied)?;
                } else {
                    carriers_device
                        .copy_range_from_slice(carrier_at, &stage.carrier)
                        .map_err(substrate)?;
                    overflow_device
                        .copy_range_from_slice(overflow_at, &stage.overflow)
                        .map_err(substrate)?;
                    counts_device
                        .copy_range_from_slice(counts_at, &stage.overflow_counts)
                        .map_err(substrate)?;
                    self.carrier_full_mounts = self
                        .carrier_full_mounts
                        .checked_add(1)
                        .ok_or(LiveCurrentError::ResourceReservation)?;
                    add_words(
                        &mut self.carrier_host_words,
                        carrier_extent + overflow_extent + caps.max_depth,
                    )?;
                }
            }

            // **The device states what it has, and the demand is refused BY NAME when it does not
            // fit.** Running `count` lanes instead of one multiplies the per-thread local-memory
            // reservation by `count`, so the population's demand genuinely scales with the front --
            // that is the real cost of the repair, not a hidden one. Without this the driver
            // returns a bare `CUDA_ERROR_OUT_OF_MEMORY` with no numbers, which is what surfaced
            // when six card tests ran concurrently, each holding its own context.
            let free = self.context.memory_info().map_err(substrate)?.free_bytes;
            let words: usize = checked_mul(count, cuda::CONTROL_WORDS)?
                + checked_mul(count, COG_WORDS)?
                + checked_mul(count, carrier_extent)?
                + checked_mul(count, overflow_extent)?
                + checked_mul(count, caps.max_depth)?
                + checked_mul(count, emission_extent)?
                + checked_mul(count, cuda::EMANATION_WORDS)?;
            let buffers = checked_mul(words, core::mem::size_of::<u32>())?;
            let owns = checked_mul(
                checked_mul(count, caps.own)?,
                core::mem::size_of::<SparseOwnCell>(),
            )?;
            let local = checked_mul(count, self.stack_limit_bytes)?;
            let demand = buffers
                .checked_add(owns)
                .and_then(|value| value.checked_add(local))
                .ok_or(LiveCurrentError::ResourceReservation)?;
            if demand > free {
                return Err(LiveCurrentError::PopulationExceedsDevice {
                    lanes: count,
                    demanded_bytes: demand as u64,
                    free_bytes: free as u64,
                    per_lane_stack_bytes: self.stack_limit_bytes as u64,
                });
            }

            // ONE crossing. The shape comes from `Function::linear_launch`, which reads it off the
            // function's own attribute and the device census.
            let census = self.device_census()?;
            self.module
                .lineage_event_population()
                .map_err(substrate)?
                .launch(
                    census,
                    LiveEventArguments {
                        standing: LiveEventSpan::prefix(standing, standing_len)
                            .map_err(substrate)?,
                        control: LiveEventSpan::whole(&control_device),
                        relations: LiveEventSpan::whole(&relations_device),
                        owns: LiveEventSpan::whole(&owns_device),
                        carriers: LiveEventSpan::whole(&carriers_device),
                        overflow_nodes: LiveEventSpan::whole(&overflow_device),
                        overflow_counts: LiveEventSpan::whole(&counts_device),
                        directed_events: LiveEventSpan::prefix(&directed_device, 0)
                            .map_err(substrate)?,
                        directed_contacts: LiveEventSpan::prefix(&contacts_device, 0)
                            .map_err(substrate)?,
                        emissions: LiveEventSpan::whole(&emissions_device),
                        emanation: LiveEventSpan::whole(&emanation_device),
                    },
                    count,
                )
                .map_err(substrate)?;
            self.context.synchronize().map_err(substrate)?;
            self.launches = self
                .launches
                .checked_add(1)
                .ok_or(LiveCurrentError::ResourceReservation)?;

            let mut control_read = vec![0u32; control_flat.len()];
            control_device
                .copy_to_slice(&mut control_read)
                .map_err(substrate)?;

            // Resource pressure is a property of the POPULATION: the mouth is uniform, so it grows
            // to the widest requirement any lane reported and the whole population re-crosses.
            let mut grown = caps;
            let mut pressured = false;
            for lane in 0..count {
                let base = lane * cuda::CONTROL_WORDS + cuda::CONTROL_STATUS;
                match control_read[base + cuda::STATUS_KIND] {
                    cuda::STATUS_RESOURCE => {
                        pressured = true;
                        let required_depth = usize::try_from(cuda::join_u64(
                            &control_read,
                            base + cuda::STATUS_REQUIRED_DEPTH_LO,
                            base + cuda::STATUS_REQUIRED_DEPTH_HI,
                        ))
                        .map_err(|_| LiveCurrentError::ResourceReservation)?;
                        let required_own = control_read[base + cuda::STATUS_REQUIRED_OWN] as usize;
                        let required_overflow =
                            control_read[base + cuda::STATUS_REQUIRED_OVERFLOW] as usize;
                        let required_emissions =
                            control_read[base + cuda::STATUS_REQUIRED_EMISSIONS] as usize;
                        if required_own > grown.own {
                            grown.own = next_capacity(grown.own, required_own)?;
                        }
                        if required_depth > grown.max_depth {
                            grown.max_depth = next_capacity(grown.max_depth, required_depth)?;
                        }
                        if required_overflow > grown.overflow {
                            grown.overflow = next_capacity(grown.overflow, required_overflow)?;
                        }
                        if required_emissions > grown.emission {
                            grown.emission = next_capacity(grown.emission, required_emissions)?;
                        }
                    }
                    cuda::STATUS_COMPLETE => {}
                    other => {
                        return Err(LiveCurrentError::ExecutionMismatchStatus(
                            requests[lane].lineage(),
                            "lineage-population-kernel-status",
                            other,
                        ))
                    }
                }
            }
            if pressured {
                if grown == caps {
                    return Err(LiveCurrentError::ExecutionMismatch(requests[0].lineage()));
                }
                caps = grown;
                self.resource_retries = self
                    .resource_retries
                    .checked_add(1)
                    .ok_or(LiveCurrentError::ResourceReservation)?;
                continue;
            }

            return self.decode_population(
                requests,
                &control_read,
                caps,
                carrier_extent,
                overflow_extent,
                emission_extent,
                &owns_device,
                &carriers_device,
                &overflow_device,
                &counts_device,
                &emissions_device,
                &emanation_device,
                contacts,
            );
        }
    }
}

impl CudaLiveCurrentExecutor {
    /// The device's own launch census, taken once at mount. `μ`'s `D` constituent.
    fn device_census(&self) -> Result<::mount::cuda::LaunchCensus, LiveCurrentError> {
        self.launch_census
            .ok_or(LiveCurrentError::PhysicalSettlement)
    }

    /// Stage one current's host region at the population's uniform capacities.
    ///
    /// This is `enact_one`'s packing, taking its capacities as arguments instead of owning them, so
    /// the single-current path and the population path pack byte-identically at equal capacities.
    #[allow(clippy::too_many_arguments)]
    fn stage_one(
        &mut self,
        standing_axis: u32,
        request: CurrentExecutionRequest<'_>,
        resident: Option<&ResidentCarrier>,
        contact: &CardContactPopulation,
        caps: PopulationCapacities,
        carrier_extent: usize,
        overflow_extent: usize,
    ) -> Result<StagedCurrent, LiveCurrentError> {
        let prior = request.mount().carrier();
        let prior_depth = prior.depth();
        let source_grain = request.event().geometry().source_grain()?;
        let (relation_count, relation_host) = match request.event().geometry() {
            CurrentGeometry::Cell(relation) => (1usize, relation.words().to_vec()),
            CurrentGeometry::Complex(_) => (0usize, Vec::new()),
        };
        // Every lane's relation region is one whole cog wide; the lane's DECLARED extent is
        // `PARAM_RELATIONS * COG_WORDS`, which the kernel reads from this control block.
        let mut relation = vec![0u32; COG_WORDS];
        relation[..relation_host.len()].copy_from_slice(&relation_host);

        let mut control = vec![0u32; cuda::CONTROL_WORDS];
        let params = cuda::CONTROL_PARAMS;
        control[params + cuda::PARAM_VERSION] = cuda::LAYOUT_VERSION;
        control[params + cuda::PARAM_STANDING_AXIS] = standing_axis;
        control[params + cuda::PARAM_MOUNT] = request.mount().header().is_some() as u32;
        control[params + cuda::PARAM_WHOLE_DARK] = request.wholly_dark() as u32;
        control[params + cuda::PARAM_ENDING] = request.event().ends_lineage() as u32;
        control[params + cuda::PARAM_OWN_CAPACITY] =
            u32::try_from(caps.own).map_err(|_| LiveCurrentError::ResourceReservation)?;
        control[params + cuda::PARAM_CARRIER_DEPTH] =
            u32::try_from(prior_depth).map_err(|_| LiveCurrentError::ResourceReservation)?;
        control[params + cuda::PARAM_CARRIER_MAX_DEPTH] =
            u32::try_from(caps.max_depth).map_err(|_| LiveCurrentError::ResourceReservation)?;
        control[params + cuda::PARAM_OVERFLOW_CAPACITY] =
            u32::try_from(caps.overflow).map_err(|_| LiveCurrentError::ResourceReservation)?;
        control[params + cuda::PARAM_EMISSION_CAPACITY] =
            u32::try_from(caps.emission).map_err(|_| LiveCurrentError::ResourceReservation)?;
        control[params + cuda::PARAM_RELATIONS] = relation_count as u32;
        control[params + cuda::PARAM_DIRECTED_EVENTS] = 0;
        control[params + cuda::PARAM_SOURCE_GRAIN] = source_grain;
        control[params + cuda::PARAM_COMPLEX] =
            request.event().geometry().complex().is_some() as u32;
        for (lo, hi, value) in [
            (
                cuda::PARAM_EVENT_CELLS_LO,
                cuda::PARAM_EVENT_CELLS_HI,
                request.event().geometry().cells(),
            ),
            (
                cuda::PARAM_EVENT_INCIDENCES_LO,
                cuda::PARAM_EVENT_INCIDENCES_HI,
                request.event().geometry().incidences(),
            ),
            (
                cuda::PARAM_EVENT_RESOLVING_LO,
                cuda::PARAM_EVENT_RESOLVING_HI,
                request.event().geometry().resolving_cells(),
            ),
            (
                cuda::PARAM_EVENT_COMPOUNDS_LO,
                cuda::PARAM_EVENT_COMPOUNDS_HI,
                request.event().geometry().compounds(),
            ),
            (
                cuda::PARAM_EVENT_FORMED_LO,
                cuda::PARAM_EVENT_FORMED_HI,
                contact.formed_incidences,
            ),
        ] {
            control[params + lo] = value as u32;
            control[params + hi] = (value >> 32) as u32;
        }
        let event = cuda::EventRow::new(
            request.face(),
            request
                .mount()
                .seed_anchor()
                .unwrap_or(request.face().place),
            request.event().action().cog(),
            request.pending_dark(),
        )
        .ok_or(LiveCurrentError::ExecutionMismatch(request.lineage()))?;
        control[cuda::CONTROL_EVENT..cuda::CONTROL_EVENT + cuda::EVENT_WORDS]
            .copy_from_slice(&event.words());
        if let Some(header) = request.mount().header() {
            control[cuda::CONTROL_HEADER..cuda::CONTROL_HEADER + CARRIER_HEADER_WORDS]
                .copy_from_slice(header.words());
        }

        let exact_resident = resident.filter(|resident| {
            resident.depth == prior_depth
                && resident.max_depth >= prior_depth
                && resident.overflow_counts.len() == prior_depth
        });
        let mut carrier = Vec::new();
        let mut overflow = Vec::new();
        let mut overflow_counts = Vec::new();
        if exact_resident.is_none() {
            carrier = vec![0u32; carrier_extent];
            overflow = vec![0u32; overflow_extent];
            overflow_counts = vec![0u32; caps.max_depth];
            put_prior_carrier(
                request,
                caps.max_depth,
                caps.overflow,
                &mut carrier,
                &mut overflow,
                &mut overflow_counts,
            )?;
        }

        Ok(StagedCurrent {
            control,
            relation,
            owns: vec![SparseOwnCell::EMPTY; caps.own],
            carrier,
            overflow,
            overflow_counts,
            prior_depth,
            resident: exact_resident.is_some(),
        })
    }

    /// Decode every lane's region. Byte-for-byte the single-current decode, read at the lane's own
    /// offset, and the residency buffers are split back out so `ResidentCarrier`'s contract is
    /// unchanged.
    #[allow(clippy::too_many_arguments)]
    fn decode_population(
        &mut self,
        requests: &[CurrentExecutionRequest<'_>],
        control_read: &[u32],
        caps: PopulationCapacities,
        carrier_extent: usize,
        overflow_extent: usize,
        emission_extent: usize,
        owns_device: &DeviceBuffer<SparseOwnCell>,
        carriers_device: &DeviceBuffer<u32>,
        overflow_device: &DeviceBuffer<u32>,
        counts_device: &DeviceBuffer<u32>,
        emissions_device: &DeviceBuffer<u32>,
        emanation_device: &DeviceBuffer<u32>,
        contacts: &[CardContactPopulation],
    ) -> Result<Vec<(ExecutedLiveCurrent, ResidentCarrier)>, LiveCurrentError> {
        let count = requests.len();
        let mut owns_all = vec![SparseOwnCell::EMPTY; checked_mul(count, caps.own)?];
        owns_device.copy_to_slice(&mut owns_all).map_err(substrate)?;
        let mut carrier_all = vec![0u32; checked_mul(count, carrier_extent)?];
        carriers_device
            .copy_to_slice(&mut carrier_all)
            .map_err(substrate)?;
        let mut overflow_all = vec![0u32; checked_mul(count, overflow_extent)?];
        overflow_device
            .copy_to_slice(&mut overflow_all)
            .map_err(substrate)?;
        let mut counts_all = vec![0u32; checked_mul(count, caps.max_depth)?];
        counts_device
            .copy_to_slice(&mut counts_all)
            .map_err(substrate)?;
        let mut emission_all = vec![0u32; checked_mul(count, emission_extent)?];
        emissions_device
            .copy_to_slice(&mut emission_all)
            .map_err(substrate)?;
        let mut emanation_all = vec![0u32; checked_mul(count, cuda::EMANATION_WORDS)?];
        emanation_device
            .copy_to_slice(&mut emanation_all)
            .map_err(substrate)?;

        let mut decoded = Vec::new();
        decoded
            .try_reserve_exact(count)
            .map_err(|_| LiveCurrentError::ResourceReservation)?;

        for (lane, request) in requests.iter().enumerate() {
            let lineage = request.lineage();
            let control = &control_read[lane * cuda::CONTROL_WORDS..(lane + 1) * cuda::CONTROL_WORDS];
            let state = cuda::CONTROL_STATE;
            let own_axis = control[state + cuda::STATE_OWN_AXIS];
            let own_live = control[state + cuda::STATE_OWN_LIVE] as usize;
            let depth = control[state + cuda::STATE_CARRIER_DEPTH] as usize;
            let emitted = control[state + cuda::STATE_EMISSIONS] as usize;
            if own_axis == 0
                || !own_axis.is_power_of_two()
                || own_live > caps.own
                || depth == 0
                || depth > caps.max_depth
                || emitted > caps.emission
            {
                return Err(LiveCurrentError::ExecutionMismatch(lineage));
            }

            let rank = own_axis.trailing_zeros() as u64;
            let owns = &owns_all[lane * caps.own..lane * caps.own + caps.own];
            let mut contributions = Vec::new();
            contributions
                .try_reserve_exact(own_live)
                .map_err(|_| LiveCurrentError::ResourceReservation)?;
            for cell in owns.iter().copied().take(own_live) {
                let cell = RankedOwnCell::from_flat_at_rank(rank, cell)
                    .map_err(|_| LiveCurrentError::ExecutionMismatch(lineage))?;
                contributions.push((cell.founder(), cell.form()));
            }

            let carrier_at = lane * carrier_extent;
            let overflow_at = lane * overflow_extent;
            let counts_at = lane * caps.max_depth;
            let carrier_words = &carrier_all[carrier_at..carrier_at + carrier_extent];
            let overflow_words = &overflow_all[overflow_at..overflow_at + overflow_extent];
            let count_words = &counts_all[counts_at..counts_at + caps.max_depth];

            let mut overflow = Vec::new();
            overflow
                .try_reserve_exact(depth)
                .map_err(|_| LiveCurrentError::ResourceReservation)?;
            for row in 0..depth {
                let held = count_words[row] as usize;
                if held > caps.overflow {
                    return Err(LiveCurrentError::ExecutionMismatch(lineage));
                }
                let mut nodes = Vec::new();
                nodes
                    .try_reserve_exact(held)
                    .map_err(|_| LiveCurrentError::ResourceReservation)?;
                for ordinal in 0..held {
                    let at = (row * caps.overflow + ordinal) * NODE_WORDS;
                    if !body::manifold::packed_node_is_canonical(overflow_words, at) {
                        return Err(LiveCurrentError::ExecutionMismatch(lineage));
                    }
                    nodes.push(body::manifold::unpack_node(overflow_words, at));
                }
                overflow.push(nodes);
            }

            let header = cuda::header_from_control(control)
                .ok_or(LiveCurrentError::ExecutionMismatch(lineage))?;
            let next = LiveCarrierSnapshot::from_substrate_parts(
                header,
                carrier_words[..depth * ENCLOSURE_WORDS].to_vec(),
                overflow,
            )
            .map_err(LiveCurrentError::Carrier)?;

            let mut event_words = [0u32; cuda::EVENT_WORDS];
            event_words.copy_from_slice(
                &control[cuda::CONTROL_EVENT..cuda::CONTROL_EVENT + cuda::EVENT_WORDS],
            );
            let pending_dark = cuda::EventRow::from_words(event_words)
                .ok_or(LiveCurrentError::ExecutionMismatch(lineage))?
                .pending_dark();

            let emissions_at = lane * emission_extent;
            let mut emissions = Vec::new();
            emissions
                .try_reserve_exact(emitted)
                .map_err(|_| LiveCurrentError::ResourceReservation)?;
            for ordinal in 0..emitted {
                let at = emissions_at + ordinal * DEED_WORDS;
                let row: [u32; DEED_WORDS] = emission_all[at..at + DEED_WORDS]
                    .try_into()
                    .map_err(|_| LiveCurrentError::ExecutionMismatch(lineage))?;
                let emission = DeedEmission::from_words(row)
                    .ok_or(LiveCurrentError::ExecutionMismatch(lineage))?;
                emissions.push(emission.felt_emission());
            }

            let emanation_at = lane * cuda::EMANATION_WORDS;
            let emanation_row: [u32; cuda::EMANATION_WORDS] = emanation_all
                [emanation_at..emanation_at + cuda::EMANATION_WORDS]
                .try_into()
                .map_err(|_| LiveCurrentError::ExecutionMismatch(lineage))?;
            let consequence = cuda::EmanationRow::from_words(emanation_row)
                .ok_or(LiveCurrentError::ExecutionMismatch(lineage))?
                .emanation();

            // Split this lane's region back into its own buffers so residency is unchanged.
            let carrier_own = DeviceBuffer::alloc_zeroed(carrier_extent).map_err(substrate)?;
            carrier_own
                .copy_range_from_buffer(0, carriers_device, carrier_at, carrier_extent)
                .map_err(substrate)?;
            let overflow_own = DeviceBuffer::alloc_zeroed(overflow_extent).map_err(substrate)?;
            overflow_own
                .copy_range_from_buffer(0, overflow_device, overflow_at, overflow_extent)
                .map_err(substrate)?;
            let counts_own = DeviceBuffer::alloc_zeroed(caps.max_depth).map_err(substrate)?;
            counts_own
                .copy_range_from_buffer(0, counts_device, counts_at, caps.max_depth)
                .map_err(substrate)?;

            let witness = carrier_witness(Some(header), next.carrier())?;
            let resident = ResidentCarrier {
                witness,
                depth,
                max_depth: caps.max_depth,
                own_capacity: caps.own,
                emission_capacity: caps.emission,
                overflow_capacity: caps.overflow,
                overflow_counts: count_words[..depth].iter().map(|c| *c as usize).collect(),
                carrier: carrier_own,
                overflow: overflow_own,
                counts: counts_own,
            };
            decoded.push((
                ExecutedLiveCurrent::new(
                    lineage,
                    next,
                    pending_dark,
                    consequence,
                    emissions,
                    contacts[lane].incidences.clone(),
                    contributions,
                ),
                resident,
            ));
        }
        Ok(decoded)
    }
}

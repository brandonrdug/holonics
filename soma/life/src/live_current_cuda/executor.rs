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
            for current in currents {
                let contacts = self.form_card_contact_population(
                    resident_standing.axis,
                    &resident_standing.device,
                    resident_standing.words,
                    *current,
                    relations,
                    regional,
                )?;
                let witness = carrier_witness(current.mount().header(), current.mount().carrier())?;
                let prior_resident = self.resident_lineages.remove(&current.lineage());
                let exact_resident = prior_resident
                    .as_ref()
                    .filter(|resident| resident.witness == witness);
                let outcome = self.enact_one(
                    resident_standing.axis,
                    &resident_standing.device,
                    resident_standing.words,
                    *current,
                    exact_resident,
                    &[],
                    &contacts.incidences,
                    contacts.formed_incidences,
                );
                if let Some(prior) = prior_resident {
                    self.resident_lineages.insert(current.lineage(), prior);
                }
                let (enacted_current, resolved, next_resident) = outcome?;
                if !resolved.is_empty() {
                    return Err(LiveCurrentError::ExecutionMismatch(current.lineage()));
                }
                enacted.push(enacted_current);
                let staged = if current.event().ends_lineage() {
                    StagedCarrier::Departed
                } else {
                    StagedCarrier::Continuing(next_resident)
                };
                if staged_lineages.insert(current.lineage(), staged).is_some() {
                    return Err(LiveCurrentError::ExecutionMismatch(current.lineage()));
                }
                for (at, relation) in contacts.directed {
                    if relation_results[at].replace(relation).is_some() {
                        return Err(LiveCurrentError::ExecutionMismatch(current.lineage()));
                    }
                }
                for (at, relation) in contacts.regional {
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

use super::*;

impl CudaRefineExecutor {
    /// Conduct one shared state action through every declared modality and receiver family.
    ///
    /// `decoder` is family-major, port-major, state-minor. The same `successor_action` is read by
    /// every lane; a second per-port action table is neither accepted nor constructed. The global
    /// and every single-port ablation are returned together after one terminal synchronization.
    pub fn conduct_heterogeneous_fusion_on_device(
        &mut self,
        successor_action: &[u32],
        decoder: &[u32],
        native_start: &[u32],
        families: usize,
        ports: usize,
    ) -> Result<DeviceHeterogeneousFusion, CudaRefineError> {
        let states = successor_action.len();
        let cells = families
            .checked_mul(ports)
            .ok_or(CudaRefineError::NativeActionTooWide)?;
        let expected_decoder = cells
            .checked_mul(states)
            .ok_or(CudaRefineError::NativeActionTooWide)?;
        let local_entries = cells
            .checked_mul(ports)
            .ok_or(CudaRefineError::NativeActionTooWide)?;
        if states == 0
            || families == 0
            || ports < 2
            || cells == 0
            || cells > u32::MAX as usize
            || states > u32::MAX as usize
            || ports > u32::MAX as usize
            || decoder.len() != expected_decoder
            || native_start.len() != cells
        {
            return Err(CudaRefineError::NativeActionTooWide);
        }
        if let Some(state) = successor_action
            .iter()
            .chain(native_start)
            .copied()
            .find(|state| *state as usize >= states)
        {
            return Err(CudaRefineError::NativeStateOutsidePopulation { state, states });
        }

        driver(unsafe { cuCtxSetCurrent(self.context) }, "cuCtxSetCurrent")?;
        let action = Buffer::of(successor_action)?;
        let decoder_device = Buffer::of(decoder)?;
        let starts = Buffer::of(native_start)?;
        let cell_octets = cells * std::mem::size_of::<u32>();
        let predecessor = Buffer::alloc(cell_octets)?;
        let successor = Buffer::alloc(cell_octets)?;
        let shared_ablated = Buffer::alloc(cell_octets)?;
        let local_octets = local_entries * std::mem::size_of::<u32>();
        let local_ablated = Buffer::alloc(local_octets)?;

        let grid = self.grid_for(cells as u64)?;
        let mut action_pointer = action.pointer;
        let mut decoder_pointer = decoder_device.pointer;
        let mut starts_pointer = starts.pointer;
        let mut predecessor_pointer = predecessor.pointer;
        let mut successor_pointer = successor.pointer;
        let mut shared_ablated_pointer = shared_ablated.pointer;
        let mut local_ablated_pointer = local_ablated.pointer;
        let mut cell_count = cells as u32;
        let mut state_count = states as u32;
        let mut port_count = ports as u32;
        let mut arguments: [*mut c_void; 10] = [
            &mut action_pointer as *mut u64 as *mut c_void,
            &mut decoder_pointer as *mut u64 as *mut c_void,
            &mut starts_pointer as *mut u64 as *mut c_void,
            &mut predecessor_pointer as *mut u64 as *mut c_void,
            &mut successor_pointer as *mut u64 as *mut c_void,
            &mut shared_ablated_pointer as *mut u64 as *mut c_void,
            &mut local_ablated_pointer as *mut u64 as *mut c_void,
            &mut cell_count as *mut u32 as *mut c_void,
            &mut state_count as *mut u32 as *mut c_void,
            &mut port_count as *mut u32 as *mut c_void,
        ];
        driver(
            unsafe {
                cuLaunchKernel(
                    self.heterogeneous_fusion,
                    grid,
                    1,
                    1,
                    self.block_x,
                    1,
                    1,
                    0,
                    ptr::null_mut(),
                    arguments.as_mut_ptr(),
                    ptr::null_mut(),
                )
            },
            "cuLaunchKernel(conduct_heterogeneous_fusion)",
        )?;
        driver(unsafe { cuCtxSynchronize() }, "cuCtxSynchronize")?;
        self.launches += 1;

        let mut predecessor_consequence = vec![0u32; cells];
        let mut successor_consequence = vec![0u32; cells];
        let mut shared_ablated_consequence = vec![0u32; cells];
        let mut local_ablated_consequence = vec![0u32; local_entries];
        predecessor.read(&mut predecessor_consequence)?;
        successor.read(&mut successor_consequence)?;
        shared_ablated.read(&mut shared_ablated_consequence)?;
        local_ablated.read(&mut local_ablated_consequence)?;

        let action_octets = std::mem::size_of_val(successor_action) as u64;
        let decoder_octets = std::mem::size_of_val(decoder) as u64;
        let start_octets = std::mem::size_of_val(native_start) as u64;
        let cell_octets = cell_octets as u64;
        let local_octets = local_octets as u64;
        let scalar_ingress_octets = 3 * std::mem::size_of::<u32>() as u64;
        Ok(DeviceHeterogeneousFusion {
            predecessor_consequence,
            successor_consequence,
            shared_ablated_consequence,
            local_ablated_consequence,
            families,
            ports,
            launches: 1,
            synchronizations: 1,
            block_threads: self.block_x,
            active_lanes: cells as u32,
            host_ingress_octets: action_octets
                + decoder_octets
                + start_octets
                + scalar_ingress_octets,
            host_egress_octets: cell_octets * 3 + local_octets,
            resident_octets: action_octets
                + decoder_octets
                + start_octets
                + cell_octets * 3
                + local_octets,
        })
    }

    /// Derive the complete candidate multiplicity of each source anchor/port cell on the card.
    /// Long exterior addresses have already crossed the codec mouth into exact local indices; the
    /// kernel visits every candidate for every cell and returns no winner or confidence quotient.
    pub fn derive_media_candidate_counts_on_device(
        &mut self,
        pair_anchor: &[u32],
        pair_port: &[u32],
        anchors: usize,
        ports: usize,
    ) -> Result<DeviceMediaCandidateCounts, CudaRefineError> {
        let cells = anchors
            .checked_mul(ports)
            .ok_or(CudaRefineError::JointMediaPassageShape)?;
        if anchors == 0
            || ports < 2
            || cells == 0
            || cells > u32::MAX as usize
            || pair_anchor.is_empty()
            || pair_anchor.len() != pair_port.len()
            || pair_anchor.len() > u32::MAX as usize
            || pair_anchor.iter().any(|anchor| *anchor as usize >= anchors)
            || pair_port.iter().any(|port| *port as usize >= ports)
        {
            return Err(CudaRefineError::JointMediaPassageShape);
        }

        driver(unsafe { cuCtxSetCurrent(self.context) }, "cuCtxSetCurrent")?;
        let anchors_device = Buffer::of(pair_anchor)?;
        let ports_device = Buffer::of(pair_port)?;
        let count_octets = cells * std::mem::size_of::<u32>();
        let counts_device = Buffer::alloc(count_octets)?;
        let grid = self.grid_for(cells as u64)?;
        let mut anchor_pointer = anchors_device.pointer;
        let mut port_pointer = ports_device.pointer;
        let mut count_pointer = counts_device.pointer;
        let mut anchor_count = anchors as u32;
        let mut port_count = ports as u32;
        let mut pair_count = pair_anchor.len() as u32;
        let mut arguments: [*mut c_void; 6] = [
            &mut anchor_pointer as *mut u64 as *mut c_void,
            &mut port_pointer as *mut u64 as *mut c_void,
            &mut count_pointer as *mut u64 as *mut c_void,
            &mut anchor_count as *mut u32 as *mut c_void,
            &mut port_count as *mut u32 as *mut c_void,
            &mut pair_count as *mut u32 as *mut c_void,
        ];
        driver(
            unsafe {
                cuLaunchKernel(
                    self.media_candidate_counts,
                    grid,
                    1,
                    1,
                    self.block_x,
                    1,
                    1,
                    0,
                    ptr::null_mut(),
                    arguments.as_mut_ptr(),
                    ptr::null_mut(),
                )
            },
            "cuLaunchKernel(derive_media_candidate_counts)",
        )?;
        driver(unsafe { cuCtxSynchronize() }, "cuCtxSynchronize")?;
        self.launches += 1;
        let mut candidate_counts = vec![0u32; cells];
        counts_device.read(&mut candidate_counts)?;

        let anchor_octets = std::mem::size_of_val(pair_anchor) as u64;
        let port_octets = std::mem::size_of_val(pair_port) as u64;
        let scalar_octets = 3 * std::mem::size_of::<u32>() as u64;
        let semantic_pair_visits = (cells as u128)
            .checked_mul(pair_anchor.len() as u128)
            .ok_or(CudaRefineError::JointMediaPassageShape)?;
        Ok(DeviceMediaCandidateCounts {
            candidate_counts,
            anchors,
            ports,
            pairs: pair_anchor.len(),
            launches: 1,
            synchronizations: 1,
            block_threads: self.block_x,
            active_lanes: cells as u32,
            semantic_pair_visits,
            host_ingress_octets: anchor_octets + port_octets + scalar_octets,
            host_egress_octets: count_octets as u64,
            resident_octets: anchor_octets + port_octets + count_octets as u64,
        })
    }

    /// Enact one compact shared-media subcomplex and all its withdrawals in one resident front.
    #[allow(clippy::too_many_arguments)]
    pub fn conduct_joint_media_transport_on_device(
        &mut self,
        candidate_counts: &[u32],
        anchors: usize,
        successor_action: &[u32],
        decoder: &[u32],
        native_start: &[u32],
        families: usize,
        ports: usize,
    ) -> Result<DeviceJointMediaTransport, CudaRefineError> {
        let states = successor_action.len();
        let anchor_cells = anchors
            .checked_mul(ports)
            .ok_or(CudaRefineError::JointMediaPassageShape)?;
        let cells = families
            .checked_mul(ports)
            .ok_or(CudaRefineError::JointMediaPassageShape)?;
        let expected_decoder = cells
            .checked_mul(states)
            .ok_or(CudaRefineError::JointMediaPassageShape)?;
        let local_anchor_entries = anchor_cells;
        let local_entries = cells
            .checked_mul(ports)
            .ok_or(CudaRefineError::JointMediaPassageShape)?;
        let work = anchors.max(cells);
        if anchors == 0
            || families == 0
            || ports < 2
            || states == 0
            || work == 0
            || work > u32::MAX as usize
            || candidate_counts.len() != anchor_cells
            || candidate_counts.iter().any(|count| *count == 0)
            || decoder.len() != expected_decoder
            || native_start.len() != cells
            || successor_action
                .iter()
                .chain(native_start)
                .any(|state| *state as usize >= states)
        {
            return Err(CudaRefineError::JointMediaPassageShape);
        }

        driver(unsafe { cuCtxSetCurrent(self.context) }, "cuCtxSetCurrent")?;
        let counts_device = Buffer::of(candidate_counts)?;
        let action_device = Buffer::of(successor_action)?;
        let decoder_device = Buffer::of(decoder)?;
        let starts_device = Buffer::of(native_start)?;
        let anchor_octets = anchors * std::mem::size_of::<u32>();
        let local_anchor_octets = local_anchor_entries * std::mem::size_of::<u32>();
        let cell_octets = cells * std::mem::size_of::<u32>();
        let local_octets = local_entries * std::mem::size_of::<u32>();
        let joint_device = Buffer::alloc(anchor_octets)?;
        let shared_joint_device = Buffer::alloc(anchor_octets)?;
        let local_joint_device = Buffer::alloc(local_anchor_octets)?;
        let predecessor_device = Buffer::alloc(cell_octets)?;
        let successor_device = Buffer::alloc(cell_octets)?;
        let shared_device = Buffer::alloc(cell_octets)?;
        let local_device = Buffer::alloc(local_octets)?;

        let grid = self.grid_for(work as u64)?;
        let mut counts_pointer = counts_device.pointer;
        let mut joint_pointer = joint_device.pointer;
        let mut shared_joint_pointer = shared_joint_device.pointer;
        let mut local_joint_pointer = local_joint_device.pointer;
        let mut anchor_count = anchors as u32;
        let mut action_pointer = action_device.pointer;
        let mut decoder_pointer = decoder_device.pointer;
        let mut starts_pointer = starts_device.pointer;
        let mut predecessor_pointer = predecessor_device.pointer;
        let mut successor_pointer = successor_device.pointer;
        let mut shared_pointer = shared_device.pointer;
        let mut local_pointer = local_device.pointer;
        let mut cell_count = cells as u32;
        let mut state_count = states as u32;
        let mut port_count = ports as u32;
        let mut arguments: [*mut c_void; 15] = [
            &mut counts_pointer as *mut u64 as *mut c_void,
            &mut joint_pointer as *mut u64 as *mut c_void,
            &mut shared_joint_pointer as *mut u64 as *mut c_void,
            &mut local_joint_pointer as *mut u64 as *mut c_void,
            &mut anchor_count as *mut u32 as *mut c_void,
            &mut action_pointer as *mut u64 as *mut c_void,
            &mut decoder_pointer as *mut u64 as *mut c_void,
            &mut starts_pointer as *mut u64 as *mut c_void,
            &mut predecessor_pointer as *mut u64 as *mut c_void,
            &mut successor_pointer as *mut u64 as *mut c_void,
            &mut shared_pointer as *mut u64 as *mut c_void,
            &mut local_pointer as *mut u64 as *mut c_void,
            &mut cell_count as *mut u32 as *mut c_void,
            &mut state_count as *mut u32 as *mut c_void,
            &mut port_count as *mut u32 as *mut c_void,
        ];
        driver(
            unsafe {
                cuLaunchKernel(
                    self.joint_media_transport,
                    grid,
                    1,
                    1,
                    self.block_x,
                    1,
                    1,
                    0,
                    ptr::null_mut(),
                    arguments.as_mut_ptr(),
                    ptr::null_mut(),
                )
            },
            "cuLaunchKernel(conduct_joint_media_transport)",
        )?;
        driver(unsafe { cuCtxSynchronize() }, "cuCtxSynchronize")?;
        self.launches += 1;

        let mut joint_anchor = vec![0u32; anchors];
        let mut shared_ablated_joint_anchor = vec![0u32; anchors];
        let mut local_ablated_joint_anchor = vec![0u32; local_anchor_entries];
        let mut predecessor_consequence = vec![0u32; cells];
        let mut successor_consequence = vec![0u32; cells];
        let mut shared_ablated_consequence = vec![0u32; cells];
        let mut local_ablated_consequence = vec![0u32; local_entries];
        joint_device.read(&mut joint_anchor)?;
        shared_joint_device.read(&mut shared_ablated_joint_anchor)?;
        local_joint_device.read(&mut local_ablated_joint_anchor)?;
        predecessor_device.read(&mut predecessor_consequence)?;
        successor_device.read(&mut successor_consequence)?;
        shared_device.read(&mut shared_ablated_consequence)?;
        local_device.read(&mut local_ablated_consequence)?;

        let count_octets = std::mem::size_of_val(candidate_counts) as u64;
        let action_octets = std::mem::size_of_val(successor_action) as u64;
        let decoder_octets = std::mem::size_of_val(decoder) as u64;
        let start_octets = std::mem::size_of_val(native_start) as u64;
        let scalar_octets = 4 * std::mem::size_of::<u32>() as u64;
        let returned_octets =
            (anchor_octets * 2 + local_anchor_octets + cell_octets * 3 + local_octets) as u64;
        Ok(DeviceJointMediaTransport {
            joint_anchor,
            shared_ablated_joint_anchor,
            local_ablated_joint_anchor,
            predecessor_consequence,
            successor_consequence,
            shared_ablated_consequence,
            local_ablated_consequence,
            anchors,
            families,
            ports,
            launches: 1,
            synchronizations: 1,
            block_threads: self.block_x,
            active_lanes: work as u32,
            host_ingress_octets: count_octets
                + action_octets
                + decoder_octets
                + start_octets
                + scalar_octets,
            host_egress_octets: returned_octets,
            resident_octets: count_octets
                + action_octets
                + decoder_octets
                + start_octets
                + returned_octets,
        })
    }

    /// Conduct R6's context, derivation, and mathematical-media fronts independently, then join
    /// only their complete exact returns through one typed reduction on the same CUDA stream.
    /// There is one synchronization after both launches and no host semantic callback between.
    #[allow(clippy::too_many_arguments)]
    pub fn conduct_production_aperture_on_device(
        &mut self,
        context_table: &[u32],
        context_states: usize,
        context_word: &[u32],
        context_start: &[u32],
        derivation_predecessor_action: &[u32],
        derivation_successor_action: &[u32],
        derivation_start: &[u32],
        media_candidate_species: &[u32],
        media_anchors: usize,
        media_species_port: &[u32],
        media_ports: usize,
        left_species: usize,
        right_species: usize,
        committed: bool,
    ) -> Result<DeviceProductionAperture, CudaRefineError> {
        let context_generators = context_table
            .len()
            .checked_div(context_states.max(1))
            .ok_or(CudaRefineError::ProductionApertureShape)?;
        let context_trace_stride = context_word
            .len()
            .checked_add(1)
            .ok_or(CudaRefineError::ProductionApertureShape)?;
        let context_trace_entries = context_start
            .len()
            .checked_mul(context_trace_stride)
            .ok_or(CudaRefineError::ProductionApertureShape)?;
        let derivation_states = derivation_predecessor_action.len();
        let derivation_trace_stride = derivation_states
            .checked_add(1)
            .ok_or(CudaRefineError::ProductionApertureShape)?;
        let derivation_trace_entries = derivation_start
            .len()
            .checked_mul(derivation_trace_stride)
            .ok_or(CudaRefineError::ProductionApertureShape)?;
        let media_species = media_species_port.len();
        let media_entries = media_anchors
            .checked_mul(media_species)
            .ok_or(CudaRefineError::ProductionApertureShape)?;
        let local_entries = media_species
            .checked_mul(media_ports)
            .ok_or(CudaRefineError::ProductionApertureShape)?;
        let active_lanes = context_start
            .len()
            .max(derivation_start.len())
            .max(media_anchors);
        let maximum_media_total = media_candidate_species
            .iter()
            .try_fold(0_u128, |total, value| total.checked_add(u128::from(*value)))
            .ok_or(CudaRefineError::ProductionApertureShape)?;
        if context_states == 0
            || context_table.len() != context_generators * context_states
            || context_generators < 2
            || context_word.is_empty()
            || context_start.len() < 2
            || context_states > u32::MAX as usize
            || context_word.len() > u32::MAX as usize
            || context_start.len() > u32::MAX as usize
            || context_table
                .iter()
                .any(|state| *state as usize >= context_states)
            || context_start
                .iter()
                .any(|state| *state as usize >= context_states)
            || context_word
                .iter()
                .any(|generator| *generator as usize >= context_generators)
            || derivation_states < 2
            || derivation_successor_action.len() != derivation_states
            || derivation_start.len() < 2
            || derivation_states > u32::MAX as usize
            || derivation_start.len() > u32::MAX as usize
            || derivation_predecessor_action
                .iter()
                .chain(derivation_successor_action)
                .chain(derivation_start)
                .any(|state| *state as usize >= derivation_states)
            || media_anchors == 0
            || media_species < 3
            || media_ports < 2
            || media_entries != media_candidate_species.len()
            || media_entries > u32::MAX as usize
            || media_candidate_species.iter().any(|count| *count == 0)
            || media_species_port
                .iter()
                .any(|port| *port as usize >= media_ports)
            || left_species >= media_species
            || right_species >= media_species
            || left_species == right_species
            || media_anchors > u32::MAX as usize
            || media_species > u32::MAX as usize
            || media_ports > u32::MAX as usize
            || active_lanes == 0
            || active_lanes > u32::MAX as usize
            || maximum_media_total > i64::MAX as u128
        {
            return Err(CudaRefineError::ProductionApertureShape);
        }

        driver(unsafe { cuCtxSetCurrent(self.context) }, "cuCtxSetCurrent")?;
        let context_table_device = Buffer::of(context_table)?;
        let context_word_device = Buffer::of(context_word)?;
        let context_start_device = Buffer::of(context_start)?;
        let context_trace_octets = context_trace_entries * std::mem::size_of::<u32>();
        let context_trace_device = Buffer::alloc(context_trace_octets)?;
        let context_withdrawn_device = Buffer::alloc(context_trace_octets)?;

        let derivation_predecessor_device = Buffer::of(derivation_predecessor_action)?;
        let derivation_successor_device = Buffer::of(derivation_successor_action)?;
        let derivation_start_device = Buffer::of(derivation_start)?;
        let derivation_trace_octets = derivation_trace_entries * std::mem::size_of::<u32>();
        let derivation_predecessor_trace_device = Buffer::alloc(derivation_trace_octets)?;
        let derivation_successor_trace_device = Buffer::alloc(derivation_trace_octets)?;
        let derivation_selected_trace_device = Buffer::alloc(derivation_trace_octets)?;
        let derivation_generator_withdrawn_trace_device = Buffer::alloc(derivation_trace_octets)?;
        let derivation_length_octets = derivation_start.len() * std::mem::size_of::<u32>();
        let derivation_predecessor_length_device = Buffer::alloc(derivation_length_octets)?;
        let derivation_successor_length_device = Buffer::alloc(derivation_length_octets)?;
        let derivation_selected_length_device = Buffer::alloc(derivation_length_octets)?;
        let derivation_generator_withdrawn_length_device = Buffer::alloc(derivation_length_octets)?;

        let media_candidate_device = Buffer::of(media_candidate_species)?;
        let media_species_port_device = Buffer::of(media_species_port)?;
        let media_totals_octets = media_species * std::mem::size_of::<u64>();
        let media_totals_device = Buffer::alloc(media_totals_octets)?;
        media_totals_device.fill(0, media_totals_octets)?;
        let media_joint_device = Buffer::alloc(std::mem::size_of::<u64>())?;
        media_joint_device.fill(0, std::mem::size_of::<u64>())?;
        let media_shared_device = Buffer::alloc(media_totals_octets)?;
        let media_local_octets = local_entries * std::mem::size_of::<u64>();
        let media_local_device = Buffer::alloc(media_local_octets)?;
        let total_joint_device = Buffer::alloc(std::mem::size_of::<u64>())?;
        let oriented_difference_device = Buffer::alloc(std::mem::size_of::<i64>())?;
        let difference_magnitude_device = Buffer::alloc(std::mem::size_of::<u64>())?;
        let difference_hand_device = Buffer::alloc(std::mem::size_of::<i32>())?;
        let selected_cultivation_device = Buffer::alloc(std::mem::size_of::<u32>())?;

        let mut context_table_pointer = context_table_device.pointer;
        let mut context_word_pointer = context_word_device.pointer;
        let mut context_start_pointer = context_start_device.pointer;
        let mut context_trace_pointer = context_trace_device.pointer;
        let mut context_withdrawn_pointer = context_withdrawn_device.pointer;
        let mut context_cell_count = context_start.len() as u32;
        let mut context_state_count = context_states as u32;
        let mut context_word_length = context_word.len() as u32;
        let mut derivation_predecessor_pointer = derivation_predecessor_device.pointer;
        let mut derivation_successor_pointer = derivation_successor_device.pointer;
        let mut derivation_start_pointer = derivation_start_device.pointer;
        let mut derivation_predecessor_trace_pointer = derivation_predecessor_trace_device.pointer;
        let mut derivation_successor_trace_pointer = derivation_successor_trace_device.pointer;
        let mut derivation_selected_trace_pointer = derivation_selected_trace_device.pointer;
        let mut derivation_generator_withdrawn_trace_pointer =
            derivation_generator_withdrawn_trace_device.pointer;
        let mut derivation_predecessor_length_pointer =
            derivation_predecessor_length_device.pointer;
        let mut derivation_successor_length_pointer = derivation_successor_length_device.pointer;
        let mut derivation_selected_length_pointer = derivation_selected_length_device.pointer;
        let mut derivation_generator_withdrawn_length_pointer =
            derivation_generator_withdrawn_length_device.pointer;
        let mut derivation_cell_count = derivation_start.len() as u32;
        let mut derivation_state_count = derivation_states as u32;
        let mut media_candidate_pointer = media_candidate_device.pointer;
        let mut media_totals_pointer = media_totals_device.pointer;
        let mut media_joint_pointer = media_joint_device.pointer;
        let mut media_anchor_count = media_anchors as u32;
        let mut media_species_count = media_species as u32;
        let mut decision = u32::from(committed);
        let mut front_arguments: [*mut c_void; 27] = [
            &mut context_table_pointer as *mut u64 as *mut c_void,
            &mut context_word_pointer as *mut u64 as *mut c_void,
            &mut context_start_pointer as *mut u64 as *mut c_void,
            &mut context_trace_pointer as *mut u64 as *mut c_void,
            &mut context_withdrawn_pointer as *mut u64 as *mut c_void,
            &mut context_cell_count as *mut u32 as *mut c_void,
            &mut context_state_count as *mut u32 as *mut c_void,
            &mut context_word_length as *mut u32 as *mut c_void,
            &mut derivation_predecessor_pointer as *mut u64 as *mut c_void,
            &mut derivation_successor_pointer as *mut u64 as *mut c_void,
            &mut derivation_start_pointer as *mut u64 as *mut c_void,
            &mut derivation_predecessor_trace_pointer as *mut u64 as *mut c_void,
            &mut derivation_successor_trace_pointer as *mut u64 as *mut c_void,
            &mut derivation_selected_trace_pointer as *mut u64 as *mut c_void,
            &mut derivation_generator_withdrawn_trace_pointer as *mut u64 as *mut c_void,
            &mut derivation_predecessor_length_pointer as *mut u64 as *mut c_void,
            &mut derivation_successor_length_pointer as *mut u64 as *mut c_void,
            &mut derivation_selected_length_pointer as *mut u64 as *mut c_void,
            &mut derivation_generator_withdrawn_length_pointer as *mut u64 as *mut c_void,
            &mut derivation_cell_count as *mut u32 as *mut c_void,
            &mut derivation_state_count as *mut u32 as *mut c_void,
            &mut media_candidate_pointer as *mut u64 as *mut c_void,
            &mut media_totals_pointer as *mut u64 as *mut c_void,
            &mut media_joint_pointer as *mut u64 as *mut c_void,
            &mut media_anchor_count as *mut u32 as *mut c_void,
            &mut media_species_count as *mut u32 as *mut c_void,
            &mut decision as *mut u32 as *mut c_void,
        ];
        let grid = self.grid_for(active_lanes as u64)?;
        driver(
            unsafe {
                cuLaunchKernel(
                    self.production_aperture_fronts,
                    grid,
                    1,
                    1,
                    self.block_x,
                    1,
                    1,
                    0,
                    ptr::null_mut(),
                    front_arguments.as_mut_ptr(),
                    ptr::null_mut(),
                )
            },
            "cuLaunchKernel(conduct_production_aperture_fronts)",
        )?;
        self.launches += 1;

        let mut media_species_port_pointer = media_species_port_device.pointer;
        let mut media_shared_pointer = media_shared_device.pointer;
        let mut media_local_pointer = media_local_device.pointer;
        let mut total_joint_pointer = total_joint_device.pointer;
        let mut oriented_difference_pointer = oriented_difference_device.pointer;
        let mut difference_magnitude_pointer = difference_magnitude_device.pointer;
        let mut difference_hand_pointer = difference_hand_device.pointer;
        let mut selected_cultivation_pointer = selected_cultivation_device.pointer;
        let mut media_port_count = media_ports as u32;
        let mut left = left_species as u32;
        let mut right = right_species as u32;
        let mut reduction_arguments: [*mut c_void; 14] = [
            &mut media_totals_pointer as *mut u64 as *mut c_void,
            &mut media_species_port_pointer as *mut u64 as *mut c_void,
            &mut media_shared_pointer as *mut u64 as *mut c_void,
            &mut media_local_pointer as *mut u64 as *mut c_void,
            &mut total_joint_pointer as *mut u64 as *mut c_void,
            &mut oriented_difference_pointer as *mut u64 as *mut c_void,
            &mut difference_magnitude_pointer as *mut u64 as *mut c_void,
            &mut difference_hand_pointer as *mut u64 as *mut c_void,
            &mut selected_cultivation_pointer as *mut u64 as *mut c_void,
            &mut media_species_count as *mut u32 as *mut c_void,
            &mut media_port_count as *mut u32 as *mut c_void,
            &mut left as *mut u32 as *mut c_void,
            &mut right as *mut u32 as *mut c_void,
            &mut decision as *mut u32 as *mut c_void,
        ];
        driver(
            unsafe {
                cuLaunchKernel(
                    self.production_aperture_reduction,
                    1,
                    1,
                    1,
                    self.block_x,
                    1,
                    1,
                    0,
                    ptr::null_mut(),
                    reduction_arguments.as_mut_ptr(),
                    ptr::null_mut(),
                )
            },
            "cuLaunchKernel(reduce_production_aperture_fronts)",
        )?;
        self.launches += 1;
        driver(unsafe { cuCtxSynchronize() }, "cuCtxSynchronize")?;

        let mut context_trace = vec![0_u32; context_trace_entries];
        let mut context_boundary_withdrawn_trace = vec![0_u32; context_trace_entries];
        context_trace_device.read(&mut context_trace)?;
        context_withdrawn_device.read(&mut context_boundary_withdrawn_trace)?;
        let mut derivation_predecessor_trace = vec![0_u32; derivation_trace_entries];
        let mut derivation_successor_trace = vec![0_u32; derivation_trace_entries];
        let mut derivation_selected_trace = vec![0_u32; derivation_trace_entries];
        let mut derivation_generator_withdrawn_trace = vec![0_u32; derivation_trace_entries];
        derivation_predecessor_trace_device.read(&mut derivation_predecessor_trace)?;
        derivation_successor_trace_device.read(&mut derivation_successor_trace)?;
        derivation_selected_trace_device.read(&mut derivation_selected_trace)?;
        derivation_generator_withdrawn_trace_device
            .read(&mut derivation_generator_withdrawn_trace)?;
        let mut derivation_predecessor_lengths = vec![0_u32; derivation_start.len()];
        let mut derivation_successor_lengths = vec![0_u32; derivation_start.len()];
        let mut derivation_selected_lengths = vec![0_u32; derivation_start.len()];
        let mut derivation_generator_withdrawn_lengths = vec![0_u32; derivation_start.len()];
        derivation_predecessor_length_device.read(&mut derivation_predecessor_lengths)?;
        derivation_successor_length_device.read(&mut derivation_successor_lengths)?;
        derivation_selected_length_device.read(&mut derivation_selected_lengths)?;
        derivation_generator_withdrawn_length_device
            .read(&mut derivation_generator_withdrawn_lengths)?;
        if derivation_predecessor_lengths
            .iter()
            .chain(&derivation_successor_lengths)
            .chain(&derivation_selected_lengths)
            .chain(&derivation_generator_withdrawn_lengths)
            .any(|length| *length < 2 || *length as usize > derivation_trace_stride)
        {
            return Err(CudaRefineError::ProductionApertureShape);
        }
        let selected_expected = if committed {
            (&derivation_successor_trace, &derivation_successor_lengths)
        } else {
            (
                &derivation_predecessor_trace,
                &derivation_predecessor_lengths,
            )
        };
        if &derivation_selected_trace != selected_expected.0
            || &derivation_selected_lengths != selected_expected.1
        {
            return Err(CudaRefineError::ProductionApertureShape);
        }

        let mut media_species_totals = vec![0_u64; media_species];
        let mut media_shared_withdrawn_totals = vec![0_u64; media_species];
        let mut media_local_withdrawn_totals = vec![0_u64; local_entries];
        let mut media_joint_anchors = [0_u64];
        let mut total_joint_incidence = [0_u64];
        let mut oriented_difference = [0_i64];
        let mut difference_magnitude = [0_u64];
        let mut difference_hand = [0_i32];
        let mut selected_cultivation_state = [0_u32];
        media_totals_device.read(&mut media_species_totals)?;
        media_shared_device.read(&mut media_shared_withdrawn_totals)?;
        media_local_device.read(&mut media_local_withdrawn_totals)?;
        media_joint_device.read(&mut media_joint_anchors)?;
        total_joint_device.read(&mut total_joint_incidence)?;
        oriented_difference_device.read(&mut oriented_difference)?;
        difference_magnitude_device.read(&mut difference_magnitude)?;
        difference_hand_device.read(&mut difference_hand)?;
        selected_cultivation_device.read(&mut selected_cultivation_state)?;
        if media_joint_anchors[0] != media_anchors as u64
            || selected_cultivation_state[0] != u32::from(committed)
            || media_shared_withdrawn_totals
                .iter()
                .any(|value| *value != 0)
            || oriented_difference[0].unsigned_abs() != difference_magnitude[0]
            || oriented_difference[0].signum() != i64::from(difference_hand[0])
        {
            return Err(CudaRefineError::ProductionApertureShape);
        }

        let context_work = (context_start.len() as u128) * (context_word.len() as u128);
        let derivation_work =
            (derivation_start.len() as u128) * (derivation_states as u128) * 4_u128;
        let media_work = (media_anchors as u128) * (media_species as u128);
        let reduction_work = (media_species as u128) * (media_ports as u128 + 2_u128) + 5_u128;
        let semantic_work = context_work + derivation_work + media_work + reduction_work;
        let semantic_span = (context_word.len() as u64)
            .max(derivation_states as u64)
            .max((media_species * (media_ports + 2) + 5) as u64);
        let ingress = std::mem::size_of_val(context_table)
            + std::mem::size_of_val(context_word)
            + std::mem::size_of_val(context_start)
            + std::mem::size_of_val(derivation_predecessor_action)
            + std::mem::size_of_val(derivation_successor_action)
            + std::mem::size_of_val(derivation_start)
            + std::mem::size_of_val(media_candidate_species)
            + std::mem::size_of_val(media_species_port)
            + 12 * std::mem::size_of::<u32>();
        let egress = context_trace_octets * 2
            + derivation_trace_octets * 4
            + derivation_length_octets * 4
            + media_totals_octets * 2
            + media_local_octets
            + 3 * std::mem::size_of::<u64>()
            + std::mem::size_of::<i64>()
            + std::mem::size_of::<i32>()
            + std::mem::size_of::<u32>();
        let resident = ingress
            .checked_add(egress)
            .ok_or(CudaRefineError::ProductionApertureShape)?;
        Ok(DeviceProductionAperture {
            context_trace,
            context_boundary_withdrawn_trace,
            context_trace_stride,
            derivation_predecessor_trace,
            derivation_successor_trace,
            derivation_selected_trace,
            derivation_generator_withdrawn_trace,
            derivation_predecessor_lengths,
            derivation_successor_lengths,
            derivation_selected_lengths,
            derivation_generator_withdrawn_lengths,
            derivation_trace_stride,
            media_species_totals,
            media_shared_withdrawn_totals,
            media_local_withdrawn_totals,
            media_joint_anchors: media_joint_anchors[0],
            total_joint_incidence: total_joint_incidence[0],
            oriented_difference: oriented_difference[0],
            difference_magnitude: difference_magnitude[0],
            difference_hand: difference_hand[0],
            selected_cultivation_state: selected_cultivation_state[0],
            context_fronts: context_start.len(),
            derivation_fronts: derivation_start.len(),
            media_anchors,
            media_species,
            media_ports,
            committed,
            launches: 2,
            synchronizations: 1,
            typed_reductions: 1,
            block_threads: self.block_x,
            active_lanes: active_lanes as u32,
            semantic_work,
            semantic_span,
            host_ingress_octets: ingress as u64,
            host_egress_octets: egress as u64,
            resident_octets: resident as u64,
        })
    }
}

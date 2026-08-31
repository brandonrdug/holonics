use super::*;

impl CudaRefineExecutor {
    /// Conduct the recurrent passage and every admitted heterogeneous face in one resident front.
    /// The decision is data crossing the front, not a host-selected semantic branch between I3 and
    /// I4. Both alternative routes and all withdrawals return as dissection testimony.
    #[allow(clippy::too_many_arguments)]
    pub fn conduct_inference_ecology_on_device(
        &mut self,
        recurrent_action: &[u32],
        recurrent_start: &[u32],
        recurrent_predecessor_from: u32,
        recurrent_predecessor_to: u32,
        world_action: &[u32],
        world_decoder: &[u32],
        world_start: &[u32],
        families: usize,
        ports: usize,
        committed: bool,
    ) -> Result<DeviceInferenceEcology, CudaRefineError> {
        let recurrent_states = recurrent_action.len();
        let recurrent_cells = recurrent_start.len();
        let trace_stride = recurrent_states
            .checked_add(1)
            .ok_or(CudaRefineError::NativeActionTooWide)?;
        let trace_entries = recurrent_cells
            .checked_mul(trace_stride)
            .ok_or(CudaRefineError::NativeActionTooWide)?;
        let visited_words = recurrent_states
            .checked_add(u32::BITS as usize - 1)
            .ok_or(CudaRefineError::NativeActionTooWide)?
            / u32::BITS as usize;
        let visited_entries = recurrent_cells
            .checked_mul(4)
            .and_then(|rows| rows.checked_mul(visited_words))
            .ok_or(CudaRefineError::NativeActionTooWide)?;

        let world_states = world_action.len();
        let world_cells = families
            .checked_mul(ports)
            .ok_or(CudaRefineError::NativeActionTooWide)?;
        let expected_decoder = world_cells
            .checked_mul(world_states)
            .ok_or(CudaRefineError::NativeActionTooWide)?;
        let local_entries = world_cells
            .checked_mul(ports)
            .ok_or(CudaRefineError::NativeActionTooWide)?;
        let active_lanes = recurrent_cells.max(world_cells);
        if recurrent_states == 0
            || recurrent_cells == 0
            || world_states == 0
            || world_cells == 0
            || ports < 2
            || world_decoder.len() != expected_decoder
            || world_start.len() != world_cells
            || active_lanes > u32::MAX as usize
            || recurrent_states > u32::MAX as usize
            || world_states > u32::MAX as usize
            || ports > u32::MAX as usize
            || visited_words > u32::MAX as usize
        {
            return Err(CudaRefineError::NativeActionTooWide);
        }
        if let Some(state) = recurrent_action
            .iter()
            .chain(recurrent_start)
            .copied()
            .chain([recurrent_predecessor_from, recurrent_predecessor_to])
            .find(|state| *state as usize >= recurrent_states)
        {
            return Err(CudaRefineError::NativeStateOutsidePopulation {
                state,
                states: recurrent_states,
            });
        }
        if recurrent_action[recurrent_predecessor_from as usize] == recurrent_predecessor_to {
            return Err(CudaRefineError::NativeActionTooWide);
        }
        if let Some(state) = world_action
            .iter()
            .chain(world_start)
            .copied()
            .find(|state| *state as usize >= world_states)
        {
            return Err(CudaRefineError::NativeStateOutsidePopulation {
                state,
                states: world_states,
            });
        }

        driver(unsafe { cuCtxSetCurrent(self.context) }, "cuCtxSetCurrent")?;
        let recurrent_action_device = Buffer::of(recurrent_action)?;
        let recurrent_start_device = Buffer::of(recurrent_start)?;
        let trace_octets = trace_entries * std::mem::size_of::<u32>();
        let predecessor_trace_device = Buffer::alloc(trace_octets)?;
        let successor_trace_device = Buffer::alloc(trace_octets)?;
        let withdrawn_trace_device = Buffer::alloc(trace_octets)?;
        let selected_trace_device = Buffer::alloc(trace_octets)?;
        let length_octets = recurrent_cells * std::mem::size_of::<u32>();
        let predecessor_length_device = Buffer::alloc(length_octets)?;
        let successor_length_device = Buffer::alloc(length_octets)?;
        let withdrawn_length_device = Buffer::alloc(length_octets)?;
        let selected_length_device = Buffer::alloc(length_octets)?;
        let visited_octets = visited_entries * std::mem::size_of::<u32>();
        let visited_device = Buffer::alloc(visited_octets)?;
        visited_device.fill(0, visited_octets)?;

        let world_action_device = Buffer::of(world_action)?;
        let world_decoder_device = Buffer::of(world_decoder)?;
        let world_start_device = Buffer::of(world_start)?;
        let world_cell_octets = world_cells * std::mem::size_of::<u32>();
        let world_predecessor_device = Buffer::alloc(world_cell_octets)?;
        let world_successor_device = Buffer::alloc(world_cell_octets)?;
        let world_selected_device = Buffer::alloc(world_cell_octets)?;
        let world_shared_ablated_device = Buffer::alloc(world_cell_octets)?;
        let world_local_octets = local_entries * std::mem::size_of::<u32>();
        let world_local_ablated_device = Buffer::alloc(world_local_octets)?;

        let mut recurrent_action_pointer = recurrent_action_device.pointer;
        let mut recurrent_start_pointer = recurrent_start_device.pointer;
        let mut predecessor_trace_pointer = predecessor_trace_device.pointer;
        let mut successor_trace_pointer = successor_trace_device.pointer;
        let mut withdrawn_trace_pointer = withdrawn_trace_device.pointer;
        let mut selected_trace_pointer = selected_trace_device.pointer;
        let mut predecessor_length_pointer = predecessor_length_device.pointer;
        let mut successor_length_pointer = successor_length_device.pointer;
        let mut withdrawn_length_pointer = withdrawn_length_device.pointer;
        let mut selected_length_pointer = selected_length_device.pointer;
        let mut visited_pointer = visited_device.pointer;
        let mut recurrent_cell_count = recurrent_cells as u32;
        let mut recurrent_state_count = recurrent_states as u32;
        let mut recurrent_seen_words = visited_words as u32;
        let mut local_from = recurrent_predecessor_from;
        let mut local_to = recurrent_predecessor_to;
        let mut world_action_pointer = world_action_device.pointer;
        let mut world_decoder_pointer = world_decoder_device.pointer;
        let mut world_start_pointer = world_start_device.pointer;
        let mut world_predecessor_pointer = world_predecessor_device.pointer;
        let mut world_successor_pointer = world_successor_device.pointer;
        let mut world_selected_pointer = world_selected_device.pointer;
        let mut world_shared_ablated_pointer = world_shared_ablated_device.pointer;
        let mut world_local_ablated_pointer = world_local_ablated_device.pointer;
        let mut world_cell_count = world_cells as u32;
        let mut world_state_count = world_states as u32;
        let mut world_port_count = ports as u32;
        let mut decision = u32::from(committed);
        let mut arguments: [*mut c_void; 28] = [
            &mut recurrent_action_pointer as *mut u64 as *mut c_void,
            &mut recurrent_start_pointer as *mut u64 as *mut c_void,
            &mut predecessor_trace_pointer as *mut u64 as *mut c_void,
            &mut successor_trace_pointer as *mut u64 as *mut c_void,
            &mut withdrawn_trace_pointer as *mut u64 as *mut c_void,
            &mut selected_trace_pointer as *mut u64 as *mut c_void,
            &mut predecessor_length_pointer as *mut u64 as *mut c_void,
            &mut successor_length_pointer as *mut u64 as *mut c_void,
            &mut withdrawn_length_pointer as *mut u64 as *mut c_void,
            &mut selected_length_pointer as *mut u64 as *mut c_void,
            &mut visited_pointer as *mut u64 as *mut c_void,
            &mut recurrent_cell_count as *mut u32 as *mut c_void,
            &mut recurrent_state_count as *mut u32 as *mut c_void,
            &mut recurrent_seen_words as *mut u32 as *mut c_void,
            &mut local_from as *mut u32 as *mut c_void,
            &mut local_to as *mut u32 as *mut c_void,
            &mut world_action_pointer as *mut u64 as *mut c_void,
            &mut world_decoder_pointer as *mut u64 as *mut c_void,
            &mut world_start_pointer as *mut u64 as *mut c_void,
            &mut world_predecessor_pointer as *mut u64 as *mut c_void,
            &mut world_successor_pointer as *mut u64 as *mut c_void,
            &mut world_selected_pointer as *mut u64 as *mut c_void,
            &mut world_shared_ablated_pointer as *mut u64 as *mut c_void,
            &mut world_local_ablated_pointer as *mut u64 as *mut c_void,
            &mut world_cell_count as *mut u32 as *mut c_void,
            &mut world_state_count as *mut u32 as *mut c_void,
            &mut world_port_count as *mut u32 as *mut c_void,
            &mut decision as *mut u32 as *mut c_void,
        ];
        let grid = self.grid_for(active_lanes as u64)?;
        driver(
            unsafe {
                cuLaunchKernel(
                    self.inference_ecology,
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
            "cuLaunchKernel(conduct_inference_ecology)",
        )?;
        driver(unsafe { cuCtxSynchronize() }, "cuCtxSynchronize")?;
        self.launches += 1;

        let mut predecessor_trace = vec![0u32; trace_entries];
        let mut successor_trace = vec![0u32; trace_entries];
        let mut withdrawn_trace = vec![0u32; trace_entries];
        let mut selected_trace = vec![0u32; trace_entries];
        let mut predecessor_lengths = vec![0u32; recurrent_cells];
        let mut successor_lengths = vec![0u32; recurrent_cells];
        let mut withdrawn_lengths = vec![0u32; recurrent_cells];
        let mut selected_lengths = vec![0u32; recurrent_cells];
        predecessor_trace_device.read(&mut predecessor_trace)?;
        successor_trace_device.read(&mut successor_trace)?;
        withdrawn_trace_device.read(&mut withdrawn_trace)?;
        selected_trace_device.read(&mut selected_trace)?;
        predecessor_length_device.read(&mut predecessor_lengths)?;
        successor_length_device.read(&mut successor_lengths)?;
        withdrawn_length_device.read(&mut withdrawn_lengths)?;
        selected_length_device.read(&mut selected_lengths)?;
        for (at, length) in predecessor_lengths
            .iter()
            .chain(&successor_lengths)
            .chain(&withdrawn_lengths)
            .chain(&selected_lengths)
            .copied()
            .enumerate()
        {
            if length < 2 || length as usize > trace_stride {
                return Err(CudaRefineError::NativeRecurrenceDidNotClose {
                    at: at % recurrent_cells,
                });
            }
        }

        let mut predecessor_consequence = vec![0u32; world_cells];
        let mut successor_consequence = vec![0u32; world_cells];
        let mut selected_consequence = vec![0u32; world_cells];
        let mut shared_ablated_consequence = vec![0u32; world_cells];
        let mut local_ablated_consequence = vec![0u32; local_entries];
        world_predecessor_device.read(&mut predecessor_consequence)?;
        world_successor_device.read(&mut successor_consequence)?;
        world_selected_device.read(&mut selected_consequence)?;
        world_shared_ablated_device.read(&mut shared_ablated_consequence)?;
        world_local_ablated_device.read(&mut local_ablated_consequence)?;
        let selected_expected = if committed {
            (&successor_trace, &successor_lengths, &successor_consequence)
        } else {
            (
                &predecessor_trace,
                &predecessor_lengths,
                &predecessor_consequence,
            )
        };
        if &selected_trace != selected_expected.0
            || &selected_lengths != selected_expected.1
            || &selected_consequence != selected_expected.2
        {
            return Err(CudaRefineError::NativeActionTooWide);
        }

        let recurrent_action_octets = std::mem::size_of_val(recurrent_action) as u64;
        let recurrent_start_octets = std::mem::size_of_val(recurrent_start) as u64;
        let trace_octets = trace_octets as u64;
        let length_octets = length_octets as u64;
        let visited_octets = visited_octets as u64;
        let world_action_octets = std::mem::size_of_val(world_action) as u64;
        let world_decoder_octets = std::mem::size_of_val(world_decoder) as u64;
        let world_start_octets = std::mem::size_of_val(world_start) as u64;
        let world_cell_octets = world_cell_octets as u64;
        let world_local_octets = world_local_octets as u64;
        let scalar_ingress_octets = 9 * std::mem::size_of::<u32>() as u64;
        let host_ingress_octets = recurrent_action_octets
            + recurrent_start_octets
            + world_action_octets
            + world_decoder_octets
            + world_start_octets
            + scalar_ingress_octets;
        let host_egress_octets =
            trace_octets * 4 + length_octets * 4 + world_cell_octets * 4 + world_local_octets;
        Ok(DeviceInferenceEcology {
            predecessor_trace,
            successor_trace,
            withdrawn_trace,
            selected_trace,
            predecessor_lengths,
            successor_lengths,
            withdrawn_lengths,
            selected_lengths,
            trace_stride,
            predecessor_consequence,
            successor_consequence,
            selected_consequence,
            shared_ablated_consequence,
            local_ablated_consequence,
            families,
            ports,
            committed,
            launches: 1,
            synchronizations: 1,
            block_threads: self.block_x,
            active_lanes: active_lanes as u32,
            visited_words,
            host_ingress_octets,
            host_egress_octets,
            resident_octets: host_ingress_octets + host_egress_octets + visited_octets,
        })
    }

    /// Conduct one addressed material-to-operation passage through every unchanged I5 start.
    /// Presentation branches form a full pullback with the recurrent/world starts: no host-side
    /// semantic representative is chosen. Quotient, contact, M1 entry, recurrence, section, and
    /// heterogeneous consequence return under one kernel launch and one terminal synchronization.
    #[allow(clippy::too_many_arguments)]
    pub fn conduct_material_operation_world_tube_on_device(
        &mut self,
        face_payload_keys: &[[u64; 4]],
        face_branch: &[u32],
        branch_staging_events: &[u64],
        branch_terminal_events: &[u64],
        contact_from: &[u32],
        contact_to: &[u32],
        contact_relation: &[u32],
        recurrent_action: &[u32],
        recurrent_start: &[u32],
        recurrent_predecessor_from: u32,
        recurrent_predecessor_to: u32,
        world_action: &[u32],
        world_decoder: &[u32],
        world_start: &[u32],
        families: usize,
        ports: usize,
        committed: bool,
    ) -> Result<DeviceMaterialOperationWorldTube, CudaRefineError> {
        let face_count = face_payload_keys.len();
        let contact_count = contact_from.len();
        let branch_count = branch_staging_events.len();
        let recurrent_states = recurrent_action.len();
        let recurrent_cells_per_branch = recurrent_start.len();
        let world_states = world_action.len();
        let world_cells_per_branch = families
            .checked_mul(ports)
            .ok_or(CudaRefineError::MaterialOperationPassageShape)?;
        let recurrent_cells = branch_count
            .checked_mul(recurrent_cells_per_branch)
            .ok_or(CudaRefineError::MaterialOperationPassageShape)?;
        let world_cells = branch_count
            .checked_mul(world_cells_per_branch)
            .ok_or(CudaRefineError::MaterialOperationPassageShape)?;
        let total_families = branch_count
            .checked_mul(families)
            .ok_or(CudaRefineError::MaterialOperationPassageShape)?;
        if face_count == 0
            || contact_count == 0
            || branch_count < 2
            || recurrent_states == 0
            || recurrent_cells_per_branch == 0
            || world_states == 0
            || world_cells_per_branch == 0
            || ports < 2
            || face_branch.len() != face_count
            || branch_terminal_events.len() != branch_count
            || contact_to.len() != contact_count
            || contact_relation.len() != contact_count
            || world_start.len() != world_cells_per_branch
            || world_decoder.len()
                != world_cells_per_branch
                    .checked_mul(world_states)
                    .ok_or(CudaRefineError::MaterialOperationPassageShape)?
            || face_branch
                .iter()
                .any(|branch| *branch as usize >= branch_count)
            || contact_from
                .iter()
                .chain(contact_to)
                .any(|face| *face as usize >= face_count)
            || [
                face_count,
                contact_count,
                branch_count,
                recurrent_cells,
                recurrent_states,
                recurrent_cells_per_branch,
                world_cells,
                world_cells_per_branch,
                world_states,
                ports,
            ]
            .iter()
            .any(|extent| *extent > u32::MAX as usize)
        {
            return Err(CudaRefineError::MaterialOperationPassageShape);
        }
        if recurrent_action
            .iter()
            .chain(recurrent_start)
            .copied()
            .chain([recurrent_predecessor_from, recurrent_predecessor_to])
            .any(|state| state as usize >= recurrent_states)
            || recurrent_action[recurrent_predecessor_from as usize] == recurrent_predecessor_to
            || world_action
                .iter()
                .chain(world_start)
                .any(|state| *state as usize >= world_states)
        {
            return Err(CudaRefineError::MaterialOperationPassageShape);
        }

        let trace_stride = recurrent_states
            .checked_add(1)
            .ok_or(CudaRefineError::MaterialOperationPassageShape)?;
        let trace_entries = recurrent_cells
            .checked_mul(trace_stride)
            .ok_or(CudaRefineError::MaterialOperationPassageShape)?;
        let visited_words = recurrent_states
            .checked_add(u32::BITS as usize - 1)
            .ok_or(CudaRefineError::MaterialOperationPassageShape)?
            / u32::BITS as usize;
        let visited_entries = recurrent_cells
            .checked_mul(4)
            .and_then(|rows| rows.checked_mul(visited_words))
            .ok_or(CudaRefineError::MaterialOperationPassageShape)?;
        let local_entries = world_cells
            .checked_mul(ports)
            .ok_or(CudaRefineError::MaterialOperationPassageShape)?;
        let active_lanes = face_count
            .max(contact_count)
            .max(recurrent_cells)
            .max(world_cells);

        driver(unsafe { cuCtxSetCurrent(self.context) }, "cuCtxSetCurrent")?;
        let face_key_device = Buffer::of(face_payload_keys)?;
        let face_branch_device = Buffer::of(face_branch)?;
        let branch_staging_device = Buffer::of(branch_staging_events)?;
        let branch_terminal_device = Buffer::of(branch_terminal_events)?;
        let contact_from_device = Buffer::of(contact_from)?;
        let contact_to_device = Buffer::of(contact_to)?;
        let contact_relation_device = Buffer::of(contact_relation)?;
        let face_u32_octets = face_count * std::mem::size_of::<u32>();
        let face_u64_octets = face_count * std::mem::size_of::<u64>();
        let contact_u32_octets = contact_count * std::mem::size_of::<u32>();
        let recurrence_u64_octets = recurrent_cells * std::mem::size_of::<u64>();
        let payload_class_device = Buffer::alloc(face_u32_octets)?;
        let payload_comparison_device = Buffer::alloc(face_u32_octets)?;
        let face_staging_device = Buffer::alloc(face_u64_octets)?;
        let face_terminal_device = Buffer::alloc(face_u64_octets)?;
        let contact_left_class_device = Buffer::alloc(contact_u32_octets)?;
        let contact_right_class_device = Buffer::alloc(contact_u32_octets)?;
        let contact_relation_out_device = Buffer::alloc(contact_u32_octets)?;
        let recurrence_staging_device = Buffer::alloc(recurrence_u64_octets)?;
        let recurrence_terminal_device = Buffer::alloc(recurrence_u64_octets)?;

        let recurrent_action_device = Buffer::of(recurrent_action)?;
        let recurrent_start_device = Buffer::of(recurrent_start)?;
        let trace_octets = trace_entries * std::mem::size_of::<u32>();
        let predecessor_trace_device = Buffer::alloc(trace_octets)?;
        let successor_trace_device = Buffer::alloc(trace_octets)?;
        let withdrawn_trace_device = Buffer::alloc(trace_octets)?;
        let selected_trace_device = Buffer::alloc(trace_octets)?;
        let length_octets = recurrent_cells * std::mem::size_of::<u32>();
        let predecessor_length_device = Buffer::alloc(length_octets)?;
        let successor_length_device = Buffer::alloc(length_octets)?;
        let withdrawn_length_device = Buffer::alloc(length_octets)?;
        let selected_length_device = Buffer::alloc(length_octets)?;
        let visited_octets = visited_entries * std::mem::size_of::<u32>();
        let visited_device = Buffer::alloc(visited_octets)?;
        visited_device.fill(0, visited_octets)?;

        let world_action_device = Buffer::of(world_action)?;
        let world_decoder_device = Buffer::of(world_decoder)?;
        let world_start_device = Buffer::of(world_start)?;
        let world_cell_octets = world_cells * std::mem::size_of::<u32>();
        let world_predecessor_device = Buffer::alloc(world_cell_octets)?;
        let world_successor_device = Buffer::alloc(world_cell_octets)?;
        let world_selected_device = Buffer::alloc(world_cell_octets)?;
        let world_shared_ablated_device = Buffer::alloc(world_cell_octets)?;
        let world_local_octets = local_entries * std::mem::size_of::<u32>();
        let world_local_ablated_device = Buffer::alloc(world_local_octets)?;

        let mut face_key_pointer = face_key_device.pointer;
        let mut face_branch_pointer = face_branch_device.pointer;
        let mut branch_staging_pointer = branch_staging_device.pointer;
        let mut branch_terminal_pointer = branch_terminal_device.pointer;
        let mut contact_from_pointer = contact_from_device.pointer;
        let mut contact_to_pointer = contact_to_device.pointer;
        let mut contact_relation_pointer = contact_relation_device.pointer;
        let mut payload_class_pointer = payload_class_device.pointer;
        let mut payload_comparison_pointer = payload_comparison_device.pointer;
        let mut face_staging_pointer = face_staging_device.pointer;
        let mut face_terminal_pointer = face_terminal_device.pointer;
        let mut contact_left_class_pointer = contact_left_class_device.pointer;
        let mut contact_right_class_pointer = contact_right_class_device.pointer;
        let mut contact_relation_out_pointer = contact_relation_out_device.pointer;
        let mut recurrence_staging_pointer = recurrence_staging_device.pointer;
        let mut recurrence_terminal_pointer = recurrence_terminal_device.pointer;
        let mut face_count_wire = face_count as u32;
        let mut contact_count_wire = contact_count as u32;
        let mut branch_count_wire = branch_count as u32;
        let mut recurrence_cells_per_branch_wire = recurrent_cells_per_branch as u32;
        let mut recurrent_action_pointer = recurrent_action_device.pointer;
        let mut recurrent_start_pointer = recurrent_start_device.pointer;
        let mut predecessor_trace_pointer = predecessor_trace_device.pointer;
        let mut successor_trace_pointer = successor_trace_device.pointer;
        let mut withdrawn_trace_pointer = withdrawn_trace_device.pointer;
        let mut selected_trace_pointer = selected_trace_device.pointer;
        let mut predecessor_length_pointer = predecessor_length_device.pointer;
        let mut successor_length_pointer = successor_length_device.pointer;
        let mut withdrawn_length_pointer = withdrawn_length_device.pointer;
        let mut selected_length_pointer = selected_length_device.pointer;
        let mut visited_pointer = visited_device.pointer;
        let mut recurrent_cell_count = recurrent_cells as u32;
        let mut recurrent_state_count = recurrent_states as u32;
        let mut recurrent_seen_words = visited_words as u32;
        let mut local_from = recurrent_predecessor_from;
        let mut local_to = recurrent_predecessor_to;
        let mut world_action_pointer = world_action_device.pointer;
        let mut world_decoder_pointer = world_decoder_device.pointer;
        let mut world_start_pointer = world_start_device.pointer;
        let mut world_predecessor_pointer = world_predecessor_device.pointer;
        let mut world_successor_pointer = world_successor_device.pointer;
        let mut world_selected_pointer = world_selected_device.pointer;
        let mut world_shared_ablated_pointer = world_shared_ablated_device.pointer;
        let mut world_local_ablated_pointer = world_local_ablated_device.pointer;
        let mut world_cell_count = world_cells as u32;
        let mut world_cells_per_branch_wire = world_cells_per_branch as u32;
        let mut world_state_count = world_states as u32;
        let mut world_port_count = ports as u32;
        let mut decision = u32::from(committed);
        let mut arguments: Vec<*mut c_void> = vec![
            &mut face_key_pointer as *mut u64 as *mut c_void,
            &mut face_branch_pointer as *mut u64 as *mut c_void,
            &mut branch_staging_pointer as *mut u64 as *mut c_void,
            &mut branch_terminal_pointer as *mut u64 as *mut c_void,
            &mut contact_from_pointer as *mut u64 as *mut c_void,
            &mut contact_to_pointer as *mut u64 as *mut c_void,
            &mut contact_relation_pointer as *mut u64 as *mut c_void,
            &mut payload_class_pointer as *mut u64 as *mut c_void,
            &mut payload_comparison_pointer as *mut u64 as *mut c_void,
            &mut face_staging_pointer as *mut u64 as *mut c_void,
            &mut face_terminal_pointer as *mut u64 as *mut c_void,
            &mut contact_left_class_pointer as *mut u64 as *mut c_void,
            &mut contact_right_class_pointer as *mut u64 as *mut c_void,
            &mut contact_relation_out_pointer as *mut u64 as *mut c_void,
            &mut recurrence_staging_pointer as *mut u64 as *mut c_void,
            &mut recurrence_terminal_pointer as *mut u64 as *mut c_void,
            &mut face_count_wire as *mut u32 as *mut c_void,
            &mut contact_count_wire as *mut u32 as *mut c_void,
            &mut branch_count_wire as *mut u32 as *mut c_void,
            &mut recurrence_cells_per_branch_wire as *mut u32 as *mut c_void,
            &mut recurrent_action_pointer as *mut u64 as *mut c_void,
            &mut recurrent_start_pointer as *mut u64 as *mut c_void,
            &mut predecessor_trace_pointer as *mut u64 as *mut c_void,
            &mut successor_trace_pointer as *mut u64 as *mut c_void,
            &mut withdrawn_trace_pointer as *mut u64 as *mut c_void,
            &mut selected_trace_pointer as *mut u64 as *mut c_void,
            &mut predecessor_length_pointer as *mut u64 as *mut c_void,
            &mut successor_length_pointer as *mut u64 as *mut c_void,
            &mut withdrawn_length_pointer as *mut u64 as *mut c_void,
            &mut selected_length_pointer as *mut u64 as *mut c_void,
            &mut visited_pointer as *mut u64 as *mut c_void,
            &mut recurrent_cell_count as *mut u32 as *mut c_void,
            &mut recurrent_state_count as *mut u32 as *mut c_void,
            &mut recurrent_seen_words as *mut u32 as *mut c_void,
            &mut local_from as *mut u32 as *mut c_void,
            &mut local_to as *mut u32 as *mut c_void,
            &mut world_action_pointer as *mut u64 as *mut c_void,
            &mut world_decoder_pointer as *mut u64 as *mut c_void,
            &mut world_start_pointer as *mut u64 as *mut c_void,
            &mut world_predecessor_pointer as *mut u64 as *mut c_void,
            &mut world_successor_pointer as *mut u64 as *mut c_void,
            &mut world_selected_pointer as *mut u64 as *mut c_void,
            &mut world_shared_ablated_pointer as *mut u64 as *mut c_void,
            &mut world_local_ablated_pointer as *mut u64 as *mut c_void,
            &mut world_cell_count as *mut u32 as *mut c_void,
            &mut world_cells_per_branch_wire as *mut u32 as *mut c_void,
            &mut world_state_count as *mut u32 as *mut c_void,
            &mut world_port_count as *mut u32 as *mut c_void,
            &mut decision as *mut u32 as *mut c_void,
        ];
        driver(
            unsafe {
                cuLaunchKernel(
                    self.material_operation_world_tube,
                    self.grid_for(active_lanes as u64)?,
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
            "cuLaunchKernel(conduct_material_operation_world_tube)",
        )?;
        driver(unsafe { cuCtxSynchronize() }, "cuCtxSynchronize")?;
        self.launches += 1;

        let mut payload_classes = vec![0u32; face_count];
        let mut payload_comparisons = vec![0u32; face_count];
        let mut face_staging_events = vec![0u64; face_count];
        let mut face_terminal_events = vec![0u64; face_count];
        let mut contact_left_classes = vec![0u32; contact_count];
        let mut contact_right_classes = vec![0u32; contact_count];
        let mut contact_relations = vec![0u32; contact_count];
        let mut recurrence_staging_events = vec![0u64; recurrent_cells];
        let mut recurrence_terminal_events = vec![0u64; recurrent_cells];
        payload_class_device.read(&mut payload_classes)?;
        payload_comparison_device.read(&mut payload_comparisons)?;
        face_staging_device.read(&mut face_staging_events)?;
        face_terminal_device.read(&mut face_terminal_events)?;
        contact_left_class_device.read(&mut contact_left_classes)?;
        contact_right_class_device.read(&mut contact_right_classes)?;
        contact_relation_out_device.read(&mut contact_relations)?;
        recurrence_staging_device.read(&mut recurrence_staging_events)?;
        recurrence_terminal_device.read(&mut recurrence_terminal_events)?;

        let mut predecessor_trace = vec![0u32; trace_entries];
        let mut successor_trace = vec![0u32; trace_entries];
        let mut withdrawn_trace = vec![0u32; trace_entries];
        let mut selected_trace = vec![0u32; trace_entries];
        let mut predecessor_lengths = vec![0u32; recurrent_cells];
        let mut successor_lengths = vec![0u32; recurrent_cells];
        let mut withdrawn_lengths = vec![0u32; recurrent_cells];
        let mut selected_lengths = vec![0u32; recurrent_cells];
        predecessor_trace_device.read(&mut predecessor_trace)?;
        successor_trace_device.read(&mut successor_trace)?;
        withdrawn_trace_device.read(&mut withdrawn_trace)?;
        selected_trace_device.read(&mut selected_trace)?;
        predecessor_length_device.read(&mut predecessor_lengths)?;
        successor_length_device.read(&mut successor_lengths)?;
        withdrawn_length_device.read(&mut withdrawn_lengths)?;
        selected_length_device.read(&mut selected_lengths)?;
        if predecessor_lengths
            .iter()
            .chain(&successor_lengths)
            .chain(&withdrawn_lengths)
            .chain(&selected_lengths)
            .enumerate()
            .any(|(at, length)| {
                let _ = at;
                *length < 2 || *length as usize > trace_stride
            })
        {
            return Err(CudaRefineError::NativeRecurrenceDidNotClose { at: 0 });
        }

        let mut predecessor_consequence = vec![0u32; world_cells];
        let mut successor_consequence = vec![0u32; world_cells];
        let mut selected_consequence = vec![0u32; world_cells];
        let mut shared_ablated_consequence = vec![0u32; world_cells];
        let mut local_ablated_consequence = vec![0u32; local_entries];
        world_predecessor_device.read(&mut predecessor_consequence)?;
        world_successor_device.read(&mut successor_consequence)?;
        world_selected_device.read(&mut selected_consequence)?;
        world_shared_ablated_device.read(&mut shared_ablated_consequence)?;
        world_local_ablated_device.read(&mut local_ablated_consequence)?;
        let selected_expected = if committed {
            (&successor_trace, &successor_lengths, &successor_consequence)
        } else {
            (
                &predecessor_trace,
                &predecessor_lengths,
                &predecessor_consequence,
            )
        };
        if &selected_trace != selected_expected.0
            || &selected_lengths != selected_expected.1
            || &selected_consequence != selected_expected.2
            || contact_relations != contact_relation
        {
            return Err(CudaRefineError::MaterialOperationPassageShape);
        }
        for (face, branch) in face_branch.iter().copied().enumerate() {
            if face_staging_events[face] != branch_staging_events[branch as usize]
                || face_terminal_events[face] != branch_terminal_events[branch as usize]
            {
                return Err(CudaRefineError::MaterialOperationPassageShape);
            }
        }
        for at in 0..recurrent_cells {
            let branch = at / recurrent_cells_per_branch;
            if recurrence_staging_events[at] != branch_staging_events[branch]
                || recurrence_terminal_events[at] != branch_terminal_events[branch]
            {
                return Err(CudaRefineError::MaterialOperationPassageShape);
            }
        }

        let material_ingress_octets = std::mem::size_of_val(face_payload_keys) as u64
            + std::mem::size_of_val(face_branch) as u64
            + std::mem::size_of_val(branch_staging_events) as u64
            + std::mem::size_of_val(branch_terminal_events) as u64
            + std::mem::size_of_val(contact_from) as u64
            + std::mem::size_of_val(contact_to) as u64
            + std::mem::size_of_val(contact_relation) as u64;
        let inference_ingress_octets = std::mem::size_of_val(recurrent_action) as u64
            + std::mem::size_of_val(recurrent_start) as u64
            + std::mem::size_of_val(world_action) as u64
            + std::mem::size_of_val(world_decoder) as u64
            + std::mem::size_of_val(world_start) as u64
            + 14 * std::mem::size_of::<u32>() as u64;
        let material_egress_octets = (face_u32_octets * 2
            + face_u64_octets * 2
            + contact_u32_octets * 3
            + recurrence_u64_octets * 2) as u64;
        let inference_egress_octets =
            (trace_octets * 4 + length_octets * 4 + world_cell_octets * 4 + world_local_octets)
                as u64;
        let host_ingress_octets = material_ingress_octets + inference_ingress_octets;
        let host_egress_octets = material_egress_octets + inference_egress_octets;
        let inference = DeviceInferenceEcology {
            predecessor_trace,
            successor_trace,
            withdrawn_trace,
            selected_trace,
            predecessor_lengths,
            successor_lengths,
            withdrawn_lengths,
            selected_lengths,
            trace_stride,
            predecessor_consequence,
            successor_consequence,
            selected_consequence,
            shared_ablated_consequence,
            local_ablated_consequence,
            families: total_families,
            ports,
            committed,
            launches: 1,
            synchronizations: 1,
            block_threads: self.block_x,
            active_lanes: active_lanes as u32,
            visited_words,
            host_ingress_octets: inference_ingress_octets,
            host_egress_octets: inference_egress_octets,
            resident_octets: inference_ingress_octets
                + inference_egress_octets
                + visited_octets as u64,
        };
        Ok(DeviceMaterialOperationWorldTube {
            payload_classes,
            payload_comparisons,
            face_staging_events,
            face_terminal_events,
            contact_left_classes,
            contact_right_classes,
            contact_relations,
            recurrence_staging_events,
            recurrence_terminal_events,
            inference,
            launches: 1,
            synchronizations: 1,
            host_ingress_octets,
            host_egress_octets,
            resident_octets: host_ingress_octets + host_egress_octets + visited_octets as u64,
        })
    }
}

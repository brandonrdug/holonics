//! Resident CUDA recurrence and native conduct methods.

use super::*;

impl CudaRefineExecutor {
    /// **The exact quotient on the card.** Same law, other chart.
    ///
    /// The capacity is the next power of two above the cell count, so the table can never fill:
    /// distinct pairs are at most cells. Derived from the material; no load factor.
    pub fn quotient_on_device(
        &mut self,
        classes: &[u32],
        keys: &[u64],
    ) -> Result<Quotient, CudaRefineError> {
        driver(unsafe { cuCtxSetCurrent(self.context) }, "cuCtxSetCurrent")?;
        let count = classes.len();
        if count == 0 || keys.len() != count {
            return Ok(Quotient {
                cell_class: Vec::new(),
                classes: 0,
                carrier: QuotientCarrier::Device,
            });
        }
        let capacity = (count + 1).next_power_of_two();
        let mut mask = (capacity - 1) as u32;
        let table_pair = Buffer::alloc(capacity * std::mem::size_of::<u64>())?;
        let mut current = classes.to_vec();
        let grid = self.grid_for(count as u64)?;
        for half in [
            keys.iter()
                .map(|key| (key >> 32) as u32)
                .collect::<Vec<_>>(),
            keys.iter().map(|key| *key as u32).collect::<Vec<_>>(),
        ] {
            table_pair.fill(0xff, capacity * std::mem::size_of::<u64>())?;
            let device_class = Buffer::of(&current)?;
            let device_key = Buffer::of(&half)?;
            let device_next = Buffer::alloc(count * std::mem::size_of::<u32>())?;
            let mut cells = count as u32;
            // CUDA receives pointers to the argument values. These locals must live through
            // `cuLaunchKernel`; taking a raw pointer to a block-expression temporary works by
            // accident in an unoptimized build and produced address `0x30` in release.
            let mut class_pointer = device_class.pointer;
            let mut key_pointer = device_key.pointer;
            let mut table_pointer = table_pair.pointer;
            let mut next_pointer = device_next.pointer;
            let mut arguments: Vec<*mut c_void> = vec![
                &mut class_pointer as *mut u64 as *mut c_void,
                &mut key_pointer as *mut u64 as *mut c_void,
                &mut table_pointer as *mut u64 as *mut c_void,
                &mut next_pointer as *mut u64 as *mut c_void,
                &mut cells as *mut u32 as *mut c_void,
                &mut mask as *mut u32 as *mut c_void,
            ];
            driver(
                unsafe {
                    cuLaunchKernel(
                        self.claim,
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
                "cuLaunchKernel(claim_identities)",
            )?;
            driver(unsafe { cuCtxSynchronize() }, "cuCtxSynchronize")?;
            self.launches += 1;
            let mut slots = vec![0u32; count];
            device_next.read(&mut slots)?;
            let mut dense: BTreeMap<u32, u32> = BTreeMap::new();
            for (at, slot) in slots.iter().enumerate() {
                let next = dense.len() as u32 + 1;
                current[at] = *dense.entry(*slot).or_insert(next);
            }
        }
        Ok(Quotient {
            classes: current.iter().copied().collect::<BTreeSet<_>>().len(),
            cell_class: current,
            carrier: QuotientCarrier::Device,
        })
    }

    /// Carry a population through one complete ordered word on the resident card.
    ///
    /// `generator_table` is row-major `[generator][native state]`. It, the ordered word and the
    /// starting population cross once; every intermediate state remains device-local.
    pub fn conduct_native_word_on_device(
        &mut self,
        states: usize,
        generators: usize,
        generator_table: &[u32],
        word: &[u32],
        native_start: &[u32],
    ) -> Result<DeviceNativeWord, CudaRefineError> {
        let expected = states
            .checked_mul(generators)
            .ok_or(CudaRefineError::NativeActionTooWide)?;
        if generator_table.len() != expected {
            return Err(CudaRefineError::NativeTableExtentDisagrees {
                table_entries: generator_table.len(),
                generators,
                states,
            });
        }
        if states > u32::MAX as usize
            || generators > u32::MAX as usize
            || word.len() > u32::MAX as usize
            || native_start.len() > u32::MAX as usize
        {
            return Err(CudaRefineError::NativeActionTooWide);
        }
        if let Some(state) = generator_table
            .iter()
            .chain(native_start)
            .copied()
            .find(|state| *state as usize >= states)
        {
            return Err(CudaRefineError::NativeStateOutsidePopulation { state, states });
        }
        if let Some(generator) = word
            .iter()
            .copied()
            .find(|generator| *generator as usize >= generators)
        {
            return Err(CudaRefineError::NativeGeneratorOutsideFamily {
                generator,
                generators,
            });
        }

        driver(unsafe { cuCtxSetCurrent(self.context) }, "cuCtxSetCurrent")?;
        let table = Buffer::of(generator_table)?;
        let device_word = Buffer::of(word)?;
        let start = Buffer::of(native_start)?;
        let end = Buffer::alloc(std::mem::size_of_val(native_start))?;
        let count = native_start.len();
        if count > 0 {
            let grid = self.grid_for(count as u64)?;
            let mut table_pointer = table.pointer;
            let mut word_pointer = device_word.pointer;
            let mut start_pointer = start.pointer;
            let mut end_pointer = end.pointer;
            let mut cell_count = count as u32;
            let mut state_count = states as u32;
            let mut word_length = word.len() as u32;
            let mut arguments: Vec<*mut c_void> = vec![
                &mut table_pointer as *mut u64 as *mut c_void,
                &mut word_pointer as *mut u64 as *mut c_void,
                &mut start_pointer as *mut u64 as *mut c_void,
                &mut end_pointer as *mut u64 as *mut c_void,
                &mut cell_count as *mut u32 as *mut c_void,
                &mut state_count as *mut u32 as *mut c_void,
                &mut word_length as *mut u32 as *mut c_void,
            ];
            driver(
                unsafe {
                    cuLaunchKernel(
                        self.native_word,
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
                "cuLaunchKernel(conduct_native_word)",
            )?;
            driver(unsafe { cuCtxSynchronize() }, "cuCtxSynchronize")?;
            self.launches += 1;
        }
        let mut native_end = vec![0u32; count];
        if count > 0 {
            end.read(&mut native_end)?;
        }
        let table_octets = std::mem::size_of_val(generator_table) as u64;
        let word_octets = std::mem::size_of_val(word) as u64;
        let state_octets = std::mem::size_of_val(native_start) as u64;
        Ok(DeviceNativeWord {
            native_end,
            launches: u64::from(count > 0),
            host_ingress_octets: table_octets + word_octets + state_octets,
            host_egress_octets: state_octets,
            resident_octets: table_octets + word_octets + state_octets * 2,
        })
    }

    /// Carry every starting occurrence through one complete ordered word and retain every
    /// intermediate boundary until the one terminal card read.
    ///
    /// This is the trace face of [`Self::conduct_native_word_on_device`], not another transition
    /// law. The word extent comes from the caller's admitted causal section. No callback, scalar
    /// winner, or stop case crosses between its steps.
    pub fn conduct_native_trace_on_device(
        &mut self,
        states: usize,
        generators: usize,
        generator_table: &[u32],
        word: &[u32],
        native_start: &[u32],
    ) -> Result<DeviceNativeTrace, CudaRefineError> {
        let expected = states
            .checked_mul(generators)
            .ok_or(CudaRefineError::NativeActionTooWide)?;
        let trace_stride = word
            .len()
            .checked_add(1)
            .ok_or(CudaRefineError::NativeActionTooWide)?;
        let trace_entries = native_start
            .len()
            .checked_mul(trace_stride)
            .ok_or(CudaRefineError::NativeActionTooWide)?;
        if generator_table.len() != expected {
            return Err(CudaRefineError::NativeTableExtentDisagrees {
                table_entries: generator_table.len(),
                generators,
                states,
            });
        }
        if states > u32::MAX as usize
            || generators > u32::MAX as usize
            || word.len() > u32::MAX as usize
            || trace_stride > u32::MAX as usize
            || native_start.len() > u32::MAX as usize
        {
            return Err(CudaRefineError::NativeActionTooWide);
        }
        if let Some(state) = generator_table
            .iter()
            .chain(native_start)
            .copied()
            .find(|state| *state as usize >= states)
        {
            return Err(CudaRefineError::NativeStateOutsidePopulation { state, states });
        }
        if let Some(generator) = word
            .iter()
            .copied()
            .find(|generator| *generator as usize >= generators)
        {
            return Err(CudaRefineError::NativeGeneratorOutsideFamily {
                generator,
                generators,
            });
        }

        driver(unsafe { cuCtxSetCurrent(self.context) }, "cuCtxSetCurrent")?;
        let table = Buffer::of(generator_table)?;
        let device_word = Buffer::of(word)?;
        let start = Buffer::of(native_start)?;
        let trace = Buffer::alloc(trace_entries * std::mem::size_of::<u32>())?;
        let count = native_start.len();
        if count > 0 {
            let grid = self.grid_for(count as u64)?;
            let mut table_pointer = table.pointer;
            let mut word_pointer = device_word.pointer;
            let mut start_pointer = start.pointer;
            let mut trace_pointer = trace.pointer;
            let mut cell_count = count as u32;
            let mut state_count = states as u32;
            let mut word_length = word.len() as u32;
            let mut stride = trace_stride as u32;
            let mut arguments: [*mut c_void; 8] = [
                &mut table_pointer as *mut u64 as *mut c_void,
                &mut word_pointer as *mut u64 as *mut c_void,
                &mut start_pointer as *mut u64 as *mut c_void,
                &mut trace_pointer as *mut u64 as *mut c_void,
                &mut cell_count as *mut u32 as *mut c_void,
                &mut state_count as *mut u32 as *mut c_void,
                &mut word_length as *mut u32 as *mut c_void,
                &mut stride as *mut u32 as *mut c_void,
            ];
            driver(
                unsafe {
                    cuLaunchKernel(
                        self.native_trace,
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
                "cuLaunchKernel(conduct_native_trace)",
            )?;
            driver(unsafe { cuCtxSynchronize() }, "cuCtxSynchronize")?;
            self.launches += 1;
        }
        let mut native_trace = vec![0u32; trace_entries];
        if count > 0 {
            trace.read(&mut native_trace)?;
        }
        let table_octets = std::mem::size_of_val(generator_table) as u64;
        let word_octets = std::mem::size_of_val(word) as u64;
        let state_octets = std::mem::size_of_val(native_start) as u64;
        let trace_octets = (trace_entries * std::mem::size_of::<u32>()) as u64;
        Ok(DeviceNativeTrace {
            native_trace,
            trace_stride,
            starting_occurrences: count,
            launches: u64::from(count > 0),
            synchronizations: u64::from(count > 0),
            block_threads: self.block_x,
            active_lanes: count as u32,
            host_ingress_octets: table_octets + word_octets + state_octets,
            host_egress_octets: trace_octets,
            resident_octets: table_octets + word_octets + state_octets + trace_octets,
        })
    }

    /// Carry plural addressed words through one shared native action and return their exact
    /// ragged traces after one terminal synchronization.
    ///
    /// `word_offsets` is the canonical prefix-sum boundary of `words`, with one interval per
    /// starting occurrence.  Trace extents are therefore derived from the material word family;
    /// there is no padded context capacity and no host callback between steps.
    pub fn conduct_native_ragged_traces_on_device(
        &mut self,
        states: usize,
        generators: usize,
        generator_table: &[u32],
        words: &[u32],
        word_offsets: &[u32],
        native_start: &[u32],
    ) -> Result<DeviceRaggedNativeTrace, CudaRefineError> {
        let expected = states
            .checked_mul(generators)
            .ok_or(CudaRefineError::NativeActionTooWide)?;
        let expected_offsets = native_start
            .len()
            .checked_add(1)
            .ok_or(CudaRefineError::NativeActionTooWide)?;
        if generator_table.len() != expected {
            return Err(CudaRefineError::NativeTableExtentDisagrees {
                table_entries: generator_table.len(),
                generators,
                states,
            });
        }
        if states == 0
            || generators == 0
            || native_start.is_empty()
            || word_offsets.len() != expected_offsets
            || word_offsets.first() != Some(&0)
            || word_offsets.last().copied() != u32::try_from(words.len()).ok()
            || word_offsets.windows(2).any(|pair| pair[0] > pair[1])
        {
            return Err(CudaRefineError::RaggedNativePassageShape);
        }
        if states > u32::MAX as usize
            || generators > u32::MAX as usize
            || native_start.len() > u32::MAX as usize
        {
            return Err(CudaRefineError::NativeActionTooWide);
        }
        if let Some(state) = generator_table
            .iter()
            .chain(native_start)
            .copied()
            .find(|state| *state as usize >= states)
        {
            return Err(CudaRefineError::NativeStateOutsidePopulation { state, states });
        }
        if let Some(generator) = words
            .iter()
            .copied()
            .find(|generator| *generator as usize >= generators)
        {
            return Err(CudaRefineError::NativeGeneratorOutsideFamily {
                generator,
                generators,
            });
        }

        let mut trace_offsets = Vec::with_capacity(expected_offsets);
        trace_offsets.push(0u32);
        for pair in word_offsets.windows(2) {
            let word_length = pair[1]
                .checked_sub(pair[0])
                .ok_or(CudaRefineError::RaggedNativePassageShape)?;
            let next = trace_offsets
                .last()
                .copied()
                .and_then(|offset| offset.checked_add(word_length)?.checked_add(1))
                .ok_or(CudaRefineError::NativeActionTooWide)?;
            trace_offsets.push(next);
        }
        let trace_entries = trace_offsets
            .last()
            .copied()
            .ok_or(CudaRefineError::RaggedNativePassageShape)? as usize;

        driver(unsafe { cuCtxSetCurrent(self.context) }, "cuCtxSetCurrent")?;
        let table = Buffer::of(generator_table)?;
        let device_words = Buffer::of(words)?;
        let device_word_offsets = Buffer::of(word_offsets)?;
        let starts = Buffer::of(native_start)?;
        let device_trace_offsets = Buffer::of(&trace_offsets)?;
        let trace = Buffer::alloc(trace_entries * std::mem::size_of::<u32>())?;
        let grid = self.grid_for(native_start.len() as u64)?;
        let mut table_pointer = table.pointer;
        let mut words_pointer = device_words.pointer;
        let mut word_offsets_pointer = device_word_offsets.pointer;
        let mut starts_pointer = starts.pointer;
        let mut trace_offsets_pointer = device_trace_offsets.pointer;
        let mut trace_pointer = trace.pointer;
        let mut front_count = native_start.len() as u32;
        let mut state_count = states as u32;
        let mut arguments: [*mut c_void; 8] = [
            &mut table_pointer as *mut u64 as *mut c_void,
            &mut words_pointer as *mut u64 as *mut c_void,
            &mut word_offsets_pointer as *mut u64 as *mut c_void,
            &mut starts_pointer as *mut u64 as *mut c_void,
            &mut trace_offsets_pointer as *mut u64 as *mut c_void,
            &mut trace_pointer as *mut u64 as *mut c_void,
            &mut front_count as *mut u32 as *mut c_void,
            &mut state_count as *mut u32 as *mut c_void,
        ];
        driver(
            unsafe {
                cuLaunchKernel(
                    self.native_ragged_trace,
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
            "cuLaunchKernel(conduct_native_ragged_trace)",
        )?;
        driver(unsafe { cuCtxSynchronize() }, "cuCtxSynchronize")?;
        self.launches += 1;

        let mut native_trace = vec![0u32; trace_entries];
        trace.read(&mut native_trace)?;
        let table_octets = std::mem::size_of_val(generator_table) as u64;
        let word_octets = std::mem::size_of_val(words) as u64;
        let offset_octets = std::mem::size_of_val(word_offsets) as u64;
        let start_octets = std::mem::size_of_val(native_start) as u64;
        let trace_offset_octets = std::mem::size_of_val(trace_offsets.as_slice()) as u64;
        let trace_octets = std::mem::size_of_val(native_trace.as_slice()) as u64;
        Ok(DeviceRaggedNativeTrace {
            native_trace,
            trace_offsets,
            front_count: native_start.len(),
            launches: 1,
            synchronizations: 1,
            block_threads: self.block_x,
            active_lanes: native_start.len() as u32,
            host_ingress_octets: table_octets
                + word_octets
                + offset_octets
                + start_octets
                + trace_offset_octets,
            host_egress_octets: trace_octets,
            resident_octets: table_octets
                + word_octets
                + offset_octets
                + start_octets
                + trace_offset_octets
                + trace_octets,
        })
    }

    /// Return every finite predecessor/successor/targeted-ablation recurrence after one exterior
    /// difference, under one terminal synchronization.
    ///
    /// The card derives closure from repetition inside the complete finite state population. A
    /// positive returned occurrence commits the one addressed local delta; an empty return
    /// declines it. The host supplies neither a traversal capacity nor a semantic stop case.
    #[allow(clippy::too_many_arguments)]
    pub fn conduct_returned_recurrences_on_device(
        &mut self,
        states: usize,
        generators: usize,
        generator_table: &[u32],
        generator: u32,
        native_start: &[u32],
        returned_difference_octets: u64,
        delta_from: u32,
        delta_to: u32,
        control_from: u32,
    ) -> Result<DeviceReturnedRecurrences, CudaRefineError> {
        let expected = states
            .checked_mul(generators)
            .ok_or(CudaRefineError::NativeActionTooWide)?;
        let trace_stride = states
            .checked_add(1)
            .ok_or(CudaRefineError::NativeActionTooWide)?;
        let trace_entries = native_start
            .len()
            .checked_mul(trace_stride)
            .ok_or(CudaRefineError::NativeActionTooWide)?;
        if generator_table.len() != expected {
            return Err(CudaRefineError::NativeTableExtentDisagrees {
                table_entries: generator_table.len(),
                generators,
                states,
            });
        }
        if states == 0
            || native_start.is_empty()
            || states > u32::MAX as usize
            || generators > u32::MAX as usize
            || native_start.len() > u32::MAX as usize
        {
            return Err(CudaRefineError::NativeActionTooWide);
        }
        if generator as usize >= generators {
            return Err(CudaRefineError::NativeGeneratorOutsideFamily {
                generator,
                generators,
            });
        }
        if let Some(state) = generator_table
            .iter()
            .chain(native_start)
            .copied()
            .chain([delta_from, delta_to, control_from])
            .find(|state| *state as usize >= states)
        {
            return Err(CudaRefineError::NativeStateOutsidePopulation { state, states });
        }

        driver(unsafe { cuCtxSetCurrent(self.context) }, "cuCtxSetCurrent")?;
        let table = Buffer::of(generator_table)?;
        let starts = Buffer::of(native_start)?;
        let predecessor = Buffer::alloc(trace_entries * std::mem::size_of::<u32>())?;
        let successor = Buffer::alloc(trace_entries * std::mem::size_of::<u32>())?;
        let ablated = Buffer::alloc(trace_entries * std::mem::size_of::<u32>())?;
        let lengths_octets = native_start.len() * std::mem::size_of::<u32>();
        let predecessor_lengths_device = Buffer::alloc(lengths_octets)?;
        let successor_lengths_device = Buffer::alloc(lengths_octets)?;
        let ablated_lengths_device = Buffer::alloc(lengths_octets)?;
        let decision_device = Buffer::alloc(std::mem::size_of::<u32>())?;
        let control_device = Buffer::alloc(2 * std::mem::size_of::<u32>())?;
        let grid = self.grid_for(native_start.len() as u64)?;
        let mut table_pointer = table.pointer;
        let mut starts_pointer = starts.pointer;
        let mut predecessor_pointer = predecessor.pointer;
        let mut successor_pointer = successor.pointer;
        let mut ablated_pointer = ablated.pointer;
        let mut predecessor_lengths_pointer = predecessor_lengths_device.pointer;
        let mut successor_lengths_pointer = successor_lengths_device.pointer;
        let mut ablated_lengths_pointer = ablated_lengths_device.pointer;
        let mut decision_pointer = decision_device.pointer;
        let mut control_pointer = control_device.pointer;
        let mut cell_count = native_start.len() as u32;
        let mut state_count = states as u32;
        let mut generator_row = generator;
        let mut returned_octets = returned_difference_octets;
        let mut local_from = delta_from;
        let mut local_to = delta_to;
        let mut disjoint_from = control_from;
        let mut arguments: [*mut c_void; 17] = [
            &mut table_pointer as *mut u64 as *mut c_void,
            &mut starts_pointer as *mut u64 as *mut c_void,
            &mut predecessor_pointer as *mut u64 as *mut c_void,
            &mut successor_pointer as *mut u64 as *mut c_void,
            &mut ablated_pointer as *mut u64 as *mut c_void,
            &mut predecessor_lengths_pointer as *mut u64 as *mut c_void,
            &mut successor_lengths_pointer as *mut u64 as *mut c_void,
            &mut ablated_lengths_pointer as *mut u64 as *mut c_void,
            &mut decision_pointer as *mut u64 as *mut c_void,
            &mut control_pointer as *mut u64 as *mut c_void,
            &mut cell_count as *mut u32 as *mut c_void,
            &mut state_count as *mut u32 as *mut c_void,
            &mut generator_row as *mut u32 as *mut c_void,
            &mut returned_octets as *mut u64 as *mut c_void,
            &mut local_from as *mut u32 as *mut c_void,
            &mut local_to as *mut u32 as *mut c_void,
            &mut disjoint_from as *mut u32 as *mut c_void,
        ];
        driver(
            unsafe {
                cuLaunchKernel(
                    self.returned_recurrence,
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
            "cuLaunchKernel(return_and_recur_native)",
        )?;
        driver(unsafe { cuCtxSynchronize() }, "cuCtxSynchronize")?;
        self.launches += 1;

        let mut predecessor_trace = vec![0u32; trace_entries];
        let mut successor_trace = vec![0u32; trace_entries];
        let mut ablated_trace = vec![0u32; trace_entries];
        let mut predecessor_lengths = vec![0u32; native_start.len()];
        let mut successor_lengths = vec![0u32; native_start.len()];
        let mut ablated_lengths = vec![0u32; native_start.len()];
        let mut decision = [0u32; 1];
        let mut control = [0u32; 2];
        predecessor.read(&mut predecessor_trace)?;
        successor.read(&mut successor_trace)?;
        ablated.read(&mut ablated_trace)?;
        predecessor_lengths_device.read(&mut predecessor_lengths)?;
        successor_lengths_device.read(&mut successor_lengths)?;
        ablated_lengths_device.read(&mut ablated_lengths)?;
        decision_device.read(&mut decision)?;
        control_device.read(&mut control)?;
        for (at, length) in predecessor_lengths
            .iter()
            .chain(&successor_lengths)
            .chain(&ablated_lengths)
            .copied()
            .enumerate()
        {
            if length < 2 || length as usize > trace_stride {
                return Err(CudaRefineError::NativeRecurrenceDidNotClose {
                    at: at % native_start.len(),
                });
            }
        }
        if decision[0] > 1 {
            return Err(CudaRefineError::NativeActionTooWide);
        }
        let table_octets = std::mem::size_of_val(generator_table) as u64;
        let start_octets = std::mem::size_of_val(native_start) as u64;
        let trace_octets = (trace_entries * std::mem::size_of::<u32>()) as u64;
        let length_octets = lengths_octets as u64;
        let scalar_ingress_octets =
            7 * std::mem::size_of::<u32>() as u64 + std::mem::size_of::<u64>() as u64;
        let scalar_egress_octets = 3 * std::mem::size_of::<u32>() as u64;
        Ok(DeviceReturnedRecurrences {
            predecessor_trace,
            successor_trace,
            ablated_trace,
            predecessor_lengths,
            successor_lengths,
            ablated_lengths,
            trace_stride,
            committed: decision[0] == 1,
            control_predecessor: control[0],
            control_successor: control[1],
            launches: 1,
            synchronizations: 1,
            block_threads: self.block_x,
            active_lanes: native_start.len() as u32,
            host_ingress_octets: table_octets + start_octets + scalar_ingress_octets,
            host_egress_octets: trace_octets * 3 + length_octets * 3 + scalar_egress_octets,
            resident_octets: table_octets
                + start_octets
                + trace_octets * 3
                + length_octets * 3
                + scalar_egress_octets,
        })
    }

    /// Form the exact returned receiver adjoint, decide one local commit, extend its supported
    /// finite action, and return predecessor/successor/withdrawal recurrences in one resident
    /// front. The card derives the added state from the predecessor population and closure from
    /// first recurrence; the host supplies neither a response extent nor a semantic phase choice.
    pub fn conduct_dynamic_morphology_on_device(
        &mut self,
        predecessor_action: &[u32],
        support_incidence: &[i32],
        returned_covector: &[i32],
        native_start: &[u32],
    ) -> Result<DeviceDynamicMorphology, CudaRefineError> {
        let predecessor_states = predecessor_action.len();
        let returns = returned_covector.len();
        let expected_incidence = predecessor_states
            .checked_mul(returns)
            .ok_or(CudaRefineError::NativeActionTooWide)?;
        let successor_states = predecessor_states
            .checked_add(1)
            .ok_or(CudaRefineError::NativeActionTooWide)?;
        let trace_stride = successor_states
            .checked_add(1)
            .ok_or(CudaRefineError::NativeActionTooWide)?;
        let trace_entries = native_start
            .len()
            .checked_mul(trace_stride)
            .ok_or(CudaRefineError::NativeActionTooWide)?;
        if predecessor_states == 0
            || returns == 0
            || native_start.is_empty()
            || support_incidence.len() != expected_incidence
            || predecessor_states >= u32::MAX as usize
            || returns > u32::MAX as usize
            || native_start.len() > u32::MAX as usize
            || support_incidence
                .iter()
                .any(|entry| !matches!(*entry, 0 | 1))
            || returned_covector
                .iter()
                .any(|entry| !matches!(*entry, -1 | 0 | 1))
        {
            return Err(CudaRefineError::DynamicMorphologyShape);
        }
        if let Some(state) = predecessor_action
            .iter()
            .chain(native_start)
            .copied()
            .find(|state| *state as usize >= predecessor_states)
        {
            return Err(CudaRefineError::NativeStateOutsidePopulation {
                state,
                states: predecessor_states,
            });
        }

        driver(unsafe { cuCtxSetCurrent(self.context) }, "cuCtxSetCurrent")?;
        let action = Buffer::of(predecessor_action)?;
        let incidence = Buffer::of(support_incidence)?;
        let covector = Buffer::of(returned_covector)?;
        let starts = Buffer::of(native_start)?;
        let adjoint_octets = predecessor_states * std::mem::size_of::<i64>();
        let adjoint = Buffer::alloc(adjoint_octets)?;
        let action_octets = successor_states * std::mem::size_of::<u32>();
        let predecessor_extended = Buffer::alloc(action_octets)?;
        let successor_action = Buffer::alloc(action_octets)?;
        let withdrawn_action = Buffer::alloc(action_octets)?;
        let trace_octets = trace_entries * std::mem::size_of::<u32>();
        let predecessor_trace_device = Buffer::alloc(trace_octets)?;
        let successor_trace_device = Buffer::alloc(trace_octets)?;
        let withdrawn_trace_device = Buffer::alloc(trace_octets)?;
        let length_octets = native_start.len() * std::mem::size_of::<u32>();
        let predecessor_lengths_device = Buffer::alloc(length_octets)?;
        let successor_lengths_device = Buffer::alloc(length_octets)?;
        let withdrawn_lengths_device = Buffer::alloc(length_octets)?;
        let decision_device = Buffer::alloc(std::mem::size_of::<u32>())?;
        let support_state_device = Buffer::alloc(std::mem::size_of::<u32>())?;

        let mut action_pointer = action.pointer;
        let mut incidence_pointer = incidence.pointer;
        let mut covector_pointer = covector.pointer;
        let mut starts_pointer = starts.pointer;
        let mut adjoint_pointer = adjoint.pointer;
        let mut predecessor_extended_pointer = predecessor_extended.pointer;
        let mut successor_action_pointer = successor_action.pointer;
        let mut withdrawn_action_pointer = withdrawn_action.pointer;
        let mut predecessor_trace_pointer = predecessor_trace_device.pointer;
        let mut successor_trace_pointer = successor_trace_device.pointer;
        let mut withdrawn_trace_pointer = withdrawn_trace_device.pointer;
        let mut predecessor_lengths_pointer = predecessor_lengths_device.pointer;
        let mut successor_lengths_pointer = successor_lengths_device.pointer;
        let mut withdrawn_lengths_pointer = withdrawn_lengths_device.pointer;
        let mut decision_pointer = decision_device.pointer;
        let mut support_state_pointer = support_state_device.pointer;
        let mut state_count = predecessor_states as u32;
        let mut return_count = returns as u32;
        let mut start_count = native_start.len() as u32;
        let mut arguments: [*mut c_void; 19] = [
            &mut action_pointer as *mut u64 as *mut c_void,
            &mut incidence_pointer as *mut u64 as *mut c_void,
            &mut covector_pointer as *mut u64 as *mut c_void,
            &mut starts_pointer as *mut u64 as *mut c_void,
            &mut adjoint_pointer as *mut u64 as *mut c_void,
            &mut predecessor_extended_pointer as *mut u64 as *mut c_void,
            &mut successor_action_pointer as *mut u64 as *mut c_void,
            &mut withdrawn_action_pointer as *mut u64 as *mut c_void,
            &mut predecessor_trace_pointer as *mut u64 as *mut c_void,
            &mut successor_trace_pointer as *mut u64 as *mut c_void,
            &mut withdrawn_trace_pointer as *mut u64 as *mut c_void,
            &mut predecessor_lengths_pointer as *mut u64 as *mut c_void,
            &mut successor_lengths_pointer as *mut u64 as *mut c_void,
            &mut withdrawn_lengths_pointer as *mut u64 as *mut c_void,
            &mut decision_pointer as *mut u64 as *mut c_void,
            &mut support_state_pointer as *mut u64 as *mut c_void,
            &mut state_count as *mut u32 as *mut c_void,
            &mut return_count as *mut u32 as *mut c_void,
            &mut start_count as *mut u32 as *mut c_void,
        ];
        driver(
            unsafe {
                cuLaunchKernel(
                    self.dynamic_morphology,
                    1,
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
            "cuLaunchKernel(cultivate_dynamic_morphology)",
        )?;
        driver(unsafe { cuCtxSynchronize() }, "cuCtxSynchronize")?;
        self.launches += 1;

        let mut returned_adjoint = vec![0i64; predecessor_states];
        let mut predecessor_action_returned = vec![0u32; successor_states];
        let mut successor_action_returned = vec![0u32; successor_states];
        let mut withdrawn_action_returned = vec![0u32; successor_states];
        let mut predecessor_trace = vec![0u32; trace_entries];
        let mut successor_trace = vec![0u32; trace_entries];
        let mut withdrawn_trace = vec![0u32; trace_entries];
        let mut predecessor_lengths = vec![0u32; native_start.len()];
        let mut successor_lengths = vec![0u32; native_start.len()];
        let mut withdrawn_lengths = vec![0u32; native_start.len()];
        let mut decision = [0u32; 1];
        let mut support_state = [u32::MAX; 1];
        adjoint.read(&mut returned_adjoint)?;
        predecessor_extended.read(&mut predecessor_action_returned)?;
        successor_action.read(&mut successor_action_returned)?;
        withdrawn_action.read(&mut withdrawn_action_returned)?;
        predecessor_trace_device.read(&mut predecessor_trace)?;
        successor_trace_device.read(&mut successor_trace)?;
        withdrawn_trace_device.read(&mut withdrawn_trace)?;
        predecessor_lengths_device.read(&mut predecessor_lengths)?;
        successor_lengths_device.read(&mut successor_lengths)?;
        withdrawn_lengths_device.read(&mut withdrawn_lengths)?;
        decision_device.read(&mut decision)?;
        support_state_device.read(&mut support_state)?;
        if decision[0] > 1
            || support_state[0] != u32::MAX && support_state[0] as usize >= predecessor_states
        {
            return Err(CudaRefineError::DynamicMorphologyShape);
        }
        for (at, length) in predecessor_lengths
            .iter()
            .chain(&successor_lengths)
            .chain(&withdrawn_lengths)
            .copied()
            .enumerate()
        {
            if length < 2 || length as usize > trace_stride {
                return Err(CudaRefineError::NativeRecurrenceDidNotClose {
                    at: at % native_start.len(),
                });
            }
        }

        let ingress = std::mem::size_of_val(predecessor_action)
            + std::mem::size_of_val(support_incidence)
            + std::mem::size_of_val(returned_covector)
            + std::mem::size_of_val(native_start)
            + 3 * std::mem::size_of::<u32>();
        let egress = adjoint_octets
            + action_octets * 3
            + trace_octets * 3
            + length_octets * 3
            + 2 * std::mem::size_of::<u32>();
        Ok(DeviceDynamicMorphology {
            returned_adjoint,
            predecessor_action: predecessor_action_returned,
            successor_action: successor_action_returned,
            withdrawn_action: withdrawn_action_returned,
            predecessor_trace,
            successor_trace,
            withdrawn_trace,
            predecessor_lengths,
            successor_lengths,
            withdrawn_lengths,
            trace_stride,
            committed: decision[0] == 1,
            supported_state: (support_state[0] != u32::MAX).then_some(support_state[0]),
            launches: 1,
            synchronizations: 1,
            block_threads: self.block_x,
            active_lanes: native_start.len() as u32,
            host_ingress_octets: ingress as u64,
            host_egress_octets: egress as u64,
            resident_octets: (ingress + egress) as u64,
        })
    }

    /// Conduct the compact successor, the one retained predecessor override, and withdrawal of
    /// their shared generator for every admitted starting occurrence in one resident front.
    ///
    /// The only closure extent is the finite native population. A derived bitset records visited
    /// incidence, so recurrence detection is linear in the enacted trace rather than a quadratic
    /// scan of preceding boundaries. The host observes all routes only after one synchronization.
    pub fn conduct_condensed_recurrences_on_device(
        &mut self,
        successor_table: &[u32],
        native_start: &[u32],
        predecessor_from: u32,
        predecessor_to: u32,
    ) -> Result<DeviceCondensedRecurrences, CudaRefineError> {
        let states = successor_table.len();
        let trace_stride = states
            .checked_add(1)
            .ok_or(CudaRefineError::NativeActionTooWide)?;
        let trace_entries = native_start
            .len()
            .checked_mul(trace_stride)
            .ok_or(CudaRefineError::NativeActionTooWide)?;
        let visited_words = states
            .checked_add(u32::BITS as usize - 1)
            .ok_or(CudaRefineError::NativeActionTooWide)?
            / u32::BITS as usize;
        let visited_entries = native_start
            .len()
            .checked_mul(3)
            .and_then(|rows| rows.checked_mul(visited_words))
            .ok_or(CudaRefineError::NativeActionTooWide)?;
        if states == 0
            || native_start.is_empty()
            || states > u32::MAX as usize
            || native_start.len() > u32::MAX as usize
            || visited_words > u32::MAX as usize
        {
            return Err(CudaRefineError::NativeActionTooWide);
        }
        if let Some(state) = successor_table
            .iter()
            .chain(native_start)
            .copied()
            .chain([predecessor_from, predecessor_to])
            .find(|state| *state as usize >= states)
        {
            return Err(CudaRefineError::NativeStateOutsidePopulation { state, states });
        }
        if successor_table[predecessor_from as usize] == predecessor_to {
            return Err(CudaRefineError::NativeActionTooWide);
        }

        driver(unsafe { cuCtxSetCurrent(self.context) }, "cuCtxSetCurrent")?;
        let table = Buffer::of(successor_table)?;
        let starts = Buffer::of(native_start)?;
        let trace_octets = trace_entries * std::mem::size_of::<u32>();
        let predecessor = Buffer::alloc(trace_octets)?;
        let successor = Buffer::alloc(trace_octets)?;
        let withdrawn = Buffer::alloc(trace_octets)?;
        let lengths_octets = native_start.len() * std::mem::size_of::<u32>();
        let predecessor_lengths_device = Buffer::alloc(lengths_octets)?;
        let successor_lengths_device = Buffer::alloc(lengths_octets)?;
        let withdrawn_lengths_device = Buffer::alloc(lengths_octets)?;
        let visited_octets = visited_entries * std::mem::size_of::<u32>();
        let visited = Buffer::alloc(visited_octets)?;
        visited.fill(0, visited_octets)?;

        let grid = self.grid_for(native_start.len() as u64)?;
        let mut table_pointer = table.pointer;
        let mut starts_pointer = starts.pointer;
        let mut predecessor_pointer = predecessor.pointer;
        let mut successor_pointer = successor.pointer;
        let mut withdrawn_pointer = withdrawn.pointer;
        let mut predecessor_lengths_pointer = predecessor_lengths_device.pointer;
        let mut successor_lengths_pointer = successor_lengths_device.pointer;
        let mut withdrawn_lengths_pointer = withdrawn_lengths_device.pointer;
        let mut visited_pointer = visited.pointer;
        let mut cell_count = native_start.len() as u32;
        let mut state_count = states as u32;
        let mut seen_words = visited_words as u32;
        let mut local_from = predecessor_from;
        let mut local_to = predecessor_to;
        let mut arguments: [*mut c_void; 14] = [
            &mut table_pointer as *mut u64 as *mut c_void,
            &mut starts_pointer as *mut u64 as *mut c_void,
            &mut predecessor_pointer as *mut u64 as *mut c_void,
            &mut successor_pointer as *mut u64 as *mut c_void,
            &mut withdrawn_pointer as *mut u64 as *mut c_void,
            &mut predecessor_lengths_pointer as *mut u64 as *mut c_void,
            &mut successor_lengths_pointer as *mut u64 as *mut c_void,
            &mut withdrawn_lengths_pointer as *mut u64 as *mut c_void,
            &mut visited_pointer as *mut u64 as *mut c_void,
            &mut cell_count as *mut u32 as *mut c_void,
            &mut state_count as *mut u32 as *mut c_void,
            &mut seen_words as *mut u32 as *mut c_void,
            &mut local_from as *mut u32 as *mut c_void,
            &mut local_to as *mut u32 as *mut c_void,
        ];
        driver(
            unsafe {
                cuLaunchKernel(
                    self.condensed_recurrence,
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
            "cuLaunchKernel(conduct_condensed_recurrences)",
        )?;
        driver(unsafe { cuCtxSynchronize() }, "cuCtxSynchronize")?;
        self.launches += 1;

        let mut predecessor_trace = vec![0u32; trace_entries];
        let mut successor_trace = vec![0u32; trace_entries];
        let mut withdrawn_trace = vec![0u32; trace_entries];
        let mut predecessor_lengths = vec![0u32; native_start.len()];
        let mut successor_lengths = vec![0u32; native_start.len()];
        let mut withdrawn_lengths = vec![0u32; native_start.len()];
        predecessor.read(&mut predecessor_trace)?;
        successor.read(&mut successor_trace)?;
        withdrawn.read(&mut withdrawn_trace)?;
        predecessor_lengths_device.read(&mut predecessor_lengths)?;
        successor_lengths_device.read(&mut successor_lengths)?;
        withdrawn_lengths_device.read(&mut withdrawn_lengths)?;
        for (at, length) in predecessor_lengths
            .iter()
            .chain(&successor_lengths)
            .chain(&withdrawn_lengths)
            .copied()
            .enumerate()
        {
            if length < 2 || length as usize > trace_stride {
                return Err(CudaRefineError::NativeRecurrenceDidNotClose {
                    at: at % native_start.len(),
                });
            }
        }

        let table_octets = std::mem::size_of_val(successor_table) as u64;
        let start_octets = std::mem::size_of_val(native_start) as u64;
        let trace_octets = trace_octets as u64;
        let length_octets = lengths_octets as u64;
        let visited_octets = visited_octets as u64;
        let scalar_ingress_octets = 5 * std::mem::size_of::<u32>() as u64;
        Ok(DeviceCondensedRecurrences {
            predecessor_trace,
            successor_trace,
            withdrawn_trace,
            predecessor_lengths,
            successor_lengths,
            withdrawn_lengths,
            trace_stride,
            launches: 1,
            synchronizations: 1,
            block_threads: self.block_x,
            active_lanes: native_start.len() as u32,
            visited_words,
            host_ingress_octets: table_octets + start_octets + scalar_ingress_octets,
            host_egress_octets: trace_octets * 3 + length_octets * 3,
            resident_octets: table_octets
                + start_octets
                + trace_octets * 3
                + length_octets * 3
                + visited_octets,
        })
    }
}

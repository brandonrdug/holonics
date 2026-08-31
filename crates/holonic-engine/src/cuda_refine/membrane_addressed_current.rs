//! Resident addressed current and receiver-history transport.
//!
//! This owner keeps the exact current occurrence mount, continuation address, and resident
//! generator passage together while preserving the public CUDA membrane API.

use super::*;

impl ResidentMembraneInteriorWord {
    /// Terminally inspect the finite-chart rank witness after its exact factorization square has
    /// closed. The production coordinate passage reads `selected_rank`, `selected_rows`, and
    /// `selected_columns` on the device instead.
    /// Mount the first rank-one current family into the already-founded operation complex.  A
    /// later call must present no host current: the previously descended target is then the sole
    /// continuing source.
    pub(super) fn mount_factored_current_state(
        &mut self,
        contexts: &[AddressedCurrentSection],
    ) -> Result<(u64, ResidentCurrentAddress), CudaRefineError> {
        let already_resident = self
            .factored_receiver_history
            .as_ref()
            .is_some_and(|mounted| mounted.current.is_some() || mounted.image.is_some());
        if already_resident {
            return Err(CudaRefineError::MembraneInteriorWordShape);
        }
        let factors = self.factors as usize;
        let valid_current = |current: &[(u32, BigUint)]| {
            !current.is_empty()
                && !current.windows(2).any(|pair| pair[0].0 >= pair[1].0)
                && !current
                    .iter()
                    .any(|(factor, coefficient)| *factor >= self.factors || coefficient.is_zero())
        };
        if contexts.is_empty()
            || contexts.len() > u32::MAX as usize
            || contexts.iter().any(|context| {
                context.quadratic_weight.is_zero() || !valid_current(&context.factor_current)
            })
        {
            return Err(CudaRefineError::MembraneInteriorWordShape);
        }
        let maximal_current = contexts
            .iter()
            .flat_map(|context| &context.factor_current)
            .map(|(_, coefficient)| coefficient)
            .max()
            .cloned()
            .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
        let maximal_weight = contexts
            .iter()
            .map(|context| &context.quadratic_weight)
            .max()
            .cloned()
            .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
        let current_limb_count = maximal_current.to_u32_digits().len().max(1);
        let weight_limb_count = maximal_weight.to_u32_digits().len().max(1);
        let mut current_limbs =
            vec![
                0_u32;
                contexts
                    .len()
                    .checked_mul(factors)
                    .and_then(|extent| extent.checked_mul(current_limb_count))
                    .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?
            ];
        let mut weight_limbs = vec![0_u32; contexts.len() * weight_limb_count];
        let boundary_state_present = contexts
            .iter()
            .map(|context| u8::from(context.boundary_state.is_some()))
            .collect::<Vec<_>>();
        let boundary_states = contexts
            .iter()
            .map(|context| context.boundary_state.unwrap_or(0))
            .collect::<Vec<_>>();
        for (context_at, context) in contexts.iter().enumerate() {
            for (factor, coefficient) in &context.factor_current {
                let limbs = coefficient.to_u32_digits();
                let begin = (context_at * factors + *factor as usize) * current_limb_count;
                current_limbs[begin..begin + limbs.len()].copy_from_slice(&limbs);
            }
            let limbs = context.quadratic_weight.to_u32_digits();
            let begin = context_at * weight_limb_count;
            weight_limbs[begin..begin + limbs.len()].copy_from_slice(&limbs);
        }
        driver(
            unsafe { cuCtxSetCurrent(self.card.context) },
            "cuCtxSetCurrent",
        )?;
        let ingress = std::mem::size_of_val(&current_limbs[..])
            .checked_add(std::mem::size_of_val(&weight_limbs[..]))
            .and_then(|octets| {
                octets.checked_add(std::mem::size_of_val(&boundary_state_present[..]))
            })
            .and_then(|octets| octets.checked_add(std::mem::size_of_val(&boundary_states[..])))
            .and_then(|octets| u64::try_from(octets).ok())
            .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        self.factored_receiver_history
            .as_mut()
            .ok_or(CudaRefineError::MembraneInteriorWordShape)?
            .current = Some(ResidentFactoredCurrentState {
            generation: 0,
            context_count: contexts.len() as u32,
            current_limb_count: current_limb_count as u32,
            weight_limb_count: weight_limb_count as u32,
            maximal_current,
            maximal_weight,
            active_factors: contexts
                .iter()
                .flat_map(|context| context.factor_current.iter().map(|(factor, _)| *factor))
                .collect::<BTreeSet<_>>()
                .into_iter()
                .collect(),
            boundary_state_present: Buffer::of(&boundary_state_present)?,
            boundary_states: Buffer::of(&boundary_states)?,
            current_limbs: Buffer::of(&current_limbs)?,
            weight_limbs: Buffer::of(&weight_limbs)?,
        });
        self.mount_host_ingress_octets = self
            .mount_host_ingress_octets
            .checked_add(ingress)
            .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        Ok((ingress, self.resident_current_address()?))
    }

    /// Close the transient current/image section of one exterior occurrence while retaining the
    /// single resident operation complex and every invariant morphology-derived axis.  A later
    /// exterior occurrence is a new addressed current through that same ecology: it must not be
    /// mistaken for a continuation address belonging to the preceding occurrence, and it must
    /// not remount the invariant receiver, restriction, or generator owners.
    pub fn begin_factored_current_occurrence(&mut self) -> Result<(), CudaRefineError> {
        // The first exterior occurrence precedes foundation of the composed operation complex;
        // there is then no transient predecessor to close. Later occurrences retain that founded
        // complex and release only its occurrence-local section.
        if let Some(mounted) = self.factored_receiver_history.as_mut() {
            mounted.current = None;
            mounted.image = None;
            // The sparse pair section is the occurrence-local native current, not invariant
            // morphology.  Retaining it here makes the next exterior occurrence collide with a
            // foreign carrier even though the receiver/restriction/generator owners are shared.
            mounted.sparse_pair = None;
            mounted.transported_image = None;
        }
        self.sparse_relational_current = None;
        Ok(())
    }

    pub(super) fn resident_current_address(
        &self,
    ) -> Result<ResidentCurrentAddress, CudaRefineError> {
        let mounted = self
            .factored_receiver_history
            .as_ref()
            .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
        let current = mounted
            .current
            .as_ref()
            .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
        Ok(ResidentCurrentAddress {
            operation_complex_identity_sha256: mounted.receipt.identity_sha256.clone(),
            device_context_identity: self.card.context as usize,
            generation: current.generation,
            section_population: current.context_count as usize,
        })
    }

    pub(super) fn validate_resident_current_address(
        &self,
        address: &ResidentCurrentAddress,
    ) -> Result<(), CudaRefineError> {
        if &self.resident_current_address()? != address {
            return Err(CudaRefineError::MembraneInteriorWordShape);
        }
        Ok(())
    }

    /// Mount and conduct the first exact current occurrence through the resident operation
    /// complex. Later continuation must use [`Self::continue_addressed_current_passage`].
    pub fn mount_addressed_current_passage(
        &mut self,
        contexts: &[AddressedCurrentSection],
        generator_targets: &[u32],
        generator_count: u32,
    ) -> Result<ResidentAddressedCurrentPassageReturn, CudaRefineError> {
        self.conduct_addressed_current_passage(None, contexts, generator_targets, generator_count)
    }

    /// Continue the exact addressed current occurrence already owned by the resident operation
    /// complex. `contexts` is cold reconstruction testimony for the pure passage certificate; it
    /// is neither uploaded nor used to determine the device transport.
    pub fn continue_addressed_current_passage(
        &mut self,
        source_address: &ResidentCurrentAddress,
        contexts: &[AddressedCurrentSection],
        generator_targets: &[u32],
        generator_count: u32,
    ) -> Result<ResidentAddressedCurrentPassageReturn, CudaRefineError> {
        self.conduct_addressed_current_passage(
            Some(source_address),
            contexts,
            generator_targets,
            generator_count,
        )
    }

    /// Push one exact weighted current family through a plural generator front on the card and
    /// condense only complete equal transported rows. No ambient covariance, host pivot,
    /// projective divisor, or caller-chosen rank enters the operation.
    fn conduct_addressed_current_passage(
        &mut self,
        source_address: Option<&ResidentCurrentAddress>,
        contexts: &[AddressedCurrentSection],
        generator_targets: &[u32],
        generator_count: u32,
    ) -> Result<ResidentAddressedCurrentPassageReturn, CudaRefineError> {
        let factors = self.factors as usize;
        let generators = generator_count as usize;
        if factors == 0
            || generators == 0
            || generator_targets.len() != generators.saturating_mul(factors)
            || generator_targets
                .iter()
                .any(|target| *target >= self.factors)
            || contexts.is_empty()
            || contexts.len() > u32::MAX as usize
        {
            return Err(CudaRefineError::MembraneInteriorWordShape);
        }
        self.mount_quadratic_action(generator_count, generator_targets)?;
        self.found_factored_receiver_history()?;
        let valid_current = |current: &[(u32, BigUint)]| {
            !current.is_empty()
                && !current.windows(2).any(|pair| pair[0].0 >= pair[1].0)
                && !current
                    .iter()
                    .any(|(factor, coefficient)| *factor >= self.factors || coefficient.is_zero())
        };
        if contexts.iter().any(|context| {
            context.quadratic_weight.is_zero() || !valid_current(&context.factor_current)
        }) {
            return Err(CudaRefineError::MembraneInteriorWordShape);
        }
        let source_current_mounted_this_pass = source_address.is_none();
        let (source_current_ingress_octets, source_address) = match source_address {
            Some(address) => {
                self.validate_resident_current_address(address)?;
                if address.section_population != contexts.len() {
                    return Err(CudaRefineError::MembraneInteriorWordShape);
                }
                (0, address.clone())
            }
            None => self.mount_factored_current_state(contexts)?,
        };
        driver(
            unsafe { cuCtxSetCurrent(self.card.context) },
            "cuCtxSetCurrent",
        )?;
        let source_state = self
            .factored_receiver_history
            .as_ref()
            .and_then(|mounted| mounted.current.as_ref())
            .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
        let source_context_population = source_state.context_count as usize;
        let candidate_count = source_context_population
            .checked_mul(generators)
            .filter(|count| *count <= u32::MAX as usize)
            .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        let maximal_current = source_state.maximal_current.clone();
        let maximal_weight = source_state.maximal_weight.clone();
        let mut source_current_pointer = source_state.current_limbs.pointer;
        let mut source_weight_pointer = source_state.weight_limbs.pointer;
        let mut source_state_present_pointer = source_state.boundary_state_present.pointer;
        let mut source_states_pointer = source_state.boundary_states.pointer;
        let maximal_preimage = generator_targets
            .chunks_exact(factors)
            .map(|generator| {
                let mut preimages = vec![0_usize; factors];
                for target in generator {
                    preimages[*target as usize] += 1;
                }
                preimages.into_iter().max().unwrap_or(0)
            })
            .max()
            .filter(|count| *count != 0)
            .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
        let source_limb_count = source_state.current_limb_count as usize;
        let target_limb_count = (&maximal_current * BigUint::from(maximal_preimage))
            .to_u32_digits()
            .len()
            .max(1);
        let source_weight_limb_count = source_state.weight_limb_count as usize;
        let target_weight_limb_count = (&maximal_weight * BigUint::from(candidate_count))
            .to_u32_digits()
            .len()
            .max(1);
        if [
            source_limb_count,
            target_limb_count,
            source_weight_limb_count,
            target_weight_limb_count,
        ]
        .into_iter()
        .any(|extent| extent > u32::MAX as usize)
            || factors
                .checked_mul(target_limb_count)
                .filter(|extent| *extent <= u32::MAX as usize)
                .is_none()
        {
            return Err(CudaRefineError::MembraneInteriorCurrentOutsideApparatus);
        }
        let candidate_current_population = candidate_count
            .checked_mul(factors)
            .and_then(|extent| extent.checked_mul(target_limb_count))
            .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        let action = self
            .quadratic_action
            .as_ref()
            .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
        let candidates = Buffer::alloc(
            candidate_current_population
                .checked_mul(std::mem::size_of::<u32>())
                .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?,
        )?;
        let candidate_state_present = Buffer::alloc(candidate_count)?;
        let candidate_states = Buffer::alloc(
            candidate_count
                .checked_mul(std::mem::size_of::<u32>())
                .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?,
        )?;
        let representatives = Buffer::alloc(
            candidate_count
                .checked_mul(std::mem::size_of::<u32>())
                .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?,
        )?;
        let target_currents = Buffer::alloc(
            candidate_current_population
                .checked_mul(std::mem::size_of::<u32>())
                .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?,
        )?;
        let target_weights = Buffer::alloc(
            candidate_count
                .checked_mul(target_weight_limb_count)
                .and_then(|extent| extent.checked_mul(std::mem::size_of::<u32>()))
                .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?,
        )?;
        let target_state_present = Buffer::alloc(candidate_count)?;
        let target_states = Buffer::alloc(
            candidate_count
                .checked_mul(std::mem::size_of::<u32>())
                .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?,
        )?;
        let candidate_to_target = Buffer::alloc(
            candidate_count
                .checked_mul(std::mem::size_of::<u32>())
                .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?,
        )?;
        let target_count = Buffer::alloc(std::mem::size_of::<u32>())?;
        target_count.fill(0, std::mem::size_of::<u32>())?;

        let mut generator_pointer = action.native_generator_targets.pointer;
        let mut candidate_pointer = candidates.pointer;
        let mut candidate_state_present_pointer = candidate_state_present.pointer;
        let mut candidate_states_pointer = candidate_states.pointer;
        let mut representative_pointer = representatives.pointer;
        let mut target_current_pointer = target_currents.pointer;
        let mut target_weight_pointer = target_weights.pointer;
        let mut target_state_present_pointer = target_state_present.pointer;
        let mut target_states_pointer = target_states.pointer;
        let mut candidate_to_target_pointer = candidate_to_target.pointer;
        let mut target_count_pointer = target_count.pointer;
        let mut context_count_wire = source_context_population as u32;
        let mut factor_count_wire = self.factors;
        let mut generator_count_wire = generator_count;
        let mut candidate_count_wire = candidate_count as u32;
        let mut source_limb_count_wire = source_limb_count as u32;
        let mut target_limb_count_wire = target_limb_count as u32;
        let mut source_weight_limb_count_wire = source_weight_limb_count as u32;
        let mut target_weight_limb_count_wire = target_weight_limb_count as u32;

        let mut transport_arguments: [*mut c_void; 12] = [
            &mut source_current_pointer as *mut u64 as *mut c_void,
            &mut source_state_present_pointer as *mut u64 as *mut c_void,
            &mut source_states_pointer as *mut u64 as *mut c_void,
            &mut generator_pointer as *mut u64 as *mut c_void,
            &mut candidate_pointer as *mut u64 as *mut c_void,
            &mut candidate_state_present_pointer as *mut u64 as *mut c_void,
            &mut candidate_states_pointer as *mut u64 as *mut c_void,
            &mut context_count_wire as *mut u32 as *mut c_void,
            &mut factor_count_wire as *mut u32 as *mut c_void,
            &mut generator_count_wire as *mut u32 as *mut c_void,
            &mut source_limb_count_wire as *mut u32 as *mut c_void,
            &mut target_limb_count_wire as *mut u32 as *mut c_void,
        ];
        let grid = self.card.grid_for(candidate_count as u64)?;
        driver(
            unsafe {
                cuLaunchKernel(
                    self.card.membrane_factor_current_transport,
                    grid,
                    1,
                    1,
                    self.card.block_x,
                    1,
                    1,
                    0,
                    ptr::null_mut(),
                    transport_arguments.as_mut_ptr(),
                    ptr::null_mut(),
                )
            },
            "cuLaunchKernel(transport_membrane_factor_current_sections)",
        )?;
        let mut identify_arguments: [*mut c_void; 7] = [
            &mut candidate_pointer as *mut u64 as *mut c_void,
            &mut candidate_state_present_pointer as *mut u64 as *mut c_void,
            &mut candidate_states_pointer as *mut u64 as *mut c_void,
            &mut representative_pointer as *mut u64 as *mut c_void,
            &mut candidate_count_wire as *mut u32 as *mut c_void,
            &mut factor_count_wire as *mut u32 as *mut c_void,
            &mut target_limb_count_wire as *mut u32 as *mut c_void,
        ];
        driver(
            unsafe {
                cuLaunchKernel(
                    self.card.membrane_factor_current_identify,
                    grid,
                    1,
                    1,
                    self.card.block_x,
                    1,
                    1,
                    0,
                    ptr::null_mut(),
                    identify_arguments.as_mut_ptr(),
                    ptr::null_mut(),
                )
            },
            "cuLaunchKernel(identify_membrane_equal_factor_current_sections)",
        )?;
        let mut compact_arguments: [*mut c_void; 17] = [
            &mut candidate_pointer as *mut u64 as *mut c_void,
            &mut source_weight_pointer as *mut u64 as *mut c_void,
            &mut representative_pointer as *mut u64 as *mut c_void,
            &mut candidate_state_present_pointer as *mut u64 as *mut c_void,
            &mut candidate_states_pointer as *mut u64 as *mut c_void,
            &mut target_current_pointer as *mut u64 as *mut c_void,
            &mut target_weight_pointer as *mut u64 as *mut c_void,
            &mut target_state_present_pointer as *mut u64 as *mut c_void,
            &mut target_states_pointer as *mut u64 as *mut c_void,
            &mut candidate_to_target_pointer as *mut u64 as *mut c_void,
            &mut target_count_pointer as *mut u64 as *mut c_void,
            &mut context_count_wire as *mut u32 as *mut c_void,
            &mut factor_count_wire as *mut u32 as *mut c_void,
            &mut generator_count_wire as *mut u32 as *mut c_void,
            &mut target_limb_count_wire as *mut u32 as *mut c_void,
            &mut source_weight_limb_count_wire as *mut u32 as *mut c_void,
            &mut target_weight_limb_count_wire as *mut u32 as *mut c_void,
        ];
        driver(
            unsafe {
                cuLaunchKernel(
                    self.card.membrane_factor_current_compact,
                    grid,
                    1,
                    1,
                    self.card.block_x,
                    1,
                    1,
                    0,
                    ptr::null_mut(),
                    compact_arguments.as_mut_ptr(),
                    ptr::null_mut(),
                )
            },
            "cuLaunchKernel(compact_membrane_equal_factor_current_sections)",
        )?;
        driver(unsafe { cuCtxSynchronize() }, "cuCtxSynchronize")?;
        self.card.launches += 3;

        let mut target_count_host = [0_u32; 1];
        target_count.read(&mut target_count_host)?;
        let target_context_population = target_count_host[0] as usize;
        if target_context_population == 0 || target_context_population > candidate_count {
            return Err(CudaRefineError::MembraneInteriorWordShape);
        }
        let mut target_current_host =
            vec![0_u32; target_context_population * factors * target_limb_count];
        let mut target_weight_host =
            vec![0_u32; target_context_population * target_weight_limb_count];
        let mut target_state_present_host = vec![0_u8; candidate_count];
        let mut target_states_host = vec![0_u32; candidate_count];
        let mut candidate_to_target_host = vec![0_u32; candidate_count];
        target_currents.read(&mut target_current_host)?;
        target_weights.read(&mut target_weight_host)?;
        target_state_present.read(&mut target_state_present_host)?;
        target_states.read(&mut target_states_host)?;
        target_state_present_host.truncate(target_context_population);
        target_states_host.truncate(target_context_population);
        candidate_to_target.read(&mut candidate_to_target_host)?;
        if candidate_to_target_host
            .iter()
            .any(|target| *target as usize >= target_context_population)
        {
            return Err(CudaRefineError::MembraneInteriorWordShape);
        }
        let mut returned_contexts = Vec::with_capacity(target_context_population);
        for target in 0..target_context_population {
            let weight_begin = target * target_weight_limb_count;
            let quadratic_weight = BigUint::new(
                target_weight_host[weight_begin..weight_begin + target_weight_limb_count].to_vec(),
            );
            let mut factor_current = Vec::new();
            for factor in 0..factors {
                let begin = (target * factors + factor) * target_limb_count;
                let coefficient =
                    BigUint::new(target_current_host[begin..begin + target_limb_count].to_vec());
                if !coefficient.is_zero() {
                    factor_current.push((factor as u32, coefficient));
                }
            }
            if quadratic_weight.is_zero() || factor_current.is_empty() {
                return Err(CudaRefineError::MembraneInteriorWordShape);
            }
            returned_contexts.push(AddressedCurrentSection {
                boundary_state: (target_state_present_host[target] != 0)
                    .then_some(target_states_host[target]),
                quadratic_weight,
                factor_current,
            });
        }
        let occurrences = candidate_to_target_host
            .into_iter()
            .enumerate()
            .map(|(candidate, target_section)| AddressedCurrentOccurrence {
                source_section: (candidate / generators) as u32,
                generator: (candidate % generators) as u32,
                target_section,
            })
            .collect::<Vec<_>>();
        let host_ingress_octets = source_current_ingress_octets;
        let host_egress_octets = [
            std::mem::size_of_val(&target_count_host[..]),
            std::mem::size_of_val(&target_current_host[..]),
            std::mem::size_of_val(&target_weight_host[..]),
            occurrences
                .len()
                .checked_mul(std::mem::size_of::<u32>())
                .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?,
        ]
        .into_iter()
        .try_fold(0_u64, |sum, octets| {
            sum.checked_add(u64::try_from(octets).ok()?)
        })
        .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        let target_maximal_current = returned_contexts
            .iter()
            .flat_map(|context| &context.factor_current)
            .map(|(_, coefficient)| coefficient)
            .max()
            .cloned()
            .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
        let target_maximal_weight = returned_contexts
            .iter()
            .map(|context| &context.quadratic_weight)
            .max()
            .cloned()
            .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
        let target_generation = source_address
            .generation
            .checked_add(1)
            .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
        let passage = AddressedCurrentPassage::found(
            self.factors,
            generator_targets.to_vec(),
            contexts.to_vec(),
            returned_contexts.clone(),
            occurrences,
        )
        .map_err(|_| CudaRefineError::MembraneInteriorWordShape)?;
        self.factored_receiver_history
            .as_mut()
            .ok_or(CudaRefineError::MembraneInteriorWordShape)?
            .current = Some(ResidentFactoredCurrentState {
            generation: target_generation,
            context_count: target_context_population as u32,
            current_limb_count: target_limb_count as u32,
            weight_limb_count: target_weight_limb_count as u32,
            maximal_current: target_maximal_current,
            maximal_weight: target_maximal_weight,
            active_factors: returned_contexts
                .iter()
                .flat_map(|context| context.factor_current.iter().map(|(factor, _)| *factor))
                .collect::<BTreeSet<_>>()
                .into_iter()
                .collect(),
            boundary_state_present: target_state_present,
            boundary_states: target_states,
            current_limbs: target_currents,
            weight_limbs: target_weights,
        });
        let target_address = self.resident_current_address()?;
        Ok(ResidentAddressedCurrentPassageReturn {
            passage,
            source_address,
            target_address,
            device: self.card.device_name.clone(),
            context_identity: self.card.context as usize,
            launches: 3,
            synchronizations: 1,
            host_ingress_octets,
            host_egress_octets,
            intermediate_host_egress_octets: 0,
            source_current_mounted_this_pass,
            invariant_transport_reuploaded: false,
            cpu_semantic_replay_after_device: false,
        })
    }
}

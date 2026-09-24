//! Resident generated-port transport and target-successor founding.

use super::*;

impl ResidentMembraneInteriorWord {
    /// Transport the standing sparse relational current through the same generator family which
    /// will found the next factor-current section.  The return owns only transported causal-adjoint
    /// coefficients; projective, phase and exterior receiver buffers are deliberately absent.
    pub(super) fn transport_sparse_relational_generators(
        &mut self,
        generator_targets: &[u32],
        generator_count: u32,
    ) -> Result<Option<ResidentSparseRelationalGeneratorTransport>, CudaRefineError> {
        let factors = self.factors as usize;
        let generators = generator_count as usize;
        if factors == 0
            || generators == 0
            || generator_targets.len() != factors.saturating_mul(generators)
        {
            return Err(CudaRefineError::MembraneInteriorWordShape);
        }
        let Some((
            state_present_pointer,
            states_pointer,
            state_count,
            source_real_sign_pointer,
            source_real_limbs_pointer,
            source_imaginary_sign_pointer,
            source_imaginary_limbs_pointer,
            source_limb_count,
            receipt,
            source_bound,
        )) = self.sparse_relational_current.as_ref().map(|current| {
            (
                current.state_present.pointer,
                current.states.pointer,
                current.state_count,
                current.factor_real_sign.pointer,
                current.factor_real_limbs.pointer,
                current.factor_imaginary_sign.pointer,
                current.factor_imaginary_limbs.pointer,
                current.factor_limb_count,
                current.receipt.clone(),
                current.returned_factor_bound.clone(),
            )
        })
        else {
            return Ok(None);
        };
        let generator_pointer = self
            .quadratic_action
            .as_ref()
            .ok_or(CudaRefineError::MembraneInteriorWordShape)?
            .native_generator_targets
            .pointer;
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
            .filter(|extent| *extent != 0)
            .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
        let returned_factor_bound = &source_bound * BigUint::from(maximal_preimage);
        let limb_count = returned_factor_bound.to_u32_digits().len().max(1);
        let population = state_count
            .checked_mul(generators)
            .and_then(|extent| extent.checked_mul(factors))
            .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        let limb_octets = population
            .checked_mul(limb_count)
            .and_then(|extent| extent.checked_mul(std::mem::size_of::<u32>()))
            .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        let real_sign = Buffer::alloc(population)?;
        let real_limbs = Buffer::alloc(limb_octets)?;
        let imaginary_sign = Buffer::alloc(population)?;
        let imaginary_limbs = Buffer::alloc(limb_octets)?;
        let obstruction = Buffer::alloc(std::mem::size_of::<u32>())?;
        obstruction.fill(0, std::mem::size_of::<u32>())?;

        let mut function = ptr::null_mut();
        driver(
            unsafe {
                cuModuleGetFunction(
                    &mut function,
                    self.card.module,
                    c"transport_membrane_sparse_relational_generator_limbs".as_ptr(),
                )
            },
            "cuModuleGetFunction(transport_membrane_sparse_relational_generator_limbs)",
        )?;
        let mut generator_pointer = generator_pointer;
        let mut source_state_present_pointer = state_present_pointer;
        let mut source_real_sign_pointer = source_real_sign_pointer;
        let mut source_real_limbs_pointer = source_real_limbs_pointer;
        let mut source_imaginary_sign_pointer = source_imaginary_sign_pointer;
        let mut source_imaginary_limbs_pointer = source_imaginary_limbs_pointer;
        let mut target_real_sign_pointer = real_sign.pointer;
        let mut target_real_limbs_pointer = real_limbs.pointer;
        let mut target_imaginary_sign_pointer = imaginary_sign.pointer;
        let mut target_imaginary_limbs_pointer = imaginary_limbs.pointer;
        let mut factor_count_wire = self.factors;
        let mut generator_count_wire = generator_count;
        let mut state_count_wire = state_count as u32;
        let mut source_limb_count_wire = source_limb_count as u32;
        let mut target_limb_count_wire = limb_count as u32;
        let mut obstruction_pointer = obstruction.pointer;
        let mut arguments: [*mut c_void; 16] = [
            &mut generator_pointer as *mut u64 as *mut c_void,
            &mut source_state_present_pointer as *mut u64 as *mut c_void,
            &mut source_real_sign_pointer as *mut u64 as *mut c_void,
            &mut source_real_limbs_pointer as *mut u64 as *mut c_void,
            &mut source_imaginary_sign_pointer as *mut u64 as *mut c_void,
            &mut source_imaginary_limbs_pointer as *mut u64 as *mut c_void,
            &mut target_real_sign_pointer as *mut u64 as *mut c_void,
            &mut target_real_limbs_pointer as *mut u64 as *mut c_void,
            &mut target_imaginary_sign_pointer as *mut u64 as *mut c_void,
            &mut target_imaginary_limbs_pointer as *mut u64 as *mut c_void,
            &mut factor_count_wire as *mut u32 as *mut c_void,
            &mut generator_count_wire as *mut u32 as *mut c_void,
            &mut state_count_wire as *mut u32 as *mut c_void,
            &mut source_limb_count_wire as *mut u32 as *mut c_void,
            &mut target_limb_count_wire as *mut u32 as *mut c_void,
            &mut obstruction_pointer as *mut u64 as *mut c_void,
        ];
        driver(
            unsafe {
                cuLaunchKernel(
                    function,
                    self.card.grid_for(population as u64)?,
                    1,
                    1,
                    self.card.block_x,
                    1,
                    1,
                    0,
                    ptr::null_mut(),
                    arguments.as_mut_ptr(),
                    ptr::null_mut(),
                )
            },
            "cuLaunchKernel(transport_membrane_sparse_relational_generator_limbs)",
        )?;
        self.card.launches = self
            .card
            .launches
            .checked_add(1)
            .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        Ok(Some(ResidentSparseRelationalGeneratorTransport {
            real_sign,
            real_limbs,
            imaginary_sign,
            imaginary_limbs,
            obstruction,
            state_present_pointer,
            states_pointer,
            state_count,
            limb_count,
            receipt,
            returned_factor_bound,
        }))
    }

    /// Gather the complete rested boundary aperture and found the target-site junction before any
    /// downstream observer is allocated.  This is the resident realization of
    /// `FiniteLocalCurrentEcology.step`; its return is later testimony, never a selector.
    pub(super) fn found_complete_resident_generated_port_successor(
        &mut self,
        front: &ResidentQuadraticMomentFront,
        port_population: usize,
        boundary: &ResidentBoundaryRestrictionFront,
        source_address: &ResidentCurrentAddress,
    ) -> Result<ResidentCompletedTargetObservationAperture, CudaRefineError> {
        let boundary_state_count = boundary.boundary_states.len();
        let restriction_count = boundary_state_count
            .checked_mul(port_population)
            .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        if boundary_state_count == 0
            || boundary.universal_ports.len() != port_population
            || restriction_count == 0
        {
            return Err(CudaRefineError::MembraneInteriorWordShape);
        }
        let (
            atlas_state_count,
            atlas_port_count,
            restriction_limb_count,
            maximal_restriction,
            state_port_transition_pointer,
            transition_targets_pointer,
            transition_factor_offsets_pointer,
            transition_factors_pointer,
            transition_current_limbs_pointer,
        ) = {
            let atlas = self
                .boundary_restriction_atlas
                .as_ref()
                .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
            if boundary
                .boundary_states
                .iter()
                .any(|state| *state >= atlas.state_count)
                || boundary
                    .universal_ports
                    .iter()
                    .any(|port| *port >= atlas.universal_port_count)
            {
                return Err(CudaRefineError::MembraneInteriorWordShape);
            }
            (
                atlas.state_count,
                atlas.universal_port_count,
                atlas.restriction_limb_count as usize,
                atlas.maximal_current.clone(),
                atlas.state_port_transition.pointer,
                atlas.transition_targets.pointer,
                atlas.transition_factor_offsets.pointer,
                atlas.transition_factors.pointer,
                atlas.transition_current_limbs.pointer,
            )
        };
        let factors = self.factors as usize;
        let restriction_current = Buffer::alloc(
            restriction_count
                .checked_mul(factors)
                .and_then(|extent| extent.checked_mul(restriction_limb_count))
                .and_then(|extent| extent.checked_mul(std::mem::size_of::<u32>()))
                .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?,
        )?;
        let restriction_present = Buffer::alloc(restriction_count)?;
        let restriction_target_states = Buffer::alloc(
            restriction_count
                .checked_mul(std::mem::size_of::<u32>())
                .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?,
        )?;
        let boundary_states = Buffer::of(&boundary.boundary_states)?;
        let universal_ports = Buffer::of(&boundary.universal_ports)?;
        let mut state_port_transition_pointer = state_port_transition_pointer;
        let mut transition_targets_pointer = transition_targets_pointer;
        let mut transition_factor_offsets_pointer = transition_factor_offsets_pointer;
        let mut transition_factors_pointer = transition_factors_pointer;
        let mut transition_current_limbs_pointer = transition_current_limbs_pointer;
        let mut boundary_states_pointer = boundary_states.pointer;
        let mut universal_ports_pointer = universal_ports.pointer;
        let mut restriction_current_pointer = restriction_current.pointer;
        let mut restriction_present_pointer = restriction_present.pointer;
        let mut restriction_target_states_pointer = restriction_target_states.pointer;
        let mut boundary_state_count_wire = boundary_state_count as u32;
        let mut port_count_wire = port_population as u32;
        let mut atlas_state_count_wire = atlas_state_count;
        let mut atlas_port_count_wire = atlas_port_count;
        let mut factor_count_wire = self.factors;
        let mut restriction_limb_count_wire = restriction_limb_count as u32;
        let mut gather_arguments: [*mut c_void; 16] = [
            &mut state_port_transition_pointer as *mut u64 as *mut c_void,
            &mut transition_targets_pointer as *mut u64 as *mut c_void,
            &mut transition_factor_offsets_pointer as *mut u64 as *mut c_void,
            &mut transition_factors_pointer as *mut u64 as *mut c_void,
            &mut transition_current_limbs_pointer as *mut u64 as *mut c_void,
            &mut boundary_states_pointer as *mut u64 as *mut c_void,
            &mut universal_ports_pointer as *mut u64 as *mut c_void,
            &mut restriction_current_pointer as *mut u64 as *mut c_void,
            &mut restriction_present_pointer as *mut u64 as *mut c_void,
            &mut restriction_target_states_pointer as *mut u64 as *mut c_void,
            &mut boundary_state_count_wire as *mut u32 as *mut c_void,
            &mut port_count_wire as *mut u32 as *mut c_void,
            &mut atlas_state_count_wire as *mut u32 as *mut c_void,
            &mut atlas_port_count_wire as *mut u32 as *mut c_void,
            &mut factor_count_wire as *mut u32 as *mut c_void,
            &mut restriction_limb_count_wire as *mut u32 as *mut c_void,
        ];
        driver(
            unsafe {
                cuLaunchKernel(
                    self.card.membrane_resident_boundary_restriction_gather,
                    self.card.grid_for(restriction_count as u64)?,
                    1,
                    1,
                    self.card.block_x,
                    1,
                    1,
                    0,
                    ptr::null_mut(),
                    gather_arguments.as_mut_ptr(),
                    ptr::null_mut(),
                )
            },
            "cuLaunchKernel(gather_membrane_resident_boundary_restrictions_before_step)",
        )?;
        self.card.launches = self
            .card
            .launches
            .checked_add(1)
            .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;

        let relational = self.transport_sparse_relational_generators(
            &front.generator_targets,
            front.generator_count,
        )?;
        let relational_continuation = relational.as_ref().map(|transport| {
            (
                transport.state_present_pointer,
                transport.states_pointer,
                transport.state_count,
                transport.real_sign.pointer,
                transport.real_limbs.pointer,
                transport.imaginary_sign.pointer,
                transport.imaginary_limbs.pointer,
                transport.limb_count,
                transport.receipt.clone(),
                transport.returned_factor_bound.clone(),
            )
        });
        let mut aperture = self.condition_resident_current_by_generated_ports(
            source_address,
            &front.contexts,
            &front.generator_targets,
            front.generator_count,
            port_population,
            &boundary.boundary_states,
            &restriction_target_states,
            &restriction_current,
            &restriction_present,
            restriction_limb_count,
            &maximal_restriction,
            front.resident_source.is_none(),
            relational_continuation,
            front.presented_current.as_deref(),
        )?;
        if let Some(transport) = relational {
            let mut obstruction = [0_u32; 1];
            transport.obstruction.read(&mut obstruction)?;
            if obstruction[0] != 0 {
                return Err(CudaRefineError::MembraneInteriorWordShape);
            }
            aperture.returned.launches = aperture
                .returned
                .launches
                .checked_add(1)
                .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        }
        aperture.returned.launches = aperture
            .returned
            .launches
            .checked_add(1)
            .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        aperture.returned.host_ingress_octets = aperture
            .returned
            .host_ingress_octets
            .checked_add(
                u64::try_from(
                    std::mem::size_of_val(&boundary.boundary_states[..])
                        .checked_add(std::mem::size_of_val(&boundary.universal_ports[..]))
                        .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?,
                )
                .map_err(|_| CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?,
            )
            .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        Ok(aperture)
    }
}

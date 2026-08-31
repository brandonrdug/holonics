use super::membrane_moment_plan::MomentFrontPlan;
use super::*;

fn buffer_octets(population: usize, limbs: usize) -> Result<usize, CudaRefineError> {
    population
        .checked_mul(limbs)
        .and_then(|held| held.checked_mul(std::mem::size_of::<u32>()))
        .ok_or(CudaRefineError::MembraneInteriorWordShape)
}

pub(super) struct MomentFrontWorkspace {
    pub(super) context_current: Option<Buffer>,
    pub(super) context_weight: Option<Buffer>,
    pub(super) context_state_present: Option<Buffer>,
    pub(super) context_states: Option<Buffer>,
    pub(super) restriction_port: Buffer,
    pub(super) port_restriction_offset: Buffer,
    pub(super) restriction_current: Buffer,
    pub(super) restriction_present: Buffer,
    pub(super) restriction_target_states: Buffer,
    pub(super) boundary_states_device: Buffer,
    pub(super) universal_ports_device: Buffer,
    pub(super) active_factor_chart: Buffer,
    pub(super) generator_targets: Buffer,
    pub(super) generator_local_targets: Buffer,
    pub(super) moment: Buffer,
    pub(super) left_scratch: Buffer,
    pub(super) right_scratch: Buffer,
    pub(super) quadratic_scratch: Buffer,
    pub(super) term_scratch: Buffer,
    pub(super) action_sign: Buffer,
    pub(super) action_limbs: Buffer,
    pub(super) reflected_sign: Buffer,
    pub(super) reflected_limbs: Buffer,
    pub(super) receiver_sign: Buffer,
    pub(super) receiver_limbs: Buffer,
    pub(super) receiver_norm_sign: Buffer,
    pub(super) receiver_norm_limbs: Buffer,
    pub(super) contact_real_sign: Buffer,
    pub(super) contact_real_limbs: Buffer,
    pub(super) contact_imaginary_sign: Buffer,
    pub(super) contact_imaginary_limbs: Buffer,
    pub(super) overlap_scratch: Buffer,
    pub(super) contribution_action_sign: Buffer,
    pub(super) contribution_action_limbs: Buffer,
    pub(super) contribution_reflected_sign: Buffer,
    pub(super) contribution_reflected_limbs: Buffer,
    pub(super) contribution_receiver_sign: Buffer,
    pub(super) contribution_receiver_limbs: Buffer,
    pub(super) contribution_receiver_norm_sign: Buffer,
    pub(super) contribution_receiver_norm_limbs: Buffer,
    pub(super) factorized_left_scratch: Buffer,
    pub(super) factorized_right_scratch: Buffer,
    pub(super) factorized_bucket_scratch: Buffer,
    pub(super) factorized_quadratic_scratch: Buffer,
    pub(super) factorized_term_scratch: Buffer,
    pub(super) factorized_overlap_scratch: Buffer,
    pub(super) support_port: Buffer,
    pub(super) support_real_sign: Buffer,
    pub(super) support_real_limbs: Buffer,
    pub(super) support_imaginary_sign: Buffer,
    pub(super) support_imaginary_limbs: Buffer,
    pub(super) port_real_sign: Buffer,
    pub(super) port_real_limbs: Buffer,
    pub(super) port_imaginary_sign: Buffer,
    pub(super) port_imaginary_limbs: Buffer,
    pub(super) joint_real_sign: Buffer,
    pub(super) joint_real_limbs: Buffer,
    pub(super) joint_imaginary_sign: Buffer,
    pub(super) joint_imaginary_limbs: Buffer,
    pub(super) port_action_sign: Buffer,
    pub(super) port_action_limbs: Buffer,
    pub(super) port_reflected_sign: Buffer,
    pub(super) port_reflected_limbs: Buffer,
    pub(super) port_receiver_sign: Buffer,
    pub(super) port_receiver_limbs: Buffer,
    pub(super) port_receiver_norm_sign: Buffer,
    pub(super) port_receiver_norm_limbs: Buffer,
    pub(super) compatibility_sign: Buffer,
    pub(super) compatibility_limbs: Buffer,
    pub(super) phase_norm_limbs: Buffer,
    pub(super) phase_locked: Buffer,
    pub(super) phase_square_scratch: Buffer,
    pub(super) phase_left_cross_scratch: Buffer,
    pub(super) phase_right_cross_scratch: Buffer,
    pub(super) situated_pairing_sign: Buffer,
    pub(super) situated_pairing_limbs: Buffer,
    pub(super) situated_pairing_imaginary_scratch: Buffer,
    pub(super) situated_pairing_front: Buffer,
    pub(super) complete_native_successor_front: Buffer,
    pub(super) incoming_real_sign_device: Buffer,
    pub(super) incoming_real_limbs_device: Buffer,
    pub(super) incoming_imaginary_sign_device: Buffer,
    pub(super) incoming_imaginary_limbs_device: Buffer,
    pub(super) stored_real_sign: Buffer,
    pub(super) stored_real_limbs: Buffer,
    pub(super) stored_imaginary_sign: Buffer,
    pub(super) stored_imaginary_limbs: Buffer,
    pub(super) balance_scratch: Buffer,
    pub(super) factorized_relational_workspace: Option<ResidentFactorizedRelationalWorkspace>,
}

pub(super) struct MomentCompletedTargetObserverBuffers {
    pub(super) face_current: Buffer,
    pub(super) face_relational_real_sign: Buffer,
    pub(super) face_relational_real_limbs: Buffer,
    pub(super) face_relational_imaginary_sign: Buffer,
    pub(super) face_relational_imaginary_limbs: Buffer,
    pub(super) relational_dot_real_sign: Buffer,
    pub(super) relational_dot_real_limbs: Buffer,
    pub(super) relational_dot_imaginary_sign: Buffer,
    pub(super) relational_dot_imaginary_limbs: Buffer,
    pub(super) target_norm_limbs: Buffer,
    pub(super) relational_norm_limbs: Buffer,
    pub(super) norm_product_limbs: Buffer,
    pub(super) first_scratch: Buffer,
    pub(super) second_scratch: Buffer,
    pub(super) third_scratch: Buffer,
    pub(super) obstruction: Buffer,
}

pub(super) fn allocate(
    word: &ResidentMembraneInteriorWord,
    plan: &MomentFrontPlan<'_>,
    post_target_observer: bool,
    materialize_moment_field: bool,
) -> Result<MomentFrontWorkspace, CudaRefineError> {
    driver(
        unsafe { cuCtxSetCurrent(word.card.context) },
        "cuCtxSetCurrent",
    )?;
    let context_current = if plan.resident_context_state.is_some() {
        None
    } else {
        Some(Buffer::of(&plan.context_current_limbs)?)
    };
    let context_weight = if plan.resident_context_state.is_some() {
        None
    } else {
        Some(Buffer::of(&plan.context_weight_limbs)?)
    };
    let context_state_present = if plan.resident_context_state.is_some() {
        None
    } else {
        Some(Buffer::of(&[0_u8])?)
    };
    let context_states = if plan.resident_context_state.is_some() {
        None
    } else {
        Some(Buffer::of(&[u32::MAX])?)
    };
    let restriction_port = if plan.resident_rectangular_restrictions {
        Buffer::alloc(std::mem::size_of::<u32>())?
    } else {
        Buffer::of(&plan.restriction_ports)?
    };
    let port_restriction_offset = if plan.resident_rectangular_restrictions {
        Buffer::alloc(std::mem::size_of::<u64>())?
    } else {
        Buffer::of(&plan.port_restriction_offsets)?
    };
    let restriction_current = if post_target_observer {
        Buffer::alloc(buffer_octets(
            plan.current_factor_population,
            plan.restriction_limb_count,
        )?)?
    } else if plan.resident_rectangular_restrictions {
        Buffer::alloc(buffer_octets(
            plan.restriction_count
                .saturating_mul(plan.current_factor_population),
            plan.restriction_limb_count,
        )?)?
    } else {
        Buffer::of(&plan.restriction_current_limbs)?
    };
    let restriction_present = Buffer::alloc(plan.legacy_restriction_allocation_count)?;
    let restriction_target_states = Buffer::alloc(
        plan.legacy_restriction_allocation_count
            .checked_mul(std::mem::size_of::<u32>())
            .ok_or(CudaRefineError::MembraneInteriorWordShape)?,
    )?;
    let boundary_states_device = if let Some(boundary) = plan.resident_boundary {
        Buffer::of(&boundary.boundary_states)?
    } else {
        Buffer::alloc(std::mem::size_of::<u32>())?
    };
    let universal_ports_device = if let Some(boundary) = plan.resident_boundary {
        Buffer::of(&boundary.universal_ports)?
    } else {
        Buffer::alloc(std::mem::size_of::<u32>())?
    };
    let active_factor_chart = if materialize_moment_field {
        Buffer::of(&plan.active_factors)?
    } else {
        Buffer::alloc(std::mem::size_of::<u32>())?
    };
    let generator_targets = Buffer::of(&plan.active_generator_targets)?;
    let generator_local_targets = Buffer::of(&plan.active_generator_local_targets)?;
    let moment = Buffer::alloc(buffer_octets(
        plan.moment_population,
        plan.moment_limb_count,
    )?)?;
    let left_scratch = Buffer::alloc(buffer_octets(
        plan.moment_population,
        plan.product_limb_count,
    )?)?;
    let right_scratch = Buffer::alloc(buffer_octets(
        plan.moment_population,
        plan.product_limb_count,
    )?)?;
    let quadratic_scratch = Buffer::alloc(buffer_octets(
        plan.moment_population,
        plan.quadratic_limb_count,
    )?)?;
    let term_scratch = Buffer::alloc(buffer_octets(
        plan.moment_population,
        plan.moment_limb_count,
    )?)?;
    let action_sign = Buffer::alloc(plan.family_population)?;
    let action_limbs = Buffer::alloc(buffer_octets(
        plan.family_population,
        plan.overlap_limb_count,
    )?)?;
    let reflected_sign = Buffer::alloc(plan.family_population)?;
    let reflected_limbs = Buffer::alloc(buffer_octets(
        plan.family_population,
        plan.overlap_limb_count,
    )?)?;
    let receiver_sign = Buffer::alloc(plan.receiver_population)?;
    let receiver_limbs = Buffer::alloc(buffer_octets(
        plan.receiver_population,
        plan.overlap_limb_count,
    )?)?;
    let receiver_norm_sign = Buffer::alloc(plan.receiver_population)?;
    let receiver_norm_limbs = Buffer::alloc(buffer_octets(
        plan.receiver_population,
        plan.overlap_limb_count,
    )?)?;
    let contact_real_sign = Buffer::alloc(plan.family_population)?;
    let contact_real_limbs = Buffer::alloc(buffer_octets(
        plan.family_population,
        plan.contact_limb_count,
    )?)?;
    let contact_imaginary_sign = Buffer::alloc(plan.family_population)?;
    let contact_imaginary_limbs = Buffer::alloc(buffer_octets(
        plan.family_population,
        plan.contact_limb_count,
    )?)?;
    let overlap_scratch = Buffer::alloc(buffer_octets(
        plan.contraction_work,
        plan.overlap_limb_count,
    )?)?;
    let contribution_action_sign = Buffer::alloc(plan.contribution_work)?;
    let contribution_action_limbs = Buffer::alloc(buffer_octets(
        plan.contribution_work,
        plan.overlap_limb_count,
    )?)?;
    let contribution_reflected_sign = Buffer::alloc(plan.contribution_work)?;
    let contribution_reflected_limbs = Buffer::alloc(buffer_octets(
        plan.contribution_work,
        plan.overlap_limb_count,
    )?)?;
    let contribution_receiver_sign = Buffer::alloc(plan.contribution_work)?;
    let contribution_receiver_limbs = Buffer::alloc(buffer_octets(
        plan.contribution_work,
        plan.overlap_limb_count,
    )?)?;
    let contribution_receiver_norm_sign = Buffer::alloc(plan.contribution_work)?;
    let contribution_receiver_norm_limbs = Buffer::alloc(buffer_octets(
        plan.contribution_work,
        plan.overlap_limb_count,
    )?)?;
    let factorized_left_scratch = Buffer::alloc(buffer_octets(
        plan.contribution_work,
        plan.product_limb_count,
    )?)?;
    let factorized_right_scratch = Buffer::alloc(buffer_octets(
        plan.contribution_work,
        plan.product_limb_count,
    )?)?;
    let factorized_bucket_scratch = Buffer::alloc(buffer_octets(
        plan.contribution_work,
        plan.product_limb_count,
    )?)?;
    let factorized_quadratic_scratch = Buffer::alloc(buffer_octets(
        plan.contribution_work,
        plan.quadratic_limb_count,
    )?)?;
    let factorized_term_scratch = Buffer::alloc(buffer_octets(
        plan.contribution_work,
        plan.moment_limb_count,
    )?)?;
    let factorized_overlap_scratch = Buffer::alloc(buffer_octets(
        plan.contribution_work,
        plan.overlap_limb_count,
    )?)?;
    let support_ports = (0..plan.response_population as u32).collect::<Vec<_>>();
    let support_port = Buffer::of(&support_ports)?;
    let support_real_sign = Buffer::alloc(plan.response_population)?;
    let support_real_limbs = Buffer::alloc(buffer_octets(
        plan.response_population,
        plan.radiation_limb_count,
    )?)?;
    let support_imaginary_sign = Buffer::alloc(plan.response_population)?;
    let support_imaginary_limbs = Buffer::alloc(buffer_octets(
        plan.response_population,
        plan.radiation_limb_count,
    )?)?;
    let port_real_sign = Buffer::alloc(plan.response_population)?;
    let port_real_limbs = Buffer::alloc(buffer_octets(
        plan.response_population,
        plan.radiation_limb_count,
    )?)?;
    let port_imaginary_sign = Buffer::alloc(plan.response_population)?;
    let port_imaginary_limbs = Buffer::alloc(buffer_octets(
        plan.response_population,
        plan.radiation_limb_count,
    )?)?;
    let joint_real_sign = Buffer::alloc(1)?;
    let joint_real_limbs = Buffer::alloc(buffer_octets(1, plan.radiation_limb_count)?)?;
    let joint_imaginary_sign = Buffer::alloc(1)?;
    let joint_imaginary_limbs = Buffer::alloc(buffer_octets(1, plan.radiation_limb_count)?)?;
    let port_action_sign = Buffer::alloc(plan.family_population)?;
    let port_action_limbs = Buffer::alloc(buffer_octets(
        plan.family_population,
        plan.overlap_limb_count,
    )?)?;
    let port_reflected_sign = Buffer::alloc(plan.family_population)?;
    let port_reflected_limbs = Buffer::alloc(buffer_octets(
        plan.family_population,
        plan.overlap_limb_count,
    )?)?;
    let port_receiver_sign = Buffer::alloc(plan.receiver_population)?;
    let port_receiver_limbs = Buffer::alloc(buffer_octets(
        plan.receiver_population,
        plan.overlap_limb_count,
    )?)?;
    let port_receiver_norm_sign = Buffer::alloc(plan.receiver_population)?;
    let port_receiver_norm_limbs = Buffer::alloc(buffer_octets(
        plan.receiver_population,
        plan.overlap_limb_count,
    )?)?;
    let compatibility_sign = Buffer::alloc(plan.component_population)?;
    let compatibility_limbs = Buffer::alloc(buffer_octets(
        plan.component_population,
        plan.compatibility_limb_count,
    )?)?;
    let phase_norm_limbs = Buffer::alloc(buffer_octets(
        plan.component_population,
        plan.norm_limb_count,
    )?)?;
    let phase_locked = Buffer::alloc(plan.response_population)?;
    let phase_square_scratch = Buffer::alloc(buffer_octets(
        plan.response_population,
        plan.square_limb_count,
    )?)?;
    let phase_left_cross_scratch = Buffer::alloc(buffer_octets(
        plan.response_population,
        plan.cross_limb_count,
    )?)?;
    let phase_right_cross_scratch = Buffer::alloc(buffer_octets(
        plan.response_population,
        plan.cross_limb_count,
    )?)?;
    let situated_pairing_sign = Buffer::alloc(plan.response_population)?;
    let situated_pairing_limbs = Buffer::alloc(buffer_octets(
        plan.response_population,
        plan.situated_pairing_limb_count,
    )?)?;
    let situated_pairing_imaginary_scratch = Buffer::alloc(buffer_octets(
        plan.response_population,
        plan.situated_pairing_limb_count,
    )?)?;
    let situated_pairing_front = Buffer::alloc(plan.response_population)?;
    let complete_native_successor_front = Buffer::alloc(plan.response_population)?;
    let incoming_real_sign_device = Buffer::of(&[plan.incoming_real_sign])?;
    let incoming_real_limbs_device = Buffer::of(&plan.incoming_real_limbs)?;
    let incoming_imaginary_sign_device = Buffer::of(&[plan.incoming_imaginary_sign])?;
    let incoming_imaginary_limbs_device = Buffer::of(&plan.incoming_imaginary_limbs)?;
    let stored_real_sign = Buffer::alloc(1)?;
    let stored_real_limbs = Buffer::alloc(buffer_octets(1, plan.stored_limb_count)?)?;
    let stored_imaginary_sign = Buffer::alloc(1)?;
    let stored_imaginary_limbs = Buffer::alloc(buffer_octets(1, plan.stored_limb_count)?)?;
    let balance_scratch = Buffer::alloc(buffer_octets(1, plan.stored_limb_count)?)?;
    let factorized_relational_workspace = if post_target_observer {
        None
    } else if let Some((
        _receipt,
        _,
        _,
        source_relational_state_count,
        _,
        _,
        _,
        _,
        _source_relational_limb_count,
        returned_factor_bound,
    )) = plan.relational_current_aperture.as_ref()
    {
        // The relational component is appended to the existing phase section.  Its device
        // coordinates therefore use the common component chart, even when its independently
        // derived bound is smaller than another admitted receiver component.
        let limb_count = plan.compatibility_limb_count;
        let transported_bound =
            &plan.maximal_context * BigUint::from(plan.maximal_generator_preimage);
        let transported_limb_count = transported_bound.to_u32_digits().len().max(1);
        let transported_relational_bound =
            returned_factor_bound * BigUint::from(plan.maximal_generator_preimage);
        let transported_relational_limb_count =
            transported_relational_bound.to_u32_digits().len().max(1);
        let transported_section_population =
            plan.context_count
                .checked_mul(plan.generator_count)
                .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        let transported_population = transported_section_population
            .checked_mul(plan.native_factors)
            .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        // Each resident context occupies one addressed boundary-state summand.  Its local
        // `(port,generator)` family is the complete non-radical partial population; pairing
        // that context with every other source-state face would only materialize the known
        // direct-sum radical.
        let partial_population = plan
            .local_response_population
            .checked_mul(plan.context_count)
            .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        let relational_factor_population = source_relational_state_count
            .checked_mul(plan.generator_count)
            .and_then(|population| population.checked_mul(plan.native_factors))
            .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        let transported_current = Buffer::alloc(buffer_octets(
            transported_population,
            transported_limb_count,
        )?)?;
        let transported_state_present = Buffer::alloc(transported_section_population)?;
        let transported_states = Buffer::alloc(
            transported_section_population
                .checked_mul(std::mem::size_of::<u32>())
                .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?,
        )?;
        let transported_relational_octets = buffer_octets(
            relational_factor_population,
            transported_relational_limb_count,
        )?;
        let transported_relational_real_sign = Buffer::alloc(relational_factor_population)?;
        let transported_relational_real_limbs = Buffer::alloc(transported_relational_octets)?;
        let transported_relational_imaginary_sign = Buffer::alloc(relational_factor_population)?;
        let transported_relational_imaginary_limbs = Buffer::alloc(transported_relational_octets)?;
        let partial_limbs = buffer_octets(partial_population, limb_count)?;
        let face_limbs = buffer_octets(plan.response_population, limb_count)?;
        let resident_working_octets = [
            buffer_octets(transported_population, transported_limb_count)?,
            transported_section_population,
            transported_section_population
                .checked_mul(std::mem::size_of::<u32>())
                .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?,
            transported_relational_octets
                .checked_mul(2)
                .and_then(|octets| octets.checked_add(relational_factor_population.checked_mul(2)?))
                .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?,
            partial_limbs
                .checked_mul(7)
                .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?,
            face_limbs
                .checked_mul(6)
                .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?,
            partial_population
                .checked_mul(2)
                .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?,
            std::mem::size_of::<u32>(),
        ]
        .into_iter()
        .try_fold(0_u64, |sum, octets| {
            sum.checked_add(u64::try_from(octets).ok()?)
        })
        .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
        let obstruction = Buffer::alloc(std::mem::size_of::<u32>())?;
        obstruction.fill(0, std::mem::size_of::<u32>())?;
        Some(ResidentFactorizedRelationalWorkspace {
            transported_current,
            transported_state_present,
            transported_states,
            transported_relational_real_sign,
            transported_relational_real_limbs,
            transported_relational_imaginary_sign,
            transported_relational_imaginary_limbs,
            partial_overlap: Buffer::alloc(partial_limbs)?,
            partial_target_norm: Buffer::alloc(partial_limbs)?,
            dot_real_signs: Buffer::alloc(partial_population)?,
            dot_real: Buffer::alloc(partial_limbs)?,
            dot_imaginary_signs: Buffer::alloc(partial_population)?,
            dot_imaginary: Buffer::alloc(partial_limbs)?,
            partial_first_scratch: Buffer::alloc(partial_limbs)?,
            partial_second_scratch: Buffer::alloc(partial_limbs)?,
            partial_third_scratch: Buffer::alloc(partial_limbs)?,
            relational_norm: Buffer::alloc(face_limbs)?,
            norm_first_scratch: Buffer::alloc(face_limbs)?,
            norm_second_scratch: Buffer::alloc(face_limbs)?,
            reduce_first_scratch: Buffer::alloc(face_limbs)?,
            reduce_second_scratch: Buffer::alloc(face_limbs)?,
            reduce_third_scratch: Buffer::alloc(face_limbs)?,
            obstruction,
            limb_count,
            transported_limb_count,
            transported_relational_limb_count,
            resident_working_octets,
        })
    } else {
        None
    };

    Ok(MomentFrontWorkspace {
        context_current,
        context_weight,
        context_state_present,
        context_states,
        restriction_port,
        port_restriction_offset,
        restriction_current,
        restriction_present,
        restriction_target_states,
        boundary_states_device,
        universal_ports_device,
        active_factor_chart,
        generator_targets,
        generator_local_targets,
        moment,
        left_scratch,
        right_scratch,
        quadratic_scratch,
        term_scratch,
        action_sign,
        action_limbs,
        reflected_sign,
        reflected_limbs,
        receiver_sign,
        receiver_limbs,
        receiver_norm_sign,
        receiver_norm_limbs,
        contact_real_sign,
        contact_real_limbs,
        contact_imaginary_sign,
        contact_imaginary_limbs,
        overlap_scratch,
        contribution_action_sign,
        contribution_action_limbs,
        contribution_reflected_sign,
        contribution_reflected_limbs,
        contribution_receiver_sign,
        contribution_receiver_limbs,
        contribution_receiver_norm_sign,
        contribution_receiver_norm_limbs,
        factorized_left_scratch,
        factorized_right_scratch,
        factorized_bucket_scratch,
        factorized_quadratic_scratch,
        factorized_term_scratch,
        factorized_overlap_scratch,
        support_port,
        support_real_sign,
        support_real_limbs,
        support_imaginary_sign,
        support_imaginary_limbs,
        port_real_sign,
        port_real_limbs,
        port_imaginary_sign,
        port_imaginary_limbs,
        joint_real_sign,
        joint_real_limbs,
        joint_imaginary_sign,
        joint_imaginary_limbs,
        port_action_sign,
        port_action_limbs,
        port_reflected_sign,
        port_reflected_limbs,
        port_receiver_sign,
        port_receiver_limbs,
        port_receiver_norm_sign,
        port_receiver_norm_limbs,
        compatibility_sign,
        compatibility_limbs,
        phase_norm_limbs,
        phase_locked,
        phase_square_scratch,
        phase_left_cross_scratch,
        phase_right_cross_scratch,
        situated_pairing_sign,
        situated_pairing_limbs,
        situated_pairing_imaginary_scratch,
        situated_pairing_front,
        complete_native_successor_front,
        incoming_real_sign_device,
        incoming_real_limbs_device,
        incoming_imaginary_sign_device,
        incoming_imaginary_limbs_device,
        stored_real_sign,
        stored_real_limbs,
        stored_imaginary_sign,
        stored_imaginary_limbs,
        balance_scratch,
        factorized_relational_workspace,
    })
}

pub(super) fn allocate_completed_target_observer(
    response_population: usize,
    face_factor_population: usize,
    face_current_limb_count: usize,
    face_relational_limb_count: usize,
    observer_limb_count: usize,
    observer_work: usize,
) -> Result<MomentCompletedTargetObserverBuffers, CudaRefineError> {
    let face_current = Buffer::alloc(buffer_octets(
        face_factor_population,
        face_current_limb_count,
    )?)?;
    let face_relational_real_sign = Buffer::alloc(face_factor_population)?;
    let face_relational_real_limbs = Buffer::alloc(buffer_octets(
        face_factor_population,
        face_relational_limb_count,
    )?)?;
    let face_relational_imaginary_sign = Buffer::alloc(face_factor_population)?;
    let face_relational_imaginary_limbs = Buffer::alloc(buffer_octets(
        face_factor_population,
        face_relational_limb_count,
    )?)?;
    let relational_dot_real_sign = Buffer::alloc(response_population)?;
    let relational_dot_real_limbs =
        Buffer::alloc(buffer_octets(response_population, observer_limb_count)?)?;
    let relational_dot_imaginary_sign = Buffer::alloc(response_population)?;
    let relational_dot_imaginary_limbs =
        Buffer::alloc(buffer_octets(response_population, observer_limb_count)?)?;
    let target_norm_limbs =
        Buffer::alloc(buffer_octets(response_population, observer_limb_count)?)?;
    let relational_norm_limbs =
        Buffer::alloc(buffer_octets(response_population, observer_limb_count)?)?;
    let norm_product_limbs =
        Buffer::alloc(buffer_octets(response_population, observer_limb_count)?)?;
    let first_scratch = Buffer::alloc(buffer_octets(observer_work, observer_limb_count)?)?;
    let second_scratch = Buffer::alloc(buffer_octets(observer_work, observer_limb_count)?)?;
    let third_scratch = Buffer::alloc(buffer_octets(observer_work, observer_limb_count)?)?;
    let obstruction = Buffer::alloc(std::mem::size_of::<u32>())?;
    obstruction.fill(0, std::mem::size_of::<u32>())?;
    Ok(MomentCompletedTargetObserverBuffers {
        face_current,
        face_relational_real_sign,
        face_relational_real_limbs,
        face_relational_imaginary_sign,
        face_relational_imaginary_limbs,
        relational_dot_real_sign,
        relational_dot_real_limbs,
        relational_dot_imaginary_sign,
        relational_dot_imaginary_limbs,
        target_norm_limbs,
        relational_norm_limbs,
        norm_product_limbs,
        first_scratch,
        second_scratch,
        third_scratch,
        obstruction,
    })
}

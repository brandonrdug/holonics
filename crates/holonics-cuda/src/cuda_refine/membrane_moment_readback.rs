use super::membrane_moment_execution::{MomentContractionLaunch, MomentFrontExecution};
use super::membrane_moment_plan::MomentFrontPlan;
use super::membrane_moment_workspace::MomentFrontWorkspace;
use super::*;

pub(super) fn readback(
    word: &mut ResidentMembraneInteriorWord,
    entering_current: &ExactComplexWaveCurrent,
    completed_step: Option<ResidentCompletedTargetObservationAperture>,
    execution: MomentFrontExecution<'_>,
    contraction: MomentContractionLaunch,
) -> Result<ResidentQuadraticMomentReturn, CudaRefineError> {
    let MomentFrontExecution {
        plan,
        workspace,
        post_target_observer,
        materialize_moment_field,
        resident_began,
        cuda_profile,
    } = execution;
    let MomentContractionLaunch {
        resident_gather_launches,
        factorized_relational_launches,
        completed_target_observer_workspace,
    } = contraction;
    let MomentFrontPlan {
        active_factors,
        active_generator_local_targets,
        active_generator_targets,
        balance_denominator,
        compatibility_limb_count,
        component_count,
        component_population,
        context_chunk_count,
        context_count,
        context_current_limbs,
        context_weight_limbs,
        contraction_work,
        contribution_work,
        cross_limb_count,
        current_factor_population,
        descend_boundary_state_receiver,
        factored_receiver_history,
        factors,
        family_population,
        generator_count,
        incidence_chunk_count,
        legacy_restriction_allocation_count,
        local_response_population,
        moment_limb_count,
        moment_population,
        native_factors,
        norm_limb_count,
        overlap_limb_count,
        port_population,
        port_restriction_offsets,
        product_limb_count,
        quadratic_limb_count,
        radiation_limb_count,
        receiver_population,
        resident_boundary,
        resident_current,
        resident_rectangular_restrictions,
        response_population,
        restriction_count,
        restriction_current_limbs,
        restriction_limb_count,
        restriction_ports,
        situated_pairing_limb_count,
        square_limb_count,
        stored_limb_count,
        ..
    } = plan;
    let MomentFrontWorkspace {
        action_limbs,
        action_sign,
        active_factor_chart,
        balance_scratch,
        boundary_states_device,
        boundary_port_imaginary_limbs,
        boundary_port_imaginary_sign,
        boundary_port_phase_locked,
        boundary_port_real_limbs,
        boundary_port_real_sign,
        compatibility_limbs,
        compatibility_sign,
        complete_native_successor_front,
        contact_imaginary_limbs,
        contact_imaginary_sign,
        contact_real_limbs,
        contact_real_sign,
        context_current,
        context_state_present,
        context_states,
        context_weight,
        contribution_action_limbs,
        contribution_action_sign,
        contribution_receiver_limbs,
        contribution_receiver_norm_limbs,
        contribution_receiver_norm_sign,
        contribution_receiver_sign,
        contribution_reflected_limbs,
        contribution_reflected_sign,
        factorized_bucket_scratch,
        factorized_left_scratch,
        factorized_overlap_scratch,
        factorized_quadratic_scratch,
        factorized_relational_workspace,
        factorized_right_scratch,
        factorized_term_scratch,
        generator_local_targets,
        generator_targets,
        incoming_imaginary_limbs_device,
        incoming_imaginary_sign_device,
        incoming_real_limbs_device,
        incoming_real_sign_device,
        joint_imaginary_limbs,
        joint_imaginary_sign,
        joint_real_limbs,
        joint_real_sign,
        left_scratch,
        moment,
        overlap_scratch,
        phase_left_cross_scratch,
        phase_locked,
        phase_norm_limbs,
        phase_right_cross_scratch,
        phase_square_scratch,
        port_action_limbs,
        port_action_sign,
        port_imaginary_limbs,
        port_imaginary_sign,
        port_real_limbs,
        port_real_sign,
        port_receiver_limbs,
        port_receiver_norm_limbs,
        port_receiver_norm_sign,
        port_receiver_sign,
        port_reflected_limbs,
        port_reflected_sign,
        port_restriction_offset,
        quadratic_scratch,
        receiver_limbs,
        receiver_norm_limbs,
        receiver_norm_sign,
        receiver_sign,
        reflected_limbs,
        reflected_sign,
        restriction_port,
        restriction_present,
        right_scratch,
        situated_pairing_front,
        situated_pairing_imaginary_scratch,
        situated_pairing_limbs,
        situated_pairing_sign,
        stored_imaginary_limbs,
        stored_imaginary_sign,
        stored_real_limbs,
        stored_real_sign,
        support_imaginary_limbs,
        support_imaginary_sign,
        support_port,
        support_real_limbs,
        support_real_sign,
        term_scratch,
        universal_ports_device,
        ..
    } = workspace;
    let octets = |population: usize, limbs: usize| {
        population
            .checked_mul(limbs)
            .and_then(|words| words.checked_mul(std::mem::size_of::<u32>()))
            .ok_or(CudaRefineError::MembraneInteriorWordShape)
    };
    let relational_observer_present =
        factorized_relational_workspace.is_some() || completed_target_observer_workspace.is_some();
    let moment_transport_launches = if post_target_observer {
        // The completed target is observed through the sparse inverse-incidence
        // passage above.  Re-running either moment transport would enact a
        // second state transition instead of observing the committed one.
        0_u64
    } else if materialize_moment_field {
        2_u64
    } else {
        u64::try_from(context_chunk_count)
            .ok()
            .and_then(|contexts| contexts.checked_mul(u64::try_from(incidence_chunk_count).ok()?))
            .and_then(|covers| covers.checked_mul(2))
            .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?
    };
    let launches = 6_u64
        .checked_add(moment_transport_launches)
        .and_then(|count| count.checked_add(resident_gather_launches))
        .and_then(|count| count.checked_add(factorized_relational_launches))
        .and_then(|count| count.checked_add(1))
        .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
    word.card.launches += launches;

    let restriction_population = if post_target_observer {
        // This receipt counts the retained caused incidences which carry the
        // completed target into its receiver chart.  It is not an outgoing
        // boundary-atlas population and therefore requires no fabricated
        // identity restriction at the target.
        completed_step
            .as_ref()
            .ok_or(CudaRefineError::MembraneInteriorWordShape)?
            .selected_slot_count
    } else if resident_rectangular_restrictions {
        let mut present = vec![0_u8; restriction_count];
        restriction_present.read(&mut present)?;
        if trace_configuration().holonics_uar2_trace {
            eprintln!(
                "post-target-observer-restrictions present={} total={} boundary-state-count={}",
                present.iter().filter(|value| **value != 0).count(),
                present.len(),
                resident_boundary
                    .expect("the resident presentation was established")
                    .boundary_states
                    .len(),
            );
        }
        if present.iter().any(|value| *value > 1)
            || present
                .chunks_exact(
                    resident_boundary
                        .expect("the resident presentation was established")
                        .boundary_states
                        .len(),
                )
                .any(|port| !port.iter().any(|value| *value != 0))
        {
            return Err(CudaRefineError::MembraneInteriorWordShape);
        }
        present.iter().filter(|value| **value != 0).count()
    } else {
        restriction_count
    };

    let mut moment_host = vec![0_u32; moment_population * moment_limb_count];
    let mut action_sign_host = vec![0_u8; family_population];
    let mut action_limbs_host = vec![0_u32; family_population * overlap_limb_count];
    let mut reflected_sign_host = vec![0_u8; family_population];
    let mut reflected_limbs_host = vec![0_u32; family_population * overlap_limb_count];
    let mut receiver_sign_host = vec![0_u8; receiver_population];
    let mut receiver_limbs_host = vec![0_u32; receiver_population * overlap_limb_count];
    let mut receiver_norm_sign_host = vec![0_u8; receiver_population];
    let mut receiver_norm_limbs_host = vec![0_u32; receiver_population * overlap_limb_count];
    moment.read(&mut moment_host)?;
    action_sign.read(&mut action_sign_host)?;
    action_limbs.read(&mut action_limbs_host)?;
    reflected_sign.read(&mut reflected_sign_host)?;
    reflected_limbs.read(&mut reflected_limbs_host)?;
    receiver_sign.read(&mut receiver_sign_host)?;
    receiver_limbs.read(&mut receiver_limbs_host)?;
    receiver_norm_sign.read(&mut receiver_norm_sign_host)?;
    receiver_norm_limbs.read(&mut receiver_norm_limbs_host)?;
    let mut port_receiver_norm_sign_host = vec![0_u8; receiver_population];
    port_receiver_norm_sign.read(&mut port_receiver_norm_sign_host)?;
    if trace_configuration().holonics_uar2_trace {
        eprintln!(
            "post-target-observer-sign-ranges action={:?} reflected={:?} receiver={:?} receiver-norm={:?} port-receiver-norm={:?}",
            action_sign_host.iter().copied().max(),
            reflected_sign_host.iter().copied().max(),
            receiver_sign_host.iter().copied().max(),
            receiver_norm_sign_host.iter().copied().max(),
            port_receiver_norm_sign_host.iter().copied().max(),
        );
    }
    if action_sign_host.iter().any(|sign| *sign > 2)
        || reflected_sign_host.iter().any(|sign| *sign > 2)
        || receiver_sign_host.iter().any(|sign| *sign > 2)
        || receiver_norm_sign_host.iter().any(|sign| *sign > 1)
        || port_receiver_norm_sign_host.iter().any(|sign| *sign > 1)
    {
        return Err(CudaRefineError::MembraneInteriorWordShape);
    }
    let mut face_real_sign_host = vec![0_u8; response_population];
    let mut face_real_limbs_host = vec![0_u32; response_population * radiation_limb_count];
    let mut face_imaginary_sign_host = vec![0_u8; response_population];
    let mut face_imaginary_limbs_host = vec![0_u32; response_population * radiation_limb_count];
    let mut boundary_real_sign_host = vec![0_u8; port_population];
    let mut boundary_real_limbs_host = vec![0_u32; port_population * radiation_limb_count];
    let mut boundary_imaginary_sign_host = vec![0_u8; port_population];
    let mut boundary_imaginary_limbs_host = vec![0_u32; port_population * radiation_limb_count];
    let mut boundary_port_phase_locked_host = vec![0_u8; port_population];
    let mut phase_locked_host = vec![0_u8; response_population];
    let mut situated_pairing_sign_host = vec![0_u8; response_population];
    let mut situated_pairing_limbs_host =
        vec![0_u32; response_population * situated_pairing_limb_count];
    let mut situated_pairing_front_host = vec![0_u8; response_population];
    let mut complete_native_successor_front_host = vec![0_u8; response_population];
    let mut joint_real_sign_host = [0_u8; 1];
    let mut joint_real_limbs_host = vec![0_u32; radiation_limb_count];
    let mut joint_imaginary_sign_host = [0_u8; 1];
    let mut joint_imaginary_limbs_host = vec![0_u32; radiation_limb_count];
    let mut stored_real_sign_host = [0_u8; 1];
    let mut stored_real_limbs_host = vec![0_u32; stored_limb_count];
    let mut stored_imaginary_sign_host = [0_u8; 1];
    let mut stored_imaginary_limbs_host = vec![0_u32; stored_limb_count];
    port_real_sign.read(&mut face_real_sign_host)?;
    port_real_limbs.read(&mut face_real_limbs_host)?;
    port_imaginary_sign.read(&mut face_imaginary_sign_host)?;
    port_imaginary_limbs.read(&mut face_imaginary_limbs_host)?;
    boundary_port_real_sign.read(&mut boundary_real_sign_host)?;
    boundary_port_real_limbs.read(&mut boundary_real_limbs_host)?;
    boundary_port_imaginary_sign.read(&mut boundary_imaginary_sign_host)?;
    boundary_port_imaginary_limbs.read(&mut boundary_imaginary_limbs_host)?;
    boundary_port_phase_locked.read(&mut boundary_port_phase_locked_host)?;
    phase_locked.read(&mut phase_locked_host)?;
    situated_pairing_sign.read(&mut situated_pairing_sign_host)?;
    situated_pairing_limbs.read(&mut situated_pairing_limbs_host)?;
    situated_pairing_front.read(&mut situated_pairing_front_host)?;
    complete_native_successor_front.read(&mut complete_native_successor_front_host)?;
    joint_real_sign.read(&mut joint_real_sign_host)?;
    joint_real_limbs.read(&mut joint_real_limbs_host)?;
    joint_imaginary_sign.read(&mut joint_imaginary_sign_host)?;
    joint_imaginary_limbs.read(&mut joint_imaginary_limbs_host)?;
    stored_real_sign.read(&mut stored_real_sign_host)?;
    stored_real_limbs.read(&mut stored_real_limbs_host)?;
    stored_imaginary_sign.read(&mut stored_imaginary_sign_host)?;
    stored_imaginary_limbs.read(&mut stored_imaginary_limbs_host)?;
    let factorized_relational_host = if let Some(workspace) =
        factorized_relational_workspace.as_ref()
    {
        let mut compatibility_sign_host = vec![0_u8; component_population];
        let mut compatibility_limbs_host =
            vec![0_u32; component_population * compatibility_limb_count];
        let mut target_norm_host = vec![0_u32; response_population * workspace.limb_count];
        let mut current_norm_host = vec![0_u32; response_population * workspace.limb_count];
        let mut norm_product_host = vec![0_u32; response_population * workspace.limb_count];
        let mut obstruction_host = [0_u32; 1];
        let mut oriented_real_signs = vec![0_u8; response_population];
        let mut oriented_real_limbs = vec![0_u32; response_population * workspace.limb_count];
        let mut oriented_imaginary_signs = vec![0_u8; response_population];
        let mut oriented_imaginary_limbs = vec![0_u32; response_population * workspace.limb_count];
        compatibility_sign.read(&mut compatibility_sign_host)?;
        compatibility_limbs.read(&mut compatibility_limbs_host)?;
        workspace.reduce_first_scratch.read(&mut target_norm_host)?;
        workspace.relational_norm.read(&mut current_norm_host)?;
        workspace
            .reduce_second_scratch
            .read(&mut norm_product_host)?;
        workspace.obstruction.read(&mut obstruction_host)?;
        workspace
            .oriented_real_signs
            .read(&mut oriented_real_signs)?;
        workspace.oriented_real.read(&mut oriented_real_limbs)?;
        workspace
            .oriented_imaginary_signs
            .read(&mut oriented_imaginary_signs)?;
        workspace
            .oriented_imaginary
            .read(&mut oriented_imaginary_limbs)?;
        Some((
            compatibility_sign_host,
            compatibility_limbs_host,
            target_norm_host,
            current_norm_host,
            norm_product_host,
            obstruction_host[0],
            oriented_real_signs,
            oriented_real_limbs,
            oriented_imaginary_signs,
            oriented_imaginary_limbs,
        ))
    } else if let Some(workspace) = completed_target_observer_workspace.as_ref() {
        let mut compatibility_sign_host = vec![0_u8; component_population];
        let mut compatibility_limbs_host =
            vec![0_u32; component_population * compatibility_limb_count];
        let mut target_norm_host = vec![0_u32; response_population * workspace.limb_count];
        let mut current_norm_host = vec![0_u32; response_population * workspace.limb_count];
        let mut norm_product_host = vec![0_u32; response_population * workspace.limb_count];
        let mut obstruction_host = [0_u32; 1];
        compatibility_sign.read(&mut compatibility_sign_host)?;
        compatibility_limbs.read(&mut compatibility_limbs_host)?;
        workspace.target_norm_limbs.read(&mut target_norm_host)?;
        workspace
            .relational_norm_limbs
            .read(&mut current_norm_host)?;
        workspace.norm_product_limbs.read(&mut norm_product_host)?;
        workspace.obstruction.read(&mut obstruction_host)?;
        Some((
            compatibility_sign_host,
            compatibility_limbs_host,
            target_norm_host,
            current_norm_host,
            norm_product_host,
            obstruction_host[0],
            Vec::new(),
            Vec::new(),
            Vec::new(),
            Vec::new(),
        ))
    } else {
        None
    };
    let completed_oriented_relational_host =
        if let Some(workspace) = completed_target_observer_workspace.as_ref() {
            let mut real_signs = vec![0_u8; response_population];
            let mut real_limbs = vec![0_u32; response_population * workspace.limb_count];
            let mut imaginary_signs = vec![0_u8; response_population];
            let mut imaginary_limbs = vec![0_u32; response_population * workspace.limb_count];
            workspace.relational_dot_real_sign.read(&mut real_signs)?;
            workspace.relational_dot_real_limbs.read(&mut real_limbs)?;
            workspace
                .relational_dot_imaginary_sign
                .read(&mut imaginary_signs)?;
            workspace
                .relational_dot_imaginary_limbs
                .read(&mut imaginary_limbs)?;
            Some((
                real_signs,
                real_limbs,
                imaginary_signs,
                imaginary_limbs,
                workspace.limb_count,
            ))
        } else {
            None
        };
    let phase_locked_port_population = phase_locked_host.iter().filter(|held| **held != 0).count();
    let situated_receiver_front_ports = situated_pairing_front_host
        .iter()
        .enumerate()
        .filter_map(|(port, held)| (*held != 0).then_some(port as u32))
        .collect::<Vec<_>>();
    if trace_configuration().holonics_uar2_trace {
        let complete_native_productive = complete_native_successor_front_host
            .iter()
            .filter(|held| **held != 0)
            .count();
        let phase_locked = phase_locked_host.iter().filter(|held| **held != 0).count();
        let invalid_relational = factorized_relational_host.as_ref().map(
            |(signs, _, target_norms, current_norms, products, obstruction, ..)| {
                (
                    *obstruction,
                    signs.iter().filter(|sign| **sign != 0).count(),
                    target_norms.iter().filter(|limb| **limb != 0).count(),
                    current_norms.iter().filter(|limb| **limb != 0).count(),
                    products.iter().filter(|limb| **limb != 0).count(),
                )
            },
        );
        eprintln!(
            "post-target-observer-front native-productive={} phase-locked={} situated={} relational={invalid_relational:?}",
            complete_native_productive,
            phase_locked,
            situated_receiver_front_ports.len(),
        );
    }
    if phase_locked_port_population == 0
        || phase_locked_host.iter().any(|held| *held > 1)
        || situated_pairing_sign_host.iter().any(|sign| *sign > 2)
        || situated_pairing_front_host.iter().any(|held| *held > 1)
        || complete_native_successor_front_host
            .iter()
            .any(|held| *held > 1)
        || complete_native_successor_front_host
            .iter()
            .all(|held| *held == 0)
        || situated_receiver_front_ports.is_empty()
        || situated_pairing_front_host
            .iter()
            .zip(&phase_locked_host)
            .any(|(situated, native)| *situated != 0 && *native == 0)
        || factorized_relational_host.as_ref().is_some_and(
            |(signs, _, _, _, _, obstruction, ..)| {
                *obstruction != 0 || signs.iter().any(|sign| *sign > 2)
            },
        )
        || completed_oriented_relational_host.as_ref().is_some_and(
            |(real_signs, _, imaginary_signs, _, _)| {
                real_signs.iter().any(|sign| *sign > 2)
                    || imaginary_signs.iter().any(|sign| *sign > 2)
            },
        )
    {
        return Err(CudaRefineError::MembraneInteriorWordShape);
    }
    let decode_integer = |sign: u8, limbs: &[u32]| -> Result<BigInt, CudaRefineError> {
        let value = decode_component(sign, limbs, &BigInt::one())?;
        Ok(value.numer().clone())
    };
    let situated_receiver_pairing_coordinates = (0..response_population)
        .map(|port| {
            let begin = port * situated_pairing_limb_count;
            decode_integer(
                situated_pairing_sign_host[port],
                &situated_pairing_limbs_host[begin..begin + situated_pairing_limb_count],
            )
        })
        .collect::<Result<Vec<_>, _>>()?;
    let (
        receiver_relational_coordinates,
        relational_target_self_pairings,
        relational_current_self_pairings,
        relational_squared_norm_products,
    ) = if let Some((
        compatibility_sign_host,
        compatibility_limbs_host,
        target_norm_host,
        current_norm_host,
        norm_product_host,
        _,
        _,
        _,
        _,
        _,
    )) = factorized_relational_host.as_ref()
    {
        let relational_component =
            word.families
                .checked_add(word.receiver_count)
                .ok_or(CudaRefineError::MembraneInteriorWordShape)? as usize;
        let mut coordinates = Vec::with_capacity(response_population);
        let mut target_norms = Vec::with_capacity(response_population);
        let mut current_norms = Vec::with_capacity(response_population);
        let mut norm_products = Vec::with_capacity(response_population);
        for face in 0..response_population {
            let component = face * component_count as usize + relational_component;
            let component_begin = component * compatibility_limb_count;
            coordinates.push(decode_integer(
                compatibility_sign_host[component],
                &compatibility_limbs_host
                    [component_begin..component_begin + compatibility_limb_count],
            )?);
            let begin = face * compatibility_limb_count;
            let target =
                BigUint::new(target_norm_host[begin..begin + compatibility_limb_count].to_vec());
            let current =
                BigUint::new(current_norm_host[begin..begin + compatibility_limb_count].to_vec());
            let product =
                BigUint::new(norm_product_host[begin..begin + compatibility_limb_count].to_vec());
            if &target * &current != product {
                if trace_configuration().holonics_uar2_trace {
                    eprintln!(
                        "post-target-observer-obstruction=relational-norm-product face={face}"
                    );
                }
                return Err(CudaRefineError::MembraneInteriorWordShape);
            }
            target_norms.push(target);
            current_norms.push(current);
            norm_products.push(product);
        }
        (coordinates, target_norms, current_norms, norm_products)
    } else {
        (Vec::new(), Vec::new(), Vec::new(), Vec::new())
    };
    let (
        relational_oriented_real_coordinates,
        relational_oriented_imaginary_coordinates,
        relational_modulus_squared_coordinates,
    ) = if let Some((real_signs, real_limbs, imaginary_signs, imaginary_limbs, limb_count)) =
        completed_oriented_relational_host.as_ref()
    {
        let mut real = Vec::with_capacity(response_population);
        let mut imaginary = Vec::with_capacity(response_population);
        let mut modulus_squared = Vec::with_capacity(response_population);
        for face in 0..response_population {
            let begin = face * *limb_count;
            let real_coordinate =
                decode_integer(real_signs[face], &real_limbs[begin..begin + *limb_count])?;
            let imaginary_coordinate = decode_integer(
                imaginary_signs[face],
                &imaginary_limbs[begin..begin + *limb_count],
            )?;
            if receiver_relational_coordinates.get(face) != Some(&real_coordinate) {
                if trace_configuration().holonics_uar2_trace {
                    eprintln!(
                        "post-target-observer-obstruction=oriented-real-projection face={face}"
                    );
                }
                return Err(CudaRefineError::MembraneInteriorWordShape);
            }
            modulus_squared.push(
                real_coordinate.magnitude() * real_coordinate.magnitude()
                    + imaginary_coordinate.magnitude() * imaginary_coordinate.magnitude(),
            );
            real.push(real_coordinate);
            imaginary.push(imaginary_coordinate);
        }
        (real, imaginary, modulus_squared)
    } else if let Some((
        _,
        _,
        _,
        _,
        _,
        _,
        real_signs,
        real_limbs,
        imaginary_signs,
        imaginary_limbs,
    )) = factorized_relational_host.as_ref()
    {
        let limb_count = factorized_relational_workspace
            .as_ref()
            .map(|workspace| workspace.limb_count)
            .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
        let mut real = Vec::with_capacity(response_population);
        let mut imaginary = Vec::with_capacity(response_population);
        for face in 0..response_population {
            let begin = face * limb_count;
            real.push(decode_integer(
                real_signs[face],
                &real_limbs[begin..begin + limb_count],
            )?);
            imaginary.push(decode_integer(
                imaginary_signs[face],
                &imaginary_limbs[begin..begin + limb_count],
            )?);
        }
        (
            real,
            imaginary,
            receiver_relational_coordinates
                .iter()
                .map(|coordinate| coordinate.magnitude().clone())
                .collect(),
        )
    } else {
        (
            Vec::new(),
            Vec::new(),
            receiver_relational_coordinates
                .iter()
                .map(|coordinate| coordinate.magnitude().clone())
                .collect::<Vec<_>>(),
        )
    };
    let mut ports = Vec::with_capacity(response_population);
    for port in 0..response_population {
        let port_moment = if materialize_moment_field {
            let moment_begin = port * factors * factors * moment_limb_count;
            moment_host[moment_begin..moment_begin + factors * factors * moment_limb_count]
                .chunks_exact(moment_limb_count)
                .map(|limbs| BigUint::new(limbs.to_vec()))
                .collect::<Vec<_>>()
        } else {
            Vec::new()
        };
        let family_begin = port * word.families as usize;
        let receiver_begin = port * word.receiver_count as usize;
        let decode_family = |signs: &[u8], limbs: &[u32]| {
            (family_begin..family_begin + word.families as usize)
                .map(|at| {
                    let begin = at * overlap_limb_count;
                    decode_integer(signs[at], &limbs[begin..begin + overlap_limb_count])
                })
                .collect::<Result<Vec<_>, _>>()
        };
        ports.push(ResidentQuadraticMomentPortReturn {
            port: port as u32,
            moment: port_moment,
            reflected_family_overlaps: decode_family(&reflected_sign_host, &reflected_limbs_host)?,
            family_overlaps: decode_family(&action_sign_host, &action_limbs_host)?,
            receiver_overlaps: (receiver_begin..receiver_begin + word.receiver_count as usize)
                .map(|at| {
                    let begin = at * overlap_limb_count;
                    decode_integer(
                        receiver_sign_host[at],
                        &receiver_limbs_host[begin..begin + overlap_limb_count],
                    )
                })
                .collect::<Result<Vec<_>, _>>()?,
            receiver_action_norms: (receiver_begin..receiver_begin + word.receiver_count as usize)
                .map(|at| {
                    let begin = at * overlap_limb_count;
                    BigUint::new(
                        receiver_norm_limbs_host[begin..begin + overlap_limb_count].to_vec(),
                    )
                })
                .collect(),
        });
    }
    let decode_current = |real_sign: u8,
                          real_limbs: &[u32],
                          imaginary_sign: u8,
                          imaginary_limbs: &[u32],
                          denominator: &BigInt|
     -> Result<ExactComplexWaveCurrent, CudaRefineError> {
        Ok(ExactComplexWaveCurrent::new(
            decode_component(real_sign, real_limbs, denominator)?,
            decode_component(imaginary_sign, imaginary_limbs, denominator)?,
        ))
    };
    let port_returns = (0..response_population)
        .map(|port| {
            let begin = port * radiation_limb_count;
            let end = begin + radiation_limb_count;
            let returned_response = decode_current(
                face_real_sign_host[port],
                &face_real_limbs_host[begin..end],
                face_imaginary_sign_host[port],
                &face_imaginary_limbs_host[begin..end],
                &word.family_common_denominator,
            )?;
            Ok(ResidentBoundaryChainPortReturn {
                port: port as u32,
                lies_in_joint_port_kernel: returned_response.is_zero(),
                lies_in_receiver_phase_front: phase_locked_host[port] != 0,
                returned_response,
            })
        })
        .collect::<Result<Vec<_>, CudaRefineError>>()?;
    let boundary_port_returns = (0..port_population)
        .map(|port| {
            let begin = port * radiation_limb_count;
            let end = begin + radiation_limb_count;
            let returned_response = decode_current(
                boundary_real_sign_host[port],
                &boundary_real_limbs_host[begin..end],
                boundary_imaginary_sign_host[port],
                &boundary_imaginary_limbs_host[begin..end],
                &word.family_common_denominator,
            )?;
            Ok(ResidentBoundaryChainPortReturn {
                port: port as u32,
                lies_in_joint_port_kernel: returned_response.is_zero(),
                lies_in_receiver_phase_front: boundary_port_phase_locked_host[port] != 0,
                returned_response,
            })
        })
        .collect::<Result<Vec<_>, CudaRefineError>>()?;
    let total_returned_current = decode_current(
        joint_real_sign_host[0],
        &joint_real_limbs_host,
        joint_imaginary_sign_host[0],
        &joint_imaginary_limbs_host,
        &word.family_common_denominator,
    )?;
    let stored_difference = decode_current(
        stored_real_sign_host[0],
        &stored_real_limbs_host,
        stored_imaginary_sign_host[0],
        &stored_imaginary_limbs_host,
        &balance_denominator,
    )?;
    let local_balance_closes = stored_difference.add(&total_returned_current) == *entering_current;
    let boundary_sum = boundary_port_returns
        .iter()
        .fold(ExactComplexWaveCurrent::zero(), |total, returned| {
            total.add(&returned.returned_response)
        });
    if !local_balance_closes || boundary_sum != total_returned_current {
        if trace_configuration().holonics_uar2_trace {
            eprintln!("post-target-observer-obstruction=local-current-balance");
        }
        return Err(CudaRefineError::MembraneInteriorCurrentOutsideApparatus);
    }
    let situated_face_ports = (0..response_population)
        .map(|face| {
            if materialize_moment_field {
                face as u32
            } else {
                ((face % local_response_population) / generator_count) as u32
            }
        })
        .collect::<Vec<_>>();
    let situated_face_generators = (0..response_population)
        .map(|face| {
            if materialize_moment_field {
                0
            } else {
                ((face % local_response_population) % generator_count) as u32
            }
        })
        .collect::<Vec<_>>();
    let situated_face_source_states = if descend_boundary_state_receiver {
        vec![u32::MAX; response_population]
    } else if let Some(boundary) = resident_boundary {
        (0..response_population)
            .map(|face| boundary.boundary_states[face / local_response_population])
            .collect::<Vec<_>>()
    } else {
        vec![u32::MAX; response_population]
    };
    let situated_receiver_front_ports = situated_receiver_front_ports
        .iter()
        .map(|face| situated_face_ports[*face as usize])
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect::<Vec<_>>();
    let situated_receiver_pairing = ResidentSituatedReceiverPairingReturn {
        receiver_chart: if completed_target_observer_workspace.is_some() {
            "completed-target-sparse-incidence-relational-and-exterior-current".to_owned()
        } else if factorized_relational_workspace.is_some() {
            "state-addressed-factorized-relational-and-exterior-current".to_owned()
        } else {
            "exterior-complex-current".to_owned()
        },
        coordinate_denominator: &word.family_common_denominator * &balance_denominator,
        coordinates: situated_receiver_pairing_coordinates,
        current_self_pairings: Vec::new(),
        ingress_self_pairings: Vec::new(),
        squared_norm_products: Vec::new(),
        relational_oriented_real_coordinates,
        relational_oriented_imaginary_coordinates,
        relational_modulus_squared_coordinates,
        relational_target_self_pairings,
        relational_current_self_pairings,
        relational_squared_norm_products,
        face_source_states: situated_face_source_states,
        face_ports: situated_face_ports,
        face_generators: situated_face_generators,
        front_faces: situated_pairing_front_host
            .iter()
            .enumerate()
            .filter_map(|(face, held)| (*held != 0).then_some(face as u32))
            .collect(),
        front_is_unique: situated_pairing_front_host
            .iter()
            .filter(|held| **held != 0)
            .count()
            == 1,
        front_ports: situated_receiver_front_ports,
        native_phase_front_faces: phase_locked_host
            .iter()
            .enumerate()
            .filter_map(|(face, held)| (*held != 0).then_some(face as u32))
            .collect(),
        projective_candidate_faces: Vec::new(),
        projective_interval_limb_count: 0,
        projective_interval_obstruction_reopened_front: false,
        complete_native_phase_front_retained: true,
        ingress_moment_reconstruction_fibre_retained: relational_observer_present,
    };
    let direct_restriction_ingress = if resident_rectangular_restrictions {
        0
    } else {
        std::mem::size_of_val(&restriction_ports[..])
            .checked_add(std::mem::size_of_val(&port_restriction_offsets[..]))
            .and_then(|octets| {
                octets.checked_add(std::mem::size_of_val(&restriction_current_limbs[..]))
            })
            .ok_or(CudaRefineError::MembraneInteriorWordShape)?
    };
    let resident_aperture_ingress = if let Some(boundary) = resident_boundary {
        std::mem::size_of_val(&boundary.boundary_states[..])
            .checked_add(std::mem::size_of_val(&boundary.universal_ports[..]))
            .ok_or(CudaRefineError::MembraneInteriorWordShape)?
    } else {
        0
    };
    let materialized_chart_ingress = if materialize_moment_field {
        std::mem::size_of_val(&active_factors[..])
            .checked_add(std::mem::size_of_val(&active_generator_targets[..]))
            .and_then(|octets| {
                octets.checked_add(std::mem::size_of_val(&active_generator_local_targets[..]))
            })
            .ok_or(CudaRefineError::MembraneInteriorWordShape)?
    } else {
        0
    };
    let successor_host_ingress_octets = [
        std::mem::size_of_val(&context_current_limbs[..]),
        std::mem::size_of_val(&context_weight_limbs[..]),
        direct_restriction_ingress,
        resident_aperture_ingress,
        materialized_chart_ingress,
    ]
    .into_iter()
    .try_fold(0_u64, |sum, octets| {
        sum.checked_add(u64::try_from(octets).ok()?)
    })
    .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
    let relational_host_egress_octets = factorized_relational_host
        .as_ref()
        .and_then(
            |(
                signs,
                coordinates,
                target_norms,
                current_norms,
                norm_products,
                _,
                oriented_real_signs,
                oriented_real,
                oriented_imaginary_signs,
                oriented_imaginary,
            )| {
                std::mem::size_of_val(&signs[..])
                    .checked_add(std::mem::size_of_val(&coordinates[..]))
                    .and_then(|held| held.checked_add(std::mem::size_of_val(&target_norms[..])))
                    .and_then(|held| held.checked_add(std::mem::size_of_val(&current_norms[..])))
                    .and_then(|held| held.checked_add(std::mem::size_of_val(&norm_products[..])))
                    .and_then(|held| {
                        held.checked_add(std::mem::size_of_val(&oriented_real_signs[..]))
                    })
                    .and_then(|held| held.checked_add(std::mem::size_of_val(&oriented_real[..])))
                    .and_then(|held| {
                        held.checked_add(std::mem::size_of_val(&oriented_imaginary_signs[..]))
                    })
                    .and_then(|held| {
                        held.checked_add(std::mem::size_of_val(&oriented_imaginary[..]))
                    })
                    .and_then(|held| held.checked_add(std::mem::size_of::<u32>()))
            },
        )
        .unwrap_or(0)
        .checked_add(
            completed_oriented_relational_host
                .as_ref()
                .and_then(
                    |(real_signs, real_coordinates, imaginary_signs, imaginary_coordinates, _)| {
                        std::mem::size_of_val(&real_signs[..])
                            .checked_add(std::mem::size_of_val(&real_coordinates[..]))
                            .and_then(|held| {
                                held.checked_add(std::mem::size_of_val(&imaginary_signs[..]))
                            })
                            .and_then(|held| {
                                held.checked_add(std::mem::size_of_val(&imaginary_coordinates[..]))
                            })
                    },
                )
                .unwrap_or(0),
        )
        .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
    let successor_host_egress_octets = std::mem::size_of_val(&moment_host[..])
        .checked_add(std::mem::size_of_val(&action_sign_host[..]))
        .and_then(|octets| octets.checked_add(std::mem::size_of_val(&action_limbs_host[..])))
        .and_then(|octets| octets.checked_add(std::mem::size_of_val(&reflected_sign_host[..])))
        .and_then(|octets| octets.checked_add(std::mem::size_of_val(&reflected_limbs_host[..])))
        .and_then(|octets| octets.checked_add(std::mem::size_of_val(&receiver_sign_host[..])))
        .and_then(|octets| octets.checked_add(std::mem::size_of_val(&receiver_limbs_host[..])))
        .and_then(|octets| octets.checked_add(std::mem::size_of_val(&receiver_norm_sign_host[..])))
        .and_then(|octets| octets.checked_add(std::mem::size_of_val(&receiver_norm_limbs_host[..])))
        .and_then(|octets| {
            octets.checked_add(std::mem::size_of_val(&situated_pairing_sign_host[..]))
        })
        .and_then(|octets| {
            octets.checked_add(std::mem::size_of_val(&situated_pairing_limbs_host[..]))
        })
        .and_then(|octets| {
            octets.checked_add(std::mem::size_of_val(&situated_pairing_front_host[..]))
        })
        .and_then(|octets| {
            octets.checked_add(
                if resident_rectangular_restrictions && !post_target_observer {
                    restriction_count
                } else {
                    0
                },
            )
        })
        .and_then(|octets| octets.checked_add(relational_host_egress_octets))
        .ok_or(CudaRefineError::MembraneInteriorWordShape)?
        as u64;
    let dense_working_octets = octets(moment_population, moment_limb_count)?
        .checked_add(octets(moment_population, product_limb_count)? * 2)
        .and_then(|held| held.checked_add(octets(moment_population, quadratic_limb_count).ok()?))
        .and_then(|held| held.checked_add(octets(moment_population, moment_limb_count).ok()?))
        .and_then(|held| held.checked_add(octets(contraction_work, overlap_limb_count).ok()?))
        .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
    let factorized_working_octets = octets(contribution_work, product_limb_count)?
        .checked_mul(3)
        .and_then(|held| held.checked_add(octets(contribution_work, quadratic_limb_count).ok()?))
        .and_then(|held| held.checked_add(octets(contribution_work, moment_limb_count).ok()?))
        .and_then(|held| {
            held.checked_add(
                octets(contribution_work, overlap_limb_count)
                    .ok()?
                    .checked_mul(5)?,
            )
        })
        .and_then(|held| held.checked_add(contribution_work.checked_mul(4)?))
        .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
    let phase_working_octets = octets(component_population, compatibility_limb_count)?
        .checked_add(octets(component_population, norm_limb_count)?)
        .and_then(|held| held.checked_add(component_population))
        .and_then(|held| held.checked_add(response_population))
        .and_then(|held| held.checked_add(response_population))
        .and_then(|held| held.checked_add(octets(response_population, square_limb_count).ok()?))
        .and_then(|held| {
            held.checked_add(
                octets(response_population, cross_limb_count)
                    .ok()?
                    .checked_mul(2)?,
            )
        })
        .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
    let situated_pairing_working_octets = response_population
        .checked_add(octets(response_population, situated_pairing_limb_count)?)
        .and_then(|held| {
            held.checked_add(octets(response_population, situated_pairing_limb_count).ok()?)
        })
        .and_then(|held| held.checked_add(response_population))
        .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
    let relational_working_octets =
        if let Some(workspace) = factorized_relational_workspace.as_ref() {
            usize::try_from(workspace.resident_working_octets)
                .map_err(|_| CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?
        } else if let Some(workspace) = completed_target_observer_workspace.as_ref() {
            usize::try_from(workspace.resident_working_octets)
                .map_err(|_| CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?
        } else {
            0
        };
    let resident_working_octets = (if materialize_moment_field {
        dense_working_octets
    } else {
        factorized_working_octets
    })
    .checked_add(phase_working_octets)
    .and_then(|held| held.checked_add(situated_pairing_working_octets))
    .and_then(|held| {
        held.checked_add(
            octets(
                legacy_restriction_allocation_count.saturating_mul(current_factor_population),
                restriction_limb_count,
            )
            .ok()?,
        )
    })
    .and_then(|held| held.checked_add(legacy_restriction_allocation_count))
    .and_then(|held| {
        held.checked_add(
            legacy_restriction_allocation_count.checked_mul(std::mem::size_of::<u32>())?,
        )
    })
    .and_then(|held| held.checked_add(relational_working_octets))
    .ok_or(CudaRefineError::MembraneInteriorWordShape)? as u64;
    if cuda_profile {
        eprintln!(
            "mem6-cuda before_buffer_release_ms={} resident_working_octets={}",
            resident_began.elapsed().as_millis(),
            resident_working_octets,
        );
    }
    // The phase/current word has crossed its terminal synchronization and all of its cold
    // receiver testimony has already been reconstructed above.  Release that occurrence-
    // local apparatus before founding the successor current.  Keeping these buffers alive
    // across the successor allocation falsely made two causal orders co-resident; at the
    // plural state front that occupied nearly the complete card even though the direct-sum
    // successor retains only state-matched incidences.
    drop(context_current);
    drop(context_weight);
    drop(context_state_present);
    drop(context_states);
    drop(restriction_port);
    drop(port_restriction_offset);
    drop(boundary_states_device);
    drop(universal_ports_device);
    drop(active_factor_chart);
    drop(generator_targets);
    drop(generator_local_targets);
    drop(moment);
    drop(left_scratch);
    drop(right_scratch);
    drop(quadratic_scratch);
    drop(term_scratch);
    drop(action_sign);
    drop(action_limbs);
    drop(reflected_sign);
    drop(reflected_limbs);
    drop(receiver_sign);
    drop(receiver_limbs);
    drop(receiver_norm_sign);
    drop(receiver_norm_limbs);
    drop(contact_real_sign);
    drop(contact_real_limbs);
    drop(contact_imaginary_sign);
    drop(contact_imaginary_limbs);
    drop(overlap_scratch);
    drop(contribution_action_sign);
    drop(contribution_action_limbs);
    drop(contribution_reflected_sign);
    drop(contribution_reflected_limbs);
    drop(contribution_receiver_sign);
    drop(contribution_receiver_limbs);
    drop(contribution_receiver_norm_sign);
    drop(contribution_receiver_norm_limbs);
    drop(factorized_left_scratch);
    drop(factorized_right_scratch);
    drop(factorized_bucket_scratch);
    drop(factorized_quadratic_scratch);
    drop(factorized_term_scratch);
    drop(factorized_overlap_scratch);
    drop(support_port);
    drop(support_real_sign);
    drop(support_real_limbs);
    drop(support_imaginary_sign);
    drop(support_imaginary_limbs);
    drop(port_real_sign);
    drop(port_real_limbs);
    drop(port_imaginary_sign);
    drop(port_imaginary_limbs);
    drop(boundary_port_real_sign);
    drop(boundary_port_real_limbs);
    drop(boundary_port_imaginary_sign);
    drop(boundary_port_imaginary_limbs);
    drop(boundary_port_phase_locked);
    drop(joint_real_sign);
    drop(joint_real_limbs);
    drop(joint_imaginary_sign);
    drop(joint_imaginary_limbs);
    drop(port_action_sign);
    drop(port_action_limbs);
    drop(port_reflected_sign);
    drop(port_reflected_limbs);
    drop(port_receiver_sign);
    drop(port_receiver_limbs);
    drop(port_receiver_norm_sign);
    drop(port_receiver_norm_limbs);
    drop(compatibility_sign);
    drop(compatibility_limbs);
    drop(phase_norm_limbs);
    drop(phase_locked);
    drop(phase_square_scratch);
    drop(phase_left_cross_scratch);
    drop(phase_right_cross_scratch);
    drop(situated_pairing_sign);
    drop(situated_pairing_limbs);
    drop(situated_pairing_imaginary_scratch);
    drop(incoming_real_sign_device);
    drop(incoming_real_limbs_device);
    drop(incoming_imaginary_sign_device);
    drop(incoming_imaginary_limbs_device);
    drop(stored_real_sign);
    drop(stored_real_limbs);
    drop(stored_imaginary_sign);
    drop(stored_imaginary_limbs);
    drop(balance_scratch);

    // The relational observer workspace belongs only to `observe_R(X')`.  The causal-adjoint
    // current which founded `X'` was already transported and committed by the early step.
    drop(factorized_relational_workspace);
    drop(completed_target_observer_workspace);
    let continuation_launches = completed_step
        .as_ref()
        .map_or(0, |aperture| aperture.returned.launches);
    let continuation_synchronizations = completed_step
        .as_ref()
        .map_or(0, |aperture| aperture.returned.synchronizations);
    let conditioned_current = completed_step.map(|aperture| aperture.returned);
    let relational_current = word
        .sparse_relational_current
        .as_ref()
        .map(|current| current.receipt.clone());
    Ok(ResidentQuadraticMomentReturn {
        factored_receiver_history,
        resident_current,
        conditioned_current,
        relational_current,
        receiver_coordinate_denominator: BigInt::one(),
        ports,
        port_returns,
        boundary_port_returns,
        entering_current: entering_current.clone(),
        total_returned_current,
        stored_difference,
        local_balance_closes,
        phase_locked_port_population,
        phase_front_is_unique: phase_locked_port_population == 1,
        situated_receiver_pairing: Some(situated_receiver_pairing),
        complete_successor_faces: (0..response_population)
            .filter(|face| {
                // The complete front is device-derived above and read only after the
                // resident successor has committed.  This older returned-current chart has
                // no addressed state axis, so its face index is its complete address.
                complete_native_successor_front_host[*face] != 0
            })
            .map(|face| face as u32)
            .collect(),
        complete_successor_face_population: if descend_boundary_state_receiver {
            resident_boundary
                .map(|boundary| boundary.boundary_states.len())
                .unwrap_or(1)
                .checked_mul(local_response_population)
                .ok_or(CudaRefineError::MembraneInteriorWordShape)?
        } else {
            response_population
        },
        active_factor_population: factors,
        native_factor_population: native_factors,
        moment_field_materialized: materialize_moment_field,
        moment_factorization_retained: true,
        context_population: context_count,
        restriction_population,
        generator_population: generator_count,
        device: word.card.device_name.clone(),
        context_identity: word.card.context as usize,
        launches: launches + continuation_launches,
        device_dependency_edges: launches + continuation_launches - 1,
        synchronizations: 1 + continuation_synchronizations,
        block_threads: word.card.block_x,
        mount_host_ingress_octets: word.mount_host_ingress_octets,
        successor_host_ingress_octets,
        successor_host_egress_octets,
        intermediate_host_egress_octets: 0,
        resident_invariant_octets: word.mount_host_ingress_octets,
        resident_working_octets,
        invariant_transport_reuploaded: false,
        cpu_semantic_replay_after_device: false,
    })
}

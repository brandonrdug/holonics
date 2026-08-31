use super::*;

use super::membrane_boundary_plan::{
    NativeSparseBoundaryAperture, NativeSparseRelationalReceiver, SituatedProjectiveDimensions,
};
use super::membrane_boundary_workspace::buffer_octets;

/// All state which crosses from the resident boundary launches into terminal image readback.
///
/// Device buffers are owned by this state rather than reduced to raw addresses.  That keeps the
/// complete launch/readback lifetime intact while the image completion mutates the resident
/// ecology and the exact exterior return is assembled.
pub(super) struct BoundaryReturnState<'a> {
    pub(super) interior: &'a mut ResidentMembraneInteriorWord,
    pub(super) address: &'a ResidentFactoredMomentReceiverAddress,
    pub(super) sparse_pair_completion: bool,
    pub(super) rooted_completion: bool,
    pub(super) entering_current: &'a ExactComplexWaveCurrent,
    pub(super) obstruction: Buffer,
    pub(super) port_action_sign: Buffer,
    pub(super) port_action_limbs: Buffer,
    pub(super) port_reflected_sign: Buffer,
    pub(super) port_reflected_limbs: Buffer,
    pub(super) port_receiver_sign: Buffer,
    pub(super) port_receiver_limbs: Buffer,
    pub(super) port_receiver_norm_sign: Buffer,
    pub(super) port_receiver_norm_limbs: Buffer,
    pub(super) port_real_sign: Buffer,
    pub(super) port_real_limbs: Buffer,
    pub(super) port_imaginary_sign: Buffer,
    pub(super) port_imaginary_limbs: Buffer,
    pub(super) phase_locked: Buffer,
    pub(super) situated_pairing_sign: Buffer,
    pub(super) situated_pairing_limbs: Buffer,
    pub(super) situated_pairing_front: Buffer,
    pub(super) complete_native_successor_front: Buffer,
    pub(super) situated_native_phase_front: Option<Buffer>,
    pub(super) projective_candidate_front: Option<Buffer>,
    pub(super) projective_interval_obstruction: Option<Buffer>,
    pub(super) situated_projective_norm_product: Option<Buffer>,
    pub(super) situated_projective_current_self: Option<Buffer>,
    pub(super) situated_projective_ingress_self: Option<Buffer>,
    pub(super) relational_projective_front: Option<Buffer>,
    pub(super) joint_real_sign: Buffer,
    pub(super) joint_real_limbs: Buffer,
    pub(super) joint_imaginary_sign: Buffer,
    pub(super) joint_imaginary_limbs: Buffer,
    pub(super) stored_real_sign: Buffer,
    pub(super) stored_real_limbs: Buffer,
    pub(super) stored_imaginary_sign: Buffer,
    pub(super) stored_imaginary_limbs: Buffer,
    pub(super) completed_relational_receiver: Option<ResidentSparseRelationalBoundaryReceiver>,
    pub(super) native_sparse_boundary: &'a NativeSparseBoundaryAperture,
    pub(super) native_sparse_relational_receiver: &'a NativeSparseRelationalReceiver,
    pub(super) situated_projective_dimensions: &'a SituatedProjectiveDimensions,
    pub(super) situated_face_source_states: &'a [u32],
    pub(super) situated_face_ports: &'a [u32],
    pub(super) situated_face_generators: &'a [u32],
    pub(super) receiver_denominator: &'a BigInt,
    pub(super) returned_denominator: &'a BigInt,
    pub(super) balance_denominator: &'a BigInt,
    pub(super) incoming_real_limbs: &'a [u32],
    pub(super) incoming_imaginary_limbs: &'a [u32],
    pub(super) port_population: usize,
    pub(super) support_count: usize,
    pub(super) family_count: usize,
    pub(super) opaque_receiver_count: usize,
    pub(super) generator_count: usize,
    pub(super) situated_population: usize,
    pub(super) support_family_population: usize,
    pub(super) support_receiver_population: usize,
    pub(super) port_family_population: usize,
    pub(super) port_receiver_population: usize,
    pub(super) component_population: usize,
    pub(super) phase_pair_population: usize,
    pub(super) overlap_limb_count: usize,
    pub(super) contact_limb_count: usize,
    pub(super) radiation_limb_count: usize,
    pub(super) compatibility_limb_count: usize,
    pub(super) norm_limb_count: usize,
    pub(super) square_limb_count: usize,
    pub(super) cross_limb_count: usize,
    pub(super) situated_pairing_limb_count: usize,
    pub(super) stored_limb_count: usize,
    pub(super) situated_pairing_workspace_octets: u64,
    pub(super) projective_interval_workspace_octets: u64,
    pub(super) situated_front_workspace_octets: u64,
    pub(super) projective_stream_workspace_octets: u64,
    pub(super) relational_projective_workspace_octets: u64,
    pub(super) projective_interval_launches: u64,
    pub(super) situated_front_launches: u64,
    pub(super) situated_formation_launches: u64,
    pub(super) projective_stream_launches: u64,
    pub(super) relational_projective_launches: u64,
}

pub(super) fn complete_boundary_return(
    state: BoundaryReturnState<'_>,
) -> Result<ResidentFactoredMomentBoundaryReturn, CudaRefineError> {
    let BoundaryReturnState {
        interior,
        address,
        sparse_pair_completion,
        rooted_completion,
        entering_current,
        obstruction,
        port_action_sign,
        port_action_limbs,
        port_reflected_sign,
        port_reflected_limbs,
        port_receiver_sign,
        port_receiver_limbs,
        port_receiver_norm_sign,
        port_receiver_norm_limbs,
        port_real_sign,
        port_real_limbs,
        port_imaginary_sign,
        port_imaginary_limbs,
        phase_locked,
        situated_pairing_sign,
        situated_pairing_limbs,
        situated_pairing_front,
        complete_native_successor_front,
        situated_native_phase_front,
        projective_candidate_front,
        projective_interval_obstruction,
        situated_projective_norm_product,
        situated_projective_current_self,
        situated_projective_ingress_self,
        relational_projective_front,
        joint_real_sign,
        joint_real_limbs,
        joint_imaginary_sign,
        joint_imaginary_limbs,
        stored_real_sign,
        stored_real_limbs,
        stored_imaginary_sign,
        stored_imaginary_limbs,
        completed_relational_receiver,
        native_sparse_boundary,
        native_sparse_relational_receiver,
        situated_projective_dimensions,
        situated_face_source_states,
        situated_face_ports,
        situated_face_generators,
        receiver_denominator,
        returned_denominator,
        balance_denominator,
        incoming_real_limbs,
        incoming_imaginary_limbs,
        port_population,
        support_count,
        family_count,
        opaque_receiver_count,
        generator_count,
        situated_population,
        support_family_population,
        support_receiver_population,
        port_family_population,
        port_receiver_population,
        component_population,
        phase_pair_population,
        overlap_limb_count,
        contact_limb_count,
        radiation_limb_count,
        compatibility_limb_count,
        norm_limb_count,
        square_limb_count,
        cross_limb_count,
        situated_pairing_limb_count,
        stored_limb_count,
        situated_pairing_workspace_octets,
        projective_interval_workspace_octets,
        situated_front_workspace_octets,
        projective_stream_workspace_octets,
        relational_projective_workspace_octets,
        projective_interval_launches,
        situated_front_launches,
        situated_formation_launches,
        projective_stream_launches,
        relational_projective_launches,
    } = state;

    // The ordinary image completion supplies the sole synchronization and atomically moves
    // the already-admitted target buffers. All boundary kernels above were queued before it;
    // its diagnostic coordinate read is therefore terminal testimony, never continuation.
    let image_return = if sparse_pair_completion {
        interior.complete_resident_sparse_quadratic_receivers(address)
    } else if rooted_completion {
        interior.complete_resident_factored_constitutive_spine_receivers(address)
    } else {
        interior.complete_resident_factored_moment_receivers(address)
    };
    let image = match image_return {
        Ok(image) => image,
        Err(error) => {
            if trace_configuration().holonics_phase_trace {
                eprintln!("mem6-image-boundary image-completion-refused: {error}");
            }
            return Err(error);
        }
    };
    if trace_configuration().holonics_phase_trace {
        eprintln!(
            "mem6-image-boundary image-completion-admitted generation={}",
            image.target_address.generation,
        );
    }

    let mut obstruction_host = [0_u32; 1];
    obstruction.read(&mut obstruction_host)?;
    let mut port_action_sign_host = vec![0_u8; port_family_population];
    let mut port_action_limbs_host = vec![0_u32; port_family_population * overlap_limb_count];
    let mut port_reflected_sign_host = vec![0_u8; port_family_population];
    let mut port_reflected_limbs_host = vec![0_u32; port_family_population * overlap_limb_count];
    let mut port_receiver_sign_host = vec![0_u8; port_receiver_population];
    let mut port_receiver_limbs_host = vec![0_u32; port_receiver_population * overlap_limb_count];
    let mut port_receiver_norm_sign_host = vec![0_u8; port_receiver_population];
    let mut port_receiver_norm_limbs_host =
        vec![0_u32; port_receiver_population * overlap_limb_count];
    let mut port_real_sign_host = vec![0_u8; port_population];
    let mut port_real_limbs_host = vec![0_u32; port_population * radiation_limb_count];
    let mut port_imaginary_sign_host = vec![0_u8; port_population];
    let mut port_imaginary_limbs_host = vec![0_u32; port_population * radiation_limb_count];
    let mut phase_locked_host = vec![0_u8; port_population];
    let mut situated_pairing_sign_host = vec![0_u8; situated_population];
    let mut situated_pairing_limbs_host =
        vec![0_u32; situated_population * situated_pairing_limb_count];
    let mut situated_pairing_front_host = vec![0_u8; situated_population];
    let mut complete_native_successor_front_host = vec![0_u8; situated_population];
    let mut situated_native_phase_front_host = situated_native_phase_front
        .as_ref()
        .map(|_| vec![0_u8; situated_population]);
    let mut projective_candidate_front_host = projective_candidate_front
        .as_ref()
        .map(|_| vec![0_u8; situated_population]);
    let mut projective_interval_obstruction_host = [0_u32; 1];
    let mut situated_projective_norm_product_host = situated_projective_dimensions
        .as_ref()
        .map(|(_, limb_count, _, _)| vec![0_u32; situated_population * *limb_count]);
    let mut situated_projective_current_self_host = situated_projective_dimensions
        .as_ref()
        .map(|_| vec![0_u32; situated_population * situated_pairing_limb_count]);
    let mut situated_projective_ingress_self_host = situated_projective_dimensions
        .as_ref()
        .map(|_| vec![0_u32; situated_population * situated_pairing_limb_count]);
    let mut relational_compatibility_sign_host = native_sparse_relational_receiver
        .as_ref()
        .map(|_| vec![0_u8; situated_population]);
    let mut relational_compatibility_limbs_host = native_sparse_relational_receiver
        .as_ref()
        .map(|(_, _, _, limb_count, _, _, _, _, _)| vec![0_u32; situated_population * *limb_count]);
    let mut relational_target_norm_limbs_host = native_sparse_relational_receiver
        .as_ref()
        .map(|(_, _, _, limb_count, _, _, _, _, _)| vec![0_u32; situated_population * *limb_count]);
    let mut relational_current_norm_limbs_host = native_sparse_relational_receiver
        .as_ref()
        .map(|(_, _, _, limb_count, _, _, _, _, _)| vec![0_u32; situated_population * *limb_count]);
    let mut joint_real_sign_host = [0_u8; 1];
    let mut joint_real_limbs_host = vec![0_u32; radiation_limb_count];
    let mut joint_imaginary_sign_host = [0_u8; 1];
    let mut joint_imaginary_limbs_host = vec![0_u32; radiation_limb_count];
    let mut stored_real_sign_host = [0_u8; 1];
    let mut stored_real_limbs_host = vec![0_u32; stored_limb_count];
    let mut stored_imaginary_sign_host = [0_u8; 1];
    let mut stored_imaginary_limbs_host = vec![0_u32; stored_limb_count];
    port_action_sign.read(&mut port_action_sign_host)?;
    port_action_limbs.read(&mut port_action_limbs_host)?;
    port_reflected_sign.read(&mut port_reflected_sign_host)?;
    port_reflected_limbs.read(&mut port_reflected_limbs_host)?;
    port_receiver_sign.read(&mut port_receiver_sign_host)?;
    port_receiver_limbs.read(&mut port_receiver_limbs_host)?;
    port_receiver_norm_sign.read(&mut port_receiver_norm_sign_host)?;
    port_receiver_norm_limbs.read(&mut port_receiver_norm_limbs_host)?;
    port_real_sign.read(&mut port_real_sign_host)?;
    port_real_limbs.read(&mut port_real_limbs_host)?;
    port_imaginary_sign.read(&mut port_imaginary_sign_host)?;
    port_imaginary_limbs.read(&mut port_imaginary_limbs_host)?;
    phase_locked.read(&mut phase_locked_host)?;
    situated_pairing_sign.read(&mut situated_pairing_sign_host)?;
    situated_pairing_limbs.read(&mut situated_pairing_limbs_host)?;
    if let Some(front) = relational_projective_front.as_ref() {
        front.read(&mut situated_pairing_front_host)?;
    } else {
        situated_pairing_front.read(&mut situated_pairing_front_host)?;
    }
    complete_native_successor_front.read(&mut complete_native_successor_front_host)?;
    if let (Some(device), Some(host)) = (
        situated_native_phase_front.as_ref(),
        situated_native_phase_front_host.as_mut(),
    ) {
        device.read(host)?;
    }
    if let (Some(device), Some(host)) = (
        projective_candidate_front.as_ref(),
        projective_candidate_front_host.as_mut(),
    ) {
        device.read(host)?;
    }
    if let Some(device) = projective_interval_obstruction.as_ref() {
        device.read(&mut projective_interval_obstruction_host)?;
    }
    if let (Some(device), Some(host)) = (
        situated_projective_norm_product.as_ref(),
        situated_projective_norm_product_host.as_mut(),
    ) {
        device.read(host)?;
    }
    if let (Some(device), Some(host)) = (
        situated_projective_current_self.as_ref(),
        situated_projective_current_self_host.as_mut(),
    ) {
        device.read(host)?;
    }
    if let (Some(device), Some(host)) = (
        situated_projective_ingress_self.as_ref(),
        situated_projective_ingress_self_host.as_mut(),
    ) {
        device.read(host)?;
    }
    if let (Some(native), Some(signs), Some(compatibility), Some(target_norm), Some(current_norm)) = (
        completed_relational_receiver.as_ref(),
        relational_compatibility_sign_host.as_mut(),
        relational_compatibility_limbs_host.as_mut(),
        relational_target_norm_limbs_host.as_mut(),
        relational_current_norm_limbs_host.as_mut(),
    ) {
        native.compatibility_signs.read(signs)?;
        native.compatibility_limbs.read(compatibility)?;
        native.transported_norm_limbs.read(target_norm)?;
        native.ingress_norm_limbs.read(current_norm)?;
    }
    joint_real_sign.read(&mut joint_real_sign_host)?;
    joint_real_limbs.read(&mut joint_real_limbs_host)?;
    joint_imaginary_sign.read(&mut joint_imaginary_sign_host)?;
    joint_imaginary_limbs.read(&mut joint_imaginary_limbs_host)?;
    stored_real_sign.read(&mut stored_real_sign_host)?;
    stored_real_limbs.read(&mut stored_real_limbs_host)?;
    stored_imaginary_sign.read(&mut stored_imaginary_sign_host)?;
    stored_imaginary_limbs.read(&mut stored_imaginary_limbs_host)?;
    if obstruction_host[0] != 0
        || port_action_sign_host.iter().any(|sign| *sign > 2)
        || port_reflected_sign_host.iter().any(|sign| *sign > 2)
        || port_receiver_sign_host.iter().any(|sign| *sign > 2)
        || port_receiver_norm_sign_host.iter().any(|sign| *sign > 1)
        || phase_locked_host.iter().any(|selected| *selected > 1)
        || situated_pairing_sign_host.iter().any(|sign| *sign > 2)
        || situated_pairing_front_host
            .iter()
            .any(|selected| *selected > 1)
        || complete_native_successor_front_host
            .iter()
            .any(|selected| *selected > 1)
        || projective_candidate_front_host
            .as_ref()
            .is_some_and(|front| front.iter().any(|selected| *selected > 1))
    {
        if trace_configuration().holonics_phase_trace {
            eprintln!(
                "mem6-image-boundary invalid-sign obstruction={} action={} reflected={} receiver={} norm={} phase={}",
                obstruction_host[0],
                port_action_sign_host.iter().copied().max().unwrap_or(0),
                port_reflected_sign_host.iter().copied().max().unwrap_or(0),
                port_receiver_sign_host.iter().copied().max().unwrap_or(0),
                port_receiver_norm_sign_host
                    .iter()
                    .copied()
                    .max()
                    .unwrap_or(0),
                phase_locked_host.iter().copied().max().unwrap_or(0),
            );
        }
        return Err(CudaRefineError::MembraneInteriorWordShape);
    }
    let phase_locked_port_population = phase_locked_host
        .iter()
        .filter(|selected| **selected != 0)
        .count();
    if phase_locked_port_population == 0 {
        if trace_configuration().holonics_phase_trace {
            eprintln!("mem6-image-boundary empty-phase-front");
        }
        return Err(CudaRefineError::MembraneInteriorWordShape);
    }
    let situated_receiver_front_faces = situated_pairing_front_host
        .iter()
        .enumerate()
        .filter_map(|(face, selected)| (*selected != 0).then_some(face as u32))
        .collect::<Vec<_>>();
    let complete_successor_faces = complete_native_successor_front_host
        .iter()
        .enumerate()
        .filter_map(|(face, present)| (*present != 0).then_some(face as u32))
        .collect::<Vec<_>>();
    let native_phase_front_faces = situated_native_phase_front_host
        .as_ref()
        .map(|front| {
            front
                .iter()
                .enumerate()
                .filter_map(|(face, selected)| (*selected != 0).then_some(face as u32))
                .collect::<Vec<_>>()
        })
        .unwrap_or_else(|| {
            (0..situated_population)
                .filter(|face| phase_locked_host[situated_face_ports[*face] as usize] != 0)
                .map(|face| face as u32)
                .collect::<Vec<_>>()
        });
    let projective_candidate_faces = projective_candidate_front_host
        .as_ref()
        .map(|front| {
            front
                .iter()
                .enumerate()
                .filter_map(|(face, selected)| (*selected != 0).then_some(face as u32))
                .collect::<Vec<_>>()
        })
        .unwrap_or_default();
    let situated_receiver_front_ports = situated_receiver_front_faces
        .iter()
        .map(|face| situated_face_ports[*face as usize])
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect::<Vec<_>>();
    if (sparse_pair_completion && complete_successor_faces.is_empty())
        || situated_receiver_front_faces.is_empty()
        || native_phase_front_faces.is_empty()
        || projective_candidate_front_host.as_ref().is_some_and(|_| {
            projective_candidate_faces.is_empty()
                || projective_candidate_faces
                    .iter()
                    .any(|face| !native_phase_front_faces.contains(face))
        })
        || situated_pairing_front_host
            .iter()
            .enumerate()
            .any(|(face, situated)| {
                *situated != 0 && !native_phase_front_faces.contains(&(face as u32))
            })
    {
        if trace_configuration().holonics_phase_trace {
            eprintln!(
                "mem6-image-boundary front-refused native={} interval={} exact={} interval-obstruction={} interval-subset={}",
                native_phase_front_faces.len(),
                projective_candidate_faces.len(),
                situated_receiver_front_faces.len(),
                projective_interval_obstruction_host[0],
                projective_candidate_faces
                    .iter()
                    .all(|face| native_phase_front_faces.contains(face)),
            );
        }
        return Err(CudaRefineError::MembraneInteriorWordShape);
    }
    let decode_integer = |sign: u8, limbs: &[u32]| -> Result<BigInt, CudaRefineError> {
        Ok(decode_component(sign, limbs, &BigInt::one())?
            .numer()
            .clone())
    };
    let situated_receiver_pairing_coordinates = (0..situated_population)
        .map(|face| {
            let begin = face * situated_pairing_limb_count;
            decode_integer(
                situated_pairing_sign_host[face],
                &situated_pairing_limbs_host[begin..begin + situated_pairing_limb_count],
            )
        })
        .collect::<Result<Vec<_>, _>>()?;
    let situated_receiver_squared_norm_products = match (
        situated_projective_dimensions.as_ref(),
        situated_projective_norm_product_host.as_ref(),
    ) {
        (Some((_, limb_count, _, _)), Some(products)) => (0..situated_population)
            .map(|face| {
                let begin = face * *limb_count;
                BigUint::new(products[begin..begin + *limb_count].to_vec())
            })
            .collect::<Vec<_>>(),
        _ => Vec::new(),
    };
    let decode_projective_self_pairings = |limbs: Option<&Vec<u32>>| {
        limbs
            .map(|coordinates| {
                (0..situated_population)
                    .map(|face| {
                        let begin = face * situated_pairing_limb_count;
                        BigUint::new(
                            coordinates[begin..begin + situated_pairing_limb_count].to_vec(),
                        )
                    })
                    .collect::<Vec<_>>()
            })
            .unwrap_or_default()
    };
    let situated_receiver_current_self_pairings =
        decode_projective_self_pairings(situated_projective_current_self_host.as_ref());
    let situated_receiver_ingress_self_pairings =
        decode_projective_self_pairings(situated_projective_ingress_self_host.as_ref());
    let relational_oriented_real_coordinates = match (
        native_sparse_relational_receiver.as_ref(),
        relational_compatibility_sign_host.as_ref(),
        relational_compatibility_limbs_host.as_ref(),
    ) {
        (Some((_, _, _, limb_count, _, _, _, _, _)), Some(signs), Some(limbs)) => (0
            ..situated_population)
            .map(|face| {
                let begin = face * *limb_count;
                decode_integer(signs[face], &limbs[begin..begin + *limb_count])
            })
            .collect::<Result<Vec<_>, _>>()?,
        _ => Vec::new(),
    };
    let relational_oriented_imaginary_coordinates = Vec::new();
    let relational_modulus_squared_coordinates = relational_oriented_real_coordinates
        .iter()
        .map(|coordinate| coordinate.magnitude() * coordinate.magnitude())
        .collect::<Vec<_>>();
    let decode_relational_norms =
        |limbs: Option<&Vec<u32>>| match (native_sparse_relational_receiver.as_ref(), limbs) {
            (Some((_, _, _, limb_count, _, _, _, _, _)), Some(coordinates)) => (0
                ..situated_population)
                .map(|face| {
                    let begin = face * *limb_count;
                    BigUint::new(coordinates[begin..begin + *limb_count].to_vec())
                })
                .collect::<Vec<_>>(),
            _ => Vec::new(),
        };
    let relational_target_self_pairings =
        decode_relational_norms(relational_target_norm_limbs_host.as_ref());
    let relational_current_self_pairings =
        decode_relational_norms(relational_current_norm_limbs_host.as_ref());
    let relational_squared_norm_products = relational_target_self_pairings
        .iter()
        .zip(&relational_current_self_pairings)
        .map(|(left, right)| left * right)
        .collect::<Vec<_>>();
    let mut ports = Vec::with_capacity(port_population);
    for port in 0..port_population {
        let family_begin = port * family_count;
        let receiver_begin = port * opaque_receiver_count;
        let decode_family = |signs: &[u8], limbs: &[u32]| {
            (family_begin..family_begin + family_count)
                .map(|at| {
                    let begin = at * overlap_limb_count;
                    decode_integer(signs[at], &limbs[begin..begin + overlap_limb_count])
                })
                .collect::<Result<Vec<_>, _>>()
        };
        ports.push(ResidentQuadraticMomentPortReturn {
            port: port as u32,
            moment: Vec::new(),
            reflected_family_overlaps: decode_family(
                &port_reflected_sign_host,
                &port_reflected_limbs_host,
            )?,
            family_overlaps: decode_family(&port_action_sign_host, &port_action_limbs_host)?,
            receiver_overlaps: (receiver_begin..receiver_begin + opaque_receiver_count)
                .map(|at| {
                    let begin = at * overlap_limb_count;
                    decode_integer(
                        port_receiver_sign_host[at],
                        &port_receiver_limbs_host[begin..begin + overlap_limb_count],
                    )
                })
                .collect::<Result<Vec<_>, _>>()?,
            receiver_action_norms: (receiver_begin..receiver_begin + opaque_receiver_count)
                .map(|at| {
                    let begin = at * overlap_limb_count;
                    BigUint::new(
                        port_receiver_norm_limbs_host[begin..begin + overlap_limb_count].to_vec(),
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
    let port_returns = (0..port_population)
        .map(|port| {
            let begin = port * radiation_limb_count;
            let end = begin + radiation_limb_count;
            let returned_response = decode_current(
                port_real_sign_host[port],
                &port_real_limbs_host[begin..end],
                port_imaginary_sign_host[port],
                &port_imaginary_limbs_host[begin..end],
                returned_denominator,
            )?;
            Ok(ResidentBoundaryChainPortReturn {
                port: port as u32,
                lies_in_joint_port_kernel: returned_response.is_zero(),
                lies_in_receiver_phase_front: phase_locked_host[port] != 0,
                returned_response,
            })
        })
        .collect::<Result<Vec<_>, CudaRefineError>>()?;
    let total_returned_current = decode_current(
        joint_real_sign_host[0],
        &joint_real_limbs_host,
        joint_imaginary_sign_host[0],
        &joint_imaginary_limbs_host,
        returned_denominator,
    )?;
    let stored_difference = decode_current(
        stored_real_sign_host[0],
        &stored_real_limbs_host,
        stored_imaginary_sign_host[0],
        &stored_imaginary_limbs_host,
        balance_denominator,
    )?;
    let local_balance_closes = stored_difference.add(&total_returned_current) == *entering_current;
    if !local_balance_closes
        || port_returns
            .iter()
            .fold(ExactComplexWaveCurrent::zero(), |total, returned| {
                total.add(&returned.returned_response)
            })
            != total_returned_current
    {
        if trace_configuration().holonics_phase_trace {
            eprintln!(
                "mem6-image-boundary balance-refused local={} ports={} total={:?} entering={:?}",
                local_balance_closes,
                port_returns.len(),
                total_returned_current,
                entering_current,
            );
        }
        return Err(CudaRefineError::MembraneInteriorCurrentOutsideApparatus);
    }
    let situated_receiver_pairing = ResidentSituatedReceiverPairingReturn {
        receiver_chart: if sparse_pair_completion {
            if native_sparse_relational_receiver.is_some() {
                "complete-native-pair-and-relational-projective-compatibility".to_owned()
            } else if native_sparse_boundary.is_some() {
                "complete-native-pair-projective-compatibility".to_owned()
            } else {
                "complete-native-ingress-quadratic-moment".to_owned()
            }
        } else {
            "exterior-complex-current".to_owned()
        },
        coordinate_denominator: if sparse_pair_completion {
            BigInt::one()
        } else {
            returned_denominator * balance_denominator
        },
        coordinates: situated_receiver_pairing_coordinates,
        current_self_pairings: situated_receiver_current_self_pairings,
        ingress_self_pairings: situated_receiver_ingress_self_pairings,
        squared_norm_products: situated_receiver_squared_norm_products,
        relational_oriented_real_coordinates,
        relational_oriented_imaginary_coordinates,
        relational_modulus_squared_coordinates,
        relational_target_self_pairings,
        relational_current_self_pairings,
        relational_squared_norm_products,
        face_source_states: situated_face_source_states.to_vec(),
        face_ports: situated_face_ports.to_vec(),
        face_generators: situated_face_generators.to_vec(),
        front_faces: situated_receiver_front_faces.clone(),
        front_is_unique: situated_receiver_front_faces.len() == 1,
        front_ports: situated_receiver_front_ports,
        native_phase_front_faces,
        projective_candidate_faces,
        projective_interval_limb_count: if projective_candidate_front_host.is_some() {
            26
        } else {
            0
        },
        projective_interval_obstruction_reopened_front: projective_interval_obstruction_host[0]
            != 0,
        complete_native_phase_front_retained: true,
        ingress_moment_reconstruction_fibre_retained: sparse_pair_completion,
    };
    let factored_receiver_history = interior.found_factored_receiver_history()?;
    let boundary_egress_octets = [
        std::mem::size_of_val(&obstruction_host),
        std::mem::size_of_val(port_action_sign_host.as_slice()),
        std::mem::size_of_val(port_action_limbs_host.as_slice()),
        std::mem::size_of_val(port_reflected_sign_host.as_slice()),
        std::mem::size_of_val(port_reflected_limbs_host.as_slice()),
        std::mem::size_of_val(port_receiver_sign_host.as_slice()),
        std::mem::size_of_val(port_receiver_limbs_host.as_slice()),
        std::mem::size_of_val(port_receiver_norm_sign_host.as_slice()),
        std::mem::size_of_val(port_receiver_norm_limbs_host.as_slice()),
        std::mem::size_of_val(port_real_sign_host.as_slice()),
        std::mem::size_of_val(port_real_limbs_host.as_slice()),
        std::mem::size_of_val(port_imaginary_sign_host.as_slice()),
        std::mem::size_of_val(port_imaginary_limbs_host.as_slice()),
        std::mem::size_of_val(phase_locked_host.as_slice()),
        std::mem::size_of_val(situated_pairing_sign_host.as_slice()),
        std::mem::size_of_val(situated_pairing_limbs_host.as_slice()),
        std::mem::size_of_val(situated_pairing_front_host.as_slice()),
        std::mem::size_of_val(&joint_real_sign_host),
        std::mem::size_of_val(joint_real_limbs_host.as_slice()),
        std::mem::size_of_val(&joint_imaginary_sign_host),
        std::mem::size_of_val(joint_imaginary_limbs_host.as_slice()),
        std::mem::size_of_val(&stored_real_sign_host),
        std::mem::size_of_val(stored_real_limbs_host.as_slice()),
        std::mem::size_of_val(&stored_imaginary_sign_host),
        std::mem::size_of_val(stored_imaginary_limbs_host.as_slice()),
    ]
    .into_iter()
    .try_fold(0_u64, |sum, octets| {
        sum.checked_add(u64::try_from(octets).ok()?)
    })
    .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
    let resident_working_octets = [
        buffer_octets(support_family_population, overlap_limb_count)? * 2,
        buffer_octets(support_receiver_population, overlap_limb_count)? * 2,
        buffer_octets(support_family_population, contact_limb_count)? * 2,
        buffer_octets(support_count, radiation_limb_count)? * 2,
        buffer_octets(port_population, radiation_limb_count)? * 2,
        buffer_octets(port_family_population, overlap_limb_count)? * 2,
        buffer_octets(port_receiver_population, overlap_limb_count)? * 2,
        buffer_octets(component_population, compatibility_limb_count)?,
        buffer_octets(component_population, norm_limb_count)?,
        buffer_octets(phase_pair_population, square_limb_count)?,
        buffer_octets(phase_pair_population, cross_limb_count)? * 2,
        port_population,
        buffer_octets(situated_population, situated_pairing_limb_count)? * 2,
        situated_population,
        buffer_octets(1, stored_limb_count)? * 3,
    ]
    .into_iter()
    .try_fold(0_u64, |sum, octets| {
        sum.checked_add(u64::try_from(octets).ok()?)
    })
    .and_then(|held| held.checked_add(situated_pairing_workspace_octets))
    .and_then(|held| held.checked_add(projective_interval_workspace_octets))
    .and_then(|held| held.checked_add(situated_front_workspace_octets))
    .and_then(|held| held.checked_add(projective_stream_workspace_octets))
    .and_then(|held| held.checked_add(relational_projective_workspace_octets))
    .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
    let boundary_launches = image
        .launches
        .checked_add(
            6_u64
                .saturating_add(projective_interval_launches)
                .saturating_add(situated_front_launches)
                .saturating_add(situated_formation_launches)
                .saturating_add(projective_stream_launches)
                .saturating_add(relational_projective_launches),
        )
        .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
    let boundary = ResidentQuadraticMomentReturn {
        factored_receiver_history,
        resident_current: None,
        conditioned_current: None,
        relational_current: None,
        receiver_coordinate_denominator: receiver_denominator.clone(),
        ports,
        port_returns,
        entering_current: entering_current.clone(),
        total_returned_current,
        stored_difference,
        local_balance_closes,
        phase_locked_port_population,
        phase_front_is_unique: phase_locked_port_population == 1,
        situated_receiver_pairing: Some(situated_receiver_pairing),
        complete_successor_faces,
        complete_successor_face_population: if sparse_pair_completion {
            situated_population
        } else {
            0
        },
        active_factor_population: image.target_address.image_population as usize,
        native_factor_population: interior.factors as usize,
        moment_field_materialized: false,
        moment_factorization_retained: true,
        context_population: image.target_address.image_population as usize,
        restriction_population: support_count,
        generator_population: generator_count,
        device: interior.card.device_name.clone(),
        context_identity: interior.card.context as usize,
        launches: boundary_launches,
        device_dependency_edges: boundary_launches.saturating_sub(1),
        synchronizations: image.synchronizations,
        block_threads: interior.card.block_x,
        mount_host_ingress_octets: interior.mount_host_ingress_octets,
        successor_host_ingress_octets: u64::try_from(
            2 * std::mem::size_of::<u8>()
                + std::mem::size_of_val(incoming_real_limbs)
                + std::mem::size_of_val(incoming_imaginary_limbs),
        )
        .map_err(|_| CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?,
        successor_host_egress_octets: boundary_egress_octets,
        intermediate_host_egress_octets: 0,
        resident_invariant_octets: interior.mount_host_ingress_octets,
        resident_working_octets,
        invariant_transport_reuploaded: false,
        cpu_semantic_replay_after_device: false,
    };
    Ok(ResidentFactoredMomentBoundaryReturn { image, boundary })
}

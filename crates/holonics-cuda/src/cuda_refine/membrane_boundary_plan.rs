use super::*;

/// The validated, receiver-specific aperture shared by the resident boundary phases.
///
/// This plan owns no device allocations. It carries only copied host metadata and resident
/// addresses, so workspace allocation and launch ordering remain explicit in later phases.
pub(super) struct BoundaryCompletionPlan {
    pub(super) port_population: usize,
    pub(super) support_count: usize,
    pub(super) primitive_receiver_count: usize,
    pub(super) family_count: usize,
    pub(super) opaque_receiver_count: usize,
    pub(super) generator_count: usize,
    pub(super) support_ports: Vec<u32>,
    pub(super) support_port_pointer: u64,
    pub(super) support_receiver_class_pointer: u64,
    pub(super) support_quadratic_scale_pointer: u64,
    pub(super) support_quadratic_scale_limb_count: usize,
    pub(super) maximal_support_quadratic_scale: BigUint,
    pub(super) receiver_output_population: usize,
    pub(super) receiver_limb_count: usize,
    pub(super) receiver_output_bound: BigUint,
    pub(super) receiver_denominator: BigInt,
    pub(super) receiver_sign_pointer: u64,
    pub(super) receiver_limbs_pointer: u64,
    pub(super) rooted_completion: bool,
    pub(super) sparse_pair_completion: bool,
    pub(super) native_sparse_boundary: NativeSparseBoundaryAperture,
    pub(super) native_sparse_situated_aperture: NativeSparseSituatedAperture,
    pub(super) native_sparse_relational_receiver: NativeSparseRelationalReceiver,
    pub(super) situated_population: usize,
    pub(super) situated_face_source_states: Vec<u32>,
    pub(super) situated_face_ports: Vec<u32>,
    pub(super) situated_face_generators: Vec<u32>,
    pub(super) sparse_situated_current: SparseSituatedCurrent,
    pub(super) support_family_population: usize,
    pub(super) support_receiver_population: usize,
    pub(super) port_family_population: usize,
    pub(super) port_receiver_population: usize,
    pub(super) component_count: usize,
    pub(super) component_population: usize,
    pub(super) phase_pair_population: usize,
    pub(super) situated_pair_population: usize,
    pub(super) overlap_limb_count: usize,
    pub(super) contact_limb_count: usize,
    pub(super) radiation_limb_count: usize,
    pub(super) compatibility_limb_count: usize,
    pub(super) norm_limb_count: usize,
    pub(super) square_limb_count: usize,
    pub(super) cross_limb_count: usize,
    pub(super) returned_denominator: BigInt,
    pub(super) balance_denominator: BigInt,
    pub(super) joint_scale: u64,
    pub(super) incoming_real_bound: BigInt,
    pub(super) incoming_imaginary_bound: BigInt,
    pub(super) situated_pairing_limb_count: usize,
    pub(super) situated_projective_dimensions: SituatedProjectiveDimensions,
    pub(super) relational_projective_dimensions: RelationalProjectiveDimensions,
    pub(super) stored_limb_count: usize,
    pub(super) incoming_real_sign: u8,
    pub(super) incoming_real_limbs: Vec<u32>,
    pub(super) incoming_imaginary_sign: u8,
    pub(super) incoming_imaginary_limbs: Vec<u32>,
}

pub(super) type NativeSparseBoundaryAperture = Option<(
    u64,
    u64,
    usize,
    BigUint,
    u64,
    BigUint,
    u64,
    BigUint,
    u64,
    u64,
)>;
pub(super) type NativeSparseSituatedAperture = Option<(
    usize,
    usize,
    usize,
    u64,
    u64,
    usize,
    u64,
    usize,
    u64,
    u64,
    usize,
    u64,
    u64,
    u64,
    u64,
    usize,
)>;
pub(super) type NativeSparseRelationalReceiver =
    Option<(String, u64, u64, usize, BigUint, u64, BigUint, u64, BigUint)>;
pub(super) type SparseSituatedCurrent = Option<(
    usize,
    u64,
    u64,
    usize,
    BigUint,
    u64,
    usize,
    BigUint,
    u64,
    usize,
    BigUint,
)>;
pub(super) type SituatedProjectiveDimensions = Option<(BigUint, usize, usize, usize)>;
pub(super) type RelationalProjectiveDimensions = Option<(usize, usize, usize)>;

pub(super) fn prepare_boundary_completion(
    word: &ResidentMembraneInteriorWord,
    address: &ResidentFactoredMomentReceiverAddress,
    port_population: usize,
    entering_current: &ExactComplexWaveCurrent,
) -> Result<BoundaryCompletionPlan, CudaRefineError> {
    let live_address = word.resident_factored_moment_receiver_address()?;
    if trace_configuration().holonics_phase_trace {
        eprintln!(
            "uar2-boundary-completion-enter address-matches={} ports={} entering-zero={}",
            &live_address == address,
            port_population,
            entering_current.is_zero(),
        );
    }
    if &live_address != address
        || port_population == 0
        || port_population > u32::MAX as usize
        || entering_current.is_zero()
    {
        return Err(CudaRefineError::MembraneInteriorWordShape);
    }
    let (
        support_count,
        primitive_receiver_count,
        family_count,
        opaque_receiver_count,
        generator_count,
        support_ports,
        support_port_pointer,
        support_receiver_class_pointer,
        support_quadratic_scale_pointer,
        support_quadratic_scale_limb_count,
        maximal_support_quadratic_scale,
        receiver_output_population,
        receiver_limb_count,
        receiver_output_bound,
        receiver_denominator,
        receiver_sign_pointer,
        receiver_limbs_pointer,
        rooted_completion,
        sparse_pair_completion,
        native_sparse_boundary,
    ) = {
        let transport = word
            .factored_receiver_history
            .as_ref()
            .and_then(|mount| mount.transported_image.as_ref())
            .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
        let descended_receiver = transport
            .rank_atlas
            .as_ref()
            .and_then(|atlas| atlas.coordinates.as_ref())
            .and_then(|coordinates| coordinates.candidate.as_ref())
            .and_then(|candidate| candidate.receiver.as_ref());
        let (receiver, rooted_completion) =
            match (descended_receiver, transport.productive_receiver.as_ref()) {
                (Some(receiver), None) => (receiver, false),
                (None, Some(receiver)) => (receiver, true),
                _ => return Err(CudaRefineError::MembraneInteriorWordShape),
            };
        if let Some(native) = transport.sparse_native_boundary.as_ref() {
            if !transport.sparse_pair_completion
                || native.identity_sha256 != receiver.frame_identity_sha256
                || native.port_population as usize != port_population
            {
                return Err(CudaRefineError::MembraneInteriorWordShape);
            }
            (
                native.face_population as usize,
                native.face_population as usize,
                word.families as usize,
                word.receiver_count as usize,
                transport.generator_population as usize,
                native.support_ports_host.clone(),
                native.support_ports.pointer,
                native.support_receiver_classes.pointer,
                native.support_quadratic_scales.pointer,
                1,
                BigUint::one(),
                receiver.receiver_population as usize,
                receiver.output_limb_count as usize,
                receiver.output_bound.clone(),
                receiver
                    .output_denominator
                    .clone()
                    .ok_or(CudaRefineError::MembraneInteriorWordShape)?,
                receiver.output_signs.pointer,
                receiver.output_limbs.pointer,
                rooted_completion,
                transport.sparse_pair_completion,
                Some((
                    native.situated_signs.pointer,
                    native.situated_limbs.pointer,
                    native.situated_limb_count as usize,
                    native.situated_bound.clone(),
                    native.situated_current_norm_limbs.pointer,
                    native.situated_current_norm_bound.clone(),
                    native.situated_ingress_norm_limbs.pointer,
                    native.situated_ingress_norm_bound.clone(),
                    native.resident_octets,
                    native.working_octets,
                )),
            )
        } else {
            let frame = word
                .addressed_factored_receiver_frame
                .as_ref()
                .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
            if frame.identity_sha256 != receiver.frame_identity_sha256 {
                return Err(CudaRefineError::MembraneInteriorWordShape);
            }
            (
                frame.support_count as usize,
                frame.occurrence_count as usize,
                frame.family_count as usize,
                frame.opaque_receiver_count as usize,
                frame.generator_count as usize,
                frame.occurrence_ports_host.clone(),
                frame.occurrence_ports.pointer,
                frame.support_receiver_classes.pointer,
                frame.support_quadratic_scale_limbs.pointer,
                frame.support_quadratic_scale_limb_count as usize,
                frame.maximal_support_quadratic_scale.clone(),
                receiver.receiver_population as usize,
                receiver.output_limb_count as usize,
                receiver.output_bound.clone(),
                receiver
                    .output_denominator
                    .clone()
                    .ok_or(CudaRefineError::MembraneInteriorWordShape)?,
                receiver.output_signs.pointer,
                receiver.output_limbs.pointer,
                rooted_completion,
                transport.sparse_pair_completion,
                None,
            )
        }
    };
    // The situated receiver is deliberately staged after the native phase quotient.  This
    // view carries only resident addresses into that later launch; it does not reconstruct a
    // host section or collapse the `(port,generator)` occurrence axis.
    let native_sparse_situated_aperture = if native_sparse_boundary.is_some() {
        let mount = word
            .factored_receiver_history
            .as_ref()
            .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
        let source = mount
            .sparse_pair
            .as_ref()
            .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
        let transport = mount
            .transported_image
            .as_ref()
            .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
        let native = transport
            .sparse_native_boundary
            .as_ref()
            .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
        Some((
            source.state_population as usize,
            native.port_population as usize,
            source.pair_population as usize,
            source.pair_factors.pointer,
            transport.limbs.pointer,
            transport.numerator_limb_count as usize,
            source.situated_receiver_coefficients.pointer,
            source.situated_receiver_limb_count as usize,
            native.restrictions.pointer,
            native.restriction_present.pointer,
            native.restriction_limb_count as usize,
            native.situated_signs.pointer,
            native.situated_limbs.pointer,
            native.situated_current_norm_limbs.pointer,
            native.situated_ingress_norm_limbs.pointer,
            native.situated_limb_count as usize,
        ))
    } else {
        None
    };
    let native_sparse_relational_receiver = word
        .factored_receiver_history
        .as_ref()
        .and_then(|mount| mount.transported_image.as_ref())
        .and_then(|transport| transport.sparse_native_boundary.as_ref())
        .and_then(|native| native.relational_receiver.as_ref())
        .map(|receiver| {
            (
                receiver.identity_sha256.clone(),
                receiver.compatibility_signs.pointer,
                receiver.compatibility_limbs.pointer,
                receiver.limb_count as usize,
                receiver.compatibility_bound.clone(),
                receiver.transported_norm_limbs.pointer,
                receiver.transported_norm_bound.clone(),
                receiver.ingress_norm_limbs.pointer,
                receiver.ingress_norm_bound.clone(),
            )
        });
    let (
        situated_population,
        situated_face_source_states,
        situated_face_ports,
        situated_face_generators,
    ) = word
        .factored_receiver_history
        .as_ref()
        .and_then(|mount| mount.transported_image.as_ref())
        .and_then(|transport| transport.sparse_native_boundary.as_ref())
        .map(|native| {
            (
                native.face_population as usize,
                native.face_source_states_host.clone(),
                native.face_ports_host.clone(),
                native.face_generators_host.clone(),
            )
        })
        .unwrap_or_else(|| {
            (
                port_population,
                vec![u32::MAX; port_population],
                (0..port_population as u32).collect(),
                vec![0_u32; port_population],
            )
        });
    if situated_population == 0
        || situated_face_source_states.len() != situated_population
        || situated_face_ports.len() != situated_population
        || situated_face_generators.len() != situated_population
    {
        return Err(CudaRefineError::MembraneInteriorWordShape);
    }
    let sparse_situated_current = if sparse_pair_completion && native_sparse_boundary.is_none() {
        let mount = word
            .factored_receiver_history
            .as_ref()
            .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
        let source = mount
            .sparse_pair
            .as_ref()
            .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
        let transport = mount
            .transported_image
            .as_ref()
            .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
        let conditioner = word
            .addressed_factored_receiver_frame
            .as_ref()
            .and_then(|frame| frame.sparse_pair_boundary_conditioners.as_ref())
            .ok_or(CudaRefineError::MembraneInteriorWordShape)?;
        if source.pair_population != transport.transported_row_population
            || source.factor_population != transport.factor_population
            || conditioner.port_population as usize != port_population
            || conditioner.factor_population != source.factor_population
        {
            return Err(CudaRefineError::MembraneInteriorWordShape);
        }
        Some((
            source.pair_population as usize,
            source.pair_factors.pointer,
            transport.limbs.pointer,
            transport.numerator_limb_count as usize,
            transport.maximal_numerator.magnitude().clone(),
            source.situated_receiver_coefficients.pointer,
            source.situated_receiver_limb_count as usize,
            source.maximal_situated_receiver_coefficient.clone(),
            conditioner.coefficients.pointer,
            conditioner.coefficient_limb_count as usize,
            conditioner.maximal_coefficient.clone(),
        ))
    } else {
        None
    };
    let receiver_stride = family_count
        .checked_mul(2)
        .and_then(|held| held.checked_add(opaque_receiver_count.checked_mul(2)?))
        .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
    if support_count == 0
        || family_count != word.families as usize
        || opaque_receiver_count != word.receiver_count as usize
        || generator_count == 0
        || primitive_receiver_count == 0
        || support_ports.len() != support_count
        || support_ports
            .iter()
            .any(|port| *port as usize >= port_population)
        || support_ports.iter().copied().collect::<BTreeSet<_>>().len() != port_population
        || receiver_output_population
            != primitive_receiver_count
                .checked_mul(receiver_stride)
                .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?
        || receiver_limb_count == 0
        || support_quadratic_scale_limb_count == 0
        || receiver_denominator <= BigInt::zero()
        || native_sparse_boundary.as_ref().is_some_and(
            |(
                signs,
                limbs,
                limb_count,
                bound,
                current_norm,
                current_norm_bound,
                ingress_norm,
                ingress_norm_bound,
                _,
                _,
            )| {
                *signs == 0
                    || *limbs == 0
                    || *limb_count == 0
                    || bound.is_zero()
                    || *current_norm == 0
                    || current_norm_bound.is_zero()
                    || *ingress_norm == 0
                    || ingress_norm_bound.is_zero()
            },
        )
        || sparse_situated_current.as_ref().is_some_and(
            |(
                pairs,
                pair_factors,
                current,
                current_limbs,
                current_maximum,
                ingress,
                ingress_limbs,
                ingress_maximum,
                restriction,
                restriction_limbs,
                restriction_maximum,
            )| {
                *pairs == 0
                    || *pair_factors == 0
                    || *current == 0
                    || *current_limbs == 0
                    || current_maximum.is_zero()
                    || *ingress == 0
                    || *ingress_limbs == 0
                    || ingress_maximum.is_zero()
                    || *restriction == 0
                    || *restriction_limbs == 0
                    || restriction_maximum.is_zero()
            },
        )
    {
        return Err(CudaRefineError::MembraneInteriorWordShape);
    }
    if trace_configuration().holonics_phase_trace {
        eprintln!(
            "uar2-boundary-shape-admitted supports={} primitive-receivers={} situated={} receiver-outputs={} limb-count={}",
            support_count,
            primitive_receiver_count,
            situated_population,
            receiver_output_population,
            receiver_limb_count,
        );
    }

    let support_family_population = support_count
        .checked_mul(family_count)
        .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
    let support_receiver_population = support_count
        .checked_mul(opaque_receiver_count)
        .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
    let port_family_population = port_population
        .checked_mul(family_count)
        .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
    let port_receiver_population = port_population
        .checked_mul(opaque_receiver_count)
        .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
    let component_count = family_count
        .checked_add(opaque_receiver_count)
        .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
    let component_population = port_population
        .checked_mul(component_count)
        .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
    let phase_pair_population = port_population
        .checked_mul(port_population)
        .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
    let situated_pair_population = situated_population
        .checked_mul(situated_population)
        .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
    let scaled_receiver_output_bound = &receiver_output_bound * &maximal_support_quadratic_scale;
    let port_overlap_bound = &scaled_receiver_output_bound * BigUint::from(support_count);
    let overlap_limb_count = port_overlap_bound
        .to_u32_digits()
        .len()
        .max(1)
        .saturating_add(2);
    let contact_bound = &scaled_receiver_output_bound * word.maximal_family_numerator.magnitude();
    let contact_limb_count = contact_bound.to_u32_digits().len().max(1).saturating_add(1);
    let radiation_bound =
        &contact_bound * BigUint::from(family_count) * BigUint::from(support_count);
    let radiation_limb_count = radiation_bound
        .to_u32_digits()
        .len()
        .max(1)
        .saturating_add(1);
    let phase_component_bound =
        (&port_overlap_bound * &port_overlap_bound).max(port_overlap_bound.clone());
    let compatibility_limb_count = phase_component_bound
        .to_u32_digits()
        .len()
        .max(1)
        .saturating_add(2);
    let norm_limb_count = compatibility_limb_count;
    let square_limb_count = compatibility_limb_count
        .checked_mul(2)
        .and_then(|limbs| limbs.checked_add(1))
        .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
    let cross_limb_count = square_limb_count
        .checked_add(norm_limb_count)
        .and_then(|limbs| limbs.checked_add(1))
        .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
    for extent in [
        overlap_limb_count,
        contact_limb_count,
        radiation_limb_count,
        compatibility_limb_count,
        norm_limb_count,
        square_limb_count,
        cross_limb_count,
    ] {
        if extent > u32::MAX as usize {
            return Err(CudaRefineError::MembraneInteriorCurrentOutsideApparatus);
        }
    }

    let returned_denominator = &receiver_denominator * &word.family_common_denominator;
    let incoming_denominator = lcm_positive(
        entering_current.real.denom().clone(),
        entering_current.imaginary.denom(),
    );
    let balance_denominator = lcm_positive(returned_denominator.clone(), &incoming_denominator);
    let joint_scale = (&balance_denominator / &returned_denominator)
        .to_u64()
        .ok_or(CudaRefineError::MembraneInteriorCurrentOutsideApparatus)?;
    let incoming_real_bound = (entering_current.real.numer()
        * (&balance_denominator / entering_current.real.denom()))
    .abs();
    let incoming_imaginary_bound = (entering_current.imaginary.numer()
        * (&balance_denominator / entering_current.imaginary.denom()))
    .abs();
    let (_situated_pairing_bound, situated_pairing_limb_count) =
        if let Some((_, _, limb_count, bound, _, _, _, _, _, _)) = &native_sparse_boundary {
            (BigInt::from(bound.clone()), *limb_count)
        } else if let Some((
            pair_population,
            _,
            _,
            _,
            maximal_current,
            _,
            _,
            maximal_ingress,
            _,
            _,
            maximal_restriction,
        )) = &sparse_situated_current
        {
            let bound = BigInt::from(
                maximal_current
                    * maximal_ingress
                    * maximal_restriction
                    * maximal_restriction
                    * BigUint::from(2_u8)
                    * BigUint::from(*pair_population),
            );
            let (_, digits) = bound.to_u32_digits();
            (bound, digits.len().max(1).saturating_add(1))
        } else {
            let bound = BigInt::from(radiation_bound.clone())
                * (&incoming_real_bound + &incoming_imaginary_bound);
            let (_, digits) = bound.to_u32_digits();
            (bound, digits.len().max(1).saturating_add(1))
        };
    let situated_projective_dimensions = native_sparse_boundary.as_ref().map(
        |(_, _, _, cross_bound, _, current_norm_bound, _, ingress_norm_bound, _, _)| {
            let norm_product_bound = current_norm_bound * ingress_norm_bound;
            let square_bound = cross_bound * cross_bound;
            let cross_product_bound = &square_bound * &norm_product_bound;
            let norm_product_limb_count = norm_product_bound
                .to_u32_digits()
                .len()
                .max(1)
                .saturating_add(1);
            let projective_square_limb_count =
                square_bound.to_u32_digits().len().max(1).saturating_add(1);
            let projective_cross_limb_count = cross_product_bound
                .to_u32_digits()
                .len()
                .max(1)
                .saturating_add(1);
            (
                norm_product_bound,
                norm_product_limb_count,
                projective_square_limb_count,
                projective_cross_limb_count,
            )
        },
    );
    let relational_projective_dimensions = native_sparse_relational_receiver.as_ref().map(
        |(_, _, _, _, compatibility_bound, _, transported_norm_bound, _, ingress_norm_bound)| {
            let norm_product_bound = transported_norm_bound * ingress_norm_bound;
            let square_bound = compatibility_bound * compatibility_bound;
            let cross_bound = &square_bound * &norm_product_bound;
            (
                norm_product_bound
                    .to_u32_digits()
                    .len()
                    .max(1)
                    .saturating_add(1),
                square_bound.to_u32_digits().len().max(1).saturating_add(1),
                cross_bound.to_u32_digits().len().max(1).saturating_add(1),
            )
        },
    );
    if situated_projective_dimensions.as_ref().is_some_and(
        |(_, norm_product_limbs, projective_square_limbs, projective_cross_limbs)| {
            *norm_product_limbs > u32::MAX as usize
                || *projective_square_limbs > u32::MAX as usize
                || *projective_cross_limbs > u32::MAX as usize
        },
    ) {
        return Err(CudaRefineError::MembraneInteriorCurrentOutsideApparatus);
    }
    if relational_projective_dimensions.as_ref().is_some_and(
        |(norm_product_limbs, square_limbs, cross_limbs)| {
            *norm_product_limbs > u32::MAX as usize
                || *square_limbs > u32::MAX as usize
                || *cross_limbs > u32::MAX as usize
        },
    ) {
        return Err(CudaRefineError::MembraneInteriorCurrentOutsideApparatus);
    }
    let stored_bound = incoming_real_bound
        .clone()
        .max(incoming_imaginary_bound.clone())
        + BigInt::from(radiation_bound.clone()) * BigInt::from(joint_scale);
    let (_, stored_digits) = stored_bound.to_u32_digits();
    let stored_limb_count = stored_digits.len().max(2).saturating_add(1);
    if stored_limb_count > u32::MAX as usize || situated_pairing_limb_count > u32::MAX as usize {
        return Err(CudaRefineError::MembraneInteriorCurrentOutsideApparatus);
    }
    let (incoming_real_sign, incoming_real_limbs) = encode_component(
        &entering_current.real,
        &balance_denominator,
        stored_limb_count,
    )?;
    let (incoming_imaginary_sign, incoming_imaginary_limbs) = encode_component(
        &entering_current.imaginary,
        &balance_denominator,
        stored_limb_count,
    )?;
    if trace_configuration().holonics_phase_trace {
        eprintln!(
            "uar2-boundary-scale-admitted overlap-limbs={} radiation-limbs={} situated-limbs={} stored-limbs={} situated-pairs={}",
            overlap_limb_count,
            radiation_limb_count,
            situated_pairing_limb_count,
            stored_limb_count,
            situated_pair_population,
        );
    }
    Ok(BoundaryCompletionPlan {
        port_population,
        support_count,
        primitive_receiver_count,
        family_count,
        opaque_receiver_count,
        generator_count,
        support_ports,
        support_port_pointer,
        support_receiver_class_pointer,
        support_quadratic_scale_pointer,
        support_quadratic_scale_limb_count,
        maximal_support_quadratic_scale,
        receiver_output_population,
        receiver_limb_count,
        receiver_output_bound,
        receiver_denominator,
        receiver_sign_pointer,
        receiver_limbs_pointer,
        rooted_completion,
        sparse_pair_completion,
        native_sparse_boundary,
        native_sparse_situated_aperture,
        native_sparse_relational_receiver,
        situated_population,
        situated_face_source_states,
        situated_face_ports,
        situated_face_generators,
        sparse_situated_current,
        support_family_population,
        support_receiver_population,
        port_family_population,
        port_receiver_population,
        component_count,
        component_population,
        phase_pair_population,
        situated_pair_population,
        overlap_limb_count,
        contact_limb_count,
        radiation_limb_count,
        compatibility_limb_count,
        norm_limb_count,
        square_limb_count,
        cross_limb_count,
        returned_denominator,
        balance_denominator,
        joint_scale,
        incoming_real_bound,
        incoming_imaginary_bound,
        situated_pairing_limb_count,
        situated_projective_dimensions,
        relational_projective_dimensions,
        stored_limb_count,
        incoming_real_sign,
        incoming_real_limbs,
        incoming_imaginary_sign,
        incoming_imaginary_limbs,
    })
}

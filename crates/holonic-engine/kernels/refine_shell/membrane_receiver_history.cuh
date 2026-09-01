// Membrane receiver and history transport.
// This fragment is included by refine_shell.cu after refine_shared.cuh.

extern "C" __global__ void contract_membrane_factorized_quadratic_moments(
    const uint32_t *context_current_limbs,
    const uint32_t *context_weight_limbs,
    const uint8_t *context_state_present,
    const uint32_t *context_states,
    const uint32_t *restriction_current_limbs,
    const uint32_t *boundary_states,
    const uint32_t *generator_targets,
    const uint32_t *receiver_class_bases,
    const uint64_t *source_class_factor_offsets,
    const uint32_t *source_class_factors,
    const uint64_t *generator_class_factor_offsets,
    const uint32_t *generator_class_factors,
    const uint64_t *factor_capacity,
    const int8_t *family_orientation,
    uint8_t *action_overlap_sign,
    uint32_t *action_overlap_limbs,
    uint8_t *reflected_overlap_sign,
    uint32_t *reflected_overlap_limbs,
    uint8_t *receiver_overlap_sign,
    uint32_t *receiver_overlap_limbs,
    uint8_t *receiver_action_norm_sign,
    uint32_t *receiver_action_norm_limbs,
    uint32_t *left_scratch,
    uint32_t *right_scratch,
    uint32_t *bucket_scratch,
    uint32_t *quadratic_scratch,
    uint32_t *term_scratch,
    uint32_t *overlap_scratch,
    uint32_t context_count,
    uint32_t restriction_count,
    uint32_t port_count,
    uint32_t factor_count,
    uint32_t generator_count,
    uint32_t family_count,
    uint32_t receiver_count,
    uint32_t context_chunk_count,
    uint32_t context_chunk_size,
    uint32_t incidence_chunk_count,
    uint32_t incidence_chunk_size,
    uint32_t selected_context_chunk,
    uint32_t selected_incidence_chunk,
    uint32_t context_limb_count,
    uint32_t restriction_limb_count,
    uint32_t weight_limb_count,
    uint32_t product_limb_count,
    uint32_t quadratic_limb_count,
    uint32_t moment_limb_count,
    uint32_t overlap_limb_count,
    uint32_t resident_rectangular_restrictions,
    uint32_t resident_boundary_state_count)
{
    const uint64_t at = (uint64_t)blockIdx.x * blockDim.x + threadIdx.x;
    const uint32_t axis_count = family_count > receiver_count ? family_count : receiver_count;
    const uint64_t section_count =
        (uint64_t)restriction_count * (uint64_t)generator_count
        * (uint64_t)axis_count;
    const uint64_t work = section_count;
    if (at >= work || context_chunk_count == 0U || context_chunk_size == 0U
        || incidence_chunk_count == 0U || incidence_chunk_size == 0U
        || selected_context_chunk >= context_chunk_count
        || selected_incidence_chunk >= incidence_chunk_count) return;
    const uint32_t incidence_chunk = selected_incidence_chunk;
    const uint32_t context_chunk = selected_context_chunk;
    const uint64_t section = at;
    const uint32_t generator = (section / axis_count) % generator_count;
    const uint32_t restriction = section / (axis_count * generator_count);
    const uint32_t axis = section % axis_count;
    const uint64_t product_at = at * (uint64_t)product_limb_count;
    const uint64_t quadratic_at = at * (uint64_t)quadratic_limb_count;
    const uint64_t moment_at = at * (uint64_t)moment_limb_count;
    const uint64_t overlap_at_scratch = at * (uint64_t)overlap_limb_count;

    uint8_t *axis_sign = 0;
    uint32_t *axis_limbs = 0;
    uint8_t *axis_norm_sign = 0;
    uint32_t *axis_norm_limbs = 0;
    const uint64_t output = at;
    const uint64_t output_at = output * (uint64_t)overlap_limb_count;
    if (axis < receiver_count) {
        axis_sign = receiver_overlap_sign + output;
        axis_limbs = receiver_overlap_limbs + output_at;
        axis_norm_sign = receiver_action_norm_sign + output;
        axis_norm_limbs = receiver_action_norm_limbs + output_at;
        *axis_sign = 0U;
        *axis_norm_sign = 0U;
        zero_unsigned_limbs(axis_limbs, overlap_limb_count);
        zero_unsigned_limbs(axis_norm_limbs, overlap_limb_count);
    }
    if (axis < family_count) {
        action_overlap_sign[output] = 0U;
        reflected_overlap_sign[output] = 0U;
        zero_unsigned_limbs(action_overlap_limbs + output_at, overlap_limb_count);
        zero_unsigned_limbs(reflected_overlap_limbs + output_at, overlap_limb_count);
    }

    // Contexts are the retained rank-one summands.  Each lane owns one apparatus-derived
    // contiguous context interval of one restriction/generator/receiver section.  The later
    // reduction visits those intervals in address order, so this parallel cover is exactly the
    // same ordered finite sum without forcing one lane to serialize the complete history.
    const uint64_t context_begin =
        (uint64_t)context_chunk * (uint64_t)context_chunk_size;
    uint64_t context_end = context_begin + context_chunk_size;
    if (context_end > context_count) context_end = context_count;
    for (uint64_t context64 = context_begin; context64 < context_end; ++context64) {
        const uint32_t context = (uint32_t)context64;
        if (resident_rectangular_restrictions != 0U) {
            if (resident_boundary_state_count == 0U
                || context_state_present[context] == 0U
                || context_states[context]
                    != boundary_states[restriction % resident_boundary_state_count]) continue;
        }
        const uint64_t weight_at = (uint64_t)context * (uint64_t)weight_limb_count;
            const uint64_t source_begin =
                (uint64_t)incidence_chunk * (uint64_t)incidence_chunk_size;
            uint64_t source_end = source_begin + incidence_chunk_size;
            if (source_end > factor_count) source_end = factor_count;
            for (uint64_t source64 = source_begin; source64 < source_end; ++source64) {
                const uint32_t source = (uint32_t)source64;
                const uint64_t context_source =
                    ((uint64_t)context * (uint64_t)factor_count + source)
                        * (uint64_t)context_limb_count;
                const uint64_t restriction_source =
                    ((uint64_t)restriction * (uint64_t)factor_count + source)
                        * (uint64_t)restriction_limb_count;
                multiply_unsigned_limbs(
                    context_current_limbs + context_source, context_limb_count,
                    restriction_current_limbs + restriction_source, restriction_limb_count,
                    left_scratch + product_at, product_limb_count);
                if (unsigned_limbs_are_zero(
                        left_scratch + product_at, product_limb_count)) continue;
                multiply_unsigned_limbs(
                    left_scratch + product_at, product_limb_count,
                    left_scratch + product_at, product_limb_count,
                    quadratic_scratch + quadratic_at, quadratic_limb_count);
                multiply_unsigned_limbs(
                    quadratic_scratch + quadratic_at, quadratic_limb_count,
                    context_weight_limbs + weight_at, weight_limb_count,
                    term_scratch + moment_at, moment_limb_count);

                if (axis < family_count) {
                    const int8_t orientation = family_orientation[
                        (uint64_t)axis * (uint64_t)factor_count + source];
                    const uint8_t orientation_sign = orientation < 0
                        ? 2U : (orientation > 0 ? 1U : 0U);
                    if (orientation_sign != 0U) {
                        scale_unsigned_limbs(
                            term_scratch + moment_at, moment_limb_count,
                            factor_capacity[source], overlap_scratch + overlap_at_scratch,
                            overlap_limb_count);
                        add_signed_magnitude(
                            reflected_overlap_sign + output,
                            reflected_overlap_limbs + output_at,
                            orientation_sign,
                            overlap_scratch + overlap_at_scratch,
                            overlap_limb_count);
                        add_signed_magnitude(
                            action_overlap_sign + output,
                            action_overlap_limbs + output_at,
                            opposite_sign(orientation_sign),
                            overlap_scratch + overlap_at_scratch,
                            overlap_limb_count);
                    }
                    const uint32_t target = generator_targets[
                        (uint64_t)generator * (uint64_t)factor_count + source];
                    const uint64_t context_target =
                        ((uint64_t)context * (uint64_t)factor_count + target)
                            * (uint64_t)context_limb_count;
                    const uint64_t restriction_target =
                        ((uint64_t)restriction * (uint64_t)factor_count + target)
                            * (uint64_t)restriction_limb_count;
                    multiply_unsigned_limbs(
                        context_current_limbs + context_target, context_limb_count,
                        restriction_current_limbs + restriction_target,
                        restriction_limb_count,
                        right_scratch + product_at, product_limb_count);
                    if (unsigned_limbs_are_zero(
                            right_scratch + product_at, product_limb_count)) continue;
                    multiply_unsigned_limbs(
                        right_scratch + product_at, product_limb_count,
                        left_scratch + product_at, product_limb_count,
                        quadratic_scratch + quadratic_at, quadratic_limb_count);
                    multiply_unsigned_limbs(
                        quadratic_scratch + quadratic_at, quadratic_limb_count,
                        context_weight_limbs + weight_at, weight_limb_count,
                        term_scratch + moment_at, moment_limb_count);
                    const int8_t target_orientation = family_orientation[
                        (uint64_t)axis * (uint64_t)factor_count + target];
                    const uint8_t target_sign = target_orientation < 0
                        ? 2U : (target_orientation > 0 ? 1U : 0U);
                    if (target_sign != 0U) {
                        scale_unsigned_limbs(
                            term_scratch + moment_at, moment_limb_count,
                            factor_capacity[target], overlap_scratch + overlap_at_scratch,
                            overlap_limb_count);
                        add_signed_magnitude(
                            action_overlap_sign + output,
                            action_overlap_limbs + output_at,
                            target_sign,
                            overlap_scratch + overlap_at_scratch,
                            overlap_limb_count);
                    }
                }
            }

            if (axis < receiver_count) {
                const uint32_t class_begin = receiver_class_bases[axis];
                const uint32_t class_end = receiver_class_bases[axis + 1U];
                const uint32_t total_classes = receiver_class_bases[receiver_count];
                const uint64_t generator_class_at =
                    (uint64_t)generator * ((uint64_t)total_classes + 1ULL);
                uint64_t receiver_class_begin = (uint64_t)class_begin
                    + (uint64_t)incidence_chunk * (uint64_t)incidence_chunk_size;
                uint64_t receiver_class_end = receiver_class_begin + incidence_chunk_size;
                if (receiver_class_end > class_end) receiver_class_end = class_end;
                for (uint64_t receiver_class64 = receiver_class_begin;
                         receiver_class64 < receiver_class_end;
                         ++receiver_class64) {
                        const uint32_t receiver_class = (uint32_t)receiver_class64;
                        zero_unsigned_limbs(
                            right_scratch + product_at, product_limb_count);
                        zero_unsigned_limbs(
                            bucket_scratch + product_at, product_limb_count);
                        for (uint64_t source_at =
                                source_class_factor_offsets[receiver_class];
                             source_at < source_class_factor_offsets[receiver_class + 1U];
                             ++source_at) {
                            const uint32_t source = source_class_factors[source_at];
                            const uint64_t context_source =
                                ((uint64_t)context * (uint64_t)factor_count + source)
                                    * (uint64_t)context_limb_count;
                            const uint64_t restriction_source =
                                ((uint64_t)restriction * (uint64_t)factor_count + source)
                                    * (uint64_t)restriction_limb_count;
                            multiply_unsigned_limbs(
                                context_current_limbs + context_source, context_limb_count,
                                restriction_current_limbs + restriction_source,
                                restriction_limb_count,
                                left_scratch + product_at, product_limb_count);
                            if (unsigned_limbs_are_zero(
                                    left_scratch + product_at, product_limb_count)) continue;
                            add_unsigned_limbs(
                                right_scratch + product_at,
                                left_scratch + product_at,
                                product_limb_count);
                        }
                        const uint64_t transported_class =
                            generator_class_at + receiver_class;
                        for (uint64_t source_at =
                                generator_class_factor_offsets[transported_class];
                             source_at
                                < generator_class_factor_offsets[transported_class + 1U];
                             ++source_at) {
                            const uint32_t source = generator_class_factors[source_at];
                            const uint64_t context_source =
                                ((uint64_t)context * (uint64_t)factor_count + source)
                                    * (uint64_t)context_limb_count;
                            const uint64_t restriction_source =
                                ((uint64_t)restriction * (uint64_t)factor_count + source)
                                    * (uint64_t)restriction_limb_count;
                            multiply_unsigned_limbs(
                                context_current_limbs + context_source, context_limb_count,
                                restriction_current_limbs + restriction_source,
                                restriction_limb_count,
                                left_scratch + product_at, product_limb_count);
                            if (unsigned_limbs_are_zero(
                                    left_scratch + product_at, product_limb_count)) continue;
                            add_unsigned_limbs(
                                bucket_scratch + product_at,
                                left_scratch + product_at,
                                product_limb_count);
                        }

                        const uint32_t *source_sum = right_scratch + product_at;
                        const uint32_t *target_sum = bucket_scratch + product_at;
                        const bool source_zero =
                            unsigned_limbs_are_zero(source_sum, product_limb_count);
                        const bool target_zero =
                            unsigned_limbs_are_zero(target_sum, product_limb_count);
                        if (source_zero && target_zero) continue;
                        const uint32_t *weight = context_weight_limbs + weight_at;
                        uint32_t *quadratic = quadratic_scratch + quadratic_at;
                        uint32_t *term = term_scratch + moment_at;
                        uint32_t *overlap = overlap_scratch + overlap_at_scratch;
                        if (!source_zero && !target_zero) {
                            add_weighted_quadratic_term(
                                source_sum, target_sum, weight, 1U,
                                axis_sign, axis_limbs, quadratic, term, overlap,
                                product_limb_count, weight_limb_count,
                                quadratic_limb_count, moment_limb_count,
                                overlap_limb_count);
                        }
                        if (!source_zero) {
                            add_weighted_quadratic_term(
                                source_sum, source_sum, weight, 2U,
                                axis_sign, axis_limbs, quadratic, term, overlap,
                                product_limb_count, weight_limb_count,
                                quadratic_limb_count, moment_limb_count,
                                overlap_limb_count);
                        }
                        if (!target_zero) {
                            add_weighted_quadratic_term(
                                target_sum, target_sum, weight, 1U,
                                axis_norm_sign, axis_norm_limbs, quadratic, term, overlap,
                                product_limb_count, weight_limb_count,
                                quadratic_limb_count, moment_limb_count,
                                overlap_limb_count);
                        }
                        if (!source_zero && !target_zero) {
                            add_weighted_quadratic_term(
                                source_sum, target_sum, weight, 2U,
                                axis_norm_sign, axis_norm_limbs, quadratic, term, overlap,
                                product_limb_count, weight_limb_count,
                                quadratic_limb_count, moment_limb_count,
                                overlap_limb_count);
                            add_weighted_quadratic_term(
                                source_sum, target_sum, weight, 2U,
                                axis_norm_sign, axis_norm_limbs, quadratic, term, overlap,
                                product_limb_count, weight_limb_count,
                                quadratic_limb_count, moment_limb_count,
                                overlap_limb_count);
                        }
                        if (!source_zero) {
                            add_weighted_quadratic_term(
                                source_sum, source_sum, weight, 1U,
                                axis_norm_sign, axis_norm_limbs, quadratic, term, overlap,
                                product_limb_count, weight_limb_count,
                                quadratic_limb_count, moment_limb_count,
                                overlap_limb_count);
                        }
                    }
            }
    }
}

extern "C" __global__ void reduce_membrane_factorized_quadratic_moments(
    const uint8_t *contribution_action_sign,
    const uint32_t *contribution_action_limbs,
    const uint8_t *contribution_reflected_sign,
    const uint32_t *contribution_reflected_limbs,
    const uint8_t *contribution_receiver_sign,
    const uint32_t *contribution_receiver_limbs,
    const uint8_t *contribution_receiver_norm_sign,
    const uint32_t *contribution_receiver_norm_limbs,
    const uint64_t *port_restriction_offsets,
    const uint8_t *family_real_sign,
    const uint32_t *family_real_limbs,
    const uint8_t *family_imaginary_sign,
    const uint32_t *family_imaginary_limbs,
    uint8_t *action_overlap_sign,
    uint32_t *action_overlap_limbs,
    uint8_t *reflected_overlap_sign,
    uint32_t *reflected_overlap_limbs,
    uint8_t *receiver_overlap_sign,
    uint32_t *receiver_overlap_limbs,
    uint8_t *receiver_action_norm_sign,
    uint32_t *receiver_action_norm_limbs,
    uint8_t *contact_real_sign,
    uint32_t *contact_real_limbs,
    uint8_t *contact_imaginary_sign,
    uint32_t *contact_imaginary_limbs,
    uint32_t context_chunk_count,
    uint32_t incidence_chunk_count,
    uint32_t port_count,
    uint32_t generator_count,
    uint32_t family_count,
    uint32_t receiver_count,
    uint32_t axis_count,
    uint32_t overlap_limb_count,
    uint32_t family_limb_count,
    uint32_t contact_limb_count,
    uint32_t resident_rectangular_restrictions,
    uint32_t resident_boundary_state_count,
    uint32_t descend_boundary_state_receiver,
    uint32_t clear_output,
    uint32_t finalize_contact)
{
    const uint32_t at = blockIdx.x * blockDim.x + threadIdx.x;
    const uint32_t response_state_count = resident_rectangular_restrictions
            && descend_boundary_state_receiver == 0U
        ? resident_boundary_state_count : 1U;
    const uint64_t local_face_count =
        (uint64_t)port_count * (uint64_t)generator_count;
    const uint64_t work = (uint64_t)response_state_count * local_face_count
        * (uint64_t)axis_count;
    if ((uint64_t)at >= work) return;
    const uint32_t face = at / axis_count;
    const uint32_t source_state_coordinate = (uint32_t)(face / local_face_count);
    const uint32_t local_face = (uint32_t)(face % local_face_count);
    const uint32_t port = local_face / generator_count;
    const uint32_t generator = local_face % generator_count;
    const uint32_t axis = at % axis_count;

    if (axis < family_count) {
        const uint64_t output = (uint64_t)face * (uint64_t)family_count + axis;
        const uint64_t output_at = output * (uint64_t)overlap_limb_count;
        if (clear_output != 0U) {
            action_overlap_sign[output] = 0U;
            reflected_overlap_sign[output] = 0U;
            zero_unsigned_limbs(action_overlap_limbs + output_at, overlap_limb_count);
            zero_unsigned_limbs(reflected_overlap_limbs + output_at, overlap_limb_count);
        }
        const uint64_t restriction_begin = resident_rectangular_restrictions
            ? (uint64_t)port * resident_boundary_state_count
                + (descend_boundary_state_receiver != 0U ? 0U : source_state_coordinate)
            : port_restriction_offsets[port];
        const uint64_t restriction_end = resident_rectangular_restrictions
            ? restriction_begin
                + (descend_boundary_state_receiver != 0U
                    ? resident_boundary_state_count : 1U)
            : port_restriction_offsets[port + 1U];
        for (uint64_t restriction = restriction_begin;
             restriction < restriction_end;
             ++restriction) {
            const uint64_t section =
                (restriction * (uint64_t)generator_count + generator)
                    * (uint64_t)axis_count + axis;
            const uint64_t contribution = section;
            const uint64_t contribution_at =
                contribution * (uint64_t)overlap_limb_count;
            add_signed_magnitude(
                action_overlap_sign + output,
                action_overlap_limbs + output_at,
                contribution_action_sign[contribution],
                contribution_action_limbs + contribution_at,
                overlap_limb_count);
            add_signed_magnitude(
                reflected_overlap_sign + output,
                reflected_overlap_limbs + output_at,
                contribution_reflected_sign[contribution],
                contribution_reflected_limbs + contribution_at,
                overlap_limb_count);
        }
        if (finalize_contact != 0U) {
            const uint64_t family_at = (uint64_t)axis * (uint64_t)family_limb_count;
            const uint64_t contact_at = output * (uint64_t)contact_limb_count;
            contact_real_sign[output] =
                product_sign(family_real_sign[axis], action_overlap_sign[output]);
            contact_imaginary_sign[output] =
                product_sign(family_imaginary_sign[axis], action_overlap_sign[output]);
            multiply_unsigned_limbs(
                family_real_limbs + family_at, family_limb_count,
                action_overlap_limbs + output_at, overlap_limb_count,
                contact_real_limbs + contact_at, contact_limb_count);
            multiply_unsigned_limbs(
                family_imaginary_limbs + family_at, family_limb_count,
                action_overlap_limbs + output_at, overlap_limb_count,
                contact_imaginary_limbs + contact_at, contact_limb_count);
        }
    }

    if (axis < receiver_count) {
        const uint64_t output = (uint64_t)face * (uint64_t)receiver_count + axis;
        const uint64_t output_at = output * (uint64_t)overlap_limb_count;
        if (clear_output != 0U) {
            receiver_overlap_sign[output] = 0U;
            receiver_action_norm_sign[output] = 0U;
            zero_unsigned_limbs(receiver_overlap_limbs + output_at, overlap_limb_count);
            zero_unsigned_limbs(receiver_action_norm_limbs + output_at, overlap_limb_count);
        }
        const uint64_t restriction_begin = resident_rectangular_restrictions
            ? (uint64_t)port * resident_boundary_state_count
                + (descend_boundary_state_receiver != 0U ? 0U : source_state_coordinate)
            : port_restriction_offsets[port];
        const uint64_t restriction_end = resident_rectangular_restrictions
            ? restriction_begin
                + (descend_boundary_state_receiver != 0U
                    ? resident_boundary_state_count : 1U)
            : port_restriction_offsets[port + 1U];
        for (uint64_t restriction = restriction_begin;
             restriction < restriction_end;
             ++restriction) {
            const uint64_t section =
                (restriction * (uint64_t)generator_count + generator)
                    * (uint64_t)axis_count + axis;
            const uint64_t contribution = section;
            const uint64_t contribution_at =
                contribution * (uint64_t)overlap_limb_count;
            add_signed_magnitude(
                receiver_overlap_sign + output,
                receiver_overlap_limbs + output_at,
                contribution_receiver_sign[contribution],
                contribution_receiver_limbs + contribution_at,
                overlap_limb_count);
            add_signed_magnitude(
                receiver_action_norm_sign + output,
                receiver_action_norm_limbs + output_at,
                contribution_receiver_norm_sign[contribution],
                contribution_receiver_norm_limbs + contribution_at,
                overlap_limb_count);
        }
    }
}

extern "C" __global__ void contract_membrane_quadratic_moments(
    const uint32_t *moment_limbs,
    const uint32_t *active_factors,
    const uint32_t *generator_targets,
    const uint32_t *generator_local_targets,
    const uint64_t *factor_receiver_observations,
    const uint64_t *factor_capacity,
    const int8_t *family_orientation,
    const uint8_t *family_real_sign,
    const uint32_t *family_real_limbs,
    const uint8_t *family_imaginary_sign,
    const uint32_t *family_imaginary_limbs,
    uint8_t *action_overlap_sign,
    uint32_t *action_overlap_limbs,
    uint8_t *reflected_overlap_sign,
    uint32_t *reflected_overlap_limbs,
    uint8_t *receiver_overlap_sign,
    uint32_t *receiver_overlap_limbs,
    uint8_t *receiver_action_norm_sign,
    uint32_t *receiver_action_norm_limbs,
    uint8_t *contact_real_sign,
    uint32_t *contact_real_limbs,
    uint8_t *contact_imaginary_sign,
    uint32_t *contact_imaginary_limbs,
    uint32_t *overlap_scratch,
    uint32_t port_count,
    uint32_t factor_count,
    uint32_t native_factor_count,
    uint32_t generator_count,
    uint32_t family_count,
    uint32_t receiver_count,
    uint32_t moment_limb_count,
    uint32_t overlap_limb_count,
    uint32_t family_limb_count,
    uint32_t contact_limb_count)
{
    const uint32_t at = blockIdx.x * blockDim.x + threadIdx.x;
    const uint32_t axis_count = family_count > receiver_count ? family_count : receiver_count;
    const uint64_t work = (uint64_t)port_count * (uint64_t)axis_count;
    if ((uint64_t)at >= work) return;
    const uint32_t port = at / axis_count;
    const uint32_t axis = at % axis_count;
    const uint64_t scratch_at = (uint64_t)at * (uint64_t)overlap_limb_count;

    if (axis < receiver_count) {
        const uint32_t receiver = axis;
        const uint64_t output =
            (uint64_t)port * (uint64_t)receiver_count + receiver;
        const uint64_t output_at = output * (uint64_t)overlap_limb_count;
        receiver_overlap_sign[output] = 0U;
        receiver_action_norm_sign[output] = 0U;
        zero_unsigned_limbs(receiver_overlap_limbs + output_at, overlap_limb_count);
        zero_unsigned_limbs(receiver_action_norm_limbs + output_at, overlap_limb_count);
        for (uint32_t generator = 0U; generator < generator_count; ++generator) {
            const uint64_t generator_at =
                (uint64_t)generator * (uint64_t)factor_count;
            for (uint32_t first = 0U; first < factor_count; ++first) {
                const uint32_t first_factor = active_factors[first];
                const uint64_t first_observation = factor_receiver_observations[
                    (uint64_t)first_factor * (uint64_t)receiver_count + receiver];
                for (uint32_t second = 0U; second < factor_count; ++second) {
                    const uint32_t transported_second =
                        generator_targets[generator_at + second];
                    const uint64_t moment_at =
                        (((uint64_t)port * (uint64_t)factor_count + first)
                            * (uint64_t)factor_count + second)
                        * (uint64_t)moment_limb_count;
                    const uint32_t second_factor = active_factors[second];
                    const uint64_t second_observation = factor_receiver_observations[
                        (uint64_t)second_factor * (uint64_t)receiver_count + receiver];
                    const uint64_t transported_second_observation =
                        factor_receiver_observations[
                            (uint64_t)transported_second * (uint64_t)receiver_count + receiver];
                    if (first_observation == transported_second_observation) {
                        add_signed_magnitude(
                            receiver_overlap_sign + output,
                            receiver_overlap_limbs + output_at,
                            1U,
                            moment_limbs + moment_at,
                            moment_limb_count);
                    }
                    if (first_observation == second_observation) {
                        add_signed_magnitude(
                            receiver_overlap_sign + output,
                            receiver_overlap_limbs + output_at,
                            2U,
                            moment_limbs + moment_at,
                            moment_limb_count);
                    }
                }
            }
            for (uint32_t first = 0U; first < factor_count; ++first) {
                const uint32_t first_factor = active_factors[first];
                const uint32_t transported_first = generator_targets[generator_at + first];
                const uint64_t first_observation = factor_receiver_observations[
                    (uint64_t)first_factor * (uint64_t)receiver_count + receiver];
                const uint64_t transported_first_observation =
                    factor_receiver_observations[
                        (uint64_t)transported_first * (uint64_t)receiver_count + receiver];
                for (uint32_t second = 0U; second < factor_count; ++second) {
                    const uint32_t second_factor = active_factors[second];
                    const uint32_t transported_second =
                        generator_targets[generator_at + second];
                    const uint64_t second_observation = factor_receiver_observations[
                        (uint64_t)second_factor * (uint64_t)receiver_count + receiver];
                    const uint64_t transported_second_observation =
                        factor_receiver_observations[
                            (uint64_t)transported_second * (uint64_t)receiver_count + receiver];
                    const uint64_t moment_at =
                        (((uint64_t)port * (uint64_t)factor_count + first)
                            * (uint64_t)factor_count + second)
                        * (uint64_t)moment_limb_count;
                    if (transported_first_observation == transported_second_observation) {
                        add_signed_magnitude(
                            receiver_action_norm_sign + output,
                            receiver_action_norm_limbs + output_at,
                            1U, moment_limbs + moment_at, moment_limb_count);
                    }
                    if (transported_first_observation == second_observation) {
                        add_signed_magnitude(
                            receiver_action_norm_sign + output,
                            receiver_action_norm_limbs + output_at,
                            2U, moment_limbs + moment_at, moment_limb_count);
                    }
                    if (first_observation == transported_second_observation) {
                        add_signed_magnitude(
                            receiver_action_norm_sign + output,
                            receiver_action_norm_limbs + output_at,
                            2U, moment_limbs + moment_at, moment_limb_count);
                    }
                    if (first_observation == second_observation) {
                        add_signed_magnitude(
                            receiver_action_norm_sign + output,
                            receiver_action_norm_limbs + output_at,
                            1U, moment_limbs + moment_at, moment_limb_count);
                    }
                }
            }
        }
    }

    if (axis >= family_count) return;
    const uint32_t family = axis;
    const uint64_t output = (uint64_t)port * (uint64_t)family_count + family;
    const uint64_t output_at = output * (uint64_t)overlap_limb_count;
    action_overlap_sign[output] = 0U;
    reflected_overlap_sign[output] = 0U;
    zero_unsigned_limbs(action_overlap_limbs + output_at, overlap_limb_count);
    zero_unsigned_limbs(reflected_overlap_limbs + output_at, overlap_limb_count);
    for (uint32_t generator = 0U; generator < generator_count; ++generator) {
        const uint64_t generator_at = (uint64_t)generator * (uint64_t)factor_count;
        for (uint32_t factor = 0U; factor < factor_count; ++factor) {
            const uint32_t global_factor = active_factors[factor];
            const uint64_t diagonal_at =
                (((uint64_t)port * (uint64_t)factor_count + factor)
                    * (uint64_t)factor_count + factor)
                * (uint64_t)moment_limb_count;
            const int8_t orientation =
                family_orientation[(uint64_t)family * (uint64_t)native_factor_count
                    + global_factor];
            const uint8_t orientation_sign =
                orientation < 0 ? 2U : (orientation > 0 ? 1U : 0U);
            if (orientation_sign != 0U) {
                scale_unsigned_limbs(
                    moment_limbs + diagonal_at, moment_limb_count,
                    factor_capacity[global_factor], overlap_scratch + scratch_at,
                    overlap_limb_count);
                add_signed_magnitude(
                    reflected_overlap_sign + output,
                    reflected_overlap_limbs + output_at,
                    orientation_sign, overlap_scratch + scratch_at,
                    overlap_limb_count);
                add_signed_magnitude(
                    action_overlap_sign + output,
                    action_overlap_limbs + output_at,
                    opposite_sign(orientation_sign), overlap_scratch + scratch_at,
                    overlap_limb_count);
            }
            const uint32_t target = generator_targets[generator_at + factor];
            const uint32_t local_target = generator_local_targets[generator_at + factor];
            const int8_t target_orientation =
                family_orientation[(uint64_t)family * (uint64_t)native_factor_count
                    + target];
            const uint8_t target_sign = target_orientation < 0
                ? 2U : (target_orientation > 0 ? 1U : 0U);
            if (target_sign != 0U && local_target != 0xFFFFFFFFU) {
                const uint64_t transported_at =
                    (((uint64_t)port * (uint64_t)factor_count + local_target)
                        * (uint64_t)factor_count + factor)
                    * (uint64_t)moment_limb_count;
                scale_unsigned_limbs(
                    moment_limbs + transported_at, moment_limb_count,
                    factor_capacity[target], overlap_scratch + scratch_at,
                    overlap_limb_count);
                add_signed_magnitude(
                    action_overlap_sign + output,
                    action_overlap_limbs + output_at,
                    target_sign, overlap_scratch + scratch_at,
                    overlap_limb_count);
            }
        }
    }
    const uint64_t family_at = (uint64_t)family * (uint64_t)family_limb_count;
    const uint64_t contact_at = output * (uint64_t)contact_limb_count;
    contact_real_sign[output] =
        product_sign(family_real_sign[family], action_overlap_sign[output]);
    contact_imaginary_sign[output] =
        product_sign(family_imaginary_sign[family], action_overlap_sign[output]);
    multiply_unsigned_limbs(
        family_real_limbs + family_at, family_limb_count,
        action_overlap_limbs + output_at, overlap_limb_count,
        contact_real_limbs + contact_at, contact_limb_count);
    multiply_unsigned_limbs(
        family_imaginary_limbs + family_at, family_limb_count,
        action_overlap_limbs + output_at, overlap_limb_count,
        contact_imaginary_limbs + contact_at, contact_limb_count);
}

extern "C" __global__ void gather_membrane_boundary_chain_radiation(
    const uint32_t *support_port,
    const uint8_t *action_overlap_sign,
    const uint32_t *action_overlap_limbs,
    const uint8_t *reflected_overlap_sign,
    const uint32_t *reflected_overlap_limbs,
    const uint8_t *receiver_overlap_sign,
    const uint32_t *receiver_overlap_limbs,
    const uint8_t *receiver_action_norm_sign,
    const uint32_t *receiver_action_norm_limbs,
    const uint8_t *contact_real_sign,
    const uint32_t *contact_real_limbs,
    const uint8_t *contact_imaginary_sign,
    const uint32_t *contact_imaginary_limbs,
    uint8_t *support_real_sign,
    uint32_t *support_real_limbs,
    uint8_t *support_imaginary_sign,
    uint32_t *support_imaginary_limbs,
    uint8_t *port_real_sign,
    uint32_t *port_real_limbs,
    uint8_t *port_imaginary_sign,
    uint32_t *port_imaginary_limbs,
    uint8_t *joint_real_sign,
    uint32_t *joint_real_limbs,
    uint8_t *joint_imaginary_sign,
    uint32_t *joint_imaginary_limbs,
    uint8_t *port_action_overlap_sign,
    uint32_t *port_action_overlap_limbs,
    uint8_t *port_reflected_overlap_sign,
    uint32_t *port_reflected_overlap_limbs,
    uint8_t *port_receiver_overlap_sign,
    uint32_t *port_receiver_overlap_limbs,
    uint8_t *port_receiver_action_norm_sign,
    uint32_t *port_receiver_action_norm_limbs,
    uint32_t support_count,
    uint32_t port_count,
    uint32_t family_count,
    uint32_t receiver_count,
    uint32_t overlap_limb_count,
    uint32_t contact_limb_count,
    uint32_t radiation_limb_count)
{
    if (blockIdx.x != 0U || threadIdx.x != 0U) return;
    *joint_real_sign = 0U;
    *joint_imaginary_sign = 0U;
    for (uint32_t limb = 0U; limb < radiation_limb_count; ++limb) {
        joint_real_limbs[limb] = 0U;
        joint_imaginary_limbs[limb] = 0U;
    }
    for (uint32_t support = 0U; support < support_count; ++support) {
        support_real_sign[support] = 0U;
        support_imaginary_sign[support] = 0U;
        const uint64_t support_at = (uint64_t)support * (uint64_t)radiation_limb_count;
        for (uint32_t limb = 0U; limb < radiation_limb_count; ++limb) {
            support_real_limbs[support_at + limb] = 0U;
            support_imaginary_limbs[support_at + limb] = 0U;
        }
    }
    for (uint32_t port = 0U; port < port_count; ++port) {
        port_real_sign[port] = 0U;
        port_imaginary_sign[port] = 0U;
        const uint64_t port_at = (uint64_t)port * (uint64_t)radiation_limb_count;
        for (uint32_t limb = 0U; limb < radiation_limb_count; ++limb) {
            port_real_limbs[port_at + limb] = 0U;
            port_imaginary_limbs[port_at + limb] = 0U;
        }
        for (uint32_t family = 0U; family < family_count; ++family) {
            const uint64_t family_at =
                ((uint64_t)port * (uint64_t)family_count + family)
                * (uint64_t)overlap_limb_count;
            const uint64_t family_index =
                (uint64_t)port * (uint64_t)family_count + family;
            port_action_overlap_sign[family_index] = 0U;
            port_reflected_overlap_sign[family_index] = 0U;
            zero_unsigned_limbs(
                port_action_overlap_limbs + family_at, overlap_limb_count);
            zero_unsigned_limbs(
                port_reflected_overlap_limbs + family_at, overlap_limb_count);
        }
        for (uint32_t receiver = 0U; receiver < receiver_count; ++receiver) {
            const uint64_t port_receiver =
                (uint64_t)port * (uint64_t)receiver_count + receiver;
            const uint64_t receiver_at =
                port_receiver * (uint64_t)overlap_limb_count;
            port_receiver_overlap_sign[port_receiver] = 0U;
            port_receiver_action_norm_sign[port_receiver] = 0U;
            zero_unsigned_limbs(
                port_receiver_overlap_limbs + receiver_at, overlap_limb_count);
            zero_unsigned_limbs(
                port_receiver_action_norm_limbs + receiver_at, overlap_limb_count);
        }
    }
    for (uint32_t support = 0U; support < support_count; ++support) {
        const uint32_t port = support_port[support];
        if (port >= port_count) continue;
        const uint64_t support_at = (uint64_t)support * (uint64_t)radiation_limb_count;
        const uint64_t port_at = (uint64_t)port * (uint64_t)radiation_limb_count;
        for (uint32_t family = 0U; family < family_count; ++family) {
            const uint64_t response =
                (uint64_t)support * (uint64_t)family_count + family;
            const uint64_t contact_at = response * (uint64_t)contact_limb_count;
            const uint64_t overlap_at = response * (uint64_t)overlap_limb_count;
            const uint64_t port_family =
                (uint64_t)port * (uint64_t)family_count + family;
            const uint64_t port_overlap_at =
                port_family * (uint64_t)overlap_limb_count;
            add_signed_magnitude(
                port_action_overlap_sign + port_family,
                port_action_overlap_limbs + port_overlap_at,
                action_overlap_sign[response],
                action_overlap_limbs + overlap_at,
                overlap_limb_count);
            add_signed_magnitude(
                port_reflected_overlap_sign + port_family,
                port_reflected_overlap_limbs + port_overlap_at,
                reflected_overlap_sign[response],
                reflected_overlap_limbs + overlap_at,
                overlap_limb_count);
            add_signed_magnitude(
                support_real_sign + support,
                support_real_limbs + support_at,
                contact_real_sign[response],
                contact_real_limbs + contact_at,
                contact_limb_count);
            add_signed_magnitude(
                support_imaginary_sign + support,
                support_imaginary_limbs + support_at,
                contact_imaginary_sign[response],
                contact_imaginary_limbs + contact_at,
                contact_limb_count);
        }
        for (uint32_t receiver = 0U; receiver < receiver_count; ++receiver) {
            const uint64_t support_receiver =
                (uint64_t)support * (uint64_t)receiver_count + receiver;
            const uint64_t port_receiver =
                (uint64_t)port * (uint64_t)receiver_count + receiver;
            const uint64_t support_receiver_at =
                support_receiver * (uint64_t)overlap_limb_count;
            const uint64_t port_receiver_at =
                port_receiver * (uint64_t)overlap_limb_count;
            add_signed_magnitude(
                port_receiver_overlap_sign + port_receiver,
                port_receiver_overlap_limbs + port_receiver_at,
                receiver_overlap_sign[support_receiver],
                receiver_overlap_limbs + support_receiver_at,
                overlap_limb_count);
            add_signed_magnitude(
                port_receiver_action_norm_sign + port_receiver,
                port_receiver_action_norm_limbs + port_receiver_at,
                receiver_action_norm_sign[support_receiver],
                receiver_action_norm_limbs + support_receiver_at,
                overlap_limb_count);
        }
        add_signed_magnitude(
            port_real_sign + port,
            port_real_limbs + port_at,
            support_real_sign[support],
            support_real_limbs + support_at,
            radiation_limb_count);
        add_signed_magnitude(
            port_imaginary_sign + port,
            port_imaginary_limbs + port_at,
            support_imaginary_sign[support],
            support_imaginary_limbs + support_at,
            radiation_limb_count);
        add_signed_magnitude(
            joint_real_sign,
            joint_real_limbs,
            support_real_sign[support],
            support_real_limbs + support_at,
            radiation_limb_count);
        add_signed_magnitude(
            joint_imaginary_sign,
            joint_imaginary_limbs,
            support_imaginary_sign[support],
            support_imaginary_limbs + support_at,
            radiation_limb_count);
    }
}

/// Descend the addressed `(source-state,port,generator)` radiation faces to the declared physical
/// boundary-port receiver.  The complete face section remains resident beside this quotient; this
/// kernel performs only its exact finite direct sum and the corresponding existential phase-front
/// projection.  One lane owns the ordered reduction so signed arbitrary-width addition is
/// deterministic and no host reconstruction participates.
extern "C" __global__ void aggregate_membrane_boundary_face_radiation_by_port(
    const uint8_t *face_real_sign,
    const uint32_t *face_real_limbs,
    const uint8_t *face_imaginary_sign,
    const uint32_t *face_imaginary_limbs,
    const uint8_t *face_phase_locked,
    uint8_t *port_real_sign,
    uint32_t *port_real_limbs,
    uint8_t *port_imaginary_sign,
    uint32_t *port_imaginary_limbs,
    uint8_t *port_phase_locked,
    uint32_t face_count,
    uint32_t port_count,
    uint32_t local_face_count,
    uint32_t generator_count,
    uint32_t limb_count)
{
    if (blockIdx.x != 0U || threadIdx.x != 0U || port_count == 0U
        || local_face_count == 0U || generator_count == 0U) return;
    for (uint32_t port = 0U; port < port_count; ++port) {
        port_real_sign[port] = 0U;
        port_imaginary_sign[port] = 0U;
        port_phase_locked[port] = 0U;
        zero_unsigned_limbs(
            port_real_limbs + (uint64_t)port * limb_count, limb_count);
        zero_unsigned_limbs(
            port_imaginary_limbs + (uint64_t)port * limb_count, limb_count);
    }
    for (uint32_t face = 0U; face < face_count; ++face) {
        const uint32_t local_face = face % local_face_count;
        const uint32_t port = local_face / generator_count;
        if (port >= port_count) continue;
        add_signed_magnitude(
            port_real_sign + port,
            port_real_limbs + (uint64_t)port * limb_count,
            face_real_sign[face],
            face_real_limbs + (uint64_t)face * limb_count,
            limb_count);
        add_signed_magnitude(
            port_imaginary_sign + port,
            port_imaginary_limbs + (uint64_t)port * limb_count,
            face_imaginary_sign[face],
            face_imaginary_limbs + (uint64_t)face * limb_count,
            limb_count);
        if (face_phase_locked[face] != 0U) port_phase_locked[port] = 1U;
    }
}

extern "C" __global__ void prepare_membrane_factored_receiver_boundary_supports(
    const uint8_t *receiver_sign,
    const uint32_t *receiver_limbs,
    const uint32_t *support_port,
    const uint32_t *support_receiver_class,
    const uint32_t *support_quadratic_scale_limbs,
    const uint8_t *family_real_sign,
    const uint32_t *family_real_limbs,
    const uint8_t *family_imaginary_sign,
    const uint32_t *family_imaginary_limbs,
    uint8_t *action_overlap_sign,
    uint32_t *action_overlap_limbs,
    uint8_t *reflected_overlap_sign,
    uint32_t *reflected_overlap_limbs,
    uint8_t *opaque_receiver_overlap_sign,
    uint32_t *opaque_receiver_overlap_limbs,
    uint8_t *receiver_action_norm_sign,
    uint32_t *receiver_action_norm_limbs,
    uint8_t *contact_real_sign,
    uint32_t *contact_real_limbs,
    uint8_t *contact_imaginary_sign,
    uint32_t *contact_imaginary_limbs,
    uint32_t *obstruction,
    uint32_t support_count,
    uint32_t port_count,
    uint32_t family_count,
    uint32_t opaque_receiver_count,
    uint32_t receiver_limb_count,
    uint32_t support_quadratic_scale_limb_count,
    uint32_t overlap_limb_count,
    uint32_t family_limb_count,
    uint32_t contact_limb_count)
{
    const uint32_t at = blockIdx.x * blockDim.x + threadIdx.x;
    const uint32_t axis_count = family_count > opaque_receiver_count
        ? family_count : opaque_receiver_count;
    const uint64_t work = (uint64_t)support_count * (uint64_t)axis_count;
    if ((uint64_t)at >= work || axis_count == 0U) return;
    const uint32_t support = at / axis_count;
    const uint32_t axis = at % axis_count;
    if (support_port[support] >= port_count) {
        atomicExch(obstruction, 1U);
        return;
    }
    const uint64_t receiver_stride =
        (uint64_t)family_count * 2ULL + (uint64_t)opaque_receiver_count * 2ULL;
    const uint64_t receiver_base =
        (uint64_t)support_receiver_class[support] * receiver_stride;
    const uint32_t *support_scale = support_quadratic_scale_limbs
        + (uint64_t)support * (uint64_t)support_quadratic_scale_limb_count;

    if (axis < family_count) {
        const uint64_t response = (uint64_t)support * (uint64_t)family_count + axis;
        const uint64_t output_at = response * (uint64_t)overlap_limb_count;
        const uint64_t reflected = receiver_base + axis;
        const uint64_t action = receiver_base + (uint64_t)family_count + axis;
        const uint8_t reflected_class = receiver_sign[reflected];
        const uint8_t action_class = receiver_sign[action];
        if (reflected_class > 2U || action_class > 2U) {
            atomicExch(obstruction, 1U);
            return;
        }
        reflected_overlap_sign[response] = reflected_class;
        action_overlap_sign[response] = action_class;
        zero_unsigned_limbs(reflected_overlap_limbs + output_at, overlap_limb_count);
        zero_unsigned_limbs(action_overlap_limbs + output_at, overlap_limb_count);
        const uint64_t reflected_at = reflected * (uint64_t)receiver_limb_count;
        const uint64_t action_at = action * (uint64_t)receiver_limb_count;
        multiply_unsigned_limbs(
            receiver_limbs + reflected_at, receiver_limb_count,
            support_scale, support_quadratic_scale_limb_count,
            reflected_overlap_limbs + output_at, overlap_limb_count);
        multiply_unsigned_limbs(
            receiver_limbs + action_at, receiver_limb_count,
            support_scale, support_quadratic_scale_limb_count,
            action_overlap_limbs + output_at, overlap_limb_count);
        const uint64_t family_at = (uint64_t)axis * (uint64_t)family_limb_count;
        const uint64_t contact_at = response * (uint64_t)contact_limb_count;
        contact_real_sign[response] = product_sign(family_real_sign[axis], action_class);
        contact_imaginary_sign[response] = product_sign(family_imaginary_sign[axis], action_class);
        multiply_unsigned_limbs(
            family_real_limbs + family_at, family_limb_count,
            action_overlap_limbs + output_at, overlap_limb_count,
            contact_real_limbs + contact_at, contact_limb_count);
        multiply_unsigned_limbs(
            family_imaginary_limbs + family_at, family_limb_count,
            action_overlap_limbs + output_at, overlap_limb_count,
            contact_imaginary_limbs + contact_at, contact_limb_count);
    }

    if (axis < opaque_receiver_count) {
        const uint64_t response =
            (uint64_t)support * (uint64_t)opaque_receiver_count + axis;
        const uint64_t output_at = response * (uint64_t)overlap_limb_count;
        const uint64_t overlap = receiver_base
            + (uint64_t)family_count * 2ULL + (uint64_t)axis * 2ULL;
        const uint64_t norm = overlap + 1ULL;
        const uint8_t overlap_class = receiver_sign[overlap];
        const uint8_t norm_class = receiver_sign[norm];
        if (overlap_class > 2U || norm_class > 1U) {
            atomicExch(obstruction, 1U);
            return;
        }
        opaque_receiver_overlap_sign[response] = overlap_class;
        receiver_action_norm_sign[response] = norm_class;
        zero_unsigned_limbs(opaque_receiver_overlap_limbs + output_at, overlap_limb_count);
        zero_unsigned_limbs(receiver_action_norm_limbs + output_at, overlap_limb_count);
        const uint64_t overlap_at = overlap * (uint64_t)receiver_limb_count;
        const uint64_t norm_at = norm * (uint64_t)receiver_limb_count;
        multiply_unsigned_limbs(
            receiver_limbs + overlap_at, receiver_limb_count,
            support_scale, support_quadratic_scale_limb_count,
            opaque_receiver_overlap_limbs + output_at, overlap_limb_count);
        multiply_unsigned_limbs(
            receiver_limbs + norm_at, receiver_limb_count,
            support_scale, support_quadratic_scale_limb_count,
            receiver_action_norm_limbs + output_at, overlap_limb_count);
    }
}

extern "C" __global__ void form_membrane_factorized_relational_moment_partials(
    const uint32_t *transported_current_limbs,
    const uint8_t *transported_state_present,
    const uint32_t *transported_states,
    const uint32_t *context_weight_limbs,
    const uint32_t *restriction_current_limbs,
    const uint8_t *restriction_present,
    const uint32_t *boundary_states,
    const uint32_t *relational_state_present,
    const uint32_t *relational_states,
    const uint8_t *relational_real_sign,
    const uint32_t *relational_real_limbs,
    const uint8_t *relational_imaginary_sign,
    const uint32_t *relational_imaginary_limbs,
    uint32_t *partial_overlap_limbs,
    uint32_t *partial_target_norm_limbs,
    uint8_t *dot_real_signs,
    uint32_t *dot_real_limbs,
    uint8_t *dot_imaginary_signs,
    uint32_t *dot_imaginary_limbs,
    uint32_t *first_scratch,
    uint32_t *second_scratch,
    uint32_t *third_scratch,
    uint32_t context_count,
    uint32_t factor_count,
    uint32_t port_count,
    uint32_t generator_count,
    uint32_t boundary_state_count,
    uint32_t relational_state_count,
    uint32_t transported_limb_count,
    uint32_t restriction_limb_count,
    uint32_t relational_limb_count,
    uint32_t weight_limb_count,
    uint32_t output_limb_count)
{
    const uint64_t at = (uint64_t)blockIdx.x * blockDim.x + threadIdx.x;
    const uint64_t local_face_count =
        (uint64_t)port_count * (uint64_t)generator_count;
    const uint64_t work = local_face_count * (uint64_t)context_count;
    if (at >= work || boundary_state_count == 0U || generator_count == 0U) return;
    const uint32_t context = (uint32_t)(at / local_face_count);
    const uint32_t local_face = (uint32_t)(at % local_face_count);
    const uint32_t port = local_face / generator_count;
    const uint32_t generator = local_face % generator_count;
    const uint32_t transported_section = context * generator_count + generator;
    uint32_t *partial_overlap = partial_overlap_limbs + at * (uint64_t)output_limb_count;
    uint32_t *partial_target_norm =
        partial_target_norm_limbs + at * (uint64_t)output_limb_count;
    uint32_t *dot_real = dot_real_limbs + at * (uint64_t)output_limb_count;
    uint32_t *dot_imaginary = dot_imaginary_limbs + at * (uint64_t)output_limb_count;
    uint32_t *first = first_scratch + at * (uint64_t)output_limb_count;
    uint32_t *second = second_scratch + at * (uint64_t)output_limb_count;
    uint32_t *third = third_scratch + at * (uint64_t)output_limb_count;
    zero_unsigned_limbs(partial_overlap, output_limb_count);
    zero_unsigned_limbs(partial_target_norm, output_limb_count);
    zero_unsigned_limbs(dot_real, output_limb_count);
    zero_unsigned_limbs(dot_imaginary, output_limb_count);
    dot_real_signs[at] = 0U;
    dot_imaginary_signs[at] = 0U;
    if (transported_state_present[transported_section] == 0U) return;
    const uint32_t source_state = transported_states[transported_section];
    uint32_t source_state_coordinate = 0xffffffffU;
    for (uint32_t coordinate = 0U; coordinate < boundary_state_count; ++coordinate) {
        if (boundary_states[coordinate] == source_state) {
            source_state_coordinate = coordinate;
            break;
        }
    }
    if (source_state_coordinate == 0xffffffffU) return;
    bool relational_state_present_for_source = false;
    for (uint32_t candidate = 0U; candidate < relational_state_count; ++candidate) {
        if (relational_state_present[candidate] != 0U
            && relational_states[candidate] == source_state) {
            relational_state_present_for_source = true;
            break;
        }
    }
    if (!relational_state_present_for_source) return;
    const uint32_t restriction =
        port * boundary_state_count + source_state_coordinate;
    if (restriction_present[restriction] == 0U) return;
    const uint64_t transported_base =
        (uint64_t)transported_section * (uint64_t)factor_count
            * (uint64_t)transported_limb_count;
    const uint64_t restriction_base =
        (uint64_t)restriction * (uint64_t)factor_count
            * (uint64_t)restriction_limb_count;
    for (uint32_t factor = 0U; factor < factor_count; ++factor) {
        const uint32_t *source = transported_current_limbs + transported_base
            + (uint64_t)factor * (uint64_t)transported_limb_count;
        const uint32_t *restriction_value = restriction_current_limbs + restriction_base
            + (uint64_t)factor * (uint64_t)restriction_limb_count;
        if (unsigned_limbs_are_zero(source, transported_limb_count)
            || unsigned_limbs_are_zero(restriction_value, restriction_limb_count)) continue;
        multiply_unsigned_limbs(
            source, transported_limb_count,
            restriction_value, restriction_limb_count,
            first, output_limb_count);
        multiply_unsigned_limbs(
            first, output_limb_count,
            first, output_limb_count,
            third, output_limb_count);
        add_unsigned_limbs(partial_target_norm, third, output_limb_count);

        for (uint32_t relational_state = 0U;
             relational_state < relational_state_count; ++relational_state) {
            if (relational_state_present[relational_state] == 0U
                || relational_states[relational_state] != source_state) continue;
            const uint64_t relational =
                ((uint64_t)relational_state * (uint64_t)generator_count + generator)
                    * (uint64_t)factor_count + factor;
            const uint32_t *real_magnitude = relational_real_limbs
                + relational * (uint64_t)relational_limb_count;
            if (relational_real_sign[relational] != 0U
                && !unsigned_limbs_are_zero(real_magnitude, relational_limb_count)) {
                multiply_unsigned_limbs(
                    restriction_value, restriction_limb_count,
                    real_magnitude, relational_limb_count,
                    second, output_limb_count);
                multiply_unsigned_limbs(
                    first, output_limb_count,
                    second, output_limb_count,
                    third, output_limb_count);
                add_signed_magnitude(
                    dot_real_signs + at, dot_real,
                    relational_real_sign[relational], third, output_limb_count);
            }
            const uint32_t *imaginary_magnitude = relational_imaginary_limbs
                + relational * (uint64_t)relational_limb_count;
            if (relational_imaginary_sign[relational] != 0U
                && !unsigned_limbs_are_zero(imaginary_magnitude, relational_limb_count)) {
                multiply_unsigned_limbs(
                    restriction_value, restriction_limb_count,
                    imaginary_magnitude, relational_limb_count,
                    second, output_limb_count);
                multiply_unsigned_limbs(
                    first, output_limb_count,
                    second, output_limb_count,
                    third, output_limb_count);
                add_signed_magnitude(
                    dot_imaginary_signs + at, dot_imaginary,
                    relational_imaginary_sign[relational], third, output_limb_count);
            }
        }
    }
    multiply_unsigned_limbs(
        dot_real, output_limb_count,
        dot_real, output_limb_count,
        first, output_limb_count);
    add_unsigned_limbs(partial_overlap, first, output_limb_count);
    multiply_unsigned_limbs(
        dot_imaginary, output_limb_count,
        dot_imaginary, output_limb_count,
        first, output_limb_count);
    add_unsigned_limbs(partial_overlap, first, output_limb_count);
    const uint32_t *weight = context_weight_limbs
        + (uint64_t)context * (uint64_t)weight_limb_count;
    multiply_unsigned_limbs(
        partial_overlap, output_limb_count,
        weight, weight_limb_count,
        first, output_limb_count);
    for (uint32_t limb = 0U; limb < output_limb_count; ++limb) {
        partial_overlap[limb] = first[limb];
    }
    multiply_unsigned_limbs(
        partial_target_norm, output_limb_count,
        weight, weight_limb_count,
        first, output_limb_count);
    for (uint32_t limb = 0U; limb < output_limb_count; ++limb) {
        partial_target_norm[limb] = first[limb];
    }
    multiply_unsigned_limbs(
        dot_real, output_limb_count,
        weight, weight_limb_count,
        first, output_limb_count);
    for (uint32_t limb = 0U; limb < output_limb_count; ++limb) {
        dot_real[limb] = first[limb];
    }
    multiply_unsigned_limbs(
        dot_imaginary, output_limb_count,
        weight, weight_limb_count,
        first, output_limb_count);
    for (uint32_t limb = 0U; limb < output_limb_count; ++limb) {
        dot_imaginary[limb] = first[limb];
    }
}

extern "C" __global__ void form_membrane_factorized_relational_current_norms(
    const uint32_t *restriction_current_limbs,
    const uint8_t *restriction_present,
    const uint32_t *boundary_states,
    const uint32_t *relational_state_present,
    const uint32_t *relational_states,
    const uint8_t *relational_real_sign,
    const uint32_t *relational_real_limbs,
    const uint8_t *relational_imaginary_sign,
    const uint32_t *relational_imaginary_limbs,
    uint32_t *relational_norm_limbs,
    uint32_t *first_scratch,
    uint32_t *second_scratch,
    uint32_t port_count,
    uint32_t factor_count,
    uint32_t generator_count,
    uint32_t boundary_state_count,
    uint32_t relational_state_count,
    uint32_t restriction_limb_count,
    uint32_t relational_limb_count,
    uint32_t output_limb_count,
    uint32_t descend_boundary_state_receiver)
{
    const uint32_t face = blockIdx.x * blockDim.x + threadIdx.x;
    const uint32_t local_face_count = port_count * generator_count;
    const uint32_t response_state_count = descend_boundary_state_receiver != 0U
        ? 1U : boundary_state_count;
    const uint32_t face_count = response_state_count * local_face_count;
    if (face >= face_count || generator_count == 0U) return;
    const uint32_t source_state_coordinate = face / local_face_count;
    const uint32_t local_face = face % local_face_count;
    const uint32_t port = local_face / generator_count;
    const uint32_t generator = local_face % generator_count;
    uint32_t *output = relational_norm_limbs
        + (uint64_t)face * (uint64_t)output_limb_count;
    uint32_t *first = first_scratch + (uint64_t)face * (uint64_t)output_limb_count;
    uint32_t *second = second_scratch + (uint64_t)face * (uint64_t)output_limb_count;
    zero_unsigned_limbs(output, output_limb_count);
    if (source_state_coordinate >= response_state_count) return;
    const uint32_t coordinate_begin = descend_boundary_state_receiver != 0U
        ? 0U : source_state_coordinate;
    const uint32_t coordinate_end = descend_boundary_state_receiver != 0U
        ? boundary_state_count : source_state_coordinate + 1U;
    for (uint32_t coordinate = coordinate_begin; coordinate < coordinate_end; ++coordinate) {
      const uint32_t source_state = boundary_states[coordinate];
      const uint32_t restriction = port * boundary_state_count + coordinate;
      for (uint32_t relational_state = 0U;
           relational_state < relational_state_count; ++relational_state) {
        if (relational_state_present[relational_state] == 0U
            || relational_states[relational_state] != source_state) continue;
        if (restriction_present[restriction] == 0U) continue;
        const uint64_t relational_base =
            ((uint64_t)relational_state * (uint64_t)generator_count + generator)
                * (uint64_t)factor_count;
        const uint64_t restriction_base =
            (uint64_t)restriction * (uint64_t)factor_count
                * (uint64_t)restriction_limb_count;
        for (uint32_t factor = 0U; factor < factor_count; ++factor) {
            const uint32_t *restriction_value = restriction_current_limbs + restriction_base
                + (uint64_t)factor * (uint64_t)restriction_limb_count;
            if (unsigned_limbs_are_zero(restriction_value, restriction_limb_count)) continue;
            const uint64_t relational = relational_base + factor;
            const uint8_t component_signs[2] = {
                relational_real_sign[relational],
                relational_imaginary_sign[relational]
            };
            const uint32_t *component_limbs[2] = {
                relational_real_limbs + relational * (uint64_t)relational_limb_count,
                relational_imaginary_limbs + relational * (uint64_t)relational_limb_count
            };
            for (uint32_t component = 0U; component < 2U; ++component) {
                if (component_signs[component] == 0U
                    || unsigned_limbs_are_zero(component_limbs[component], relational_limb_count)) {
                    continue;
                }
                multiply_unsigned_limbs(
                    restriction_value, restriction_limb_count,
                    component_limbs[component], relational_limb_count,
                    first, output_limb_count);
                multiply_unsigned_limbs(
                    first, output_limb_count,
                    first, output_limb_count,
                    second, output_limb_count);
                add_unsigned_limbs(output, second, output_limb_count);
            }
        }
      }
    }
}

extern "C" __global__ void reduce_membrane_factorized_relational_moment_components(
    const uint32_t *partial_overlap_limbs,
    const uint32_t *partial_target_norm_limbs,
    const uint32_t *relational_norm_limbs,
    const uint8_t *context_state_present,
    const uint32_t *context_states,
    const uint32_t *boundary_states,
    uint8_t *compatibility_signs,
    uint32_t *compatibility_limbs,
    uint32_t *norm_limbs,
    uint32_t *first_scratch,
    uint32_t *second_scratch,
    uint32_t *third_scratch,
    uint32_t face_count,
    uint32_t context_count,
    uint32_t port_count,
    uint32_t generator_count,
    uint32_t boundary_state_count,
    uint32_t component_count,
    uint32_t relational_component,
    uint32_t limb_count,
    uint32_t descend_boundary_state_receiver)
{
    const uint32_t face = blockIdx.x * blockDim.x + threadIdx.x;
    if (face >= face_count || relational_component >= component_count
        || generator_count == 0U || boundary_state_count == 0U) return;
    const uint32_t local_face_count = port_count * generator_count;
    if (local_face_count == 0U) return;
    const uint32_t source_state_coordinate = face / local_face_count;
    const uint32_t local_face = face % local_face_count;
    const uint32_t response_state_count = descend_boundary_state_receiver != 0U
        ? 1U : boundary_state_count;
    if (source_state_coordinate >= response_state_count) return;
    const uint64_t component =
        (uint64_t)face * (uint64_t)component_count + relational_component;
    uint32_t *overlap = compatibility_limbs + component * (uint64_t)limb_count;
    uint32_t *norm = norm_limbs + component * (uint64_t)limb_count;
    uint32_t *target_norm = first_scratch + (uint64_t)face * (uint64_t)limb_count;
    uint32_t *denominator = second_scratch + (uint64_t)face * (uint64_t)limb_count;
    uint32_t *square = third_scratch + (uint64_t)face * (uint64_t)limb_count;
    zero_unsigned_limbs(overlap, limb_count);
    zero_unsigned_limbs(norm, limb_count);
    zero_unsigned_limbs(target_norm, limb_count);
    for (uint32_t context = 0U; context < context_count; ++context) {
        if (context_state_present[context] == 0U) continue;
        if (descend_boundary_state_receiver == 0U
            && context_states[context] != boundary_states[source_state_coordinate]) continue;
        const uint64_t partial =
            ((uint64_t)context * (uint64_t)local_face_count + local_face)
                * (uint64_t)limb_count;
        add_unsigned_limbs(overlap, partial_overlap_limbs + partial, limb_count);
        add_unsigned_limbs(
            target_norm, partial_target_norm_limbs + partial, limb_count);
    }
    multiply_unsigned_limbs(
        target_norm, limb_count,
        relational_norm_limbs + (uint64_t)face * (uint64_t)limb_count,
        limb_count,
        denominator, limb_count);
    multiply_unsigned_limbs(
        denominator, limb_count,
        denominator, limb_count,
        square, limb_count);
    for (uint32_t limb = 0U; limb < limb_count; ++limb) norm[limb] = square[limb];
    compatibility_signs[component] =
        unsigned_limbs_are_zero(overlap, limb_count) ? 0U : 1U;
}

extern "C" __global__ void reduce_membrane_factorized_relational_oriented_components(
    const uint8_t *partial_real_signs,
    const uint32_t *partial_real_limbs,
    const uint8_t *partial_imaginary_signs,
    const uint32_t *partial_imaginary_limbs,
    const uint8_t *context_state_present,
    const uint32_t *context_states,
    const uint32_t *boundary_states,
    uint8_t *oriented_real_signs,
    uint32_t *oriented_real_limbs,
    uint8_t *oriented_imaginary_signs,
    uint32_t *oriented_imaginary_limbs,
    uint32_t face_count,
    uint32_t context_count,
    uint32_t port_count,
    uint32_t generator_count,
    uint32_t boundary_state_count,
    uint32_t limb_count,
    uint32_t descend_boundary_state_receiver)
{
    const uint32_t face = blockIdx.x * blockDim.x + threadIdx.x;
    if (face >= face_count || generator_count == 0U || boundary_state_count == 0U) return;
    const uint32_t local_face_count = port_count * generator_count;
    if (local_face_count == 0U) return;
    const uint32_t source_state_coordinate = face / local_face_count;
    const uint32_t local_face = face % local_face_count;
    const uint32_t response_state_count = descend_boundary_state_receiver != 0U
        ? 1U : boundary_state_count;
    if (source_state_coordinate >= response_state_count) return;
    uint32_t *real = oriented_real_limbs + (uint64_t)face * limb_count;
    uint32_t *imaginary = oriented_imaginary_limbs + (uint64_t)face * limb_count;
    zero_unsigned_limbs(real, limb_count);
    zero_unsigned_limbs(imaginary, limb_count);
    oriented_real_signs[face] = 0U;
    oriented_imaginary_signs[face] = 0U;
    for (uint32_t context = 0U; context < context_count; ++context) {
        if (context_state_present[context] == 0U) continue;
        if (descend_boundary_state_receiver == 0U
            && context_states[context] != boundary_states[source_state_coordinate]) continue;
        const uint64_t partial = (uint64_t)context * local_face_count + local_face;
        add_signed_magnitude(
            oriented_real_signs + face,
            real,
            partial_real_signs[partial],
            partial_real_limbs + partial * limb_count,
            limb_count);
        add_signed_magnitude(
            oriented_imaginary_signs + face,
            imaginary,
            partial_imaginary_signs[partial],
            partial_imaginary_limbs + partial * limb_count,
            limb_count);
    }
}

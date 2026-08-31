// Membrane sparse quadratic transport.
// This fragment is included by refine_shell.cu after refine_shared.cuh.

extern "C" __global__ void transport_membrane_sparse_quadratic_pairs(
    const uint64_t *target_offsets,
    const uint32_t *source_pairs,
    const uint8_t *multiplicities,
    const uint32_t *source_limbs,
    uint32_t *target_limbs,
    uint32_t pair_count,
    uint32_t source_limb_count,
    uint32_t target_limb_count)
{
    const uint32_t target = blockIdx.x * blockDim.x + threadIdx.x;
    if (target >= pair_count) return;
    uint32_t *output = target_limbs + (uint64_t)target * target_limb_count;
    for (uint32_t limb = 0; limb < target_limb_count; ++limb) output[limb] = 0;
    for (uint64_t edge = target_offsets[target]; edge < target_offsets[target + 1]; ++edge) {
        const uint32_t source = source_pairs[edge];
        const uint32_t *input = source_limbs + (uint64_t)source * source_limb_count;
        uint64_t carry = 0;
        for (uint32_t limb = 0; limb < target_limb_count; ++limb) {
            const uint64_t source_value = limb < source_limb_count ? input[limb] : 0;
            const unsigned __int128 sum =
                (unsigned __int128)output[limb]
                + (unsigned __int128)source_value * (unsigned __int128)multiplicities[edge]
                + (unsigned __int128)carry;
            output[limb] = (uint32_t)sum;
            carry = (uint64_t)(sum >> 32);
        }
    }
}

extern "C" __global__ void form_membrane_sparse_quadratic_diagonal_chronology(
    const uint32_t *pair_factors,
    const uint32_t *diagonal_currents,
    uint32_t *standing_limbs,
    uint32_t *accumulated_limbs,
    uint32_t *overflow,
    uint32_t pair_count,
    uint32_t factor_count,
    uint32_t chronology_count,
    uint32_t coefficient_limb_count)
{
    const uint32_t pair = blockIdx.x * blockDim.x + threadIdx.x;
    if (pair >= pair_count) return;
    const uint32_t left = pair_factors[(uint64_t)pair * 2ULL];
    const uint32_t right = pair_factors[(uint64_t)pair * 2ULL + 1ULL];
    if (left >= factor_count || right >= factor_count || left > right) {
        atomicExch(overflow, 1U);
        return;
    }
    uint32_t *standing = standing_limbs + (uint64_t)pair * coefficient_limb_count;
    uint32_t *accumulated = accumulated_limbs + (uint64_t)pair * coefficient_limb_count;
    zero_unsigned_limbs(standing, coefficient_limb_count);
    zero_unsigned_limbs(accumulated, coefficient_limb_count);
    for (uint32_t order = 0U; order < chronology_count; ++order) {
        const uint64_t diagonal_at = (uint64_t)order * factor_count;
        const uint64_t scale = (uint64_t)diagonal_currents[diagonal_at + left]
            * (uint64_t)diagonal_currents[diagonal_at + right];
        if (scale == 0ULL) {
            zero_unsigned_limbs(standing, coefficient_limb_count);
            continue;
        }

        uint64_t carry = 1ULL;
        for (uint32_t limb = 0U; limb < coefficient_limb_count && carry != 0ULL; ++limb) {
            const uint64_t sum = (uint64_t)standing[limb] + carry;
            standing[limb] = (uint32_t)sum;
            carry = sum >> 32U;
        }
        if (carry != 0ULL) {
            atomicExch(overflow, 1U);
            return;
        }

        carry = 0ULL;
        for (uint32_t limb = 0U; limb < coefficient_limb_count; ++limb) {
            const unsigned __int128 product =
                (unsigned __int128)standing[limb] * (unsigned __int128)scale
                + (unsigned __int128)carry;
            standing[limb] = (uint32_t)product;
            carry = (uint64_t)(product >> 32U);
        }
        if (carry != 0ULL) {
            atomicExch(overflow, 1U);
            return;
        }

        carry = 0ULL;
        for (uint32_t limb = 0U; limb < coefficient_limb_count; ++limb) {
            const uint64_t sum = (uint64_t)accumulated[limb]
                + (uint64_t)standing[limb] + carry;
            accumulated[limb] = (uint32_t)sum;
            carry = sum >> 32U;
        }
        if (carry != 0ULL) {
            atomicExch(overflow, 1U);
            return;
        }
    }
}

extern "C" __global__ void transport_membrane_sparse_quadratic_generator_pairs(
    const uint64_t *generator_target_offsets,
    const uint32_t *generator_source_pairs,
    const uint8_t *generator_multiplicities,
    const uint32_t *source_limbs,
    uint32_t *target_limbs,
    uint32_t generator_count,
    uint32_t pair_count,
    uint32_t source_limb_count,
    uint32_t target_limb_count)
{
    const uint64_t at = (uint64_t)blockIdx.x * blockDim.x + threadIdx.x;
    const uint64_t work = (uint64_t)generator_count * pair_count;
    if (at >= work) return;
    const uint32_t generator = (uint32_t)(at / pair_count);
    const uint32_t target = (uint32_t)(at % pair_count);
    uint32_t *output = target_limbs + at * target_limb_count;
    zero_unsigned_limbs(output, target_limb_count);
    const uint64_t offset_base = (uint64_t)generator * (pair_count + 1ULL);
    for (uint64_t edge = generator_target_offsets[offset_base + target];
         edge < generator_target_offsets[offset_base + target + 1ULL]; ++edge) {
        const uint32_t source = generator_source_pairs[edge];
        const uint32_t *input = source_limbs + (uint64_t)source * source_limb_count;
        uint64_t carry = 0ULL;
        for (uint32_t limb = 0U; limb < target_limb_count; ++limb) {
            const uint64_t source_value = limb < source_limb_count ? input[limb] : 0ULL;
            const unsigned __int128 sum = (unsigned __int128)output[limb]
                + (unsigned __int128)source_value * generator_multiplicities[edge]
                + (unsigned __int128)carry;
            output[limb] = (uint32_t)sum;
            carry = (uint64_t)(sum >> 32);
        }
    }
}

extern "C" __global__ void resolve_membrane_sparse_quadratic_returned_port(
    const uint8_t *situated_front,
    uint32_t *selection,
    uint32_t port_count)
{
    if (blockIdx.x != 0U || threadIdx.x != 0U) return;
    uint32_t selected = 0U;
    uint32_t population = 0U;
    for (uint32_t port = 0U; port < port_count; ++port) {
        if (situated_front[port] == 0U) continue;
        selected = port;
        ++population;
    }
    selection[0] = selected;
    selection[1] = population;
}

extern "C" __global__ void lift_membrane_phase_front_to_addressed_faces(
    const uint8_t *port_front,
    const uint32_t *face_ports,
    const uint8_t *face_present,
    uint8_t *face_front,
    uint32_t port_count,
    uint32_t face_count)
{
    const uint32_t face = blockIdx.x * blockDim.x + threadIdx.x;
    if (face >= face_count) return;
    const uint32_t port = face_ports[face];
    face_front[face] =
        port < port_count && face_present[face] != 0U ? port_front[port] : 0U;
}

extern "C" __global__ void condition_membrane_sparse_quadratic_pairs_by_returned_port(
    const uint32_t *pair_factors,
    const uint32_t *restriction_limbs,
    const uint32_t *source_limbs,
    const uint32_t *selection,
    uint32_t *target_limbs,
    uint32_t *scratch_limbs,
    uint32_t pair_count,
    uint32_t factor_count,
    uint32_t port_count,
    uint32_t source_limb_count,
    uint32_t restriction_limb_count,
    uint32_t target_limb_count)
{
    const uint32_t pair = blockIdx.x * blockDim.x + threadIdx.x;
    if (pair >= pair_count) return;
    const uint32_t *source = source_limbs + (uint64_t)pair * source_limb_count;
    uint32_t *target = target_limbs + (uint64_t)pair * target_limb_count;
    uint32_t *scratch = scratch_limbs + (uint64_t)pair * target_limb_count;
    if (selection[1] != 1U || selection[0] >= port_count) {
        for (uint32_t limb = 0U; limb < target_limb_count; ++limb) {
            target[limb] = limb < source_limb_count ? source[limb] : 0U;
            scratch[limb] = 0U;
        }
        return;
    }
    const uint32_t left = pair_factors[(uint64_t)pair * 2ULL];
    const uint32_t right = pair_factors[(uint64_t)pair * 2ULL + 1ULL];
    if (left >= factor_count || right >= factor_count) {
        for (uint32_t limb = 0U; limb < target_limb_count; ++limb) {
            target[limb] = 0U;
            scratch[limb] = 0U;
        }
        return;
    }
    const uint64_t port_base =
        (uint64_t)selection[0] * (uint64_t)factor_count * (uint64_t)restriction_limb_count;
    const uint32_t *left_restriction =
        restriction_limbs + port_base + (uint64_t)left * restriction_limb_count;
    const uint32_t *right_restriction =
        restriction_limbs + port_base + (uint64_t)right * restriction_limb_count;
    multiply_unsigned_limbs(
        source, source_limb_count,
        left_restriction, restriction_limb_count,
        target, target_limb_count);
    multiply_unsigned_limbs(
        target, target_limb_count,
        right_restriction, restriction_limb_count,
        scratch, target_limb_count);
    for (uint32_t limb = 0U; limb < target_limb_count; ++limb) target[limb] = scratch[limb];
}

extern "C" __global__ void condition_membrane_sparse_quadratic_pairs_by_returned_faces(
    const uint32_t *pair_factors,
    const uint32_t *face_restriction_limbs,
    const uint32_t *face_source_limbs,
    const uint8_t *situated_front,
    uint32_t *target_limbs,
    uint32_t *first_scratch_limbs,
    uint32_t *second_scratch_limbs,
    uint32_t pair_count,
    uint32_t factor_count,
    uint32_t face_count,
    uint32_t generator_count,
    uint32_t source_limb_count,
    uint32_t restriction_limb_count,
    uint32_t target_limb_count)
{
    const uint32_t pair = blockIdx.x * blockDim.x + threadIdx.x;
    if (pair >= pair_count) return;
    uint32_t *target = target_limbs + (uint64_t)pair * target_limb_count;
    uint32_t *first = first_scratch_limbs + (uint64_t)pair * target_limb_count;
    uint32_t *second = second_scratch_limbs + (uint64_t)pair * target_limb_count;
    zero_unsigned_limbs(target, target_limb_count);
    const uint32_t left = pair_factors[(uint64_t)pair * 2ULL];
    const uint32_t right = pair_factors[(uint64_t)pair * 2ULL + 1ULL];
    if (left >= factor_count || right >= factor_count) return;
    if (generator_count == 0U) return;
    for (uint32_t face = 0U; face < face_count; ++face) {
        if (situated_front[face] == 0U) continue;
        const uint64_t restriction_base =
            (uint64_t)face * factor_count * restriction_limb_count;
        const uint32_t generator = face % generator_count;
        const uint32_t *source = face_source_limbs
            + ((uint64_t)generator * pair_count + pair) * source_limb_count;
        multiply_unsigned_limbs(
            source, source_limb_count,
            face_restriction_limbs + restriction_base
                + (uint64_t)left * restriction_limb_count,
            restriction_limb_count,
            first, target_limb_count);
        multiply_unsigned_limbs(
            first, target_limb_count,
            face_restriction_limbs + restriction_base
                + (uint64_t)right * restriction_limb_count,
            restriction_limb_count,
            second, target_limb_count);
        add_unsigned_limbs(target, second, target_limb_count);
    }
}

extern "C" __global__ void contract_membrane_sparse_quadratic_pair_receivers(
    const uint64_t *receiver_offsets,
    const uint32_t *pair_coordinates,
    const uint8_t *coefficient_signs,
    const uint32_t *coefficient_limbs,
    const uint32_t *pair_current_limbs,
    uint8_t *output_signs,
    uint32_t *output_limbs,
    uint32_t receiver_count,
    uint32_t coefficient_limb_count,
    uint32_t current_limb_count,
    uint32_t output_limb_count)
{
    const uint32_t receiver = blockIdx.x;
    if (receiver >= receiver_count) return;
    const uint32_t lane = threadIdx.x;
    extern __shared__ unsigned char shared_octets[];
    const uint32_t sign_octets = (blockDim.x + 3U) & ~3U;
    uint8_t *local_signs = (uint8_t *)shared_octets;
    uint32_t *local_limbs = (uint32_t *)(shared_octets + sign_octets);
    const uint64_t lane_width = (uint64_t)output_limb_count;
    uint32_t *accumulator = local_limbs + (uint64_t)lane * lane_width * 2ULL;
    uint32_t *product = accumulator + lane_width;
    local_signs[lane] = 0U;
    zero_unsigned_limbs(accumulator, output_limb_count);
    zero_unsigned_limbs(product, output_limb_count);

    for (uint64_t term = receiver_offsets[receiver] + lane;
         term < receiver_offsets[receiver + 1]; term += blockDim.x) {
        multiply_unsigned_limbs(
            coefficient_limbs + term * (uint64_t)coefficient_limb_count,
            coefficient_limb_count,
            pair_current_limbs + (uint64_t)pair_coordinates[term] * current_limb_count,
            current_limb_count,
            product,
            output_limb_count);
        add_signed_magnitude(
            local_signs + lane,
            accumulator,
            coefficient_signs[term],
            product,
            output_limb_count);
    }
    __syncthreads();

    uint32_t active = blockDim.x;
    while (active > 1U) {
        const uint32_t half = (active + 1U) >> 1U;
        if (lane < half) {
            const uint32_t partner = lane + half;
            if (partner < active) {
                uint32_t *partner_accumulator =
                    local_limbs + (uint64_t)partner * lane_width * 2ULL;
                add_signed_magnitude(
                    local_signs + lane,
                    accumulator,
                    local_signs[partner],
                    partner_accumulator,
                    output_limb_count);
            }
        }
        __syncthreads();
        active = half;
    }

    if (lane == 0U) {
        uint32_t *output = output_limbs + (uint64_t)receiver * output_limb_count;
        output_signs[receiver] = local_signs[0];
        for (uint32_t limb = 0U; limb < output_limb_count; ++limb) {
            output[limb] = accumulator[limb];
        }
    }
}

extern "C" __global__ void form_membrane_sparse_quadratic_situated_chunks(
    const uint32_t *pair_factors,
    const uint32_t *current_limbs,
    const uint32_t *ingress_receiver_limbs,
    const uint32_t *restriction_limbs,
    uint32_t *partial_limbs,
    uint32_t *product_first_scratch,
    uint32_t *product_second_scratch,
    uint32_t pair_count,
    uint32_t factor_count,
    uint32_t port_count,
    uint32_t chunk_count,
    uint32_t chunk_size,
    uint32_t current_limb_count,
    uint32_t ingress_receiver_limb_count,
    uint32_t restriction_limb_count,
    uint32_t output_limb_count)
{
    const uint32_t at = blockIdx.x * blockDim.x + threadIdx.x;
    const uint64_t work = (uint64_t)port_count * (uint64_t)chunk_count;
    if ((uint64_t)at >= work) return;
    const uint32_t port = at / chunk_count;
    const uint32_t chunk = at % chunk_count;
    const uint64_t output_at = (uint64_t)at * (uint64_t)output_limb_count;
    uint32_t *accumulator = partial_limbs + output_at;
    uint32_t *first = product_first_scratch + output_at;
    uint32_t *second = product_second_scratch + output_at;
    zero_unsigned_limbs(accumulator, output_limb_count);
    zero_unsigned_limbs(first, output_limb_count);
    zero_unsigned_limbs(second, output_limb_count);
    const uint64_t begin = (uint64_t)chunk * (uint64_t)chunk_size;
    uint64_t end = begin + chunk_size;
    if (end > pair_count) end = pair_count;
    const uint64_t restriction_base =
        (uint64_t)port * (uint64_t)factor_count * (uint64_t)restriction_limb_count;
    for (uint64_t pair = begin; pair < end; ++pair) {
        const uint32_t left = pair_factors[pair * 2ULL];
        const uint32_t right = pair_factors[pair * 2ULL + 1ULL];
        if (left >= factor_count || right >= factor_count) continue;
        multiply_unsigned_limbs(
            current_limbs + pair * (uint64_t)current_limb_count,
            current_limb_count,
            ingress_receiver_limbs + pair * (uint64_t)ingress_receiver_limb_count,
            ingress_receiver_limb_count,
            first,
            output_limb_count);
        multiply_unsigned_limbs(
            first,
            output_limb_count,
            restriction_limbs + restriction_base
                + (uint64_t)left * (uint64_t)restriction_limb_count,
            restriction_limb_count,
            second,
            output_limb_count);
        multiply_unsigned_limbs(
            second,
            output_limb_count,
            restriction_limbs + restriction_base
                + (uint64_t)right * (uint64_t)restriction_limb_count,
            restriction_limb_count,
            first,
            output_limb_count);
        add_unsigned_limbs(accumulator, first, output_limb_count);
        if (left != right) add_unsigned_limbs(accumulator, first, output_limb_count);
    }
}

extern "C" __global__ void reduce_membrane_sparse_quadratic_situated_chunks(
    const uint32_t *input_limbs,
    uint32_t *output_limbs,
    uint32_t port_count,
    uint32_t input_count_per_port,
    uint32_t output_count_per_port,
    uint32_t chunk_size,
    uint32_t limb_count)
{
    const uint32_t at = blockIdx.x * blockDim.x + threadIdx.x;
    const uint64_t work = (uint64_t)port_count * (uint64_t)output_count_per_port;
    if ((uint64_t)at >= work) return;
    const uint32_t port = at / output_count_per_port;
    const uint32_t chunk = at % output_count_per_port;
    const uint64_t output_at = (uint64_t)at * (uint64_t)limb_count;
    uint32_t *output = output_limbs + output_at;
    zero_unsigned_limbs(output, limb_count);
    const uint64_t begin = (uint64_t)chunk * (uint64_t)chunk_size;
    uint64_t end = begin + chunk_size;
    if (end > input_count_per_port) end = input_count_per_port;
    const uint64_t input_base =
        (uint64_t)port * (uint64_t)input_count_per_port * (uint64_t)limb_count;
    for (uint64_t input = begin; input < end; ++input) {
        add_unsigned_limbs(
            output,
            input_limbs + input_base + input * (uint64_t)limb_count,
            limb_count);
    }
}

extern "C" __global__ void mark_membrane_sparse_quadratic_situated_signs(
    const uint32_t *pairing_limbs,
    uint8_t *pairing_signs,
    uint32_t port_count,
    uint32_t limb_count)
{
    const uint32_t port = blockIdx.x * blockDim.x + threadIdx.x;
    if (port >= port_count) return;
    pairing_signs[port] = unsigned_limbs_are_zero(
        pairing_limbs + (uint64_t)port * (uint64_t)limb_count,
        limb_count) ? 0U : 1U;
}

extern "C" __global__ void form_membrane_sparse_quadratic_native_family_chunks(
    const uint64_t *pair_row_offsets,
    const uint32_t *pair_factors,
    const uint32_t *current_limbs,
    const uint32_t *restriction_limbs,
    const uint8_t *restriction_present,
    const uint32_t *generator_targets,
    const uint64_t *factor_capacity,
    const int8_t *family_orientation,
    uint8_t *partial_signs,
    uint32_t *partial_limbs,
    uint32_t *product_scratch,
    uint32_t *scaled_scratch,
    uint32_t port_count,
    uint32_t source_state_count,
    uint32_t factor_count,
    uint32_t family_count,
    uint32_t generator_count,
    uint32_t chunk_count,
    uint32_t chunk_size,
    uint32_t current_limb_count,
    uint32_t restriction_limb_count,
    uint32_t output_limb_count,
    uint32_t *obstruction)
{
    const uint64_t at = (uint64_t)blockIdx.x * blockDim.x + threadIdx.x;
    const uint64_t work =
        (uint64_t)port_count * (uint64_t)family_count * (uint64_t)chunk_count;
    if (at >= work) return;
    const uint32_t chunk = (uint32_t)(at % chunk_count);
    const uint64_t port_family = at / chunk_count;
    const uint32_t family = (uint32_t)(port_family % family_count);
    const uint32_t face = (uint32_t)(port_family / family_count);
    const uint32_t carried_generator = face % generator_count;
    const uint32_t family_axis_count = family_count * 2U;
    const uint64_t reflected_section =
        (uint64_t)face * family_axis_count + family;
    const uint64_t action_section = reflected_section + family_count;
    const uint64_t reflected_partial =
        reflected_section * chunk_count + chunk;
    const uint64_t action_partial = action_section * chunk_count + chunk;
    uint8_t *reflected_sign = partial_signs + reflected_partial;
    uint8_t *action_sign = partial_signs + action_partial;
    uint32_t *reflected = partial_limbs
        + reflected_partial * (uint64_t)output_limb_count;
    uint32_t *action = partial_limbs
        + action_partial * (uint64_t)output_limb_count;
    *reflected_sign = 0U;
    *action_sign = 0U;
    zero_unsigned_limbs(reflected, output_limb_count);
    zero_unsigned_limbs(action, output_limb_count);
    if (restriction_present[face] == 0U) return;
    if (source_state_count == 0U || port_count % source_state_count != 0U) {
        atomicExch(obstruction, 1U);
        return;
    }
    uint32_t *product = product_scratch + at * (uint64_t)output_limb_count;
    uint32_t *scaled = scaled_scratch + at * (uint64_t)output_limb_count;
    const uint64_t restriction_base =
        (uint64_t)face * factor_count * restriction_limb_count;
    const uint32_t faces_per_state = port_count / source_state_count;
    const uint32_t source_state = face / faces_per_state;
    const uint64_t current_base =
        ((uint64_t)source_state * generator_count + carried_generator)
        * pair_row_offsets[factor_count] * current_limb_count;
    const uint64_t begin = (uint64_t)chunk * chunk_size;
    uint64_t end = begin + chunk_size;
    if (end > factor_count) end = factor_count;
    for (uint64_t source64 = begin; source64 < end; ++source64) {
        const uint32_t source = (uint32_t)source64;
        const uint32_t *source_restriction = restriction_limbs + restriction_base
            + source64 * restriction_limb_count;
        if (unsigned_limbs_are_zero(source_restriction, restriction_limb_count)) continue;
        const int64_t diagonal = find_membrane_sparse_quadratic_pair(
            pair_row_offsets, pair_factors, source, source);
        if (diagonal >= 0) {
            const uint32_t *moment = current_limbs + current_base
                + (uint64_t)diagonal * current_limb_count;
            multiply_unsigned_limbs(
                moment, current_limb_count,
                source_restriction, restriction_limb_count,
                product, output_limb_count);
            multiply_unsigned_limbs(
                product, output_limb_count,
                source_restriction, restriction_limb_count,
                scaled, output_limb_count);
            const int8_t orientation = family_orientation[
                (uint64_t)family * factor_count + source];
            const uint8_t sign = orientation < 0 ? 2U : (orientation > 0 ? 1U : 0U);
            if (sign != 0U) {
                scale_unsigned_limbs(
                    scaled, output_limb_count,
                    factor_capacity[source], product, output_limb_count);
                for (uint32_t generator = 0U; generator < generator_count; ++generator) {
                    add_signed_magnitude(
                        reflected_sign, reflected, sign, product, output_limb_count);
                    add_signed_magnitude(
                        action_sign, action, opposite_sign(sign), product,
                        output_limb_count);
                }
            }
        }
        for (uint32_t generator = 0U; generator < generator_count; ++generator) {
            const uint32_t target = generator_targets[
                (uint64_t)generator * factor_count + source];
            if (target >= factor_count) {
                atomicExch(obstruction, 1U);
                return;
            }
            const uint32_t *target_restriction = restriction_limbs + restriction_base
                + (uint64_t)target * restriction_limb_count;
            if (unsigned_limbs_are_zero(target_restriction, restriction_limb_count)) continue;
            const int64_t pair = find_membrane_sparse_quadratic_pair(
                pair_row_offsets, pair_factors, source, target);
            if (pair < 0) continue;
            multiply_unsigned_limbs(
                current_limbs + current_base + (uint64_t)pair * current_limb_count,
                current_limb_count,
                source_restriction, restriction_limb_count,
                product, output_limb_count);
            multiply_unsigned_limbs(
                product, output_limb_count,
                target_restriction, restriction_limb_count,
                scaled, output_limb_count);
            scale_unsigned_limbs(
                scaled, output_limb_count,
                factor_capacity[target], product, output_limb_count);
            const int8_t target_orientation = family_orientation[
                (uint64_t)family * factor_count + target];
            const uint8_t target_sign = target_orientation < 0
                ? 2U : (target_orientation > 0 ? 1U : 0U);
            add_signed_magnitude(
                action_sign, action, target_sign, product, output_limb_count);
        }
    }
}

extern "C" __global__ void form_membrane_sparse_quadratic_native_potential_chunks(
    const uint32_t *pair_factors,
    const uint32_t *current_limbs,
    const uint32_t *ingress_receiver_limbs,
    const uint32_t *restriction_limbs,
    const uint8_t *restriction_present,
    const uint32_t *generator_targets,
    const uint32_t *factor_receiver_classes,
    uint8_t *partial_signs,
    uint32_t *partial_limbs,
    uint32_t *product_first_scratch,
    uint32_t *product_second_scratch,
    uint32_t pair_count,
    uint32_t factor_count,
    uint32_t port_count,
    uint32_t source_state_count,
    uint32_t receiver_count,
    uint32_t generator_count,
    uint32_t chunk_count,
    uint32_t chunk_size,
    uint32_t current_limb_count,
    uint32_t ingress_receiver_limb_count,
    uint32_t restriction_limb_count,
    uint32_t output_limb_count,
    uint32_t *obstruction)
{
    const uint64_t at = (uint64_t)blockIdx.x * blockDim.x + threadIdx.x;
    const uint64_t work = (uint64_t)port_count * chunk_count;
    if (at >= work) return;
    const uint32_t face = (uint32_t)(at / chunk_count);
    const uint32_t carried_generator = face % generator_count;
    const uint32_t chunk = (uint32_t)(at % chunk_count);
    const uint32_t axis_count = receiver_count * 2U;
    const uint64_t section_base = (uint64_t)face * axis_count;
    for (uint32_t axis = 0U; axis < axis_count; ++axis) {
        const uint64_t partial = (section_base + axis) * chunk_count + chunk;
        partial_signs[partial] = 0U;
        zero_unsigned_limbs(
            partial_limbs + partial * (uint64_t)output_limb_count,
            output_limb_count);
    }
    if (restriction_present[face] == 0U) return;
    if (source_state_count == 0U || port_count % source_state_count != 0U) {
        atomicExch(obstruction, 1U);
        return;
    }
    uint32_t *first = product_first_scratch + at * (uint64_t)output_limb_count;
    uint32_t *second = product_second_scratch + at * (uint64_t)output_limb_count;
    const uint64_t restriction_base =
        (uint64_t)face * factor_count * restriction_limb_count;
    const uint32_t faces_per_state = port_count / source_state_count;
    const uint32_t source_state = face / faces_per_state;
    const uint64_t current_base =
        ((uint64_t)source_state * generator_count + carried_generator)
        * pair_count * current_limb_count;
    const uint32_t current_once_limbs = current_limb_count + restriction_limb_count
        < output_limb_count
        ? current_limb_count + restriction_limb_count
        : output_limb_count;
    const uint64_t begin = (uint64_t)chunk * chunk_size;
    uint64_t end = begin + chunk_size;
    if (end > pair_count) end = pair_count;
    for (uint64_t pair = begin; pair < end; ++pair) {
        const uint32_t left = pair_factors[pair * 2ULL];
        const uint32_t right = pair_factors[pair * 2ULL + 1ULL];
        if (left >= factor_count || right >= factor_count) {
            atomicExch(obstruction, 1U);
            return;
        }
        const uint32_t *left_restriction = restriction_limbs + restriction_base
            + (uint64_t)left * restriction_limb_count;
        const uint32_t *right_restriction = restriction_limbs + restriction_base
            + (uint64_t)right * restriction_limb_count;
        if (unsigned_limbs_are_zero(left_restriction, restriction_limb_count)
            || unsigned_limbs_are_zero(right_restriction, restriction_limb_count)) continue;
        multiply_unsigned_limbs(
            current_limbs + current_base + pair * (uint64_t)current_limb_count,
            current_limb_count,
            left_restriction, restriction_limb_count,
            first, output_limb_count);
        multiply_unsigned_limbs(
            first, current_once_limbs,
            right_restriction, restriction_limb_count,
            second, output_limb_count);
        if (unsigned_limbs_are_zero(second, output_limb_count)) continue;
        const bool diagonal = left == right;
        for (uint32_t receiver = 0U; receiver < receiver_count; ++receiver) {
            int32_t overlap_coefficient = 0;
            int32_t norm_coefficient = 0;
            const uint32_t left_source = factor_receiver_classes[
                (uint64_t)left * receiver_count + receiver];
            const uint32_t right_source = factor_receiver_classes[
                (uint64_t)right * receiver_count + receiver];
            for (uint32_t generator = 0U; generator < generator_count; ++generator) {
                const uint32_t target_left = generator_targets[
                    (uint64_t)generator * factor_count + left];
                const uint32_t target_right = generator_targets[
                    (uint64_t)generator * factor_count + right];
                if (target_left >= factor_count || target_right >= factor_count) {
                    atomicExch(obstruction, 1U);
                    return;
                }
                const uint32_t left_target = factor_receiver_classes[
                    (uint64_t)target_left * receiver_count + receiver];
                const uint32_t right_target = factor_receiver_classes[
                    (uint64_t)target_right * receiver_count + receiver];
                overlap_coefficient += membrane_receiver_class_delta(
                    left_source, right_source, left_target, right_target,
                    diagonal, false);
                norm_coefficient += membrane_receiver_class_delta(
                    left_source, right_source, left_target, right_target,
                    diagonal, true);
            }
            const int32_t coefficients[2] = { overlap_coefficient, norm_coefficient };
            for (uint32_t kind = 0U; kind < 2U; ++kind) {
                const int32_t coefficient = coefficients[kind];
                if (coefficient == 0) continue;
                scale_unsigned_limbs(
                    second, output_limb_count,
                    (uint64_t)(coefficient < 0 ? -coefficient : coefficient),
                    first, output_limb_count);
                const uint32_t axis = receiver * 2U + kind;
                const uint64_t partial = (section_base + axis) * chunk_count + chunk;
                add_signed_magnitude(
                    partial_signs + partial,
                    partial_limbs + partial * (uint64_t)output_limb_count,
                    coefficient < 0 ? 2U : 1U,
                    first,
                    output_limb_count);
            }
        }
    }
}

extern "C" __global__ void form_membrane_sparse_quadratic_situated_front_chunks(
    const uint8_t *native_phase_front,
    const uint32_t *pair_factors,
    const uint32_t *current_limbs,
    const uint32_t *ingress_receiver_limbs,
    const uint32_t *restriction_limbs,
    const uint8_t *restriction_present,
    uint8_t *partial_signs,
    uint32_t *partial_limbs,
    uint32_t *product_first_scratch,
    uint32_t *product_second_scratch,
    uint32_t pair_count,
    uint32_t factor_count,
    uint32_t face_count,
    uint32_t generator_count,
    uint32_t chunk_count,
    uint32_t chunk_size,
    uint32_t current_limb_count,
    uint32_t ingress_receiver_limb_count,
    uint32_t restriction_limb_count,
    uint32_t output_limb_count,
    uint32_t *obstruction)
{
    const uint64_t at = (uint64_t)blockIdx.x * blockDim.x + threadIdx.x;
    const uint64_t work = (uint64_t)face_count * chunk_count;
    if (at >= work) return;
    const uint32_t face = (uint32_t)(at / chunk_count);
    const uint32_t chunk = (uint32_t)(at % chunk_count);
    const uint64_t section_base = (uint64_t)face * 3ULL;
    for (uint32_t axis = 0U; axis < 3U; ++axis) {
        const uint64_t partial = (section_base + axis) * chunk_count + chunk;
        partial_signs[partial] = 0U;
        zero_unsigned_limbs(
            partial_limbs + partial * (uint64_t)output_limb_count,
            output_limb_count);
    }
    if (native_phase_front[face] == 0U) return;
    if (restriction_present[face] == 0U) return;
    const uint32_t carried_generator = face % generator_count;
    uint32_t *first = product_first_scratch + at * (uint64_t)output_limb_count;
    uint32_t *second = product_second_scratch + at * (uint64_t)output_limb_count;
    const uint64_t restriction_base =
        (uint64_t)face * factor_count * restriction_limb_count;
    const uint64_t current_base =
        (uint64_t)carried_generator * pair_count * current_limb_count;
    const uint32_t current_once_limbs = current_limb_count + restriction_limb_count
        < output_limb_count
        ? current_limb_count + restriction_limb_count
        : output_limb_count;
    const uint32_t restricted_current_limbs = current_once_limbs + restriction_limb_count
        < output_limb_count
        ? current_once_limbs + restriction_limb_count
        : output_limb_count;
    const uint32_t ingress_once_limbs =
        ingress_receiver_limb_count + restriction_limb_count < output_limb_count
        ? ingress_receiver_limb_count + restriction_limb_count
        : output_limb_count;
    const uint32_t restricted_ingress_limbs = ingress_once_limbs + restriction_limb_count
        < output_limb_count
        ? ingress_once_limbs + restriction_limb_count
        : output_limb_count;
    const uint64_t begin = (uint64_t)chunk * chunk_size;
    uint64_t end = begin + chunk_size;
    if (end > pair_count) end = pair_count;
    for (uint64_t pair = begin; pair < end; ++pair) {
        const uint32_t left = pair_factors[pair * 2ULL];
        const uint32_t right = pair_factors[pair * 2ULL + 1ULL];
        if (left >= factor_count || right >= factor_count) {
            atomicExch(obstruction, 1U);
            return;
        }
        const uint32_t *left_restriction = restriction_limbs + restriction_base
            + (uint64_t)left * restriction_limb_count;
        const uint32_t *right_restriction = restriction_limbs + restriction_base
            + (uint64_t)right * restriction_limb_count;
        if (unsigned_limbs_are_zero(left_restriction, restriction_limb_count)
            || unsigned_limbs_are_zero(right_restriction, restriction_limb_count)) continue;
        multiply_unsigned_limbs(
            current_limbs + current_base + pair * (uint64_t)current_limb_count,
            current_limb_count,
            left_restriction, restriction_limb_count,
            first, output_limb_count);
        multiply_unsigned_limbs(
            first, output_limb_count,
            right_restriction, restriction_limb_count,
            second, output_limb_count);
        if (unsigned_limbs_are_zero(second, output_limb_count)) continue;
        const bool diagonal = left == right;
        const uint32_t multiplicity = diagonal ? 1U : 2U;
        const uint64_t situated_cross_partial = section_base * chunk_count + chunk;
        const uint64_t situated_current_norm_partial =
            (section_base + 1ULL) * chunk_count + chunk;
        const uint64_t situated_ingress_norm_partial =
            (section_base + 2ULL) * chunk_count + chunk;

        multiply_unsigned_limbs(
            second, restricted_current_limbs,
            ingress_receiver_limbs + pair * (uint64_t)ingress_receiver_limb_count,
            ingress_receiver_limb_count,
            first, output_limb_count);
        for (uint32_t copy = 0U; copy < multiplicity; ++copy) {
            add_signed_magnitude(
                partial_signs + situated_cross_partial,
                partial_limbs + situated_cross_partial * (uint64_t)output_limb_count,
                1U, first, output_limb_count);
        }

        multiply_unsigned_limbs(
            second, restricted_current_limbs,
            second, restricted_current_limbs,
            first, output_limb_count);
        for (uint32_t copy = 0U; copy < multiplicity; ++copy) {
            add_signed_magnitude(
                partial_signs + situated_current_norm_partial,
                partial_limbs + situated_current_norm_partial * (uint64_t)output_limb_count,
                1U, first, output_limb_count);
        }

        // C is port-valued, but the exact-work aperture is face-valued and may retain generator
        // g while excluding generator 0 at the same port.  Form the identical port norm on every
        // retained addressed face; copying from an excluded generator would fabricate a radical.
        multiply_unsigned_limbs(
            ingress_receiver_limbs + pair * (uint64_t)ingress_receiver_limb_count,
            ingress_receiver_limb_count,
            left_restriction, restriction_limb_count,
            first, output_limb_count);
        multiply_unsigned_limbs(
            first, ingress_once_limbs,
            right_restriction, restriction_limb_count,
            second, output_limb_count);
        multiply_unsigned_limbs(
            second, restricted_ingress_limbs,
            second, restricted_ingress_limbs,
            first, output_limb_count);
        for (uint32_t copy = 0U; copy < multiplicity; ++copy) {
            add_signed_magnitude(
                partial_signs + situated_ingress_norm_partial,
                partial_limbs + situated_ingress_norm_partial * (uint64_t)output_limb_count,
                1U, first, output_limb_count);
        }
    }
}

extern "C" __global__ void scatter_membrane_sparse_quadratic_situated_front(
    const uint8_t *section_signs,
    const uint32_t *section_limbs,
    uint8_t *situated_signs,
    uint32_t *situated_limbs,
    uint32_t *situated_current_norm_limbs,
    uint32_t *situated_ingress_norm_limbs,
    uint32_t face_offset,
    uint32_t window_face_count,
    uint32_t generator_count,
    uint32_t limb_count)
{
    const uint32_t local_face = blockIdx.x * blockDim.x + threadIdx.x;
    if (local_face >= window_face_count) return;
    const uint32_t face = face_offset + local_face;
    const uint64_t section = (uint64_t)local_face * 3ULL;
    situated_signs[face] = section_signs[section];
    for (uint32_t limb = 0U; limb < limb_count; ++limb) {
        situated_limbs[(uint64_t)face * limb_count + limb] =
            section_limbs[section * limb_count + limb];
        situated_current_norm_limbs[(uint64_t)face * limb_count + limb] =
            section_limbs[(section + 1ULL) * limb_count + limb];
        situated_ingress_norm_limbs[(uint64_t)face * limb_count + limb] =
            section_limbs[(section + 2ULL) * limb_count + limb];
    }
}

extern "C" __global__ void form_membrane_sparse_quadratic_projective_interval_chunks(
    const uint8_t *native_phase_front,
    const uint32_t *pair_factors,
    const uint32_t *current_limbs,
    const uint32_t *ingress_receiver_limbs,
    const uint32_t *restriction_limbs,
    const uint8_t *restriction_present,
    uint32_t *partial_lower,
    uint32_t *partial_upper,
    uint32_t pair_count,
    uint32_t factor_count,
    uint32_t face_count,
    uint32_t generator_count,
    uint32_t chunk_count,
    uint32_t chunk_size,
    uint32_t current_limb_count,
    uint32_t ingress_receiver_limb_count,
    uint32_t restriction_limb_count,
    uint32_t output_limb_count,
    uint32_t interval_limb_count,
    uint32_t interval_payload_limbs,
    uint32_t *obstruction)
{
    const uint64_t at = (uint64_t)blockIdx.x * blockDim.x + threadIdx.x;
    const uint64_t work = (uint64_t)face_count * chunk_count;
    if (at >= work) return;
    const uint32_t face = (uint32_t)(at / chunk_count);
    const uint32_t chunk = (uint32_t)(at % chunk_count);
    const uint64_t section_base = (uint64_t)face * 3ULL;
    for (uint32_t axis = 0U; axis < 3U; ++axis) {
        const uint64_t partial = (section_base + axis) * chunk_count + chunk;
        zero_unsigned_limbs(
            partial_lower + partial * interval_limb_count, interval_limb_count);
        zero_unsigned_limbs(
            partial_upper + partial * interval_limb_count, interval_limb_count);
    }
    if (restriction_present[face] == 0U) {
        atomicExch(obstruction, 1U);
        return;
    }
    if (native_phase_front[face] == 0U) return;
    if (restriction_limb_count != 1U
        || interval_limb_count < interval_payload_limbs + 1U
        || interval_payload_limbs < MEMBRANE_INTERVAL_CORE_LIMBS) {
        atomicExch(obstruction, 1U);
        return;
    }
    const uint32_t receiver_exponent = output_limb_count > interval_payload_limbs
        ? output_limb_count - interval_payload_limbs : 0U;
    const uint32_t carried_generator = face % generator_count;
    const uint64_t restriction_base = (uint64_t)face * factor_count;
    const uint64_t current_base =
        (uint64_t)carried_generator * pair_count * current_limb_count;
    const uint64_t begin = (uint64_t)chunk * chunk_size;
    uint64_t end = begin + chunk_size;
    if (end > pair_count) end = pair_count;
    for (uint64_t pair = begin; pair < end; ++pair) {
        const uint32_t left = pair_factors[pair * 2ULL];
        const uint32_t right = pair_factors[pair * 2ULL + 1ULL];
        if (left >= factor_count || right >= factor_count) {
            atomicExch(obstruction, 1U);
            return;
        }
        const uint32_t left_restriction = restriction_limbs[restriction_base + left];
        const uint32_t right_restriction = restriction_limbs[restriction_base + right];
        if (left_restriction == 0U || right_restriction == 0U) continue;
        uint32_t current_lower[MEMBRANE_INTERVAL_PREFIX_LIMBS + 1U];
        uint32_t current_upper[MEMBRANE_INTERVAL_PREFIX_LIMBS + 1U];
        uint32_t ingress_lower[MEMBRANE_INTERVAL_PREFIX_LIMBS + 1U];
        uint32_t ingress_upper[MEMBRANE_INTERVAL_PREFIX_LIMBS + 1U];
        uint32_t current_exponent = 0U;
        uint32_t ingress_exponent = 0U;
        membrane_prefix_interval(
            current_limbs + current_base + pair * (uint64_t)current_limb_count,
            current_limb_count,
            current_lower, current_upper, &current_exponent);
        membrane_prefix_interval(
            ingress_receiver_limbs + pair * (uint64_t)ingress_receiver_limb_count,
            ingress_receiver_limb_count,
            ingress_lower, ingress_upper, &ingress_exponent);
        uint32_t linear_scale[5];
        uint32_t square_scale[5];
        membrane_scale_linear(
            left_restriction, right_restriction, left == right, linear_scale);
        membrane_scale_square(
            left_restriction, right_restriction, left == right, square_scale);
        const uint64_t cross_partial = section_base * chunk_count + chunk;
        const uint64_t current_norm_partial =
            (section_base + 1ULL) * chunk_count + chunk;
        const uint64_t ingress_norm_partial =
            (section_base + 2ULL) * chunk_count + chunk;
        if (!membrane_accumulate_prefix_product(
                partial_lower + cross_partial * interval_limb_count,
                partial_upper + cross_partial * interval_limb_count,
                interval_limb_count, receiver_exponent,
                current_lower, current_upper, current_exponent,
                ingress_lower, ingress_upper, ingress_exponent, linear_scale)
            || !membrane_accumulate_prefix_product(
                partial_lower + current_norm_partial * interval_limb_count,
                partial_upper + current_norm_partial * interval_limb_count,
                interval_limb_count, receiver_exponent,
                current_lower, current_upper, current_exponent,
                current_lower, current_upper, current_exponent, square_scale)
            || !membrane_accumulate_prefix_product(
                partial_lower + ingress_norm_partial * interval_limb_count,
                partial_upper + ingress_norm_partial * interval_limb_count,
                interval_limb_count, receiver_exponent,
                ingress_lower, ingress_upper, ingress_exponent,
                ingress_lower, ingress_upper, ingress_exponent, square_scale)) {
            atomicExch(obstruction, 1U);
            return;
        }
    }
}

extern "C" __global__ void reduce_membrane_sparse_quadratic_unsigned_intervals(
    const uint32_t *input,
    uint32_t *output,
    uint32_t section_count,
    uint32_t input_count_per_section,
    uint32_t output_count_per_section,
    uint32_t chunk_size,
    uint32_t limb_count,
    uint32_t *obstruction)
{
    const uint64_t at = (uint64_t)blockIdx.x * blockDim.x + threadIdx.x;
    const uint64_t work = (uint64_t)section_count * output_count_per_section;
    if (at >= work) return;
    const uint32_t section = (uint32_t)(at / output_count_per_section);
    const uint32_t chunk = (uint32_t)(at % output_count_per_section);
    uint32_t *target = output + at * limb_count;
    zero_unsigned_limbs(target, limb_count);
    const uint64_t begin = (uint64_t)chunk * chunk_size;
    uint64_t end = begin + chunk_size;
    if (end > input_count_per_section) end = input_count_per_section;
    const uint64_t input_base = (uint64_t)section * input_count_per_section;
    for (uint64_t input_at = begin; input_at < end; ++input_at) {
        const uint32_t *term = input + (input_base + input_at) * limb_count;
        uint64_t carry = 0ULL;
        for (uint32_t limb = 0U; limb < limb_count; ++limb) {
            const uint64_t sum = (uint64_t)target[limb] + term[limb] + carry;
            target[limb] = (uint32_t)sum;
            carry = sum >> 32U;
        }
        if (carry != 0ULL) atomicExch(obstruction, 1U);
    }
}

extern "C" __global__ void compare_membrane_sparse_quadratic_projective_interval_pairs(
    const uint8_t *native_phase_front,
    const uint32_t *lower,
    const uint32_t *upper,
    uint8_t *pair_dominates,
    uint32_t *square_scratch,
    uint32_t *denominator_scratch,
    uint32_t *left_cross_scratch,
    uint32_t *right_cross_scratch,
    uint32_t face_count,
    uint32_t interval_limb_count,
    uint32_t square_limb_count,
    uint32_t cross_limb_count)
{
    const uint64_t at = (uint64_t)blockIdx.x * blockDim.x + threadIdx.x;
    const uint64_t work = (uint64_t)face_count * face_count;
    if (at >= work) return;
    const uint32_t challenged = (uint32_t)(at / face_count);
    const uint32_t challenger = (uint32_t)(at % face_count);
    pair_dominates[at] = 0U;
    if (challenger == challenged || native_phase_front[challenger] == 0U
        || native_phase_front[challenged] == 0U) return;
    const uint64_t challenger_section = (uint64_t)challenger * 3ULL;
    const uint64_t challenged_section = (uint64_t)challenged * 3ULL;
    const uint32_t *challenger_a_lower = lower
        + challenger_section * interval_limb_count;
    const uint32_t *challenger_b_upper = upper
        + (challenger_section + 1ULL) * interval_limb_count;
    const uint32_t *challenger_c_upper = upper
        + (challenger_section + 2ULL) * interval_limb_count;
    const uint32_t *challenged_a_upper = upper
        + challenged_section * interval_limb_count;
    const uint32_t *challenged_b_lower = lower
        + (challenged_section + 1ULL) * interval_limb_count;
    const uint32_t *challenged_c_lower = lower
        + (challenged_section + 2ULL) * interval_limb_count;
    if (unsigned_limbs_are_zero(challenger_a_lower, interval_limb_count)
        || unsigned_limbs_are_zero(challenged_b_lower, interval_limb_count)
        || unsigned_limbs_are_zero(challenged_c_lower, interval_limb_count)) return;
    uint32_t *square = square_scratch + at * square_limb_count;
    uint32_t *denominator = denominator_scratch + at * square_limb_count;
    uint32_t *left_cross = left_cross_scratch + at * cross_limb_count;
    uint32_t *right_cross = right_cross_scratch + at * cross_limb_count;
    multiply_unsigned_limbs(
        challenger_a_lower, interval_limb_count,
        challenger_a_lower, interval_limb_count,
        square, square_limb_count);
    multiply_unsigned_limbs(
        challenged_b_lower, interval_limb_count,
        challenged_c_lower, interval_limb_count,
        denominator, square_limb_count);
    multiply_unsigned_limbs(
        square, square_limb_count,
        denominator, square_limb_count,
        left_cross, cross_limb_count);
    multiply_unsigned_limbs(
        challenged_a_upper, interval_limb_count,
        challenged_a_upper, interval_limb_count,
        square, square_limb_count);
    multiply_unsigned_limbs(
        challenger_b_upper, interval_limb_count,
        challenger_c_upper, interval_limb_count,
        denominator, square_limb_count);
    multiply_unsigned_limbs(
        square, square_limb_count,
        denominator, square_limb_count,
        right_cross, cross_limb_count);
    if (compare_magnitude(left_cross, right_cross, cross_limb_count) > 0) {
        pair_dominates[at] = 1U;
    }
}

extern "C" __global__ void select_membrane_sparse_quadratic_projective_interval_front(
    const uint8_t *native_phase_front,
    const uint8_t *pair_dominates,
    const uint32_t *obstruction,
    uint8_t *candidate_front,
    uint32_t face_count)
{
    const uint32_t challenged = blockIdx.x * blockDim.x + threadIdx.x;
    if (challenged >= face_count) return;
    if (native_phase_front[challenged] == 0U) {
        candidate_front[challenged] = 0U;
        return;
    }
    if (*obstruction != 0U) {
        candidate_front[challenged] = 1U;
        return;
    }
    const uint64_t begin = (uint64_t)challenged * face_count;
    for (uint32_t challenger = 0U; challenger < face_count; ++challenger) {
        if (pair_dominates[begin + challenger] != 0U) {
            candidate_front[challenged] = 0U;
            return;
        }
    }
    candidate_front[challenged] = 1U;
}

extern "C" __global__ void ensure_membrane_sparse_quadratic_projective_interval_front(
    const uint8_t *native_phase_front,
    uint8_t *candidate_front,
    uint32_t face_count,
    uint32_t *obstruction)
{
    if (blockIdx.x != 0U || threadIdx.x != 0U) return;
    uint32_t candidate_count = 0U;
    for (uint32_t face = 0U; face < face_count; ++face) {
        candidate_count += candidate_front[face] != 0U ? 1U : 0U;
    }
    if (candidate_count != 0U) return;
    *obstruction = 1U;
    for (uint32_t face = 0U; face < face_count; ++face) {
        candidate_front[face] = native_phase_front[face];
    }
}

extern "C" __global__ void reduce_membrane_sparse_quadratic_signed_sections(
    const uint8_t *input_signs,
    const uint32_t *input_limbs,
    uint8_t *output_signs,
    uint32_t *output_limbs,
    uint32_t section_count,
    uint32_t input_count_per_section,
    uint32_t output_count_per_section,
    uint32_t chunk_size,
    uint32_t limb_count)
{
    const uint64_t at = (uint64_t)blockIdx.x * blockDim.x + threadIdx.x;
    const uint64_t work =
        (uint64_t)section_count * (uint64_t)output_count_per_section;
    if (at >= work) return;
    const uint32_t section = (uint32_t)(at / output_count_per_section);
    const uint32_t chunk = (uint32_t)(at % output_count_per_section);
    const uint64_t output_at = at * limb_count;
    output_signs[at] = 0U;
    zero_unsigned_limbs(output_limbs + output_at, limb_count);
    const uint64_t begin = (uint64_t)chunk * chunk_size;
    uint64_t end = begin + chunk_size;
    if (end > input_count_per_section) end = input_count_per_section;
    const uint64_t input_base =
        (uint64_t)section * input_count_per_section;
    for (uint64_t input = begin; input < end; ++input) {
        const uint64_t source = input_base + input;
        add_signed_magnitude(
            output_signs + at,
            output_limbs + output_at,
            input_signs[source],
            input_limbs + source * limb_count,
            limb_count);
    }
}

extern "C" __global__ void scatter_membrane_sparse_quadratic_native_receivers(
    const uint8_t *family_signs,
    const uint32_t *family_limbs,
    const uint8_t *potential_signs,
    const uint32_t *potential_limbs,
    uint8_t *receiver_signs,
    uint32_t *receiver_limbs,
    uint8_t *situated_signs,
    uint32_t *situated_limbs,
    uint32_t *situated_current_norm_limbs,
    uint32_t *situated_ingress_norm_limbs,
    uint32_t port_count,
    uint32_t family_count,
    uint32_t receiver_count,
    uint32_t limb_count)
{
    const uint64_t at = (uint64_t)blockIdx.x * blockDim.x + threadIdx.x;
    const uint32_t receiver_stride = family_count * 2U + receiver_count * 2U;
    const uint64_t receiver_population =
        (uint64_t)port_count * receiver_stride;
    if (at < receiver_population) {
        const uint32_t port = (uint32_t)(at / receiver_stride);
        const uint32_t local = (uint32_t)(at % receiver_stride);
        const uint64_t source = local < family_count * 2U
            ? (uint64_t)port * family_count * 2ULL + local
            : (uint64_t)port * (receiver_count * 2ULL)
                + (local - family_count * 2U);
        const bool family = local < family_count * 2U;
        const uint8_t *source_signs = family ? family_signs : potential_signs;
        const uint32_t *source_limbs = family ? family_limbs : potential_limbs;
        receiver_signs[at] = source_signs[source];
        for (uint32_t limb = 0U; limb < limb_count; ++limb) {
            receiver_limbs[at * limb_count + limb] =
                source_limbs[source * limb_count + limb];
        }
    }
    if (at < port_count) {
        situated_signs[at] = 0U;
        for (uint32_t limb = 0U; limb < limb_count; ++limb) {
            situated_limbs[at * limb_count + limb] = 0U;
            situated_current_norm_limbs[at * limb_count + limb] = 0U;
            situated_ingress_norm_limbs[at * limb_count + limb] = 0U;
        }
    }
}

extern "C" __global__ void form_membrane_sparse_quadratic_situated_norm_products(
    const uint32_t *current_norm_limbs,
    const uint32_t *ingress_norm_limbs,
    uint32_t *norm_product_limbs,
    uint32_t *returned_current_norm_limbs,
    uint32_t *returned_ingress_norm_limbs,
    uint32_t port_count,
    uint32_t norm_limb_count,
    uint32_t product_limb_count)
{
    const uint32_t port = blockIdx.x * blockDim.x + threadIdx.x;
    if (port >= port_count) return;
    for (uint32_t limb = 0U; limb < norm_limb_count; ++limb) {
        returned_current_norm_limbs[(uint64_t)port * norm_limb_count + limb] =
            current_norm_limbs[(uint64_t)port * norm_limb_count + limb];
        returned_ingress_norm_limbs[(uint64_t)port * norm_limb_count + limb] =
            ingress_norm_limbs[(uint64_t)port * norm_limb_count + limb];
    }
    multiply_unsigned_limbs(
        current_norm_limbs + (uint64_t)port * norm_limb_count,
        norm_limb_count,
        ingress_norm_limbs + (uint64_t)port * norm_limb_count,
        norm_limb_count,
        norm_product_limbs + (uint64_t)port * product_limb_count,
        product_limb_count);
}

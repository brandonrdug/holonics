// Membrane state-addressed returned transport.
// This fragment is included by refine_shell.cu after refine_shared.cuh.

extern "C" __global__ void transport_membrane_sparse_quadratic_state_generator_pairs(
    const uint64_t *generator_target_offsets,
    const uint32_t *generator_source_pairs,
    const uint8_t *generator_multiplicities,
    const uint32_t *source_limbs,
    uint32_t *target_limbs,
    uint32_t source_state_count,
    uint32_t generator_count,
    uint32_t pair_count,
    uint32_t source_limb_count,
    uint32_t target_limb_count,
    uint32_t *obstruction)
{
    const uint64_t at = (uint64_t)blockIdx.x * blockDim.x + threadIdx.x;
    const uint64_t generator_pair_count =
        (uint64_t)generator_count * (uint64_t)pair_count;
    const uint64_t work = (uint64_t)source_state_count * generator_pair_count;
    if (at >= work || pair_count == 0U || generator_count == 0U) return;
    const uint32_t pair_target = (uint32_t)(at % pair_count);
    const uint64_t state_generator = at / pair_count;
    const uint32_t generator = (uint32_t)(state_generator % generator_count);
    const uint32_t source_state = (uint32_t)(state_generator / generator_count);
    uint32_t *output = target_limbs + at * (uint64_t)target_limb_count;
    zero_unsigned_limbs(output, target_limb_count);
    const uint64_t offset_base =
        (uint64_t)generator * ((uint64_t)pair_count + 1ULL);
    for (uint64_t edge = generator_target_offsets[offset_base + pair_target];
         edge < generator_target_offsets[offset_base + pair_target + 1ULL];
         ++edge) {
        const uint32_t source_pair = generator_source_pairs[edge];
        if (source_pair >= pair_count) {
            atomicExch(obstruction, 1U);
            return;
        }
        const uint32_t *input = source_limbs
            + ((uint64_t)source_state * (uint64_t)pair_count + source_pair)
                * (uint64_t)source_limb_count;
        uint64_t carry = 0ULL;
        for (uint32_t limb = 0U; limb < target_limb_count; ++limb) {
            const uint64_t source_value = limb < source_limb_count ? input[limb] : 0ULL;
            const unsigned __int128 sum =
                (unsigned __int128)output[limb]
                + (unsigned __int128)source_value
                    * (unsigned __int128)generator_multiplicities[edge]
                + (unsigned __int128)carry;
            output[limb] = (uint32_t)sum;
            carry = (uint64_t)(sum >> 32U);
        }
        if (carry != 0ULL) atomicExch(obstruction, 1U);
    }
}

extern "C" __global__ void gather_membrane_sparse_quadratic_state_addressed_face_restrictions(
    const uint32_t *state_port_transition,
    const uint32_t *transition_target_states,
    const uint64_t *transition_factor_offsets,
    const uint32_t *transition_factors,
    const uint32_t *transition_current_limbs,
    const uint32_t *source_state_ids,
    const uint32_t *universal_ports,
    uint32_t *restriction_current_limbs,
    uint8_t *restriction_present,
    uint32_t *restriction_target_states,
    uint32_t source_state_count,
    uint32_t local_port_count,
    uint32_t generator_count,
    uint32_t atlas_state_count,
    uint32_t universal_port_count,
    uint32_t transition_count,
    uint32_t factor_count,
    uint32_t restriction_limb_count,
    uint32_t *obstruction)
{
    const uint64_t at = (uint64_t)blockIdx.x * blockDim.x + threadIdx.x;
    const uint64_t face_count =
        (uint64_t)source_state_count
        * (uint64_t)local_port_count
        * (uint64_t)generator_count;
    if (at >= face_count || local_port_count == 0U || generator_count == 0U) return;
    const uint32_t generator = (uint32_t)(at % generator_count);
    const uint64_t state_port = at / generator_count;
    const uint32_t local_port = (uint32_t)(state_port % local_port_count);
    const uint32_t source_state_block = (uint32_t)(state_port / local_port_count);
    const uint64_t restriction_at =
        at * (uint64_t)factor_count * (uint64_t)restriction_limb_count;
    zero_unsigned_limbs(
        restriction_current_limbs + restriction_at,
        factor_count * restriction_limb_count);
    restriction_present[at] = 0U;
    restriction_target_states[at] = 0xffffffffU;
    if (source_state_block >= source_state_count || local_port >= local_port_count) {
        atomicExch(obstruction, 1U);
        return;
    }
    const uint32_t source_state = source_state_ids[source_state_block];
    if (source_state >= atlas_state_count) {
        atomicExch(obstruction, 1U);
        return;
    }
    const uint32_t universal_port = universal_ports[local_port];
    if (universal_port >= universal_port_count) {
        atomicExch(obstruction, 1U);
        return;
    }
    const uint32_t transition = state_port_transition[
        (uint64_t)source_state * (uint64_t)universal_port_count + universal_port];
    if (transition == 0xffffffffU) return;
    if (transition >= transition_count) {
        atomicExch(obstruction, 1U);
        return;
    }
    const uint32_t target_state = transition_target_states[transition];
    if (target_state >= atlas_state_count) {
        atomicExch(obstruction, 1U);
        return;
    }
    restriction_present[at] = 1U;
    restriction_target_states[at] = target_state;
    const uint64_t begin = transition_factor_offsets[transition];
    const uint64_t end = transition_factor_offsets[(uint64_t)transition + 1ULL];
    for (uint64_t coordinate = begin; coordinate < end; ++coordinate) {
        const uint32_t factor = transition_factors[coordinate];
        if (factor >= factor_count) {
            atomicExch(obstruction, 1U);
            return;
        }
        const uint64_t source_at = coordinate * (uint64_t)restriction_limb_count;
        const uint64_t target_at = restriction_at
            + (uint64_t)factor * (uint64_t)restriction_limb_count;
        for (uint32_t limb = 0U; limb < restriction_limb_count; ++limb) {
            restriction_current_limbs[target_at + limb] =
                transition_current_limbs[source_at + limb];
        }
    }
    (void)generator;
}

extern "C" __global__ void form_membrane_sparse_quadratic_state_addressed_situated_front_chunks(
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
    uint32_t source_state_count,
    uint32_t port_count,
    uint32_t face_count,
    uint32_t face_offset,
    uint32_t window_face_count,
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
    const uint64_t work = (uint64_t)window_face_count * (uint64_t)chunk_count;
    if (at >= work || generator_count == 0U || port_count == 0U) return;
    const uint32_t local_face = (uint32_t)(at / chunk_count);
    const uint32_t face = face_offset + local_face;
    const uint32_t chunk = (uint32_t)(at % chunk_count);
    if (face >= face_count) return;
    const uint64_t section_base = (uint64_t)local_face * 3ULL;
    for (uint32_t axis = 0U; axis < 3U; ++axis) {
        const uint64_t partial = (section_base + axis) * chunk_count + chunk;
        partial_signs[partial] = 0U;
        zero_unsigned_limbs(
            partial_limbs + partial * (uint64_t)output_limb_count,
            output_limb_count);
    }
    if (native_phase_front[face] == 0U) return;
    if (restriction_present[face] == 0U) {
        atomicExch(obstruction, 1U);
        return;
    }
    const uint64_t face_stride = (uint64_t)port_count * (uint64_t)generator_count;
    const uint32_t carried_generator = face % generator_count;
    const uint32_t source_state = (uint32_t)((uint64_t)face / face_stride);
    if (source_state >= source_state_count) {
        atomicExch(obstruction, 1U);
        return;
    }
    const uint64_t current_base =
        ((uint64_t)source_state * (uint64_t)generator_count
            + (uint64_t)carried_generator)
        * (uint64_t)pair_count * (uint64_t)current_limb_count;
    const uint64_t restriction_base =
        (uint64_t)face * (uint64_t)factor_count * (uint64_t)restriction_limb_count;
    const uint64_t begin = (uint64_t)chunk * chunk_size;
    uint64_t end = begin + chunk_size;
    if (end > pair_count) end = pair_count;
    uint32_t *first = product_first_scratch + at * (uint64_t)output_limb_count;
    uint32_t *second = product_second_scratch + at * (uint64_t)output_limb_count;
    const uint32_t current_once_limbs = current_limb_count + restriction_limb_count
        < output_limb_count ? current_limb_count + restriction_limb_count : output_limb_count;
    const uint32_t restricted_current_limbs = current_once_limbs + restriction_limb_count
        < output_limb_count ? current_once_limbs + restriction_limb_count : output_limb_count;
    const uint32_t ingress_once_limbs = ingress_receiver_limb_count + restriction_limb_count
        < output_limb_count ? ingress_receiver_limb_count + restriction_limb_count : output_limb_count;
    const uint32_t restricted_ingress_limbs = ingress_once_limbs + restriction_limb_count
        < output_limb_count ? ingress_once_limbs + restriction_limb_count : output_limb_count;
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
            current_limb_count, left_restriction, restriction_limb_count,
            first, output_limb_count);
        multiply_unsigned_limbs(
            first, current_once_limbs, right_restriction, restriction_limb_count,
            second, output_limb_count);
        if (unsigned_limbs_are_zero(second, output_limb_count)) continue;
        const uint32_t multiplicity = left == right ? 1U : 2U;
        const uint64_t a_partial = section_base * chunk_count + chunk;
        const uint64_t b_partial = (section_base + 1ULL) * chunk_count + chunk;
        const uint64_t c_partial = (section_base + 2ULL) * chunk_count + chunk;
        multiply_unsigned_limbs(
            second, restricted_current_limbs,
            ingress_receiver_limbs + pair * (uint64_t)ingress_receiver_limb_count,
            ingress_receiver_limb_count, first, output_limb_count);
        for (uint32_t copy = 0U; copy < multiplicity; ++copy) {
            add_signed_magnitude(
                partial_signs + a_partial,
                partial_limbs + a_partial * (uint64_t)output_limb_count,
                1U, first, output_limb_count);
        }
        multiply_unsigned_limbs(
            second, restricted_current_limbs, second, restricted_current_limbs,
            first, output_limb_count);
        for (uint32_t copy = 0U; copy < multiplicity; ++copy) {
            add_signed_magnitude(
                partial_signs + b_partial,
                partial_limbs + b_partial * (uint64_t)output_limb_count,
                1U, first, output_limb_count);
        }
        multiply_unsigned_limbs(
            ingress_receiver_limbs + pair * (uint64_t)ingress_receiver_limb_count,
            ingress_receiver_limb_count, left_restriction, restriction_limb_count,
            first, output_limb_count);
        multiply_unsigned_limbs(
            first, ingress_once_limbs, right_restriction, restriction_limb_count,
            second, output_limb_count);
        multiply_unsigned_limbs(
            second, restricted_ingress_limbs, second, restricted_ingress_limbs,
            first, output_limb_count);
        for (uint32_t copy = 0U; copy < multiplicity; ++copy) {
            add_signed_magnitude(
                partial_signs + c_partial,
                partial_limbs + c_partial * (uint64_t)output_limb_count,
                1U, first, output_limb_count);
        }
    }
}

extern "C" __global__ void index_membrane_sparse_quadratic_returned_state_faces(
    const uint8_t *situated_front,
    const uint8_t *restriction_present,
    const uint32_t *face_target_states,
    uint32_t *face_target_blocks,
    uint32_t *target_state_ids,
    uint32_t *target_state_population,
    uint32_t face_count)
{
    if (blockIdx.x != 0U || threadIdx.x != 0U) return;
    uint32_t population = 0U;
    for (uint32_t face = 0U; face < face_count; ++face) {
        face_target_blocks[face] = 0xffffffffU;
        if (situated_front[face] == 0U || restriction_present[face] == 0U) continue;
        const uint32_t target_state = face_target_states[face];
        if (target_state == 0xffffffffU) continue;
        uint32_t block = 0xffffffffU;
        for (uint32_t candidate = 0U; candidate < population; ++candidate) {
            if (target_state_ids[candidate] == target_state) {
                block = candidate;
                break;
            }
        }
        if (block == 0xffffffffU) {
            block = population;
            target_state_ids[population] = target_state;
            ++population;
        }
        face_target_blocks[face] = block;
    }
    target_state_population[0] = population;
}

extern "C" __global__ void condition_membrane_sparse_quadratic_state_addressed_pairs_by_returned_faces(
    const uint32_t *pair_factors,
    const uint32_t *face_restriction_limbs,
    const uint32_t *face_source_limbs,
    const uint8_t *situated_front,
    const uint32_t *face_target_states,
    const uint32_t *face_target_blocks,
    uint32_t *target_limbs,
    uint32_t *first_scratch_limbs,
    uint32_t *second_scratch_limbs,
    uint64_t work_offset,
    uint32_t window_count,
    uint32_t pair_count,
    uint32_t factor_count,
    uint32_t source_state_count,
    uint32_t port_count,
    uint32_t generator_count,
    uint32_t face_count,
    uint32_t target_state_count,
    uint32_t source_limb_count,
    uint32_t restriction_limb_count,
    uint32_t target_limb_count,
    uint32_t *obstruction)
{
    const uint64_t local_at = (uint64_t)blockIdx.x * blockDim.x + threadIdx.x;
    const uint64_t work = (uint64_t)target_state_count * (uint64_t)pair_count;
    if (local_at >= window_count || pair_count == 0U || port_count == 0U
        || generator_count == 0U) return;
    const uint64_t at = work_offset + local_at;
    if (at >= work) return;
    const uint32_t target_block = (uint32_t)(at / pair_count);
    const uint32_t pair = (uint32_t)(at % pair_count);
    const uint64_t target_at =
        ((uint64_t)target_block * (uint64_t)pair_count + pair)
        * (uint64_t)target_limb_count;
    uint32_t *target = target_limbs + target_at;
    uint32_t *first = first_scratch_limbs
        + local_at * (uint64_t)target_limb_count;
    uint32_t *second = second_scratch_limbs
        + local_at * (uint64_t)target_limb_count;
    zero_unsigned_limbs(target, target_limb_count);
    zero_unsigned_limbs(first, target_limb_count);
    zero_unsigned_limbs(second, target_limb_count);
    const uint32_t left = pair_factors[pair * 2ULL];
    const uint32_t right = pair_factors[pair * 2ULL + 1ULL];
    if (left >= factor_count || right >= factor_count) {
        atomicExch(obstruction, 1U);
        return;
    }
    const uint64_t face_stride = (uint64_t)port_count * (uint64_t)generator_count;
    for (uint32_t face = 0U; face < face_count; ++face) {
        if (situated_front[face] == 0U || face_target_blocks[face] != target_block) continue;
        if (face_target_states[face] == 0xffffffffU) {
            atomicExch(obstruction, 1U);
            return;
        }
        const uint32_t carried_generator = face % generator_count;
        const uint32_t source_state = (uint32_t)((uint64_t)face / face_stride);
        if (source_state >= source_state_count) {
            atomicExch(obstruction, 1U);
            return;
        }
        const uint64_t source_at =
            ((uint64_t)source_state * (uint64_t)generator_count + carried_generator)
            * (uint64_t)pair_count + pair;
        const uint64_t restriction_at =
            (uint64_t)face * (uint64_t)factor_count * (uint64_t)restriction_limb_count;
        const uint32_t *source = face_source_limbs
            + source_at * (uint64_t)source_limb_count;
        const uint32_t *left_restriction = face_restriction_limbs
            + restriction_at + (uint64_t)left * restriction_limb_count;
        const uint32_t *right_restriction = face_restriction_limbs
            + restriction_at + (uint64_t)right * restriction_limb_count;
        multiply_unsigned_limbs(
            source, source_limb_count, left_restriction, restriction_limb_count,
            first, target_limb_count);
        multiply_unsigned_limbs(
            first, target_limb_count, right_restriction, restriction_limb_count,
            second, target_limb_count);
        add_unsigned_limbs(target, second, target_limb_count);
    }
}

extern "C" __global__ void condition_membrane_sparse_relational_state_addressed_current_by_returned_faces(
    const uint32_t *source_state_ids,
    const uint32_t *relational_state_present,
    const uint32_t *relational_states,
    const uint8_t *transported_real_sign,
    const uint32_t *transported_real_limbs,
    const uint8_t *transported_imaginary_sign,
    const uint32_t *transported_imaginary_limbs,
    const uint32_t *face_restriction_limbs,
    const uint8_t *situated_front,
    const uint32_t *face_target_blocks,
    uint32_t *target_state_present,
    uint8_t *target_real_sign,
    uint32_t *target_real_limbs,
    uint8_t *target_imaginary_sign,
    uint32_t *target_imaginary_limbs,
    uint32_t *product_scratch_limbs,
    uint32_t factor_count,
    uint32_t source_state_count,
    uint32_t port_count,
    uint32_t generator_count,
    uint32_t face_count,
    uint32_t relational_state_count,
    uint32_t target_state_count,
    uint32_t source_limb_count,
    uint32_t restriction_limb_count,
    uint32_t target_limb_count,
    uint32_t *obstruction)
{
    const uint64_t at = (uint64_t)blockIdx.x * blockDim.x + threadIdx.x;
    const uint64_t work = (uint64_t)target_state_count * (uint64_t)factor_count;
    if (at >= work || factor_count == 0U || source_state_count == 0U
        || port_count == 0U || generator_count == 0U || relational_state_count == 0U) return;
    const uint32_t target_block = (uint32_t)(at / factor_count);
    const uint32_t factor = (uint32_t)(at % factor_count);
    const uint64_t target_at = at * (uint64_t)target_limb_count;
    uint8_t *real_sign = target_real_sign + at;
    uint8_t *imaginary_sign = target_imaginary_sign + at;
    uint32_t *real = target_real_limbs + target_at;
    uint32_t *imaginary = target_imaginary_limbs + target_at;
    uint32_t *product = product_scratch_limbs + target_at;
    *real_sign = 0U;
    *imaginary_sign = 0U;
    zero_unsigned_limbs(real, target_limb_count);
    zero_unsigned_limbs(imaginary, target_limb_count);
    zero_unsigned_limbs(product, target_limb_count);
    bool met = false;
    const uint64_t face_stride = (uint64_t)port_count * (uint64_t)generator_count;
    for (uint32_t face = 0U; face < face_count; ++face) {
        if (situated_front[face] == 0U || face_target_blocks[face] != target_block) continue;
        const uint32_t source_state = (uint32_t)((uint64_t)face / face_stride);
        if (source_state >= source_state_count) {
            atomicExch(obstruction, 1U);
            return;
        }
        uint32_t relational_state = 0xffffffffU;
        for (uint32_t candidate = 0U; candidate < relational_state_count; ++candidate) {
            if (relational_state_present[candidate] != 0U
                && relational_states[candidate] == source_state_ids[source_state]) {
                if (relational_state != 0xffffffffU) {
                    atomicExch(obstruction, 1U);
                    return;
                }
                relational_state = candidate;
            }
        }
        if (relational_state == 0xffffffffU) continue;
        const uint32_t generator = face % generator_count;
        const uint64_t source_at =
            ((uint64_t)relational_state * (uint64_t)generator_count + generator)
            * (uint64_t)factor_count + factor;
        const uint64_t restriction_at =
            ((uint64_t)face * (uint64_t)factor_count + factor)
            * (uint64_t)restriction_limb_count;
        const uint8_t component_signs[2] = {
            transported_real_sign[source_at], transported_imaginary_sign[source_at]
        };
        const uint32_t *component_limbs[2] = {
            transported_real_limbs + source_at * (uint64_t)source_limb_count,
            transported_imaginary_limbs + source_at * (uint64_t)source_limb_count
        };
        for (uint32_t component = 0U; component < 2U; ++component) {
            if (component_signs[component] == 0U) continue;
            multiply_unsigned_limbs(
                component_limbs[component], source_limb_count,
                face_restriction_limbs + restriction_at, restriction_limb_count,
                product, target_limb_count);
            if (component == 0U) {
                add_signed_magnitude(
                    real_sign, real, component_signs[component], product, target_limb_count);
            } else {
                add_signed_magnitude(
                    imaginary_sign, imaginary, component_signs[component], product,
                    target_limb_count);
            }
        }
        met = true;
    }
    if (met && factor == 0U) atomicExch(target_state_present + target_block, 1U);
    if (unsigned_limbs_are_zero(real, target_limb_count)) *real_sign = 0U;
    if (unsigned_limbs_are_zero(imaginary, target_limb_count)) *imaginary_sign = 0U;
}

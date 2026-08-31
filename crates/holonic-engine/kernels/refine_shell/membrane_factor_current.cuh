// Membrane factor-current transport.
// This fragment is included by refine_shell.cu after refine_shared.cuh.

extern "C" __global__ void transport_membrane_factor_current_sections(
    const uint32_t *source_current_limbs,
    const uint8_t *source_state_present,
    const uint32_t *source_states,
    const uint32_t *generator_targets,
    uint32_t *candidate_current_limbs,
    uint8_t *candidate_state_present,
    uint32_t *candidate_states,
    uint32_t context_count,
    uint32_t factor_count,
    uint32_t generator_count,
    uint32_t source_limb_count,
    uint32_t target_limb_count)
{
    const uint32_t candidate = blockIdx.x * blockDim.x + threadIdx.x;
    const uint64_t candidate_count =
        (uint64_t)context_count * (uint64_t)generator_count;
    if ((uint64_t)candidate >= candidate_count) return;
    const uint32_t context = candidate / generator_count;
    const uint32_t generator = candidate % generator_count;
    uint32_t *target_row = candidate_current_limbs
        + (uint64_t)candidate * (uint64_t)factor_count * (uint64_t)target_limb_count;
    zero_unsigned_limbs(
        target_row,
        factor_count * target_limb_count);
    candidate_state_present[candidate] = source_state_present[context];
    candidate_states[candidate] = source_states[context];
    for (uint32_t source = 0U; source < factor_count; ++source) {
        const uint32_t target = generator_targets[
            (uint64_t)generator * (uint64_t)factor_count + source];
        if (target >= factor_count) continue;
        const uint32_t *source_value = source_current_limbs
            + ((uint64_t)context * (uint64_t)factor_count + source)
                * (uint64_t)source_limb_count;
        uint32_t *target_value = target_row
            + (uint64_t)target * (uint64_t)target_limb_count;
        uint64_t carry = 0ULL;
        uint32_t limb = 0U;
        for (; limb < source_limb_count; ++limb) {
            const uint64_t sum =
                (uint64_t)target_value[limb] + (uint64_t)source_value[limb] + carry;
            target_value[limb] = (uint32_t)sum;
            carry = sum >> 32U;
        }
        while (carry != 0ULL && limb < target_limb_count) {
            const uint64_t sum = (uint64_t)target_value[limb] + carry;
            target_value[limb] = (uint32_t)sum;
            carry = sum >> 32U;
            ++limb;
        }
    }
}

extern "C" __global__ void transport_membrane_active_factor_current_sections(
    const uint32_t *source_current_limbs,
    const uint8_t *source_state_present,
    const uint32_t *source_states,
    const uint32_t *generator_targets,
    const uint32_t *source_active_factors,
    const uint32_t *successor_factor_coordinates,
    uint32_t *candidate_current_limbs,
    uint8_t *candidate_state_present,
    uint32_t *candidate_states,
    uint32_t context_count,
    uint32_t native_factor_count,
    uint32_t source_active_factor_count,
    uint32_t successor_factor_count,
    uint32_t generator_count,
    uint32_t source_limb_count,
    uint32_t target_limb_count)
{
    const uint32_t candidate = blockIdx.x * blockDim.x + threadIdx.x;
    const uint64_t candidate_count =
        (uint64_t)context_count * (uint64_t)generator_count;
    if ((uint64_t)candidate >= candidate_count || successor_factor_count == 0U) return;
    const uint32_t context = candidate / generator_count;
    const uint32_t generator = candidate % generator_count;
    uint32_t *target_row = candidate_current_limbs
        + (uint64_t)candidate * (uint64_t)successor_factor_count
            * (uint64_t)target_limb_count;
    zero_unsigned_limbs(target_row, successor_factor_count * target_limb_count);
    candidate_state_present[candidate] = source_state_present[context];
    candidate_states[candidate] = source_states[context];
    for (uint32_t source_local = 0U;
         source_local < source_active_factor_count; ++source_local) {
        const uint32_t source = source_active_factors[source_local];
        if (source >= native_factor_count) continue;
        const uint32_t native_target = generator_targets[
            (uint64_t)generator * (uint64_t)native_factor_count + source];
        if (native_target >= native_factor_count) continue;
        const uint32_t target = successor_factor_coordinates[native_target];
        if (target >= successor_factor_count) continue;
        const uint32_t *source_value = source_current_limbs
            + ((uint64_t)context * (uint64_t)native_factor_count + source)
                * (uint64_t)source_limb_count;
        uint32_t *target_value = target_row
            + (uint64_t)target * (uint64_t)target_limb_count;
        uint64_t carry = 0ULL;
        uint32_t limb = 0U;
        for (; limb < source_limb_count; ++limb) {
            const uint64_t sum =
                (uint64_t)target_value[limb] + (uint64_t)source_value[limb] + carry;
            target_value[limb] = (uint32_t)sum;
            carry = sum >> 32U;
        }
        while (carry != 0ULL && limb < target_limb_count) {
            const uint64_t sum = (uint64_t)target_value[limb] + carry;
            target_value[limb] = (uint32_t)sum;
            carry = sum >> 32U;
            ++limb;
        }
    }
}

extern "C" __global__ void collect_membrane_selected_generated_port_restrictions(
    const uint8_t *presented_generator_mask,
    const uint8_t *restriction_present,
    uint32_t *selected_faces,
    uint32_t *selected_restrictions,
    uint32_t *selected_count,
    uint32_t port_count,
    uint32_t generator_count,
    uint32_t boundary_state_count)
{
    if (blockIdx.x != 0U || threadIdx.x != 0U) return;
    uint32_t count = 0U;
    const uint32_t local_face_count = port_count * generator_count;
    const uint32_t face_count = boundary_state_count * local_face_count;
    for (uint32_t face = 0U; face < face_count; ++face) {
        const uint32_t source_state_coordinate = face / local_face_count;
        const uint32_t local_face = face % local_face_count;
        const uint32_t port = local_face / generator_count;
        const uint32_t generator = local_face % generator_count;
        if (presented_generator_mask[generator] == 0U) continue;
        const uint32_t restriction =
            port * boundary_state_count + source_state_coordinate;
        if (restriction_present[restriction] == 0U) continue;
        selected_faces[count] = face;
        selected_restrictions[count] = restriction;
        ++count;
    }
    *selected_count = count;
}

extern "C" __global__ void condition_membrane_factor_current_sections_by_generated_ports(
    const uint32_t *transported_current_limbs,
    const uint8_t *transported_state_present,
    const uint32_t *transported_states,
    const uint32_t *restriction_current_limbs,
    const uint32_t *selected_faces,
    const uint32_t *selected_restrictions,
    const uint32_t *restriction_target_states,
    const uint32_t *boundary_states,
    const uint32_t *candidate_source_contexts,
    const uint32_t *candidate_selected_slots,
    uint32_t *candidate_current_limbs,
    uint8_t *candidate_state_present,
    uint32_t *candidate_states,
    uint32_t context_count,
    uint32_t factor_count,
    uint32_t generator_count,
    uint32_t selected_slot_count,
    uint32_t candidate_count,
    uint32_t boundary_state_count,
    uint32_t transported_limb_count,
    uint32_t restriction_limb_count,
    uint32_t target_limb_count)
{
    const uint32_t candidate = blockIdx.x * blockDim.x + threadIdx.x;
    if (candidate >= candidate_count) return;
    const uint32_t context = candidate_source_contexts[candidate];
    const uint32_t slot = candidate_selected_slots[candidate];
    if (context >= context_count || slot >= selected_slot_count) return;
    const uint32_t face = selected_faces[slot];
    const uint32_t generator = face % generator_count;
    const uint32_t restriction = selected_restrictions[slot];
    const uint32_t transported_section = context * generator_count + generator;
    const uint32_t boundary = restriction % boundary_state_count;
    uint32_t *target = candidate_current_limbs
        + (uint64_t)candidate * (uint64_t)factor_count * (uint64_t)target_limb_count;
    if (boundary_state_count == 0U || boundary >= boundary_state_count
        || transported_state_present[transported_section] == 0U
        || transported_states[transported_section] != boundary_states[boundary]) {
        zero_unsigned_limbs(target, factor_count * target_limb_count);
        candidate_state_present[candidate] = 0U;
        candidate_states[candidate] = 0xffffffffU;
        return;
    }
    const uint32_t *transported = transported_current_limbs
        + ((uint64_t)context * (uint64_t)generator_count + generator)
            * (uint64_t)factor_count * (uint64_t)transported_limb_count;
    const uint32_t *restricted = restriction_current_limbs
        + (uint64_t)restriction * (uint64_t)factor_count
            * (uint64_t)restriction_limb_count;
    candidate_state_present[candidate] = 1U;
    candidate_states[candidate] = restriction_target_states[restriction];
    for (uint32_t factor = 0U; factor < factor_count; ++factor) {
        multiply_unsigned_limbs(
            transported + (uint64_t)factor * transported_limb_count,
            transported_limb_count,
            restricted + (uint64_t)factor * restriction_limb_count,
            restriction_limb_count,
            target + (uint64_t)factor * target_limb_count,
            target_limb_count);
    }
}

extern "C" __global__ void condition_membrane_active_factor_current_sections_by_generated_ports(
    const uint32_t *transported_current_limbs,
    const uint8_t *transported_state_present,
    const uint32_t *transported_states,
    const uint32_t *restriction_current_limbs,
    const uint32_t *presented_current_limbs,
    const uint32_t *successor_factors,
    const uint32_t *selected_faces,
    const uint32_t *selected_restrictions,
    const uint32_t *restriction_target_states,
    const uint32_t *boundary_states,
    const uint32_t *candidate_source_contexts,
    const uint32_t *candidate_selected_slots,
    uint32_t *candidate_current_limbs,
    uint32_t *first_product_scratch_limbs,
    uint8_t *candidate_state_present,
    uint32_t *candidate_states,
    uint32_t context_count,
    uint32_t native_factor_count,
    uint32_t successor_factor_count,
    uint32_t generator_count,
    uint32_t selected_slot_count,
    uint32_t candidate_count,
    uint32_t boundary_state_count,
    uint32_t transported_limb_count,
    uint32_t restriction_limb_count,
    uint32_t presented_limb_count,
    uint32_t presented_current_present,
    uint32_t first_product_limb_count,
    uint32_t target_limb_count)
{
    const uint32_t candidate = blockIdx.x * blockDim.x + threadIdx.x;
    if (candidate >= candidate_count) return;
    const uint32_t context = candidate_source_contexts[candidate];
    const uint32_t slot = candidate_selected_slots[candidate];
    if (context >= context_count || slot >= selected_slot_count) return;
    const uint32_t face = selected_faces[slot];
    const uint32_t generator = face % generator_count;
    const uint32_t restriction = selected_restrictions[slot];
    const uint32_t transported_section = context * generator_count + generator;
    const uint32_t boundary = restriction % boundary_state_count;
    uint32_t *target = candidate_current_limbs
        + (uint64_t)candidate * (uint64_t)successor_factor_count
            * (uint64_t)target_limb_count;
    if (boundary_state_count == 0U || boundary >= boundary_state_count
        || transported_state_present[transported_section] == 0U
        || transported_states[transported_section] != boundary_states[boundary]) {
        zero_unsigned_limbs(target, successor_factor_count * target_limb_count);
        candidate_state_present[candidate] = 0U;
        candidate_states[candidate] = 0xffffffffU;
        return;
    }
    const uint32_t *transported = transported_current_limbs
        + ((uint64_t)context * (uint64_t)generator_count + generator)
            * (uint64_t)successor_factor_count * (uint64_t)transported_limb_count;
    const uint32_t *restricted = restriction_current_limbs
        + (uint64_t)restriction * (uint64_t)native_factor_count
            * (uint64_t)restriction_limb_count;
    uint32_t *first_product = first_product_scratch_limbs
        + (uint64_t)candidate * (uint64_t)successor_factor_count
            * (uint64_t)first_product_limb_count;
    candidate_state_present[candidate] = 1U;
    candidate_states[candidate] = restriction_target_states[restriction];
    for (uint32_t local = 0U; local < successor_factor_count; ++local) {
        const uint32_t factor = successor_factors[local];
        if (factor >= native_factor_count) continue;
        multiply_unsigned_limbs(
            transported + (uint64_t)local * transported_limb_count,
            transported_limb_count,
            restricted + (uint64_t)factor * restriction_limb_count,
            restriction_limb_count,
            first_product + (uint64_t)local * first_product_limb_count,
            first_product_limb_count);
        uint32_t *target_value = target + (uint64_t)local * target_limb_count;
        if (presented_current_present != 0U) {
            multiply_unsigned_limbs(
                first_product + (uint64_t)local * first_product_limb_count,
                first_product_limb_count,
                presented_current_limbs + (uint64_t)factor * presented_limb_count,
                presented_limb_count,
                target_value,
                target_limb_count);
        } else {
            zero_unsigned_limbs(target_value, target_limb_count);
            const uint32_t copy_limbs = first_product_limb_count < target_limb_count
                ? first_product_limb_count : target_limb_count;
            for (uint32_t limb = 0U; limb < copy_limbs; ++limb) {
                target_value[limb] = first_product[
                    (uint64_t)local * first_product_limb_count + limb];
            }
        }
    }
    if (unsigned_limbs_are_zero(
            target, (uint64_t)successor_factor_count * (uint64_t)target_limb_count)) {
        candidate_state_present[candidate] = 0U;
        candidate_states[candidate] = 0xffffffffU;
    }
}

extern "C" __global__ void aggregate_membrane_factor_current_candidates_by_target_state(
    const uint32_t *candidate_current_limbs,
    const uint32_t *target_member_offsets,
    const uint32_t *target_members,
    uint32_t *target_current_limbs,
    uint8_t *target_state_present,
    uint32_t *target_weight_limbs,
    uint32_t *obstruction,
    uint32_t target_count,
    uint32_t factor_count,
    uint32_t candidate_limb_count,
    uint32_t target_limb_count)
{
    const uint64_t at = (uint64_t)blockIdx.x * blockDim.x + threadIdx.x;
    const uint64_t work = (uint64_t)target_count * (uint64_t)factor_count;
    if (at >= work) return;
    const uint32_t target = (uint32_t)(at / factor_count);
    const uint32_t factor = (uint32_t)(at % factor_count);
    uint32_t *sum = target_current_limbs
        + at * (uint64_t)target_limb_count;
    zero_unsigned_limbs(sum, target_limb_count);
    for (uint32_t member = target_member_offsets[target];
         member < target_member_offsets[target + 1U]; ++member) {
        const uint32_t candidate = target_members[member];
        const uint32_t *term = candidate_current_limbs
            + ((uint64_t)candidate * (uint64_t)factor_count + factor)
                * (uint64_t)candidate_limb_count;
        add_unsigned_limbs_checked(
            sum, term, target_limb_count, candidate_limb_count, obstruction);
    }
    if (factor == 0U) {
        target_state_present[target] = 1U;
        target_weight_limbs[target] = 1U;
    }
}

extern "C" __global__ void index_membrane_generated_port_target_site_fibres(
    const uint8_t *candidate_state_present,
    const uint32_t *candidate_states,
    uint32_t *candidate_to_target,
    uint32_t *target_states,
    uint32_t *target_member_offsets,
    uint32_t *target_members,
    uint32_t *target_cursors,
    uint32_t *target_count,
    uint32_t candidate_count)
{
    if (blockIdx.x != 0U || threadIdx.x != 0U) return;
    for (uint32_t at = 0U; at <= candidate_count; ++at) target_member_offsets[at] = 0U;
    uint32_t population = 0U;
    for (uint32_t candidate = 0U; candidate < candidate_count; ++candidate) {
        candidate_to_target[candidate] = 0xffffffffU;
        if (candidate_state_present[candidate] == 0U
            || candidate_states[candidate] == 0xffffffffU) continue;
        const uint32_t state = candidate_states[candidate];
        uint32_t target = 0xffffffffU;
        for (uint32_t prior = 0U; prior < population; ++prior) {
            if (target_states[prior] == state) {
                target = prior;
                break;
            }
        }
        if (target == 0xffffffffU) {
            target = population++;
            target_states[target] = state;
        }
        candidate_to_target[candidate] = target;
        ++target_member_offsets[target + 1U];
    }
    for (uint32_t target = 0U; target < population; ++target) {
        target_member_offsets[target + 1U] += target_member_offsets[target];
        target_cursors[target] = target_member_offsets[target];
    }
    for (uint32_t candidate = 0U; candidate < candidate_count; ++candidate) {
        const uint32_t target = candidate_to_target[candidate];
        if (target == 0xffffffffU) continue;
        target_members[target_cursors[target]++] = candidate;
    }
    target_count[0] = population;
}

extern "C" __global__ void pushforward_membrane_completed_target_observer_current(
    const uint32_t *target_current_limbs,
    const uint8_t *target_relational_real_sign,
    const uint32_t *target_relational_real_limbs,
    const uint8_t *target_relational_imaginary_sign,
    const uint32_t *target_relational_imaginary_limbs,
    const uint32_t *selected_faces,
    const uint32_t *candidate_selected_slots,
    const uint32_t *candidate_to_target,
    uint32_t *face_current_limbs,
    uint8_t *face_relational_real_sign,
    uint32_t *face_relational_real_limbs,
    uint8_t *face_relational_imaginary_sign,
    uint32_t *face_relational_imaginary_limbs,
    uint32_t *obstruction,
    uint32_t target_count,
    uint32_t factor_count,
    uint32_t selected_slot_count,
    uint32_t candidate_count,
    uint32_t face_count,
    uint32_t target_limb_count,
    uint32_t target_relational_limb_count,
    uint32_t face_current_limb_count,
    uint32_t face_relational_limb_count)
{
    const uint64_t at = (uint64_t)blockIdx.x * blockDim.x + threadIdx.x;
    const uint64_t work = (uint64_t)face_count * (uint64_t)factor_count;
    if (at >= work || face_count == 0U || factor_count == 0U) return;
    const uint32_t face = (uint32_t)(at / factor_count);
    const uint32_t factor = (uint32_t)(at % factor_count);
    uint32_t *current = face_current_limbs
        + at * (uint64_t)face_current_limb_count;
    uint8_t *real_sign = face_relational_real_sign + at;
    uint32_t *real = face_relational_real_limbs
        + at * (uint64_t)face_relational_limb_count;
    uint8_t *imaginary_sign = face_relational_imaginary_sign + at;
    uint32_t *imaginary = face_relational_imaginary_limbs
        + at * (uint64_t)face_relational_limb_count;
    zero_unsigned_limbs(current, face_current_limb_count);
    zero_unsigned_limbs(real, face_relational_limb_count);
    zero_unsigned_limbs(imaginary, face_relational_limb_count);
    *real_sign = 0U;
    *imaginary_sign = 0U;
    for (uint32_t candidate = 0U; candidate < candidate_count; ++candidate) {
        const uint32_t slot = candidate_selected_slots[candidate];
        if (slot >= selected_slot_count) {
            atomicExch(obstruction, 1U);
            return;
        }
        const uint32_t addressed_face = selected_faces[slot];
        if (addressed_face % face_count != face) continue;
        const uint32_t target = candidate_to_target[candidate];
        if (target == 0xffffffffU) continue;
        if (target >= target_count) {
            atomicExch(obstruction, 2U);
            return;
        }
        const uint64_t source = (uint64_t)target * (uint64_t)factor_count + factor;
        add_unsigned_limbs_checked(
            current,
            target_current_limbs + source * (uint64_t)target_limb_count,
            face_current_limb_count,
            target_limb_count,
            obstruction);
        add_signed_magnitude_width(
            real_sign, real, face_relational_limb_count,
            target_relational_real_sign[source],
            target_relational_real_limbs
                + source * (uint64_t)target_relational_limb_count,
            target_relational_limb_count);
        add_signed_magnitude_width(
            imaginary_sign, imaginary, face_relational_limb_count,
            target_relational_imaginary_sign[source],
            target_relational_imaginary_limbs
                + source * (uint64_t)target_relational_limb_count,
            target_relational_limb_count);
    }
    if (unsigned_limbs_are_zero(real, face_relational_limb_count)) *real_sign = 0U;
    if (unsigned_limbs_are_zero(imaginary, face_relational_limb_count)) *imaginary_sign = 0U;
}

extern "C" __global__ void contract_membrane_completed_target_observer(
    const uint32_t *face_current_limbs,
    const uint8_t *face_relational_real_sign,
    const uint32_t *face_relational_real_limbs,
    const uint8_t *face_relational_imaginary_sign,
    const uint32_t *face_relational_imaginary_limbs,
    const uint32_t *receiver_class_bases,
    const uint64_t *source_class_factor_offsets,
    const uint32_t *source_class_factors,
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
    uint8_t *dot_real_sign,
    uint32_t *dot_real_limbs,
    uint8_t *dot_imaginary_sign,
    uint32_t *dot_imaginary_limbs,
    uint32_t *target_norm_limbs,
    uint32_t *relational_norm_limbs,
    uint32_t *first_scratch,
    uint32_t *second_scratch,
    uint32_t *third_scratch,
    uint32_t *obstruction,
    uint32_t face_count,
    uint32_t factor_count,
    uint32_t family_count,
    uint32_t receiver_count,
    uint32_t axis_count,
    uint32_t face_current_limb_count,
    uint32_t face_relational_limb_count,
    uint32_t family_limb_count,
    uint32_t overlap_limb_count,
    uint32_t scratch_limb_count,
    uint32_t contact_limb_count)
{
    const uint64_t at = (uint64_t)blockIdx.x * blockDim.x + threadIdx.x;
    const uint64_t work = (uint64_t)face_count * (uint64_t)axis_count;
    if (at >= work || axis_count == 0U) return;
    const uint32_t face = (uint32_t)(at / axis_count);
    const uint32_t axis = (uint32_t)(at % axis_count);
    uint32_t *first = first_scratch + at * (uint64_t)scratch_limb_count;
    uint32_t *second = second_scratch + at * (uint64_t)scratch_limb_count;
    uint32_t *third = third_scratch + at * (uint64_t)scratch_limb_count;

    if (axis < family_count) {
        const uint64_t output = (uint64_t)face * (uint64_t)family_count + axis;
        const uint64_t output_at = output * (uint64_t)overlap_limb_count;
        action_overlap_sign[output] = 0U;
        reflected_overlap_sign[output] = 0U;
        zero_unsigned_limbs(action_overlap_limbs + output_at, overlap_limb_count);
        zero_unsigned_limbs(reflected_overlap_limbs + output_at, overlap_limb_count);
        for (uint32_t factor = 0U; factor < factor_count; ++factor) {
            const uint64_t coordinate =
                (uint64_t)face * (uint64_t)factor_count + factor;
            const uint32_t *current = face_current_limbs
                + coordinate * (uint64_t)face_current_limb_count;
            if (unsigned_limbs_are_zero(current, face_current_limb_count)) continue;
            const int8_t orientation = family_orientation[
                (uint64_t)axis * (uint64_t)factor_count + factor];
            const uint8_t orientation_sign = orientation < 0
                ? 2U : (orientation > 0 ? 1U : 0U);
            if (orientation_sign == 0U) continue;
            multiply_unsigned_limbs(
                current, face_current_limb_count,
                current, face_current_limb_count,
                first, scratch_limb_count);
            scale_unsigned_limbs(
                first, scratch_limb_count, factor_capacity[factor],
                third, scratch_limb_count);
            add_signed_magnitude(
                reflected_overlap_sign + output,
                reflected_overlap_limbs + output_at,
                orientation_sign, third, overlap_limb_count);
            const uint8_t component_signs[2] = {
                face_relational_real_sign[coordinate],
                face_relational_imaginary_sign[coordinate]
            };
            const uint32_t *component_limbs[2] = {
                face_relational_real_limbs
                    + coordinate * (uint64_t)face_relational_limb_count,
                face_relational_imaginary_limbs
                    + coordinate * (uint64_t)face_relational_limb_count
            };
            for (uint32_t component = 0U; component < 2U; ++component) {
                if (component_signs[component] == 0U) continue;
                multiply_unsigned_limbs(
                    current, face_current_limb_count,
                    component_limbs[component], face_relational_limb_count,
                    first, scratch_limb_count);
                scale_unsigned_limbs(
                    first, scratch_limb_count, factor_capacity[factor],
                    third, scratch_limb_count);
                add_signed_magnitude(
                    action_overlap_sign + output,
                    action_overlap_limbs + output_at,
                    product_sign(orientation_sign, component_signs[component]),
                    third, overlap_limb_count);
            }
        }
        const uint64_t family_at = (uint64_t)axis * (uint64_t)family_limb_count;
        const uint64_t contact_at = output * (uint64_t)contact_limb_count;
        contact_real_sign[output] = product_sign(
            family_real_sign[axis], action_overlap_sign[output]);
        contact_imaginary_sign[output] = product_sign(
            family_imaginary_sign[axis], action_overlap_sign[output]);
        multiply_unsigned_limbs(
            family_real_limbs + family_at, family_limb_count,
            action_overlap_limbs + output_at, overlap_limb_count,
            contact_real_limbs + contact_at, contact_limb_count);
        multiply_unsigned_limbs(
            family_imaginary_limbs + family_at, family_limb_count,
            action_overlap_limbs + output_at, overlap_limb_count,
            contact_imaginary_limbs + contact_at, contact_limb_count);
    }

    if (axis < receiver_count) {
        const uint64_t output = (uint64_t)face * (uint64_t)receiver_count + axis;
        const uint64_t output_at = output * (uint64_t)overlap_limb_count;
        receiver_overlap_sign[output] = 0U;
        receiver_action_norm_sign[output] = 0U;
        zero_unsigned_limbs(receiver_overlap_limbs + output_at, overlap_limb_count);
        zero_unsigned_limbs(receiver_action_norm_limbs + output_at, overlap_limb_count);
        for (uint32_t receiver_class = receiver_class_bases[axis];
             receiver_class < receiver_class_bases[axis + 1U];
             ++receiver_class) {
            zero_unsigned_limbs(first, scratch_limb_count);
            for (uint64_t incidence = source_class_factor_offsets[receiver_class];
                 incidence < source_class_factor_offsets[receiver_class + 1U];
                 ++incidence) {
                const uint32_t factor = source_class_factors[incidence];
                if (factor >= factor_count) continue;
                const uint64_t coordinate =
                    (uint64_t)face * (uint64_t)factor_count + factor;
                add_unsigned_limbs_checked(
                    first,
                    face_current_limbs
                        + coordinate * (uint64_t)face_current_limb_count,
                    scratch_limb_count,
                    face_current_limb_count,
                    obstruction);
            }
            for (uint32_t component = 0U; component < 2U; ++component) {
                uint8_t sum_sign = 0U;
                zero_unsigned_limbs(second, scratch_limb_count);
                for (uint64_t incidence = source_class_factor_offsets[receiver_class];
                     incidence < source_class_factor_offsets[receiver_class + 1U];
                     ++incidence) {
                    const uint32_t factor = source_class_factors[incidence];
                    if (factor >= factor_count) continue;
                    const uint64_t coordinate =
                        (uint64_t)face * (uint64_t)factor_count + factor;
                    const uint8_t sign = component == 0U
                        ? face_relational_real_sign[coordinate]
                        : face_relational_imaginary_sign[coordinate];
                    const uint32_t *magnitude = component == 0U
                        ? face_relational_real_limbs
                            + coordinate * (uint64_t)face_relational_limb_count
                        : face_relational_imaginary_limbs
                            + coordinate * (uint64_t)face_relational_limb_count;
                    add_signed_magnitude_width(
                        &sum_sign, second, scratch_limb_count,
                        sign, magnitude, face_relational_limb_count);
                }
                if (sum_sign == 0U) continue;
                multiply_unsigned_limbs(
                    first, scratch_limb_count,
                    second, scratch_limb_count,
                    third, scratch_limb_count);
                add_signed_magnitude(
                    receiver_overlap_sign + output,
                    receiver_overlap_limbs + output_at,
                    sum_sign, third, overlap_limb_count);
                multiply_unsigned_limbs(
                    second, scratch_limb_count,
                    second, scratch_limb_count,
                    third, scratch_limb_count);
                add_signed_magnitude(
                    receiver_action_norm_sign + output,
                    receiver_action_norm_limbs + output_at,
                    1U, third, overlap_limb_count);
            }
        }
    }

    if (axis == 0U) {
        dot_real_sign[face] = 0U;
        dot_imaginary_sign[face] = 0U;
        zero_unsigned_limbs(
            dot_real_limbs + (uint64_t)face * scratch_limb_count, scratch_limb_count);
        zero_unsigned_limbs(
            dot_imaginary_limbs + (uint64_t)face * scratch_limb_count, scratch_limb_count);
        zero_unsigned_limbs(
            target_norm_limbs + (uint64_t)face * scratch_limb_count, scratch_limb_count);
        zero_unsigned_limbs(
            relational_norm_limbs + (uint64_t)face * scratch_limb_count, scratch_limb_count);
        for (uint32_t factor = 0U; factor < factor_count; ++factor) {
            const uint64_t coordinate =
                (uint64_t)face * (uint64_t)factor_count + factor;
            const uint32_t *current = face_current_limbs
                + coordinate * (uint64_t)face_current_limb_count;
            multiply_unsigned_limbs(
                current, face_current_limb_count,
                current, face_current_limb_count,
                first, scratch_limb_count);
            add_unsigned_limbs(
                target_norm_limbs + (uint64_t)face * scratch_limb_count,
                first, scratch_limb_count);
            const uint8_t component_signs[2] = {
                face_relational_real_sign[coordinate],
                face_relational_imaginary_sign[coordinate]
            };
            const uint32_t *component_limbs[2] = {
                face_relational_real_limbs
                    + coordinate * (uint64_t)face_relational_limb_count,
                face_relational_imaginary_limbs
                    + coordinate * (uint64_t)face_relational_limb_count
            };
            for (uint32_t component = 0U; component < 2U; ++component) {
                if (component_signs[component] == 0U) continue;
                multiply_unsigned_limbs(
                    current, face_current_limb_count,
                    component_limbs[component], face_relational_limb_count,
                    first, scratch_limb_count);
                add_signed_magnitude(
                    component == 0U ? dot_real_sign + face : dot_imaginary_sign + face,
                    component == 0U
                        ? dot_real_limbs + (uint64_t)face * scratch_limb_count
                        : dot_imaginary_limbs + (uint64_t)face * scratch_limb_count,
                    component_signs[component], first, scratch_limb_count);
                multiply_unsigned_limbs(
                    component_limbs[component], face_relational_limb_count,
                    component_limbs[component], face_relational_limb_count,
                    first, scratch_limb_count);
                add_unsigned_limbs(
                    relational_norm_limbs + (uint64_t)face * scratch_limb_count,
                    first, scratch_limb_count);
            }
        }
    }
}

extern "C" __global__ void append_membrane_completed_target_oriented_relational_component(
    const uint8_t *dot_real_sign,
    const uint32_t *dot_real_limbs,
    const uint32_t *target_norm_limbs,
    const uint32_t *relational_norm_limbs,
    uint8_t *compatibility_sign,
    uint32_t *compatibility_limbs,
    uint32_t *phase_norm_limbs,
    uint32_t *norm_product_limbs,
    uint32_t *scratch,
    uint32_t face_count,
    uint32_t component_count,
    uint32_t relational_component,
    uint32_t limb_count)
{
    const uint32_t face = blockIdx.x * blockDim.x + threadIdx.x;
    if (face >= face_count || relational_component >= component_count) return;
    const uint64_t component =
        (uint64_t)face * (uint64_t)component_count + relational_component;
    uint32_t *compatibility = compatibility_limbs
        + component * (uint64_t)limb_count;
    uint32_t *norm = phase_norm_limbs
        + component * (uint64_t)limb_count;
    uint32_t *product = scratch + (uint64_t)face * (uint64_t)limb_count;
    zero_unsigned_limbs(compatibility, limb_count);
    zero_unsigned_limbs(norm, limb_count);
    zero_unsigned_limbs(product, limb_count);
    const uint32_t *dot_real = dot_real_limbs
        + (uint64_t)face * (uint64_t)limb_count;
    compatibility_sign[component] = dot_real_sign[face];
    for (uint32_t limb = 0U; limb < limb_count; ++limb) {
        compatibility[limb] = dot_real[limb];
    }
    multiply_unsigned_limbs(
        target_norm_limbs + (uint64_t)face * (uint64_t)limb_count,
        limb_count,
        relational_norm_limbs + (uint64_t)face * (uint64_t)limb_count,
        limb_count,
        product, limb_count);
    for (uint32_t limb = 0U; limb < limb_count; ++limb) {
        norm[limb] = product[limb];
        norm_product_limbs[(uint64_t)face * limb_count + limb] = product[limb];
    }
}

extern "C" __global__ void verify_resident_receiver_history_compression(
    const unsigned long long* quotient_by_source,
    unsigned long long source_population,
    const unsigned long long* source_edge_from,
    const unsigned long long* source_edge_to,
    const unsigned long long* source_edge_generator,
    unsigned long long source_edge_population,
    const unsigned long long* native_generator_targets,
    unsigned long long native_population,
    unsigned long long generator_population,
    const unsigned long long* fibre_native_by_source,
    unsigned int* obstruction) {
    const unsigned long long at =
        (unsigned long long)blockIdx.x * blockDim.x + threadIdx.x;
    if (at < source_edge_population) {
        const unsigned long long from = source_edge_from[at];
        const unsigned long long to = source_edge_to[at];
        const unsigned long long generator = source_edge_generator[at];
        if (from >= source_population || to >= source_population ||
            generator >= generator_population) {
            atomicOr(obstruction, 1u);
        } else {
            const unsigned long long native_from = quotient_by_source[from];
            const unsigned long long native_to = quotient_by_source[to];
            if (native_from >= native_population || native_to >= native_population ||
                native_generator_targets[generator * native_population + native_from] !=
                    native_to) {
                atomicOr(obstruction, 1u);
            }
        }
    }
    if (at < source_population &&
        (quotient_by_source[at] >= native_population ||
         fibre_native_by_source[at] != quotient_by_source[at])) {
        atomicOr(obstruction, 2u);
    }
}

extern "C" __global__ void expand_membrane_compact_factor_current_sections(
    const uint32_t *compact_current_limbs,
    const uint32_t *successor_factors,
    uint32_t *native_current_limbs,
    uint32_t section_count,
    uint32_t successor_factor_count,
    uint32_t native_factor_count,
    uint32_t limb_count)
{
    const uint32_t section = blockIdx.x * blockDim.x + threadIdx.x;
    if (section >= section_count) return;
    uint32_t *native = native_current_limbs
        + (uint64_t)section * (uint64_t)native_factor_count * (uint64_t)limb_count;
    zero_unsigned_limbs(native, native_factor_count * limb_count);
    const uint32_t *compact = compact_current_limbs
        + (uint64_t)section * (uint64_t)successor_factor_count * (uint64_t)limb_count;
    for (uint32_t local = 0U; local < successor_factor_count; ++local) {
        const uint32_t factor = successor_factors[local];
        if (factor >= native_factor_count) continue;
        uint32_t *target = native
            + (uint64_t)factor * (uint64_t)limb_count;
        const uint32_t *source = compact
            + (uint64_t)local * (uint64_t)limb_count;
        for (uint32_t limb = 0U; limb < limb_count; ++limb) target[limb] = source[limb];
    }
}

extern "C" __global__ void identify_membrane_equal_factor_current_sections(
    const uint32_t *candidate_current_limbs,
    const uint8_t *candidate_state_present,
    const uint32_t *candidate_states,
    uint32_t *representatives,
    uint32_t candidate_count,
    uint32_t factor_count,
    uint32_t limb_count)
{
    const uint32_t candidate = blockIdx.x * blockDim.x + threadIdx.x;
    if (candidate >= candidate_count) return;
    const uint64_t row_limbs = (uint64_t)factor_count * (uint64_t)limb_count;
    const uint32_t *row = candidate_current_limbs + (uint64_t)candidate * row_limbs;
    if (unsigned_limbs_are_zero(row, row_limbs)) {
        representatives[candidate] = 0xffffffffU;
        return;
    }
    uint32_t representative = candidate;
    for (uint32_t prior = 0U; prior < candidate; ++prior) {
        if (membrane_factor_current_sections_are_equal(
                candidate_current_limbs,
                candidate_state_present,
                candidate_states,
                candidate,
                prior,
                row_limbs)) {
            representative = prior;
            break;
        }
    }
    representatives[candidate] = representative;
}

extern "C" __global__ void compact_membrane_equal_factor_current_sections(
    const uint32_t *candidate_current_limbs,
    const uint32_t *source_weight_limbs,
    const uint32_t *representatives,
    const uint8_t *candidate_state_present,
    const uint32_t *candidate_states,
    uint32_t *target_current_limbs,
    uint32_t *target_weight_limbs,
    uint8_t *target_state_present,
    uint32_t *target_states,
    uint32_t *candidate_to_target,
    uint32_t *target_count,
    uint32_t source_context_count,
    uint32_t factor_count,
    uint32_t generator_count,
    uint32_t current_limb_count,
    uint32_t source_weight_limb_count,
    uint32_t target_weight_limb_count)
{
    const uint32_t candidate = blockIdx.x * blockDim.x + threadIdx.x;
    const uint32_t candidate_count = source_context_count * generator_count;
    if (candidate >= candidate_count) return;
    const uint32_t representative = representatives[candidate];
    if (representative == 0xffffffffU) {
        candidate_to_target[candidate] = 0xffffffffU;
        return;
    }
    uint32_t compact = 0U;
    for (uint32_t prior = 0U; prior < representative; ++prior) {
        if (representatives[prior] == prior) ++compact;
    }
    candidate_to_target[candidate] = compact;
    if (representative != candidate) return;
    const uint64_t row_limbs = (uint64_t)factor_count * (uint64_t)current_limb_count;
    const uint32_t *source_row = candidate_current_limbs + (uint64_t)candidate * row_limbs;
    uint32_t *target_row = target_current_limbs + (uint64_t)compact * row_limbs;
    for (uint64_t limb = 0ULL; limb < row_limbs; ++limb) target_row[limb] = source_row[limb];
    target_state_present[compact] = candidate_state_present[candidate];
    target_states[compact] = candidate_states[candidate];
    uint32_t *target_weight = target_weight_limbs
        + (uint64_t)compact * (uint64_t)target_weight_limb_count;
    zero_unsigned_limbs(target_weight, target_weight_limb_count);
    for (uint32_t member = 0U; member < candidate_count; ++member) {
        if (representatives[member] != candidate) continue;
        const uint32_t context = member / generator_count;
        const uint32_t *source_weight = source_weight_limbs
            + (uint64_t)context * (uint64_t)source_weight_limb_count;
        uint64_t carry = 0ULL;
        uint32_t limb = 0U;
        for (; limb < source_weight_limb_count; ++limb) {
            const uint64_t sum =
                (uint64_t)target_weight[limb] + (uint64_t)source_weight[limb] + carry;
            target_weight[limb] = (uint32_t)sum;
            carry = sum >> 32U;
        }
        while (carry != 0ULL && limb < target_weight_limb_count) {
            const uint64_t sum = (uint64_t)target_weight[limb] + carry;
            target_weight[limb] = (uint32_t)sum;
            carry = sum >> 32U;
            ++limb;
        }
    }
    atomicMax(target_count, compact + 1U);
}

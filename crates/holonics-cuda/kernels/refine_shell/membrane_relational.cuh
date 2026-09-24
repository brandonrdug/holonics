// Membrane sparse relational current.
// This fragment is included by refine_shell.cu after refine_shared.cuh.

extern "C" __global__ void conduct_membrane_local_contacts(
    const uint64_t *cell_offsets,
    const uint32_t *cell_factors,
    const uint64_t *cell_multiplicities,
    const uint64_t *cell_total_mass,
    const uint64_t *factor_capacity,
    const int8_t *family_orientation,
    const uint8_t *family_real_sign,
    const uint32_t *family_real_limbs,
    const uint8_t *family_imaginary_sign,
    const uint32_t *family_imaginary_limbs,
    int64_t *overlap_numerator,
    uint64_t *overlap_denominator,
    uint8_t *contact_real_sign,
    uint32_t *contact_real_limbs,
    uint8_t *contact_imaginary_sign,
    uint32_t *contact_imaginary_limbs,
    uint32_t left_cell,
    uint32_t right_cell,
    uint32_t cell_count,
    uint32_t factor_count,
    uint32_t family_count,
    uint32_t family_limb_count,
    uint32_t contact_limb_count)
{
    const uint32_t family = blockIdx.x * blockDim.x + threadIdx.x;
    if (family >= family_count || left_cell >= cell_count || right_cell >= cell_count) return;
    const uint64_t left_begin = cell_offsets[left_cell];
    const uint64_t left_end = cell_offsets[left_cell + 1U];
    const uint64_t right_begin = cell_offsets[right_cell];
    const uint64_t right_end = cell_offsets[right_cell + 1U];
    uint64_t left_at = left_begin;
    uint64_t right_at = right_begin;
    __int128 numerator = 0;
    while (left_at < left_end && right_at < right_end) {
        const uint32_t left_factor = cell_factors[left_at];
        const uint32_t right_factor = cell_factors[right_at];
        if (left_factor < right_factor) {
            ++left_at;
            continue;
        }
        if (right_factor < left_factor) {
            ++right_at;
            continue;
        }
        const int8_t orientation =
            family_orientation[(uint64_t)family * (uint64_t)factor_count + left_factor];
        numerator += (__int128)orientation
                   * (__int128)factor_capacity[left_factor]
                   * (__int128)cell_multiplicities[left_at]
                   * (__int128)cell_multiplicities[right_at];
        ++left_at;
        ++right_at;
    }
    const uint64_t denominator =
        cell_total_mass[left_cell] * cell_total_mass[right_cell];
    overlap_numerator[family] = (int64_t)numerator;
    overlap_denominator[family] = denominator;
    const uint64_t magnitude = numerator < 0 ? (uint64_t)(-numerator) : (uint64_t)numerator;
    const uint8_t overlap_sign = numerator < 0 ? 2U : (numerator > 0 ? 1U : 0U);
    const uint64_t family_at = (uint64_t)family * (uint64_t)family_limb_count;
    const uint64_t contact_at = (uint64_t)family * (uint64_t)contact_limb_count;
    contact_real_sign[family] = product_sign(family_real_sign[family], overlap_sign);
    contact_imaginary_sign[family] =
        product_sign(family_imaginary_sign[family], overlap_sign);
    scale_unsigned_limbs(
        family_real_limbs + family_at,
        family_limb_count,
        magnitude,
        contact_real_limbs + contact_at,
        contact_limb_count);
    scale_unsigned_limbs(
        family_imaginary_limbs + family_at,
        family_limb_count,
        magnitude,
        contact_imaginary_limbs + contact_at,
        contact_limb_count);
}

extern "C" __global__ void conduct_membrane_sparse_relational_forward(
    const uint64_t *row_offsets,
    const uint32_t *term_factors,
    const uint64_t *term_ingress_population,
    const uint64_t *term_emanation_population,
    const uint64_t *term_return_population,
    const uint64_t *factor_current,
    const int8_t *family_orientation,
    int64_t *row_family_real,
    int64_t *row_family_imaginary,
    uint32_t row_population,
    uint32_t factor_population,
    uint32_t family_population)
{
    const uint64_t coordinate =
        (uint64_t)blockIdx.x * (uint64_t)blockDim.x + (uint64_t)threadIdx.x;
    const uint64_t population = (uint64_t)row_population * (uint64_t)family_population;
    if (coordinate >= population) return;
    const uint32_t row = (uint32_t)(coordinate / (uint64_t)family_population);
    const uint32_t family = (uint32_t)(coordinate % (uint64_t)family_population);
    __int128 real = 0;
    __int128 imaginary = 0;
    for (uint64_t term = row_offsets[row]; term < row_offsets[row + 1U]; ++term) {
        const uint32_t factor = term_factors[term];
        const int64_t orientation =
            (int64_t)family_orientation[(uint64_t)family * (uint64_t)factor_population + factor];
        const __int128 current = (__int128)factor_current[factor];
        const __int128 ingress = (__int128)term_ingress_population[term];
        real += ((__int128)term_emanation_population[term] - ingress)
              * current * (__int128)orientation;
        imaginary += ((__int128)term_return_population[term] - ingress)
                   * current * (__int128)orientation;
    }
    row_family_real[coordinate] = (int64_t)real;
    row_family_imaginary[coordinate] = (int64_t)imaginary;
}

extern "C" __global__ void return_membrane_sparse_relational_adjoint(
    const uint32_t *term_rows,
    const uint32_t *term_factors,
    const uint64_t *term_ingress_population,
    const uint64_t *term_emanation_population,
    const uint64_t *term_return_population,
    const int64_t *row_family_real,
    const int64_t *row_family_imaginary,
    const uint8_t *family_real_sign,
    const uint8_t *family_imaginary_sign,
    int64_t *factor_real,
    int64_t *factor_imaginary,
    uint64_t term_population,
    uint32_t family_population)
{
    const uint64_t coordinate =
        (uint64_t)blockIdx.x * (uint64_t)blockDim.x + (uint64_t)threadIdx.x;
    const uint64_t population = term_population * (uint64_t)family_population;
    if (coordinate >= population) return;
    const uint64_t term = coordinate / (uint64_t)family_population;
    const uint32_t family = (uint32_t)(coordinate % (uint64_t)family_population);
    const uint32_t row = term_rows[term];
    const uint32_t factor = term_factors[term];
    const uint64_t row_family = (uint64_t)row * (uint64_t)family_population + family;
    const __int128 a_real = (__int128)row_family_real[row_family];
    const __int128 a_imaginary = (__int128)row_family_imaginary[row_family];
    const __int128 j_real = (__int128)signed_family_phase(family_real_sign[family]);
    const __int128 j_imaginary =
        (__int128)signed_family_phase(family_imaginary_sign[family]);
    const __int128 response_real = j_real * a_real - j_imaginary * a_imaginary;
    const __int128 response_imaginary = j_real * a_imaginary + j_imaginary * a_real;
    const __int128 ingress = (__int128)term_ingress_population[term];
    const __int128 incidence_real = (__int128)term_emanation_population[term] - ingress;
    const __int128 incidence_imaginary = (__int128)term_return_population[term] - ingress;
    const __int128 returned_real =
        incidence_real * response_real + incidence_imaginary * response_imaginary;
    const __int128 returned_imaginary =
        incidence_real * response_imaginary - incidence_imaginary * response_real;
    atomic_add_signed_i64(factor_real + factor, (int64_t)returned_real);
    atomic_add_signed_i64(factor_imaginary + factor, (int64_t)returned_imaginary);
}

extern "C" __global__ void transport_membrane_sparse_relational_generator_limbs(
    const uint32_t *generator_targets,
    const uint32_t *source_state_present,
    const uint8_t *source_real_sign,
    const uint32_t *source_real_limbs,
    const uint8_t *source_imaginary_sign,
    const uint32_t *source_imaginary_limbs,
    uint8_t *target_real_sign,
    uint32_t *target_real_limbs,
    uint8_t *target_imaginary_sign,
    uint32_t *target_imaginary_limbs,
    uint32_t factor_count,
    uint32_t generator_count,
    uint32_t state_count,
    uint32_t source_limb_count,
    uint32_t target_limb_count,
    uint32_t *obstruction)
{
    const uint64_t at = (uint64_t)blockIdx.x * blockDim.x + threadIdx.x;
    const uint64_t population = (uint64_t)state_count * (uint64_t)generator_count
        * (uint64_t)factor_count;
    if (at >= population || source_limb_count == 0U || target_limb_count == 0U) return;
    const uint64_t state_generator = at / factor_count;
    const uint32_t state = (uint32_t)(state_generator / generator_count);
    const uint32_t generator = (uint32_t)(state_generator % generator_count);
    const uint32_t target = (uint32_t)(at % factor_count);
    const uint64_t target_at = at * (uint64_t)target_limb_count;
    target_real_sign[at] = 0U;
    target_imaginary_sign[at] = 0U;
    zero_unsigned_limbs(target_real_limbs + target_at, target_limb_count);
    zero_unsigned_limbs(target_imaginary_limbs + target_at, target_limb_count);
    if (source_state_present[state] == 0U) return;
    for (uint32_t source = 0U; source < factor_count; ++source) {
        const uint32_t image = generator_targets[
            (uint64_t)generator * (uint64_t)factor_count + source];
        if (image >= factor_count) {
            atomicExch(obstruction, 1U);
            return;
        }
        if (image != target) continue;
        const uint64_t source_coordinate =
            (uint64_t)state * (uint64_t)factor_count + source;
        const uint64_t source_at = source_coordinate * (uint64_t)source_limb_count;
        add_signed_magnitude_width(
            target_real_sign + at, target_real_limbs + target_at, target_limb_count,
            source_real_sign[source_coordinate], source_real_limbs + source_at,
            source_limb_count);
        add_signed_magnitude_width(
            target_imaginary_sign + at, target_imaginary_limbs + target_at, target_limb_count,
            source_imaginary_sign[source_coordinate], source_imaginary_limbs + source_at,
            source_limb_count);
    }
}

extern "C" __global__ void condition_and_aggregate_membrane_sparse_relational_current_by_target_state(
    const uint32_t *source_state_present,
    const uint32_t *source_states,
    const uint8_t *transported_real_sign,
    const uint32_t *transported_real_limbs,
    const uint8_t *transported_imaginary_sign,
    const uint32_t *transported_imaginary_limbs,
    const uint32_t *selected_faces,
    const uint32_t *selected_restrictions,
    const uint32_t *restriction_current_limbs,
    const uint32_t *presented_current_limbs,
    const uint32_t *boundary_states,
    const uint32_t *restriction_target_states,
    const uint32_t *candidate_selected_slots,
    const uint32_t *target_member_offsets,
    const uint32_t *target_members,
    const uint32_t *junction_target_states,
    uint32_t *target_state_present,
    uint32_t *target_states,
    uint8_t *target_real_sign,
    uint32_t *target_real_limbs,
    uint8_t *target_imaginary_sign,
    uint32_t *target_imaginary_limbs,
    uint32_t *product_scratch,
    uint32_t *returned_product_scratch,
    uint32_t factor_count,
    uint32_t generator_count,
    uint32_t boundary_state_count,
    uint32_t source_state_count,
    uint32_t selected_slot_count,
    uint32_t target_count,
    uint32_t source_limb_count,
    uint32_t restriction_limb_count,
    uint32_t presented_limb_count,
    uint32_t presented_current_present,
    uint32_t target_limb_count,
    uint32_t *obstruction)
{
    const uint64_t output = (uint64_t)blockIdx.x * blockDim.x + threadIdx.x;
    const uint64_t output_population = (uint64_t)target_count * (uint64_t)factor_count;
    if (output >= output_population || generator_count == 0U
        || boundary_state_count == 0U || source_state_count == 0U) return;
    const uint32_t target = (uint32_t)(output / factor_count);
    const uint32_t factor = (uint32_t)(output % factor_count);
    const uint32_t target_state = junction_target_states[target];
    const uint64_t accumulator_at = output * (uint64_t)target_limb_count;
    uint8_t *real_sign = target_real_sign + output;
    uint8_t *imaginary_sign = target_imaginary_sign + output;
    uint32_t *real_accumulator = target_real_limbs + accumulator_at;
    uint32_t *imaginary_accumulator = target_imaginary_limbs + accumulator_at;
    uint32_t *product = product_scratch + accumulator_at;
    uint32_t *returned_product = returned_product_scratch + accumulator_at;
    *real_sign = 0U;
    *imaginary_sign = 0U;
    zero_unsigned_limbs(real_accumulator, target_limb_count);
    zero_unsigned_limbs(imaginary_accumulator, target_limb_count);
    zero_unsigned_limbs(product, target_limb_count);
    zero_unsigned_limbs(returned_product, target_limb_count);
    bool met_target_state = false;
    for (uint32_t member = target_member_offsets[target];
         member < target_member_offsets[target + 1U]; ++member) {
        const uint32_t candidate = target_members[member];
        const uint32_t slot = candidate_selected_slots[candidate];
        if (slot >= selected_slot_count) {
            atomicOr(obstruction, 1U);
            return;
        }
        const uint32_t selected_restriction = selected_restrictions[slot];
        const uint32_t selected_boundary = selected_restriction % boundary_state_count;
        if (restriction_target_states[selected_restriction] != target_state) {
            atomicOr(obstruction, 2U);
            continue;
        }
        const uint32_t face = selected_faces[slot];
        const uint32_t generator = face % generator_count;
        const uint32_t *restriction_value = restriction_current_limbs
            + ((uint64_t)selected_restriction * (uint64_t)factor_count + factor)
                * (uint64_t)restriction_limb_count;
        for (uint32_t source_state_coordinate = 0U;
             source_state_coordinate < source_state_count; ++source_state_coordinate) {
            if (source_state_present[source_state_coordinate] == 0U
                || source_states[source_state_coordinate]
                    != boundary_states[selected_boundary]) continue;
            met_target_state = true;
            const uint64_t at = ((uint64_t)source_state_coordinate
                    * (uint64_t)generator_count + generator)
                * (uint64_t)factor_count + factor;
            const uint8_t component_signs[2] = {
                transported_real_sign[at], transported_imaginary_sign[at]
            };
            const uint32_t *component_limbs[2] = {
                transported_real_limbs + at * (uint64_t)source_limb_count,
                transported_imaginary_limbs + at * (uint64_t)source_limb_count
            };
            for (uint32_t component = 0U; component < 2U; ++component) {
                if (component_signs[component] == 0U
                    || unsigned_limbs_are_zero(
                        component_limbs[component], source_limb_count)) continue;
                multiply_unsigned_limbs(
                    component_limbs[component], source_limb_count,
                    restriction_value, restriction_limb_count,
                    product, target_limb_count);
                const uint32_t *conditioned = product;
                if (presented_current_present != 0U) {
                    multiply_unsigned_limbs(
                        product, target_limb_count,
                        presented_current_limbs
                            + (uint64_t)factor * presented_limb_count,
                        presented_limb_count,
                        returned_product, target_limb_count);
                    conditioned = returned_product;
                }
                if (component == 0U) {
                    add_signed_magnitude(
                        real_sign, real_accumulator,
                        component_signs[component], conditioned, target_limb_count);
                } else {
                    add_signed_magnitude(
                        imaginary_sign, imaginary_accumulator,
                        component_signs[component], conditioned, target_limb_count);
                }
            }
        }
    }
    if (factor == 0U) {
        target_states[target] = target_state;
        if (met_target_state) target_state_present[target] = 1U;
    }
    if (unsigned_limbs_are_zero(real_accumulator, target_limb_count)) *real_sign = 0U;
    if (unsigned_limbs_are_zero(imaginary_accumulator, target_limb_count)) *imaginary_sign = 0U;
}

extern "C" __global__ void widen_membrane_sparse_relational_i64_current(
    const int64_t *source_real,
    const int64_t *source_imaginary,
    uint8_t *target_real_sign,
    uint32_t *target_real_limbs,
    uint8_t *target_imaginary_sign,
    uint32_t *target_imaginary_limbs,
    uint32_t factor_count,
    uint32_t limb_count)
{
    const uint32_t factor = blockIdx.x * blockDim.x + threadIdx.x;
    if (factor >= factor_count || limb_count == 0U) return;
    const uint64_t at = (uint64_t)factor * (uint64_t)limb_count;
    target_real_sign[factor] = signed_i64_magnitude_sign(source_real[factor]);
    target_imaginary_sign[factor] = signed_i64_magnitude_sign(source_imaginary[factor]);
    zero_unsigned_limbs(target_real_limbs + at, limb_count);
    zero_unsigned_limbs(target_imaginary_limbs + at, limb_count);
    const uint64_t real_magnitude = magnitude_i64(source_real[factor]);
    const uint64_t imaginary_magnitude = magnitude_i64(source_imaginary[factor]);
    target_real_limbs[at] = (uint32_t)real_magnitude;
    target_imaginary_limbs[at] = (uint32_t)imaginary_magnitude;
    if (limb_count > 1U) {
        target_real_limbs[at + 1U] = (uint32_t)(real_magnitude >> 32U);
        target_imaginary_limbs[at + 1U] = (uint32_t)(imaginary_magnitude >> 32U);
    }
}

extern "C" __global__ void form_membrane_sparse_relational_boundary_chunks_arbitrary(
    const uint8_t *transported_real_sign,
    const uint32_t *transported_real_limbs,
    const uint8_t *transported_imaginary_sign,
    const uint32_t *transported_imaginary_limbs,
    const uint32_t *relational_state_present,
    const uint32_t *relational_states,
    const uint32_t *source_state_ids,
    const uint32_t *pair_factors,
    const uint32_t *current_limbs,
    const uint32_t *restriction_limbs,
    const uint8_t *restriction_present,
    uint8_t *partial_signs,
    uint32_t *partial_limbs,
    uint32_t *first_scratch,
    uint32_t *second_scratch,
    uint32_t *third_scratch,
    uint32_t pair_count,
    uint32_t factor_count,
    uint32_t face_count,
    uint32_t source_state_count,
    uint32_t port_count,
    uint32_t generator_count,
    uint32_t relational_state_count,
    uint32_t relational_limb_count,
    uint32_t chunk_count,
    uint32_t chunk_size,
    uint32_t current_limb_count,
    uint32_t restriction_limb_count,
    uint32_t output_limb_count,
    uint32_t *obstruction)
{
    const uint64_t at = (uint64_t)blockIdx.x * blockDim.x + threadIdx.x;
    const uint64_t work = (uint64_t)face_count * (uint64_t)chunk_count;
    if (at >= work || generator_count == 0U || port_count == 0U
        || chunk_count == 0U || relational_limb_count == 0U) return;
    const uint32_t face = (uint32_t)(at / chunk_count);
    const uint32_t chunk = (uint32_t)(at % chunk_count);
    const uint64_t section = (uint64_t)face * 3ULL;
    for (uint32_t axis = 0U; axis < 3U; ++axis) {
        const uint64_t partial = (section + axis) * (uint64_t)chunk_count + chunk;
        partial_signs[partial] = 0U;
        zero_unsigned_limbs(
            partial_limbs + partial * (uint64_t)output_limb_count,
            output_limb_count);
    }
    if (restriction_present[face] == 0U) return;
    const uint32_t generator = face % generator_count;
    const uint64_t face_stride = (uint64_t)port_count * (uint64_t)generator_count;
    const uint32_t source_state = (uint32_t)((uint64_t)face / face_stride);
    if (source_state >= source_state_count) {
        atomicExch(obstruction, 1U);
        return;
    }
    uint32_t relational_state = 0xffffffffU;
    const uint32_t source_state_id = source_state_ids[source_state];
    for (uint32_t candidate = 0U; candidate < relational_state_count; ++candidate) {
        if (relational_state_present[candidate] != 0U
            && relational_states[candidate] == source_state_id) {
            if (relational_state != 0xffffffffU) {
                atomicExch(obstruction, 1U);
                return;
            }
            relational_state = candidate;
        }
    }
    const uint64_t current_base =
        ((uint64_t)source_state * (uint64_t)generator_count + generator)
        * (uint64_t)pair_count * (uint64_t)current_limb_count;
    const uint64_t restriction_base =
        (uint64_t)face * (uint64_t)factor_count * (uint64_t)restriction_limb_count;
    const uint64_t relational_base = relational_state == 0xffffffffU
        ? 0ULL
        : ((uint64_t)relational_state * (uint64_t)generator_count + generator)
          * (uint64_t)factor_count;
    uint32_t *first = first_scratch + at * (uint64_t)output_limb_count;
    uint32_t *second = second_scratch + at * (uint64_t)output_limb_count;
    uint32_t *third = third_scratch + at * (uint64_t)output_limb_count;
    const uint64_t begin = (uint64_t)chunk * (uint64_t)chunk_size;
    uint64_t end = begin + chunk_size;
    if (end > pair_count) end = pair_count;
    const uint64_t overlap_partial = section * (uint64_t)chunk_count + chunk;
    const uint64_t transported_norm_partial =
        (section + 1ULL) * (uint64_t)chunk_count + chunk;
    const uint64_t ingress_norm_partial =
        (section + 2ULL) * (uint64_t)chunk_count + chunk;
    for (uint64_t pair = begin; pair < end; ++pair) {
        const uint32_t left = pair_factors[pair * 2ULL];
        const uint32_t right = pair_factors[pair * 2ULL + 1ULL];
        if (left >= factor_count || right >= factor_count) {
            atomicExch(obstruction, 1U);
            return;
        }
        const uint32_t *left_restriction = restriction_limbs
            + restriction_base + (uint64_t)left * restriction_limb_count;
        const uint32_t *right_restriction = restriction_limbs
            + restriction_base + (uint64_t)right * restriction_limb_count;
        if (unsigned_limbs_are_zero(left_restriction, restriction_limb_count)
            || unsigned_limbs_are_zero(right_restriction, restriction_limb_count)) continue;

        zero_unsigned_limbs(first, output_limb_count);
        uint8_t relational_sign = 0U;
        if (relational_state != 0xffffffffU) {
            const uint64_t left_coordinate = relational_base + left;
            const uint64_t right_coordinate = relational_base + right;
            const uint8_t left_signs[2] = {
                transported_real_sign[left_coordinate],
                transported_imaginary_sign[left_coordinate]
            };
            const uint8_t right_signs[2] = {
                transported_real_sign[right_coordinate],
                transported_imaginary_sign[right_coordinate]
            };
            const uint32_t *left_components[2] = {
                transported_real_limbs
                    + left_coordinate * (uint64_t)relational_limb_count,
                transported_imaginary_limbs
                    + left_coordinate * (uint64_t)relational_limb_count
            };
            const uint32_t *right_components[2] = {
                transported_real_limbs
                    + right_coordinate * (uint64_t)relational_limb_count,
                transported_imaginary_limbs
                    + right_coordinate * (uint64_t)relational_limb_count
            };
            for (uint32_t component = 0U; component < 2U; ++component) {
                if (left_signs[component] == 0U || right_signs[component] == 0U) continue;
                multiply_unsigned_limbs(
                    left_components[component], relational_limb_count,
                    right_components[component], relational_limb_count,
                    second, output_limb_count);
                add_signed_magnitude(
                    &relational_sign, first,
                    product_sign(left_signs[component], right_signs[component]),
                    second, output_limb_count);
            }
        }
        if (relational_sign != 0U) {
            multiply_unsigned_limbs(
                first, output_limb_count,
                left_restriction, restriction_limb_count,
                second, output_limb_count);
            multiply_unsigned_limbs(
                second, output_limb_count,
                right_restriction, restriction_limb_count,
                first, output_limb_count);
        }
        multiply_unsigned_limbs(
            current_limbs + current_base + pair * (uint64_t)current_limb_count,
            current_limb_count,
            left_restriction, restriction_limb_count,
            second, output_limb_count);
        multiply_unsigned_limbs(
            second, output_limb_count,
            right_restriction, restriction_limb_count,
            third, output_limb_count);
        const uint32_t multiplicity = left == right ? 1U : 2U;
        const bool target_nonzero = !unsigned_limbs_are_zero(third, output_limb_count);
        if (target_nonzero) {
            multiply_unsigned_limbs(
                third, output_limb_count, third, output_limb_count,
                second, output_limb_count);
            for (uint32_t copy = 0U; copy < multiplicity; ++copy) {
                add_signed_magnitude(
                    partial_signs + transported_norm_partial,
                    partial_limbs + transported_norm_partial * (uint64_t)output_limb_count,
                    1U, second, output_limb_count);
            }
        }
        if (relational_sign != 0U) {
            multiply_unsigned_limbs(
                first, output_limb_count, first, output_limb_count,
                second, output_limb_count);
            for (uint32_t copy = 0U; copy < multiplicity; ++copy) {
                add_signed_magnitude(
                    partial_signs + ingress_norm_partial,
                    partial_limbs + ingress_norm_partial * (uint64_t)output_limb_count,
                    1U, second, output_limb_count);
            }
        }
        if (target_nonzero && relational_sign != 0U) {
            multiply_unsigned_limbs(
                first, output_limb_count, third, output_limb_count,
                second, output_limb_count);
            for (uint32_t copy = 0U; copy < multiplicity; ++copy) {
                add_signed_magnitude(
                    partial_signs + overlap_partial,
                    partial_limbs + overlap_partial * (uint64_t)output_limb_count,
                    relational_sign, second, output_limb_count);
            }
        }
    }
}

extern "C" __global__ void scatter_membrane_sparse_relational_boundary(
    const uint8_t *section_signs,
    const uint32_t *section_limbs,
    uint8_t *compatibility_signs,
    uint32_t *compatibility_limbs,
    uint32_t *transported_norm_limbs,
    uint32_t *ingress_norm_limbs,
    uint32_t face_count,
    uint32_t limb_count)
{
    const uint32_t face = blockIdx.x * blockDim.x + threadIdx.x;
    if (face >= face_count) return;
    const uint64_t section = (uint64_t)face * 3ULL;
    compatibility_signs[face] = section_signs[section];
    for (uint32_t limb = 0U; limb < limb_count; ++limb) {
        compatibility_limbs[(uint64_t)face * limb_count + limb] =
            section_limbs[section * limb_count + limb];
        transported_norm_limbs[(uint64_t)face * limb_count + limb] =
            section_limbs[(section + 1ULL) * limb_count + limb];
        ingress_norm_limbs[(uint64_t)face * limb_count + limb] =
            section_limbs[(section + 2ULL) * limb_count + limb];
    }
}

extern "C" __global__ void gather_membrane_radiation(
    const uint8_t *contact_real_sign,
    const uint32_t *contact_real_limbs,
    const uint8_t *contact_imaginary_sign,
    const uint32_t *contact_imaginary_limbs,
    uint8_t *radiation_real_sign,
    uint32_t *radiation_real_limbs,
    uint8_t *radiation_imaginary_sign,
    uint32_t *radiation_imaginary_limbs,
    uint32_t family_count,
    uint32_t limb_count)
{
    if (blockIdx.x != 0U || threadIdx.x != 0U) return;
    *radiation_real_sign = 0U;
    *radiation_imaginary_sign = 0U;
    for (uint32_t limb = 0U; limb < limb_count; ++limb) {
        radiation_real_limbs[limb] = 0U;
        radiation_imaginary_limbs[limb] = 0U;
    }
    for (uint32_t family = 0U; family < family_count; ++family) {
        const uint64_t at = (uint64_t)family * (uint64_t)limb_count;
        add_signed_magnitude(
            radiation_real_sign,
            radiation_real_limbs,
            contact_real_sign[family],
            contact_real_limbs + at,
            limb_count);
        add_signed_magnitude(
            radiation_imaginary_sign,
            radiation_imaginary_limbs,
            contact_imaginary_sign[family],
            contact_imaginary_limbs + at,
            limb_count);
    }
}

extern "C" __global__ void inject_membrane_boundary_current(
    const uint8_t *radiation_real_sign,
    const uint32_t *radiation_real_limbs,
    const uint8_t *radiation_imaginary_sign,
    const uint32_t *radiation_imaginary_limbs,
    uint8_t injection_real_sign,
    uint64_t injection_real_magnitude,
    uint8_t injection_imaginary_sign,
    uint64_t injection_imaginary_magnitude,
    uint8_t *returned_real_sign,
    uint32_t *returned_real_limbs,
    uint8_t *returned_imaginary_sign,
    uint32_t *returned_imaginary_limbs,
    uint32_t *scratch,
    uint32_t radiation_limb_count,
    uint32_t returned_limb_count)
{
    if (blockIdx.x != 0U || threadIdx.x != 0U) return;
    *returned_real_sign = 0U;
    *returned_imaginary_sign = 0U;
    for (uint32_t limb = 0U; limb < returned_limb_count; ++limb) {
        returned_real_limbs[limb] = 0U;
        returned_imaginary_limbs[limb] = 0U;
        scratch[limb] = 0U;
    }
    scale_and_accumulate(
        returned_real_sign, returned_real_limbs,
        *radiation_real_sign, radiation_real_limbs, radiation_limb_count,
        injection_real_sign, injection_real_magnitude, false,
        scratch, returned_limb_count);
    scale_and_accumulate(
        returned_real_sign, returned_real_limbs,
        *radiation_imaginary_sign, radiation_imaginary_limbs, radiation_limb_count,
        injection_imaginary_sign, injection_imaginary_magnitude, true,
        scratch, returned_limb_count);
    scale_and_accumulate(
        returned_imaginary_sign, returned_imaginary_limbs,
        *radiation_real_sign, radiation_real_limbs, radiation_limb_count,
        injection_imaginary_sign, injection_imaginary_magnitude, false,
        scratch, returned_limb_count);
    scale_and_accumulate(
        returned_imaginary_sign, returned_imaginary_limbs,
        *radiation_imaginary_sign, radiation_imaginary_limbs, radiation_limb_count,
        injection_real_sign, injection_real_magnitude, false,
        scratch, returned_limb_count);
}

extern "C" __global__ void conduct_membrane_boundary_chain_contacts(
    const uint64_t *cell_offsets,
    const uint32_t *cell_factors,
    const uint8_t *cell_multiplicity_sign,
    const uint32_t *cell_multiplicity_limbs,
    const uint32_t *support_reflected_scale_limbs,
    const uint32_t *support_pair_scale_limbs,
    const uint32_t *support_action_scale_limbs,
    const uint64_t *factor_receiver_observations,
    const uint64_t *factor_capacity,
    const int8_t *family_orientation,
    const uint8_t *family_real_sign,
    const uint32_t *family_real_limbs,
    const uint8_t *family_imaginary_sign,
    const uint32_t *family_imaginary_limbs,
    uint8_t *overlap_sign,
    uint32_t *overlap_limbs,
    uint8_t *reflected_overlap_sign,
    uint32_t *reflected_overlap_limbs,
    uint8_t *receiver_overlap_sign,
    uint32_t *receiver_overlap_limbs,
    uint8_t *receiver_action_norm_sign,
    uint32_t *receiver_action_norm_limbs,
    uint32_t *overlap_scratch,
    uint8_t *contact_real_sign,
    uint32_t *contact_real_limbs,
    uint8_t *contact_imaginary_sign,
    uint32_t *contact_imaginary_limbs,
    uint32_t support_count,
    uint32_t factor_count,
    uint32_t family_count,
    uint32_t multiplicity_limb_count,
    uint32_t support_scale_limb_count,
    uint32_t receiver_count,
    uint32_t overlap_limb_count,
    uint32_t family_limb_count,
    uint32_t contact_limb_count)
{
    const uint32_t at = blockIdx.x * blockDim.x + threadIdx.x;
    const uint32_t axis_count = family_count > receiver_count ? family_count : receiver_count;
    const uint64_t work = (uint64_t)support_count * (uint64_t)axis_count;
    if ((uint64_t)at >= work) return;
    const uint32_t support = at / axis_count;
    const uint32_t axis = at % axis_count;
    const uint32_t left_cell = support * 2U;
    const uint32_t right_cell = left_cell + 1U;
    uint64_t left_at = cell_offsets[left_cell];
    const uint64_t left_end = cell_offsets[left_cell + 1U];
    uint64_t right_at = cell_offsets[right_cell];
    const uint64_t right_end = cell_offsets[right_cell + 1U];
    const uint64_t scratch_at = (uint64_t)at * (uint64_t)overlap_limb_count;
    const uint64_t support_scale_at =
        (uint64_t)support * (uint64_t)support_scale_limb_count;

    if (axis < receiver_count) {
        const uint32_t receiver = axis;
        const uint64_t receiver_output =
            (uint64_t)support * (uint64_t)receiver_count + receiver;
        const uint64_t receiver_output_at =
            receiver_output * (uint64_t)overlap_limb_count;
        receiver_overlap_sign[receiver_output] = 0U;
        receiver_action_norm_sign[receiver_output] = 0U;
        zero_unsigned_limbs(
            receiver_overlap_limbs + receiver_output_at, overlap_limb_count);
        zero_unsigned_limbs(
            receiver_action_norm_limbs + receiver_output_at, overlap_limb_count);
        for (uint64_t presented_at = left_at; presented_at < left_end; ++presented_at) {
            const uint32_t presented_factor = cell_factors[presented_at];
            const uint64_t presented_observation = factor_receiver_observations[
                (uint64_t)presented_factor * (uint64_t)receiver_count + receiver];
            for (uint64_t action_at = right_at; action_at < right_end; ++action_at) {
                const uint32_t action_factor = cell_factors[action_at];
                if (factor_receiver_observations[
                        (uint64_t)action_factor * (uint64_t)receiver_count + receiver]
                    != presented_observation) continue;
                multiply_unsigned_limbs(
                    cell_multiplicity_limbs
                        + presented_at * (uint64_t)multiplicity_limb_count,
                    multiplicity_limb_count,
                    cell_multiplicity_limbs
                        + action_at * (uint64_t)multiplicity_limb_count,
                    multiplicity_limb_count,
                    overlap_scratch + scratch_at,
                    overlap_limb_count);
                add_signed_magnitude(
                    receiver_overlap_sign + receiver_output,
                    receiver_overlap_limbs + receiver_output_at,
                    cell_multiplicity_sign[action_at],
                    overlap_scratch + scratch_at,
                    overlap_limb_count);
            }
        }
        for (uint64_t first_at = right_at; first_at < right_end; ++first_at) {
            const uint32_t first_factor = cell_factors[first_at];
            const uint64_t first_observation = factor_receiver_observations[
                (uint64_t)first_factor * (uint64_t)receiver_count + receiver];
            for (uint64_t second_at = right_at; second_at < right_end; ++second_at) {
                const uint32_t second_factor = cell_factors[second_at];
                if (factor_receiver_observations[
                        (uint64_t)second_factor * (uint64_t)receiver_count + receiver]
                    != first_observation) continue;
                multiply_unsigned_limbs(
                    cell_multiplicity_limbs
                        + first_at * (uint64_t)multiplicity_limb_count,
                    multiplicity_limb_count,
                    cell_multiplicity_limbs
                        + second_at * (uint64_t)multiplicity_limb_count,
                    multiplicity_limb_count,
                    overlap_scratch + scratch_at,
                    overlap_limb_count);
                add_signed_magnitude(
                    receiver_action_norm_sign + receiver_output,
                    receiver_action_norm_limbs + receiver_output_at,
                    product_sign(
                        cell_multiplicity_sign[first_at],
                        cell_multiplicity_sign[second_at]),
                    overlap_scratch + scratch_at,
                    overlap_limb_count);
            }
        }
        multiply_unsigned_limbs_in_place(
            receiver_overlap_limbs + receiver_output_at,
            overlap_limb_count,
            support_pair_scale_limbs + support_scale_at,
            support_scale_limb_count,
            overlap_scratch + scratch_at);
        multiply_unsigned_limbs_in_place(
            receiver_action_norm_limbs + receiver_output_at,
            overlap_limb_count,
            support_action_scale_limbs + support_scale_at,
            support_scale_limb_count,
            overlap_scratch + scratch_at);
    }

    if (axis >= family_count) return;
    const uint32_t family = axis;
    const uint64_t response = (uint64_t)support * (uint64_t)family_count + family;
    const uint64_t overlap_at = response * (uint64_t)overlap_limb_count;
    const uint64_t contact_at = response * (uint64_t)contact_limb_count;
    overlap_sign[response] = 0U;
    reflected_overlap_sign[response] = 0U;
    zero_unsigned_limbs(overlap_limbs + overlap_at, overlap_limb_count);
    zero_unsigned_limbs(reflected_overlap_limbs + overlap_at, overlap_limb_count);

    // Preserve the reflected ingress metric as its own family section.  Squaring removes the
    // coordinate sign; family orientation remains the signed constitutive face.
    for (uint64_t reflected_at = left_at; reflected_at < left_end; ++reflected_at) {
        const uint32_t factor = cell_factors[reflected_at];
        const int8_t orientation =
            family_orientation[(uint64_t)family * (uint64_t)factor_count + factor];
        const uint8_t orientation_sign =
            orientation < 0 ? 2U : (orientation > 0 ? 1U : 0U);
        const uint64_t current_at = reflected_at * (uint64_t)multiplicity_limb_count;
        multiply_unsigned_limbs(
            cell_multiplicity_limbs + current_at,
            multiplicity_limb_count,
            cell_multiplicity_limbs + current_at,
            multiplicity_limb_count,
            overlap_scratch + scratch_at,
            overlap_limb_count);
        scale_unsigned_limbs(
            overlap_scratch + scratch_at,
            overlap_limb_count,
            factor_capacity[factor],
            contact_imaginary_limbs + contact_at,
            overlap_limb_count);
        add_signed_magnitude(
            reflected_overlap_sign + response,
            reflected_overlap_limbs + overlap_at,
            orientation_sign,
            contact_imaginary_limbs + contact_at,
            overlap_limb_count);
    }
    while (left_at < left_end && right_at < right_end) {
        const uint32_t left_factor = cell_factors[left_at];
        const uint32_t right_factor = cell_factors[right_at];
        if (left_factor < right_factor) {
            ++left_at;
            continue;
        }
        if (right_factor < left_factor) {
            ++right_at;
            continue;
        }
        const int8_t orientation =
            family_orientation[(uint64_t)family * (uint64_t)factor_count + left_factor];
        const uint64_t left_current_at = left_at * (uint64_t)multiplicity_limb_count;
        const uint64_t right_current_at = right_at * (uint64_t)multiplicity_limb_count;
        multiply_unsigned_limbs(
            cell_multiplicity_limbs + left_current_at,
            multiplicity_limb_count,
            cell_multiplicity_limbs + right_current_at,
            multiplicity_limb_count,
            overlap_scratch + scratch_at,
            overlap_limb_count);
        scale_unsigned_limbs(
            overlap_scratch + scratch_at,
            overlap_limb_count,
            factor_capacity[left_factor],
            contact_real_limbs + contact_at,
            overlap_limb_count);
        const uint8_t orientation_sign =
            orientation < 0 ? 2U : (orientation > 0 ? 1U : 0U);
        const uint8_t term_sign =
            product_sign(cell_multiplicity_sign[right_at], orientation_sign);
        add_signed_magnitude(
            overlap_sign + response,
            overlap_limbs + overlap_at,
            term_sign,
            contact_real_limbs + contact_at,
            overlap_limb_count);
        ++left_at;
        ++right_at;
    }
    multiply_unsigned_limbs_in_place(
        overlap_limbs + overlap_at,
        overlap_limb_count,
        support_pair_scale_limbs + support_scale_at,
        support_scale_limb_count,
        overlap_scratch + scratch_at);
    multiply_unsigned_limbs_in_place(
        reflected_overlap_limbs + overlap_at,
        overlap_limb_count,
        support_reflected_scale_limbs + support_scale_at,
        support_scale_limb_count,
        overlap_scratch + scratch_at);
    const uint64_t family_at = (uint64_t)family * (uint64_t)family_limb_count;
    contact_real_sign[response] = product_sign(family_real_sign[family], overlap_sign[response]);
    contact_imaginary_sign[response] =
        product_sign(family_imaginary_sign[family], overlap_sign[response]);
    multiply_unsigned_limbs(
        family_real_limbs + family_at,
        family_limb_count,
        overlap_limbs + overlap_at,
        overlap_limb_count,
        contact_real_limbs + contact_at,
        contact_limb_count);
    multiply_unsigned_limbs(
        family_imaginary_limbs + family_at,
        family_limb_count,
        overlap_limbs + overlap_at,
        overlap_limb_count,
        contact_imaginary_limbs + contact_at,
        contact_limb_count);
}

extern "C" __global__ void form_membrane_quadratic_moments(
    const uint32_t *context_current_limbs,
    const uint32_t *context_weight_limbs,
    const uint32_t *restriction_port,
    const uint32_t *restriction_current_limbs,
    uint32_t *moment_limbs,
    uint32_t *left_scratch,
    uint32_t *right_scratch,
    uint32_t *quadratic_scratch,
    uint32_t *term_scratch,
    uint32_t context_count,
    uint32_t restriction_count,
    uint32_t port_count,
    uint32_t factor_count,
    uint32_t context_limb_count,
    uint32_t restriction_limb_count,
    uint32_t weight_limb_count,
    uint32_t product_limb_count,
    uint32_t quadratic_limb_count,
    uint32_t moment_limb_count)
{
    const uint32_t at = blockIdx.x * blockDim.x + threadIdx.x;
    const uint64_t work =
        (uint64_t)port_count * (uint64_t)factor_count * (uint64_t)factor_count;
    if ((uint64_t)at >= work) return;
    const uint32_t right = at % factor_count;
    const uint32_t left = (at / factor_count) % factor_count;
    const uint32_t port = at / (factor_count * factor_count);
    const uint64_t moment_at = (uint64_t)at * (uint64_t)moment_limb_count;
    const uint64_t product_at = (uint64_t)at * (uint64_t)product_limb_count;
    const uint64_t quadratic_at = (uint64_t)at * (uint64_t)quadratic_limb_count;
    zero_unsigned_limbs(moment_limbs + moment_at, moment_limb_count);
    for (uint32_t context = 0U; context < context_count; ++context) {
        const uint64_t context_left =
            ((uint64_t)context * (uint64_t)factor_count + left)
            * (uint64_t)context_limb_count;
        const uint64_t context_right =
            ((uint64_t)context * (uint64_t)factor_count + right)
            * (uint64_t)context_limb_count;
        const uint64_t weight_at =
            (uint64_t)context * (uint64_t)weight_limb_count;
        for (uint32_t restriction = 0U; restriction < restriction_count; ++restriction) {
            if (restriction_port[restriction] != port) continue;
            const uint64_t restriction_left =
                ((uint64_t)restriction * (uint64_t)factor_count + left)
                * (uint64_t)restriction_limb_count;
            const uint64_t restriction_right =
                ((uint64_t)restriction * (uint64_t)factor_count + right)
                * (uint64_t)restriction_limb_count;
            multiply_unsigned_limbs(
                context_current_limbs + context_left, context_limb_count,
                restriction_current_limbs + restriction_left, restriction_limb_count,
                left_scratch + product_at, product_limb_count);
            multiply_unsigned_limbs(
                context_current_limbs + context_right, context_limb_count,
                restriction_current_limbs + restriction_right, restriction_limb_count,
                right_scratch + product_at, product_limb_count);
            multiply_unsigned_limbs(
                left_scratch + product_at, product_limb_count,
                right_scratch + product_at, product_limb_count,
                quadratic_scratch + quadratic_at, quadratic_limb_count);
            multiply_unsigned_limbs(
                quadratic_scratch + quadratic_at, quadratic_limb_count,
                context_weight_limbs + weight_at, weight_limb_count,
                term_scratch + moment_at, moment_limb_count);
            add_unsigned_limbs(
                moment_limbs + moment_at,
                term_scratch + moment_at,
                moment_limb_count);
        }
    }
}

extern "C" __global__ void gather_membrane_resident_boundary_restrictions(
    const uint32_t *state_port_transition,
    const uint32_t *transition_targets,
    const uint64_t *transition_factor_offsets,
    const uint32_t *transition_factors,
    const uint32_t *transition_current_limbs,
    const uint32_t *boundary_states,
    const uint32_t *universal_ports,
    uint32_t *restriction_current_limbs,
    uint8_t *restriction_present,
    uint32_t *restriction_target_states,
    uint32_t boundary_state_count,
    uint32_t local_port_count,
    uint32_t atlas_state_count,
    uint32_t universal_port_count,
    uint32_t factor_count,
    uint32_t restriction_limb_count)
{
    const uint32_t at = blockIdx.x * blockDim.x + threadIdx.x;
    const uint64_t pair_count =
        (uint64_t)local_port_count * (uint64_t)boundary_state_count;
    if ((uint64_t)at >= pair_count) return;
    const uint32_t local_port = at / boundary_state_count;
    const uint32_t boundary_at = at % boundary_state_count;
    const uint32_t state = boundary_states[boundary_at];
    const uint32_t port = universal_ports[local_port];
    const uint64_t section_at =
        (uint64_t)at * (uint64_t)factor_count * (uint64_t)restriction_limb_count;
    zero_unsigned_limbs(
        restriction_current_limbs + section_at,
        factor_count * restriction_limb_count);
    restriction_present[at] = 0U;
    restriction_target_states[at] = 0xffffffffU;
    if (state >= atlas_state_count || port >= universal_port_count) return;
    const uint32_t transition =
        state_port_transition[(uint64_t)state * universal_port_count + port];
    if (transition == 0xffffffffU) return;
    restriction_present[at] = 1U;
    restriction_target_states[at] = transition_targets[transition];
    const uint64_t begin = transition_factor_offsets[transition];
    const uint64_t end = transition_factor_offsets[(uint64_t)transition + 1ULL];
    for (uint64_t coordinate = begin; coordinate < end; ++coordinate) {
        const uint32_t factor = transition_factors[coordinate];
        if (factor >= factor_count) continue;
        const uint64_t source_at = coordinate * restriction_limb_count;
        const uint64_t target_at =
            section_at + (uint64_t)factor * restriction_limb_count;
        for (uint32_t limb = 0U; limb < restriction_limb_count; ++limb) {
            restriction_current_limbs[target_at + limb] =
                transition_current_limbs[source_at + limb];
        }
    }
}

extern "C" __global__ void contract_membrane_observable_integral_forms(
    const uint32_t *context_current_limbs,
    const uint32_t *context_weight_limbs,
    const uint64_t *form_entry_offsets,
    const uint32_t *form_entry_rows,
    const uint32_t *form_entry_columns,
    const uint8_t *form_entry_signs,
    const uint32_t *form_entry_limbs,
    uint8_t *coordinate_signs,
    uint32_t *coordinate_limbs,
    uint32_t *quadratic_scratch,
    uint32_t *coefficient_scratch,
    uint32_t *term_scratch,
    uint32_t context_count,
    uint32_t factor_count,
    uint32_t form_count,
    uint32_t context_limb_count,
    uint32_t weight_limb_count,
    uint32_t coefficient_limb_count,
    uint32_t quadratic_limb_count,
    uint32_t coefficient_product_limb_count,
    uint32_t coordinate_limb_count)
{
    const uint32_t form = blockIdx.x * blockDim.x + threadIdx.x;
    if (form >= form_count) return;
    const uint64_t coordinate_at =
        (uint64_t)form * (uint64_t)coordinate_limb_count;
    const uint64_t quadratic_at =
        (uint64_t)form * (uint64_t)quadratic_limb_count;
    const uint64_t coefficient_at =
        (uint64_t)form * (uint64_t)coefficient_product_limb_count;
    coordinate_signs[form] = 0U;
    zero_unsigned_limbs(
        coordinate_limbs + coordinate_at, coordinate_limb_count);
    const uint64_t entry_begin = form_entry_offsets[form];
    const uint64_t entry_end = form_entry_offsets[(uint64_t)form + 1ULL];
    for (uint32_t context = 0U; context < context_count; ++context) {
        const uint64_t weight_at =
            (uint64_t)context * (uint64_t)weight_limb_count;
        for (uint64_t entry = entry_begin; entry < entry_end; ++entry) {
            const uint32_t row = form_entry_rows[entry];
            const uint32_t column = form_entry_columns[entry];
            if (row >= factor_count || column >= factor_count) continue;
            const uint64_t row_at =
                ((uint64_t)context * factor_count + row) * context_limb_count;
            const uint64_t column_at =
                ((uint64_t)context * factor_count + column) * context_limb_count;
            multiply_unsigned_limbs(
                context_current_limbs + row_at, context_limb_count,
                context_current_limbs + column_at, context_limb_count,
                quadratic_scratch + quadratic_at, quadratic_limb_count);
            if (unsigned_limbs_are_zero(
                    quadratic_scratch + quadratic_at, quadratic_limb_count)) continue;
            const uint64_t entry_at = entry * coefficient_limb_count;
            multiply_unsigned_limbs(
                quadratic_scratch + quadratic_at, quadratic_limb_count,
                form_entry_limbs + entry_at, coefficient_limb_count,
                coefficient_scratch + coefficient_at,
                coefficient_product_limb_count);
            multiply_unsigned_limbs(
                coefficient_scratch + coefficient_at,
                coefficient_product_limb_count,
                context_weight_limbs + weight_at, weight_limb_count,
                term_scratch + coordinate_at, coordinate_limb_count);
            add_signed_magnitude(
                coordinate_signs + form,
                coordinate_limbs + coordinate_at,
                form_entry_signs[entry],
                term_scratch + coordinate_at,
                coordinate_limb_count);
        }
    }
}

extern "C" __global__ void transport_membrane_observable_integral_form_factors(
    const uint8_t *source_signs,
    const uint32_t *source_limbs,
    const uint32_t *factor_sources,
    const uint8_t *factor_scale_signs,
    const uint32_t *factor_scale_limbs,
    uint8_t *target_signs,
    uint32_t *target_limbs,
    uint32_t source_count,
    uint32_t target_count,
    uint32_t source_limb_count,
    uint32_t scale_limb_count,
    uint32_t target_limb_count)
{
    const uint32_t target = blockIdx.x * blockDim.x + threadIdx.x;
    if (target >= target_count) return;
    const uint64_t target_at = (uint64_t)target * target_limb_count;
    target_signs[target] = 0U;
    zero_unsigned_limbs(target_limbs + target_at, target_limb_count);
    const uint32_t source = factor_sources[target];
    const uint8_t scale_sign = factor_scale_signs[target];
    if (source == 0xffffffffU || scale_sign == 0U) return;
    if (source >= source_count) return;
    const uint8_t source_sign = source_signs[source];
    if (source_sign == 0U) return;
    const uint64_t source_at = (uint64_t)source * source_limb_count;
    const uint64_t scale_at = (uint64_t)target * scale_limb_count;
    multiply_unsigned_limbs(
        source_limbs + source_at, source_limb_count,
        factor_scale_limbs + scale_at, scale_limb_count,
        target_limbs + target_at, target_limb_count);
    target_signs[target] = product_sign(source_sign, scale_sign);
}

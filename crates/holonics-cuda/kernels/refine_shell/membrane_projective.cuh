// Membrane projective and terminal receiver transport.
// This fragment is included by refine_shell.cu after refine_shared.cuh.

extern "C" __global__ void compare_membrane_sparse_quadratic_situated_projective_pairs(
    const uint8_t *native_phase_front,
    const uint8_t *compatibility_sign,
    const uint32_t *compatibility_limbs,
    const uint32_t *norm_product_limbs,
    uint8_t *pair_dominates,
    uint32_t *square_scratch,
    uint32_t *left_cross_scratch,
    uint32_t *right_cross_scratch,
    uint32_t port_count,
    uint32_t compatibility_limb_count,
    uint32_t norm_product_limb_count,
    uint32_t square_limb_count,
    uint32_t cross_limb_count)
{
    const uint32_t at = blockIdx.x * blockDim.x + threadIdx.x;
    const uint64_t work = (uint64_t)port_count * (uint64_t)port_count;
    if ((uint64_t)at >= work) return;
    const uint32_t challenged = at / port_count;
    const uint32_t challenger = at % port_count;
    pair_dominates[at] = 0U;
    if (native_phase_front[challenged] == 0U) return;
    const uint32_t *challenged_norm = norm_product_limbs
        + (uint64_t)challenged * norm_product_limb_count;
    if (unsigned_limbs_are_zero(challenged_norm, norm_product_limb_count)) {
        if (challenger == challenged) pair_dominates[at] = 1U;
        return;
    }
    if (challenger == challenged || native_phase_front[challenger] == 0U) return;
    const uint32_t *challenger_norm = norm_product_limbs
        + (uint64_t)challenger * norm_product_limb_count;
    if (unsigned_limbs_are_zero(challenger_norm, norm_product_limb_count)) return;
    uint32_t *square = square_scratch + (uint64_t)at * square_limb_count;
    uint32_t *left_cross = left_cross_scratch + (uint64_t)at * cross_limb_count;
    uint32_t *right_cross = right_cross_scratch + (uint64_t)at * cross_limb_count;
    const int comparison = compare_boundary_phase_component(
            challenger, challenged, 0U, 1U,
            compatibility_sign, compatibility_limbs, norm_product_limbs,
            compatibility_limb_count, norm_product_limb_count,
            square, square_limb_count,
            left_cross, right_cross, cross_limb_count);
    pair_dominates[at] = comparison > 0 ? 1U : (comparison == 0 ? 2U : 0U);
}

extern "C" __global__ void compare_membrane_sparse_quadratic_situated_projective_pair_window(
    const uint8_t *native_phase_front,
    const uint8_t *compatibility_sign,
    const uint32_t *compatibility_limbs,
    const uint32_t *norm_product_limbs,
    uint8_t *pair_dominates,
    uint32_t *square_scratch,
    uint32_t *left_cross_scratch,
    uint32_t *right_cross_scratch,
    uint64_t pair_offset,
    uint32_t window_pair_count,
    uint32_t face_count,
    uint32_t compatibility_limb_count,
    uint32_t norm_product_limb_count,
    uint32_t square_limb_count,
    uint32_t cross_limb_count)
{
    const uint32_t local = blockIdx.x * blockDim.x + threadIdx.x;
    if (local >= window_pair_count || face_count == 0U) return;
    const uint64_t global = pair_offset + (uint64_t)local;
    const uint64_t complete_pair_count = (uint64_t)face_count * (uint64_t)face_count;
    if (global >= complete_pair_count) return;
    const uint32_t challenged = (uint32_t)(global / face_count);
    const uint32_t challenger = (uint32_t)(global % face_count);
    pair_dominates[local] = 0U;
    if (native_phase_front[challenged] == 0U) return;
    const uint32_t *challenged_norm = norm_product_limbs
        + (uint64_t)challenged * norm_product_limb_count;
    if (unsigned_limbs_are_zero(challenged_norm, norm_product_limb_count)) {
        if (challenger == challenged) pair_dominates[local] = 1U;
        return;
    }
    if (challenger == challenged || native_phase_front[challenger] == 0U) return;
    const uint32_t *challenger_norm = norm_product_limbs
        + (uint64_t)challenger * norm_product_limb_count;
    if (unsigned_limbs_are_zero(challenger_norm, norm_product_limb_count)) return;
    uint32_t *square = square_scratch + (uint64_t)local * square_limb_count;
    uint32_t *left_cross = left_cross_scratch + (uint64_t)local * cross_limb_count;
    uint32_t *right_cross = right_cross_scratch + (uint64_t)local * cross_limb_count;
    const int comparison = compare_boundary_phase_component(
        challenger, challenged, 0U, 1U,
        compatibility_sign, compatibility_limbs, norm_product_limbs,
        compatibility_limb_count, norm_product_limb_count,
        square, square_limb_count,
        left_cross, right_cross, cross_limb_count);
    pair_dominates[local] = comparison > 0 ? 1U : (comparison == 0 ? 2U : 0U);
}

extern "C" __global__ void accumulate_membrane_sparse_projective_pair_window(
    const uint8_t *native_phase_front,
    const uint8_t *quadratic_pair_relation,
    const uint8_t *relational_pair_relation,
    uint32_t *challenged_dominated,
    uint64_t pair_offset,
    uint32_t window_pair_count,
    uint32_t face_count,
    uint32_t relational_present)
{
    const uint32_t local = blockIdx.x * blockDim.x + threadIdx.x;
    if (local >= window_pair_count || face_count == 0U) return;
    const uint64_t global = pair_offset + (uint64_t)local;
    const uint64_t complete_pair_count = (uint64_t)face_count * (uint64_t)face_count;
    if (global >= complete_pair_count) return;
    const uint32_t challenged = (uint32_t)(global / face_count);
    const uint32_t challenger = (uint32_t)(global % face_count);
    if (native_phase_front[challenged] == 0U) return;
    const uint8_t quadratic = quadratic_pair_relation[local];
    bool dominates = quadratic == 1U;
    if (relational_present != 0U) {
        if (challenger == challenged || native_phase_front[challenger] == 0U) return;
        const uint8_t relational = relational_pair_relation[local];
        const bool non_worse = quadratic != 0U && relational != 0U;
        const bool strict = quadratic == 1U || relational == 1U;
        dominates = non_worse && strict;
    }
    if (dominates) atomicExch(challenged_dominated + challenged, 1U);
}

extern "C" __global__ void select_membrane_sparse_projective_streamed_front(
    const uint8_t *native_phase_front,
    const uint32_t *challenged_dominated,
    uint8_t *selected_front,
    uint32_t face_count)
{
    const uint32_t challenged = blockIdx.x * blockDim.x + threadIdx.x;
    if (challenged >= face_count) return;
    selected_front[challenged] =
        native_phase_front[challenged] != 0U && challenged_dominated[challenged] == 0U ? 1U : 0U;
}

extern "C" __global__ void combine_membrane_sparse_quadratic_projective_pair_fronts(
    const uint8_t *native_phase_front,
    const uint8_t *quadratic_pair_dominates,
    const uint8_t *relational_pair_dominates,
    uint8_t *joint_pair_dominates,
    uint32_t face_count)
{
    const uint64_t at = (uint64_t)blockIdx.x * blockDim.x + threadIdx.x;
    const uint64_t work = (uint64_t)face_count * (uint64_t)face_count;
    if (at >= work) return;
    const uint32_t challenged = (uint32_t)(at / face_count);
    const uint32_t challenger = (uint32_t)(at % face_count);
    if (challenger == challenged || native_phase_front[challenger] == 0U
        || native_phase_front[challenged] == 0U) {
        joint_pair_dominates[at] = 0U;
        return;
    }
    const uint8_t quadratic = quadratic_pair_dominates[at];
    const uint8_t relational = relational_pair_dominates[at];
    const bool non_worse = quadratic != 0U && relational != 0U;
    const bool strict = quadratic == 1U || relational == 1U;
    joint_pair_dominates[at] = non_worse && strict ? 1U : 0U;
}

extern "C" __global__ void form_membrane_boundary_phase_components(
    const uint32_t *family_real_limbs,
    const uint32_t *family_imaginary_limbs,
    const uint8_t *port_action_overlap_sign,
    const uint32_t *port_action_overlap_limbs,
    const uint8_t *port_reflected_overlap_sign,
    const uint32_t *port_reflected_overlap_limbs,
    const uint8_t *port_receiver_overlap_sign,
    const uint32_t *port_receiver_overlap_limbs,
    const uint32_t *port_receiver_action_norm_limbs,
    uint8_t *compatibility_sign,
    uint32_t *compatibility_limbs,
    uint32_t *norm_limbs,
    uint32_t port_count,
    uint32_t family_count,
    uint32_t receiver_count,
    uint32_t component_count,
    uint32_t family_limb_count,
    uint32_t overlap_limb_count,
    uint32_t compatibility_limb_count,
    uint32_t norm_limb_count)
{
    const uint32_t at = blockIdx.x * blockDim.x + threadIdx.x;
    const uint64_t work = (uint64_t)port_count * (uint64_t)component_count;
    if ((uint64_t)at >= work) return;
    const uint32_t port = at / component_count;
    const uint32_t component_at = at % component_count;
    const uint64_t component =
        (uint64_t)port * (uint64_t)component_count + component_at;
    uint8_t *component_sign = compatibility_sign + component;
    uint32_t *compatibility = compatibility_limbs
        + component * (uint64_t)compatibility_limb_count;
    uint32_t *norm = norm_limbs + component * (uint64_t)norm_limb_count;
    *component_sign = 0U;
    zero_unsigned_limbs(compatibility, compatibility_limb_count);
    zero_unsigned_limbs(norm, norm_limb_count);

    if (component_at < family_count) {
        const uint32_t family = component_at;
        const uint64_t family_at = (uint64_t)family * (uint64_t)family_limb_count;
        const uint64_t port_family =
            (uint64_t)port * (uint64_t)family_count + family;
        const uint64_t overlap_at = port_family * (uint64_t)overlap_limb_count;
        const bool family_is_active =
            !unsigned_limbs_are_zero(
                family_real_limbs + family_at, family_limb_count)
            || !unsigned_limbs_are_zero(
                family_imaginary_limbs + family_at, family_limb_count);
        if (!family_is_active) return;
        *component_sign = product_sign(
            port_action_overlap_sign[port_family],
            port_reflected_overlap_sign[port_family]);
        multiply_unsigned_limbs(
            port_action_overlap_limbs + overlap_at, overlap_limb_count,
            port_reflected_overlap_limbs + overlap_at, overlap_limb_count,
            compatibility, compatibility_limb_count);
        multiply_unsigned_limbs(
            port_action_overlap_limbs + overlap_at, overlap_limb_count,
            port_action_overlap_limbs + overlap_at, overlap_limb_count,
            norm, norm_limb_count);
        return;
    }

    const uint32_t receiver = component_at - family_count;
    if (receiver >= receiver_count) return;
    const uint64_t port_receiver =
        (uint64_t)port * (uint64_t)receiver_count + receiver;
    const uint64_t receiver_at = port_receiver * (uint64_t)overlap_limb_count;
    *component_sign = port_receiver_overlap_sign[port_receiver];
    for (uint32_t limb = 0U; limb < overlap_limb_count; ++limb) {
        compatibility[limb] = port_receiver_overlap_limbs[receiver_at + limb];
        norm[limb] = port_receiver_action_norm_limbs[receiver_at + limb];
    }
}

extern "C" __global__ void compare_membrane_boundary_phase_pairs(
    const uint8_t *compatibility_sign,
    const uint32_t *compatibility_limbs,
    const uint32_t *norm_limbs,
    uint8_t *pair_dominates,
    uint32_t *square_scratch,
    uint32_t *left_cross_scratch,
    uint32_t *right_cross_scratch,
    uint32_t local_face_count,
    uint32_t chart_count,
    uint32_t component_count,
    uint32_t compatibility_limb_count,
    uint32_t norm_limb_count,
    uint32_t square_limb_count,
    uint32_t cross_limb_count)
{
    const uint32_t at = blockIdx.x * blockDim.x + threadIdx.x;
    const uint64_t local_pair_count =
        (uint64_t)local_face_count * (uint64_t)local_face_count;
    const uint64_t work = (uint64_t)chart_count * local_pair_count;
    if ((uint64_t)at >= work) return;
    const uint32_t chart = (uint32_t)((uint64_t)at / local_pair_count);
    const uint32_t local_pair = (uint32_t)((uint64_t)at % local_pair_count);
    const uint32_t challenged =
        chart * local_face_count + local_pair / local_face_count;
    const uint32_t challenger =
        chart * local_face_count + local_pair % local_face_count;
    pair_dominates[at] = 0U;
    if (challenger == challenged) return;
    uint32_t *square = square_scratch + (uint64_t)at * (uint64_t)square_limb_count;
    uint32_t *left_cross =
        left_cross_scratch + (uint64_t)at * (uint64_t)cross_limb_count;
    uint32_t *right_cross =
        right_cross_scratch + (uint64_t)at * (uint64_t)cross_limb_count;
    bool any_strictly_greater = false;
    for (uint32_t component = 0U; component < component_count; ++component) {
        const int comparison = compare_boundary_phase_component(
            challenger, challenged, component, component_count,
            compatibility_sign, compatibility_limbs, norm_limbs,
            compatibility_limb_count, norm_limb_count,
            square, square_limb_count, left_cross, right_cross, cross_limb_count);
        if (comparison < 0) return;
        if (comparison > 0) any_strictly_greater = true;
    }
    pair_dominates[at] = any_strictly_greater ? 1U : 0U;
}

extern "C" __global__ void select_membrane_boundary_phase_front(
    const uint8_t *pair_dominates,
    uint8_t *phase_locked,
    uint32_t local_face_count,
    uint32_t chart_count)
{
    const uint32_t challenged = blockIdx.x * blockDim.x + threadIdx.x;
    const uint32_t face_count = local_face_count * chart_count;
    if (challenged >= face_count) return;
    const uint32_t chart = challenged / local_face_count;
    const uint32_t local_challenged = challenged % local_face_count;
    const uint64_t begin = (uint64_t)chart * (uint64_t)local_face_count
        * (uint64_t)local_face_count
        + (uint64_t)local_challenged * (uint64_t)local_face_count;
    for (uint32_t challenger = 0U; challenger < local_face_count; ++challenger) {
        if (pair_dominates[begin + challenger] != 0U) {
            phase_locked[challenged] = 0U;
            return;
        }
    }
    phase_locked[challenged] = 1U;
}

extern "C" __global__ void select_membrane_boundary_phase_front_direct(
    const uint8_t *compatibility_sign,
    const uint32_t *compatibility_limbs,
    const uint32_t *norm_limbs,
    uint8_t *phase_locked,
    uint32_t *square_scratch,
    uint32_t *left_cross_scratch,
    uint32_t *right_cross_scratch,
    uint32_t local_face_count,
    uint32_t chart_count,
    uint32_t component_count,
    uint32_t compatibility_limb_count,
    uint32_t norm_limb_count,
    uint32_t square_limb_count,
    uint32_t cross_limb_count)
{
    const uint32_t challenged = blockIdx.x * blockDim.x + threadIdx.x;
    const uint32_t face_count = local_face_count * chart_count;
    if (challenged >= face_count || local_face_count == 0U) return;
    const uint32_t chart = challenged / local_face_count;
    uint32_t *square = square_scratch
        + (uint64_t)challenged * (uint64_t)square_limb_count;
    uint32_t *left_cross = left_cross_scratch
        + (uint64_t)challenged * (uint64_t)cross_limb_count;
    uint32_t *right_cross = right_cross_scratch
        + (uint64_t)challenged * (uint64_t)cross_limb_count;
    for (uint32_t local_challenger = 0U;
         local_challenger < local_face_count; ++local_challenger) {
        const uint32_t challenger = chart * local_face_count + local_challenger;
        if (challenger == challenged) continue;
        bool any_strictly_greater = false;
        bool non_worse = true;
        for (uint32_t component = 0U; component < component_count; ++component) {
            const int comparison = compare_boundary_phase_component(
                challenger, challenged, component, component_count,
                compatibility_sign, compatibility_limbs, norm_limbs,
                compatibility_limb_count, norm_limb_count,
                square, square_limb_count, left_cross, right_cross, cross_limb_count);
            if (comparison < 0) {
                non_worse = false;
                break;
            }
            if (comparison > 0) any_strictly_greater = true;
        }
        if (non_worse && any_strictly_greater) {
            phase_locked[challenged] = 0U;
            return;
        }
    }
    phase_locked[challenged] = 1U;
}

extern "C" __global__ void mark_membrane_productive_current_front(
    const uint32_t *self_pairing_limbs,
    uint8_t *productive_front,
    uint32_t face_count,
    uint32_t component_count,
    uint32_t limb_count)
{
    const uint32_t face = blockIdx.x * blockDim.x + threadIdx.x;
    if (face >= face_count) return;
    bool productive = false;
    for (uint32_t component = 0U; component < component_count && !productive; ++component) {
        const uint32_t *value = self_pairing_limbs
            + ((uint64_t)face * (uint64_t)component_count + component)
                * (uint64_t)limb_count;
        productive = !unsigned_limbs_are_zero(value, limb_count);
    }
    productive_front[face] = productive ? 1U : 0U;
}

extern "C" __global__ void select_membrane_boundary_phase_front_complete_receiver_direct(
    const uint8_t *compatibility_sign,
    const uint32_t *compatibility_limbs,
    const uint32_t *norm_limbs,
    const uint32_t *productive_target_norm_limbs,
    uint8_t *phase_locked,
    uint32_t *square_scratch,
    uint32_t *left_cross_scratch,
    uint32_t *right_cross_scratch,
    uint32_t face_count,
    uint32_t component_count,
    uint32_t compatibility_limb_count,
    uint32_t norm_limb_count,
    uint32_t productive_limb_count,
    uint32_t square_limb_count,
    uint32_t cross_limb_count)
{
    const uint32_t challenged = blockIdx.x * blockDim.x + threadIdx.x;
    if (challenged >= face_count || face_count == 0U) return;
    if (productive_limb_count != 0U
        && unsigned_limbs_are_zero(
            productive_target_norm_limbs
                + (uint64_t)challenged * (uint64_t)productive_limb_count,
            productive_limb_count)) {
        phase_locked[challenged] = 0U;
        return;
    }
    uint32_t *square = square_scratch
        + (uint64_t)challenged * (uint64_t)square_limb_count;
    uint32_t *left_cross = left_cross_scratch
        + (uint64_t)challenged * (uint64_t)cross_limb_count;
    uint32_t *right_cross = right_cross_scratch
        + (uint64_t)challenged * (uint64_t)cross_limb_count;
    for (uint32_t challenger = 0U; challenger < face_count; ++challenger) {
        if (challenger == challenged) continue;
        if (productive_limb_count != 0U
            && unsigned_limbs_are_zero(
                productive_target_norm_limbs
                    + (uint64_t)challenger * (uint64_t)productive_limb_count,
                productive_limb_count)) continue;
        bool any_strictly_greater = false;
        bool non_worse = true;
        for (uint32_t component = 0U; component < component_count; ++component) {
            const int comparison = compare_boundary_phase_component(
                challenger, challenged, component, component_count,
                compatibility_sign, compatibility_limbs, norm_limbs,
                compatibility_limb_count, norm_limb_count,
                square, square_limb_count, left_cross, right_cross, cross_limb_count);
            if (comparison < 0) {
                non_worse = false;
                break;
            }
            if (comparison > 0) any_strictly_greater = true;
        }
        if (non_worse && any_strictly_greater) {
            phase_locked[challenged] = 0U;
            return;
        }
    }
    phase_locked[challenged] = 1U;
}

extern "C" __global__ void select_membrane_boundary_phase_front_target_state_direct(
    const uint8_t *compatibility_sign,
    const uint32_t *compatibility_limbs,
    const uint32_t *norm_limbs,
    const uint32_t *restriction_target_states,
    const uint32_t *productive_target_norm_limbs,
    uint8_t *phase_locked,
    uint32_t *square_scratch,
    uint32_t *left_cross_scratch,
    uint32_t *right_cross_scratch,
    uint32_t face_count,
    uint32_t boundary_state_count,
    uint32_t port_count,
    uint32_t generator_count,
    uint32_t component_count,
    uint32_t compatibility_limb_count,
    uint32_t norm_limb_count,
    uint32_t productive_limb_count,
    uint32_t square_limb_count,
    uint32_t cross_limb_count)
{
    const uint32_t challenged = blockIdx.x * blockDim.x + threadIdx.x;
    const uint32_t local_face_count = port_count * generator_count;
    if (challenged >= face_count || local_face_count == 0U
        || boundary_state_count == 0U || generator_count == 0U) return;
    const uint32_t challenged_state_coordinate = challenged / local_face_count;
    const uint32_t challenged_local_face = challenged % local_face_count;
    const uint32_t challenged_port = challenged_local_face / generator_count;
    if (challenged_state_coordinate >= boundary_state_count || challenged_port >= port_count) {
        phase_locked[challenged] = 0U;
        return;
    }
    const uint32_t challenged_restriction =
        challenged_port * boundary_state_count + challenged_state_coordinate;
    const uint32_t target_state = restriction_target_states[challenged_restriction];
    if (target_state == 0xffffffffU) {
        phase_locked[challenged] = 0U;
        return;
    }
    // A receiver cannot select a face whose restricted transported current is the exact radical.
    // `restriction_present` alone says that the state/port transition exists; it does not say
    // that this particular current meets it.  The independently formed target self-pairing is the
    // exact productivity witness and prevents zero-current slots from entering the successor
    // reconstruction fibre.
    if (productive_limb_count != 0U
        && unsigned_limbs_are_zero(
            productive_target_norm_limbs
                + (uint64_t)challenged * (uint64_t)productive_limb_count,
            productive_limb_count)) {
        phase_locked[challenged] = 0U;
        return;
    }
    uint32_t *square = square_scratch
        + (uint64_t)challenged * (uint64_t)square_limb_count;
    uint32_t *left_cross = left_cross_scratch
        + (uint64_t)challenged * (uint64_t)cross_limb_count;
    uint32_t *right_cross = right_cross_scratch
        + (uint64_t)challenged * (uint64_t)cross_limb_count;
    for (uint32_t challenger = 0U; challenger < face_count; ++challenger) {
        if (challenger == challenged) continue;
        const uint32_t challenger_state_coordinate = challenger / local_face_count;
        const uint32_t challenger_local_face = challenger % local_face_count;
        const uint32_t challenger_port = challenger_local_face / generator_count;
        if (challenger_state_coordinate >= boundary_state_count || challenger_port >= port_count) {
            continue;
        }
        const uint32_t challenger_restriction =
            challenger_port * boundary_state_count + challenger_state_coordinate;
        if (restriction_target_states[challenger_restriction] != target_state) continue;
        if (productive_limb_count != 0U
            && unsigned_limbs_are_zero(
                productive_target_norm_limbs
                    + (uint64_t)challenger * (uint64_t)productive_limb_count,
                productive_limb_count)) continue;
        bool any_strictly_greater = false;
        bool non_worse = true;
        for (uint32_t component = 0U; component < component_count; ++component) {
            const int comparison = compare_boundary_phase_component(
                challenger, challenged, component, component_count,
                compatibility_sign, compatibility_limbs, norm_limbs,
                compatibility_limb_count, norm_limb_count,
                square, square_limb_count, left_cross, right_cross, cross_limb_count);
            if (comparison < 0) {
                non_worse = false;
                break;
            }
            if (comparison > 0) any_strictly_greater = true;
        }
        if (non_worse && any_strictly_greater) {
            phase_locked[challenged] = 0U;
            return;
        }
    }
    phase_locked[challenged] = 1U;
}

extern "C" __global__ void form_membrane_situated_output_pairing(
    const uint8_t *port_real_sign,
    const uint32_t *port_real_limbs,
    const uint8_t *port_imaginary_sign,
    const uint32_t *port_imaginary_limbs,
    const uint8_t *incoming_real_sign,
    const uint32_t *incoming_real_limbs,
    const uint8_t *incoming_imaginary_sign,
    const uint32_t *incoming_imaginary_limbs,
    const uint8_t *native_phase_front,
    uint8_t *power_sign,
    uint32_t *power_limbs,
    uint32_t *imaginary_product_scratch,
    uint32_t port_count,
    uint32_t radiation_limb_count,
    uint32_t incoming_limb_count,
    uint32_t power_limb_count)
{
    const uint32_t port = blockIdx.x * blockDim.x + threadIdx.x;
    if (port >= port_count) return;
    const uint64_t radiation_at = (uint64_t)port * (uint64_t)radiation_limb_count;
    const uint64_t power_at = (uint64_t)port * (uint64_t)power_limb_count;
    uint32_t *power = power_limbs + power_at;
    uint32_t *imaginary_product = imaginary_product_scratch + power_at;
    zero_unsigned_limbs(power, power_limb_count);
    zero_unsigned_limbs(imaginary_product, power_limb_count);
    power_sign[port] = 0U;
    if (native_phase_front[port] == 0U) return;

    multiply_unsigned_limbs(
        port_real_limbs + radiation_at, radiation_limb_count,
        incoming_real_limbs, incoming_limb_count,
        power, power_limb_count);
    power_sign[port] = product_sign(port_real_sign[port], incoming_real_sign[0]);
    multiply_unsigned_limbs(
        port_imaginary_limbs + radiation_at, radiation_limb_count,
        incoming_imaginary_limbs, incoming_limb_count,
        imaginary_product, power_limb_count);
    add_signed_magnitude(
        power_sign + port, power,
        product_sign(port_imaginary_sign[port], incoming_imaginary_sign[0]),
        imaginary_product, power_limb_count);
}

extern "C" __global__ void compare_membrane_situated_output_pairing_pairs(
    const uint8_t *native_phase_front,
    const uint8_t *power_sign,
    const uint32_t *power_limbs,
    uint8_t *pair_dominates,
    uint32_t local_face_count,
    uint32_t chart_count,
    uint32_t power_limb_count)
{
    const uint32_t at = blockIdx.x * blockDim.x + threadIdx.x;
    const uint64_t local_pair_count =
        (uint64_t)local_face_count * (uint64_t)local_face_count;
    const uint64_t work = (uint64_t)chart_count * local_pair_count;
    if ((uint64_t)at >= work) return;
    const uint32_t chart = (uint32_t)((uint64_t)at / local_pair_count);
    const uint32_t local_pair = (uint32_t)((uint64_t)at % local_pair_count);
    const uint32_t challenged =
        chart * local_face_count + local_pair / local_face_count;
    const uint32_t challenger =
        chart * local_face_count + local_pair % local_face_count;
    pair_dominates[at] = 0U;
    if (challenger == challenged || native_phase_front[challenger] == 0U
        || native_phase_front[challenged] == 0U) return;
    const uint64_t challenged_at = (uint64_t)challenged * (uint64_t)power_limb_count;
    const uint64_t challenger_at = (uint64_t)challenger * (uint64_t)power_limb_count;
    if (compare_signed_receiver_pairing(
            power_sign[challenger], power_limbs + challenger_at,
            power_sign[challenged], power_limbs + challenged_at,
            power_limb_count) > 0) {
        pair_dominates[at] = 1U;
    }
}

extern "C" __global__ void select_membrane_situated_output_pairing_front(
    const uint8_t *native_phase_front,
    const uint8_t *pair_dominates,
    uint8_t *situated_front,
    uint32_t local_face_count,
    uint32_t chart_count)
{
    const uint32_t challenged = blockIdx.x * blockDim.x + threadIdx.x;
    const uint32_t face_count = local_face_count * chart_count;
    if (challenged >= face_count) return;
    if (native_phase_front[challenged] == 0U) {
        situated_front[challenged] = 0U;
        return;
    }
    const uint32_t chart = challenged / local_face_count;
    const uint32_t local_challenged = challenged % local_face_count;
    const uint64_t begin = (uint64_t)chart * (uint64_t)local_face_count
        * (uint64_t)local_face_count
        + (uint64_t)local_challenged * (uint64_t)local_face_count;
    for (uint32_t challenger = 0U; challenger < local_face_count; ++challenger) {
        // Projective pair relations use 1=strict win, 2=tie, 0=loss.  Only a strict
        // challenger removes a face from this receiver front; exact ties remain plural.
        if (pair_dominates[begin + challenger] == 1U) {
            situated_front[challenged] = 0U;
            return;
        }
    }
    situated_front[challenged] = 1U;
}

extern "C" __global__ void select_membrane_situated_output_pairing_front_direct(
    const uint8_t *native_phase_front,
    const uint8_t *power_sign,
    const uint32_t *power_limbs,
    uint8_t *situated_front,
    uint32_t local_face_count,
    uint32_t chart_count,
    uint32_t power_limb_count)
{
    const uint32_t challenged = blockIdx.x * blockDim.x + threadIdx.x;
    const uint32_t face_count = local_face_count * chart_count;
    if (challenged >= face_count || local_face_count == 0U) return;
    if (native_phase_front[challenged] == 0U) {
        situated_front[challenged] = 0U;
        return;
    }
    const uint32_t chart = challenged / local_face_count;
    const uint64_t challenged_at =
        (uint64_t)challenged * (uint64_t)power_limb_count;
    for (uint32_t local_challenger = 0U;
         local_challenger < local_face_count; ++local_challenger) {
        const uint32_t challenger = chart * local_face_count + local_challenger;
        if (challenger == challenged || native_phase_front[challenger] == 0U) continue;
        const uint64_t challenger_at =
            (uint64_t)challenger * (uint64_t)power_limb_count;
        if (compare_signed_receiver_pairing(
                power_sign[challenger], power_limbs + challenger_at,
                power_sign[challenged], power_limbs + challenged_at,
                power_limb_count) > 0) {
            situated_front[challenged] = 0U;
            return;
        }
    }
    situated_front[challenged] = 1U;
}

extern "C" __global__ void
select_membrane_situated_relational_then_output_front_direct(
    const uint8_t *native_phase_front,
    const uint8_t *compatibility_sign,
    const uint32_t *compatibility_limbs,
    const uint32_t *norm_limbs,
    const uint8_t *power_sign,
    const uint32_t *power_limbs,
    uint8_t *situated_front,
    uint32_t *square_scratch,
    uint32_t *left_cross_scratch,
    uint32_t *right_cross_scratch,
    uint32_t face_count,
    uint32_t component_count,
    uint32_t relational_component,
    uint32_t compatibility_limb_count,
    uint32_t norm_limb_count,
    uint32_t power_limb_count,
    uint32_t square_limb_count,
    uint32_t cross_limb_count)
{
    const uint32_t challenged = blockIdx.x * blockDim.x + threadIdx.x;
    if (challenged >= face_count || component_count == 0U
        || relational_component >= component_count) return;
    if (native_phase_front[challenged] == 0U) {
        situated_front[challenged] = 0U;
        return;
    }
    uint32_t *square = square_scratch
        + (uint64_t)challenged * (uint64_t)square_limb_count;
    uint32_t *left_cross = left_cross_scratch
        + (uint64_t)challenged * (uint64_t)cross_limb_count;
    uint32_t *right_cross = right_cross_scratch
        + (uint64_t)challenged * (uint64_t)cross_limb_count;
    const uint64_t challenged_power =
        (uint64_t)challenged * (uint64_t)power_limb_count;
    for (uint32_t challenger = 0U; challenger < face_count; ++challenger) {
        if (challenger == challenged || native_phase_front[challenger] == 0U) continue;
        const int relational = compare_boundary_phase_component(
            challenger, challenged, relational_component, component_count,
            compatibility_sign, compatibility_limbs, norm_limbs,
            compatibility_limb_count, norm_limb_count,
            square, square_limb_count, left_cross, right_cross, cross_limb_count);
        if (relational > 0) {
            situated_front[challenged] = 0U;
            return;
        }
        if (relational == 0) {
            const uint64_t challenger_power =
                (uint64_t)challenger * (uint64_t)power_limb_count;
            if (compare_signed_receiver_pairing(
                    power_sign[challenger], power_limbs + challenger_power,
                    power_sign[challenged], power_limbs + challenged_power,
                    power_limb_count) > 0) {
                situated_front[challenged] = 0U;
                return;
            }
        }
    }
    situated_front[challenged] = 1U;
}

extern "C" __global__ void select_membrane_situated_output_pairing_front_target_state_direct(
    const uint8_t *native_phase_front,
    const uint8_t *power_sign,
    const uint32_t *power_limbs,
    const uint32_t *restriction_target_states,
    uint8_t *situated_front,
    uint32_t face_count,
    uint32_t boundary_state_count,
    uint32_t port_count,
    uint32_t generator_count,
    uint32_t power_limb_count)
{
    const uint32_t challenged = blockIdx.x * blockDim.x + threadIdx.x;
    const uint32_t local_face_count = port_count * generator_count;
    if (challenged >= face_count || local_face_count == 0U
        || boundary_state_count == 0U || generator_count == 0U) return;
    if (native_phase_front[challenged] == 0U) {
        situated_front[challenged] = 0U;
        return;
    }
    const uint32_t challenged_state_coordinate = challenged / local_face_count;
    const uint32_t challenged_local_face = challenged % local_face_count;
    const uint32_t challenged_port = challenged_local_face / generator_count;
    if (challenged_state_coordinate >= boundary_state_count || challenged_port >= port_count) {
        situated_front[challenged] = 0U;
        return;
    }
    const uint32_t challenged_restriction =
        challenged_port * boundary_state_count + challenged_state_coordinate;
    const uint32_t target_state = restriction_target_states[challenged_restriction];
    if (target_state == 0xffffffffU) {
        situated_front[challenged] = 0U;
        return;
    }
    const uint64_t challenged_at =
        (uint64_t)challenged * (uint64_t)power_limb_count;
    for (uint32_t challenger = 0U; challenger < face_count; ++challenger) {
        if (challenger == challenged || native_phase_front[challenger] == 0U) continue;
        const uint32_t challenger_state_coordinate = challenger / local_face_count;
        const uint32_t challenger_local_face = challenger % local_face_count;
        const uint32_t challenger_port = challenger_local_face / generator_count;
        if (challenger_state_coordinate >= boundary_state_count || challenger_port >= port_count) {
            continue;
        }
        const uint32_t challenger_restriction =
            challenger_port * boundary_state_count + challenger_state_coordinate;
        if (restriction_target_states[challenger_restriction] != target_state) continue;
        const uint64_t challenger_at =
            (uint64_t)challenger * (uint64_t)power_limb_count;
        if (compare_signed_receiver_pairing(
                power_sign[challenger], power_limbs + challenger_at,
                power_sign[challenged], power_limbs + challenged_at,
                power_limb_count) > 0) {
            situated_front[challenged] = 0U;
            return;
        }
    }
    situated_front[challenged] = 1U;
}

extern "C" __global__ void balance_membrane_boundary_chain(
    const uint8_t *joint_real_sign,
    const uint32_t *joint_real_limbs,
    const uint8_t *joint_imaginary_sign,
    const uint32_t *joint_imaginary_limbs,
    const uint8_t *incoming_real_sign,
    const uint32_t *incoming_real_limbs,
    const uint8_t *incoming_imaginary_sign,
    const uint32_t *incoming_imaginary_limbs,
    uint64_t joint_scale,
    uint8_t *stored_real_sign,
    uint32_t *stored_real_limbs,
    uint8_t *stored_imaginary_sign,
    uint32_t *stored_imaginary_limbs,
    uint32_t *scratch,
    uint32_t joint_limb_count,
    uint32_t stored_limb_count)
{
    if (blockIdx.x != 0U || threadIdx.x != 0U) return;
    *stored_real_sign = *incoming_real_sign;
    *stored_imaginary_sign = *incoming_imaginary_sign;
    for (uint32_t limb = 0U; limb < stored_limb_count; ++limb) {
        stored_real_limbs[limb] = incoming_real_limbs[limb];
        stored_imaginary_limbs[limb] = incoming_imaginary_limbs[limb];
        scratch[limb] = 0U;
    }
    scale_and_accumulate(
        stored_real_sign, stored_real_limbs,
        *joint_real_sign, joint_real_limbs, joint_limb_count,
        1U, joint_scale, true, scratch, stored_limb_count);
    scale_and_accumulate(
        stored_imaginary_sign, stored_imaginary_limbs,
        *joint_imaginary_sign, joint_imaginary_limbs, joint_limb_count,
        1U, joint_scale, true, scratch, stored_limb_count);
}

extern "C" __global__ void refine_shell(
    const uint32_t *site_whole,      // per site: which whole it lives in
    const uint32_t *site_position,   // per site: its index inside that whole
    const uint32_t *site_class,      // per site: its class at shell k-1
    const uint32_t *whole_offset,    // per whole: where its stream begins in `stream`
    const uint32_t *whole_length,    // per whole: how long its stream is
    const uint32_t *stream,          // every whole's surface ids, concatenated
    const uint32_t *reading_id,      // per surface: the dense identity of its reading
    uint64_t *table_pair,            // capacity slots of (class,key), REFINE_EMPTY when free
    uint64_t *table_key,             // capacity slots: the key half, for the second comparand
    uint32_t *site_next_class,       // per site: the claimed slot index
    uint32_t site_count,
    uint32_t depth,
    uint32_t capacity_mask)          // capacity - 1; capacity is a power of two
{
    uint32_t at = blockIdx.x * blockDim.x + threadIdx.x;
    if (at >= site_count) {
        return;
    }

    const uint32_t whole = site_whole[at];
    const int64_t position = (int64_t)site_position[at];
    const int64_t length = (int64_t)whole_length[whole];
    const uint32_t base = whole_offset[whole];
    const int64_t step = (int64_t)depth;

    const int64_t left_site = position - step;
    const int64_t right_site = position + step;
    const uint32_t left = (left_site < 0 || left_site >= length)
                              ? REFINE_ABSENT
                              : reading_id[stream[base + (uint32_t)left_site]];
    const uint32_t right = (right_site < 0 || right_site >= length)
                               ? REFINE_ABSENT
                               : reading_id[stream[base + (uint32_t)right_site]];

    const uint64_t key = ((uint64_t)left << 32) | (uint64_t)right;
    const uint64_t klass = (uint64_t)site_class[at];

    // Claim the identity of (class, key). Both halves are compared, so a slot is shared only by
    // occurrences that agree on BOTH — which is exactly the refinement condition.
    uint64_t probe = refine_mix(klass * 0x9e3779b97f4a7c15ULL + key) & (uint64_t)capacity_mask;
    for (;;) {
        const uint64_t seen = ((volatile uint64_t *)table_pair)[probe];
        if (seen == klass) {
            // **The claim and the key are two stores, so a reader can see the first without the
            // second.** Falling through here was a real defect: a lane that found its own class in
            // a slot whose key had not yet landed walked on and claimed a SECOND slot for the same
            // pair, splitting one class in two. Measured on `"of"` at shell one: 1,794 classes on
            // the card against 1,787 on the cpu, the card finer by exactly the races it lost.
            //
            // The wait is bounded by one store from a lane that has already won its exchange, and
            // `key` can never be the empty marker: it is two 32-bit reading identities and the
            // marker is all ones.
            while (((volatile uint64_t *)table_key)[probe] == REFINE_EMPTY) {
            }
            if (((volatile uint64_t *)table_key)[probe] == key) {
                site_next_class[at] = (uint32_t)probe;
                return;
            }
            probe = (probe + 1) & (uint64_t)capacity_mask;
            continue;
        }
        if (seen == REFINE_EMPTY) {
            const uint64_t won = atomicCAS(
                (unsigned long long *)&table_pair[probe],
                (unsigned long long)REFINE_EMPTY,
                (unsigned long long)klass);
            if (won == REFINE_EMPTY) {
                table_key[probe] = key;
                __threadfence();
                site_next_class[at] = (uint32_t)probe;
                return;
            }
            // Another lane took the slot between the read and the exchange. Re-examine it: if it
            // took it for this same pair we join it, otherwise we walk on.
            if (won == klass) {
                // Same wait as above: the winner claimed for this class, and its key becomes
                // visible one store later.
                while (((volatile uint64_t *)table_key)[probe] == REFINE_EMPTY) {
                }
                if (((volatile uint64_t *)table_key)[probe] == key) {
                    site_next_class[at] = (uint32_t)probe;
                    return;
                }
            }
        }
        probe = (probe + 1) & (uint64_t)capacity_mask;
    }
}

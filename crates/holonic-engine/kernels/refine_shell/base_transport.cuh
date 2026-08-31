// Base quotient and native transport.
// This fragment is included by refine_shell.cu after refine_shared.cuh.

extern "C" __global__ void claim_identities(
    const uint32_t *cell_class,
    const uint32_t *cell_key,
    uint64_t *table_pair,
    uint32_t *cell_next_class,
    uint32_t cell_count,
    uint32_t capacity_mask)
{
    uint32_t at = blockIdx.x * blockDim.x + threadIdx.x;
    if (at >= cell_count) {
        return;
    }
    const uint64_t pair = ((uint64_t)cell_class[at] << 32) | (uint64_t)cell_key[at];
    uint64_t probe = refine_mix(pair) & (uint64_t)capacity_mask;
    for (;;) {
        const uint64_t seen = ((volatile uint64_t *)table_pair)[probe];
        if (seen == pair) {
            cell_next_class[at] = (uint32_t)probe;
            return;
        }
        if (seen == REFINE_EMPTY) {
            const uint64_t won = atomicCAS(
                (unsigned long long *)&table_pair[probe],
                (unsigned long long)REFINE_EMPTY,
                (unsigned long long)pair);
            if (won == REFINE_EMPTY) {
                cell_next_class[at] = (uint32_t)probe;
                return;
            }
            if (won == pair) {
                cell_next_class[at] = (uint32_t)probe;
                return;
            }
        }
        probe = (probe + 1) & (uint64_t)capacity_mask;
    }
}

extern "C" __global__ void conduct_native_word(
    const uint32_t *generator_table,
    const uint32_t *word,
    const uint32_t *native_start,
    uint32_t *native_end,
    uint32_t cell_count,
    uint32_t state_count,
    uint32_t word_length)
{
    uint32_t at = blockIdx.x * blockDim.x + threadIdx.x;
    if (at >= cell_count) {
        return;
    }
    uint32_t state = native_start[at];
    for (uint32_t step = 0; step < word_length; ++step) {
        state = generator_table[word[step] * state_count + state];
    }
    native_end[at] = state;
}

extern "C" __global__ void conduct_complex_incidence(
    const int64_t *incidence,
    const int64_t *coefficient_real,
    const int64_t *coefficient_imaginary,
    int64_t *section_real,
    int64_t *section_imaginary,
    uint32_t branch_count,
    uint32_t node_count,
    uint32_t front_count)
{
    const uint64_t at = (uint64_t)blockIdx.x * (uint64_t)blockDim.x
                      + (uint64_t)threadIdx.x;
    const uint64_t extent = (uint64_t)front_count * (uint64_t)branch_count;
    if (at >= extent) {
        return;
    }
    const uint32_t front = (uint32_t)(at / (uint64_t)branch_count);
    const uint32_t branch = (uint32_t)(at % (uint64_t)branch_count);
    const uint64_t incidence_at = (uint64_t)branch * (uint64_t)node_count;
    const uint64_t coefficient_at = (uint64_t)front * (uint64_t)node_count;
    __int128 real = 0;
    __int128 imaginary = 0;
    for (uint32_t node = 0; node < node_count; ++node) {
        const __int128 entry = (__int128)incidence[incidence_at + (uint64_t)node];
        real += entry * (__int128)coefficient_real[coefficient_at + (uint64_t)node];
        imaginary += entry * (__int128)coefficient_imaginary[coefficient_at + (uint64_t)node];
    }
    section_real[at] = (int64_t)real;
    section_imaginary[at] = (int64_t)imaginary;
}

extern "C" __global__ void conduct_coupled_complex_parametron(
    const uint8_t *primary_real_sign,
    const uint32_t *primary_real_limbs,
    const uint8_t *primary_imaginary_sign,
    const uint32_t *primary_imaginary_limbs,
    const uint8_t *factor_active,
    const uint32_t *output_factors,
    const uint32_t *left_factors,
    const uint32_t *right_factors,
    const uint8_t *mixed_real_sign,
    const uint32_t *mixed_real_limbs,
    const uint8_t *mixed_imaginary_sign,
    const uint32_t *mixed_imaginary_limbs,
    uint8_t *section_real_sign,
    uint32_t *section_real_limbs,
    uint8_t *section_imaginary_sign,
    uint32_t *section_imaginary_limbs,
    uint32_t factor_count,
    uint32_t interaction_count,
    uint32_t limb_count)
{
    const uint32_t factor = blockIdx.x * blockDim.x + threadIdx.x;
    if (factor >= factor_count) {
        return;
    }
    const uint64_t output_at = (uint64_t)factor * (uint64_t)limb_count;
    for (uint32_t limb = 0; limb < limb_count; ++limb) {
        section_real_limbs[output_at + limb] = 0;
        section_imaginary_limbs[output_at + limb] = 0;
    }
    section_real_sign[factor] = 0;
    section_imaginary_sign[factor] = 0;
    if (factor_active[factor] == 0) {
        return;
    }
    add_signed_magnitude(section_real_sign + factor, section_real_limbs + output_at,
                         primary_real_sign[factor], primary_real_limbs + output_at, limb_count);
    add_signed_magnitude(section_imaginary_sign + factor, section_imaginary_limbs + output_at,
                         primary_imaginary_sign[factor], primary_imaginary_limbs + output_at, limb_count);
    for (uint32_t interaction = 0; interaction < interaction_count; ++interaction) {
        if (output_factors[interaction] != factor
            || factor_active[left_factors[interaction]] == 0
            || factor_active[right_factors[interaction]] == 0) {
            continue;
        }
        const uint64_t mixed_at = (uint64_t)interaction * (uint64_t)limb_count;
        add_signed_magnitude(section_real_sign + factor, section_real_limbs + output_at,
                             mixed_real_sign[interaction], mixed_real_limbs + mixed_at, limb_count);
        add_signed_magnitude(section_imaginary_sign + factor, section_imaginary_limbs + output_at,
                             mixed_imaginary_sign[interaction], mixed_imaginary_limbs + mixed_at, limb_count);
    }
}

extern "C" __global__ void receive_interval_potential_incidence(
    const int64_t *lower_incidence,
    const int64_t *upper_incidence,
    const uint32_t *row_address,
    const int64_t *coefficient,
    uint32_t *selected_address,
    int64_t *selected_lower,
    int64_t *selected_upper,
    uint32_t *plural_count,
    uint32_t row_count,
    uint32_t node_count)
{
    const uint32_t front = blockIdx.x;
    const uint32_t lane = threadIdx.x;
    __shared__ int64_t best_lower[1024];
    __shared__ uint32_t best_row[1024];
    __shared__ uint32_t plural;

    int64_t local_lower = INT64_MIN;
    uint32_t local_row = UINT32_MAX;
    const uint64_t coefficient_at = (uint64_t)front * (uint64_t)node_count;
    for (uint32_t row = lane; row < row_count; row += blockDim.x) {
        const uint64_t incidence_at = (uint64_t)row * (uint64_t)node_count;
        __int128 lower = 0;
        for (uint32_t node = 0; node < node_count; ++node) {
            const int64_t scale = coefficient[coefficient_at + (uint64_t)node];
            const int64_t from = scale >= 0
                ? lower_incidence[incidence_at + (uint64_t)node]
                : upper_incidence[incidence_at + (uint64_t)node];
            lower += (__int128)scale * (__int128)from;
        }
        const int64_t value = (int64_t)lower;
        if (value > local_lower
            || (value == local_lower && row_address[row] < local_row)) {
            local_lower = value;
            local_row = row_address[row];
        }
    }
    best_lower[lane] = local_lower;
    best_row[lane] = local_row;
    __syncthreads();
    for (uint32_t reach = blockDim.x / 2U; reach > 0U; reach >>= 1U) {
        if (lane < reach) {
            const int64_t right_lower = best_lower[lane + reach];
            const uint32_t right_row = best_row[lane + reach];
            if (right_lower > best_lower[lane]
                || (right_lower == best_lower[lane] && right_row < best_row[lane])) {
                best_lower[lane] = right_lower;
                best_row[lane] = right_row;
            }
        }
        __syncthreads();
    }
    if (lane == 0U) {
        plural = 0U;
        selected_address[front] = best_row[0];
        selected_lower[front] = best_lower[0];
        selected_upper[front] = INT64_MIN;
    }
    __syncthreads();
    for (uint32_t row = lane; row < row_count; row += blockDim.x) {
        const uint64_t incidence_at = (uint64_t)row * (uint64_t)node_count;
        __int128 upper = 0;
        for (uint32_t node = 0; node < node_count; ++node) {
            const int64_t scale = coefficient[coefficient_at + (uint64_t)node];
            const int64_t until = scale >= 0
                ? upper_incidence[incidence_at + (uint64_t)node]
                : lower_incidence[incidence_at + (uint64_t)node];
            upper += (__int128)scale * (__int128)until;
        }
        const int64_t value = (int64_t)upper;
        if (value >= best_lower[0]) {
            atomicAdd(&plural, 1U);
        }
        if (row_address[row] == best_row[0]) {
            selected_upper[front] = value;
        }
    }
    __syncthreads();
    if (lane == 0U) {
        plural_count[front] = plural;
    }
}

extern "C" __global__ void conduct_native_trace(
    const uint32_t *generator_table,
    const uint32_t *word,
    const uint32_t *native_start,
    uint32_t *native_trace,
    uint32_t cell_count,
    uint32_t state_count,
    uint32_t word_length,
    uint32_t trace_stride)
{
    uint32_t at = blockIdx.x * blockDim.x + threadIdx.x;
    if (at >= cell_count) {
        return;
    }
    uint32_t state = native_start[at];
    const uint64_t trace_at = (uint64_t)at * (uint64_t)trace_stride;
    native_trace[trace_at] = state;
    for (uint32_t step = 0; step < word_length; ++step) {
        state = generator_table[word[step] * state_count + state];
        native_trace[trace_at + (uint64_t)step + 1ULL] = state;
    }
}

extern "C" __global__ void conduct_native_ragged_trace(
    const uint32_t *generator_table,
    const uint32_t *words,
    const uint32_t *word_offset,
    const uint32_t *native_start,
    const uint32_t *trace_offset,
    uint32_t *native_trace,
    uint32_t front_count,
    uint32_t state_count)
{
    const uint32_t at = blockIdx.x * blockDim.x + threadIdx.x;
    if (at >= front_count) {
        return;
    }
    const uint32_t word_begin = word_offset[at];
    const uint32_t word_end = word_offset[at + 1U];
    const uint32_t trace_begin = trace_offset[at];
    uint32_t state = native_start[at];
    native_trace[trace_begin] = state;
    for (uint32_t step = word_begin; step < word_end; ++step) {
        state = generator_table[words[step] * state_count + state];
        native_trace[trace_begin + (step - word_begin) + 1U] = state;
    }
}

extern "C" __global__ void return_and_recur_native(
    const uint32_t *generator_table,
    const uint32_t *native_start,
    uint32_t *predecessor_trace,
    uint32_t *successor_trace,
    uint32_t *ablated_trace,
    uint32_t *predecessor_lengths,
    uint32_t *successor_lengths,
    uint32_t *ablated_lengths,
    uint32_t *decision,
    uint32_t *control_pair,
    uint32_t cell_count,
    uint32_t state_count,
    uint32_t generator,
    uint64_t returned_difference_octets,
    uint32_t delta_from,
    uint32_t delta_to,
    uint32_t control_from)
{
    uint32_t at = blockIdx.x * blockDim.x + threadIdx.x;
    if (at >= cell_count) {
        return;
    }
    const uint32_t stride = state_count + 1U;
    const uint64_t trace_at = (uint64_t)at * (uint64_t)stride;
    const bool committed = returned_difference_octets > 0ULL;
    predecessor_lengths[at] = recurrent_native_trace(
        generator_table,
        generator,
        native_start[at],
        state_count,
        false,
        delta_from,
        delta_to,
        predecessor_trace + trace_at);
    successor_lengths[at] = recurrent_native_trace(
        generator_table,
        generator,
        native_start[at],
        state_count,
        committed,
        delta_from,
        delta_to,
        successor_trace + trace_at);
    ablated_lengths[at] = recurrent_native_trace(
        generator_table,
        generator,
        native_start[at],
        state_count,
        false,
        delta_from,
        delta_to,
        ablated_trace + trace_at);
    if (at == 0U) {
        decision[0] = committed ? 1U : 0U;
        const uint32_t predecessor = generator_table[generator * state_count + control_from];
        control_pair[0] = predecessor;
        control_pair[1] = committed && control_from == delta_from ? delta_to : predecessor;
    }
}

extern "C" __global__ void cultivate_dynamic_morphology(
    const uint32_t *predecessor_action,
    const int32_t *support_incidence,
    const int32_t *receiver_covector,
    const uint32_t *native_start,
    int64_t *returned_adjoint,
    uint32_t *predecessor_extended,
    uint32_t *successor_action,
    uint32_t *withdrawn_action,
    uint32_t *predecessor_trace,
    uint32_t *successor_trace,
    uint32_t *withdrawn_trace,
    uint32_t *predecessor_lengths,
    uint32_t *successor_lengths,
    uint32_t *withdrawn_lengths,
    uint32_t *decision,
    uint32_t *support_state,
    uint32_t predecessor_state_count,
    uint32_t return_count,
    uint32_t start_count)
{
    if (blockIdx.x != 0U) {
        return;
    }
    const uint32_t lane = threadIdx.x;
    const uint32_t successor_state_count = predecessor_state_count + 1U;
    if (lane == 0U) {
        bool all_positive = return_count > 0U && predecessor_state_count > 0U;
        uint32_t nonzero_support = 0U;
        uint32_t supported = 0xffffffffU;
        for (uint32_t receiver = 0; receiver < return_count; ++receiver) {
            all_positive = all_positive && receiver_covector[receiver] > 0;
        }
        for (uint32_t state = 0; state < predecessor_state_count; ++state) {
            int64_t current = 0;
            for (uint32_t receiver = 0; receiver < return_count; ++receiver) {
                const uint64_t at = (uint64_t)receiver * (uint64_t)predecessor_state_count
                                  + (uint64_t)state;
                current += (int64_t)support_incidence[at]
                         * (int64_t)receiver_covector[receiver];
            }
            returned_adjoint[state] = current;
            if (current != 0) {
                ++nonzero_support;
                supported = state;
                all_positive = all_positive && current > 0;
            }
        }
        const bool committed = all_positive && nonzero_support == 1U;
        decision[0] = committed ? 1U : 0U;
        support_state[0] = supported;
        for (uint32_t state = 0; state < predecessor_state_count; ++state) {
            predecessor_extended[state] = predecessor_action[state];
            successor_action[state] = predecessor_action[state];
            withdrawn_action[state] = predecessor_action[state];
        }
        const uint32_t returned_state = predecessor_state_count;
        predecessor_extended[returned_state] = returned_state;
        successor_action[returned_state] = returned_state;
        withdrawn_action[returned_state] = returned_state;
        if (committed) {
            successor_action[supported] = returned_state;
        }
    }
    __syncthreads();

    for (uint32_t at = lane; at < start_count; at += blockDim.x) {
        const uint64_t trace_at = (uint64_t)at * (uint64_t)(successor_state_count + 1U);
        predecessor_lengths[at] = dynamic_morphology_trace(
            predecessor_extended,
            native_start[at],
            successor_state_count,
            predecessor_trace + trace_at);
        successor_lengths[at] = dynamic_morphology_trace(
            successor_action,
            native_start[at],
            successor_state_count,
            successor_trace + trace_at);
        withdrawn_lengths[at] = dynamic_morphology_trace(
            withdrawn_action,
            native_start[at],
            successor_state_count,
            withdrawn_trace + trace_at);
    }
}

extern "C" __global__ void conduct_condensed_recurrences(
    const uint32_t *successor_table,
    const uint32_t *native_start,
    uint32_t *predecessor_trace,
    uint32_t *successor_trace,
    uint32_t *withdrawn_trace,
    uint32_t *predecessor_lengths,
    uint32_t *successor_lengths,
    uint32_t *withdrawn_lengths,
    uint32_t *seen,
    uint32_t cell_count,
    uint32_t state_count,
    uint32_t seen_words,
    uint32_t predecessor_from,
    uint32_t predecessor_to)
{
    uint32_t at = blockIdx.x * blockDim.x + threadIdx.x;
    if (at >= cell_count) {
        return;
    }
    const uint32_t stride = state_count + 1U;
    const uint64_t trace_at = (uint64_t)at * (uint64_t)stride;
    const uint64_t predecessor_seen = (uint64_t)at * (uint64_t)seen_words;
    const uint64_t successor_seen =
        ((uint64_t)cell_count + (uint64_t)at) * (uint64_t)seen_words;
    const uint64_t withdrawn_seen =
        (2ULL * (uint64_t)cell_count + (uint64_t)at) * (uint64_t)seen_words;
    predecessor_lengths[at] = condensed_recurrent_trace(
        successor_table,
        native_start[at],
        state_count,
        true,
        false,
        predecessor_from,
        predecessor_to,
        seen + predecessor_seen,
        predecessor_trace + trace_at);
    successor_lengths[at] = condensed_recurrent_trace(
        successor_table,
        native_start[at],
        state_count,
        false,
        false,
        predecessor_from,
        predecessor_to,
        seen + successor_seen,
        successor_trace + trace_at);
    withdrawn_lengths[at] = condensed_recurrent_trace(
        successor_table,
        native_start[at],
        state_count,
        false,
        true,
        predecessor_from,
        predecessor_to,
        seen + withdrawn_seen,
        withdrawn_trace + trace_at);
}

extern "C" __global__ void conduct_heterogeneous_fusion(
    const uint32_t *successor_action,
    const uint32_t *decoder,
    const uint32_t *native_start,
    uint32_t *predecessor_consequence,
    uint32_t *successor_consequence,
    uint32_t *shared_ablated_consequence,
    uint32_t *local_ablated_consequence,
    uint32_t cell_count,
    uint32_t state_count,
    uint32_t port_count)
{
    const uint32_t at = blockIdx.x * blockDim.x + threadIdx.x;
    if (at >= cell_count) {
        return;
    }
    const uint32_t start = native_start[at];
    const uint32_t next = successor_action[start];
    const uint64_t decoder_at = (uint64_t)at * (uint64_t)state_count;
    const uint32_t before = decoder[decoder_at + start];
    const uint32_t after = decoder[decoder_at + next];
    predecessor_consequence[at] = before;
    successor_consequence[at] = after;
    shared_ablated_consequence[at] = before;

    const uint32_t local_port = at % port_count;
    const uint64_t local_at = (uint64_t)at * (uint64_t)port_count;
    for (uint32_t withdrawn_port = 0; withdrawn_port < port_count; ++withdrawn_port) {
        local_ablated_consequence[local_at + withdrawn_port] =
            local_port == withdrawn_port ? before : after;
    }
}

extern "C" __global__ void derive_media_candidate_counts(
    const uint32_t *pair_anchor,
    const uint32_t *pair_port,
    uint32_t *candidate_counts,
    uint32_t anchor_count,
    uint32_t port_count,
    uint32_t pair_count)
{
    const uint32_t at = blockIdx.x * blockDim.x + threadIdx.x;
    const uint64_t cell_count = (uint64_t)anchor_count * (uint64_t)port_count;
    if ((uint64_t)at >= cell_count) {
        return;
    }
    const uint32_t anchor = at / port_count;
    const uint32_t port = at % port_count;
    uint32_t count = 0U;
    for (uint32_t pair = 0; pair < pair_count; ++pair) {
        if (pair_anchor[pair] == anchor && pair_port[pair] == port) {
            ++count;
        }
    }
    candidate_counts[at] = count;
}

extern "C" __global__ void conduct_joint_media_transport(
    const uint32_t *candidate_counts,
    uint32_t *joint_anchor,
    uint32_t *shared_ablated_joint_anchor,
    uint32_t *local_ablated_joint_anchor,
    uint32_t anchor_count,
    const uint32_t *successor_action,
    const uint32_t *decoder,
    const uint32_t *native_start,
    uint32_t *predecessor_consequence,
    uint32_t *successor_consequence,
    uint32_t *shared_ablated_consequence,
    uint32_t *local_ablated_consequence,
    uint32_t cell_count,
    uint32_t state_count,
    uint32_t port_count)
{
    const uint32_t at = blockIdx.x * blockDim.x + threadIdx.x;
    if (at < anchor_count) {
        uint32_t joint = 1U;
        const uint64_t count_at = (uint64_t)at * (uint64_t)port_count;
        for (uint32_t port = 0; port < port_count; ++port) {
            if (candidate_counts[count_at + port] == 0U) {
                joint = 0U;
            }
        }
        joint_anchor[at] = joint;
        shared_ablated_joint_anchor[at] = 0U;
        const uint64_t local_at = (uint64_t)at * (uint64_t)port_count;
        for (uint32_t withdrawn_port = 0; withdrawn_port < port_count; ++withdrawn_port) {
            local_ablated_joint_anchor[local_at + withdrawn_port] = 0U;
        }
    }
    if (at >= cell_count) {
        return;
    }
    const uint32_t start = native_start[at];
    const uint32_t next = successor_action[start];
    const uint64_t decoder_at = (uint64_t)at * (uint64_t)state_count;
    const uint32_t before = decoder[decoder_at + start];
    const uint32_t after = decoder[decoder_at + next];
    predecessor_consequence[at] = before;
    successor_consequence[at] = after;
    shared_ablated_consequence[at] = before;
    const uint32_t local_port = at % port_count;
    const uint64_t local_at = (uint64_t)at * (uint64_t)port_count;
    for (uint32_t withdrawn_port = 0; withdrawn_port < port_count; ++withdrawn_port) {
        local_ablated_consequence[local_at + withdrawn_port] =
            local_port == withdrawn_port ? before : after;
    }
}

extern "C" __global__ void conduct_production_aperture_fronts(
    const uint32_t *context_table,
    const uint32_t *context_word,
    const uint32_t *context_start,
    uint32_t *context_trace,
    uint32_t *context_boundary_withdrawn_trace,
    uint32_t context_cells,
    uint32_t context_states,
    uint32_t context_word_length,
    const uint32_t *derivation_predecessor_action,
    const uint32_t *derivation_successor_action,
    const uint32_t *derivation_start,
    uint32_t *derivation_predecessor_trace,
    uint32_t *derivation_successor_trace,
    uint32_t *derivation_selected_trace,
    uint32_t *derivation_generator_withdrawn_trace,
    uint32_t *derivation_predecessor_length,
    uint32_t *derivation_successor_length,
    uint32_t *derivation_selected_length,
    uint32_t *derivation_generator_withdrawn_length,
    uint32_t derivation_cells,
    uint32_t derivation_states,
    const uint32_t *media_candidate_species,
    uint64_t *media_species_totals,
    uint64_t *media_joint_anchors,
    uint32_t media_anchors,
    uint32_t media_species,
    uint32_t committed)
{
    const uint32_t at = blockIdx.x * blockDim.x + threadIdx.x;
    if (at < context_cells) {
        const uint32_t stride = context_word_length + 1U;
        const uint64_t trace_at = (uint64_t)at * (uint64_t)stride;
        uint32_t state = context_start[at];
        context_trace[trace_at] = state;
        context_boundary_withdrawn_trace[trace_at] = state;
        for (uint32_t step = 0; step < context_word_length; ++step) {
            state = context_table[context_word[step] * context_states + state];
            context_trace[trace_at + (uint64_t)step + 1ULL] = state;
            context_boundary_withdrawn_trace[trace_at + (uint64_t)step + 1ULL] =
                context_start[at];
        }
    }
    if (at < derivation_cells) {
        const uint32_t stride = derivation_states + 1U;
        const uint64_t trace_at = (uint64_t)at * (uint64_t)stride;
        const uint32_t start = derivation_start[at];
        derivation_predecessor_length[at] = dynamic_morphology_trace(
            derivation_predecessor_action,
            start,
            derivation_states,
            derivation_predecessor_trace + trace_at);
        derivation_successor_length[at] = dynamic_morphology_trace(
            derivation_successor_action,
            start,
            derivation_states,
            derivation_successor_trace + trace_at);
        derivation_selected_length[at] = dynamic_morphology_trace(
            committed == 0U ? derivation_predecessor_action : derivation_successor_action,
            start,
            derivation_states,
            derivation_selected_trace + trace_at);
        // Withdrawing the generator is the identity endomap.  It is distinct from withdrawing
        // cultivation, which restores the predecessor action above.
        uint32_t *withdrawn = derivation_generator_withdrawn_trace + trace_at;
        withdrawn[0] = start;
        withdrawn[1] = start;
        for (uint32_t fill = 2U; fill <= derivation_states; ++fill) {
            withdrawn[fill] = start;
        }
        derivation_generator_withdrawn_length[at] = 2U;
    }
    if (at < media_anchors) {
        bool joint = true;
        const uint64_t base = (uint64_t)at * (uint64_t)media_species;
        for (uint32_t species = 0; species < media_species; ++species) {
            const uint32_t count = media_candidate_species[base + species];
            joint = joint && count != 0U;
            atomicAdd(
                (unsigned long long *)&media_species_totals[species],
                (unsigned long long)count);
        }
        if (joint) {
            atomicAdd((unsigned long long *)media_joint_anchors, 1ULL);
        }
    }
}

extern "C" __global__ void reduce_production_aperture_fronts(
    const uint64_t *media_species_totals,
    const uint32_t *media_species_port,
    uint64_t *media_shared_withdrawn_totals,
    uint64_t *media_local_withdrawn_totals,
    uint64_t *total_joint_incidence,
    int64_t *oriented_difference,
    uint64_t *difference_magnitude,
    int32_t *difference_hand,
    uint32_t *selected_cultivation_state,
    uint32_t media_species,
    uint32_t media_ports,
    uint32_t left_species,
    uint32_t right_species,
    uint32_t committed)
{
    if (blockIdx.x != 0U || threadIdx.x != 0U) {
        return;
    }
    uint64_t total = 0ULL;
    for (uint32_t species = 0; species < media_species; ++species) {
        const uint64_t count = media_species_totals[species];
        total += count;
        media_shared_withdrawn_totals[species] = 0ULL;
        for (uint32_t withdrawn_port = 0; withdrawn_port < media_ports; ++withdrawn_port) {
            const uint64_t at = (uint64_t)species * (uint64_t)media_ports + withdrawn_port;
            media_local_withdrawn_totals[at] =
                media_species_port[species] == withdrawn_port ? 0ULL : count;
        }
    }
    const uint64_t left = media_species_totals[left_species];
    const uint64_t right = media_species_totals[right_species];
    const bool positive = left >= right;
    total_joint_incidence[0] = total;
    difference_magnitude[0] = positive ? left - right : right - left;
    difference_hand[0] = left == right ? 0 : (positive ? 1 : -1);
    oriented_difference[0] = positive
        ? (int64_t)(left - right)
        : -(int64_t)(right - left);
    selected_cultivation_state[0] = committed;
}

extern "C" __global__ void conduct_quadratic_section_transport(
    const int64_t *coefficients,
    const int64_t *transforms,
    int64_t *transported_coefficients,
    uint32_t *invariant,
    uint32_t *selected_route,
    uint32_t *ablated_route,
    uint32_t sections,
    uint32_t cultivated)
{
    const uint32_t at = blockIdx.x * blockDim.x + threadIdx.x;
    if (at >= sections) {
        return;
    }
    const uint64_t coefficient_at = (uint64_t)at * 3ULL;
    const uint64_t transform_at = (uint64_t)at * 4ULL;
    const int64_t a = coefficients[coefficient_at];
    const int64_t b = coefficients[coefficient_at + 1ULL];
    const int64_t c = coefficients[coefficient_at + 2ULL];
    const int64_t p = transforms[transform_at];
    const int64_t q = transforms[transform_at + 1ULL];
    const int64_t r = transforms[transform_at + 2ULL];
    const int64_t s = transforms[transform_at + 3ULL];

    // The returned L0 morphology is the central-inversion fixed-locus route.  Once rested, this
    // exact chart family carries the entering degree-two coefficient face directly.  Withdrawal
    // leaves the expanded substitution below intact; no host branch or relaunch reconstructs it.
    if (cultivated != 0U && p == -1LL && q == 0LL && r == 0LL && s == -1LL) {
        transported_coefficients[coefficient_at] = a;
        transported_coefficients[coefficient_at + 1ULL] = b;
        transported_coefficients[coefficient_at + 2ULL] = c;
        invariant[at] = 1U;
        selected_route[at] = 1U;
        ablated_route[at] = 0U;
        return;
    }

    const int64_t returned_a = a * p * p + b * p * r + c * r * r;
    const int64_t returned_b =
        2LL * a * p * q + b * (p * s + q * r) + 2LL * c * r * s;
    const int64_t returned_c = a * q * q + b * q * s + c * s * s;
    transported_coefficients[coefficient_at] = returned_a;
    transported_coefficients[coefficient_at + 1ULL] = returned_b;
    transported_coefficients[coefficient_at + 2ULL] = returned_c;
    const uint32_t held =
        returned_a == a && returned_b == b && returned_c == c ? 1U : 0U;
    invariant[at] = held;
    selected_route[at] = held == 0U ? 2U : 0U;
    ablated_route[at] = held == 0U ? 2U : 0U;
}

extern "C" __global__ void conduct_fixed_section_families(
    const int64_t *sections,
    const int64_t *actions,
    const int64_t *constraints,
    const uint32_t *constraint_rows,
    const int64_t *moduli,
    const uint32_t *cultivated,
    int64_t *transported,
    uint32_t *constraint_held,
    uint32_t *invariant,
    uint32_t *selected_route,
    uint32_t *ablated_route,
    uint64_t *local_semantic_work,
    uint64_t *local_semantic_span,
    uint32_t families,
    uint32_t dimension)
{
    const uint32_t family = blockIdx.x * blockDim.x + threadIdx.x;
    if (family >= families) {
        return;
    }
    const uint64_t vector_at = (uint64_t)family * (uint64_t)dimension;
    const uint64_t matrix_at = vector_at * (uint64_t)dimension;
    const int64_t modulus = moduli[family];
    uint32_t constraints_hold = 1U;
    for (uint32_t row = 0U; row < constraint_rows[family]; ++row) {
        int64_t reading = 0LL;
        for (uint32_t column = 0U; column < dimension; ++column) {
            reading += constraints[matrix_at + (uint64_t)row * dimension + column]
                * sections[vector_at + column];
        }
        if (canonical_mod(reading, modulus) != 0LL) {
            constraints_hold = 0U;
        }
    }
    constraint_held[family] = constraints_hold;
    const uint64_t dot_work = (uint64_t)dimension * 2ULL - 1ULL;
    const uint64_t constraint_work = (uint64_t)constraint_rows[family] * dot_work;
    const uint64_t constraint_span =
        (uint64_t)constraint_rows[family] * (uint64_t)dimension;
    if (cultivated[family] != 0U && constraints_hold != 0U) {
        for (uint32_t coordinate = 0U; coordinate < dimension; ++coordinate) {
            transported[vector_at + coordinate] =
                canonical_mod(sections[vector_at + coordinate], modulus);
        }
        invariant[family] = 1U;
        selected_route[family] = 1U;
        ablated_route[family] = 0U;
        local_semantic_work[family] = constraint_work;
        local_semantic_span[family] = constraint_span;
        return;
    }
    uint32_t held = 1U;
    for (uint32_t row = 0U; row < dimension; ++row) {
        int64_t reading = 0LL;
        for (uint32_t column = 0U; column < dimension; ++column) {
            reading += actions[matrix_at + (uint64_t)row * dimension + column]
                * sections[vector_at + column];
        }
        const int64_t returned = canonical_mod(reading, modulus);
        transported[vector_at + row] = returned;
        if (returned != canonical_mod(sections[vector_at + row], modulus)) {
            held = 0U;
        }
    }
    invariant[family] = held;
    selected_route[family] = held == 0U ? 2U : 0U;
    ablated_route[family] = held == 0U ? 2U : 0U;
    local_semantic_work[family] = constraint_work + (uint64_t)dimension * dot_work;
    local_semantic_span[family] = constraint_span + (uint64_t)dimension;
}

extern "C" __global__ void conduct_native_fixed_section_families(
    const int64_t *sections,
    const int8_t *constraint_orientation,
    const int8_t *factor_orientation,
    const int64_t *moduli,
    const uint32_t *cultivated,
    int64_t *transported,
    int64_t *constraint_residual,
    uint32_t *constraint_held,
    uint32_t *invariant,
    uint32_t *selected_route,
    uint32_t *ablated_route,
    uint64_t *local_semantic_work,
    uint64_t *local_semantic_span,
    uint32_t families,
    uint32_t dimension)
{
    const uint32_t family = blockIdx.x * blockDim.x + threadIdx.x;
    if (family >= families) {
        return;
    }
    const uint64_t vector_at = (uint64_t)family * (uint64_t)dimension;
    const int64_t modulus = moduli[family];
    int64_t residual = 0LL;
    uint64_t constraint_terms = 0ULL;
    for (uint32_t coordinate = 0U; coordinate < dimension; ++coordinate) {
        const int8_t orientation = constraint_orientation[coordinate];
        if (orientation == 0) {
            continue;
        }
        const int64_t coordinate_value = sections[vector_at + coordinate];
        residual += orientation > 0 ? coordinate_value : -coordinate_value;
        ++constraint_terms;
    }
    residual = canonical_mod(residual, modulus);
    constraint_residual[family] = residual;
    const uint32_t held = residual == 0LL ? 1U : 0U;
    constraint_held[family] = held;
    invariant[family] = held;
    const uint64_t constraint_work = constraint_terms == 0ULL ? 0ULL : constraint_terms - 1ULL;
    const uint64_t constraint_span = constraint_work;
    if (cultivated[family] != 0U && held != 0U) {
        for (uint32_t coordinate = 0U; coordinate < dimension; ++coordinate) {
            transported[vector_at + coordinate] =
                canonical_mod(sections[vector_at + coordinate], modulus);
        }
        selected_route[family] = 1U;
        ablated_route[family] = 0U;
        local_semantic_work[family] = constraint_work;
        local_semantic_span[family] = constraint_span;
        return;
    }

    uint64_t factor_work = 0ULL;
    for (uint32_t coordinate = 0U; coordinate < dimension; ++coordinate) {
        const int8_t orientation = factor_orientation[coordinate];
        int64_t returned = sections[vector_at + coordinate];
        if (orientation != 0) {
            returned += orientation > 0 ? residual : -residual;
            ++factor_work;
        }
        transported[vector_at + coordinate] = canonical_mod(returned, modulus);
    }
    selected_route[family] = held != 0U ? 0U : 2U;
    ablated_route[family] = selected_route[family];
    local_semantic_work[family] = constraint_work + factor_work;
    local_semantic_span[family] = constraint_span + (factor_work == 0ULL ? 0ULL : 1ULL);
}

extern "C" __global__ void reduce_fixed_section_families(
    const uint32_t *selected_route,
    const uint32_t *ablated_route,
    const uint64_t *local_semantic_work,
    const uint64_t *local_semantic_span,
    uint32_t *joint_cultivated,
    uint32_t *local_ablated_joint,
    uint64_t *semantic_work,
    uint64_t *semantic_span,
    uint32_t families)
{
    if (blockIdx.x != 0U || threadIdx.x != 0U) {
        return;
    }
    uint32_t joint = 1U;
    uint64_t work = (uint64_t)families
        + (uint64_t)families * (uint64_t)families;
    uint64_t span = 0ULL;
    for (uint32_t family = 0U; family < families; ++family) {
        if (selected_route[family] != 1U) {
            joint = 0U;
        }
        work += local_semantic_work[family];
        if (local_semantic_span[family] > span) {
            span = local_semantic_span[family];
        }
    }
    joint_cultivated[0] = joint;
    for (uint32_t withdrawn = 0U; withdrawn < families; ++withdrawn) {
        uint32_t local_joint = 1U;
        for (uint32_t family = 0U; family < families; ++family) {
            const uint32_t route = family == withdrawn
                ? ablated_route[family]
                : selected_route[family];
            if (route != 1U) {
                local_joint = 0U;
            }
        }
        local_ablated_joint[withdrawn] = local_joint;
    }
    semantic_work[0] = work;
    semantic_span[0] = span + (uint64_t)families;
}

extern "C" __global__ void conduct_inference_ecology(
    const uint32_t *recurrent_action,
    const uint32_t *recurrent_start,
    uint32_t *recurrent_predecessor_trace,
    uint32_t *recurrent_successor_trace,
    uint32_t *recurrent_withdrawn_trace,
    uint32_t *recurrent_selected_trace,
    uint32_t *recurrent_predecessor_length,
    uint32_t *recurrent_successor_length,
    uint32_t *recurrent_withdrawn_length,
    uint32_t *recurrent_selected_length,
    uint32_t *recurrent_seen,
    uint32_t recurrent_cells,
    uint32_t recurrent_states,
    uint32_t recurrent_seen_words,
    uint32_t recurrent_predecessor_from,
    uint32_t recurrent_predecessor_to,
    const uint32_t *world_action,
    const uint32_t *world_decoder,
    const uint32_t *world_start,
    uint32_t *world_predecessor_consequence,
    uint32_t *world_successor_consequence,
    uint32_t *world_selected_consequence,
    uint32_t *world_shared_ablated_consequence,
    uint32_t *world_local_ablated_consequence,
    uint32_t world_cells,
    uint32_t world_states,
    uint32_t world_ports,
    uint32_t committed)
{
    const uint32_t at = blockIdx.x * blockDim.x + threadIdx.x;
    if (at < recurrent_cells) {
        const uint32_t stride = recurrent_states + 1U;
        const uint64_t trace_at = (uint64_t)at * (uint64_t)stride;
        const uint64_t seen_stride = (uint64_t)recurrent_cells * recurrent_seen_words;
        const uint64_t seen_at = (uint64_t)at * recurrent_seen_words;
        recurrent_predecessor_length[at] = condensed_recurrent_trace(
            recurrent_action, recurrent_start[at], recurrent_states, true, false,
            recurrent_predecessor_from, recurrent_predecessor_to,
            recurrent_seen + seen_at, recurrent_predecessor_trace + trace_at);
        recurrent_successor_length[at] = condensed_recurrent_trace(
            recurrent_action, recurrent_start[at], recurrent_states, false, false,
            recurrent_predecessor_from, recurrent_predecessor_to,
            recurrent_seen + seen_stride + seen_at, recurrent_successor_trace + trace_at);
        recurrent_withdrawn_length[at] = condensed_recurrent_trace(
            recurrent_action, recurrent_start[at], recurrent_states, false, true,
            recurrent_predecessor_from, recurrent_predecessor_to,
            recurrent_seen + 2ULL * seen_stride + seen_at,
            recurrent_withdrawn_trace + trace_at);
        recurrent_selected_length[at] = condensed_recurrent_trace(
            recurrent_action, recurrent_start[at], recurrent_states, committed == 0U, false,
            recurrent_predecessor_from, recurrent_predecessor_to,
            recurrent_seen + 3ULL * seen_stride + seen_at,
            recurrent_selected_trace + trace_at);
    }
    if (at < world_cells) {
        const uint32_t start = world_start[at];
        const uint32_t next = world_action[start];
        const uint64_t decoder_at = (uint64_t)at * (uint64_t)world_states;
        const uint32_t before = world_decoder[decoder_at + start];
        const uint32_t after = world_decoder[decoder_at + next];
        world_predecessor_consequence[at] = before;
        world_successor_consequence[at] = after;
        world_selected_consequence[at] = committed == 0U ? before : after;
        world_shared_ablated_consequence[at] = before;
        const uint32_t local_port = at % world_ports;
        const uint64_t local_at = (uint64_t)at * (uint64_t)world_ports;
        for (uint32_t withdrawn_port = 0; withdrawn_port < world_ports; ++withdrawn_port) {
            world_local_ablated_consequence[local_at + withdrawn_port] =
                local_port == withdrawn_port ? before : after;
        }
    }
}

extern "C" __global__ void conduct_material_operation_world_tube(
    const uint64_t *face_key,
    const uint32_t *face_branch,
    const uint64_t *branch_staging_event,
    const uint64_t *branch_terminal_event,
    const uint32_t *contact_from,
    const uint32_t *contact_to,
    const uint32_t *contact_relation,
    uint32_t *face_payload_class,
    uint32_t *face_comparison_count,
    uint64_t *face_staging_event,
    uint64_t *face_terminal_event,
    uint32_t *contact_left_class,
    uint32_t *contact_right_class,
    uint32_t *contact_relation_out,
    uint64_t *recurrence_staging_event,
    uint64_t *recurrence_terminal_event,
    uint32_t face_count,
    uint32_t contact_count,
    uint32_t branch_count,
    uint32_t recurrence_cells_per_branch,
    const uint32_t *recurrent_action,
    const uint32_t *recurrent_start,
    uint32_t *recurrent_predecessor_trace,
    uint32_t *recurrent_successor_trace,
    uint32_t *recurrent_withdrawn_trace,
    uint32_t *recurrent_selected_trace,
    uint32_t *recurrent_predecessor_length,
    uint32_t *recurrent_successor_length,
    uint32_t *recurrent_withdrawn_length,
    uint32_t *recurrent_selected_length,
    uint32_t *recurrent_seen,
    uint32_t recurrent_cells,
    uint32_t recurrent_states,
    uint32_t recurrent_seen_words,
    uint32_t recurrent_predecessor_from,
    uint32_t recurrent_predecessor_to,
    const uint32_t *world_action,
    const uint32_t *world_decoder,
    const uint32_t *world_start,
    uint32_t *world_predecessor_consequence,
    uint32_t *world_successor_consequence,
    uint32_t *world_selected_consequence,
    uint32_t *world_shared_ablated_consequence,
    uint32_t *world_local_ablated_consequence,
    uint32_t world_cells,
    uint32_t world_cells_per_branch,
    uint32_t world_states,
    uint32_t world_ports,
    uint32_t committed)
{
    const uint32_t at = blockIdx.x * blockDim.x + threadIdx.x;
    if (at < face_count) {
        uint32_t comparisons = 0U;
        face_payload_class[at] = first_equal_payload(face_key, at, &comparisons);
        face_comparison_count[at] = comparisons;
        const uint32_t branch = face_branch[at];
        if (branch >= branch_count) {
            return;
        }
        face_staging_event[at] = branch_staging_event[branch];
        face_terminal_event[at] = branch_terminal_event[branch];
    }
    if (at < contact_count) {
        uint32_t ignored = 0U;
        contact_left_class[at] = first_equal_payload(face_key, contact_from[at], &ignored);
        contact_right_class[at] = first_equal_payload(face_key, contact_to[at], &ignored);
        contact_relation_out[at] = contact_relation[at];
    }
    if (at < recurrent_cells) {
        const uint32_t branch = at / recurrence_cells_per_branch;
        if (branch >= branch_count) {
            return;
        }
        recurrence_staging_event[at] = branch_staging_event[branch];
        recurrence_terminal_event[at] = branch_terminal_event[branch];
        const uint32_t stride = recurrent_states + 1U;
        const uint64_t trace_at = (uint64_t)at * (uint64_t)stride;
        const uint64_t seen_stride = (uint64_t)recurrent_cells * recurrent_seen_words;
        const uint64_t seen_at = (uint64_t)at * recurrent_seen_words;
        const uint32_t recurrent_start_at = recurrent_start[at % recurrence_cells_per_branch];
        recurrent_predecessor_length[at] = condensed_recurrent_trace(
            recurrent_action, recurrent_start_at, recurrent_states, true, false,
            recurrent_predecessor_from, recurrent_predecessor_to,
            recurrent_seen + seen_at, recurrent_predecessor_trace + trace_at);
        recurrent_successor_length[at] = condensed_recurrent_trace(
            recurrent_action, recurrent_start_at, recurrent_states, false, false,
            recurrent_predecessor_from, recurrent_predecessor_to,
            recurrent_seen + seen_stride + seen_at, recurrent_successor_trace + trace_at);
        recurrent_withdrawn_length[at] = condensed_recurrent_trace(
            recurrent_action, recurrent_start_at, recurrent_states, false, true,
            recurrent_predecessor_from, recurrent_predecessor_to,
            recurrent_seen + 2ULL * seen_stride + seen_at,
            recurrent_withdrawn_trace + trace_at);
        recurrent_selected_length[at] = condensed_recurrent_trace(
            recurrent_action, recurrent_start_at, recurrent_states, committed == 0U, false,
            recurrent_predecessor_from, recurrent_predecessor_to,
            recurrent_seen + 3ULL * seen_stride + seen_at,
            recurrent_selected_trace + trace_at);
    }
    if (at < world_cells) {
        const uint32_t world_at = at % world_cells_per_branch;
        const uint32_t start = world_start[world_at];
        const uint32_t next = world_action[start];
        const uint64_t decoder_at = (uint64_t)world_at * (uint64_t)world_states;
        const uint32_t before = world_decoder[decoder_at + start];
        const uint32_t after = world_decoder[decoder_at + next];
        world_predecessor_consequence[at] = before;
        world_successor_consequence[at] = after;
        world_selected_consequence[at] = committed == 0U ? before : after;
        world_shared_ablated_consequence[at] = before;
        const uint32_t local_port = at % world_ports;
        const uint64_t local_at = (uint64_t)at * (uint64_t)world_ports;
        for (uint32_t withdrawn_port = 0; withdrawn_port < world_ports; ++withdrawn_port) {
            world_local_ablated_consequence[local_at + withdrawn_port] =
                local_port == withdrawn_port ? before : after;
        }
    }
}

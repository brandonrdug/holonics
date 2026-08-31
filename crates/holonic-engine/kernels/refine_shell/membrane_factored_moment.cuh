// Membrane factored-moment transport and reconstruction.
// This fragment is included by refine_shell.cu after refine_shared.cuh.

extern "C" __global__ void transport_membrane_factored_moment_incidence(
    const uint8_t *source_signs,
    const uint32_t *source_limbs,
    const uint32_t *generator_targets,
    uint8_t *target_signs,
    uint32_t *target_limbs,
    uint32_t source_rank,
    uint32_t factor_count,
    uint32_t generator_count,
    uint32_t source_limb_count,
    uint32_t target_limb_count,
    uint32_t *overflow)
{
    const uint32_t row = blockIdx.x * blockDim.x + threadIdx.x;
    const uint64_t row_count = (uint64_t)source_rank * (uint64_t)generator_count;
    if ((uint64_t)row >= row_count) return;
    const uint32_t generator = row / source_rank;
    const uint32_t source_image = row % source_rank;
    uint8_t *target_row_signs = target_signs + (uint64_t)row * (uint64_t)factor_count;
    uint32_t *target_row_limbs = target_limbs
        + (uint64_t)row * (uint64_t)factor_count * (uint64_t)target_limb_count;
    for (uint32_t factor = 0U; factor < factor_count; ++factor) {
        target_row_signs[factor] = 0U;
        zero_unsigned_limbs(
            target_row_limbs + (uint64_t)factor * (uint64_t)target_limb_count,
            target_limb_count);
    }
    for (uint32_t source_factor = 0U; source_factor < factor_count; ++source_factor) {
        const uint32_t target_factor = generator_targets[
            (uint64_t)generator * (uint64_t)factor_count + source_factor];
        if (target_factor >= factor_count) {
            atomicExch(overflow, 1U);
            continue;
        }
        const uint64_t source_at =
            (uint64_t)source_image * (uint64_t)factor_count + source_factor;
        add_widened_signed_magnitude(
            target_row_signs + target_factor,
            target_row_limbs
                + (uint64_t)target_factor * (uint64_t)target_limb_count,
            target_limb_count,
            source_signs[source_at],
            source_limbs + source_at * (uint64_t)source_limb_count,
            source_limb_count,
            overflow);
    }
}

extern "C" __global__ void identify_membrane_equal_factored_history_blocks(
    const uint8_t *candidate_signs,
    const uint32_t *candidate_limbs,
    uint32_t *representatives,
    uint32_t candidate_history_count,
    uint32_t block_entry_count,
    uint32_t limb_count)
{
    const uint32_t candidate = blockIdx.x * blockDim.x + threadIdx.x;
    if (candidate >= candidate_history_count) return;
    const uint64_t entry_base = (uint64_t)candidate * (uint64_t)block_entry_count;
    const uint64_t limb_base = entry_base * (uint64_t)limb_count;
    uint32_t representative = candidate;
    for (uint32_t prior = 0U; prior < candidate; ++prior) {
        const uint64_t prior_entry_base = (uint64_t)prior * (uint64_t)block_entry_count;
        const uint64_t prior_limb_base = prior_entry_base * (uint64_t)limb_count;
        bool equal = true;
        for (uint32_t entry = 0U; entry < block_entry_count; ++entry) {
            if (candidate_signs[entry_base + entry]
                != candidate_signs[prior_entry_base + entry]) {
                equal = false;
                break;
            }
        }
        if (!equal) continue;
        const uint64_t block_limbs = (uint64_t)block_entry_count * (uint64_t)limb_count;
        for (uint64_t limb = 0ULL; limb < block_limbs; ++limb) {
            if (candidate_limbs[limb_base + limb]
                != candidate_limbs[prior_limb_base + limb]) {
                equal = false;
                break;
            }
        }
        if (equal) {
            representative = prior;
            break;
        }
    }
    representatives[candidate] = representative;
}

extern "C" __global__ void compact_membrane_equal_factored_history_blocks(
    const uint8_t *candidate_signs,
    const uint32_t *candidate_limbs,
    const uint32_t *source_weight_limbs,
    const uint32_t *representatives,
    uint8_t *target_signs,
    uint32_t *target_limbs,
    uint32_t *target_weight_limbs,
    uint32_t *candidate_to_target,
    uint32_t *target_count,
    uint32_t source_history_count,
    uint32_t generator_count,
    uint32_t block_entry_count,
    uint32_t incidence_limb_count,
    uint32_t source_weight_limb_count,
    uint32_t target_weight_limb_count,
    uint32_t *overflow)
{
    const uint32_t candidate = blockIdx.x * blockDim.x + threadIdx.x;
    const uint32_t candidate_count = source_history_count * generator_count;
    if (candidate >= candidate_count) return;
    const uint32_t representative = representatives[candidate];
    uint32_t compact = 0U;
    for (uint32_t prior = 0U; prior < representative; ++prior) {
        if (representatives[prior] == prior) ++compact;
    }
    candidate_to_target[candidate] = compact;
    if (representative != candidate) return;

    const uint64_t block_entries = (uint64_t)block_entry_count;
    const uint64_t source_entry_base = (uint64_t)candidate * block_entries;
    const uint64_t target_entry_base = (uint64_t)compact * block_entries;
    for (uint64_t entry = 0ULL; entry < block_entries; ++entry) {
        target_signs[target_entry_base + entry] = candidate_signs[source_entry_base + entry];
    }
    const uint64_t block_limbs = block_entries * (uint64_t)incidence_limb_count;
    const uint64_t source_limb_base = (uint64_t)candidate * block_limbs;
    const uint64_t target_limb_base = (uint64_t)compact * block_limbs;
    for (uint64_t limb = 0ULL; limb < block_limbs; ++limb) {
        target_limbs[target_limb_base + limb] = candidate_limbs[source_limb_base + limb];
    }

    uint32_t *target_weight = target_weight_limbs
        + (uint64_t)compact * (uint64_t)target_weight_limb_count;
    zero_unsigned_limbs(target_weight, target_weight_limb_count);
    for (uint32_t member = 0U; member < candidate_count; ++member) {
        if (representatives[member] != candidate) continue;
        const uint32_t source_history = member % source_history_count;
        const uint32_t *source_weight = source_weight_limbs
            + (uint64_t)source_history * (uint64_t)source_weight_limb_count;
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
        if (carry != 0ULL) atomicExch(overflow, 1U);
    }
    atomicMax(target_count, compact + 1U);
}

extern "C" __global__ void derive_membrane_factored_moment_modular_rank(
    const uint8_t *source_signs,
    const uint32_t *source_limbs,
    const uint32_t *primes,
    uint32_t *work,
    uint32_t *row_addresses,
    uint32_t *ranks,
    uint32_t *pivot_rows,
    uint32_t *pivot_columns,
    uint32_t row_count,
    uint32_t factor_count,
    uint32_t limb_count,
    uint32_t chart_count,
    uint32_t *obstruction)
{
    const uint32_t chart = blockIdx.x * blockDim.x + threadIdx.x;
    if (chart >= chart_count) return;
    const uint32_t prime = primes[chart];
    if (prime < 3U || (prime & 1U) == 0U) {
        atomicExch(obstruction, 1U);
        return;
    }
    uint32_t *chart_work = work
        + (uint64_t)chart * (uint64_t)row_count * (uint64_t)factor_count;
    uint32_t *chart_rows = row_addresses + (uint64_t)chart * (uint64_t)row_count;
    uint32_t *chart_pivot_rows = pivot_rows + (uint64_t)chart * (uint64_t)row_count;
    uint32_t *chart_pivot_columns = pivot_columns + (uint64_t)chart * (uint64_t)row_count;
    for (uint32_t row = 0U; row < row_count; ++row) {
        chart_rows[row] = row;
        chart_pivot_rows[row] = 0xffffffffU;
        chart_pivot_columns[row] = 0xffffffffU;
        for (uint32_t factor = 0U; factor < factor_count; ++factor) {
            const uint64_t entry = (uint64_t)row * (uint64_t)factor_count + factor;
            chart_work[(uint64_t)row * (uint64_t)factor_count + factor] =
                signed_limbs_mod_word(
                    source_signs[entry],
                    source_limbs + entry * (uint64_t)limb_count,
                    limb_count,
                    prime);
        }
    }

    uint32_t rank = 0U;
    for (uint32_t factor = 0U; factor < factor_count && rank < row_count; ++factor) {
        uint32_t pivot = rank;
        while (pivot < row_count
            && chart_work[(uint64_t)pivot * (uint64_t)factor_count + factor] == 0U) {
            ++pivot;
        }
        if (pivot == row_count) continue;
        if (pivot != rank) {
            for (uint32_t column = 0U; column < factor_count; ++column) {
                const uint64_t left = (uint64_t)rank * (uint64_t)factor_count + column;
                const uint64_t right = (uint64_t)pivot * (uint64_t)factor_count + column;
                const uint32_t held = chart_work[left];
                chart_work[left] = chart_work[right];
                chart_work[right] = held;
            }
            const uint32_t held_row = chart_rows[rank];
            chart_rows[rank] = chart_rows[pivot];
            chart_rows[pivot] = held_row;
        }
        chart_pivot_rows[rank] = chart_rows[rank];
        chart_pivot_columns[rank] = factor;
        const uint32_t pivot_value =
            chart_work[(uint64_t)rank * (uint64_t)factor_count + factor];
        const uint32_t inverse = word_modular_power(pivot_value, prime - 2U, prime);
        if (((uint64_t)pivot_value * (uint64_t)inverse) % (uint64_t)prime != 1ULL) {
            atomicExch(obstruction, 1U);
            return;
        }
        for (uint32_t column = factor; column < factor_count; ++column) {
            const uint64_t at = (uint64_t)rank * (uint64_t)factor_count + column;
            chart_work[at] = (uint32_t)(
                ((uint64_t)chart_work[at] * (uint64_t)inverse) % (uint64_t)prime);
        }
        for (uint32_t row = rank + 1U; row < row_count; ++row) {
            const uint64_t pivot_at = (uint64_t)row * (uint64_t)factor_count + factor;
            const uint32_t coefficient = chart_work[pivot_at];
            if (coefficient == 0U) continue;
            for (uint32_t column = factor; column < factor_count; ++column) {
                const uint64_t target = (uint64_t)row * (uint64_t)factor_count + column;
                const uint64_t source = (uint64_t)rank * (uint64_t)factor_count + column;
                const uint32_t removed = (uint32_t)(
                    ((uint64_t)coefficient * (uint64_t)chart_work[source])
                    % (uint64_t)prime);
                chart_work[target] = chart_work[target] >= removed
                    ? chart_work[target] - removed
                    : chart_work[target] + prime - removed;
            }
        }
        ++rank;
    }
    ranks[chart] = rank;
}

extern "C" __global__ void select_membrane_factored_moment_modular_rank(
    const uint32_t *ranks,
    const uint32_t *pivot_rows,
    const uint32_t *pivot_columns,
    uint32_t *selected_chart,
    uint32_t *selected_rank,
    uint32_t *selected_rows,
    uint32_t *selected_columns,
    uint32_t row_count,
    uint32_t chart_count,
    uint32_t *obstruction)
{
    if (blockIdx.x != 0U || threadIdx.x != 0U) return;
    uint32_t best_chart = 0xffffffffU;
    uint32_t best_rank = 0U;
    for (uint32_t chart = 0U; chart < chart_count; ++chart) {
        if (ranks[chart] > best_rank) {
            best_rank = ranks[chart];
            best_chart = chart;
        }
    }
    if (best_chart == 0xffffffffU || best_rank == 0U) {
        atomicExch(obstruction, 1U);
        return;
    }
    *selected_chart = best_chart;
    *selected_rank = best_rank;
    for (uint32_t at = 0U; at < row_count; ++at) {
        selected_rows[at] = at < best_rank
            ? pivot_rows[(uint64_t)best_chart * (uint64_t)row_count + at]
            : 0xffffffffU;
        selected_columns[at] = at < best_rank
            ? pivot_columns[(uint64_t)best_chart * (uint64_t)row_count + at]
            : 0xffffffffU;
    }
}

extern "C" __global__ void derive_membrane_factored_moment_coordinate_residues(
    const uint8_t *source_signs,
    const uint32_t *source_limbs,
    const uint32_t *selected_rank,
    const uint32_t *selected_rows,
    const uint32_t *selected_columns,
    const uint32_t *primes,
    const uint8_t *constitutive_signs,
    const uint32_t *constitutive_limbs,
    uint32_t *augmented_work,
    uint8_t *good_charts,
    uint32_t *residues,
    uint32_t row_count,
    uint32_t factor_count,
    uint32_t source_limb_count,
    uint32_t source_rank,
    uint32_t generator_count,
    uint32_t constitutive_limb_count,
    uint32_t maximal_rank,
    uint32_t chart_count,
    uint32_t *obstruction)
{
    const uint32_t chart = blockIdx.x * blockDim.x + threadIdx.x;
    if (chart >= chart_count) return;
    const uint32_t rank = *selected_rank;
    const uint32_t prime = primes[chart];
    const uint64_t value_count = 1ULL
        + (uint64_t)row_count * (uint64_t)maximal_rank
        + (uint64_t)maximal_rank * (uint64_t)maximal_rank;
    uint32_t *chart_residues = residues + (uint64_t)chart * value_count;
    for (uint64_t value = 0ULL; value < value_count; ++value) chart_residues[value] = 0U;
    good_charts[chart] = 0U;
    if (rank == 0U || rank > maximal_rank
        || (uint64_t)row_count != (uint64_t)source_rank * (uint64_t)generator_count) {
        atomicExch(obstruction, 1U);
        return;
    }
    const uint32_t stride = 2U * maximal_rank;
    uint32_t *matrix = augmented_work
        + (uint64_t)chart * (uint64_t)maximal_rank * (uint64_t)stride;
    for (uint32_t row = 0U; row < rank; ++row) {
        if (selected_rows[row] >= row_count) {
            atomicExch(obstruction, 1U);
            return;
        }
        for (uint32_t column = 0U; column < rank; ++column) {
            if (selected_columns[column] >= factor_count) {
                atomicExch(obstruction, 1U);
                return;
            }
            const uint64_t entry = (uint64_t)selected_rows[row] * (uint64_t)factor_count
                + selected_columns[column];
            matrix[(uint64_t)row * stride + column] = signed_limbs_mod_word(
                source_signs[entry],
                source_limbs + entry * (uint64_t)source_limb_count,
                source_limb_count,
                prime);
            matrix[(uint64_t)row * stride + rank + column] = row == column ? 1U : 0U;
        }
    }
    uint32_t determinant = 1U;
    for (uint32_t column = 0U; column < rank; ++column) {
        uint32_t pivot = column;
        while (pivot < rank && matrix[(uint64_t)pivot * stride + column] == 0U) ++pivot;
        if (pivot == rank) return;
        if (pivot != column) {
            for (uint32_t held = 0U; held < 2U * rank; ++held) {
                const uint64_t left = (uint64_t)column * stride + held;
                const uint64_t right = (uint64_t)pivot * stride + held;
                const uint32_t value = matrix[left];
                matrix[left] = matrix[right];
                matrix[right] = value;
            }
            determinant = determinant == 0U ? 0U : prime - determinant;
        }
        const uint32_t pivot_value = matrix[(uint64_t)column * stride + column];
        determinant = (uint32_t)(
            ((uint64_t)determinant * (uint64_t)pivot_value) % (uint64_t)prime);
        const uint32_t inverse = word_modular_power(pivot_value, prime - 2U, prime);
        for (uint32_t held = 0U; held < 2U * rank; ++held) {
            const uint64_t at = (uint64_t)column * stride + held;
            matrix[at] = (uint32_t)(
                ((uint64_t)matrix[at] * (uint64_t)inverse) % (uint64_t)prime);
        }
        for (uint32_t row = 0U; row < rank; ++row) {
            if (row == column) continue;
            const uint32_t coefficient = matrix[(uint64_t)row * stride + column];
            if (coefficient == 0U) continue;
            for (uint32_t held = 0U; held < 2U * rank; ++held) {
                const uint64_t target = (uint64_t)row * stride + held;
                const uint64_t source = (uint64_t)column * stride + held;
                const uint32_t removed = (uint32_t)(
                    ((uint64_t)coefficient * (uint64_t)matrix[source])
                    % (uint64_t)prime);
                matrix[target] = matrix[target] >= removed
                    ? matrix[target] - removed
                    : matrix[target] + prime - removed;
            }
        }
    }
    if (determinant == 0U) return;
    good_charts[chart] = 1U;
    chart_residues[0] = determinant;
    const uint64_t joining_start = 1ULL;
    for (uint32_t row = 0U; row < row_count; ++row) {
        for (uint32_t target = 0U; target < rank; ++target) {
            uint64_t coordinate = 0ULL;
            for (uint32_t held = 0U; held < rank; ++held) {
                const uint64_t entry = (uint64_t)row * (uint64_t)factor_count
                    + selected_columns[held];
                const uint32_t value = signed_limbs_mod_word(
                    source_signs[entry],
                    source_limbs + entry * (uint64_t)source_limb_count,
                    source_limb_count,
                    prime);
                coordinate = (coordinate
                    + (uint64_t)value * matrix[(uint64_t)held * stride + rank + target])
                    % (uint64_t)prime;
            }
            chart_residues[joining_start
                + (uint64_t)row * maximal_rank + target] =
                (uint32_t)((coordinate * determinant) % (uint64_t)prime);
        }
    }
    const uint64_t constitutive_start = joining_start
        + (uint64_t)row_count * (uint64_t)maximal_rank;
    for (uint32_t left = 0U; left < rank; ++left) {
        for (uint32_t right = 0U; right < rank; ++right) {
            uint64_t value = 0ULL;
            for (uint32_t generator = 0U; generator < generator_count; ++generator) {
                for (uint32_t source_left = 0U; source_left < source_rank; ++source_left) {
                    const uint32_t joined_left = chart_residues[joining_start
                        + (uint64_t)(generator * source_rank + source_left) * maximal_rank
                        + left];
                    if (joined_left == 0U) continue;
                    for (uint32_t source_right = 0U; source_right < source_rank; ++source_right) {
                        const uint64_t constitutive_at =
                            (uint64_t)source_left * source_rank + source_right;
                        const uint32_t constitutive = signed_limbs_mod_word(
                            constitutive_signs[constitutive_at],
                            constitutive_limbs
                                + constitutive_at * (uint64_t)constitutive_limb_count,
                            constitutive_limb_count,
                            prime);
                        const uint32_t joined_right = chart_residues[joining_start
                            + (uint64_t)(generator * source_rank + source_right) * maximal_rank
                            + right];
                        const uint64_t term = ((uint64_t)joined_left * constitutive)
                            % (uint64_t)prime * joined_right % (uint64_t)prime;
                        value = (value + term) % (uint64_t)prime;
                    }
                }
            }
            chart_residues[constitutive_start
                + (uint64_t)left * maximal_rank + right] = (uint32_t)value;
        }
    }
}

extern "C" __global__ void prepare_membrane_factored_moment_crt_chart(
    const uint32_t *prime,
    const uint8_t *good_chart,
    const uint32_t *total_product,
    uint32_t *prefix_product,
    uint32_t *prefix_inverse,
    uint32_t *active_chart,
    uint32_t crt_limb_count,
    uint32_t *obstruction)
{
    if (blockIdx.x != 0U || threadIdx.x != 0U) return;
    *active_chart = 0U;
    if (*good_chart == 0U) return;
    for (uint32_t limb = 0U; limb < crt_limb_count; ++limb) {
        prefix_product[limb] = total_product[limb];
    }
    const uint32_t modulus = *prime;
    const uint32_t prefix_mod = unsigned_limbs_mod_word(total_product, crt_limb_count, modulus);
    if (prefix_mod == 0U) {
        atomicExch(obstruction, 1U);
        return;
    }
    *prefix_inverse = word_modular_power(prefix_mod, modulus - 2U, modulus);
    *active_chart = 1U;
}

extern "C" __global__ void accumulate_membrane_factored_moment_crt_chart(
    const uint32_t *prime,
    const uint32_t *residues,
    const uint32_t *active_chart,
    const uint32_t *prefix_product,
    const uint32_t *prefix_inverse,
    uint32_t *reconstruction,
    uint32_t value_count,
    uint32_t crt_limb_count,
    uint32_t *obstruction)
{
    const uint32_t value = blockIdx.x * blockDim.x + threadIdx.x;
    if (value >= value_count || *active_chart == 0U) return;
    const uint32_t modulus = *prime;
    uint32_t *output = reconstruction + (uint64_t)value * crt_limb_count;
    const uint32_t held = unsigned_limbs_mod_word(output, crt_limb_count, modulus);
    const uint32_t residue = residues[value];
    const uint32_t difference = residue >= held ? residue - held : residue + modulus - held;
    const uint32_t coefficient = (uint32_t)(
        ((uint64_t)difference * *prefix_inverse) % (uint64_t)modulus);
    uint64_t carry = 0ULL;
    for (uint32_t limb = 0U; limb < crt_limb_count; ++limb) {
        const uint64_t sum = (uint64_t)prefix_product[limb] * coefficient
            + output[limb] + carry;
        output[limb] = (uint32_t)sum;
        carry = sum >> 32U;
    }
    if (carry != 0ULL) atomicExch(obstruction, 1U);
}

extern "C" __global__ void advance_membrane_factored_moment_crt_chart(
    const uint32_t *prime,
    const uint32_t *active_chart,
    uint32_t *total_product,
    uint32_t *good_count,
    uint32_t crt_limb_count,
    uint32_t *obstruction)
{
    if (blockIdx.x != 0U || threadIdx.x != 0U || *active_chart == 0U) return;
    uint64_t carry = 0ULL;
    for (uint32_t limb = 0U; limb < crt_limb_count; ++limb) {
        const uint64_t product = (uint64_t)total_product[limb] * *prime + carry;
        total_product[limb] = (uint32_t)product;
        carry = product >> 32U;
    }
    if (carry != 0ULL) {
        atomicExch(obstruction, 1U);
        return;
    }
    *good_count += 1U;
}

extern "C" __global__ void close_membrane_factored_moment_crt_product(
    const uint32_t *total_product,
    const uint32_t *good_count,
    const uint32_t *signed_reconstruction_bound,
    uint32_t *half_product,
    uint32_t crt_limb_count,
    uint32_t bound_limb_count,
    uint32_t *obstruction)
{
    if (blockIdx.x != 0U || threadIdx.x != 0U) return;
    if (*good_count == 0U
        || compare_widened_magnitude(
            total_product,
            crt_limb_count,
            signed_reconstruction_bound,
            bound_limb_count) <= 0) {
        atomicExch(obstruction, 1U);
        return;
    }
    uint32_t incoming = 0U;
    for (uint32_t held = crt_limb_count; held > 0U; --held) {
        const uint32_t limb = total_product[held - 1U];
        half_product[held - 1U] = (limb >> 1U) | incoming;
        incoming = (limb & 1U) << 31U;
    }
}

extern "C" __global__ void center_membrane_factored_moment_signed_crt(
    const uint32_t *total_product,
    const uint32_t *half_product,
    const uint32_t *absolute_bound,
    uint8_t *output_signs,
    uint32_t *output_limbs,
    uint32_t value_count,
    uint32_t crt_limb_count,
    uint32_t bound_limb_count,
    uint32_t *obstruction)
{
    const uint32_t value = blockIdx.x * blockDim.x + threadIdx.x;
    if (value >= value_count) return;
    uint32_t *output = output_limbs + (uint64_t)value * crt_limb_count;
    if (compare_widened_magnitude(output, crt_limb_count, half_product, crt_limb_count) > 0) {
        uint64_t borrow = 0ULL;
        for (uint32_t limb = 0U; limb < crt_limb_count; ++limb) {
            const uint64_t subtrahend = (uint64_t)output[limb] + borrow;
            const uint64_t minuend = total_product[limb];
            output[limb] = (uint32_t)(minuend - subtrahend);
            borrow = minuend < subtrahend ? 1ULL : 0ULL;
        }
        if (borrow != 0ULL) {
            atomicExch(obstruction, 1U);
            return;
        }
        output_signs[value] = 2U;
    } else {
        output_signs[value] = 1U;
    }
    bool zero = true;
    for (uint32_t limb = 0U; limb < crt_limb_count; ++limb) zero = zero && output[limb] == 0U;
    if (zero) output_signs[value] = 0U;
    if (compare_widened_magnitude(
        output,
        crt_limb_count,
        absolute_bound,
        bound_limb_count) > 0) {
        atomicExch(obstruction, 1U);
    }
}

extern "C" __global__ void project_membrane_factored_moment_square_source_residues(
    const uint8_t *transported_signs,
    const uint32_t *transported_limbs,
    const uint8_t *constitutive_signs,
    const uint32_t *constitutive_limbs,
    const uint32_t *primes,
    uint32_t *transported_residues,
    uint32_t *constitutive_residues,
    uint32_t row_count,
    uint32_t factor_count,
    uint32_t source_rank,
    uint32_t source_limb_count,
    uint32_t constitutive_limb_count,
    uint32_t chart_count,
    uint32_t *obstruction)
{
    const uint64_t occurrence =
        (uint64_t)blockIdx.x * (uint64_t)blockDim.x + threadIdx.x;
    const uint64_t transported_count = (uint64_t)row_count * factor_count;
    const uint64_t constitutive_count = (uint64_t)source_rank * source_rank;
    const uint64_t chart_width = transported_count + constitutive_count;
    const uint64_t occurrence_count = (uint64_t)chart_count * chart_width;
    if (occurrence >= occurrence_count || *obstruction != 0U) return;
    const uint32_t chart = (uint32_t)(occurrence / chart_width);
    const uint64_t local = occurrence % chart_width;
    const uint32_t prime = primes[chart];
    if (local < transported_count) {
        transported_residues[(uint64_t)chart * transported_count + local] =
            signed_limbs_mod_word(
                transported_signs[local],
                transported_limbs + local * source_limb_count,
                source_limb_count,
                prime);
        return;
    }
    const uint64_t constitutive = local - transported_count;
    constitutive_residues[(uint64_t)chart * constitutive_count + constitutive] =
        signed_limbs_mod_word(
            constitutive_signs[constitutive],
            constitutive_limbs + constitutive * constitutive_limb_count,
            constitutive_limb_count,
            prime);
}

extern "C" __global__ void verify_membrane_factored_moment_reconstruction_squares(
    const uint32_t *coordinate_residues,
    const uint32_t *transported_residues,
    const uint32_t *constitutive_residues,
    const uint32_t *selected_rank,
    const uint32_t *selected_rows,
    const uint32_t *primes,
    uint8_t *chart_witnesses,
    uint32_t row_count,
    uint32_t factor_count,
    uint32_t source_rank,
    uint32_t generator_count,
    uint32_t maximal_rank,
    uint32_t chart_count,
    uint32_t *obstruction)
{
    const uint64_t occurrence =
        (uint64_t)blockIdx.x * (uint64_t)blockDim.x + threadIdx.x;
    const uint64_t factorization_cells = (uint64_t)row_count * factor_count;
    const uint64_t constitutive_cells = (uint64_t)maximal_rank * maximal_rank;
    const uint64_t cells_per_chart = factorization_cells + constitutive_cells;
    const uint64_t occurrence_count = (uint64_t)chart_count * cells_per_chart;
    if (occurrence >= occurrence_count) return;
    const uint32_t chart = (uint32_t)(occurrence / cells_per_chart);
    const uint64_t cell = occurrence % cells_per_chart;
    const uint32_t rank = *selected_rank;
    if (rank == 0U || rank > maximal_rank
        || (uint64_t)row_count != (uint64_t)source_rank * generator_count) {
        atomicExch(obstruction, 1U);
        return;
    }
    const uint64_t value_count = 1ULL
        + (uint64_t)row_count * maximal_rank
        + (uint64_t)maximal_rank * maximal_rank;
    const uint32_t *chart_coordinates = coordinate_residues + (uint64_t)chart * value_count;
    const uint64_t transported_count = (uint64_t)row_count * factor_count;
    const uint64_t source_constitutive_count = (uint64_t)source_rank * source_rank;
    const uint32_t *chart_transport = transported_residues
        + (uint64_t)chart * transported_count;
    const uint32_t *chart_constitutive = constitutive_residues
        + (uint64_t)chart * source_constitutive_count;
    const uint32_t determinant = chart_coordinates[0];
    const uint64_t joining_start = 1ULL;
    if (cell < factorization_cells) {
        const uint32_t row = (uint32_t)(cell / factor_count);
        const uint32_t factor = (uint32_t)(cell % factor_count);
        uint64_t left = 0ULL;
        for (uint32_t image = 0U; image < rank; ++image) {
            const uint32_t basis_row = selected_rows[image];
            if (basis_row >= row_count) {
                chart_witnesses[chart] = 0U;
                atomicExch(obstruction, 1U);
                return;
            }
            const uint32_t joining = chart_coordinates[
                joining_start + (uint64_t)row * maximal_rank + image];
            const uint32_t basis = chart_transport[
                (uint64_t)basis_row * factor_count + factor];
            left += (uint64_t)joining * basis;
            left %= (uint64_t)primes[chart];
        }
        const uint32_t transported = chart_transport[cell];
        const uint32_t right = (uint32_t)(
            ((uint64_t)determinant * transported) % (uint64_t)primes[chart]);
        if ((uint32_t)left != right) {
            chart_witnesses[chart] = 0U;
            atomicExch(obstruction, 1U);
        }
        return;
    }
    const uint64_t constitutive_cell = cell - factorization_cells;
    const uint32_t left_image = (uint32_t)(constitutive_cell / maximal_rank);
    const uint32_t right_image = (uint32_t)(constitutive_cell % maximal_rank);
    if (left_image >= rank || right_image >= rank) return;
    const uint64_t constitutive_start = joining_start
        + (uint64_t)row_count * maximal_rank;
    uint64_t expected = 0ULL;
    const uint32_t prime = primes[chart];
    for (uint32_t generator = 0U; generator < generator_count; ++generator) {
        for (uint32_t source_left = 0U; source_left < source_rank; ++source_left) {
            const uint32_t joined_left = chart_coordinates[joining_start
                + (uint64_t)(generator * source_rank + source_left) * maximal_rank
                + left_image];
            for (uint32_t source_right = 0U; source_right < source_rank; ++source_right) {
                const uint32_t constitutive = chart_constitutive[
                    (uint64_t)source_left * source_rank + source_right];
                const uint32_t joined_right = chart_coordinates[joining_start
                    + (uint64_t)(generator * source_rank + source_right) * maximal_rank
                    + right_image];
                expected = (expected
                    + ((uint64_t)joined_left * constitutive % prime) * joined_right)
                    % (uint64_t)prime;
            }
        }
    }
    const uint32_t returned = chart_coordinates[constitutive_start
        + (uint64_t)left_image * maximal_rank + right_image];
    if (returned != (uint32_t)expected) {
        chart_witnesses[chart] = 0U;
        atomicExch(obstruction, 1U);
    }
}

extern "C" __global__ void gather_membrane_factored_moment_target_image(
    const uint8_t *transported_signs,
    const uint32_t *transported_limbs,
    const uint32_t *selected_rank,
    const uint32_t *selected_rows,
    const uint8_t *reconstructed_signs,
    const uint32_t *reconstructed_limbs,
    const uint32_t *source_denominator,
    uint8_t *target_incidence_signs,
    uint32_t *target_incidence_limbs,
    uint8_t *target_constitutive_signs,
    uint32_t *target_constitutive_limbs,
    uint32_t *target_denominator,
    uint32_t *denominator_scratch,
    uint32_t *admitted,
    uint32_t row_count,
    uint32_t factor_count,
    uint32_t source_limb_count,
    uint32_t maximal_rank,
    uint32_t crt_limb_count,
    uint32_t source_denominator_limb_count,
    uint32_t target_denominator_limb_count,
    const uint32_t *obstruction)
{
    if (blockIdx.x != 0U || threadIdx.x != 0U) return;
    *admitted = 0U;
    if (*obstruction != 0U) return;
    const uint32_t rank = *selected_rank;
    if (rank == 0U || rank > maximal_rank) return;
    for (uint32_t image = 0U; image < rank; ++image) {
        const uint32_t source_row = selected_rows[image];
        if (source_row >= row_count) return;
        for (uint32_t factor = 0U; factor < factor_count; ++factor) {
            const uint64_t source_at = (uint64_t)source_row * factor_count + factor;
            const uint64_t target_at = (uint64_t)image * factor_count + factor;
            target_incidence_signs[target_at] = transported_signs[source_at];
            for (uint32_t limb = 0U; limb < source_limb_count; ++limb) {
                target_incidence_limbs[target_at * source_limb_count + limb] =
                    transported_limbs[source_at * source_limb_count + limb];
            }
        }
    }
    const uint64_t constitutive_start = 1ULL
        + (uint64_t)row_count * maximal_rank;
    for (uint32_t left = 0U; left < rank; ++left) {
        for (uint32_t right = 0U; right < rank; ++right) {
            const uint64_t source_at = constitutive_start
                + (uint64_t)left * maximal_rank + right;
            const uint64_t target_at = (uint64_t)left * rank + right;
            target_constitutive_signs[target_at] = reconstructed_signs[source_at];
            for (uint32_t limb = 0U; limb < crt_limb_count; ++limb) {
                target_constitutive_limbs[target_at * crt_limb_count + limb] =
                    reconstructed_limbs[source_at * crt_limb_count + limb];
            }
        }
    }
    const uint32_t *determinant = reconstructed_limbs;
    multiply_unsigned_limbs(
        source_denominator,
        source_denominator_limb_count,
        determinant,
        crt_limb_count,
        denominator_scratch,
        target_denominator_limb_count);
    multiply_unsigned_limbs(
        denominator_scratch,
        target_denominator_limb_count,
        determinant,
        crt_limb_count,
        target_denominator,
        target_denominator_limb_count);
    if (unsigned_limbs_are_zero(target_denominator, target_denominator_limb_count)) return;
    *admitted = 1U;
}

extern "C" __global__ void contract_membrane_factored_moment_candidate_receivers(
    const uint8_t *incidence_signs,
    const uint32_t *incidence_limbs,
    const uint8_t *constitutive_signs,
    const uint32_t *constitutive_limbs,
    const uint32_t *selected_rank,
    const uint32_t *admitted,
    const uint64_t *form_entry_offsets,
    const uint32_t *form_entry_rows,
    const uint32_t *form_entry_columns,
    const uint8_t *form_entry_signs,
    const uint32_t *form_entry_limbs,
    uint8_t *output_signs,
    uint32_t *output_limbs,
    uint32_t *left_scratch,
    uint32_t *right_scratch,
    uint32_t *term_scratch,
    uint32_t form_count,
    uint32_t factor_count,
    uint32_t incidence_limb_count,
    uint32_t constitutive_limb_count,
    uint32_t coefficient_limb_count,
    uint32_t maximal_rank,
    uint32_t output_limb_count,
    uint32_t *obstruction)
{
    const uint32_t form = blockIdx.x * blockDim.x + threadIdx.x;
    if (form >= form_count) return;
    const uint64_t output_at = (uint64_t)form * output_limb_count;
    output_signs[form] = 0U;
    zero_unsigned_limbs(output_limbs + output_at, output_limb_count);
    if (*admitted != 1U || *obstruction != 0U) return;
    const uint32_t rank = *selected_rank;
    if (rank == 0U || rank > maximal_rank) {
        atomicExch(obstruction, 1U);
        return;
    }
    const uint64_t begin = form_entry_offsets[form];
    const uint64_t end = form_entry_offsets[(uint64_t)form + 1ULL];
    for (uint64_t entry = begin; entry < end; ++entry) {
        const uint32_t row_factor = form_entry_rows[entry];
        const uint32_t column_factor = form_entry_columns[entry];
        if (row_factor >= factor_count || column_factor >= factor_count) {
            atomicExch(obstruction, 1U);
            return;
        }
        for (uint32_t left = 0U; left < rank; ++left) {
            const uint64_t left_at = (uint64_t)left * factor_count + row_factor;
            if (incidence_signs[left_at] == 0U) continue;
            for (uint32_t right = 0U; right < rank; ++right) {
                const uint64_t right_at = (uint64_t)right * factor_count + column_factor;
                const uint64_t constitutive_at = (uint64_t)left * rank + right;
                if (incidence_signs[right_at] == 0U
                    || constitutive_signs[constitutive_at] == 0U) continue;
                multiply_unsigned_limbs(
                    incidence_limbs + left_at * incidence_limb_count,
                    incidence_limb_count,
                    constitutive_limbs + constitutive_at * constitutive_limb_count,
                    constitutive_limb_count,
                    left_scratch + output_at,
                    output_limb_count);
                multiply_unsigned_limbs(
                    left_scratch + output_at,
                    output_limb_count,
                    incidence_limbs + right_at * incidence_limb_count,
                    incidence_limb_count,
                    right_scratch + output_at,
                    output_limb_count);
                multiply_unsigned_limbs(
                    right_scratch + output_at,
                    output_limb_count,
                    form_entry_limbs + entry * coefficient_limb_count,
                    coefficient_limb_count,
                    term_scratch + output_at,
                    output_limb_count);
                const uint8_t sign = product_sign(
                    product_sign(incidence_signs[left_at], constitutive_signs[constitutive_at]),
                    product_sign(incidence_signs[right_at], form_entry_signs[entry]));
                add_widened_signed_magnitude(
                    output_signs + form,
                    output_limbs + output_at,
                    output_limb_count,
                    sign,
                    term_scratch + output_at,
                    output_limb_count,
                    obstruction);
            }
        }
    }
}

extern "C" __global__ void project_membrane_factored_moment_candidate_functionals(
    const uint8_t *incidence_signs,
    const uint32_t *incidence_limbs,
    const uint32_t *admitted,
    const uint64_t *functional_offsets,
    const uint32_t *functional_factors,
    const uint8_t *functional_signs,
    const uint32_t *functional_limbs,
    uint8_t *projected_signs,
    uint32_t *projected_limbs,
    uint32_t *product_scratch,
    uint32_t functional_count,
    uint32_t factor_count,
    uint32_t incidence_limb_count,
    uint32_t functional_limb_count,
    uint32_t projected_rank,
    uint32_t projected_limb_count,
    uint32_t functional_base,
    uint32_t *obstruction)
{
    const uint64_t projection =
        (uint64_t)blockIdx.x * (uint64_t)blockDim.x + threadIdx.x;
    const uint64_t projection_count =
        (uint64_t)functional_count * (uint64_t)projected_rank;
    if (projection >= projection_count) return;
    const uint32_t local_functional = (uint32_t)(projection / projected_rank);
    const uint32_t functional = functional_base + local_functional;
    const uint32_t row = (uint32_t)(projection % projected_rank);
    projected_signs[projection] = 0U;
    zero_unsigned_limbs(
        projected_limbs + projection * projected_limb_count,
        projected_limb_count);
    if (*admitted != 1U || *obstruction != 0U) return;
    if (projected_rank == 0U) {
        atomicExch(obstruction, 1U);
        return;
    }
    const uint64_t begin = functional_offsets[functional];
    const uint64_t end = functional_offsets[(uint64_t)functional + 1ULL];
    for (uint64_t entry = begin; entry < end; ++entry) {
        const uint32_t factor = functional_factors[entry];
        if (factor >= factor_count) {
            atomicExch(obstruction, 1U);
            return;
        }
        const uint64_t incidence_at = (uint64_t)row * factor_count + factor;
        if (incidence_signs[incidence_at] == 0U || functional_signs[entry] == 0U) continue;
        multiply_unsigned_limbs(
            incidence_limbs + incidence_at * incidence_limb_count,
            incidence_limb_count,
            functional_limbs + entry * functional_limb_count,
            functional_limb_count,
            product_scratch + projection * projected_limb_count,
            projected_limb_count);
        add_widened_signed_magnitude(
            projected_signs + projection,
            projected_limbs + projection * projected_limb_count,
            projected_limb_count,
            product_sign(incidence_signs[incidence_at], functional_signs[entry]),
            product_scratch + projection * projected_limb_count,
            projected_limb_count,
            obstruction);
    }
}

extern "C" __global__ void measure_membrane_factored_moment_candidate_constitutive_aperture(
    const uint32_t *constitutive_limbs,
    const uint32_t *admitted,
    uint32_t constitutive_limb_capacity,
    uint32_t constitutive_rank,
    uint32_t *active_limb_count,
    uint32_t *obstruction)
{
    const uint32_t entry = blockIdx.x * blockDim.x + threadIdx.x;
    if (*admitted != 1U || *obstruction != 0U) return;
    if (constitutive_rank == 0U || constitutive_limb_capacity == 0U) {
        atomicExch(obstruction, 1U);
        return;
    }
    if (entry >= constitutive_rank * constitutive_rank) return;
    const uint32_t *value = constitutive_limbs
        + (uint64_t)entry * constitutive_limb_capacity;
    uint32_t used = constitutive_limb_capacity;
    while (used > 0U && value[used - 1U] == 0U) --used;
    atomicMax(active_limb_count, used == 0U ? 1U : used);
}

extern "C" __global__ void dualize_membrane_factored_moment_candidate_functionals(
    const uint8_t *projected_signs,
    const uint32_t *projected_limbs,
    const uint8_t *constitutive_signs,
    const uint32_t *constitutive_limbs,
    const uint32_t *admitted,
    uint8_t *dual_signs,
    uint32_t *dual_limbs,
    uint32_t *product_scratch,
    uint32_t functional_count,
    uint32_t projected_limb_count,
    uint32_t constitutive_limb_capacity,
    uint32_t constitutive_active_limb_count,
    uint32_t source_rank,
    uint32_t generator_count,
    uint32_t projected_rank,
    uint32_t dual_limb_count,
    uint32_t functional_base,
    uint32_t *obstruction)
{
    const uint64_t occurrence =
        (uint64_t)blockIdx.x * (uint64_t)blockDim.x + threadIdx.x;
    const uint64_t occurrence_count =
        (uint64_t)functional_count * (uint64_t)projected_rank;
    if (occurrence >= occurrence_count) return;
    const uint32_t local_functional = (uint32_t)(occurrence / projected_rank);
    const uint32_t functional = functional_base + local_functional;
    const uint32_t left = (uint32_t)(occurrence % projected_rank);
    dual_signs[occurrence] = 0U;
    zero_unsigned_limbs(dual_limbs + occurrence * dual_limb_count, dual_limb_count);
    if (*admitted != 1U || *obstruction != 0U) return;
    if (source_rank == 0U || generator_count == 0U
        || projected_rank != source_rank * generator_count) {
        atomicExch(obstruction, 1U);
        return;
    }
    const uint32_t generator = left / source_rank;
    const uint32_t source_left = left % source_rank;
    for (uint32_t source_right = 0U; source_right < source_rank; ++source_right) {
        const uint32_t right = generator * source_rank + source_right;
        const uint64_t projected_at = (uint64_t)functional * projected_rank + right;
        const uint64_t constitutive_at =
            (uint64_t)source_left * source_rank + source_right;
        if (projected_signs[projected_at] == 0U
            || constitutive_signs[constitutive_at] == 0U) continue;
        multiply_unsigned_limbs(
            constitutive_limbs + constitutive_at * constitutive_limb_capacity,
            constitutive_active_limb_count,
            projected_limbs + projected_at * projected_limb_count,
            projected_limb_count,
            product_scratch + occurrence * dual_limb_count,
            dual_limb_count);
        add_widened_signed_magnitude(
            dual_signs + occurrence,
            dual_limbs + occurrence * dual_limb_count,
            dual_limb_count,
            product_sign(constitutive_signs[constitutive_at], projected_signs[projected_at]),
            product_scratch + occurrence * dual_limb_count,
            dual_limb_count,
            obstruction);
    }
}

extern "C" __global__ void contract_membrane_factored_moment_candidate_functional_pairs(
    const uint8_t *projected_signs,
    const uint32_t *projected_limbs,
    const uint8_t *dual_signs,
    const uint32_t *dual_limbs,
    const uint32_t *admitted,
    const uint32_t *pair_left_functionals,
    const uint32_t *pair_right_functionals,
    uint8_t *pair_output_signs,
    uint32_t *pair_output_limbs,
    uint32_t *pair_scratch,
    uint32_t *weighted_pair_scratch,
    const uint32_t *history_weight_limbs,
    uint32_t pair_count,
    uint32_t functional_count,
    uint32_t projected_limb_count,
    uint32_t dual_limb_count,
    uint32_t projected_rank,
    uint32_t root_rank,
    uint32_t history_weight_limb_count,
    uint32_t pair_limb_count,
    uint32_t functional_base,
    uint32_t dual_functional_count,
    uint32_t *obstruction)
{
    const uint32_t pair = blockIdx.x * blockDim.x + threadIdx.x;
    if (pair >= pair_count) return;
    if (*admitted != 1U || *obstruction != 0U) return;
    if (projected_rank == 0U || root_rank == 0U
        || history_weight_limb_count == 0U || projected_rank % root_rank != 0U) {
        atomicExch(obstruction, 1U);
        return;
    }
    const uint32_t global_left_functional = pair_left_functionals[pair];
    const uint32_t global_right_functional = pair_right_functionals[pair];
    if (global_left_functional >= functional_count
        || global_right_functional >= functional_count) {
        atomicExch(obstruction, 1U);
        return;
    }
    if (global_right_functional < functional_base
        || global_right_functional - functional_base >= dual_functional_count) {
        return;
    }
    const uint32_t left_functional = global_left_functional;
    const uint32_t right_functional = global_right_functional - functional_base;
    const uint64_t output_at = (uint64_t)pair * pair_limb_count;
    for (uint32_t left = 0U; left < projected_rank; ++left) {
        const uint64_t left_at = (uint64_t)left_functional * projected_rank + left;
        const uint64_t right_at = (uint64_t)right_functional * projected_rank + left;
        if (projected_signs[left_at] == 0U
            || dual_signs[right_at] == 0U) continue;
        multiply_unsigned_limbs(
            projected_limbs + left_at * projected_limb_count,
            projected_limb_count,
            dual_limbs + right_at * dual_limb_count,
            dual_limb_count,
            pair_scratch + output_at,
            pair_limb_count);
        const uint32_t history = left / root_rank;
        multiply_unsigned_limbs(
            pair_scratch + output_at,
            pair_limb_count,
            history_weight_limbs
                + (uint64_t)history * (uint64_t)history_weight_limb_count,
            history_weight_limb_count,
            weighted_pair_scratch + output_at,
            pair_limb_count);
        add_widened_signed_magnitude(
            pair_output_signs + pair,
            pair_output_limbs + output_at,
            pair_limb_count,
            product_sign(projected_signs[left_at], dual_signs[right_at]),
            weighted_pair_scratch + output_at,
            pair_limb_count,
            obstruction);
    }
}

extern "C" __global__ void scale_membrane_factored_moment_candidate_receiver_factors(
    const uint8_t *pair_signs,
    const uint32_t *pair_limbs,
    const uint32_t *admitted,
    const uint32_t *factor_pair_coordinates,
    const uint8_t *factor_signs,
    const uint32_t *factor_limbs,
    uint8_t *output_signs,
    uint32_t *output_limbs,
    uint32_t *product_scratch,
    uint32_t factor_count,
    uint32_t pair_count,
    uint32_t pair_limb_count,
    uint32_t factor_limb_count,
    uint32_t output_limb_count,
    uint64_t factor_base,
    uint32_t *obstruction)
{
    const uint32_t factor = blockIdx.x * blockDim.x + threadIdx.x;
    if (factor >= factor_count) return;
    const uint64_t output_at = (uint64_t)factor * output_limb_count;
    output_signs[factor] = 0U;
    zero_unsigned_limbs(output_limbs + output_at, output_limb_count);
    if (*admitted != 1U || *obstruction != 0U) return;
    const uint64_t global_factor = factor_base + factor;
    const uint32_t pair = factor_pair_coordinates[global_factor];
    if (pair >= pair_count) {
        atomicExch(obstruction, 1U);
        return;
    }
    if (pair_signs[pair] == 0U || factor_signs[global_factor] == 0U) return;
    multiply_unsigned_limbs(
        pair_limbs + (uint64_t)pair * pair_limb_count,
        pair_limb_count,
        factor_limbs + global_factor * factor_limb_count,
        factor_limb_count,
        product_scratch + output_at,
        output_limb_count);
    output_signs[factor] = product_sign(pair_signs[pair], factor_signs[global_factor]);
    for (uint32_t limb = 0U; limb < output_limb_count; ++limb) {
        output_limbs[output_at + limb] = product_scratch[output_at + limb];
    }
}

extern "C" __global__ void reduce_membrane_factored_moment_candidate_functional_receivers(
    const uint64_t *receiver_term_offsets,
    const uint8_t *term_output_signs,
    const uint32_t *term_output_limbs,
    uint8_t *receiver_output_signs,
    uint32_t *receiver_output_limbs,
    uint32_t receiver_count,
    uint32_t term_count,
    uint32_t output_limb_count,
    uint32_t receiver_base,
    uint64_t term_base,
    uint32_t *obstruction)
{
    const uint32_t receiver = blockIdx.x * blockDim.x + threadIdx.x;
    if (receiver >= receiver_count) return;
    const uint32_t global_receiver = receiver_base + receiver;
    const uint64_t output_at = (uint64_t)global_receiver * output_limb_count;
    if (*obstruction != 0U) return;
    const uint64_t global_begin = receiver_term_offsets[global_receiver];
    const uint64_t global_end = receiver_term_offsets[(uint64_t)global_receiver + 1ULL];
    if (global_begin < term_base || global_end < global_begin
        || global_end - term_base > term_count) {
        atomicExch(obstruction, 1U);
        return;
    }
    const uint64_t begin = global_begin - term_base;
    const uint64_t end = global_end - term_base;
    for (uint64_t term = begin; term < end; ++term) {
        add_widened_signed_magnitude(
            receiver_output_signs + global_receiver,
            receiver_output_limbs + output_at,
            output_limb_count,
            term_output_signs[term],
            term_output_limbs + term * output_limb_count,
            output_limb_count,
            obstruction);
    }
}

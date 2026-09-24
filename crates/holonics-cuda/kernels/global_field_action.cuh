// Matrix-free global operative action.  D remains contact-major and resident; no D D* matrix is
// formed.  Richardson uses omega=2^-omega_bits and certifies the final solve by the actual
// residual ||rhs-A v||, with A=I+D D*.
__device__ wide global_action_grid(HistoryInteger value, uint32_t grain, wide *rounds, uint32_t *slot) {
    return history_narrow(complete_divide(value, complete_power(grain, slot), rounds, slot), slot);
}

__device__ wide global_action_relax_grid(
    HistoryInteger value, uint32_t omega_bits, wide *rounds, uint32_t *slot
) {
    return history_narrow(
        complete_divide(value, complete_power(omega_bits, slot), rounds, slot), slot
    );
}

__device__ HistoryInteger global_action_abs(wide value) {
    HistoryInteger result = history_integer(value);
    if (result.negative) result = -result;
    return result;
}

// Admit Richardson only when the declared omega dominates a resident Frobenius bound on D.
// The Frobenius norm is an upper bound on the operator norm, so this is conservative and exact.
__device__ void global_action_validate_omega(
    const wide *D, uint32_t d, uint32_t count, uint32_t grain, uint32_t omega_bits, uint32_t *slot
) {
    if (!threadIdx.x) {
        HistoryInteger total;
        HistoryInteger max_row;
        HistoryInteger max_col;
        for (uint32_t row = 0; row < count; ++row) {
            HistoryInteger sum;
            for (uint32_t port = 0; port < d; port += 2u) {
                sum = sum + global_action_abs(D[(size_t)row * d + port])
                    + global_action_abs(D[(size_t)row * d + port + 1u]);
                total = total
                    + history_integer(D[(size_t)row * d + port])
                        * history_integer(D[(size_t)row * d + port])
                    + history_integer(D[(size_t)row * d + port + 1u])
                        * history_integer(D[(size_t)row * d + port + 1u]);
            }
            if (!(sum <= max_row)) max_row = sum;
        }
        for (uint32_t port = 0; port < d; port += 2u) {
            HistoryInteger sum;
            for (uint32_t row = 0; row < count; ++row)
                sum = sum + global_action_abs(D[(size_t)row * d + port])
                    + global_action_abs(D[(size_t)row * d + port + 1u]);
            if (!(sum <= max_col)) max_col = sum;
        }
        HistoryInteger one_inf = max_row * max_col;
        if (one_inf <= total) total = one_inf;
        HistoryInteger unit = complete_power(2u * grain, slot);
        HistoryInteger limit = complete_power(omega_bits, slot) * unit - unit;
        if (!(total <= limit)) atomicOr(slot, REFUSED_MALFORMED);
    }
    __syncthreads();
}

__device__ uint32_t global_action_select_omega(
    const wide *D, uint32_t d, uint32_t count, uint32_t grain, uint32_t requested, uint32_t *slot
) {
    __shared__ uint32_t selected;
    if (!threadIdx.x) {
        selected = requested;
        if (requested == UINT32_MAX) {
            HistoryInteger frobenius;
            HistoryInteger max_row;
            HistoryInteger max_col;
            for (uint32_t row = 0; row < count; ++row) {
                HistoryInteger sum;
                for (uint32_t port = 0; port < d; port += 2u) {
                    sum = sum + global_action_abs(D[(size_t)row * d + port])
                        + global_action_abs(D[(size_t)row * d + port + 1u]);
                    frobenius = frobenius
                        + history_integer(D[(size_t)row * d + port])
                            * history_integer(D[(size_t)row * d + port])
                        + history_integer(D[(size_t)row * d + port + 1u])
                            * history_integer(D[(size_t)row * d + port + 1u]);
                }
                if (!(sum <= max_row)) max_row = sum;
            }
            for (uint32_t port = 0; port < d; port += 2u) {
                HistoryInteger sum;
                for (uint32_t row = 0; row < count; ++row)
                    sum = sum + global_action_abs(D[(size_t)row * d + port])
                        + global_action_abs(D[(size_t)row * d + port + 1u]);
                if (!(sum <= max_col)) max_col = sum;
            }
            HistoryInteger total = frobenius;
            HistoryInteger one_inf = max_row * max_col;
            if (one_inf <= total) total = one_inf;
            HistoryInteger unit = complete_power(2u * grain, slot);
            selected = 120;
            for (uint32_t bits = 0; bits <= 120; ++bits) {
                HistoryInteger limit = complete_power(bits, slot) * unit - unit;
                if (total <= limit) {
                    selected = bits;
                    break;
                }
            }
        }
    }
    __syncthreads();
    return selected;
}

__device__ void global_action_d_times_b(
    const wide *D, const wide *b, uint32_t d, uint32_t count, uint32_t grain, wide *out,
    wide *rounds, uint32_t *slot
) {
    for (uint32_t port = threadIdx.x; port < d / 2u; port += blockDim.x) {
        HistoryInteger re, im;
        wide omitted = 0;
        for (uint32_t row = 0; row < count; ++row) {
            wide dr = D[(size_t)row * d + 2u * port];
            wide di = D[(size_t)row * d + 2u * port + 1u];
            if (dr == 0 && di == 0) continue;
            history_complex_add_product(
                re,
                im,
                dr,
                di,
                b[2u * row],
                b[2u * row + 1u],
                false
            );
        }
        out[2u * port] = global_action_grid(re, grain, &omitted, slot);
        out[2u * port + 1u] = global_action_grid(im, grain, &omitted, slot);
        rounds[port] = omitted;
    }
}

__device__ void global_action_d_star_times_v(
    const wide *D, const wide *v, uint32_t d, uint32_t count, uint32_t grain, wide *out,
    wide *rounds, uint32_t *slot
) {
    for (uint32_t row = threadIdx.x; row < count; row += blockDim.x) {
        HistoryInteger re, im;
        wide omitted = 0;
        for (uint32_t port = 0; port < d; port += 2u) {
            wide dr = D[(size_t)row * d + port];
            wide di = D[(size_t)row * d + port + 1u];
            if (dr == 0 && di == 0) continue;
            history_complex_add_product(
                re,
                im,
                dr,
                di,
                v[port],
                v[port + 1u],
                true
            );
        }
        out[2u * row] = global_action_grid(re, grain, &omitted, slot);
        out[2u * row + 1u] = global_action_grid(im, grain, &omitted, slot);
        rounds[row] = omitted;
    }
}

extern "C" __global__ __launch_bounds__(512) void section_field_global_action(
    const int64_t *map,
    const int64_t *map_hi,
    const int64_t *bounds,
    const int64_t *bounds_hi,
    const int64_t *input,
    const int64_t *input_hi,
    uint32_t input_at,
    uint32_t d,
    uint32_t count,
    uint32_t grain,
    uint32_t steps,
    uint32_t omega_bits,
    int64_t *work_wire,
    int64_t *out,
    int64_t *out_hi,
    int64_t *residual,
    int64_t *residual_hi,
    uint32_t *slot,
    const uint32_t *census,
    const uint32_t *lineage,
    uint32_t lineage_count
) {
    if (blockIdx.x || upstream_refused(census, lineage, lineage_count, slot)) return;
    const uint32_t k = count;
    const uint32_t width = d + 2u * k;
    if (!d || (d & 1u) || grain == 0u || grain > 120u
        || (omega_bits > 120u && omega_bits != UINT32_MAX) || !steps
        || input_at & 1u) {
        if (!threadIdx.x) atomicOr(slot, REFUSED_MALFORMED);
        return;
    }
    if (!threadIdx.x) {
        if (((const wide *)(bounds))[0] < 0 || ((const wide *)(bounds))[1] < 0
            || ((const wide *)(input + input_at))[width] < 0) {
            atomicOr(slot, REFUSED_MALFORMED);
        }
        for (size_t i = 0; i < 2u * (size_t)d * k; ++i)
            if (map[i] != map_hi[i]) atomicOr(slot, REFUSED_MALFORMED);
        for (size_t i = 0; i < 4u; ++i)
            if (bounds[i] != bounds_hi[i]) atomicOr(slot, REFUSED_MALFORMED);
        for (size_t i = 0; i < 2u * ((size_t)width + 1u); ++i)
            if (input[input_at + i] != input_hi[input_at + i]) atomicOr(slot, REFUSED_MALFORMED);
    }
    __syncthreads();
    if (*slot) return;

    const wide *D = (const wide *)map;
    const wide *x = (const wide *)(input + input_at);
    wide *work = (wide *)work_wire;
    wide *rhs = work;
    wide *v = rhs + d;
    wide *av = v + d;
    wide *dual = av + d;
    wide *res = dual + 2u * k;
    wide *rounds = res + d;
    wide *total_rounding = rounds + d + 2u * k;
    uint32_t selected_omega = global_action_select_omega(D, d, k, grain, omega_bits, slot);
    global_action_validate_omega(D, d, k, grain, selected_omega, slot);
    if (*slot) return;
    if (!threadIdx.x) *total_rounding = 0;
    for (uint32_t i = threadIdx.x; i < d + 2u * k; i += blockDim.x) rounds[i] = 0;
    __syncthreads();
    for (uint32_t i = threadIdx.x; i < d; i += blockDim.x) v[i] = 0;
    __syncthreads();

    global_action_d_times_b(D, x + d, d, k, grain, rhs, rounds, slot);
    __syncthreads();
    if (*slot) return;
    if (!threadIdx.x)
        for (uint32_t i = 0; i < d / 2u; ++i)
            *total_rounding = add_checked(*total_rounding, rounds[i], slot);
    __syncthreads();
    if (*slot) return;
    for (uint32_t i = threadIdx.x; i < d; i += blockDim.x)
        rhs[i] = product_checked(2, add_checked(x[i], rhs[i], slot), slot);
    __syncthreads();
    if (*slot) return;

    for (uint32_t step = 0; step < steps; ++step) {
        global_action_d_star_times_v(D, v, d, k, grain, dual, rounds, slot);
        __syncthreads();
        if (*slot) return;
        if (!threadIdx.x)
            for (uint32_t i = 0; i < k; ++i)
                *total_rounding = add_checked(*total_rounding, rounds[i], slot);
        __syncthreads();
        if (*slot) return;
        global_action_d_times_b(D, dual, d, k, grain, av, rounds, slot);
        __syncthreads();
        if (*slot) return;
        if (!threadIdx.x)
            for (uint32_t i = 0; i < d / 2u; ++i)
                *total_rounding = add_checked(*total_rounding, rounds[i], slot);
        __syncthreads();
        if (*slot) return;
        for (uint32_t i = threadIdx.x; i < d; i += blockDim.x) {
            HistoryInteger difference = history_integer(sub_checked(rhs[i], add_checked(v[i], av[i], slot), slot));
            wide omitted = 0;
            v[i] = add_checked(v[i], global_action_relax_grid(difference, selected_omega, &omitted, slot), slot);
            rounds[i] = omitted;
        }
        __syncthreads();
        if (*slot) return;
        if (!threadIdx.x)
            for (uint32_t i = 0; i < d; ++i)
                *total_rounding = add_checked(*total_rounding, rounds[i], slot);
        __syncthreads();
        if (*slot) return;
    }

    global_action_d_star_times_v(D, v, d, k, grain, dual, rounds, slot);
    __syncthreads();
    if (*slot) return;
    if (!threadIdx.x)
        for (uint32_t i = 0; i < k; ++i)
            *total_rounding = add_checked(*total_rounding, rounds[i], slot);
    __syncthreads();
    if (*slot) return;
    global_action_d_times_b(D, dual, d, k, grain, av, rounds, slot);
    __syncthreads();
    if (*slot) return;
    if (!threadIdx.x)
        for (uint32_t i = 0; i < d / 2u; ++i)
            *total_rounding = add_checked(*total_rounding, rounds[i], slot);
    __syncthreads();
    if (*slot) return;
    for (uint32_t i = threadIdx.x; i < d; i += blockDim.x)
        res[i] = sub_checked(rhs[i], add_checked(v[i], av[i], slot), slot);
    for (uint32_t i = threadIdx.x; i < d; i += blockDim.x)
        ((wide *)out)[i] = sub_checked(v[i], x[i], slot);
    for (uint32_t i = threadIdx.x; i < 2u * k; i += blockDim.x)
        ((wide *)out)[d + i] = sub_checked(dual[i], x[d + i], slot);
    __syncthreads();
    if (*slot) return;

    if (!threadIdx.x) {
        wide residual_norm = complete_norm(res, d, slot);
        wide input_norm = complete_norm(x, width, slot);
        wide map_error = ((const wide *)bounds)[0];
        wide rounding = *total_rounding;
        wide d_norm = history_norm_ceiling((complete_power(selected_omega, slot)-history_integer(1))*complete_power(2u*grain,slot),slot);
        wide scale = (wide)((uwide)1u << grain);
        wide round_solve = ft_ceil_product(
            add_checked(product_checked(2, scale, slot), d_norm, slot),
            rounding,
            grain,
            slot
        );
        wide solve_error = add_checked(residual_norm, round_solve, slot);
        wide joint_error = ft_ceil_product(add_checked(scale, d_norm, slot), solve_error, grain, slot);
        joint_error = add_checked(
            joint_error,
            ft_ceil_product(d_norm, rounding, grain, slot),
            slot
        );
        wide error = add_checked(
            joint_error,
            add_checked(
                ft_ceil_product(product_checked(2, map_error, slot), input_norm, grain, slot),
                0,
                slot
            ),
            slot
        );
        ((wide *)out)[width] = add_checked(x[width], error, slot);
        for (uint32_t i = 0; i < d; ++i) ((wide *)residual)[i] = res[i];
        ((wide *)residual)[d] = add_checked(residual_norm, rounding, slot);
    }
    __syncthreads();
    if (*slot) return;
    for (size_t i = threadIdx.x; i < 2u * ((size_t)width + 1u); i += blockDim.x)
        out_hi[i] = out[i];
    for (size_t i = threadIdx.x; i < 2u * ((size_t)d + 1u); i += blockDim.x)
        residual_hi[i] = residual[i];
}

// Pull back an arbitrary full joint covector.  The two rank-two factors are returned separately:
// G_D = lambda (b-b_ref)* + v (g_b-D*lambda)*.  No boundary-only target or host-side summation is
// used, so an internal b covector survives the producing return.
extern "C" __global__ __launch_bounds__(512) void section_field_global_pullback(
    const int64_t *map,
    const int64_t *map_hi,
    const int64_t *bounds,
    const int64_t *bounds_hi,
    const int64_t *input,
    const int64_t *input_hi,
    uint32_t input_at,
    const int64_t *output,
    const int64_t *output_hi,
    uint32_t output_at,
    const int64_t *covector,
    const int64_t *covector_hi,
    uint32_t covector_at,
    uint32_t d,
    uint32_t count,
    uint32_t grain,
    uint32_t steps,
    uint32_t omega_bits,
    int64_t *work_wire,
    int64_t *incoming_lo,
    int64_t *incoming_hi,
    int64_t *ports_lo,
    int64_t *ports_hi,
    int64_t *currents_lo,
    int64_t *currents_hi,
    int64_t *delta_bounds,
    int64_t *delta_bounds_hi,
    int64_t *residual,
    int64_t *residual_hi,
    uint32_t *slot,
    const uint32_t *census,
    const uint32_t *lineage,
    uint32_t lineage_count
) {
    if (blockIdx.x || upstream_refused(census, lineage, lineage_count, slot)) return;
    const uint32_t width = d + 2u * count;
    if (!d || (d & 1u) || grain == 0u || grain > 120u
        || (omega_bits > 120u && omega_bits != UINT32_MAX) || !steps
        || input_at & 1u || output_at & 1u || covector_at & 1u) {
        if (!threadIdx.x) atomicOr(slot, REFUSED_MALFORMED);
        return;
    }
    if (!threadIdx.x) {
        if (((const wide *)(bounds))[0] < 0 || ((const wide *)(bounds))[1] < 0
            || ((const wide *)(input + input_at))[width] < 0
            || ((const wide *)(output + output_at))[width] < 0
            || ((const wide *)(covector + covector_at))[width] < 0) {
            atomicOr(slot, REFUSED_MALFORMED);
        }
        for (size_t i = 0; i < 2u * (size_t)d * count; ++i)
            if (map[i] != map_hi[i]) atomicOr(slot, REFUSED_MALFORMED);
        for (size_t i = 0; i < 4u; ++i)
            if (bounds[i] != bounds_hi[i]) atomicOr(slot, REFUSED_MALFORMED);
        for (size_t i = 0; i < 2u * ((size_t)width + 1u); ++i) {
            if (input[input_at + i] != input_hi[input_at + i]
                || output[output_at + i] != output_hi[output_at + i]
                || covector[covector_at + i] != covector_hi[covector_at + i])
                atomicOr(slot, REFUSED_MALFORMED);
        }
    }
    __syncthreads();
    if (*slot) return;
    const wide *D = (const wide *)map;
    const wide *x = (const wide *)(input + input_at);
    const wide *y = (const wide *)(output + output_at);
    const wide *g = (const wide *)(covector + covector_at);
    wide *work = (wide *)work_wire;
    wide *rhs = work;
    wide *lambda = rhs + d;
    wide *dual = lambda + d;
    wide *adual = dual + 2u * count;
    wide *res = adual + d;
    wide *rounds = res + d;
    wide *total_rounding = rounds + d + 2u * count;
    uint32_t selected_omega = global_action_select_omega(D, d, count, grain, omega_bits, slot);
    global_action_validate_omega(D, d, count, grain, selected_omega, slot);
    if (*slot) return;
    if (!threadIdx.x) *total_rounding = 0;
    for (uint32_t i = threadIdx.x; i < d + 2u * count; i += blockDim.x) rounds[i] = 0;
    for (uint32_t i = threadIdx.x; i < d; i += blockDim.x) lambda[i] = 0;
    __syncthreads();

    global_action_d_times_b(D, g + d, d, count, grain, rhs, rounds, slot);
    __syncthreads();
    if (*slot) return;
    if (!threadIdx.x)
        for (uint32_t i = 0; i < d / 2u; ++i)
            *total_rounding = add_checked(*total_rounding, rounds[i], slot);
    __syncthreads();
    if (*slot) return;
    for (uint32_t i = threadIdx.x; i < d; i += blockDim.x)
        rhs[i] = add_checked(g[i], rhs[i], slot);
    __syncthreads();
    if (*slot) return;

    for (uint32_t step = 0; step < steps; ++step) {
        global_action_d_star_times_v(D, lambda, d, count, grain, dual, rounds, slot);
        __syncthreads();
        if (*slot) return;
        if (!threadIdx.x)
            for (uint32_t i = 0; i < count; ++i)
                *total_rounding = add_checked(*total_rounding, rounds[i], slot);
        __syncthreads();
        if (*slot) return;
        global_action_d_times_b(D, dual, d, count, grain, adual, rounds, slot);
        __syncthreads();
        if (*slot) return;
        if (!threadIdx.x)
            for (uint32_t i = 0; i < d / 2u; ++i)
                *total_rounding = add_checked(*total_rounding, rounds[i], slot);
        __syncthreads();
        if (*slot) return;
        for (uint32_t i = threadIdx.x; i < d; i += blockDim.x) {
            HistoryInteger difference = history_integer(sub_checked(rhs[i], add_checked(lambda[i], adual[i], slot), slot));
            wide omitted = 0;
            lambda[i] = add_checked(lambda[i], global_action_relax_grid(difference, selected_omega, &omitted, slot), slot);
            rounds[i] = omitted;
        }
        __syncthreads();
        if (*slot) return;
        if (!threadIdx.x)
            for (uint32_t i = 0; i < d; ++i)
                *total_rounding = add_checked(*total_rounding, rounds[i], slot);
        __syncthreads();
        if (*slot) return;
    }

    global_action_d_star_times_v(D, lambda, d, count, grain, dual, rounds, slot);
    __syncthreads();
    if (*slot) return;
    if (!threadIdx.x)
        for (uint32_t i = 0; i < count; ++i)
            *total_rounding = add_checked(*total_rounding, rounds[i], slot);
    __syncthreads();
    if (*slot) return;
    global_action_d_times_b(D, dual, d, count, grain, adual, rounds, slot);
    __syncthreads();
    if (*slot) return;
    if (!threadIdx.x)
        for (uint32_t i = 0; i < d / 2u; ++i)
            *total_rounding = add_checked(*total_rounding, rounds[i], slot);
    __syncthreads();
    if (*slot) return;
    for (uint32_t i = threadIdx.x; i < d; i += blockDim.x)
        res[i] = sub_checked(rhs[i], add_checked(lambda[i], adual[i], slot), slot);
    __syncthreads();
    if (*slot) return;

    for (uint32_t i = threadIdx.x; i < d; i += blockDim.x) {
        wide v = add_checked(x[i], y[i], slot);
        ((wide *)incoming_lo)[i] = sub_checked(product_checked(2, lambda[i], slot), g[i], slot);
        ((wide *)ports_lo)[i] = lambda[i];
        ((wide *)ports_lo)[d + i] = v;
    }
    for (uint32_t i = threadIdx.x; i < 2u * count; i += blockDim.x) {
        wide first = sub_checked(x[d + i], y[d + i], slot);
        wide factor_second = sub_checked(g[d + i], dual[i], slot);
        wide incoming_second = sub_checked(product_checked(2, dual[i], slot), g[d + i], slot);
        ((wide *)incoming_lo)[d + i] = incoming_second;
        ((wide *)currents_lo)[i] = first;
        ((wide *)currents_lo)[2u * count + i] = factor_second;
    }
    __syncthreads();
    if (*slot) return;
    if (!threadIdx.x) {
        wide residual_norm = complete_norm(res, d, slot);
        wide input_norm = complete_norm(x, width, slot);
        wide covector_norm = complete_norm(g, width, slot);
        wide map_error = ((const wide *)bounds)[0];
        wide d_norm = history_norm_ceiling((complete_power(selected_omega, slot)-history_integer(1))*complete_power(2u*grain,slot),slot);
        wide scale = (wide)((uwide)1u << grain);
        wide rounding = *total_rounding;
        wide round_solve = ft_ceil_product(
            add_checked(product_checked(2, scale, slot), d_norm, slot),
            rounding,
            grain,
            slot
        );
        wide solve_error = add_checked(residual_norm, round_solve, slot);
        wide lambda_norm = complete_norm(lambda, d, slot);
        wide current_radius = x[width], output_radius = y[width], covector_radius = g[width];
        wide actual_d_bound = add_checked(d_norm, map_error, slot);
        // ||A_actual^-1|| <= 1. Bound the residual of this same lambda against actual D,g.
        wide delta_a = ft_ceil_product(add_checked(product_checked(2, d_norm, slot), map_error, slot), map_error, grain, slot);
        wide lambda_error = add_checked(solve_error,
            add_checked(ft_ceil_product(map_error, covector_norm, grain, slot),
                add_checked(ft_ceil_product(delta_a, lambda_norm, grain, slot),
                    ft_ceil_product(add_checked(scale, actual_d_bound, slot), covector_radius, grain, slot), slot), slot), slot);
        // Both factors retain their own joint uncertainty, including the input/output ball.
        wide port_error = add_checked(lambda_error, add_checked(current_radius, output_radius, slot), slot);
        wide second_error = add_checked(covector_radius,
            add_checked(ft_ceil_product(actual_d_bound, lambda_error, grain, slot),
                add_checked(ft_ceil_product(map_error, lambda_norm, grain, slot), rounding, slot), slot), slot);
        wide current_error = add_checked(add_checked(current_radius, output_radius, slot), second_error, slot);
        wide error = add_checked(covector_radius,
            add_checked(ft_ceil_product(product_checked(2, add_checked(scale, actual_d_bound, slot), slot), lambda_error, grain, slot),
                add_checked(ft_ceil_product(product_checked(2, map_error, slot), lambda_norm, grain, slot),
                    product_checked(2, rounding, slot), slot), slot), slot);
        ((wide *)incoming_lo)[width] = error;
        ((wide *)delta_bounds)[0] = port_error;
        ((wide *)delta_bounds)[1] = current_error;
        ((wide *)residual)[d] = add_checked(residual_norm, *total_rounding, slot);
    }
    __syncthreads();
    if (*slot) return;
    for (size_t i = threadIdx.x; i < 2u * ((size_t)width + 1u); i += blockDim.x)
        incoming_hi[i] = incoming_lo[i];
    for (size_t i = threadIdx.x; i < 4u * (size_t)d; i += blockDim.x) ports_hi[i] = ports_lo[i];
    for (size_t i = threadIdx.x; i < 8u * (size_t)count; i += blockDim.x)
        currents_hi[i] = currents_lo[i];
    for (size_t i = threadIdx.x; i < 4u; i += blockDim.x) delta_bounds_hi[i] = delta_bounds[i];
    for (size_t i = threadIdx.x; i < 2u * ((size_t)d + 1u); i += blockDim.x)
        residual_hi[i] = residual[i];
}

// Sum already-certified rank-two D factors without publishing each stage separately.  The table
// contains resident lo/hi pointers for [ports,currents,bounds] per pullback.
// Scale one factor in each outer product, preserving the common current factor. The stored
// words are signed wide coefficients at a fixed grain, not independent 64-bit coordinates.
extern "C" __global__ void section_field_global_scale_ports(
 const int64_t *ports,const int64_t *ports_hi,const int64_t *bounds,const int64_t *bounds_hi,
 uint32_t d,uint32_t step_bits,int64_t *out,int64_t *out_hi,int64_t *next_bounds,int64_t *next_bounds_hi,
 uint32_t *slot,const uint32_t *census,const uint32_t *lineage,uint32_t lineage_count){
 if(blockIdx.x||threadIdx.x||upstream_refused(census,lineage,lineage_count,slot))return;
 if(step_bits>120u){atomicOr(slot,REFUSED_MALFORMED);return;}
 for(size_t i=0;i<4u*(size_t)d;++i)if(ports[i]!=ports_hi[i])atomicOr(slot,REFUSED_MALFORMED);
 for(uint32_t i=0;i<4u;++i)if(bounds[i]!=bounds_hi[i])atomicOr(slot,REFUSED_MALFORMED);
 const wide *old=(const wide*)ports,*b=(const wide*)bounds;wide *result=(wide*)out,*nb=(wide*)next_bounds;
 if(b[0]<0||b[1]<0)atomicOr(slot,REFUSED_MALFORMED);if(*slot)return;
 wide divisor=(wide)((uwide)1u<<step_bits),rounds=0;
 for(size_t i=0;i<2u*(size_t)d;++i){result[i]=old[i]/divisor;rounds=add_checked(rounds,(wide)(old[i]%divisor!=0),slot);}
 nb[0]=add_checked(b[0]/divisor+(wide)(b[0]%divisor!=0),rounds,slot);nb[1]=b[1];
 if(*slot)return;
 for(size_t i=0;i<4u*(size_t)d;++i)out_hi[i]=out[i];
 for(uint32_t i=0;i<4u;++i)next_bounds_hi[i]=next_bounds[i];
}

extern "C" __global__ void section_field_global_residual_trace(
    const int64_t *residual,
    const int64_t *residual_hi,
    uint32_t d,
    int64_t *trace,
    int64_t *trace_hi,
    uint32_t *slot,
    const uint32_t *census,
    const uint32_t *lineage,
    uint32_t lineage_count
) {
    if (blockIdx.x || upstream_refused(census, lineage, lineage_count, slot)) return;
    if (!d || (d & 1u)) {
        if (!threadIdx.x) atomicOr(slot, REFUSED_MALFORMED);
        return;
    }
    for (size_t i = threadIdx.x; i < 2u * ((size_t)d + 1u); i += blockDim.x)
        if (residual[i] != residual_hi[i]) atomicOr(slot, REFUSED_MALFORMED);
    __syncthreads();
    if (*slot) return;
    for (size_t i = threadIdx.x; i < 18u * (size_t)d; i += blockDim.x)
        trace[i] = trace_hi[i] = 0;
    __syncthreads();
    for (uint32_t component = threadIdx.x; component < d; component += blockDim.x) {
        HistoryInteger value = history_integer(((const wide *)residual)[component]);
        history_write_integer(
            value,
            trace + 18u * component,
            trace_hi + 18u * component,
            slot
        );
    }
}

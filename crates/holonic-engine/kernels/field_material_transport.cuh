// Native current-to-material transport. The source is the immutable complete coupled outgoing
// current at the actual earlier source occurrence. All numbers below are dyadic representatives
// with certified error and retained factor data, never sealed exact coefficients.
//
// Report: six target center/radius blocks (new forward, contemporary old-source forward,
// observed, returned-against-old-forward, chronological current, contemporary difference),
// one source gain/error block, then [coefficient error, gain denominator, update rounding,
// source-dot rounding, new-dot rounding]. Every block uses packed signed-wide values.

__device__ __forceinline__ wide ft_abs(wide value, uint32_t *slot) {
    return of_magnitude(magnitude(value), 0, slot);
}

__device__ __forceinline__ wide ft_product(
    wide a, wide b, uint32_t grain, wide *rounds, uint32_t *slot
) {
    wide result = field_enclosed_product_zero(a, b, grain, slot);
    if ((magnitude(a) * magnitude(b)) & (((uwide)1 << grain) - 1u))
        *rounds = add_checked(*rounds, 1, slot);
    return result;
}

__device__ __forceinline__ void ft_complex_product(
    wide ar, wide ai, wide br, wide bi, uint32_t grain,
    wide *real, wide *imaginary, wide *rounds, uint32_t *slot
) {
    wide ac = ft_product(ar, br, grain, rounds, slot);
    wide bd = ft_product(ai, bi, grain, rounds, slot);
    wide ad = ft_product(ar, bi, grain, rounds, slot);
    wide bc = ft_product(ai, br, grain, rounds, slot);
    *real = sub_checked(ac, bd, slot);
    *imaginary = add_checked(ad, bc, slot);
}

__device__ __forceinline__ wide ft_ceil_product(wide a, wide b, uint32_t grain, uint32_t *slot) {
    if (a < 0 || b < 0) { atomicOr(slot, REFUSED_MALFORMED); return 0; }
    return product_shift(a, b, (int)grain, 1, slot);
}

__device__ __forceinline__ wide ft_prediction(
    const wide *state, const wide *delta, const wide *source, uint32_t targets, uint32_t sources,
    uint32_t grain, wide *out, uint32_t *slot
) {
    wide rounds = 0;
    for (uint32_t row = 0; row < targets; ++row) {
        wide real = 0, imaginary = 0;
        for (uint32_t column = 0; column < sources; ++column) {
            size_t at = 2u * ((size_t)row * sources + column);
            wide ar = state[at], ai = state[at + 1u];
            if (delta) { ar = add_checked(ar, delta[at], slot); ai = add_checked(ai, delta[at + 1u], slot); }
            wide pr, pi;
            ft_complex_product(ar, ai, source[2u * column], source[2u * column + 1u],
                grain, &pr, &pi, &rounds, slot);
            real = add_checked(real, pr, slot); imaginary = add_checked(imaginary, pi, slot);
        }
        out[2u * row] = real; out[2u * row + 1u] = imaginary;
    }
    return rounds;
}

__device__ __forceinline__ wide ft_prediction_error(
    wide coefficient_error, wide coefficient_l1, const wide *source, uint32_t source_real,
    wide source_error, wide rounding, uint32_t grain, uint32_t *slot
) {
    wide source_l1 = 0;
    for (uint32_t i = 0; i < source_real; ++i) source_l1 = add_checked(source_l1, ft_abs(source[i], slot), slot);
    return add_checked(rounding, add_checked(
        ft_ceil_product(coefficient_error, add_checked(source_l1, source_error, slot), grain, slot),
        ft_ceil_product(coefficient_l1, source_error, grain, slot), slot), slot);
}

__device__ __forceinline__ void field_material_transport_prepare(
    const wide *state, const wide *origin_current, const wide *origin_forward,
    const wide *current, const int64_t *incoming, uint32_t nodes, uint32_t linked, uint32_t grain,
    wide *delta_lo, wide *delta_hi, wide *report_lo, wide *report_hi, uint32_t *slot
) {
    if (!state || !current || !incoming || !delta_lo || !delta_hi || !report_lo || !report_hi
        || !nodes || grain < 1u || grain > 120u || linked > 1u
        || (linked && (!origin_current || !origin_forward))) {
        atomicOr(slot, REFUSED_MALFORMED); return;
    }
    const uint32_t sources = 3u * nodes, source_real = 6u * nodes, target_real = 2u * nodes;
    const size_t coefficients = (size_t)target_real * sources;
    const size_t target_stride = (size_t)target_real + 1u;
    const size_t gain_at = 6u * target_stride;
    const size_t extra_at = gain_at + source_real + 1u;
    const size_t report_values = extra_at + 5u;
    const size_t junction_stride = (size_t)source_real + 1u;
    const wide scale = (wide)1 << grain;
    for (size_t i = 0; i < report_values; ++i) report_lo[i] = report_hi[i] = 0;
    for (size_t i = 0; i <= coefficients; ++i) delta_lo[i] = delta_hi[i] = 0;
    wide old_l1 = 0;
    for (size_t i = 0; i < coefficients; ++i) old_l1 = add_checked(old_l1, ft_abs(state[i], slot), slot);
    wide error = state[coefficients];
    if (error < 0) { atomicOr(slot, REFUSED_MALFORMED); return; }
    wide *observed = report_lo + 2u * target_stride;
    wide observed_error = 0, observed_l1 = 0;
    for (uint32_t i = 0; i < target_real; ++i) {
        const int64_t *value = incoming + 3u * (i / 2u);
        if (value[2] <= 0) { atomicOr(slot, REFUSED_MALFORMED); return; }
        wide floor = signed_product_divide_2((wide)value[i % 2u], scale / 2, (wide)value[2], 0, slot);
        wide ceil = signed_product_divide_2((wide)value[i % 2u], scale / 2, (wide)value[2], 1, slot);
        observed[i] = value[i % 2u] < 0 ? ceil : floor;
        if (floor != ceil) observed_error = add_checked(observed_error, 1, slot);
        observed_l1 = add_checked(observed_l1, ft_abs(observed[i], slot), slot);
    }
    observed[target_real] = observed_error;
    if (*slot) return;
    if (linked) {
        const wide *source = origin_current + junction_stride;
        const wide source_error = source[source_real];
        if (source_error < 0 || origin_forward[target_real] < 0) { atomicOr(slot, REFUSED_MALFORMED); return; }
        wide *present = report_lo + target_stride;
        wide source_rounds = ft_prediction(state, nullptr, source, nodes, sources, grain, present, slot);
        wide present_error = ft_prediction_error(error, old_l1, source, source_real,
            source_error, source_rounds, grain, slot);
        present[target_real] = present_error;
        report_lo[extra_at + 3u] = source_rounds;
        wide *returned = report_lo + 3u * target_stride;
        wide *chronology = report_lo + 4u * target_stride;
        wide *difference = report_lo + 5u * target_stride;
        wide difference_l1 = 0;
        for (uint32_t i = 0; i < target_real; ++i) {
            returned[i] = sub_checked(observed[i], origin_forward[i], slot);
            chronology[i] = sub_checked(present[i], origin_forward[i], slot);
            difference[i] = sub_checked(observed[i], present[i], slot);
            difference_l1 = add_checked(difference_l1, ft_abs(difference[i], slot), slot);
        }
        returned[target_real] = add_checked(observed_error, origin_forward[target_real], slot);
        chronology[target_real] = add_checked(present_error, origin_forward[target_real], slot);
        difference[target_real] = add_checked(observed_error, present_error, slot);
        wide denominator = scale, denominator_rounds = 0;
        for (uint32_t i = 0; i < source_real; ++i) {
            wide floor = product_shift(source[i], source[i], (int)grain, 0, slot);
            wide ceil = product_shift(source[i], source[i], (int)grain, 1, slot);
            denominator = add_checked(denominator, ceil, slot);
            if (floor != ceil) denominator_rounds = add_checked(denominator_rounds, 1, slot);
        }
        if (*slot) return;
        wide *gain = report_lo + gain_at;
        wide gain_error = div_ceil(denominator_rounds, 2, slot);
        for (uint32_t i = 0; i < source_real; ++i) {
            wide value = i & 1u ? -source[i] : source[i];
            wide floor = signed_product_divide_2(value, scale / 2, denominator, 0, slot);
            wide ceil = signed_product_divide_2(value, scale / 2, denominator, 1, slot);
            gain[i] = value < 0 ? ceil : floor;
            if (floor != ceil) gain_error = add_checked(gain_error, 1, slot);
        }
        gain[source_real] = gain_error;
        wide delta_rounds = 0;
        for (uint32_t row = 0; row < nodes; ++row) for (uint32_t column = 0; column < sources; ++column) {
            size_t at = 2u * ((size_t)row * sources + column);
            ft_complex_product(difference[2u * row], difference[2u * row + 1u],
                gain[2u * column], gain[2u * column + 1u], grain,
                delta_lo + at, delta_lo + at + 1u, &delta_rounds, slot);
            add_checked(state[at], delta_lo[at], slot);
            add_checked(state[at + 1u], delta_lo[at + 1u], slot);
        }
        wide rounding = add_checked(div_ceil(source_rounds, 2, slot),
            add_checked(ft_ceil_product(difference_l1, gain_error, grain, slot), delta_rounds, slot), slot);
        // F(T,x,y) is nonexpansive in T. The complete graph-projector source variation is
        // bounded by ||x-xhat||; the L1 norms below are conservative Frobenius/Euclidean bounds.
        error = add_checked(error, add_checked(
            ft_ceil_product(add_checked(old_l1, observed_l1, slot), source_error, grain, slot),
            add_checked(div_ceil(observed_error, 2, slot), rounding, slot), slot), slot);
        report_lo[extra_at + 1u] = denominator;
        report_lo[extra_at + 2u] = rounding;
    }
    if (*slot) return;
    wide new_l1 = 0;
    for (size_t i = 0; i < coefficients; ++i)
        new_l1 = add_checked(new_l1, ft_abs(add_checked(state[i], delta_lo[i], slot), slot), slot);
    const wide *new_source = current + junction_stride;
    if (new_source[source_real] < 0) { atomicOr(slot, REFUSED_MALFORMED); return; }
    wide new_rounds = ft_prediction(state, delta_lo, new_source, nodes, sources, grain, report_lo, slot);
    report_lo[target_real] = ft_prediction_error(error, new_l1, new_source, source_real,
        new_source[source_real], new_rounds, grain, slot);
    report_lo[extra_at] = delta_lo[coefficients] = error;
    report_lo[extra_at + 4u] = new_rounds;
    if (*slot) return;
    for (size_t i = 0; i < report_values; ++i) report_hi[i] = report_lo[i];
    for (size_t i = 0; i <= coefficients; ++i) delta_hi[i] = delta_lo[i];
}

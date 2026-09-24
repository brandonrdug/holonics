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

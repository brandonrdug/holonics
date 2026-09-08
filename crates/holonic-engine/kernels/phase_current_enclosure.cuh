// Resident dyadic phase enclosures. A ball carries D realified centres followed by one
// nonnegative Euclidean radius; each value is a signed wide stored as two i64 words in both
// endpoint buffers. Centres are numerical representatives and never exact rational currents.

__device__ __forceinline__ wide phase_enclosure_read(const int64_t *wire, uint64_t at) {
    return ((const wide *)wire)[at];
}

__device__ __forceinline__ void phase_enclosure_write(
    int64_t *lo, int64_t *hi, uint64_t at, wide value
) {
    ((wide *)lo)[at] = value;
    ((wide *)hi)[at] = value;
}

__device__ __forceinline__ wide phase_enclosure_product_zero(
    wide left, wide right, uint32_t grain, uint32_t *slot
) {
    return product_shift(left, right, (int)grain,
        ((left < 0) != (right < 0)) ? 1 : 0, slot);
}

__device__ __forceinline__ wide phase_enclosure_product_with_error(
    wide left, wide right, uint32_t grain, wide *error, uint32_t *slot
) {
    wide floor_value = product_shift(left, right, (int)grain, 0, slot);
    wide ceil_value = product_shift(left, right, (int)grain, 1, slot);
    if (*slot) return 0;
    if (floor_value != ceil_value) *error = add_checked(*error, 1, slot);
    return ((left < 0) != (right < 0)) ? ceil_value : floor_value;
}

__device__ __forceinline__ bool phase_enclosure_validate_point(
    const int64_t *lo, const int64_t *hi, uint32_t at, uint32_t denominator_at,
    uint32_t disposition_at, uint32_t complex_coordinates, uint32_t raw_extent,
    wide *denominator, uint32_t *slot
) {
    if (!complex_coordinates || !raw_extent || raw_extent > complex_coordinates
        || (uint64_t)at + 2ULL * complex_coordinates > 0xffffffffULL) {
        atomicOr(slot, REFUSED_MALFORMED);
        return false;
    }
    *denominator = fibre_current_denominator(lo, hi, denominator_at, disposition_at, slot);
    if (*slot) return false;
    for (uint32_t coordinate = 0; coordinate < complex_coordinates; ++coordinate) {
        uint32_t index = at + 2U * coordinate;
        if (lo[index] != hi[index] || lo[index + 1U] != hi[index + 1U]
            || (coordinate >= raw_extent
                && (lo[index] != 0 || lo[index + 1U] != 0))) {
            atomicOr(slot, REFUSED_MALFORMED);
            return false;
        }
    }
    return true;
}

__device__ __forceinline__ bool phase_enclosure_validate_ball(
    const int64_t *lo, const int64_t *hi, uint32_t wide_at, uint32_t complex_extent,
    wide *radius, uint32_t *slot
) {
    uint64_t values = 2ULL * complex_extent + 1ULL;
    if (!complex_extent || values > 0x7fffffffULL
        || (uint64_t)wide_at + values > 0xffffffffULL / 2ULL) {
        atomicOr(slot, REFUSED_MALFORMED);
        return false;
    }
    for (uint64_t value = 0; value < values; ++value) {
        uint64_t base = 2ULL * ((uint64_t)wide_at + value);
        if (lo[base] != hi[base] || lo[base + 1ULL] != hi[base + 1ULL]) {
            atomicOr(slot, REFUSED_MALFORMED);
            return false;
        }
    }
    *radius = phase_enclosure_read(lo, (uint64_t)wide_at + 2ULL * complex_extent);
    if (*radius < 0) {
        atomicOr(slot, REFUSED_MALFORMED);
        return false;
    }
    return true;
}

extern "C" __global__ void section_phase_enclosure_lift(
    const int64_t *input_lo, const int64_t *input_hi,
    uint32_t input_at, uint32_t input_denominator_at, uint32_t input_disposition_at,
    uint32_t input_complex_coordinates, uint32_t raw_extent, uint32_t grain,
    int64_t *output_lo, int64_t *output_hi,
    uint32_t *slot, const uint32_t *census, const uint32_t *lineage, uint32_t lineage_count
) {
    if (blockIdx.x != 0 || threadIdx.x != 0) return;
    if (upstream_refused(census, lineage, lineage_count, slot)) return;
    if (grain < 1U || grain > 120U || !raw_extent
        || raw_extent > input_complex_coordinates || raw_extent > 0x3fffffffU
        || input_complex_coordinates > 0x7fffffffU) {
        atomicOr(slot, REFUSED_MALFORMED);
        return;
    }
    wide denominator;
    if (!phase_enclosure_validate_point(input_lo, input_hi, input_at,
        input_denominator_at, input_disposition_at, input_complex_coordinates,
        raw_extent, &denominator, slot)) return;
    wide radius = 0;
    uint32_t coordinates = 2U * raw_extent;
    for (uint32_t coordinate = 0; coordinate < coordinates; ++coordinate) {
        wide numerator = (wide)input_lo[input_at + coordinate];
        wide floor_value = signed_product_divide_2(
            numerator, (wide)1 << (grain - 1U), denominator, 0, slot);
        wide ceil_value = signed_product_divide_2(
            numerator, (wide)1 << (grain - 1U), denominator, 1, slot);
        if (*slot) return;
        wide centre = numerator < 0 ? ceil_value : floor_value;
        phase_enclosure_write(output_lo, output_hi, coordinate, centre);
        if (floor_value != ceil_value) radius = add_checked(radius, 1, slot);
    }
    if (*slot) return;
    phase_enclosure_write(output_lo, output_hi, coordinates, radius);
}

extern "C" __global__ void section_phase_enclosed_convolution_validate(
    const int64_t *source_lo, const int64_t *source_hi,
    uint32_t source_at, uint32_t source_denominator_at, uint32_t source_disposition_at,
    const int64_t *response_lo, const int64_t *response_hi, uint32_t response_wide_at,
    uint32_t source_complex_coordinates, uint32_t source_raw_extent,
    uint32_t response_raw_extent, uint32_t grain,
    wide *workspace, uint32_t *slot, const uint32_t *census,
    const uint32_t *lineage, uint32_t lineage_count
) {
    if (blockIdx.x != 0 || threadIdx.x != 0) return;
    if (*slot != 0 || upstream_refused(census, lineage, lineage_count, slot)) return;
    if (grain < 1U || grain > 120U || !response_raw_extent
        || source_raw_extent > 0x3fffffffU || response_raw_extent > 0x3fffffffU
        || response_raw_extent > 0x7fffffffU) {
        atomicOr(slot, REFUSED_MALFORMED);
        return;
    }
    wide source_den;
    if (!phase_enclosure_validate_point(source_lo, source_hi, source_at,
        source_denominator_at, source_disposition_at, source_complex_coordinates,
        source_raw_extent, &source_den, slot)) return;
    wide radius;
    if (!phase_enclosure_validate_ball(response_lo, response_hi, response_wide_at,
        response_raw_extent, &radius, slot)) return;
    uint64_t source_coordinates = 2ULL * source_raw_extent;
    uint64_t output_extent = (uint64_t)source_raw_extent + response_raw_extent - 1ULL;
    if (output_extent > 0x7fffffffULL || source_coordinates > 0x7fffffffULL) {
        atomicOr(slot, REFUSED_MALFORMED);
        return;
    }
    uint32_t output = (uint32_t)output_extent;
    uint32_t scalar_at = 2U * (uint32_t)source_coordinates + output;
    wide l1 = 0;
    for (uint32_t coordinate = 0; coordinate < source_coordinates; ++coordinate)
        l1 = add_checked(l1, (wide)magnitude((wide)source_lo[source_at + coordinate]), slot);
    wide h_l1 = 0;
    for (uint32_t coordinate = 0; coordinate < 2U * response_raw_extent; ++coordinate)
        h_l1 = add_checked(h_l1,
            magnitude(phase_enclosure_read(response_lo,
                (uint64_t)response_wide_at + coordinate)), slot);
    if (*slot) return;
    workspace[scalar_at] = source_den;
    workspace[scalar_at + 1U] = l1;
    workspace[scalar_at + 2U] = h_l1;
    workspace[scalar_at + 3U] = radius;
}

extern "C" __global__ void section_phase_enclosed_convolution_lift(
    const int64_t *source_lo, uint32_t source_at, uint32_t source_denominator_at,
    uint32_t source_raw_extent, uint32_t response_raw_extent, uint32_t grain, wide *workspace,
    uint32_t *slot, const uint32_t *census, const uint32_t *lineage, uint32_t lineage_count
) {
    uint64_t coordinate64 = (uint64_t)blockIdx.x * blockDim.x + threadIdx.x;
    if (coordinate64 >= 2ULL * source_raw_extent || *slot != 0) return;
    if (upstream_refused(census, lineage, lineage_count, slot)) return;
    uint32_t coordinate = (uint32_t)coordinate64;
    uint32_t output_extent = source_raw_extent + response_raw_extent - 1U;
    wide denominator = workspace[4U * source_raw_extent + output_extent];
    wide numerator = (wide)source_lo[source_at + coordinate];
    wide floor_value = signed_product_divide_2(
        numerator, (wide)1 << (grain - 1U), denominator, 0, slot);
    wide ceil_value = signed_product_divide_2(
        numerator, (wide)1 << (grain - 1U), denominator, 1, slot);
    if (*slot) return;
    workspace[coordinate] = numerator < 0 ? ceil_value : floor_value;
    workspace[2U * source_raw_extent + coordinate] = floor_value != ceil_value ? 1 : 0;
}

extern "C" __global__ void section_phase_enclosed_convolution_products(
    const int64_t *response_lo, uint32_t response_wide_at,
    uint32_t source_raw_extent, uint32_t response_raw_extent, uint32_t grain,
    wide *workspace, int64_t *output_lo, int64_t *output_hi,
    uint32_t *slot, const uint32_t *census, const uint32_t *lineage, uint32_t lineage_count
) {
    uint64_t target64 = (uint64_t)blockIdx.x * blockDim.x + threadIdx.x;
    if (target64 >= (uint64_t)source_raw_extent + response_raw_extent - 1ULL
        || *slot != 0) return;
    if (upstream_refused(census, lineage, lineage_count, slot)) return;
    uint32_t target = (uint32_t)target64;
    uint64_t output_extent64 = (uint64_t)source_raw_extent + response_raw_extent - 1ULL;
    if (output_extent64 > 0x7fffffffULL) {
        atomicOr(slot, REFUSED_MALFORMED);
        return;
    }
    uint32_t output_extent = (uint32_t)output_extent64;
    wide error = 0;
    wide real = 0;
    wide imaginary = 0;
    uint32_t first = target >= response_raw_extent ? target - response_raw_extent + 1U : 0U;
    uint32_t last = target < source_raw_extent ? target : source_raw_extent - 1U;
    for (uint32_t source = first; source <= last; ++source) {
        uint32_t response = target - source;
        wide ar = workspace[2U * source];
        wide ai = workspace[2U * source + 1U];
        wide br = phase_enclosure_read(response_lo,
            (uint64_t)response_wide_at + 2ULL * response);
        wide bi = phase_enclosure_read(response_lo,
            (uint64_t)response_wide_at + 2ULL * response + 1ULL);
        real = add_checked(real, phase_enclosure_product_with_error(ar, br, grain, &error, slot), slot);
        real = sub_checked(real, phase_enclosure_product_with_error(ai, bi, grain, &error, slot), slot);
        imaginary = add_checked(imaginary,
            phase_enclosure_product_with_error(ar, bi, grain, &error, slot), slot);
        imaginary = add_checked(imaginary,
            phase_enclosure_product_with_error(ai, br, grain, &error, slot), slot);
        if (*slot) return;
    }
    phase_enclosure_write(output_lo, output_hi, 2U * target, real);
    phase_enclosure_write(output_lo, output_hi, 2U * target + 1U, imaginary);
    workspace[4U * source_raw_extent + target] = error;
}

extern "C" __global__ void section_phase_enclosed_convolution_finish(
    wide *workspace, uint32_t source_raw_extent, uint32_t response_raw_extent,
    uint32_t grain, int64_t *output_lo, int64_t *output_hi,
    uint32_t *slot, const uint32_t *census, const uint32_t *lineage, uint32_t lineage_count
) {
    if (blockIdx.x != 0 || threadIdx.x != 0) return;
    if (*slot != 0 || upstream_refused(census, lineage, lineage_count, slot)) return;
    uint64_t output_extent64 = (uint64_t)source_raw_extent + response_raw_extent - 1ULL;
    if (output_extent64 > 0x7fffffffULL) {
        atomicOr(slot, REFUSED_MALFORMED);
        return;
    }
    uint32_t output_extent = (uint32_t)output_extent64;
    uint32_t source_coordinates = 2U * source_raw_extent;
    uint32_t scalar_at = 2U * source_coordinates + output_extent;
    wide xden = workspace[scalar_at];
    wide x_l1 = workspace[scalar_at + 1U];
    wide h_l1 = workspace[scalar_at + 2U];
    wide rho_h = workspace[scalar_at + 3U];
    wide source_error = 0;
    for (uint32_t coordinate = 0; coordinate < source_coordinates; ++coordinate)
        source_error = add_checked(source_error, workspace[source_coordinates + coordinate], slot);
    wide product_error = 0;
    for (uint32_t target = 0; target < output_extent; ++target)
        product_error = add_checked(product_error,
            workspace[4U * source_raw_extent + target], slot);
    wide twice_xden = product_checked(2, xden, slot);
    wide twice_scale = (wide)1 << (grain + 1U);
    wide radius_source = signed_product_divide_2(x_l1, rho_h, twice_xden, 1, slot);
    wide radius_rounding = signed_product_divide_2(source_error, h_l1, twice_scale, 1, slot);
    wide radius = add_checked(add_checked(radius_source, radius_rounding, slot), product_error, slot);
    if (*slot || radius < 0) return;
    phase_enclosure_write(output_lo, output_hi, 2U * output_extent, radius);
}

extern "C" __global__ void section_phase_enclosed_difference_validate(
    const int64_t *predicted_lo, const int64_t *predicted_hi, uint32_t predicted_wide_at,
    uint32_t predicted_raw_extent,
    const int64_t *observed_lo, const int64_t *observed_hi,
    uint32_t observed_at, uint32_t observed_denominator_at, uint32_t observed_disposition_at,
    uint32_t observed_complex_coordinates, uint32_t observed_raw_extent,
    uint32_t predicted_from, uint32_t observed_from, uint32_t extent, uint32_t grain,
    wide *workspace, uint32_t *slot, const uint32_t *census,
    const uint32_t *lineage, uint32_t lineage_count
) {
    if (blockIdx.x != 0 || threadIdx.x != 0) return;
    if (*slot != 0 || upstream_refused(census, lineage, lineage_count, slot)) return;
    if (grain < 1U || grain > 120U || !predicted_raw_extent || !observed_raw_extent || !extent
        || (uint64_t)predicted_from + extent > predicted_raw_extent
        || (uint64_t)observed_from + extent > observed_raw_extent
        || predicted_raw_extent > 0x3fffffffU || observed_raw_extent > 0x3fffffffU
        || extent > 0x3fffffffU) {
        atomicOr(slot, REFUSED_MALFORMED);
        return;
    }
    wide observed_den;
    if (!phase_enclosure_validate_ball(predicted_lo, predicted_hi, predicted_wide_at,
        predicted_raw_extent, &workspace[2U * extent + 1U], slot)) return;
    if (!phase_enclosure_validate_point(observed_lo, observed_hi, observed_at,
        observed_denominator_at, observed_disposition_at, observed_complex_coordinates,
        observed_raw_extent, &observed_den, slot)) return;
    workspace[2U * extent] = observed_den;
}

extern "C" __global__ void section_phase_enclosed_difference_products(
    const int64_t *predicted_lo, uint32_t predicted_wide_at,
    const int64_t *observed_lo, uint32_t observed_at, uint32_t predicted_from,
    uint32_t observed_from, uint32_t extent, uint32_t grain, wide *workspace,
    int64_t *output_lo, int64_t *output_hi,
    uint32_t *slot, const uint32_t *census, const uint32_t *lineage, uint32_t lineage_count
) {
    uint64_t coordinate64 = (uint64_t)blockIdx.x * blockDim.x + threadIdx.x;
    uint32_t width = 2U * extent;
    if (coordinate64 >= width || *slot != 0) return;
    if (upstream_refused(census, lineage, lineage_count, slot)) return;
    uint32_t coordinate = (uint32_t)coordinate64;
    wide observed_den = workspace[width];
    wide numerator = (wide)observed_lo[observed_at + 2U * observed_from + coordinate];
    wide floor_value = signed_product_divide_2(
        numerator, (wide)1 << (grain - 1U), observed_den, 0, slot);
    wide ceil_value = signed_product_divide_2(
        numerator, (wide)1 << (grain - 1U), observed_den, 1, slot);
    if (*slot) return;
    wide observed = numerator < 0 ? ceil_value : floor_value;
    wide predicted = phase_enclosure_read(predicted_lo,
        (uint64_t)predicted_wide_at + 2ULL * predicted_from + coordinate);
    phase_enclosure_write(output_lo, output_hi, coordinate, sub_checked(observed, predicted, slot));
    workspace[coordinate] = floor_value != ceil_value ? 1 : 0;
}

extern "C" __global__ void section_phase_enclosed_difference_finish(
    wide *workspace, uint32_t extent, int64_t *output_lo, int64_t *output_hi,
    uint32_t *slot, const uint32_t *census, const uint32_t *lineage, uint32_t lineage_count
) {
    if (blockIdx.x != 0 || threadIdx.x != 0) return;
    if (*slot != 0 || upstream_refused(census, lineage, lineage_count, slot)) return;
    uint32_t width = 2U * extent;
    wide radius = workspace[width + 1U];
    for (uint32_t coordinate = 0; coordinate < width; ++coordinate)
        radius = add_checked(radius, workspace[coordinate], slot);
    if (*slot || radius < 0) return;
    phase_enclosure_write(output_lo, output_hi, width, radius);
}

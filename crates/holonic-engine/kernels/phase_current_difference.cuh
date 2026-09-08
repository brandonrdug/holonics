// Oriented difference of two resident rational phase currents on one exact overlap.
// Validation is a serial resident admission; product lanes only run after it and write the
// private workspace. The existing convolution normalize and pack kernels finish the passage.

extern "C" __global__ void section_phase_difference_validate(
    const int64_t *predicted_lo, const int64_t *predicted_hi,
    uint32_t predicted_at, uint32_t predicted_denominator_at,
    uint32_t predicted_disposition_at,
    const int64_t *observed_lo, const int64_t *observed_hi,
    uint32_t observed_at, uint32_t observed_denominator_at,
    uint32_t observed_disposition_at,
    uint32_t predicted_complex_coordinates, uint32_t observed_complex_coordinates,
    uint32_t predicted_raw_extent, uint32_t observed_raw_extent,
    uint32_t predicted_from, uint32_t observed_from, uint32_t extent,
    wide *workspace, uint32_t *slot, const uint32_t *census,
    const uint32_t *lineage, uint32_t lineage_count
) {
    if (blockIdx.x != 0 || threadIdx.x != 0) return;
    if (*slot != 0 || upstream_refused(census, lineage, lineage_count, slot)) return;

    uint64_t predicted_complex = predicted_complex_coordinates;
    uint64_t observed_complex = observed_complex_coordinates;
    uint64_t predicted_raw = predicted_raw_extent;
    uint64_t observed_raw = observed_raw_extent;
    uint64_t predicted_start = predicted_from;
    uint64_t observed_start = observed_from;
    uint64_t overlap = extent;
    if (!predicted_complex || !observed_complex || !predicted_raw || !observed_raw || !overlap
        || predicted_raw > predicted_complex || observed_raw > observed_complex
        || predicted_complex > 0x7fffffffULL || observed_complex > 0x7fffffffULL
        || predicted_start + overlap > predicted_raw
        || observed_start + overlap > observed_raw
        || overlap > 0x7fffffffULL
        || 2ULL * overlap > (0xffffffffULL - 1ULL)) {
        atomicOr(slot, REFUSED_MALFORMED);
        return;
    }
    if (predicted_at + 2ULL * predicted_complex > 0xffffffffULL
        || observed_at + 2ULL * observed_complex > 0xffffffffULL) {
        atomicOr(slot, REFUSED_MALFORMED);
        return;
    }
    uint32_t predicted_count = (uint32_t)predicted_complex;
    uint32_t observed_count = (uint32_t)observed_complex;
    uint32_t predicted_raw_count = (uint32_t)predicted_raw;
    uint32_t observed_raw_count = (uint32_t)observed_raw;
    uint32_t width = 2U * (uint32_t)overlap;

    wide predicted_den = fibre_current_denominator(
        predicted_lo, predicted_hi, predicted_denominator_at,
        predicted_disposition_at, slot);
    wide observed_den = fibre_current_denominator(
        observed_lo, observed_hi, observed_denominator_at,
        observed_disposition_at, slot);
    if (*slot) return;
    for (uint32_t coordinate = 0; coordinate < predicted_count; ++coordinate) {
        uint64_t at64 = (uint64_t)predicted_at + 2ULL * coordinate;
        uint32_t at = (uint32_t)at64;
        if (predicted_lo[at] != predicted_hi[at]
            || predicted_lo[at + 1U] != predicted_hi[at + 1U]
            || (coordinate >= predicted_raw_count
                && (predicted_lo[at] != 0 || predicted_lo[at + 1U] != 0))) {
            atomicOr(slot, REFUSED_MALFORMED);
            return;
        }
    }
    for (uint32_t coordinate = 0; coordinate < observed_count; ++coordinate) {
        uint64_t at64 = (uint64_t)observed_at + 2ULL * coordinate;
        uint32_t at = (uint32_t)at64;
        if (observed_lo[at] != observed_hi[at]
            || observed_lo[at + 1U] != observed_hi[at + 1U]
            || (coordinate >= observed_raw_count
                && (observed_lo[at] != 0 || observed_lo[at + 1U] != 0))) {
            atomicOr(slot, REFUSED_MALFORMED);
            return;
        }
    }
    wide common = fibre_lcm(predicted_den, observed_den, slot);
    if (*slot || common <= 0) return;
    workspace[width] = common;
    workspace[width + 2U] = common / predicted_den;
    workspace[width + 3U] = common / observed_den;
}

extern "C" __global__ void section_phase_difference_products(
    const int64_t *predicted_lo, const int64_t *predicted_hi,
    uint32_t predicted_at, uint32_t predicted_denominator_at,
    uint32_t predicted_disposition_at,
    const int64_t *observed_lo, const int64_t *observed_hi,
    uint32_t observed_at, uint32_t observed_denominator_at,
    uint32_t observed_disposition_at,
    uint32_t predicted_complex_coordinates, uint32_t observed_complex_coordinates,
    uint32_t predicted_raw_extent, uint32_t observed_raw_extent,
    uint32_t predicted_from, uint32_t observed_from, uint32_t extent,
    wide *workspace, uint32_t *slot, const uint32_t *census,
    const uint32_t *lineage, uint32_t lineage_count
) {
    (void)predicted_hi;
    (void)predicted_denominator_at;
    (void)predicted_disposition_at;
    (void)observed_hi;
    (void)observed_denominator_at;
    (void)observed_disposition_at;
    (void)predicted_complex_coordinates;
    (void)observed_complex_coordinates;
    (void)predicted_raw_extent;
    (void)observed_raw_extent;
    uint64_t j64 = (uint64_t)blockIdx.x * (uint64_t)blockDim.x + (uint64_t)threadIdx.x;
    uint32_t width = 2U * extent;
    if (j64 >= width || *slot != 0) return;
    if (upstream_refused(census, lineage, lineage_count, slot)) return;
    uint32_t j = (uint32_t)j64;
    wide predicted_scale = workspace[width + 2U];
    wide observed_scale = workspace[width + 3U];
    wide observed = product_checked(
        observed_lo[observed_at + 2U * observed_from + j], observed_scale, slot);
    wide predicted = product_checked(
        predicted_lo[predicted_at + 2U * predicted_from + j], predicted_scale, slot);
    if (*slot) return;
    workspace[j] = sub_checked(observed, predicted, slot);
}

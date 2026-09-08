// Response-leg adjoint of the retained causal phase convolution. For each response coefficient k,
// accumulate conjugate(source[j]) * residual[k+j-predicted_from] only where the explicitly
// observed residual support contains k+j. This is a receiver-restricted return, not a learner.

extern "C" __global__ void section_phase_response_adjoint_validate(
    const int64_t *source_lo, const int64_t *source_hi,
    uint32_t source_at, uint32_t source_denominator_at, uint32_t source_disposition_at,
    const int64_t *residual_lo, const int64_t *residual_hi,
    uint32_t residual_at, uint32_t residual_denominator_at, uint32_t residual_disposition_at,
    uint32_t source_complex_coordinates, uint32_t residual_complex_coordinates,
    uint32_t source_raw_extent, uint32_t response_raw_extent,
    uint32_t predicted_from, uint32_t residual_raw_extent,
    wide *workspace, uint32_t *slot, const uint32_t *census,
    const uint32_t *lineage, uint32_t lineage_count
) {
    if (blockIdx.x != 0 || threadIdx.x != 0) return;
    if (*slot != 0 || upstream_refused(census, lineage, lineage_count, slot)) return;

    uint64_t source_complex = source_complex_coordinates;
    uint64_t residual_complex = residual_complex_coordinates;
    uint64_t source_raw = source_raw_extent;
    uint64_t response_raw = response_raw_extent;
    uint64_t predicted = predicted_from;
    uint64_t residual_raw = residual_raw_extent;
    if (!source_complex || !residual_complex || !source_raw || !response_raw || !residual_raw
        || source_raw > source_complex || residual_raw > residual_complex
        || source_complex > 0x7fffffffULL || residual_complex > 0x7fffffffULL
        || predicted + residual_raw > source_raw + response_raw - 1ULL
        || source_raw + response_raw - 1ULL > 0x7fffffffULL
        || 2ULL * response_raw > (0xffffffffULL - 1ULL)
        || source_at + 2ULL * source_complex > 0xffffffffULL
        || residual_at + 2ULL * residual_complex > 0xffffffffULL) {
        atomicOr(slot, REFUSED_MALFORMED);
        return;
    }
    uint32_t source_count = (uint32_t)source_complex;
    uint32_t residual_count = (uint32_t)residual_complex;
    uint32_t source_raw_count = (uint32_t)source_raw;
    uint32_t residual_raw_count = (uint32_t)residual_raw;
    uint32_t response_count = (uint32_t)response_raw;
    uint32_t width = 2U * response_count;
    wide source_den = fibre_current_denominator(
        source_lo, source_hi, source_denominator_at, source_disposition_at, slot);
    wide residual_den = fibre_current_denominator(
        residual_lo, residual_hi, residual_denominator_at, residual_disposition_at, slot);
    if (*slot) return;
    for (uint32_t coordinate = 0; coordinate < source_count; ++coordinate) {
        uint32_t at = source_at + 2U * coordinate;
        if (source_lo[at] != source_hi[at] || source_lo[at + 1U] != source_hi[at + 1U]
            || (coordinate >= source_raw_count
                && (source_lo[at] != 0 || source_lo[at + 1U] != 0))) {
            atomicOr(slot, REFUSED_MALFORMED);
            return;
        }
    }
    for (uint32_t coordinate = 0; coordinate < residual_count; ++coordinate) {
        uint32_t at = residual_at + 2U * coordinate;
        if (residual_lo[at] != residual_hi[at]
            || residual_lo[at + 1U] != residual_hi[at + 1U]
            || (coordinate >= residual_raw_count
                && (residual_lo[at] != 0 || residual_lo[at + 1U] != 0))) {
            atomicOr(slot, REFUSED_MALFORMED);
            return;
        }
    }
    wide common = product_checked(source_den, residual_den, slot);
    if (*slot || common <= 0) return;
    workspace[width] = common;
}

extern "C" __global__ void section_phase_response_adjoint_products(
    const int64_t *source_lo, const int64_t *source_hi,
    uint32_t source_at, uint32_t source_denominator_at, uint32_t source_disposition_at,
    const int64_t *residual_lo, const int64_t *residual_hi,
    uint32_t residual_at, uint32_t residual_denominator_at, uint32_t residual_disposition_at,
    uint32_t source_complex_coordinates, uint32_t residual_complex_coordinates,
    uint32_t source_raw_extent, uint32_t response_raw_extent,
    uint32_t predicted_from, uint32_t residual_raw_extent,
    wide *workspace, uint32_t *slot, const uint32_t *census,
    const uint32_t *lineage, uint32_t lineage_count
) {
    (void)source_hi;
    (void)source_denominator_at;
    (void)source_disposition_at;
    (void)residual_hi;
    (void)residual_denominator_at;
    (void)residual_disposition_at;
    (void)source_complex_coordinates;
    (void)residual_complex_coordinates;
    uint64_t target64 = (uint64_t)blockIdx.x * (uint64_t)blockDim.x + (uint64_t)threadIdx.x;
    if (target64 >= response_raw_extent || *slot != 0) return;
    if (upstream_refused(census, lineage, lineage_count, slot)) return;
    uint32_t target = (uint32_t)target64;
    wide real = 0;
    wide imaginary = 0;
    uint64_t observed_start = predicted_from;
    uint64_t observed_end = observed_start + residual_raw_extent;
    uint64_t source_begin = observed_start > target ? observed_start - target : 0;
    uint64_t source_end = observed_end > target ? observed_end - target : 0;
    if (source_end > source_raw_extent) source_end = source_raw_extent;
    for (uint64_t source = source_begin; source < source_end; ++source) {
        uint64_t summed = (uint64_t)target + source;
        uint32_t residual = (uint32_t)(summed - observed_start);
        uint32_t source_index = source_at + 2U * source;
        uint32_t residual_index = residual_at + 2U * residual;
        wide ar = source_lo[source_index];
        wide ai = source_lo[source_index + 1U];
        wide br = residual_lo[residual_index];
        wide bi = residual_lo[residual_index + 1U];
        real = add_checked(real,
            add_checked(product_checked(ar, br, slot), product_checked(ai, bi, slot), slot),
            slot);
        imaginary = add_checked(imaginary,
            sub_checked(product_checked(ar, bi, slot), product_checked(ai, br, slot), slot),
            slot);
        if (*slot) return;
    }
    if (*slot) return;
    workspace[2U * target] = real;
    workspace[2U * target + 1U] = imaginary;
}

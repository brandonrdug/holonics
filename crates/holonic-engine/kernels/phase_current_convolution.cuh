// Causal convolution of two resident complex polynomial currents. The raw extents are the
// active coefficient populations; coordinates after them must be structural zero.
extern "C" __global__ void section_phase_convolution(
    const int64_t *source_lo, const int64_t *source_hi,
    uint32_t source_at, uint32_t source_denominator_at, uint32_t source_disposition_at,
    const int64_t *response_lo, const int64_t *response_hi,
    uint32_t response_at, uint32_t response_denominator_at, uint32_t response_disposition_at,
    uint32_t source_complex_coordinates, uint32_t response_complex_coordinates,
    uint32_t source_raw_extent, uint32_t response_raw_extent,
    int64_t *output_lo, int64_t *output_hi,
    uint32_t *slot, const uint32_t *census, const uint32_t *lineage, uint32_t lineage_count
) {
    if (blockIdx.x != 0 || threadIdx.x != 0) return;
    if (upstream_refused(census, lineage, lineage_count, slot)) return;

    uint64_t source_complex = source_complex_coordinates;
    uint64_t response_complex = response_complex_coordinates;
    uint64_t source_raw = source_raw_extent;
    uint64_t response_raw = response_raw_extent;
    if (!source_complex || !response_complex || !source_raw || !response_raw
        || source_raw > source_complex || response_raw > response_complex
        || source_complex > 0x7fffffffULL || response_complex > 0x7fffffffULL) {
        atomicOr(slot, REFUSED_MALFORMED);
        return;
    }
    uint64_t output_extent64 = source_raw + response_raw - 1ULL;
    if (output_extent64 > 0x7fffffffULL
        || output_extent64 > (0xffffffffULL - 1ULL) / 2ULL) {
        atomicOr(slot, REFUSED_MALFORMED);
        return;
    }
    uint32_t source_complex_count = (uint32_t)source_complex;
    uint32_t response_complex_count = (uint32_t)response_complex;
    uint32_t source_raw_count = (uint32_t)source_raw;
    uint32_t response_raw_count = (uint32_t)response_raw;
    uint32_t output_extent = (uint32_t)output_extent64;
    uint32_t output_width = 2U * output_extent + 1U;

    wide source_den = fibre_current_denominator(source_lo, source_hi,
        source_denominator_at, source_disposition_at, slot);
    wide response_den = fibre_current_denominator(response_lo, response_hi,
        response_denominator_at, response_disposition_at, slot);
    if (*slot) return;
    for (uint32_t coordinate = 0; coordinate < source_complex_count; ++coordinate) {
        uint32_t at = source_at + 2U * coordinate;
        if (source_lo[at] != source_hi[at] || source_lo[at + 1U] != source_hi[at + 1U]) {
            atomicOr(slot, REFUSED_MALFORMED);
            return;
        }
        if (coordinate >= source_raw_count
            && (source_lo[at] != 0 || source_lo[at + 1U] != 0)) {
            atomicOr(slot, REFUSED_MALFORMED);
            return;
        }
    }
    for (uint32_t coordinate = 0; coordinate < response_complex_count; ++coordinate) {
        uint32_t at = response_at + 2U * coordinate;
        if (response_lo[at] != response_hi[at]
            || response_lo[at + 1U] != response_hi[at + 1U]) {
            atomicOr(slot, REFUSED_MALFORMED);
            return;
        }
        if (coordinate >= response_raw_count
            && (response_lo[at] != 0 || response_lo[at + 1U] != 0)) {
            atomicOr(slot, REFUSED_MALFORMED);
            return;
        }
    }
    wide common = product_checked(source_den, response_den, slot);
    if (*slot) return;
    extern __shared__ wide convolution_scratch[];
    for (uint32_t target = 0; target < output_extent; ++target) {
        wide real = 0, imaginary = 0;
        uint32_t source_first = target >= response_raw_count
            ? target - response_raw_count + 1U
            : 0U;
        uint32_t source_last = min(target, source_raw_count - 1U);
        for (uint32_t source = source_first; source <= source_last; ++source) {
            uint32_t response = target - source;
            wide product[3];
            fibre_phase_product(
                source_lo[source_at + 2U * source], source_lo[source_at + 2U * source + 1U],
                source_den,
                response_lo[response_at + 2U * response],
                response_lo[response_at + 2U * response + 1U], response_den,
                product, slot);
            if (*slot) return;
            wide factor = common / product[2];
            real = add_checked(real, product_checked(product[0], factor, slot), slot);
            imaginary = add_checked(imaginary, product_checked(product[1], factor, slot), slot);
            if (*slot) return;
        }
        convolution_scratch[2U * target] = real;
        convolution_scratch[2U * target + 1U] = imaginary;
    }
    fibre_normalize(convolution_scratch, output_width - 1U, &common, slot);
    if (*slot) return;
    for (uint32_t j = 0; j < output_width - 1U; ++j)
        to_word(convolution_scratch[j], slot);
    to_word(common, slot);
    if (*slot) return;
    for (uint32_t j = 0; j < output_width - 1U; ++j)
        output_lo[j] = output_hi[j] = to_word(convolution_scratch[j], slot);
    output_lo[output_width - 1U] = output_hi[output_width - 1U] = to_word(common, slot);
}

// Scalable phase convolution. The existing `section_phase_convolution` above intentionally keeps
// its complete operation in one shared-scratch launch. These four launches retain the same
// checked admission and per-target source ordering while moving the coefficient population into a
// resident workspace, so no intermediate section is read back or copied through the host.
// Validation is a separate serial launch so malformed/disposition refusal is complete before
// parallel arithmetic begins; product-lane refusal is consequently limited to carrier admission.
extern "C" __global__ void section_phase_convolution_validate(
    const int64_t *source_lo, const int64_t *source_hi,
    uint32_t source_at, uint32_t source_denominator_at, uint32_t source_disposition_at,
    const int64_t *response_lo, const int64_t *response_hi,
    uint32_t response_at, uint32_t response_denominator_at, uint32_t response_disposition_at,
    uint32_t source_complex_coordinates, uint32_t response_complex_coordinates,
    uint32_t source_raw_extent, uint32_t response_raw_extent,
    wide *workspace, uint32_t *slot, const uint32_t *census, const uint32_t *lineage,
    uint32_t lineage_count
) {
    uint64_t target64 = (uint64_t)blockIdx.x * (uint64_t)blockDim.x + (uint64_t)threadIdx.x;
    if (target64 != 0) return;
    if (*slot != 0 || upstream_refused(census, lineage, lineage_count, slot)) return;
    uint64_t source_complex = source_complex_coordinates;
    uint64_t response_complex = response_complex_coordinates;
    uint64_t source_raw = source_raw_extent;
    uint64_t response_raw = response_raw_extent;
    if (!source_complex || !response_complex || !source_raw || !response_raw
        || source_raw > source_complex || response_raw > response_complex
        || source_complex > 0x7fffffffULL || response_complex > 0x7fffffffULL) {
        atomicOr(slot, REFUSED_MALFORMED);
        return;
    }
    uint64_t output_extent64 = source_raw + response_raw - 1ULL;
    if (output_extent64 > 0x7fffffffULL
        || output_extent64 > (0xffffffffULL - 1ULL) / 2ULL) {
        atomicOr(slot, REFUSED_MALFORMED);
        return;
    }
    uint32_t source_complex_count = (uint32_t)source_complex;
    uint32_t response_complex_count = (uint32_t)response_complex;
    uint32_t source_raw_count = (uint32_t)source_raw;
    uint32_t response_raw_count = (uint32_t)response_raw;
    uint32_t output_extent = (uint32_t)output_extent64;
    wide source_den = fibre_current_denominator(source_lo, source_hi,
        source_denominator_at, source_disposition_at, slot);
    wide response_den = fibre_current_denominator(response_lo, response_hi,
        response_denominator_at, response_disposition_at, slot);
    if (*slot) return;
    for (uint32_t coordinate = 0; coordinate < source_complex_count; ++coordinate) {
        uint32_t at = source_at + 2U * coordinate;
        if (source_lo[at] != source_hi[at] || source_lo[at + 1U] != source_hi[at + 1U]
            || (coordinate >= source_raw_count
                && (source_lo[at] != 0 || source_lo[at + 1U] != 0))) {
            atomicOr(slot, REFUSED_MALFORMED);
            return;
        }
    }
    for (uint32_t coordinate = 0; coordinate < response_complex_count; ++coordinate) {
        uint32_t at = response_at + 2U * coordinate;
        if (response_lo[at] != response_hi[at]
            || response_lo[at + 1U] != response_hi[at + 1U]
            || (coordinate >= response_raw_count
                && (response_lo[at] != 0 || response_lo[at + 1U] != 0))) {
            atomicOr(slot, REFUSED_MALFORMED);
            return;
        }
    }
    wide common = product_checked(source_den, response_den, slot);
    if (*slot) return;
    workspace[2U * output_extent] = common;
}

extern "C" __global__ void section_phase_convolution_products(
    const int64_t *source_lo, const int64_t *source_hi,
    uint32_t source_at, uint32_t source_denominator_at, uint32_t source_disposition_at,
    const int64_t *response_lo, const int64_t *response_hi,
    uint32_t response_at, uint32_t response_denominator_at, uint32_t response_disposition_at,
    uint32_t source_complex_coordinates, uint32_t response_complex_coordinates,
    uint32_t source_raw_extent, uint32_t response_raw_extent,
    wide *workspace, uint32_t *slot, const uint32_t *census, const uint32_t *lineage,
    uint32_t lineage_count
) {
    uint64_t target64 = (uint64_t)blockIdx.x * (uint64_t)blockDim.x + (uint64_t)threadIdx.x;
    if (*slot != 0) return;
    if (upstream_refused(census, lineage, lineage_count, slot)) return;
    uint32_t output_extent = source_raw_extent + response_raw_extent - 1U;
    uint32_t target = (uint32_t)target64;
    if (target >= output_extent) return;
    uint32_t source_raw_count = source_raw_extent;
    uint32_t response_raw_count = response_raw_extent;
    uint32_t common_at = 2U * output_extent;

    wide source_den = fibre_current_denominator(source_lo, source_hi,
        source_denominator_at, source_disposition_at, slot);
    wide response_den = fibre_current_denominator(response_lo, response_hi,
        response_denominator_at, response_disposition_at, slot);
    if (*slot) return;
    wide common = workspace[common_at];

    wide real = 0, imaginary = 0;
    uint32_t source_first = target >= response_raw_count
        ? target - response_raw_count + 1U
        : 0U;
    uint32_t source_last = min(target, source_raw_count - 1U);
    for (uint32_t source = source_first; source <= source_last; ++source) {
        uint32_t response = target - source;
        wide product[3];
        fibre_phase_product(
            source_lo[source_at + 2U * source], source_lo[source_at + 2U * source + 1U],
            source_den,
            response_lo[response_at + 2U * response],
            response_lo[response_at + 2U * response + 1U], response_den,
            product, slot);
        if (*slot) return;
        wide factor = common / product[2];
        real = add_checked(real, product_checked(product[0], factor, slot), slot);
        imaginary = add_checked(imaginary, product_checked(product[1], factor, slot), slot);
        if (*slot) return;
    }
    workspace[2U * target] = real;
    workspace[2U * target + 1U] = imaginary;
}

// Reduce the common denominator and all realified output coordinates in one resident pass. The
// numerator coordinates stay unreduced until the independent pack lanes divide by this exact gcd.
extern "C" __global__ void section_phase_convolution_normalize(
    wide *workspace, uint32_t width, uint32_t *slot, const uint32_t *census,
    const uint32_t *lineage, uint32_t lineage_count
) {
    if (blockIdx.x != 0 || threadIdx.x != 0) return;
    uint32_t previous = *slot;
    int inherited = upstream_refused(census, lineage, lineage_count, slot);
    if (previous != 0 || inherited || *slot != 0) return;
    if (width == 0) {
        atomicOr(slot, REFUSED_MALFORMED);
        return;
    }
    wide common = workspace[width];
    if (common <= 0) {
        atomicOr(slot, REFUSED_MALFORMED);
        return;
    }
    uwide divisor = magnitude(common);
    for (uint32_t j = 0; j < width && divisor != 1; ++j)
        divisor = fibre_gcd(divisor, magnitude(workspace[j]));
    if (divisor == 0) {
        atomicOr(slot, REFUSED_MALFORMED);
        return;
    }
    wide gcd = of_magnitude(divisor, 0, slot);
    if (*slot) return;
    workspace[width] = common / gcd;
    workspace[width + 1U] = gcd;
}

// Pack the normalized resident workspace directly into the private output section. A lane that
// sees any prior refusal leaves the output untouched. A refused output never reaches the next
// operation: its producing passage returns the census/lineage obstruction instead.
extern "C" __global__ void section_phase_convolution_pack(
    const wide *workspace, uint32_t width, int64_t *output_lo, int64_t *output_hi,
    uint32_t *slot, const uint32_t *census, const uint32_t *lineage, uint32_t lineage_count
) {
    uint64_t j64 = (uint64_t)blockIdx.x * (uint64_t)blockDim.x + (uint64_t)threadIdx.x;
    if (j64 > width) return;
    uint32_t previous = *slot;
    int inherited = upstream_refused(census, lineage, lineage_count, slot);
    if (previous != 0 || inherited || *slot != 0) return;
    if (width == 0) {
        atomicOr(slot, REFUSED_MALFORMED);
        return;
    }
    wide gcd = workspace[width + 1U];
    if (gcd <= 0) {
        atomicOr(slot, REFUSED_MALFORMED);
        return;
    }
    uint32_t j = (uint32_t)j64;
    wide value = j < width ? workspace[j] / gcd : workspace[width];
    int64_t packed = to_word(value, slot);
    if (*slot) return;
    output_lo[j] = output_hi[j] = packed;
}

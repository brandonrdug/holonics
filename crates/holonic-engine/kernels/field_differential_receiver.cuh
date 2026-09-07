// Terminal differential receiver over an immutable junction outgoing report. It changes no
// current, contact, state or source handle. A sign is returned only if the complete current ball
// lies on one side of that differential receiver's zero plane.
extern "C" __global__ void section_field_differential_receiver(
    const int64_t *report_lo, const int64_t *report_hi, uint32_t dimension, uint32_t mode,
    uint32_t first_complex, uint32_t pairs, int64_t *out_lo, int64_t *out_hi,
    uint32_t *slot, const uint32_t *census, const uint32_t *lineage, uint32_t lineage_count
) {
    if (blockIdx.x || threadIdx.x) return;
    if (upstream_refused(census, lineage, lineage_count, slot)) return;
    if (!dimension || (dimension & 1u) || (mode < 1u || mode > 4u) || !pairs || pairs > 63u
        || first_complex > dimension / 2u || 2u * pairs > dimension / 2u - first_complex) {
        atomicOr(slot, REFUSED_MALFORMED); return;
    }
    const uint64_t stride = (uint64_t)dimension + 1u;
    const uint64_t words = mode == 4u ? 37u * (uint64_t)dimension + 44u : (mode == 3u ? 18u * (uint64_t)dimension + 24u : (mode == 1u ? 4u : 12u) * stride);
    const uint64_t start = mode >= 3u ? 0u : stride;
    for (uint64_t i = 0; i < words; ++i) {
        if (report_lo[i] != report_hi[i]) { atomicOr(slot, REFUSED_MALFORMED); return; }
    }
    wide radius = 0;
    if (mode == 1u) {
        if (report_lo[stride + dimension] <= 0) { atomicOr(slot, REFUSED_MALFORMED); return; }
    } else {
        radius = ((const wide *)report_lo)[start + dimension];
        if (radius < 0) { atomicOr(slot, REFUSED_MALFORMED); return; }
    }
    uwide error_hi, error_lo;
    mul_magnitude_256((uwide)radius, (uwide)radius, &error_hi, &error_lo);
    // Positive signed-wide radius has magnitude < 2^127; twice its square fits unsigned 256.
    error_hi = (error_hi << 1) | (error_lo >> 127);
    error_lo <<= 1;
    uint64_t positive = 0, negative = 0, unresolved = 0, exact_zero = 0;
    for (uint32_t bit = 0; bit < pairs; ++bit) {
        const uint64_t left_at = start + 2u * ((uint64_t)first_complex + 2u * bit);
        wide left, right;
        if (mode == 1u) {
            left = (wide)report_lo[left_at];
            right = (wide)report_lo[left_at + 2u];
        } else {
            left = ((const wide *)report_lo)[left_at];
            right = ((const wide *)report_lo)[left_at + 2u];
        }
        // Unsigned subtraction gives the complete magnitude even when the signed difference
        // would leave the wide carrier. No narrowed numerical current is formed or committed.
        uwide gap = right >= left ? (uwide)right - (uwide)left : (uwide)left - (uwide)right;
        uwide gap_hi, gap_lo;
        mul_magnitude_256(gap, gap, &gap_hi, &gap_lo);
        const uint64_t mask = (uint64_t)1 << bit;
        if (gap_hi > error_hi || (gap_hi == error_hi && gap_lo > error_lo)) {
            if (right > left) positive |= mask;
            else negative |= mask;
        } else {
            unresolved |= mask;
            if (radius == 0 && gap == 0) exact_zero |= mask;
        }
    }
    out_lo[0] = out_hi[0] = (int64_t)positive;
    out_lo[1] = out_hi[1] = (int64_t)negative;
    out_lo[2] = out_hi[2] = (int64_t)unresolved;
    out_lo[3] = out_hi[3] = (int64_t)exact_zero;
}

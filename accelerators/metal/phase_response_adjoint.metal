// Response-leg adjoint of the retained causal phase convolution. For each response coefficient k,
// accumulate conjugate(source[j]) * residual[k+j-predicted_from] only over the explicitly observed
// residual support. This is a receiver-restricted return, not a learner.

kernel void section_phase_response_adjoint_validate(
    device const long *source_lo [[buffer(0)]], device const long *source_hi [[buffer(1)]],
    constant uint &source_at [[buffer(2)]], constant uint &source_denominator_at [[buffer(3)]],
    constant uint &source_disposition_at [[buffer(4)]],
    device const long *residual_lo [[buffer(5)]], device const long *residual_hi [[buffer(6)]],
    constant uint &residual_at [[buffer(7)]], constant uint &residual_denominator_at [[buffer(8)]],
    constant uint &residual_disposition_at [[buffer(9)]],
    constant uint &source_complex_coordinates [[buffer(10)]],
    constant uint &residual_complex_coordinates [[buffer(11)]],
    constant uint &source_raw_extent [[buffer(12)]], constant uint &response_raw_extent [[buffer(13)]],
    constant uint &predicted_from [[buffer(14)]], constant uint &residual_raw_extent [[buffer(15)]],
    device W *workspace [[buffer(16)]], device uint *slot [[buffer(17)]],
    device const uint *census [[buffer(18)]], device const uint *lineage [[buffer(19)]],
    constant uint &lineage_count [[buffer(20)]], uint gid [[thread_position_in_grid]]) {
  if (gid != 0 || *slot || upstream(census, lineage, lineage_count, slot))
    return;
  ulong source_complex = (ulong)source_complex_coordinates;
  ulong residual_complex = (ulong)residual_complex_coordinates;
  ulong source_raw = (ulong)source_raw_extent;
  ulong response_raw = (ulong)response_raw_extent;
  ulong predicted = (ulong)predicted_from;
  ulong residual_raw = (ulong)residual_raw_extent;
  if (!source_complex || !residual_complex || !source_raw || !response_raw || !residual_raw
      || source_raw > source_complex || residual_raw > residual_complex
      || source_complex > 0x7ffffffful || residual_complex > 0x7ffffffful
      || predicted + residual_raw > source_raw + response_raw - 1ul
      || source_raw + response_raw - 1ul > 0x7ffffffful
      || 2ul * response_raw > 0xfffffffful - 1ul
      || (ulong)source_at + 2ul * source_complex > 0xfffffffful
      || (ulong)residual_at + 2ul * residual_complex > 0xfffffffful) {
    atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED,
                             memory_order_relaxed);
    return;
  }
  uint source_count = (uint)source_complex;
  uint residual_count = (uint)residual_complex;
  uint source_raw_count = (uint)source_raw;
  uint residual_raw_count = (uint)residual_raw;
  uint response_count = (uint)response_raw;
  uint width = 2u * response_count;
  W source_den = fibre_current_denominator(source_lo, source_hi,
                                           source_denominator_at,
                                           source_disposition_at, slot);
  W residual_den = fibre_current_denominator(residual_lo, residual_hi,
                                             residual_denominator_at,
                                             residual_disposition_at, slot);
  if (*slot)
    return;
  for (uint coordinate = 0; coordinate < source_count; ++coordinate) {
    ulong at64 = (ulong)source_at + 2ul * (ulong)coordinate;
    uint at = (uint)at64;
    if (source_lo[at] != source_hi[at] || source_lo[at + 1u] != source_hi[at + 1u]
        || (coordinate >= source_raw_count
            && (source_lo[at] != 0 || source_lo[at + 1u] != 0))) {
      atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED,
                               memory_order_relaxed);
      return;
    }
  }
  for (uint coordinate = 0; coordinate < residual_count; ++coordinate) {
    ulong at64 = (ulong)residual_at + 2ul * (ulong)coordinate;
    uint at = (uint)at64;
    if (residual_lo[at] != residual_hi[at]
        || residual_lo[at + 1u] != residual_hi[at + 1u]
        || (coordinate >= residual_raw_count
            && (residual_lo[at] != 0 || residual_lo[at + 1u] != 0))) {
      atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED,
                               memory_order_relaxed);
      return;
    }
  }
  W common = field_product_checked(source_den, residual_den, slot);
  if (*slot || wzero_p(common) || wneg_p(common))
    return;
  workspace[width] = common;
}

kernel void section_phase_response_adjoint_products(
    device const long *source_lo [[buffer(0)]], device const long *source_hi [[buffer(1)]],
    constant uint &source_at [[buffer(2)]], constant uint &source_denominator_at [[buffer(3)]],
    constant uint &source_disposition_at [[buffer(4)]],
    device const long *residual_lo [[buffer(5)]], device const long *residual_hi [[buffer(6)]],
    constant uint &residual_at [[buffer(7)]], constant uint &residual_denominator_at [[buffer(8)]],
    constant uint &residual_disposition_at [[buffer(9)]],
    constant uint &source_complex_coordinates [[buffer(10)]],
    constant uint &residual_complex_coordinates [[buffer(11)]],
    constant uint &source_raw_extent [[buffer(12)]], constant uint &response_raw_extent [[buffer(13)]],
    constant uint &predicted_from [[buffer(14)]], constant uint &residual_raw_extent [[buffer(15)]],
    device W *workspace [[buffer(16)]], device uint *slot [[buffer(17)]],
    device const uint *census [[buffer(18)]], device const uint *lineage [[buffer(19)]],
    constant uint &lineage_count [[buffer(20)]], uint gid [[thread_position_in_grid]]) {
  (void)source_hi;
  (void)source_denominator_at;
  (void)source_disposition_at;
  (void)residual_hi;
  (void)residual_denominator_at;
  (void)residual_disposition_at;
  (void)source_complex_coordinates;
  (void)residual_complex_coordinates;
  if (*slot || upstream(census, lineage, lineage_count, slot))
    return;
  if (gid >= response_raw_extent)
    return;
  W real = wzero();
  W imaginary = wzero();
  ulong observed_start = (ulong)predicted_from;
  ulong observed_end = observed_start + (ulong)residual_raw_extent;
  ulong source_begin = observed_start > gid ? observed_start - gid : 0ul;
  ulong source_end = observed_end > gid
      ? min((ulong)source_raw_extent, observed_end - gid) : 0ul;
  for (ulong source = source_begin; source < source_end; ++source) {
    ulong summed = (ulong)gid + (ulong)source;
    uint residual = (uint)(summed - observed_start);
    ulong source_index = (ulong)source_at + 2ul * (ulong)source;
    ulong residual_index = (ulong)residual_at + 2ul * (ulong)residual;
    W ar = fromword(source_lo[source_index]);
    W ai = fromword(source_lo[source_index + 1ul]);
    W br = fromword(residual_lo[residual_index]);
    W bi = fromword(residual_lo[residual_index + 1ul]);
    real = field_add_checked(real,
        field_add_checked(field_product_checked(ar, br, slot),
                          field_product_checked(ai, bi, slot), slot), slot);
    imaginary = field_add_checked(imaginary,
        field_sub_checked(field_product_checked(ar, bi, slot),
                          field_product_checked(ai, br, slot), slot), slot);
    if (*slot)
      return;
  }
  if (!*slot) {
    workspace[2u * gid] = real;
    workspace[2u * gid + 1u] = imaginary;
  }
}

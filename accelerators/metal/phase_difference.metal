// Oriented difference of two resident rational phase currents on one exact overlap.
// The serial admission precedes flat product lanes; the shared convolution normalize and pack
// kernels complete exact reduction and output without a host numerical read.

kernel void section_phase_difference_validate(
    device const long *predicted_lo [[buffer(0)]], device const long *predicted_hi [[buffer(1)]],
    constant uint &predicted_at [[buffer(2)]], constant uint &predicted_denominator_at [[buffer(3)]],
    constant uint &predicted_disposition_at [[buffer(4)]],
    device const long *observed_lo [[buffer(5)]], device const long *observed_hi [[buffer(6)]],
    constant uint &observed_at [[buffer(7)]], constant uint &observed_denominator_at [[buffer(8)]],
    constant uint &observed_disposition_at [[buffer(9)]],
    constant uint &predicted_complex_coordinates [[buffer(10)]],
    constant uint &observed_complex_coordinates [[buffer(11)]],
    constant uint &predicted_raw_extent [[buffer(12)]], constant uint &observed_raw_extent [[buffer(13)]],
    constant uint &predicted_from [[buffer(14)]], constant uint &observed_from [[buffer(15)]],
    constant uint &extent [[buffer(16)]], device W *workspace [[buffer(17)]],
    device uint *slot [[buffer(18)]], device const uint *census [[buffer(19)]],
    device const uint *lineage [[buffer(20)]], constant uint &lineage_count [[buffer(21)]],
    uint gid [[thread_position_in_grid]]) {
  if (gid != 0 || *slot || upstream(census, lineage, lineage_count, slot))
    return;
  ulong predicted_complex = (ulong)predicted_complex_coordinates;
  ulong observed_complex = (ulong)observed_complex_coordinates;
  ulong predicted_raw = (ulong)predicted_raw_extent;
  ulong observed_raw = (ulong)observed_raw_extent;
  ulong predicted_start = (ulong)predicted_from;
  ulong observed_start = (ulong)observed_from;
  ulong overlap = (ulong)extent;
  if (!predicted_complex || !observed_complex || !predicted_raw || !observed_raw || !overlap
      || predicted_raw > predicted_complex || observed_raw > observed_complex
      || predicted_complex > 0x7ffffffful || observed_complex > 0x7ffffffful
      || predicted_start + overlap > predicted_raw || observed_start + overlap > observed_raw
      || overlap > 0x7ffffffful || 2ul * overlap > 0xfffffffful - 1ul
      || (ulong)predicted_at + 2ul * predicted_complex > 0xfffffffful
      || (ulong)observed_at + 2ul * observed_complex > 0xfffffffful) {
    atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED,
                             memory_order_relaxed);
    return;
  }
  uint predicted_count = (uint)predicted_complex;
  uint observed_count = (uint)observed_complex;
  uint predicted_raw_count = (uint)predicted_raw;
  uint observed_raw_count = (uint)observed_raw;
  uint width = 2u * (uint)overlap;
  W predicted_den = fibre_current_denominator(predicted_lo, predicted_hi,
                                              predicted_denominator_at,
                                              predicted_disposition_at, slot);
  W observed_den = fibre_current_denominator(observed_lo, observed_hi,
                                             observed_denominator_at,
                                             observed_disposition_at, slot);
  if (*slot)
    return;
  for (uint coordinate = 0; coordinate < predicted_count; ++coordinate) {
    ulong at64 = (ulong)predicted_at + 2ul * (ulong)coordinate;
    uint at = (uint)at64;
    if (predicted_lo[at] != predicted_hi[at]
        || predicted_lo[at + 1u] != predicted_hi[at + 1u]
        || (coordinate >= predicted_raw_count
            && (predicted_lo[at] != 0 || predicted_lo[at + 1u] != 0))) {
      atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED,
                               memory_order_relaxed);
      return;
    }
  }
  for (uint coordinate = 0; coordinate < observed_count; ++coordinate) {
    ulong at64 = (ulong)observed_at + 2ul * (ulong)coordinate;
    uint at = (uint)at64;
    if (observed_lo[at] != observed_hi[at]
        || observed_lo[at + 1u] != observed_hi[at + 1u]
        || (coordinate >= observed_raw_count
            && (observed_lo[at] != 0 || observed_lo[at + 1u] != 0))) {
      atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED,
                               memory_order_relaxed);
      return;
    }
  }
  W common = field_lcm(predicted_den, observed_den, slot);
  if (*slot || wzero_p(common) || wneg_p(common))
    return;
  workspace[width] = common;
  workspace[width + 2u] = wdiv(common, predicted_den, slot);
  workspace[width + 3u] = wdiv(common, observed_den, slot);
}

kernel void section_phase_difference_products(
    device const long *predicted_lo [[buffer(0)]], device const long *predicted_hi [[buffer(1)]],
    constant uint &predicted_at [[buffer(2)]], constant uint &predicted_denominator_at [[buffer(3)]],
    constant uint &predicted_disposition_at [[buffer(4)]],
    device const long *observed_lo [[buffer(5)]], device const long *observed_hi [[buffer(6)]],
    constant uint &observed_at [[buffer(7)]], constant uint &observed_denominator_at [[buffer(8)]],
    constant uint &observed_disposition_at [[buffer(9)]],
    constant uint &predicted_complex_coordinates [[buffer(10)]],
    constant uint &observed_complex_coordinates [[buffer(11)]],
    constant uint &predicted_raw_extent [[buffer(12)]], constant uint &observed_raw_extent [[buffer(13)]],
    constant uint &predicted_from [[buffer(14)]], constant uint &observed_from [[buffer(15)]],
    constant uint &extent [[buffer(16)]], device W *workspace [[buffer(17)]],
    device uint *slot [[buffer(18)]], device const uint *census [[buffer(19)]],
    device const uint *lineage [[buffer(20)]], constant uint &lineage_count [[buffer(21)]],
    uint gid [[thread_position_in_grid]]) {
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
  if (*slot || upstream(census, lineage, lineage_count, slot))
    return;
  uint width = 2u * extent;
  if (gid >= width)
    return;
  W observed = field_product_checked(
      fromword(observed_lo[(ulong)observed_at + 2ul * (ulong)observed_from + gid]),
      workspace[width + 3u], slot);
  W predicted = field_product_checked(
      fromword(predicted_lo[(ulong)predicted_at + 2ul * (ulong)predicted_from + gid]),
      workspace[width + 2u], slot);
  if (!*slot)
    workspace[gid] = field_sub_checked(observed, predicted, slot);
}

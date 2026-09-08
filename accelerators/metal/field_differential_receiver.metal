// Terminal differential receiver over a complete resident report.  Report coordinates are
// always read from the packed i64 wire; mode 1 is the legacy single-word chart and retains its
// direct i64 access exactly as the CUDA owner does.  The comparison remains a 256-bit exact
// squared-gap admission, with no narrowed numerical current committed.

inline HistoryInteger field_differential_gap(W left, W right) {
  HistoryInteger gap = history_integer(right) - history_integer(left);
  return gap.negative ? -gap : gap;
}

inline HistoryInteger field_differential_error(W radius) {
  HistoryInteger square = history_integer(radius) * history_integer(radius);
  return square + square;
}

kernel void section_field_differential_receiver(
    device const long *report_lo [[buffer(0)]], device const long *report_hi [[buffer(1)]],
    constant uint &dimension [[buffer(2)]], constant uint &mode [[buffer(3)]],
    constant uint &first_complex [[buffer(4)]], constant uint &pairs [[buffer(5)]],
    device long *out_lo [[buffer(6)]], device long *out_hi [[buffer(7)]],
    device uint *slot [[buffer(8)]], device const uint *census [[buffer(9)]],
    device const uint *lineage [[buffer(10)]], constant uint &lineage_count [[buffer(11)]],
    uint3 tid [[thread_position_in_threadgroup]]) {
  if (tid.x || tid.y || tid.z)
    return;
  if (upstream(census, lineage, lineage_count, slot))
    return;
  if (!dimension || (dimension & 1u) || mode < 1u || mode > 5u || !pairs || pairs > 63u
      || first_complex > dimension / 2u
      || 2u * pairs > dimension / 2u - first_complex) {
    atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED,
                             memory_order_relaxed);
    return;
  }
  ulong stride = (ulong)dimension + 1ul;
  ulong words = mode == 5u ? 2ul * stride
                           : mode == 4u ? 37ul * (ulong)dimension + 44ul
                           : mode == 3u ? 18ul * (ulong)dimension + 24ul
                           : (mode == 1u ? 4ul : 12ul) * stride;
  for (ulong i = 0; i < words; ++i) {
    if (report_lo[i] != report_hi[i]) {
      atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED,
                               memory_order_relaxed);
      return;
    }
  }
  ulong start = mode >= 3u ? 0ul : stride;
  W radius = wzero();
  if (mode == 1u) {
    if (report_lo[stride + dimension] <= 0l) {
      atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED,
                               memory_order_relaxed);
      return;
    }
  } else {
    radius = field_wire_read(report_lo, start + dimension);
    if (wneg_p(radius)) {
      atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED,
                               memory_order_relaxed);
      return;
    }
  }

  HistoryInteger error = field_differential_error(radius);
  ulong positive = 0ul, negative = 0ul, unresolved = 0ul, exact_zero = 0ul;
  for (uint bit = 0; bit < pairs; ++bit) {
    ulong left_at = start + 2ul * ((ulong)first_complex + 2ul * (ulong)bit);
    W left, right;
    if (mode == 1u) {
      left = wi64(report_lo[left_at]);
      right = wi64(report_lo[left_at + 2ul]);
    } else {
      left = field_wire_read(report_lo, left_at);
      right = field_wire_read(report_lo, left_at + 2ul);
    }
    HistoryInteger gap = field_differential_gap(left, right);
    HistoryInteger square = gap * gap;
    ulong mask = 1ul << bit;
    if (history_compare(square, error) > 0) {
      if (history_compare(history_integer(right), history_integer(left)) > 0)
        positive |= mask;
      else
        negative |= mask;
    } else {
      unresolved |= mask;
      if (history_zero_p(gap) && wzero_p(radius))
        exact_zero |= mask;
    }
  }
  out_lo[0] = out_hi[0] = as_type<long>(positive);
  out_lo[1] = out_hi[1] = as_type<long>(negative);
  out_lo[2] = out_hi[2] = as_type<long>(unresolved);
  out_lo[3] = out_hi[3] = as_type<long>(exact_zero);
}

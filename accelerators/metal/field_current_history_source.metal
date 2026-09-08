// Complete internal-current source geometry for the Metal resident field path.
// This file is concatenated after native_phase, paired/enclosed junction helpers and
// field_history_integer.metal.  Resident W values remain the doubled i64 wire; the
// HistoryInteger coefficient is used only in private exact arithmetic.

inline W history_source_exact_divide(W numerator, W denominator, device uint *slot) {
  if (wzero_p(denominator) || wneg_p(denominator)) {
    atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED,
                             memory_order_relaxed);
    return wzero();
  }
  U remainder;
  U quotient = udiv(numerator.m, denominator.m, remainder);
  if (!uzero_p(remainder)) {
    atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED,
                             memory_order_relaxed);
    return wzero();
  }
  return wof(quotient, numerator.neg != denominator.neg, slot);
}

inline W history_source_isqrt_floor(W value, device uint *slot) {
  if (wneg_p(value)) {
    atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED,
                             memory_order_relaxed);
    return wzero();
  }
  W root = wzero();
  // A resident W has a 126-bit admitted magnitude, so its square root is below 2^63.
  for (int bit = 62; bit >= 0; --bit) {
    W candidate = root;
    candidate.m = uset(candidate.m, (uint)bit);
    W square = field_product_checked(candidate, candidate, slot);
    if (*slot)
      return wzero();
    if (ult(square.m, value.m) || ueq(square.m, value.m))
      root = candidate;
  }
  return root;
}

inline void field_current_history_source_prepare(
    device const long *query, device const long *origin, device const long *incoming,
    device const long *frame, device const long *origin_frame, device const long *covariance,
    device const long *before, device const long *current, device const long *state,
    uint nodes, uint linked, uint grain, ulong occurrence,
    device long *next_lo, device long *next_hi, device long *source_lo, device long *source_hi,
    threadgroup W *scratch, device uint *slot) {
  if (!nodes || grain < 1u || grain > 120u || linked > 1u || occurrence >= (ulong)0x7ffffffffffffffful) {
    atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED,
                             memory_order_relaxed);
    return;
  }
  uint dimension = 6u * nodes;
  ulong stride = (ulong)dimension + 1ul;
  ulong matrix = (ulong)dimension * (ulong)dimension;
  W before_radius = field_wire_read(before, 4ul * stride - 1ul);
  W current_radius = field_wire_read(current, 4ul * stride - 1ul);
  W current_norm = field_wire_read(current, 2ul * stride - 1ul);
  if (covariance[matrix] != 1l || state[2u * dimension + 5u] != (long)occurrence
      || state[2u * dimension + 6u] != (long)grain || state[2u * dimension + 7u] != 0l
      || wneg_p(before_radius) || wneg_p(current_radius)
      || ult(current_radius.m, before_radius.m) || wneg_p(current_norm)) {
    atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED,
                             memory_order_relaxed);
    return;
  }

  threadgroup W *face = scratch;
  threadgroup W *d = face + dimension;
  W face_den, d_den;
  if (!field_paired_build_faces(query, origin, incoming, frame, origin_frame, nodes, linked,
                                face, d, &face_den, &d_den, slot))
    return;
  if (linked) {
    for (uint i = 0; i < dimension; ++i) {
      if (wzero_p(d_den) || wneg_p(d_den)) {
        atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED,
                                 memory_order_relaxed);
        return;
      }
      d[i] = history_source_exact_divide(d[i], d_den, slot);
      if (*slot)
        return;
    }
  }

  HistoryInteger c_real = history_zero(), c_imaginary = history_zero();
  if (linked) {
    for (uint i = 0; i < dimension; i += 2u)
      history_complex_add_product(c_real, c_imaginary, d[i], d[i + 1u],
                                  field_wire_read(before, 3ul * stride + i),
                                  field_wire_read(before, 3ul * stride + i + 1ul), true);
  }
  W c_real_narrow = history_narrow(c_real, slot);
  W c_imaginary_narrow = history_narrow(c_imaginary, slot);
  if (*slot)
    return;

  HistoryInteger square = history_read_integer(state + 2u * dimension, slot);
  if (square.negative) {
    atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED,
                             memory_order_relaxed);
    return;
  }
  square = square + c_real * c_real + c_imaginary * c_imaginary;

  for (uint i = 0; i < dimension; i += 2u) {
    HistoryInteger real = history_integer(field_wire_read(state, i));
    HistoryInteger imaginary = history_integer(field_wire_read(state, i + 1u));
    if (linked)
      history_complex_add_product(real, imaginary, d[i], d[i + 1u],
                                  c_real_narrow, c_imaginary_narrow, false);
    field_wire_write(next_lo, next_hi, i, history_narrow(real, slot), slot);
    field_wire_write(next_lo, next_hi, i + 1u, history_narrow(imaginary, slot), slot);
    if (*slot)
      return;
  }
  history_write_integer(square, next_lo + 2u * dimension, next_hi + 2u * dimension, slot);
  next_lo[2u * dimension + 5u] = next_hi[2u * dimension + 5u] = (long)(occurrence + 1ul);
  next_lo[2u * dimension + 6u] = next_hi[2u * dimension + 6u] = (long)grain;
  next_lo[2u * dimension + 7u] = next_hi[2u * dimension + 7u] = 0l;
  if (*slot)
    return;

  W trace = wzero();
  for (uint i = 0; i < dimension; i += 2u) {
    trace = field_add_checked(trace, fromword(covariance[(ulong)i * dimension + i]), slot);
    HistoryInteger real = -history_integer(field_wire_read(next_lo, i));
    HistoryInteger imaginary = -history_integer(field_wire_read(next_lo, i + 1u));
    for (uint j = 0; j < dimension; j += 2u)
      history_complex_add_product(real, imaginary,
                                  fromword(covariance[(ulong)i * dimension + j]),
                                  fromword(covariance[(ulong)(i + 1u) * dimension + j]),
                                  field_wire_read(current, 3ul * stride + j),
                                  field_wire_read(current, 3ul * stride + j + 1ul), false);
    field_wire_write(source_lo, source_hi, 2ul * dimension + i, history_narrow(real, slot), slot);
    field_wire_write(source_lo, source_hi, 2ul * dimension + i + 1ul,
                     history_narrow(imaginary, slot), slot);
    if (*slot)
      return;
  }

  HistoryInteger bottom_real = -square, bottom_imaginary = history_zero();
  for (uint i = 0; i < dimension; i += 2u)
    history_complex_add_product(bottom_real, bottom_imaginary,
                                field_wire_read(next_lo, i), field_wire_read(next_lo, i + 1u),
                                field_wire_read(current, 3ul * stride + i),
                                field_wire_read(current, 3ul * stride + i + 1ul), true);
  history_write_integer(bottom_real, source_lo + 6u * dimension,
                        source_hi + 6u * dimension, slot);
  history_write_integer(bottom_imaginary, source_lo + 6u * dimension + 5u,
                        source_hi + 6u * dimension + 5u, slot);
  if (*slot)
    return;

  HistoryInteger norm_real = -bottom_real, norm_imaginary = bottom_imaginary;
  for (uint i = 0; i < dimension; i += 2u) {
    field_wire_write(source_lo, source_hi, i,
                     field_wire_read(current, stride + i), slot);
    field_wire_write(source_lo, source_hi, i + 1u,
                     field_wire_read(current, stride + i + 1ul), slot);
    field_wire_write(source_lo, source_hi, dimension + i,
                     field_wire_read(current, 3ul * stride + i), slot);
    field_wire_write(source_lo, source_hi, dimension + i + 1u,
                     field_wire_read(current, 3ul * stride + i + 1ul), slot);
    history_complex_add_product(norm_real, norm_imaginary,
                                field_wire_read(source_lo, i), field_wire_read(source_lo, i + 1u),
                                field_wire_read(source_lo, i), field_wire_read(source_lo, i + 1u), true);
    history_complex_add_product(norm_real, norm_imaginary,
                                field_wire_read(source_lo, 2ul * dimension + i),
                                field_wire_read(source_lo, 2ul * dimension + i + 1ul),
                                field_wire_read(source_lo, dimension + i),
                                field_wire_read(source_lo, dimension + i + 1ul), true);
    if (*slot)
      return;
  }
  if (norm_real.negative || !history_zero_p(norm_imaginary)
      || norm_imaginary.overflow || wneg_p(trace)) {
    atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED,
                             memory_order_relaxed);
    return;
  }
  history_write_integer(norm_real, source_lo + 6u * dimension + 10u,
                        source_hi + 6u * dimension + 10u, slot);
  source_lo[6u * dimension + 15u] = source_hi[6u * dimension + 15u] = (long)grain;

  W trace_root = history_source_isqrt_floor(trace, slot);
  if (*slot)
    return;
  W trace_square = field_product_checked(trace_root, trace_root, slot);
  if (*slot)
    return;
  if (!ueq(trace_square.m, trace.m))
    trace_root = field_add_checked(trace_root, wi64(1l), slot);
  W radius = field_add_checked(
      current_norm,
      field_product_checked(field_product_checked(wi64(2l), current_radius, slot), trace_root, slot),
      slot);
  if (*slot)
    return;
  field_wire_write(source_lo, source_hi, 3ul * dimension + 8ul, radius, slot);
  source_lo[6u * dimension + 18u] = source_hi[6u * dimension + 18u] = toword(trace, slot);
  source_lo[6u * dimension + 19u] = source_hi[6u * dimension + 19u] = (long)occurrence;
  field_wire_write(source_lo, source_hi, 3ul * dimension + 10ul,
                   history_norm_ceiling(norm_real, slot), slot);
}

kernel void section_field_current_history_source(
    device const long *query [[buffer(0)]], device const long *origin [[buffer(1)]],
    device const long *incoming [[buffer(2)]], device const long *frame [[buffer(3)]],
    device const long *origin_frame [[buffer(4)]], device const long *covariance [[buffer(5)]],
    device const long *before [[buffer(6)]], device const long *current [[buffer(7)]],
    device const long *state_lo [[buffer(8)]], device const long *state_hi [[buffer(9)]],
    constant uint &nodes [[buffer(10)]], constant uint &linked [[buffer(11)]],
    constant uint &grain [[buffer(12)]], constant ulong &occurrence [[buffer(13)]],
    device long *next_lo [[buffer(14)]], device long *next_hi [[buffer(15)]],
    device long *source_lo [[buffer(16)]], device long *source_hi [[buffer(17)]],
    device uint *slot [[buffer(18)]], device const uint *census [[buffer(19)]],
    device const uint *lineage [[buffer(20)]], constant uint &lineage_count [[buffer(21)]],
    threadgroup W *scratch [[threadgroup(0)]], uint3 tid [[thread_position_in_threadgroup]]) {
  if (tid.x || tid.y || tid.z)
    return;
  if (upstream(census, lineage, lineage_count, slot))
    return;
  if (!nodes || nodes > 0xffffffffu / 6u) {
    atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED,
                             memory_order_relaxed);
    return;
  }
  for (ulong i = 0; i < 12ul * (ulong)nodes + 8ul; ++i) {
    if (state_lo[i] != state_hi[i]) {
      atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED,
                               memory_order_relaxed);
      return;
    }
  }
  field_current_history_source_prepare(query, origin, incoming, frame, origin_frame, covariance,
                                       before, current, state_lo, nodes, linked, grain, occurrence,
                                       next_lo, next_hi, source_lo, source_hi, scratch, slot);
}

inline void history_pairing_value(device const long *a_lo, device const long *b_lo, uint dimension,
                                  thread HistoryInteger &real, thread HistoryInteger &imaginary,
                                  device uint *slot) {
  bool reverse = a_lo[6u * dimension + 19u] > b_lo[6u * dimension + 19u];
  device const long *old = reverse ? b_lo : a_lo;
  device const long *now = reverse ? a_lo : b_lo;
  HistoryInteger internal_real = -history_read_integer(old + 6u * dimension, slot);
  HistoryInteger internal_imaginary = history_read_integer(old + 6u * dimension + 5u, slot);
  for (uint i = 0; i < dimension; i += 2u) {
    history_complex_add_product(real, imaginary, field_wire_read(old, i),
                                field_wire_read(old, i + 1u), field_wire_read(now, i),
                                field_wire_read(now, i + 1u), true);
    history_complex_add_product(internal_real, internal_imaginary,
                                field_wire_read(old, 2u * dimension + i),
                                field_wire_read(old, 2u * dimension + i + 1u),
                                field_wire_read(now, dimension + i),
                                field_wire_read(now, dimension + i + 1u), true);
  }
  bool negative = (((ulong)old[6u * dimension + 19u]
                  + (ulong)now[6u * dimension + 19u]) & 1ul) != 0ul;
  real = real + (negative ? -internal_real : internal_real);
  imaginary = imaginary + (negative ? -internal_imaginary : internal_imaginary);
  if (reverse)
    imaginary = -imaginary;
}

kernel void section_field_current_history_pairing(
    device const long *a_lo [[buffer(0)]], device const long *a_hi [[buffer(1)]],
    device const long *b_lo [[buffer(2)]], device const long *b_hi [[buffer(3)]],
    constant uint &dimension [[buffer(4)]], device long *out_lo [[buffer(5)]],
    device long *out_hi [[buffer(6)]], device uint *slot [[buffer(7)]],
    device const uint *census [[buffer(8)]], device const uint *lineage [[buffer(9)]],
    constant uint &lineage_count [[buffer(10)]], uint3 tid [[thread_position_in_threadgroup]]) {
  if (tid.x || tid.y || tid.z)
    return;
  if (upstream(census, lineage, lineage_count, slot))
    return;
  if (!dimension || (dimension & 1u)) {
    atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED,
                             memory_order_relaxed);
    return;
  }
  for (ulong i = 0; i < 6ul * (ulong)dimension + 22ul; ++i) {
    if (a_lo[i] != a_hi[i] || b_lo[i] != b_hi[i]) {
      atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED,
                               memory_order_relaxed);
      return;
    }
  }
  if (a_lo[6u * dimension + 15u] != b_lo[6u * dimension + 15u]
      || a_lo[6u * dimension + 19u] < 0 || b_lo[6u * dimension + 19u] < 0) {
    atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED,
                             memory_order_relaxed);
    return;
  }
  HistoryInteger real = history_zero(), imaginary = history_zero();
  history_pairing_value(a_lo, b_lo, dimension, real, imaginary, slot);
  history_write_integer(real, out_lo, out_hi, slot);
  history_write_integer(imaginary, out_lo + 5, out_hi + 5, slot);
  W left_error = field_wire_read(a_lo, 3u * dimension + 8u);
  W right_error = field_wire_read(b_lo, 3u * dimension + 8u);
  W left_norm = field_wire_read(a_lo, 3u * dimension + 10u);
  W right_norm = field_wire_read(b_lo, 3u * dimension + 10u);
  if (wneg_p(left_error) || wneg_p(right_error) || wneg_p(left_norm) || wneg_p(right_norm)) {
    atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED,
                             memory_order_relaxed);
    return;
  }
  HistoryInteger error = history_integer(left_error) * history_integer(right_norm)
                       + history_integer(right_error) * history_integer(left_norm)
                       + history_integer(left_error) * history_integer(right_error);
  history_write_integer(error, out_lo + 10, out_hi + 10, slot);
}

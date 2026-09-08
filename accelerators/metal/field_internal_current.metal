// Exact resident internal-current and shared-drive primitives. This file is concatenated after
// paired/enclosed junction helpers. Input and output sections retain the CUDA wire ABI: ordinary
// i64 words stay one word per coordinate, while W carriers in doubled contact/output sections are
// encoded as two consecutive i64 words.

inline bool internal_word_fits(W a) {
  return !a.m.x[2] && !a.m.x[3]
      && !(a.m.x[1] == 0x80000000u && a.m.x[0] != 0)
      && !(a.m.x[1] == 0x80000000u && !a.neg)
      && a.m.x[1] <= 0x80000000u;
}

inline long internal_word(W a) {
  ulong magnitude = (ulong)a.m.x[0] | ((ulong)a.m.x[1] << 32);
  return as_type<long>(a.neg ? (ulong)0 - magnitude : magnitude);
}

inline void internal_current_store(thread const W *v, device long *lo, device long *hi,
                                   device uint *slot) {
  for (uint j = 0; j < 4u; ++j)
    field_wire_write(lo, hi, j, v[j], slot);
  if (*slot)
    return;
  lo[8] = hi[8] = 0;
  lo[9] = hi[9] = 0;
  lo[10] = hi[10] = 1;
  lo[11] = hi[11] = wzero_p(v[2]) ? 2 : 1;
  if (wzero_p(v[2]) && internal_word_fits(v[0]) && internal_word_fits(v[1])
      && internal_word_fits(v[3])) {
    lo[8] = hi[8] = internal_word(v[0]);
    lo[9] = hi[9] = internal_word(v[1]);
    lo[10] = hi[10] = internal_word(v[3]);
    lo[11] = hi[11] = 0;
  }
}

kernel void section_field_internal_current(
    device const long *birth [[buffer(0)]], device const long *source [[buffer(1)]],
    device const long *incoming [[buffer(2)]], device const long *birth_frame [[buffer(3)]],
    device const long *source_frame [[buffer(4)]], device const long *before [[buffer(5)]],
    device const long *before_hi [[buffer(6)]], device const long *now [[buffer(7)]],
    device const long *now_hi [[buffer(8)]], constant uint &nodes [[buffer(9)]],
    constant uint &mode [[buffer(10)]], constant uint &grain [[buffer(11)]],
    constant ulong &at [[buffer(12)]], device long *contact_lo [[buffer(13)]],
    device long *contact_hi [[buffer(14)]], device long *out_lo [[buffer(15)]],
    device long *out_hi [[buffer(16)]], device uint *slot [[buffer(17)]],
    device const uint *census [[buffer(18)]], device const uint *lineage [[buffer(19)]],
    constant uint &lineage_count [[buffer(20)]], threadgroup W *scratch [[threadgroup(0)]],
    uint3 tid [[thread_position_in_threadgroup]]) {
  if (tid.x || tid.y || tid.z)
    return;
  if (upstream(census, lineage, lineage_count, slot))
    return;
  if (!nodes || nodes > 0xffffffffu / 6u || (mode != 1u && mode != 2u)
      || (mode == 2u && (grain < 1u || grain > 120u))) {
    atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED,
                             memory_order_relaxed);
    return;
  }
  uint dimension = 6u * nodes;
  uint stride = dimension + 1u;
  uint words = (mode == 1u ? 4u : 12u) * stride;
  for (uint j = 0; j < words; ++j) {
    if (before[j] != before_hi[j] || now[j] != now_hi[j]) {
      atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED,
                               memory_order_relaxed);
      return;
    }
  }
  threadgroup W *u = scratch;
  threadgroup W *d = u + dimension;
  W u_den, d_den;
  if (!field_paired_build_faces(birth, source, incoming, birth_frame, source_frame,
                                nodes, 1u, u, d, &u_den, &d_den, slot))
    return;
  W pd = wzero(), real = wzero(), imaginary = wzero(), radius = wzero();
  if (mode == 1u) {
    W a = fromword(now[3u * stride + dimension]);
    W b = fromword(before[3u * stride + dimension]);
    if (wneg_p(a) || wzero_p(a) || wneg_p(b) || wzero_p(b)) {
      atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED,
                               memory_order_relaxed);
      return;
    }
    pd = field_lcm(a, b, slot);
    if (*slot)
      return;
    for (uint j = 0; j < dimension; ++j)
      u[j] = field_sub_checked(
          field_product_checked(fromword(now[3u * stride + j]), wdiv(pd, a, slot), slot),
          field_product_checked(fromword(before[3u * stride + j]), wdiv(pd, b, slot), slot),
          slot);
  } else {
    W a_den = field_wire_read(now, 3u * stride + dimension);
    W b_den = field_wire_read(before, 3u * stride + dimension);
    if (wneg_p(a_den) || wneg_p(b_den)) {
      atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED,
                               memory_order_relaxed);
      return;
    }
    pd.m = field_pow2(grain);
    pd.neg = false;
    W error = before == now ? wzero() : field_add_checked(a_den, b_den, slot);
    W l1 = wzero();
    for (uint j = 0; j < dimension; ++j) {
      u[j] = field_sub_checked(field_wire_read(now, 3u * stride + j),
                               field_wire_read(before, 3u * stride + j), slot);
      l1 = field_add_checked(l1, field_of_magnitude(d[j].m, false), slot);
    }
    radius = field_product_checked(l1, error, slot);
  }
  if (*slot)
    return;
  for (uint j = 0; j < dimension; j += 2u) {
    real = field_add_checked(
        real,
        field_add_checked(field_product_checked(d[j], u[j], slot),
                          field_product_checked(d[j + 1u], u[j + 1u], slot), slot),
        slot);
    imaginary = field_add_checked(
        imaginary,
        field_sub_checked(field_product_checked(d[j], u[j + 1u], slot),
                          field_product_checked(d[j + 1u], u[j], slot), slot),
        slot);
  }
  if (at & 1ul) {
    real = field_sub_checked(wzero(), real, slot);
    imaginary = field_sub_checked(wzero(), imaginary, slot);
  }
  W v[4] = {real, imaginary, radius, field_product_checked(d_den, pd, slot)};
  if (*slot)
    return;
  field_wnorm(v, 3u, &v[3], slot);
  if (*slot)
    return;
  for (uint j = 0; j < dimension; ++j)
    field_wire_write(contact_lo, contact_hi, j, d[j], slot);
  field_wire_write(contact_lo, contact_hi, dimension, d_den, slot);
  if (*slot)
    return;
  internal_current_store(v, out_lo, out_hi, slot);
}

kernel void section_internal_shared_drive(
    device const long *left [[buffer(0)]], device const long *left_hi [[buffer(1)]],
    device const long *right [[buffer(2)]], device const long *right_hi [[buffer(3)]],
    constant uint &words [[buffer(4)]], device uint *slot [[buffer(5)]],
    device const uint *census [[buffer(6)]], device const uint *lineage [[buffer(7)]],
    constant uint &lineage_count [[buffer(8)]], uint3 tid [[thread_position_in_threadgroup]]) {
  if (tid.x || tid.y || tid.z)
    return;
  if (upstream(census, lineage, lineage_count, slot))
    return;
  for (uint j = 0; j < words; ++j) {
    if (left[j] != left_hi[j] || right[j] != right_hi[j] || left[j] != right[j]) {
      atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED,
                               memory_order_relaxed);
      return;
    }
  }
}

kernel void section_internal_mode_unfold(
    device const long *origin [[buffer(0)]], device const long *origin_hi [[buffer(1)]],
    constant ulong &steps [[buffer(2)]], device long *lo [[buffer(3)]],
    device long *hi [[buffer(4)]], device uint *slot [[buffer(5)]],
    device const uint *census [[buffer(6)]], device const uint *lineage [[buffer(7)]],
    constant uint &lineage_count [[buffer(8)]], uint3 tid [[thread_position_in_threadgroup]]) {
  if (tid.x || tid.y || tid.z)
    return;
  if (upstream(census, lineage, lineage_count, slot))
    return;
  for (uint j = 0; j < 12u; ++j) {
    if (origin[j] != origin_hi[j]) {
      atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED,
                               memory_order_relaxed);
      return;
    }
  }
  W v[4] = {field_wire_read(origin, 0), field_wire_read(origin, 1),
            field_wire_read(origin, 2), field_wire_read(origin, 3)};
  if (wneg_p(v[2]) || wneg_p(v[3]) || wzero_p(v[3])) {
    atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED,
                             memory_order_relaxed);
    return;
  }
  if (steps & 1ul) {
    v[0] = field_sub_checked(wzero(), v[0], slot);
    v[1] = field_sub_checked(wzero(), v[1], slot);
  }
  if (*slot)
    return;
  internal_current_store(v, lo, hi, slot);
}

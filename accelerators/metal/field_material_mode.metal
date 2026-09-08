// Complete material mode return.  The factor table contains retained device addresses in the
// same four-word rows as the CUDA owner: increment wire, prefix wire, source cut and chronology
// cut.  Every numerical section remains the packed i64 wire; no cast to Metal W is used for a
// resident buffer.

struct FieldMaterialModeFactor {
  device const long *increment;
  device const long *prefix;
  ulong source;
  ulong cut;
};

inline uint material_mode_ball_count(uint nodes) { return 3u + 13u * (2u * nodes + 1u); }
inline ulong material_mode_ball_words(uint nodes) {
  return 2ul * (ulong)material_mode_ball_count(nodes);
}
inline W material_mode_norm(device const long *wire, ulong start, uint count,
                            device uint *slot) {
  return complete_norm(wire, 2ul * start, count, slot);
}

inline void material_mode_source(
    ulong source, ulong left, ulong right, ulong current_cut,
    device const long *contact, device const long *left_before,
    device const long *right_before, device const long *prefix,
    thread const W *mode, uint dimension, thread W &real, thread W &imaginary,
    device uint *slot) {
  real = wzero();
  imaginary = wzero();
  bool l = source >= left, r = source >= right;
  if (l && r) {
    real = mode[0];
    imaginary = mode[1];
    if ((source ^ current_cut) & 1ul) {
      real = field_sub_checked(wzero(), real, slot);
      imaginary = field_sub_checked(wzero(), imaginary, slot);
    }
    return;
  }
  if (!l && !r)
    return;
  if (!prefix) {
    atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED,
                             memory_order_relaxed);
    return;
  }
  device const long *born = l ? left_before : right_before;
  uint start = 3u * (dimension + 1u);
  for (uint j = 0; j < dimension; j += 2u) {
    W a = field_sub_checked(field_wire_read(prefix, (ulong)start + j),
                            field_wire_read(born, (ulong)start + j), slot);
    W b = field_sub_checked(field_wire_read(prefix, (ulong)start + j + 1ul),
                            field_wire_read(born, (ulong)start + j + 1ul), slot);
    W c = field_wire_read(contact, j);
    W d = field_wire_read(contact, j + 1u);
    real = field_add_checked(real,
                             field_add_checked(field_product_checked(c, a, slot),
                                               field_product_checked(d, b, slot), slot), slot);
    imaginary = field_add_checked(imaginary,
                                  field_sub_checked(field_product_checked(c, b, slot),
                                                    field_product_checked(d, a, slot), slot), slot);
  }
  if ((source & 1ul) != ((!l) ? 1ul : 0ul)) {
    real = field_sub_checked(wzero(), real, slot);
    imaginary = field_sub_checked(wzero(), imaginary, slot);
  }
}

kernel void section_complete_material_mode(
    device const long *state [[buffer(0)]], device const long *source_report [[buffer(1)]],
    device const long *refreshed [[buffer(2)]], device const long *receiving_report [[buffer(3)]],
    device const long *contact [[buffer(4)]], device const long *mode_report [[buffer(5)]],
    device const long *left_before [[buffer(6)]], device const long *right_before [[buffer(7)]],
    device const FieldMaterialModeFactor *factors [[buffer(8)]],
    constant uint &count [[buffer(9)]], constant uint &nodes [[buffer(10)]],
    constant uint &grain [[buffer(11)]], constant ulong &left [[buffer(12)]],
    constant ulong &right [[buffer(13)]], constant ulong &source_at [[buffer(14)]],
    constant ulong &current_cut [[buffer(15)]], constant ulong &mode_cut [[buffer(16)]],
    device long *out_lo [[buffer(17)]], device long *out_hi [[buffer(18)]],
    device uint *slot [[buffer(19)]], device const uint *census [[buffer(20)]],
    device const uint *lineage [[buffer(21)]], constant uint &lineage_count [[buffer(22)]],
    uint3 tid [[thread_position_in_threadgroup]]) {
  if (tid.x || tid.y || tid.z)
    return;
  if (upstream(census, lineage, lineage_count, slot))
    return;
  uint real_dimension = 6u * nodes;
  uint complex_dimension = 2u * nodes;
  uint stride = complex_dimension + 1u;
  if (!nodes || grain < 1u || grain > 120u || left == right
      || source_at < left || source_at < right || current_cut < source_at
      || mode_cut > current_cut || mode_cut < left || mode_cut < right
      || wzero_p(field_wire_read(contact, real_dimension))
      || wneg_p(field_wire_read(contact, real_dimension))
      || !ueq(field_wire_read(contact, real_dimension).m, uone())
      || wneg_p(field_wire_read(mode_report, 2u))
      || wzero_p(field_wire_read(mode_report, 3u))
      || wneg_p(field_wire_read(mode_report, 3u))) {
    atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED,
                             memory_order_relaxed);
    return;
  }
  W scale = wzero();
  scale.m = uset(scale.m, grain);
  W mode_den = field_wire_read(mode_report, 3u);
  U remainder;
  U scale_quotient = udiv(scale.m, mode_den.m, remainder);
  if (!uzero_p(remainder)) {
    atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED, memory_order_relaxed);
    return;
  }
  W multiplier = wof(scale_quotient, false, slot);
  W q[3];
  for (uint j = 0; j < 3u; ++j) {
    q[j] = field_product_checked(field_wire_read(mode_report, j), multiplier, slot);
  }
  W q_source[3] = {q[0], q[1], q[2]};
  if ((source_at ^ mode_cut) & 1ul) {
    q_source[0] = field_sub_checked(wzero(), q_source[0], slot);
    q_source[1] = field_sub_checked(wzero(), q_source[1], slot);
  }
  if (*slot)
    return;
  ulong ball_words = material_mode_ball_words(nodes);
  ulong raw_at = ball_words;
  uint ball_count = material_mode_ball_count(nodes);
  for (uint j = 0; j < ball_count; ++j)
    field_wire_write(out_lo, out_hi, j, wzero(), slot);
  for (uint j = 0; j < 3u; ++j)
    field_wire_write(out_lo, out_hi, j, q_source[j], slot);
  W kr[3] = {wzero(), wzero(), wzero()};
  W yr[3] = {wzero(), wzero(), wzero()};
  W full_rounds = wzero();
  bool changed = false, old_present = false;
  for (uint f = 0; f < count; ++f) {
    if (factors[f].cut > source_at)
      changed = true;
    else
      old_present = true;
  }
  device const long *original_exact = source_report + complete_forward_at(nodes);
  device const long *current_exact = refreshed ? refreshed : original_exact;
  for (uint row = 0; row < nodes; ++row) {
    HistoryInteger old_r = history_zero(), old_i = history_zero();
    HistoryInteger now_r = history_zero(), now_i = history_zero();
    for (uint f = 0; f < count; ++f) {
      device const long *increment = factors[f].increment;
      device const long *prefix = factors[f].prefix;
      ulong source = factors[f].source, cut = factors[f].cut;
      if (!increment || cut > current_cut || source >= cut) {
        atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED,
                                 memory_order_relaxed);
        return;
      }
      W qr, qi;
      material_mode_source(source, left, right, mode_cut, contact, left_before,
                           right_before, prefix, q, real_dimension, qr, qi, slot);
      ulong beta_at = complete_ball_words(nodes) / 2ul;
      W br = field_wire_read(increment, beta_at + 2ul * row);
      W bi = field_wire_read(increment, beta_at + 2ul * row + 1ul);
      HistoryInteger dr, di;
      complete_complex_product(history_integer(br), history_integer(bi),
                               history_integer(qr), -history_integer(qi), dr, di);
      now_r = now_r + dr;
      now_i = now_i + di;
      if (cut <= source_at) {
        old_r = old_r + dr;
        old_i = old_i + di;
      }
    }
    if (*slot)
      return;
    HistoryInteger k_r[3] = {old_r, now_r, now_r - old_r};
    HistoryInteger k_i[3] = {old_i, now_i, now_i - old_i};
    for (uint b = 0; b < 3u; ++b) {
      W real = complete_to_grid(k_r[b], grain + 1u, &kr[b], slot);
      W imag = complete_to_grid(k_i[b], grain + 1u, &kr[b], slot);
      field_wire_write(out_lo, out_hi, 3u + b * stride + 2u * row,
                       real, slot);
      field_wire_write(out_lo, out_hi, 3u + b * stride + 2u * row + 1u,
                       imag, slot);
      HistoryInteger a, z;
      complete_complex_product(k_r[b], k_i[b], history_integer(q_source[0]),
                               history_integer(q_source[1]), a, z);
      field_wire_write(out_lo, out_hi, 3u + (3u + b) * stride + 2u * row,
                       complete_to_grid(a, 2u * grain + 1u, &yr[b], slot), slot);
      field_wire_write(out_lo, out_hi, 3u + (3u + b) * stride + 2u * row + 1u,
                       complete_to_grid(z, 2u * grain + 1u, &yr[b], slot), slot);
      if (b < 2u) {
        ulong at = raw_at + 5ul * ((ulong)b * (ulong)complex_dimension
                                   + 2ul * (ulong)row);
        history_write_integer(k_r[b], out_lo + at, out_hi + at, slot);
        history_write_integer(k_i[b], out_lo + at + 5ul, out_hi + at + 5ul, slot);
      }
    }
    for (uint j = 0; j < 2u; ++j) {
      uint coord = 2u * row + j;
      HistoryInteger a = history_read_integer(original_exact + 5ul * coord, slot);
      HistoryInteger b = history_read_integer(current_exact + 5ul * coord, slot);
      W ignored = wzero();
      field_wire_write(out_lo, out_hi, 3u + 8u * stride + coord,
                       complete_to_grid(a, 2u * grain, &ignored, slot), slot);
      field_wire_write(out_lo, out_hi, 3u + 9u * stride + coord,
                       complete_to_grid(b, 2u * grain, &full_rounds, slot), slot);
      history_write_integer(a, out_lo + raw_at + 5ul * (2ul * complex_dimension + coord),
                            out_hi + raw_at + 5ul * (2ul * complex_dimension + coord), slot);
      history_write_integer(b, out_lo + raw_at + 5ul * (3ul * complex_dimension + coord),
                            out_hi + raw_at + 5ul * (3ul * complex_dimension + coord), slot);
      W original = field_wire_read(out_lo, 3u + 8u * stride + coord);
      W current = field_wire_read(out_lo, 3u + 9u * stride + coord);
      W old_forward = field_wire_read(out_lo, 3u + 3u * stride + coord);
      W new_forward = field_wire_read(out_lo, 3u + 4u * stride + coord);
      field_wire_write(out_lo, out_hi, 3u + 6u * stride + coord,
                       field_sub_checked(original, old_forward, slot), slot);
      field_wire_write(out_lo, out_hi, 3u + 7u * stride + coord,
                       field_sub_checked(current, new_forward, slot), slot);
      field_wire_write(out_lo, out_hi, 3u + 10u * stride + coord,
                       field_sub_checked(current, original, slot), slot);
      if (receiving_report) {
        W returned = field_wire_read(receiving_report, 2u * stride + coord);
        field_wire_write(out_lo, out_hi, 3u + 11u * stride + coord, returned, slot);
        field_wire_write(out_lo, out_hi, 3u + 12u * stride + coord,
                         field_sub_checked(returned, original, slot), slot);
      }
    }
  }
  if (*slot)
    return;
  W old_error = field_wire_read(source_report, complete_extra_at(nodes) / 2ul);
  W new_error = field_wire_read(state, (complete_state_words(nodes) - 4ul) / 2ul);
  W new_norm_error = field_wire_read(state, (complete_state_words(nodes) - 2ul) / 2ul);
  if (wneg_p(old_error) || wneg_p(new_error) || wneg_p(new_norm_error)) {
    atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED,
                             memory_order_relaxed);
    return;
  }
  old_error = old_present ? old_error : wzero();
  W errors[3] = {old_error,
                 changed ? new_error : old_error,
                 changed ? field_add_checked(old_error, new_error, slot) : wzero()};
  W qnorm = material_mode_norm(out_lo, 0ul, 2u, slot);
  for (uint b = 0; b < 3u; ++b) {
    W knorm = material_mode_norm(out_lo, 3ul + b * stride, complex_dimension, slot);
    knorm = field_add_checked(knorm, kr[b], slot);
    field_wire_write(out_lo, out_hi, 3u + b * stride + complex_dimension,
                     field_add_checked(errors[b], kr[b], slot), slot);
    W yterm = field_add_checked(qnorm, q_source[2], slot);
    yterm = ft_ceil_product(errors[b], yterm, grain, slot);
    W ynorm = ft_ceil_product(knorm, q_source[2], grain, slot);
    field_wire_write(out_lo, out_hi, 3u + (3u + b) * stride + complex_dimension,
                     field_add_checked(yr[b], field_add_checked(yterm, ynorm, slot), slot), slot);
  }
  field_wire_write(out_lo, out_hi, 3u + 8u * stride + complex_dimension,
                   field_wire_read(source_report, complex_dimension), slot);
  W forward_error = complete_forward_error(new_error, new_norm_error,
                                                source_report + complete_source_at(nodes),
                                                real_dimension, grain, full_rounds, slot);
  field_wire_write(out_lo, out_hi, 3u + 9u * stride + complex_dimension,
                   forward_error, slot);
  W old_forward_radius = field_wire_read(out_lo, 3u + 3u * stride + complex_dimension);
  W new_forward_radius = field_wire_read(out_lo, 3u + 4u * stride + complex_dimension);
  field_wire_write(out_lo, out_hi, 3u + 6u * stride + complex_dimension,
                   field_add_checked(old_forward_radius,
                                     field_wire_read(out_lo, 3u + 8u * stride + complex_dimension), slot), slot);
  field_wire_write(out_lo, out_hi, 3u + 7u * stride + complex_dimension,
                   field_add_checked(new_forward_radius,
                                     field_wire_read(out_lo, 3u + 9u * stride + complex_dimension), slot), slot);
  field_wire_write(out_lo, out_hi, 3u + 10u * stride + complex_dimension,
                   refreshed ? field_add_checked(field_wire_read(out_lo, 3u + 8u * stride + complex_dimension),
                                                 field_wire_read(out_lo, 3u + 9u * stride + complex_dimension), slot)
                             : wzero(), slot);
  if (receiving_report) {
    W returned_radius = field_wire_read(receiving_report, 3u * stride - 1ul);
    field_wire_write(out_lo, out_hi, 3u + 11u * stride + complex_dimension,
                     returned_radius, slot);
    field_wire_write(out_lo, out_hi, 3u + 12u * stride + complex_dimension,
                     field_add_checked(returned_radius,
                                       field_wire_read(out_lo, 3u + 8u * stride + complex_dimension), slot), slot);
  }
  if (*slot)
    return;
  // The lower endpoint is the staged result; publish the upper endpoint only after every
  // exact carrier, radius, and retained raw coefficient has passed its checks.
  for (ulong i = 0; i < (material_mode_ball_words(nodes) / 2ul); ++i) {
    out_hi[2ul * i] = out_lo[2ul * i];
    out_hi[2ul * i + 1ul] = out_lo[2ul * i + 1ul];
  }
  for (ulong i = raw_at; i < 92ul * (ulong)nodes + 32ul; ++i)
    out_hi[i] = out_lo[i];
}

kernel void section_material_mode_unfold(
    device const long *origin [[buffer(0)]], constant uint &nodes [[buffer(1)]],
    constant ulong &steps [[buffer(2)]], device long *lo [[buffer(3)]],
    device long *hi [[buffer(4)]], device uint *slot [[buffer(5)]],
    device const uint *census [[buffer(6)]], device const uint *lineage [[buffer(7)]],
    constant uint &lineage_count [[buffer(8)]],
    uint3 tid [[thread_position_in_threadgroup]]) {
  if (tid.x || tid.y || tid.z)
    return;
  if (upstream(census, lineage, lineage_count, slot))
    return;
  uint dimension = 2u * nodes;
  W radius = field_wire_read(origin, 3u + 4u * (dimension + 1u) + dimension);
  if (!nodes || wneg_p(field_wire_read(origin, 3u + 4u * (dimension + 1u) + dimension))) {
    atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED,
                             memory_order_relaxed);
    return;
  }
  for (uint i = 0; i < dimension; ++i) {
    W value = field_wire_read(origin, 3u + 4u * (dimension + 1u) + i);
    if (steps & 1ul)
      value = field_sub_checked(wzero(), value, slot);
    field_wire_write(lo, hi, i, value, slot);
  }
  field_wire_write(lo, hi, dimension, radius, slot);
}

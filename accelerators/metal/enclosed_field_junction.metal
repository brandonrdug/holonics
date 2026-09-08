// Enclosed paired-field junction.  This file is concatenated after native_phase.metal and
// paired_field_junction.metal.  W is device scratch; the resident ABI remains two signed-word
// arrays.  The implementation keeps the CUDA operation order and refuses before a carrier can
// be silently truncated.

inline W field_wire_read(device const long *wire, ulong at) {
  ulong base = 2ul * at;
  ulong low = (ulong)wire[base], high = (ulong)wire[base + 1ul];
  bool negative = ((long)high) < 0;
  if (!negative) {
    U m = uzero();
    m.x[0] = (uint)low;
    m.x[1] = (uint)(low >> 32);
    m.x[2] = (uint)high;
    m.x[3] = (uint)(high >> 32);
    W out; out.m = m; out.neg = false; return out;
  }
  ulong nlow = (ulong)0 - low;
  ulong nhigh = ~(ulong)high + (nlow == 0ul ? 1ul : 0ul);
  U m = uzero();
  m.x[0] = (uint)nlow;
  m.x[1] = (uint)(nlow >> 32);
  m.x[2] = (uint)nhigh;
  m.x[3] = (uint)(nhigh >> 32);
  W out; out.m = m; out.neg = !uzero_p(m); return out;
}

inline void field_wire_write(device long *lo, device long *hi, ulong at, W value,
                             device uint *slot) {
  ulong low = (ulong)value.m.x[0] | ((ulong)value.m.x[1] << 32);
  ulong high = (ulong)value.m.x[2] | ((ulong)value.m.x[3] << 32);
  if (value.neg) {
    ulong nlow = (ulong)0 - low;
    high = ~high + (nlow == 0ul ? 1ul : 0ul);
    low = nlow;
  }
  ulong base = 2ul * at;
  lo[base] = as_type<long>(low);
  lo[base + 1ul] = as_type<long>(high);
  hi[base] = lo[base];
  hi[base + 1ul] = lo[base + 1ul];
}

inline W field_cov_read(device const long *wire, ulong at) { return fromword(wire[at]); }

inline void field_cov_write(device long *lo, device long *hi, ulong at, W value,
                            device uint *slot) {
  long word = toword(value, slot);
  if (!*slot) lo[at] = hi[at] = word;
}

inline bool field_mag126(W a) {
  return a.m.x[3] < 0x40000000u;
}

inline bool field_mag127(W a) {
  return a.m.x[3] < 0x80000000u;
}

inline W field_of_magnitude(U magnitude, bool negative) {
  W out; out.m = magnitude; out.neg = negative && !uzero_p(magnitude); return out;
}

inline uint field_octaves(U value) {
  for (int i = 3; i >= 0; --i) if (value.x[i]) {
    uint bits = 0, limb = value.x[i];
    while (limb) { limb >>= 1; ++bits; }
    return (uint)i * 32u + bits;
  }
  return 0u;
}

inline U field_ushl(U a, uint n) {
  while (n--) {
    bool ov;
    a = ushl1(a, ov);
  }
  return a;
}

inline U field_ushr(U a, uint n) {
  while (n--) a = ushr1(a);
  return a;
}

inline U field_pow2(uint n) {
  U a = uzero();
  if (n < 128u) a = uset(a, n);
  return a;
}

inline void field_mul256(U a, U b, thread U &hi, thread U &lo) {
  uint p[8] = {0, 0, 0, 0, 0, 0, 0, 0};
  for (uint i = 0; i < 4u; ++i) {
    ulong carry = 0;
    for (uint j = 0; j < 4u; ++j) {
      ulong z = (ulong)a.x[i] * (ulong)b.x[j] + (ulong)p[i + j] + carry;
      p[i + j] = (uint)z;
      carry = z >> 32;
    }
    for (uint k = i + 4u; carry && k < 8u; ++k) {
      ulong z = (ulong)p[k] + carry;
      p[k] = (uint)z;
      carry = z >> 32;
    }
  }
  lo = uzero();
  hi = uzero();
  for (uint i = 0; i < 4u; ++i) {
    lo.x[i] = p[i];
    hi.x[i] = p[i + 4u];
  }
}

inline bool field_factor_sum(W a, W b, thread W &out) {
  if (!field_mag126(a) || !field_mag126(b)) return false;
  if (a.neg == b.neg) {
    bool ov;
    U m = uadd(a.m, b.m, ov);
    if (ov || m.x[3] >= 0x40000000u) return false;
    out = field_of_magnitude(m, a.neg);
    return true;
  }
  bool ov;
  bool right_larger = ult(a.m, b.m);
  out = field_of_magnitude(right_larger ? usub(b.m, a.m, ov) : usub(a.m, b.m, ov),
                           right_larger ? b.neg : a.neg);
  return !ov;
}

inline bool field_factor_product(W a, W b, thread W &out) {
  if (!field_mag126(a) || !field_mag126(b)) return false;
  U high, low;
  field_mul256(a.m, b.m, high, low);
  if (!uzero_p(high) || low.x[3] >= 0x40000000u) return false;
  out = field_of_magnitude(low, a.neg != b.neg);
  return true;
}

inline W field_add_checked(W a, W b, device uint *slot) {
  if (!field_mag126(a) || !field_mag126(b)) {
    atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_CARRIER, memory_order_relaxed);
    return wzero();
  }
  if (a.neg == b.neg) {
    bool ov;
    U m = uadd(a.m, b.m, ov);
    if (ov || m.x[3] >= 0x40000000u) {
      atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_CARRIER, memory_order_relaxed);
      return wzero();
    }
    return wof(m, a.neg, slot);
  }
  bool ov;
  if (ult(a.m, b.m)) return wof(usub(b.m, a.m, ov), b.neg, slot);
  return wof(usub(a.m, b.m, ov), a.neg, slot);
}

inline W field_sub_checked(W a, W b, device uint *slot) {
  return field_add_checked(a, wneg(b), slot);
}

inline W field_product_checked(W a, W b, device uint *slot) {
  // CUDA admits zero products before inspecting the other operand's magnitude.
  if (wzero_p(a) || wzero_p(b)) return wzero();
  if (!field_mag127(a) || !field_mag127(b) ||
      field_octaves(a.m) + field_octaves(b.m) > 127u) {
    atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_CARRIER, memory_order_relaxed);
    return wzero();
  }
  U high, low;
  field_mul256(a.m, b.m, high, low);
  if (!uzero_p(high) || low.x[3] >= 0x80000000u) {
    atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_CARRIER, memory_order_relaxed);
    return wzero();
  }
  return wof(low, a.neg != b.neg, slot);
}

inline W field_div_ceil(W n, W d, device uint *slot) {
  if (wneg_p(d) || wzero_p(d)) {
    atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED, memory_order_relaxed);
    return wzero();
  }
  U rem;
  U q = udiv(n.m, d.m, rem);
  if (!uzero_p(rem) && !n.neg) {
    bool ov;
    q = uadd(q, uone(), ov);
    if (ov) {
      atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_CARRIER, memory_order_relaxed);
      return wzero();
    }
  }
  return wof(q, n.neg, slot);
}

// Exact directed quotient of 2*a*b/d through a 256-bit product.
inline W field_signed_product_divide_2(W a, W b, W d, bool toward_ceiling,
                                      device uint *slot) {
  if (!field_mag126(a) || !field_mag126(b)) {
    atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_CARRIER, memory_order_relaxed);
    return wzero();
  }
  if (wneg_p(d) || wzero_p(d) || !field_mag126(d)) {
    atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED, memory_order_relaxed);
    return wzero();
  }
  U high, low;
  field_mul256(a.m, b.m, high, low);
  if (high.x[3] & 0x80000000u) {
    atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_CARRIER, memory_order_relaxed);
    return wzero();
  }
  bool ov;
  high = ushl1(high, ov);
  uint carry = low.x[3] >> 31;
  low = ushl1(low, ov);
  if (carry) high.x[0] |= 1u;
  U rem = uzero(), qhi = uzero(), qlo = uzero();
  for (int bit = 255; bit >= 0; --bit) {
    uint incoming = bit >= 128 ? ubit(high, (uint)(bit - 128)) : ubit(low, (uint)bit);
    rem = ushl1(rem, ov);
    if (incoming) rem = uset(rem, 0u);
    if (!ult(rem, d.m)) {
      rem = usub(rem, d.m, ov);
      if (bit >= 128) qhi = uset(qhi, (uint)(bit - 128));
      else qlo = uset(qlo, (uint)bit);
    }
  }
  if (!uzero_p(qhi) || qlo.x[3] >= 0x40000000u) {
    atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_CARRIER, memory_order_relaxed);
    return wzero();
  }
  bool negative = a.neg != b.neg;
  bool rounded = !uzero_p(rem);
  if (rounded && ((negative && !toward_ceiling) || (!negative && toward_ceiling))) {
    bool qov;
    qlo = uadd(qlo, uone(), qov);
    if (qov || qlo.x[3] >= 0x80000000u) {
      atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_CARRIER, memory_order_relaxed);
      return wzero();
    }
  }
  return wof(qlo, negative, slot);
}

inline W field_product_shift(W a, W b, uint k, bool toward_ceiling, device uint *slot) {
  if (k > 255u) {
    atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED, memory_order_relaxed);
    return wzero();
  }
  U high, low;
  field_mul256(a.m, b.m, high, low);
  bool discarded = false;
  U qhi = uzero(), qlo = uzero();
  if (!k) {
    qhi = high;
    qlo = low;
  } else if (k < 128u) {
    for (uint i = 0; i < k; ++i) if (ubit(low, i)) discarded = true;
    qlo = field_ushr(low, k);
    U moved = field_ushl(high, 128u - k);
    bool unused;
    qlo = uadd(qlo, moved, unused);
    qhi = field_ushr(high, k);
  } else {
    if (!uzero_p(low)) discarded = true;
    uint j = k - 128u;
    for (uint i = 0; i < j; ++i) if (ubit(high, i)) discarded = true;
    qlo = field_ushr(high, j);
  }
  if (!uzero_p(qhi) || qlo.x[3] > 0x40000000u ||
      (qlo.x[3] == 0x40000000u && (qlo.x[2] | qlo.x[1] | qlo.x[0]))) {
    atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_CARRIER, memory_order_relaxed);
    return wzero();
  }
  bool negative = a.neg != b.neg;
  if (discarded && ((negative && !toward_ceiling) || (!negative && toward_ceiling))) {
    bool ov;
    qlo = uadd(qlo, uone(), ov);
    if (ov || qlo.x[3] >= 0x80000000u) {
      atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_CARRIER, memory_order_relaxed);
      return wzero();
    }
  }
  return wof(qlo, negative, slot);
}

inline W field_enclosed_toward_zero(W numerator, W denominator, uint grain, device uint *slot) {
  if (wneg_p(denominator) || wzero_p(denominator) || !field_mag126(denominator)) {
    atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_CARRIER, memory_order_relaxed);
    return wzero();
  }
  return field_signed_product_divide_2(numerator, wof(field_pow2(grain - 1u), false, slot),
                                       denominator, numerator.neg, slot);
}

inline W field_enclosed_product_zero(W left, W right, uint grain, device uint *slot) {
  return field_product_shift(left, right, grain, left.neg != right.neg, slot);
}

inline uint field_bank_row(uint nodes, uint bank, uint port) {
  return bank < 2u ? 4u * port + 2u * bank : 4u * nodes + 2u * port;
}

// Bounded balanced reduction.  A failed eligibility check returns full-factorization kind 0
// without changing the refusal word, exactly as the CUDA owner does.
inline uint field_balanced_prepare(device const long *covariance, uint nodes, uint grain,
                                   device const W *u, device const W *h,
                                   device W *matrix, device W *rhs) {
  uint dimension = 6u * nodes;
  ulong count = (ulong)dimension * dimension;
  bool zero = true;
  for (ulong i = 0; i < count; ++i) if (covariance[i]) { zero = false; break; }
  if (zero) return 2u;
  if (!nodes || (nodes & 1u)) return 0u;
  uint pairs = nodes / 2u, bank_width = pairs + 1u, reduced = 3u * bank_width;
  W cden = fromword(covariance[count]);
  for (uint i = 0; i < dimension; i += 2u) for (uint j = 0; j < dimension; j += 2u) {
    if (covariance[(ulong)i * dimension + j + 1u] ||
        covariance[(ulong)(i + 1u) * dimension + j] ||
        covariance[(ulong)i * dimension + j] != covariance[(ulong)(i + 1u) * dimension + j + 1u]) return 0u;
  }
  for (uint bank = 0; bank < 3u; ++bank) {
    for (uint column = 0; column < dimension; column += 2u) {
      uint first = field_bank_row(nodes, bank, 0u), second = field_bank_row(nodes, bank, 1u);
      W common;
      if (!field_factor_sum(fromword(covariance[(ulong)first * dimension + column]),
                            fromword(covariance[(ulong)second * dimension + column]), common)) return 0u;
      for (uint bit = 1u; bit < pairs; ++bit) {
        uint left = field_bank_row(nodes, bank, 2u * bit), right = field_bank_row(nodes, bank, 2u * bit + 1u);
        W sum;
        if (!field_factor_sum(fromword(covariance[(ulong)left * dimension + column]),
                              fromword(covariance[(ulong)right * dimension + column]), sum) ||
            !ueq(sum.m, common.m) || sum.neg != common.neg) return 0u;
      }
    }
    for (uint plane = 0; plane < 2u; ++plane) for (uint which = 0; which < 2u; ++which) {
      device const W *input = which ? h : u;
      W common;
      if (!field_factor_sum(input[field_bank_row(nodes, bank, 0u) + plane],
                            input[field_bank_row(nodes, bank, 1u) + plane], common)) return 0u;
      for (uint bit = 1u; bit < pairs; ++bit) {
        W sum;
        if (!field_factor_sum(input[field_bank_row(nodes, bank, 2u * bit) + plane],
                              input[field_bank_row(nodes, bank, 2u * bit + 1u) + plane], sum) ||
            !ueq(sum.m, common.m) || sum.neg != common.neg) return 0u;
      }
    }
  }
  for (uint i = 0; i < reduced; ++i) {
    uint ibank = i / bank_width, ilocal = i % bank_width;
    for (uint j = 0; j < reduced; ++j) {
      uint jbank = j / bank_width, jlocal = j % bank_width;
      W value = wzero();
      uint icount = ilocal ? 2u : pairs, jcount = jlocal ? 2u : pairs;
      for (uint aa = 0; aa < icount; ++aa) {
        uint ip = ilocal ? 2u * (ilocal - 1u) + aa : 2u * aa;
        bool is_negative = ilocal && aa == 0u;
        uint ir = field_bank_row(nodes, ibank, ip);
        for (uint bb = 0; bb < jcount; ++bb) {
          uint jp = jlocal ? 2u * (jlocal - 1u) + bb : 2u * bb;
          bool js_negative = jlocal && bb == 0u;
          uint jr = field_bank_row(nodes, jbank, jp);
          W entry = fromword(covariance[(ulong)ir * dimension + jr]);
          if (ir == jr && !field_factor_sum(entry, cden, entry)) return 0u;
          W term = (is_negative == js_negative) ? entry : wneg(entry);
          if (!field_factor_sum(value, term, value)) return 0u;
        }
      }
      W scaled;
      if (!field_factor_product(value, field_of_magnitude(field_pow2(grain), false), scaled)) return 0u;
      matrix[(ulong)i * reduced + j] = scaled;
    }
  }
  for (uint plane = 0; plane < 2u; ++plane) for (uint i = 0; i < reduced; ++i) {
    uint bank = i / bank_width, local = i % bank_width, extent = local ? 2u : pairs;
    W value = wzero();
    for (uint aa = 0; aa < extent; ++aa) {
      uint port = local ? 2u * (local - 1u) + aa : 2u * aa;
      uint row = field_bank_row(nodes, bank, port) + plane;
      W sum;
      if (!field_factor_sum(u[row], h[row], sum)) return 0u;
      if (local && aa == 0u) sum = wneg(sum);
      if (!field_factor_sum(value, sum, value)) return 0u;
    }
    if (!field_factor_product(value, cden, value) ||
        !field_factor_product(value, wi64(2), value)) return 0u;
    rhs[(ulong)plane * reduced + i] = value;
  }
  return 1u;
}

inline bool field_enclosed_initialize(
    device const long *query, device const long *origin, device const long *incoming,
    device const long *frame, device const long *origin_frame, uint nodes, uint linked,
    uint grain, bool balanced, device const long *covariance, device const long *held,
    device long *next_cov_lo, device long *next_cov_hi, device long *report_lo,
    device long *report_hi, device W *workspace, device uint *slot) {
  if (!nodes || linked > 1u || grain < 1u || grain > 120u || !query || !incoming || !frame ||
      !covariance || !held || !next_cov_lo || !next_cov_hi || !report_lo || !report_hi || !workspace ||
      (linked && (!origin || !origin_frame))) {
    atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED, memory_order_relaxed);
    return false;
  }
  if (nodes > 0xffffffffu / 6u) {
    atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED, memory_order_relaxed);
    return false;
  }
  uint source_width = 4u * nodes, dimension = 6u * nodes;
  if (dimension > 0xffffffffu / dimension) {
    atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED, memory_order_relaxed);
    return false;
  }
  ulong matrix_count = (ulong)dimension * dimension;
  ulong report_segment = (ulong)dimension + 1u;
  long query_den_word = query[source_width], origin_den_word = linked ? origin[source_width] : 1;
  long covariance_den_word = covariance[matrix_count];
  W held_radius = field_wire_read(held, 2u * report_segment + dimension);
  W prefix_radius = field_wire_read(held, 3u * report_segment + dimension);
  if (query_den_word <= 0 || origin_den_word <= 0 || covariance_den_word <= 0 ||
      wneg_p(held_radius) || wneg_p(prefix_radius)) {
    atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED, memory_order_relaxed);
    return false;
  }
  device W *matrix = workspace;
  device W *u = matrix + matrix_count;
  device W *d = u + dimension;
  device W *h = d + dimension;
  device W *solve = h + dimension;
  device W *v = solve + dimension;
  device W *prefix = v + dimension;
  W u_den, d_den;
  if (!field_paired_build_faces(query, origin, incoming, frame, origin_frame, nodes, linked,
                                u, d, &u_den, &d_den, slot)) return false;
  if (!field_mag126(u_den)) {
    atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_CARRIER, memory_order_relaxed);
    return false;
  }
  W covariance_den;
  if (!field_paired_build_covariance(covariance, dimension, linked, d, d_den,
                                     matrix, &covariance_den, slot)) return false;
  for (ulong i = 0; i < matrix_count; ++i) (void)toword(matrix[i], slot);
  (void)toword(covariance_den, slot);
  if (*slot) return false;
  for (ulong i = 0; i < matrix_count; ++i) field_cov_write(next_cov_lo, next_cov_hi, i, matrix[i], slot);
  field_cov_write(next_cov_lo, next_cov_hi, matrix_count, covariance_den, slot);
  if (*slot) return false;

  W error_u = wzero();
  W scale = wof(field_pow2(grain - 1u), false, slot);
  for (uint i = 0; i < dimension; ++i) {
    h[i] = field_wire_read(held, 2u * report_segment + i);
    prefix[i] = field_wire_read(held, 3u * report_segment + i);
    W floor_value = field_signed_product_divide_2(u[i], scale, u_den, false, slot);
    W ceil_value = field_signed_product_divide_2(u[i], scale, u_den, true, slot);
    u[i] = u[i].neg ? ceil_value : floor_value;
    if (!ueq(floor_value.m, ceil_value.m) || floor_value.neg != ceil_value.neg)
      error_u = field_add_checked(error_u, wi64(1), slot);
  }
  if (*slot) return false;
  uint factor_kind = balanced ? field_balanced_prepare(next_cov_lo, nodes, grain, u, h, matrix, solve) : 0u;
  d[0] = wi64(factor_kind == 1u ? (long)(3u * (nodes / 2u + 1u)) :
             (factor_kind == 2u ? 0 : (long)dimension));
  d[1] = wi64((long)factor_kind);
  if (factor_kind == 0u) {
    for (uint i = 0; i < dimension; ++i) solve[i] = wzero();
    W full_scale = wof(field_pow2(grain), false, slot);
    W cden = field_cov_read(next_cov_lo, matrix_count);
    for (uint i = 0; i < dimension; ++i) for (uint j = 0; j < dimension; ++j) {
      W value = field_cov_read(next_cov_lo, (ulong)i * dimension + j);
      if (i == j) value = field_add_checked(value, cden, slot);
      matrix[(ulong)i * dimension + j] = field_product_checked(value, full_scale, slot);
    }
  }
  if (*slot) return false;
  field_wire_write(report_lo, report_hi, 4u * report_segment + dimension, error_u, slot);
  return !*slot;
}

inline void field_enclosed_solve(device const W *c_matrix, device const W *diagonal,
                                 uint dimension, uint grain, device W *solve, device W *v,
                                 device uint *slot) {
  for (uint i = 0; i < dimension; ++i) {
    W value = solve[i];
    for (uint j = 0; j < i; ++j)
      value = field_sub_checked(value,
          field_enclosed_product_zero(c_matrix[(ulong)i * dimension + j], solve[j], grain, slot), slot);
    solve[i] = value;
  }
  for (uint i = 0; i < dimension; ++i)
    v[i] = field_enclosed_toward_zero(solve[i], diagonal[i], grain, slot);
  for (int i = (int)dimension - 1; i >= 0; --i) {
    W value = v[i];
    for (uint j = (uint)i + 1u; j < dimension; ++j)
      value = field_sub_checked(value,
          field_enclosed_product_zero(c_matrix[(ulong)j * dimension + (uint) i], v[j], grain, slot), slot);
    v[i] = value;
  }
}

// Fraction-free enclosed LDL factorization shared by junction preparation and
// later condition contacts. Metal keeps this target's existing serial order;
// CUDA supplies the corresponding block-synchronized row updates.
inline void field_enclosed_factorize(device W *matrix, device W *diagonal,
                                     uint dimension, uint grain, device uint *slot) {
  for (uint k = 0; k < dimension; ++k) {
    W correction = wzero();
    for (uint j = 0; j < k; ++j) {
      W pair = field_enclosed_product_zero(matrix[(ulong)k * dimension + j],
                                           matrix[(ulong)k * dimension + j], grain, slot);
      correction = field_add_checked(correction,
          field_enclosed_product_zero(pair, diagonal[j], grain, slot), slot);
    }
    diagonal[k] = field_sub_checked(matrix[(ulong)k * dimension + k], correction, slot);
    if (wneg_p(diagonal[k]) || wzero_p(diagonal[k]))
      atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_CARRIER, memory_order_relaxed);
    if (*slot) return;
    for (uint i = k + 1u; i < dimension; ++i) {
      W correction_off = wzero();
      for (uint j = 0; j < k; ++j) {
        W pair = field_enclosed_product_zero(matrix[(ulong)i * dimension + j],
                                             matrix[(ulong)k * dimension + j], grain, slot);
        correction_off = field_add_checked(correction_off,
            field_enclosed_product_zero(pair, diagonal[j], grain, slot), slot);
      }
      W numerator = field_sub_checked(matrix[(ulong)k * dimension + i], correction_off, slot);
      matrix[(ulong)i * dimension + k] = field_enclosed_toward_zero(numerator, diagonal[k], grain, slot);
      if (*slot) return;
    }
  }
}

inline void field_enclosed_finish(device const long *next_cov_lo, device const long *held,
                                  uint dimension, ulong occurrence, uint grain, device W *workspace,
                                  device long *report_lo, device long *report_hi, device uint *slot) {
  ulong matrix_count = (ulong)dimension * dimension, report_segment = (ulong)dimension + 1u;
  device W *matrix = workspace;
  device W *u = matrix + matrix_count;
  device W *d = u + dimension;
  device W *h = d + dimension;
  device W *solve = h + dimension;
  device W *v = solve + dimension;
  device W *prefix = v + dimension;
  device W *diagonal = prefix + dimension;
  device W *residual = diagonal + dimension;
  W held_radius = field_wire_read(held, 2u * report_segment + dimension);
  W prefix_radius = field_wire_read(held, 3u * report_segment + dimension);
  W cden = field_cov_read(next_cov_lo, matrix_count);
  W error_u = field_wire_read(report_lo, 4u * report_segment + dimension);
  uint factor_dimension = d[0].m.x[0], factor_kind = d[1].m.x[0];
  if (factor_kind == 2u) {
    for (uint i = 0; i < dimension; ++i) v[i] = field_product_checked(wi64(2), field_add_checked(u[i], h[i], slot), slot);
  } else if (factor_kind == 1u) {
    uint nodes = dimension / 6u, pairs = nodes / 2u, bank_width = pairs + 1u;
    for (uint plane = 0; plane < 2u; ++plane) {
      field_enclosed_solve(matrix, diagonal, factor_dimension, grain,
                            solve + (ulong)plane * factor_dimension, residual, slot);
      if (*slot) return;
      for (uint bank = 0; bank < 3u; ++bank) for (uint bit = 0; bit < pairs; ++bit) {
        W common = residual[bank * bank_width], right = residual[bank * bank_width + 1u + bit];
        v[field_bank_row(nodes, bank, 2u * bit) + plane] = field_sub_checked(common, right, slot);
        v[field_bank_row(nodes, bank, 2u * bit + 1u) + plane] = right;
      }
    }
  } else {
    for (uint i = 0; i < dimension; ++i) {
      W sum = field_add_checked(u[i], h[i], slot);
      solve[i] = field_product_checked(wi64(2), field_product_checked(cden, sum, slot), slot);
    }
    if (*slot) return;
    field_enclosed_solve(matrix, diagonal, dimension, grain, solve, v, slot);
  }
  if (*slot) return;

  W residual_sum = wzero();
  for (uint i = 0; i < dimension; ++i) {
    W lhs = field_product_checked(cden, v[i], slot);
    for (uint j = 0; j < dimension; ++j)
      lhs = field_add_checked(lhs,
          field_product_checked(field_cov_read(next_cov_lo, (ulong)i * dimension + j), v[j], slot), slot);
    W rhs = field_product_checked(wi64(2), field_product_checked(cden,
        field_add_checked(u[i], h[i], slot), slot), slot);
    residual[i] = field_sub_checked(lhs, rhs, slot);
    W abs_value = residual[i]; abs_value.neg = false;
    residual_sum = field_add_checked(residual_sum, abs_value, slot);
  }
  if (*slot) return;
  W residual_radius = field_div_ceil(residual_sum, cden, slot);
  W radius_v = field_add_checked(field_product_checked(wi64(2), held_radius, slot),
      field_add_checked(field_product_checked(wi64(2), error_u, slot), residual_radius, slot), slot);
  W radius_b = field_add_checked(field_product_checked(wi64(2), held_radius, slot),
      field_add_checked(error_u, residual_radius, slot), slot);
  W radius_h = field_add_checked(held_radius,
      field_add_checked(field_product_checked(wi64(2), error_u, slot), residual_radius, slot), slot);
  W radius_prefix = field_add_checked(prefix_radius, radius_v, slot);
  if (*slot) return;
  for (uint i = 0; i < dimension; ++i) {
    solve[i] = field_sub_checked(v[i], u[i], slot);
    h[i] = field_sub_checked(field_add_checked(field_product_checked(wi64(2), u[i], slot), h[i], slot), v[i], slot);
    prefix[i] = (occurrence & 1u) ? field_sub_checked(prefix[i], v[i], slot)
                                  : field_add_checked(prefix[i], v[i], slot);
  }
  if (*slot) return;
  for (uint i = 0; i < dimension; ++i) {
    field_wire_write(report_lo, report_hi, i, v[i], slot);
    field_wire_write(report_lo, report_hi, report_segment + i, solve[i], slot);
    field_wire_write(report_lo, report_hi, 2u * report_segment + i, h[i], slot);
    field_wire_write(report_lo, report_hi, 3u * report_segment + i, prefix[i], slot);
    field_wire_write(report_lo, report_hi, 4u * report_segment + i, u[i], slot);
    field_wire_write(report_lo, report_hi, 5u * report_segment + i, residual[i], slot);
  }
  field_wire_write(report_lo, report_hi, dimension, radius_v, slot);
  field_wire_write(report_lo, report_hi, report_segment + dimension, radius_b, slot);
  field_wire_write(report_lo, report_hi, 2u * report_segment + dimension, radius_h, slot);
  field_wire_write(report_lo, report_hi, 3u * report_segment + dimension, radius_prefix, slot);
  field_wire_write(report_lo, report_hi, 4u * report_segment + dimension, error_u, slot);
  field_wire_write(report_lo, report_hi, 5u * report_segment + dimension, cden, slot);
}

inline void field_enclosed_junction_prepare(
    device const long *query, device const long *origin, device const long *incoming,
    device const long *frame, device const long *origin_frame, uint nodes, uint linked,
    ulong occurrence, uint grain, bool balanced, device const long *covariance,
    device const long *held, device long *next_cov_lo, device long *next_cov_hi,
    device long *report_lo, device long *report_hi, device W *workspace, device uint *slot) {
  if (!slot) return;
  if (!field_enclosed_initialize(query, origin, incoming, frame, origin_frame, nodes, linked,
                                 grain, balanced, covariance, held, next_cov_lo, next_cov_hi,
                                 report_lo, report_hi, workspace, slot) || *slot) return;
  uint dimension = 6u * nodes;
  ulong matrix_count = (ulong)dimension * dimension;
  device W *matrix = workspace;
  device W *u = matrix + matrix_count;
  device W *d = u + dimension;
  device W *h = d + dimension;
  device W *solve = h + dimension;
  device W *v = solve + dimension;
  device W *prefix = v + dimension;
  device W *diagonal = prefix + dimension;
  (void)u; (void)h; (void)solve; (void)v; (void)prefix;
  uint factor_dimension = d[0].m.x[0];
  field_enclosed_factorize(matrix, diagonal, factor_dimension, grain, slot);
  if (*slot) return;
  if (!*slot) field_enclosed_finish(next_cov_lo, held, dimension, occurrence, grain, workspace,
                                    report_lo, report_hi, slot);
}

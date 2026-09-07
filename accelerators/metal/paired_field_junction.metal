// Source-neutral paired passive junction for a resident constitutive field.
//
// This file is concatenated after native_phase.metal. All numerical work remains
// in the resident W chart; only the final covariance and report faces return to
// the signed i64 wire.

// The junction follows the shared CUDA carrier admission, including its conservative
// product bound and 126-bit checked sums. Definitions are in the enclosed helper file.
inline W field_add_checked(W a, W b, device uint *slot);
inline W field_sub_checked(W a, W b, device uint *slot);
inline W field_product_checked(W a, W b, device uint *slot);

inline W field_lcm(W a, W b, device uint *slot) {
  if (wneg_p(a) || wneg_p(b) || wzero_p(a) || wzero_p(b)) {
    atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED, memory_order_relaxed);
    return wi64(1);
  }
  return field_product_checked(wdiv(a, wgcd(a, b, slot), slot), b, slot);
}

inline void field_phase_product(W ar, W ai, W ad, W br, W bi, W bd,
                                thread W *out, device uint *slot) {
  if (wneg_p(ad) || wzero_p(ad) || wneg_p(bd) || wzero_p(bd)) {
    atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED, memory_order_relaxed);
    return;
  }
  out[0] = field_sub_checked(field_product_checked(ar, br, slot),
                             field_product_checked(ai, bi, slot), slot);
  out[1] = field_add_checked(field_product_checked(ar, bi, slot),
                             field_product_checked(ai, br, slot), slot);
  out[2] = field_product_checked(ad, bd, slot);
  if (*slot) return;
  wnorm(out, 2, out + 2, slot);
}

inline W field_wnorm(device W *row, uint width, thread W *den, device uint *slot) {
  W d = den ? (!wzero_p(*den) ? *den : wzero()) : wzero();
  for (uint j = 0; j < width && !ueq(d.m, uone()); ++j)
    d = wgcd(d, row[j], slot);
  if (wzero_p(d) || ueq(d.m, uone()))
    return d;
  for (uint j = 0; j < width; ++j)
    row[j] = wdiv(row[j], d, slot);
  if (den)
    *den = wdiv(*den, d, slot);
  return d;
}

// Exact division used by the fraction-free solve. wdiv is intentionally a
// directed quotient helper, so this path checks and rejects every nonzero
// remainder before accepting a Bareiss step.
inline bool field_exact_divide(W numerator, W denominator, thread W *quotient,
                               device uint *slot) {
  if (wzero_p(denominator)) {
    atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED,
                             memory_order_relaxed);
    return false;
  }
  U remainder;
  U q = udiv(numerator.m, denominator.m, remainder);
  if (!uzero_p(remainder)) {
    atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED,
                             memory_order_relaxed);
    return false;
  }
  *quotient = wof(q, numerator.neg != denominator.neg, slot);
  return *slot == 0;
}

// Common source/contact assembly for exact and enclosed representations. The
// target half of u is zero and the target half of d is the negative root field.
inline bool field_paired_build_faces(
    device const long *query, device const long *origin, device const long *incoming,
    device const long *frame, device const long *origin_frame,
    uint nodes, uint linked, device W *u, device W *d,
    thread W *u_den_out, thread W *d_den_out, device uint *slot) {
  if (!nodes || linked > 1 || !query || !incoming || !frame || !u || !d
      || !u_den_out || !d_den_out || (linked && (!origin || !origin_frame))) {
    atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED,
                             memory_order_relaxed);
    return false;
  }
  uint source_width = 4u * nodes;
  uint dimension = 6u * nodes;
  long query_den_word = query[source_width];
  long origin_den_word = linked ? origin[source_width] : 1;
  if (query_den_word <= 0 || origin_den_word <= 0) {
    atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED,
                             memory_order_relaxed);
    return false;
  }
  W query_den = fromword(query_den_word), origin_den = fromword(origin_den_word);
  W u_den = wi64(1), d_den = wi64(1);
  for (uint node = 0; node < nodes; ++node) {
    device const long *now = frame + 3u * node;
    W now_real = fromword(now[0]), now_imaginary = fromword(now[1]), now_den = fromword(now[2]);
    W now_norm = field_add_checked(field_product_checked(now_real, now_real, slot), field_product_checked(now_imaginary, now_imaginary, slot), slot);
    W now_squared_den = field_product_checked(now_den, now_den, slot);
    if (*slot)
      return false;
    if (now[2] <= 0 || !ueq(now_norm.m, now_squared_den.m) || now_norm.neg != now_squared_den.neg) {
      atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED,
                               memory_order_relaxed);
      return false;
    }
    device const long *before = linked ? origin_frame + 3u * node : nullptr;
    if (linked) {
      W before_real = fromword(before[0]), before_imaginary = fromword(before[1]);
      W before_den = fromword(before[2]);
      W before_norm = field_add_checked(field_product_checked(before_real, before_real, slot),
                           field_product_checked(before_imaginary, before_imaginary, slot), slot);
      W before_squared_den = field_product_checked(before_den, before_den, slot);
      if (*slot)
        return false;
      if (before[2] <= 0 || !ueq(before_norm.m, before_squared_den.m)
          || before_norm.neg != before_squared_den.neg) {
        atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED,
                                 memory_order_relaxed);
        return false;
      }
    }
    for (uint branch = 0; branch < 2u; ++branch) {
      W turned[3];
      field_phase_product(now_real, wneg(now_imaginary), now_den,
                fromword(query[4u * node + 2u * branch]),
                fromword(query[4u * node + 2u * branch + 1u]), query_den, turned, slot);
      if (*slot)
        return false;
      u_den = field_lcm(u_den, turned[2], slot);
      if (linked) {
        W old_turned[3];
        field_phase_product(fromword(before[0]), wneg(fromword(before[1])), fromword(before[2]),
                  fromword(origin[4u * node + 2u * branch]),
                  fromword(origin[4u * node + 2u * branch + 1u]), origin_den,
                  old_turned, slot);
        if (*slot)
          return false;
        d_den = field_lcm(d_den, old_turned[2], slot);
      }
    }
  }
  for (uint node = 0; node < nodes; ++node) {
    device const long *arrived = incoming + 3u * node;
    if (arrived[2] <= 0) {
      atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED,
                               memory_order_relaxed);
      return false;
    }
    if (linked)
      d_den = field_lcm(d_den, fromword(arrived[2]), slot);
  }
  if (*slot)
    return false;
  for (uint node = 0; node < nodes; ++node) {
    device const long *now = frame + 3u * node;
    device const long *before = linked ? origin_frame + 3u * node : nullptr;
    for (uint branch = 0; branch < 2u; ++branch) {
      W turned[3];
      field_phase_product(fromword(now[0]), wneg(fromword(now[1])), fromword(now[2]),
                fromword(query[4u * node + 2u * branch]),
                fromword(query[4u * node + 2u * branch + 1u]), query_den, turned, slot);
      u[4u * node + 2u * branch] = field_product_checked(turned[0], wdiv(u_den, turned[2], slot), slot);
      u[4u * node + 2u * branch + 1u] = field_product_checked(turned[1], wdiv(u_den, turned[2], slot), slot);
      if (linked) {
        W old_turned[3];
        field_phase_product(fromword(before[0]), wneg(fromword(before[1])), fromword(before[2]),
                  fromword(origin[4u * node + 2u * branch]),
                  fromword(origin[4u * node + 2u * branch + 1u]), origin_den,
                  old_turned, slot);
        d[4u * node + 2u * branch] = field_product_checked(old_turned[0], wdiv(d_den, old_turned[2], slot), slot);
        d[4u * node + 2u * branch + 1u] = field_product_checked(old_turned[1], wdiv(d_den, old_turned[2], slot), slot);
      } else {
        d[4u * node + 2u * branch] = d[4u * node + 2u * branch + 1u] = wzero();
      }
    }
    device const long *arrived = incoming + 3u * node;
    if (linked) {
      d[source_width + 2u * node] = wneg(field_product_checked(fromword(arrived[0]),
                                               wdiv(d_den, fromword(arrived[2]), slot), slot));
      d[source_width + 2u * node + 1u] = wneg(field_product_checked(fromword(arrived[1]),
                                                   wdiv(d_den, fromword(arrived[2]), slot), slot));
    } else {
      d[source_width + 2u * node] = d[source_width + 2u * node + 1u] = wzero();
    }
    u[source_width + 2u * node] = u[source_width + 2u * node + 1u] = wzero();
  }
  if (*slot)
    return false;
  field_wnorm(u, dimension, &u_den, slot);
  if (linked)
    field_wnorm(d, dimension, &d_den, slot);
  if (*slot)
    return false;
  *u_den_out = u_den;
  *d_den_out = d_den;
  return true;
}

// Common exact covariance update. Matrix storage is resident W; its denominator
// is returned separately for the exact and enclosed consumers.
inline bool field_paired_build_covariance(
    device const long *covariance, uint dimension, uint linked,
    device const W *d, W d_den, device W *matrix, thread W *den_out, device uint *slot) {
  if (!covariance || !d || !matrix || !den_out || !dimension || linked > 1
      || dimension > 0xffffffffu / dimension) {
    atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED,
                             memory_order_relaxed);
    return false;
  }
  ulong count = (ulong)dimension * dimension;
  long old_den_word = covariance[count];
  if (old_den_word <= 0 || wzero_p(d_den) || wneg_p(d_den)) {
    atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED,
                             memory_order_relaxed);
    return false;
  }
  W old_den = fromword(old_den_word);
  W residual_square_den = field_product_checked(d_den, d_den, slot);
  W next_den = linked ? field_lcm(old_den, residual_square_den, slot) : old_den;
  if (*slot)
    return false;
  for (uint i = 0; i < dimension; ++i)
    for (uint j = 0; j < dimension; ++j) {
      ulong ij = (ulong)i * dimension + j, ji = (ulong)j * dimension + i;
      if (covariance[ij] != covariance[ji]) {
        atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED,
                                 memory_order_relaxed);
        return false;
      }
      W value = field_product_checked(fromword(covariance[ij]), wdiv(next_den, old_den, slot), slot);
      if (linked) {
        uint ipair = i / 2u, jpair = j / 2u;
        W ji_value = (i & 1u) ? d[2u * ipair] : wneg(d[2u * ipair + 1u]);
        W jj_value = (j & 1u) ? d[2u * jpair] : wneg(d[2u * jpair + 1u]);
        W gram = field_add_checked(field_product_checked(d[i], d[j], slot), field_product_checked(ji_value, jj_value, slot), slot);
        value = field_add_checked(value, field_product_checked(gram, wdiv(next_den, residual_square_den, slot), slot), slot);
      }
      matrix[ij] = value;
    }
  if (*slot)
    return false;
  field_wnorm(matrix, (uint)count, &next_den, slot);
  if (*slot)
    return false;
  *den_out = next_den;
  return true;
}

// Exact resident paired-junction preparation. The matrix and all intermediate
// faces stay in the device W workspace until every output word is validated.
inline void field_paired_junction_prepare(
    device const long *query, device const long *origin, device const long *incoming,
    device const long *frame, device const long *origin_frame,
    uint nodes, uint linked, ulong occurrence,
    device const long *covariance, device const long *held,
    device long *next_cov_lo, device long *next_cov_hi,
    device long *report_lo, device long *report_hi,
    device W *workspace, device uint *slot) {
  if (!slot)
    return;
  if (!nodes || linked > 1 || !query || !incoming || !frame || !covariance || !held
      || !next_cov_lo || !next_cov_hi || !report_lo || !report_hi || !workspace
      || (linked && (!origin || !origin_frame)) || nodes > 0xffffffffu / 6u) {
    atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED,
                             memory_order_relaxed);
    return;
  }
  uint source_width = 4u * nodes, dimension = 6u * nodes;
  if (dimension > 0xffffffffu / dimension) {
    atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED, memory_order_relaxed);
    return;
  }
  ulong matrix_count = (ulong)dimension * dimension;
  uint report_segment = dimension + 1u;
  long query_den_word = query[source_width];
  long origin_den_word = linked ? origin[source_width] : 1;
  long covariance_den_word = covariance[matrix_count];
  long held_den_word = held[2u * report_segment + dimension];
  long prefix_den_word = held[3u * report_segment + dimension];
  if (query_den_word <= 0 || origin_den_word <= 0 || covariance_den_word <= 0
      || held_den_word <= 0 || prefix_den_word <= 0) {
    atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED,
                             memory_order_relaxed);
    return;
  }
  device W *matrix = workspace;
  device W *rhs = matrix + matrix_count;
  device W *u = rhs + dimension;
  device W *d = u + dimension;
  device W *h = d + dimension;
  device W *b = h + dimension;
  device W *v = b + dimension;
  device W *prefix = v + dimension;
  for (uint i = 0; i < dimension; ++i)
    rhs[i] = wzero();

  W current_den = wi64(1), residual_den = wi64(1);
  if (!field_paired_build_faces(query, origin, incoming, frame, origin_frame,
                                nodes, linked, u, d, &current_den, &residual_den, slot))
    return;
  for (uint j = 0; j < dimension; ++j) {
    h[j] = fromword(held[2u * report_segment + j]);
    prefix[j] = fromword(held[3u * report_segment + j]);
  }
  W held_den = fromword(held_den_word), prefix_den = fromword(prefix_den_word);
  field_wnorm(h, dimension, &held_den, slot);
  field_wnorm(prefix, dimension, &prefix_den, slot);
  if (*slot)
    return;
  W checked_cov_den;
  if (!field_paired_build_covariance(covariance, dimension, linked, d, residual_den,
                                     matrix, &checked_cov_den, slot))
    return;
  for (ulong j = 0; j < matrix_count; ++j)
    matrix[j] = wi64(toword(matrix[j], slot));
  checked_cov_den = wi64(toword(checked_cov_den, slot));
  if (*slot)
    return;
  for (ulong j = 0; j < matrix_count; ++j)
    next_cov_lo[j] = next_cov_hi[j] = toword(matrix[j], slot);
  next_cov_lo[matrix_count] = next_cov_hi[matrix_count] = toword(checked_cov_den, slot);
  if (*slot)
    return;

  W rhs_den = field_lcm(current_den, held_den, slot);
  if (*slot)
    return;
  for (uint i = 0; i < dimension; ++i) {
    W combined = field_add_checked(field_product_checked(u[i], wdiv(rhs_den, current_den, slot), slot),
                      field_product_checked(h[i], wdiv(rhs_den, held_den, slot), slot), slot);
    rhs[i] = field_product_checked(wi64(2), field_product_checked(checked_cov_den, combined, slot), slot);
  }
  if (*slot)
    return;
  for (uint i = 0; i < dimension; ++i)
    matrix[(ulong)i * dimension + i] = field_add_checked(matrix[(ulong)i * dimension + i], checked_cov_den, slot);
  if (*slot)
    return;

  W previous = wi64(1);
  for (uint pivot_index = 0; pivot_index + 1u < dimension; ++pivot_index) {
    W pivot = matrix[(ulong)pivot_index * dimension + pivot_index];
    if (wzero_p(pivot) || wneg_p(pivot) || wzero_p(previous) || wneg_p(previous)) {
      atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED,
                               memory_order_relaxed);
      return;
    }
    for (uint i = pivot_index + 1u; i < dimension; ++i) {
      for (uint j = pivot_index + 1u; j < dimension; ++j) {
        W numerator = field_sub_checked(field_product_checked(pivot, matrix[(ulong)i * dimension + j], slot),
                           field_product_checked(matrix[(ulong)i * dimension + pivot_index],
                                matrix[(ulong)pivot_index * dimension + j], slot), slot);
        if (*slot)
          return;
        W quotient;
        if (!field_exact_divide(numerator, previous, &quotient, slot))
          return;
        matrix[(ulong)i * dimension + j] = quotient;
      }
      W rhs_numerator = field_sub_checked(field_product_checked(pivot, rhs[i], slot),
                             field_product_checked(matrix[(ulong)i * dimension + pivot_index], rhs[pivot_index], slot), slot);
      if (*slot)
        return;
      W quotient;
      if (!field_exact_divide(rhs_numerator, previous, &quotient, slot))
        return;
      rhs[i] = quotient;
    }
    previous = pivot;
  }
  W determinant = matrix[(ulong)(dimension - 1u) * dimension + dimension - 1u];
  if (wzero_p(determinant) || wneg_p(determinant)) {
    atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED,
                             memory_order_relaxed);
    return;
  }
  for (int i = (int)dimension - 1; i >= 0; --i) {
    W numerator = field_product_checked(rhs[i], determinant, slot);
    for (uint j = (uint)i + 1u; j < dimension; ++j)
      numerator = field_sub_checked(numerator, field_product_checked(matrix[(ulong)i * dimension + j], v[j], slot), slot);
    W diagonal = matrix[(ulong)i * dimension + (uint)i];
    if (*slot)
      return;
    W solved;
    if (!field_exact_divide(numerator, diagonal, &solved, slot))
      return;
    v[i] = solved;
  }
  W v_den = field_product_checked(determinant, rhs_den, slot);
  if (*slot)
    return;
  field_wnorm(v, dimension, &v_den, slot);
  if (*slot)
    return;

  W reaction_den = field_lcm(current_den, held_den, slot);
  reaction_den = field_lcm(reaction_den, v_den, slot);
  if (*slot)
    return;
  for (uint i = 0; i < dimension; ++i) {
    W vi = field_product_checked(v[i], wdiv(reaction_den, v_den, slot), slot);
    W ui = field_product_checked(u[i], wdiv(reaction_den, current_den, slot), slot);
    W hi = field_product_checked(h[i], wdiv(reaction_den, held_den, slot), slot);
    b[i] = field_sub_checked(vi, ui, slot);
    h[i] = field_sub_checked(field_add_checked(field_product_checked(wi64(2), ui, slot), hi, slot), vi, slot);
  }
  W b_den = reaction_den;
  field_wnorm(b, dimension, &b_den, slot);
  W h_new_den = reaction_den;
  field_wnorm(h, dimension, &h_new_den, slot);
  W prefix_new_den = field_lcm(prefix_den, v_den, slot);
  for (uint i = 0; i < dimension; ++i) {
    W old_p = field_product_checked(prefix[i], wdiv(prefix_new_den, prefix_den, slot), slot);
    W new_v = field_product_checked(v[i], wdiv(prefix_new_den, v_den, slot), slot);
    prefix[i] = (occurrence & 1ul) ? field_sub_checked(old_p, new_v, slot) : field_add_checked(old_p, new_v, slot);
  }
  field_wnorm(prefix, dimension, &prefix_new_den, slot);
  if (*slot)
    return;

  for (uint i = 0; i < dimension; ++i) {
    long vv = toword(v[i], slot), bb = toword(b[i], slot), hh = toword(h[i], slot);
    long pp = toword(prefix[i], slot);
    v[i] = wi64(vv); b[i] = wi64(bb); h[i] = wi64(hh); prefix[i] = wi64(pp);
  }
  W checked_v_den = wi64(toword(v_den, slot));
  W checked_b_den = wi64(toword(b_den, slot));
  W checked_h_den = wi64(toword(h_new_den, slot));
  W checked_prefix_den = wi64(toword(prefix_new_den, slot));
  if (*slot)
    return;
  for (uint i = 0; i < dimension; ++i) {
    report_lo[i] = report_hi[i] = toword(v[i], slot);
    report_lo[report_segment + i] = report_hi[report_segment + i] = toword(b[i], slot);
    report_lo[2u * report_segment + i] = report_hi[2u * report_segment + i] = toword(h[i], slot);
    report_lo[3u * report_segment + i] = report_hi[3u * report_segment + i] = toword(prefix[i], slot);
  }
  report_lo[dimension] = report_hi[dimension] = toword(checked_v_den, slot);
  report_lo[report_segment + dimension] = report_hi[report_segment + dimension] = toword(checked_b_den, slot);
  report_lo[2u * report_segment + dimension] = report_hi[2u * report_segment + dimension] = toword(checked_h_den, slot);
  report_lo[3u * report_segment + dimension] = report_hi[3u * report_segment + dimension] = toword(checked_prefix_den, slot);
}

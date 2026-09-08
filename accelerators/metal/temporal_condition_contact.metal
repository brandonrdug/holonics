// Structured temporal unit-admittance contact. The point source and observation remain complete
// resident views; the dyadic prior and all eight returned normal/report blocks stay on the card.

inline W temporal_condition_prior(device const long *lo, uint at) {
  return field_wire_read(lo, at);
}

inline void temporal_condition_store(device long *lo, device long *hi, uint at, W value,
                                     device uint *slot) {
  field_wire_write(lo, hi, at, value, slot);
}

kernel void section_temporal_condition_contact_validate(
    device const long *x_lo [[buffer(0)]], device const long *x_hi [[buffer(1)]],
    constant uint &x_at [[buffer(2)]], constant uint &x_denominator_at [[buffer(3)]],
    constant uint &x_disposition_at [[buffer(4)]], device const long *y_lo [[buffer(5)]],
    device const long *y_hi [[buffer(6)]], constant uint &y_at [[buffer(7)]],
    constant uint &y_denominator_at [[buffer(8)]], constant uint &y_disposition_at [[buffer(9)]],
    constant uint &x_complex_coordinates [[buffer(10)]], constant uint &y_complex_coordinates [[buffer(11)]],
    constant uint &source_extent [[buffer(12)]], constant uint &response_complex [[buffer(13)]],
    constant uint &prediction_from [[buffer(14)]], constant uint &observed_from [[buffer(15)]],
    constant uint &observed_extent [[buffer(16)]], device const long *prior_lo [[buffer(17)]],
    device const long *prior_hi [[buffer(18)]], constant uint &prior_wide_at [[buffer(19)]],
    constant uint &prior_radius_wide_at [[buffer(20)]], constant uint &grain [[buffer(21)]],
    device W *workspace [[buffer(22)]], device long *report_lo [[buffer(23)]],
    device long *report_hi [[buffer(24)]], device uint *slot [[buffer(25)]],
    device const uint *census [[buffer(26)]], device const uint *lineage [[buffer(27)]],
    constant uint &lineage_count [[buffer(28)]], constant uint &observed_raw_extent [[buffer(29)]],
    uint gid [[thread_position_in_grid]]) {
  if (gid != 0 || *slot || upstream(census, lineage, lineage_count, slot)) return;
  ulong x_count = (ulong)x_complex_coordinates, y_count = (ulong)y_complex_coordinates;
  ulong n = (ulong)source_extent, k_count = (ulong)response_complex;
  ulong p = (ulong)prediction_from, o = (ulong)observed_from, length = (ulong)observed_extent;
  ulong prediction_extent = n + k_count - 1ul;
  if (!x_count || !y_count || !n || !k_count || !length || !prior_lo || !prior_hi || !workspace
      || !report_lo || !report_hi || grain < 1u || grain > 120u || k_count > 0x3ffffffful
      || x_count > 0x7ffffffful || y_count > 0x7ffffffful || n > x_count
      || !observed_raw_extent || observed_raw_extent > y_count
      || length > observed_raw_extent || p + length > prediction_extent
      || o + length > observed_raw_extent || k_count > 0x7ffffffful) {
    atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED, memory_order_relaxed);
    return;
  }
  uint dimension = 2u * (uint)k_count;
  if ((ulong)dimension * dimension > 0xfffffffful
      || (ulong)x_at + 2ul * x_count > 0xfffffffful
      || (ulong)y_at + 2ul * y_count > 0xfffffffful
      || (ulong)prior_wide_at + dimension + 1ul > 0x7ffffffful
      || (ulong)prior_radius_wide_at != (ulong)prior_wide_at + dimension) {
    atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED, memory_order_relaxed);
    return;
  }
  W xd = fibre_current_denominator(x_lo, x_hi, x_denominator_at, x_disposition_at, slot);
  W yd = fibre_current_denominator(y_lo, y_hi, y_denominator_at, y_disposition_at, slot);
  if (*slot || wneg_p(xd) || wzero_p(xd) || wneg_p(yd) || wzero_p(yd)) return;
  for (ulong coordinate = 0; coordinate < x_count; ++coordinate) {
    ulong at64 = (ulong)x_at + 2ul * coordinate;
    uint at = (uint)at64;
    if (x_lo[at] != x_hi[at] || x_lo[at + 1u] != x_hi[at + 1u]
        || (coordinate >= n && (x_lo[at] != 0 || x_lo[at + 1u] != 0))) {
      atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED, memory_order_relaxed);
      return;
    }
  }
  for (ulong coordinate = 0; coordinate < y_count; ++coordinate) {
    ulong at64 = (ulong)y_at + 2ul * coordinate;
    uint at = (uint)at64;
    if (y_lo[at] != y_hi[at] || y_lo[at + 1u] != y_hi[at + 1u]
        || (coordinate >= observed_raw_extent && (y_lo[at] != 0 || y_lo[at + 1u] != 0))) {
      atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED, memory_order_relaxed);
      return;
    }
  }
  for (uint j = 0; j <= dimension; ++j) {
    uint at = prior_wide_at + j;
    ulong base = 2ul * (ulong)at;
    if (prior_lo[base] != prior_hi[base] || prior_lo[base + 1ul] != prior_hi[base + 1ul]) {
      atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED, memory_order_relaxed);
      return;
    }
  }
  W prior_radius = temporal_condition_prior(prior_lo, prior_radius_wide_at);
  if (wneg_p(prior_radius)) {
    atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED, memory_order_relaxed);
    return;
  }
  W gcd = wgcd(xd, yd, slot);
  if (*slot || wzero_p(gcd)) return;
  W px = wdiv(xd, gcd, slot), py = wdiv(yd, gcd, slot);
  W cden = field_product_checked(xd, xd, slot);
  if (*slot || wneg_p(px) || wzero_p(px) || wneg_p(py) || wzero_p(py)
      || wneg_p(cden) || wzero_p(cden)) return;
  uint scalar_at = 2u * dimension * dimension + 6u * dimension;
  workspace[scalar_at] = xd;
  workspace[scalar_at + 1u] = yd;
  workspace[scalar_at + 2u] = px;
  workspace[scalar_at + 3u] = py;
  workspace[scalar_at + 4u] = cden;
}

kernel void section_temporal_condition_contact_gram(
    device const long *x_lo [[buffer(0)]], device const long *x_hi [[buffer(1)]],
    constant uint &x_at [[buffer(2)]], constant uint &x_denominator_at [[buffer(3)]],
    constant uint &x_disposition_at [[buffer(4)]], device const long *y_lo [[buffer(5)]],
    device const long *y_hi [[buffer(6)]], constant uint &y_at [[buffer(7)]],
    constant uint &y_denominator_at [[buffer(8)]], constant uint &y_disposition_at [[buffer(9)]],
    constant uint &x_complex_coordinates [[buffer(10)]], constant uint &y_complex_coordinates [[buffer(11)]],
    constant uint &source_extent [[buffer(12)]], constant uint &response_complex [[buffer(13)]],
    constant uint &prediction_from [[buffer(14)]], constant uint &observed_from [[buffer(15)]],
    constant uint &observed_extent [[buffer(16)]], device const long *prior_lo [[buffer(17)]],
    device const long *prior_hi [[buffer(18)]], constant uint &prior_wide_at [[buffer(19)]],
    constant uint &prior_radius_wide_at [[buffer(20)]], constant uint &grain [[buffer(21)]],
    device W *workspace [[buffer(22)]], device long *report_lo [[buffer(23)]],
    device long *report_hi [[buffer(24)]], device uint *slot [[buffer(25)]],
    device const uint *census [[buffer(26)]], device const uint *lineage [[buffer(27)]],
    constant uint &lineage_count [[buffer(28)]], constant uint &observed_raw_extent [[buffer(29)]],
    uint gid [[thread_position_in_grid]]) {
  (void)x_hi; (void)x_denominator_at; (void)x_disposition_at; (void)y_lo; (void)y_hi;
  (void)y_at; (void)y_denominator_at; (void)y_disposition_at; (void)y_complex_coordinates;
  (void)prior_lo; (void)prior_hi; (void)prior_wide_at; (void)prior_radius_wide_at;
  (void)grain; (void)report_lo; (void)report_hi; (void)observed_raw_extent;
  if (*slot || upstream(census, lineage, lineage_count, slot)) return;
  ulong k_count = (ulong)response_complex;
  if ((ulong)gid >= k_count * k_count) return;
  uint k = (uint)((ulong)gid / k_count), l = (uint)((ulong)gid % k_count);
  uint dimension = 2u * response_complex;
  ulong n_begin = (ulong)prediction_from;
  if ((ulong)k > n_begin) n_begin = k;
  if ((ulong)l > n_begin) n_begin = l;
  ulong n_end = (ulong)prediction_from + observed_extent;
  if ((ulong)k + source_extent < n_end) n_end = (ulong)k + source_extent;
  if ((ulong)l + source_extent < n_end) n_end = (ulong)l + source_extent;
  W real = wzero(), imaginary = wzero();
  for (ulong n = n_begin; n < n_end; ++n) {
    ulong xk = (ulong)x_at + 2ul * (n - k), xl = (ulong)x_at + 2ul * (n - l);
    W akr = fromword(x_lo[xk]), aki = fromword(x_lo[xk + 1ul]);
    W alr = fromword(x_lo[xl]), ali = fromword(x_lo[xl + 1ul]);
    real = field_add_checked(real, field_add_checked(field_product_checked(akr, alr, slot),
                                                      field_product_checked(aki, ali, slot), slot), slot);
    imaginary = field_add_checked(imaginary, field_sub_checked(field_product_checked(akr, ali, slot),
                                                               field_product_checked(aki, alr, slot), slot), slot);
    if (*slot) return;
  }
  uint row = 2u * k, column = 2u * l;
  workspace[(ulong)row * dimension + column] = real;
  workspace[(ulong)row * dimension + column + 1u] = wneg(imaginary);
  workspace[(ulong)(row + 1u) * dimension + column] = imaginary;
  workspace[(ulong)(row + 1u) * dimension + column + 1u] = real;
}

kernel void section_temporal_condition_contact_rhs(
    device const long *x_lo [[buffer(0)]], device const long *x_hi [[buffer(1)]],
    constant uint &x_at [[buffer(2)]], constant uint &x_denominator_at [[buffer(3)]],
    constant uint &x_disposition_at [[buffer(4)]], device const long *y_lo [[buffer(5)]],
    device const long *y_hi [[buffer(6)]], constant uint &y_at [[buffer(7)]],
    constant uint &y_denominator_at [[buffer(8)]], constant uint &y_disposition_at [[buffer(9)]],
    constant uint &x_complex_coordinates [[buffer(10)]], constant uint &y_complex_coordinates [[buffer(11)]],
    constant uint &source_extent [[buffer(12)]], constant uint &response_complex [[buffer(13)]],
    constant uint &prediction_from [[buffer(14)]], constant uint &observed_from [[buffer(15)]],
    constant uint &observed_extent [[buffer(16)]], device const long *prior_lo [[buffer(17)]],
    device const long *prior_hi [[buffer(18)]], constant uint &prior_wide_at [[buffer(19)]],
    constant uint &prior_radius_wide_at [[buffer(20)]], constant uint &grain [[buffer(21)]],
    device W *workspace [[buffer(22)]], device long *report_lo [[buffer(23)]],
    device long *report_hi [[buffer(24)]], device uint *slot [[buffer(25)]],
    device const uint *census [[buffer(26)]], device const uint *lineage [[buffer(27)]],
    constant uint &lineage_count [[buffer(28)]], constant uint &observed_raw_extent [[buffer(29)]],
    uint gid [[thread_position_in_grid]]) {
  (void)x_hi; (void)x_denominator_at; (void)x_disposition_at; (void)report_lo; (void)report_hi;
  (void)y_complex_coordinates; (void)prior_hi; (void)prior_radius_wide_at;
  (void)observed_raw_extent;
  if (*slot || upstream(census, lineage, lineage_count, slot)) return;
  if (gid >= response_complex) return;
  uint dimension = 2u * response_complex;
  ulong n_begin = max((ulong)prediction_from, (ulong)gid);
  ulong n_end = (ulong)prediction_from + observed_extent;
  if ((ulong)gid + source_extent < n_end) n_end = (ulong)gid + source_extent;
  W real = wzero(), imaginary = wzero();
  for (ulong n = n_begin; n < n_end; ++n) {
    ulong xi = (ulong)x_at + 2ul * (n - gid);
    ulong yi = (ulong)y_at + 2ul * ((ulong)observed_from + n - prediction_from);
    W xr = fromword(x_lo[xi]), xi_value = fromword(x_lo[xi + 1ul]);
    W yr = fromword(y_lo[yi]), yi_value = fromword(y_lo[yi + 1ul]);
    real = field_add_checked(real, field_add_checked(field_product_checked(xr, yr, slot),
                                                      field_product_checked(xi_value, yi_value, slot), slot), slot);
    imaginary = field_add_checked(imaginary, field_sub_checked(field_product_checked(xr, yi_value, slot),
                                                               field_product_checked(xi_value, yr, slot), slot), slot);
    if (*slot) return;
  }
  ulong matrix = (ulong)dimension * dimension, raw_at = 2ul * matrix;
  ulong rhs_u_at = raw_at + dimension, rhs_v_at = rhs_u_at + dimension;
  workspace[raw_at + 2ul * gid] = real;
  workspace[raw_at + 2ul * gid + 1ul] = imaginary;
  uint scalar_at = 2u * dimension * dimension + 6u * dimension;
  W px = workspace[scalar_at + 2u], py = workspace[scalar_at + 3u];
  W cden = workspace[scalar_at + 4u];
  workspace[rhs_u_at + 2ul * gid] = field_enclosed_toward_zero(
      field_product_checked(px, real, slot), py, grain, slot);
  workspace[rhs_u_at + 2ul * gid + 1ul] = field_enclosed_toward_zero(
      field_product_checked(px, imaginary, slot), py, grain, slot);
  W prior_r = temporal_condition_prior(prior_lo, prior_wide_at + 2u * gid);
  W prior_i = temporal_condition_prior(prior_lo, prior_wide_at + 2u * gid + 1u);
  workspace[rhs_v_at + 2ul * gid] = field_product_checked(cden, prior_r, slot);
  workspace[rhs_v_at + 2ul * gid + 1ul] = field_product_checked(cden, prior_i, slot);
}

kernel void section_temporal_condition_contact_solve(
    device const long *x_lo [[buffer(0)]], device const long *x_hi [[buffer(1)]],
    constant uint &x_at [[buffer(2)]], constant uint &x_denominator_at [[buffer(3)]],
    constant uint &x_disposition_at [[buffer(4)]], device const long *y_lo [[buffer(5)]],
    device const long *y_hi [[buffer(6)]], constant uint &y_at [[buffer(7)]],
    constant uint &y_denominator_at [[buffer(8)]], constant uint &y_disposition_at [[buffer(9)]],
    constant uint &x_complex_coordinates [[buffer(10)]], constant uint &y_complex_coordinates [[buffer(11)]],
    constant uint &source_extent [[buffer(12)]], constant uint &response_complex [[buffer(13)]],
    constant uint &prediction_from [[buffer(14)]], constant uint &observed_from [[buffer(15)]],
    constant uint &observed_extent [[buffer(16)]], device const long *prior_lo [[buffer(17)]],
    device const long *prior_hi [[buffer(18)]], constant uint &prior_wide_at [[buffer(19)]],
    constant uint &prior_radius_wide_at [[buffer(20)]], constant uint &grain [[buffer(21)]],
    device W *workspace [[buffer(22)]], device long *report_lo [[buffer(23)]],
    device long *report_hi [[buffer(24)]], device uint *slot [[buffer(25)]],
    device const uint *census [[buffer(26)]], device const uint *lineage [[buffer(27)]],
    constant uint &lineage_count [[buffer(28)]], constant uint &observed_raw_extent [[buffer(29)]],
    uint gid [[thread_position_in_grid]]) {
  (void)x_lo; (void)x_hi; (void)x_at; (void)x_denominator_at; (void)x_disposition_at;
  (void)y_lo; (void)y_hi; (void)y_at; (void)y_denominator_at; (void)y_disposition_at;
  (void)x_complex_coordinates; (void)y_complex_coordinates; (void)source_extent;
  (void)prediction_from; (void)observed_from; (void)observed_extent;
  (void)observed_raw_extent;
  if (gid != 0 || *slot || upstream(census, lineage, lineage_count, slot)) return;
  uint dimension = 2u * response_complex;
  ulong matrix_count = (ulong)dimension * dimension;
  ulong raw_at = 2ul * matrix_count, rhs_u_at = raw_at + dimension;
  ulong rhs_v_at = rhs_u_at + dimension, u_at = rhs_v_at + dimension;
  ulong v_at = u_at + dimension, diagonal_at = v_at + dimension;
  uint scalar_at = (uint)(diagonal_at + dimension);
  device W *gram = workspace, *matrix = workspace + matrix_count;
  device W *rhs_u = workspace + rhs_u_at, *rhs_v = workspace + rhs_v_at;
  device W *u = workspace + u_at, *v = workspace + v_at;
  device W *diagonal = workspace + diagonal_at;
  W grain_scale = wof(field_pow2(grain), false, slot), cden = workspace[scalar_at + 4u];
  for (ulong i = 0; i < matrix_count; ++i) {
    W value = gram[i];
    if (i / dimension == i % dimension) value = field_add_checked(value, cden, slot);
    matrix[i] = field_product_checked(value, grain_scale, slot);
  }
  if (*slot) return;
  field_enclosed_factorize(matrix, diagonal, dimension, grain, slot);
  if (*slot) return;
  field_enclosed_solve(matrix, diagonal, dimension, grain, rhs_u, u, slot);
  if (*slot) return;
  field_enclosed_solve(matrix, diagonal, dimension, grain, rhs_v, v, slot);
  if (*slot) return;
  W py = workspace[scalar_at + 3u], prior_radius = temporal_condition_prior(prior_lo, prior_radius_wide_at);
  W den_u = field_product_checked(py, cden, slot), den_v = cden;
  W sum_u = wzero(), sum_v = wzero(), px = workspace[scalar_at + 2u];
  for (uint i = 0; i < dimension; ++i) {
    W prior = temporal_condition_prior(prior_lo, prior_wide_at + i), au = wzero(), av = wzero();
    for (uint j = 0; j < dimension; ++j) {
      W a_num = gram[(ulong)i * dimension + j];
      if (i == j) a_num = field_add_checked(a_num, cden, slot);
      W a_scaled = field_product_checked(a_num, grain_scale, slot);
      au = field_add_checked(au, field_enclosed_product_zero(a_scaled, u[j], grain, slot), slot);
      av = field_add_checked(av, field_enclosed_product_zero(a_scaled, v[j], grain, slot), slot);
    }
    W raw = workspace[raw_at + i];
    W scale_raw = field_product_checked(px, field_product_checked(raw, grain_scale, slot), slot);
    // The factor diagonal is no longer needed after the solve. Retain raw_xy in
    // that carrier while using rhs_v for residual_U and raw_at for residual_V.
    diagonal[i] = raw;
    rhs_v[i] = field_sub_checked(field_product_checked(py, au, slot), scale_raw, slot);
    workspace[raw_at + i] = field_sub_checked(av, field_product_checked(cden, prior, slot), slot);
    sum_u = field_add_checked(sum_u, field_of_magnitude(rhs_v[i].m, false), slot);
    sum_v = field_add_checked(sum_v, field_of_magnitude(workspace[raw_at + i].m, false), slot);
    rhs_u[i] = field_add_checked(u[i], v[i], slot);
  }
  if (*slot) return;
  W r_u = field_div_ceil(sum_u, den_u, slot);
  W r_v = field_add_checked(prior_radius, field_div_ceil(sum_v, den_v, slot), slot);
  W r_h = field_add_checked(r_u, r_v, slot);
  W r_returned = field_add_checked(prior_radius, r_v, slot);
  W r_delta = field_add_checked(r_h, prior_radius, slot);
  if (*slot) return;
  for (uint i = 0; i < dimension; ++i) {
    W prior = temporal_condition_prior(prior_lo, prior_wide_at + i);
    (void)field_sub_checked(prior, v[i], slot);
    (void)field_sub_checked(rhs_u[i], prior, slot);
  }
  if (*slot) return;
  uint segment = dimension + 1u;
  for (uint i = 0; i < dimension; ++i) {
    W prior = temporal_condition_prior(prior_lo, prior_wide_at + i);
    temporal_condition_store(report_lo, report_hi, i, prior, slot);
    temporal_condition_store(report_lo, report_hi, segment + i, v[i], slot);
    temporal_condition_store(report_lo, report_hi, 2u * segment + i, u[i], slot);
    temporal_condition_store(report_lo, report_hi, 3u * segment + i, rhs_u[i], slot);
    temporal_condition_store(report_lo, report_hi, 4u * segment + i,
                             field_sub_checked(prior, v[i], slot), slot);
    temporal_condition_store(report_lo, report_hi, 5u * segment + i,
                             field_sub_checked(rhs_u[i], prior, slot), slot);
    temporal_condition_store(report_lo, report_hi, 6u * segment + i, rhs_v[i], slot);
    temporal_condition_store(report_lo, report_hi, 7u * segment + i, workspace[raw_at + i], slot);
  }
  temporal_condition_store(report_lo, report_hi, dimension, prior_radius, slot);
  temporal_condition_store(report_lo, report_hi, segment + dimension, r_v, slot);
  temporal_condition_store(report_lo, report_hi, 2u * segment + dimension, r_u, slot);
  temporal_condition_store(report_lo, report_hi, 3u * segment + dimension, r_h, slot);
  temporal_condition_store(report_lo, report_hi, 4u * segment + dimension, r_returned, slot);
  temporal_condition_store(report_lo, report_hi, 5u * segment + dimension, r_delta, slot);
  temporal_condition_store(report_lo, report_hi, 6u * segment + dimension, den_u, slot);
  temporal_condition_store(report_lo, report_hi, 7u * segment + dimension, den_v, slot);

  // Preserve the exact continuing-action carriers only after all certification checks
  // succeed. The factorization scratch stays private to this passage.
  uint continuation_at = 8u * segment;
  for (ulong i = 0; i < matrix_count; ++i) {
    temporal_condition_store(report_lo, report_hi, continuation_at + (uint)i, gram[i], slot);
  }
  continuation_at += (uint)matrix_count;
  for (uint i = 0; i < dimension; ++i) {
    temporal_condition_store(report_lo, report_hi, continuation_at + i, diagonal[i], slot);
  }
  continuation_at += dimension;
  temporal_condition_store(report_lo, report_hi, continuation_at, workspace[scalar_at + 2u], slot);
  temporal_condition_store(report_lo, report_hi, continuation_at + 1u,
                           workspace[scalar_at + 3u], slot);
  temporal_condition_store(report_lo, report_hi, continuation_at + 2u,
                           workspace[scalar_at + 4u], slot);
}

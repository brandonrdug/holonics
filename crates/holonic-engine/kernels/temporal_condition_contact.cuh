// Structured temporal unit-admittance contact. The source and observed current views are
// complete point apertures; the prior is a dyadic ball. All four stages retain their carriers
// in one resident workspace and publish the eight normal/report blocks only after certification.

__device__ __forceinline__ wide temporal_condition_prior(
    const int64_t *lo, uint32_t at
) {
    return ((const wide *)lo)[at];
}

__device__ __forceinline__ void temporal_condition_store(
    int64_t *lo, int64_t *hi, uint32_t at, wide value
) {
    ((wide *)lo)[at] = ((wide *)hi)[at] = value;
}

extern "C" __global__ void section_temporal_condition_contact_validate(
    const int64_t *x_lo, const int64_t *x_hi, uint32_t x_at, uint32_t x_denominator_at,
    uint32_t x_disposition_at, const int64_t *y_lo, const int64_t *y_hi, uint32_t y_at,
    uint32_t y_denominator_at, uint32_t y_disposition_at, uint32_t x_complex_coordinates,
    uint32_t y_complex_coordinates, uint32_t source_extent, uint32_t response_complex,
    uint32_t prediction_from, uint32_t observed_from, uint32_t observed_extent,
    const int64_t *prior_lo, const int64_t *prior_hi, uint32_t prior_wide_at,
    uint32_t prior_radius_wide_at, uint32_t grain, wide *workspace,
    int64_t *report_lo, int64_t *report_hi, uint32_t *slot, const uint32_t *census,
    const uint32_t *lineage, uint32_t lineage_count, uint32_t observed_raw_extent
) {
    if (blockIdx.x != 0 || threadIdx.x != 0) return;
    if (*slot != 0 || upstream_refused(census, lineage, lineage_count, slot)) return;
    uint64_t x_count = x_complex_coordinates, y_count = y_complex_coordinates;
    uint64_t n = source_extent, k_count = response_complex, p = prediction_from;
    uint64_t o = observed_from, length = observed_extent;
    uint64_t prediction_extent = n + k_count - 1ULL;
    if (!x_count || !y_count || !n || !k_count || !length || !prior_lo || !prior_hi
        || !workspace || !report_lo || !report_hi || grain < 1u || grain > 120u
        || k_count > 0x3fffffffULL
        || x_count > 0x7fffffffULL || y_count > 0x7fffffffULL
        || n > x_count || !observed_raw_extent || observed_raw_extent > y_count
        || length > observed_raw_extent || p + length > prediction_extent
        || o + length > observed_raw_extent
        || k_count > 0xffffffffULL / 2ULL) {
        atomicOr(slot, REFUSED_MALFORMED);
        return;
    }
    uint32_t dimension = 2u * (uint32_t)k_count;
    if ((uint64_t)dimension * dimension > 0xffffffffULL
        || (uint64_t)x_at + 2ULL * x_count > 0xffffffffULL
        || (uint64_t)y_at + 2ULL * y_count > 0xffffffffULL
        || (uint64_t)prior_wide_at + dimension + 1ULL > 0x7fffffffULL
        || (uint64_t)prior_radius_wide_at != (uint64_t)prior_wide_at + dimension) {
        atomicOr(slot, REFUSED_MALFORMED);
        return;
    }
    wide xd = fibre_current_denominator(x_lo, x_hi, x_denominator_at,
                                        x_disposition_at, slot);
    wide yd = fibre_current_denominator(y_lo, y_hi, y_denominator_at,
                                        y_disposition_at, slot);
    if (*slot || xd <= 0 || yd <= 0) return;
    for (uint64_t coordinate = 0; coordinate < x_count; ++coordinate) {
        uint32_t at = (uint32_t)((uint64_t)x_at + 2ULL * coordinate);
        if (x_lo[at] != x_hi[at] || x_lo[at + 1u] != x_hi[at + 1u]
            || (coordinate >= n && (x_lo[at] != 0 || x_lo[at + 1u] != 0))) {
            atomicOr(slot, REFUSED_MALFORMED);
            return;
        }
    }
    for (uint64_t coordinate = 0; coordinate < y_count; ++coordinate) {
        uint32_t at = (uint32_t)((uint64_t)y_at + 2ULL * coordinate);
        if (y_lo[at] != y_hi[at] || y_lo[at + 1u] != y_hi[at + 1u]
            || (coordinate >= observed_raw_extent && (y_lo[at] != 0 || y_lo[at + 1u] != 0))) {
            atomicOr(slot, REFUSED_MALFORMED);
            return;
        }
    }
    for (uint32_t j = 0; j <= dimension; ++j) {
        uint32_t at = prior_wide_at + j;
        const int64_t *pl = prior_lo + 2u * at, *ph = prior_hi + 2u * at;
        if (pl[0] != ph[0] || pl[1] != ph[1]) {
            atomicOr(slot, REFUSED_MALFORMED);
            return;
        }
    }
    wide prior_radius = temporal_condition_prior(prior_lo, prior_radius_wide_at);
    if (prior_radius < 0) {
        atomicOr(slot, REFUSED_MALFORMED);
        return;
    }
    wide gcd = of_magnitude(fibre_gcd(magnitude(xd), magnitude(yd)), 0, slot);
    if (*slot || gcd <= 0) return;
    wide px = xd / gcd, py = yd / gcd;
    wide cden = product_checked(xd, xd, slot);
    if (*slot || px <= 0 || py <= 0 || cden <= 0) return;
    uint64_t scalar_at = 2ULL * (uint64_t)dimension * dimension
        + 6ULL * dimension;
    workspace[scalar_at] = xd;
    workspace[scalar_at + 1u] = yd;
    workspace[scalar_at + 2u] = px;
    workspace[scalar_at + 3u] = py;
    workspace[scalar_at + 4u] = cden;
    (void)grain;
}

extern "C" __global__ void section_temporal_condition_contact_gram(
    const int64_t *x_lo, const int64_t *x_hi, uint32_t x_at, uint32_t x_denominator_at,
    uint32_t x_disposition_at, const int64_t *y_lo, const int64_t *y_hi, uint32_t y_at,
    uint32_t y_denominator_at, uint32_t y_disposition_at, uint32_t x_complex_coordinates,
    uint32_t y_complex_coordinates, uint32_t source_extent, uint32_t response_complex,
    uint32_t prediction_from, uint32_t observed_from, uint32_t observed_extent,
    const int64_t *prior_lo, const int64_t *prior_hi, uint32_t prior_wide_at,
    uint32_t prior_radius_wide_at, uint32_t grain, wide *workspace,
    int64_t *report_lo, int64_t *report_hi, uint32_t *slot, const uint32_t *census,
    const uint32_t *lineage, uint32_t lineage_count, uint32_t observed_raw_extent
) {
    (void)x_hi; (void)x_denominator_at; (void)x_disposition_at; (void)y_lo; (void)y_hi;
    (void)y_at; (void)y_denominator_at; (void)y_disposition_at; (void)y_complex_coordinates;
    (void)prior_lo; (void)prior_hi; (void)prior_wide_at; (void)prior_radius_wide_at;
    (void)grain; (void)report_lo; (void)report_hi; (void)observed_raw_extent;
    if (*slot != 0 || upstream_refused(census, lineage, lineage_count, slot)) return;
    uint64_t gid = (uint64_t)blockIdx.x * blockDim.x + threadIdx.x;
    uint64_t k_count = response_complex;
    if (gid >= k_count * k_count) return;
    uint32_t k = (uint32_t)(gid / k_count), l = (uint32_t)(gid % k_count);
    uint32_t dimension = 2u * response_complex;
    uint64_t n_begin = prediction_from;
    if (k > n_begin) n_begin = k;
    if (l > n_begin) n_begin = l;
    uint64_t n_end = (uint64_t)prediction_from + observed_extent;
    if ((uint64_t)k + source_extent < n_end) n_end = (uint64_t)k + source_extent;
    if ((uint64_t)l + source_extent < n_end) n_end = (uint64_t)l + source_extent;
    wide real = 0, imaginary = 0;
    for (uint64_t n = n_begin; n < n_end; ++n) {
        uint64_t xk = (uint64_t)x_at + 2ULL * (n - k);
        uint64_t xl = (uint64_t)x_at + 2ULL * (n - l);
        wide akr = x_lo[xk], aki = x_lo[xk + 1u];
        wide alr = x_lo[xl], ali = x_lo[xl + 1u];
        real = add_checked(real, add_checked(product_checked(akr, alr, slot),
                                             product_checked(aki, ali, slot), slot), slot);
        imaginary = add_checked(imaginary, sub_checked(product_checked(akr, ali, slot),
                                                        product_checked(aki, alr, slot), slot), slot);
        if (*slot) return;
    }
    uint32_t row = 2u * k, column = 2u * l;
    wide *gram = workspace;
    gram[(uint64_t)row * dimension + column] = real;
    gram[(uint64_t)row * dimension + column + 1u] = sub_checked(0, imaginary, slot);
    gram[(uint64_t)(row + 1u) * dimension + column] = imaginary;
    gram[(uint64_t)(row + 1u) * dimension + column + 1u] = real;
}

extern "C" __global__ void section_temporal_condition_contact_rhs(
    const int64_t *x_lo, const int64_t *x_hi, uint32_t x_at, uint32_t x_denominator_at,
    uint32_t x_disposition_at, const int64_t *y_lo, const int64_t *y_hi, uint32_t y_at,
    uint32_t y_denominator_at, uint32_t y_disposition_at, uint32_t x_complex_coordinates,
    uint32_t y_complex_coordinates, uint32_t source_extent, uint32_t response_complex,
    uint32_t prediction_from, uint32_t observed_from, uint32_t observed_extent,
    const int64_t *prior_lo, const int64_t *prior_hi, uint32_t prior_wide_at,
    uint32_t prior_radius_wide_at, uint32_t grain, wide *workspace,
    int64_t *report_lo, int64_t *report_hi, uint32_t *slot, const uint32_t *census,
    const uint32_t *lineage, uint32_t lineage_count, uint32_t observed_raw_extent
) {
    (void)x_hi; (void)x_denominator_at; (void)x_disposition_at; (void)report_lo;
    (void)report_hi; (void)y_complex_coordinates; (void)prior_hi; (void)prior_radius_wide_at;
    (void)observed_raw_extent;
    if (*slot != 0 || upstream_refused(census, lineage, lineage_count, slot)) return;
    uint64_t gid = (uint64_t)blockIdx.x * blockDim.x + threadIdx.x;
    if (gid >= response_complex) return;
    uint32_t dimension = 2u * response_complex;
    uint64_t n_begin = prediction_from > gid ? prediction_from : gid;
    uint64_t n_end = (uint64_t)prediction_from + observed_extent;
    if (gid + source_extent < n_end) n_end = gid + source_extent;
    wide real = 0, imaginary = 0;
    for (uint64_t n = n_begin; n < n_end; ++n) {
        uint64_t xi = (uint64_t)x_at + 2ULL * (n - gid);
        uint64_t yi = (uint64_t)y_at + 2ULL * (observed_from + n - prediction_from);
        wide xr = x_lo[xi], xi_value = x_lo[xi + 1u];
        wide yr = y_lo[yi], yi_value = y_lo[yi + 1u];
        real = add_checked(real, add_checked(product_checked(xr, yr, slot),
                                             product_checked(xi_value, yi_value, slot), slot), slot);
        imaginary = add_checked(imaginary, sub_checked(product_checked(xr, yi_value, slot),
                                                        product_checked(xi_value, yr, slot), slot), slot);
        if (*slot) return;
    }
    uint64_t matrix = (uint64_t)dimension * dimension;
    uint64_t raw_at = matrix * 2ULL;
    uint64_t rhs_u_at = raw_at + dimension, rhs_v_at = rhs_u_at + dimension;
    workspace[raw_at + 2ULL * gid] = real;
    workspace[raw_at + 2ULL * gid + 1u] = imaginary;
    wide px = workspace[matrix * 2ULL + 6ULL * dimension + 2u];
    wide py = workspace[matrix * 2ULL + 6ULL * dimension + 3u];
    wide cden = workspace[matrix * 2ULL + 6ULL * dimension + 4u];
    workspace[rhs_u_at + 2ULL * gid] = field_enclosed_toward_zero(
        product_checked(px, real, slot), py, grain, slot);
    workspace[rhs_u_at + 2ULL * gid + 1u] = field_enclosed_toward_zero(
        product_checked(px, imaginary, slot), py, grain, slot);
    wide prior_r = temporal_condition_prior(prior_lo, prior_wide_at + 2u * (uint32_t)gid);
    wide prior_i = temporal_condition_prior(prior_lo, prior_wide_at + 2u * (uint32_t)gid + 1u);
    workspace[rhs_v_at + 2ULL * gid] = product_checked(cden, prior_r, slot);
    workspace[rhs_v_at + 2ULL * gid + 1u] = product_checked(cden, prior_i, slot);
}

extern "C" __global__ void section_temporal_condition_contact_solve(
    const int64_t *x_lo, const int64_t *x_hi, uint32_t x_at, uint32_t x_denominator_at,
    uint32_t x_disposition_at, const int64_t *y_lo, const int64_t *y_hi, uint32_t y_at,
    uint32_t y_denominator_at, uint32_t y_disposition_at, uint32_t x_complex_coordinates,
    uint32_t y_complex_coordinates, uint32_t source_extent, uint32_t response_complex,
    uint32_t prediction_from, uint32_t observed_from, uint32_t observed_extent,
    const int64_t *prior_lo, const int64_t *prior_hi, uint32_t prior_wide_at,
    uint32_t prior_radius_wide_at, uint32_t grain, wide *workspace,
    int64_t *report_lo, int64_t *report_hi, uint32_t *slot, const uint32_t *census,
    const uint32_t *lineage, uint32_t lineage_count, uint32_t observed_raw_extent
) {
    (void)x_lo; (void)x_hi; (void)x_at; (void)x_denominator_at; (void)x_disposition_at;
    (void)y_lo; (void)y_hi; (void)y_at; (void)y_denominator_at; (void)y_disposition_at;
    (void)x_complex_coordinates; (void)y_complex_coordinates; (void)source_extent;
    (void)prediction_from; (void)observed_from; (void)observed_extent;
    (void)observed_raw_extent;
    if (blockIdx.x != 0) return;
    if (upstream_refused(census, lineage, lineage_count, slot)) return;
    uint32_t dimension = 2u * response_complex;
    uint64_t matrix_count = (uint64_t)dimension * dimension;
    uint64_t raw_at = 2ULL * matrix_count, rhs_u_at = raw_at + dimension;
    uint64_t rhs_v_at = rhs_u_at + dimension, u_at = rhs_v_at + dimension;
    uint64_t v_at = u_at + dimension, diagonal_at = v_at + dimension;
    uint64_t scalar_at = diagonal_at + dimension;
    wide *gram = workspace, *matrix = workspace + matrix_count;
    wide *rhs_u = workspace + rhs_u_at, *rhs_v = workspace + rhs_v_at;
    wide *u = workspace + u_at, *v = workspace + v_at;
    wide *diagonal = workspace + diagonal_at;
    if (threadIdx.x == 0) {
        wide grain_scale = (wide)1 << grain;
        wide cden = workspace[scalar_at + 4u];
        for (uint64_t i = 0; i < matrix_count; ++i) {
            wide value = gram[i];
            uint64_t row = i / dimension, column = i % dimension;
            if (row == column) value = add_checked(value, cden, slot);
            matrix[i] = product_checked(value, grain_scale, slot);
        }
    }
    __syncthreads();
    if (*slot) return;
    field_enclosed_factorize(matrix, diagonal, dimension, grain, slot);
    if (*slot) return;
    if (threadIdx.x != 0) return;
    field_enclosed_solve(matrix, diagonal, dimension, grain, rhs_u, u, slot);
    if (*slot) return;
    field_enclosed_solve(matrix, diagonal, dimension, grain, rhs_v, v, slot);
    if (*slot) return;
    wide cden = workspace[scalar_at + 4u], py = workspace[scalar_at + 3u];
    wide prior_radius = temporal_condition_prior(prior_lo, prior_radius_wide_at);
    wide den_u = product_checked(py, cden, slot), den_v = cden;
    wide sum_u = 0, sum_v = 0;
    for (uint32_t i = 0; i < dimension; ++i) {
        wide prior = temporal_condition_prior(prior_lo, prior_wide_at + i);
        wide au = 0, av = 0;
        for (uint32_t j = 0; j < dimension; ++j) {
            wide a_num = gram[(uint64_t)i * dimension + j];
            if (i == j) a_num = add_checked(a_num, cden, slot);
            wide a_scaled = product_checked(a_num, (wide)1 << grain, slot);
            au = add_checked(au, field_enclosed_product_zero(
                a_scaled, u[j], grain, slot), slot);
            av = add_checked(av, field_enclosed_product_zero(
                a_scaled, v[j], grain, slot), slot);
        }
        wide raw = workspace[raw_at + i];
        wide px = workspace[scalar_at + 2u];
        wide scale_raw = product_checked(px, product_checked(raw, (wide)1 << grain, slot), slot);
        // The factor diagonal is no longer needed after the solve. Retain raw_xy in
        // that carrier while using rhs_v for residual_U and raw_at for residual_V.
        diagonal[i] = raw;
        rhs_v[i] = sub_checked(product_checked(py, au, slot), scale_raw, slot);
        workspace[raw_at + i] = sub_checked(av, product_checked(cden, prior, slot), slot);
        sum_u = add_checked(sum_u, of_magnitude(magnitude(rhs_v[i]), 0, slot), slot);
        sum_v = add_checked(sum_v, of_magnitude(magnitude(workspace[raw_at + i]), 0, slot), slot);
        rhs_u[i] = add_checked(u[i], v[i], slot);
    }
    if (*slot) return;
    wide r_u = div_ceil(sum_u, den_u, slot);
    wide r_v = add_checked(prior_radius, div_ceil(sum_v, den_v, slot), slot);
    wide r_h = add_checked(r_u, r_v, slot);
    wide r_returned = r_v;
    r_returned = add_checked(prior_radius, r_returned, slot);
    wide r_delta = add_checked(r_h, prior_radius, slot);
    if (*slot) return;
    for (uint32_t i = 0; i < dimension; ++i) {
        wide prior = temporal_condition_prior(prior_lo, prior_wide_at + i);
        (void)sub_checked(prior, v[i], slot);
        (void)sub_checked(rhs_u[i], prior, slot);
    }
    if (*slot) return;
    uint32_t segment = dimension + 1u;
    for (uint32_t i = 0; i < dimension; ++i) {
        wide prior = temporal_condition_prior(prior_lo, prior_wide_at + i);
        temporal_condition_store(report_lo, report_hi, i, prior);
        temporal_condition_store(report_lo, report_hi, segment + i, v[i]);
        temporal_condition_store(report_lo, report_hi, 2u * segment + i, u[i]);
        temporal_condition_store(report_lo, report_hi, 3u * segment + i, rhs_u[i]);
        temporal_condition_store(report_lo, report_hi, 4u * segment + i,
                                 sub_checked(prior, v[i], slot));
        temporal_condition_store(report_lo, report_hi, 5u * segment + i,
                                 sub_checked(rhs_u[i], prior, slot));
        temporal_condition_store(report_lo, report_hi, 6u * segment + i, rhs_v[i]);
        temporal_condition_store(report_lo, report_hi, 7u * segment + i, workspace[raw_at + i]);
    }
    temporal_condition_store(report_lo, report_hi, dimension, prior_radius);
    temporal_condition_store(report_lo, report_hi, segment + dimension, r_v);
    temporal_condition_store(report_lo, report_hi, 2u * segment + dimension, r_u);
    temporal_condition_store(report_lo, report_hi, 3u * segment + dimension, r_h);
    temporal_condition_store(report_lo, report_hi, 4u * segment + dimension, r_returned);
    temporal_condition_store(report_lo, report_hi, 5u * segment + dimension, r_delta);
    temporal_condition_store(report_lo, report_hi, 6u * segment + dimension, den_u);
    temporal_condition_store(report_lo, report_hi, 7u * segment + dimension, den_v);

    // Preserve the exact continuing-action carriers after every certification check has
    // succeeded.  These are the original Gram numerator, raw source/observation RHS and
    // the reduced denominator scalars; the factorization scratch remains private.
    uint32_t continuation_at = 8u * segment;
    for (uint64_t i = 0; i < matrix_count; ++i) {
        temporal_condition_store(report_lo, report_hi, continuation_at + (uint32_t)i, gram[i]);
    }
    continuation_at += (uint32_t)matrix_count;
    for (uint32_t i = 0; i < dimension; ++i) {
        temporal_condition_store(report_lo, report_hi, continuation_at + i, diagonal[i]);
    }
    continuation_at += dimension;
    temporal_condition_store(report_lo, report_hi, continuation_at, workspace[scalar_at + 2u]);
    temporal_condition_store(report_lo, report_hi, continuation_at + 1u, workspace[scalar_at + 3u]);
    temporal_condition_store(report_lo, report_hi, continuation_at + 2u, workspace[scalar_at + 4u]);
}

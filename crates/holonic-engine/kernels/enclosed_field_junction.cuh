// Enclosed dyadic representation of the paired field junction.
//
// This is the same passive junction as field_paired_junction_prepare.  The exact covariance stays
// an int64 rational word matrix; only the current report is represented by dyadic grid centers and
// L2 radii.  Centers are numerical representatives, never exact values.  The exact residual and
// source quantization error remain in the packed report for the exterior receiver.

__device__ __forceinline__ wide field_enclosed_toward_zero(
    wide numerator, wide denominator, uint32_t grain, uint32_t *slot
) {
    if (denominator <= 0 || magnitude(denominator) >= ((uwide)1 << 126)) {
        atomicOr(slot, REFUSED_CARRIER); return 0;
    }
    wide scale = (wide)1 << (grain - 1u);
    int toward_ceiling = numerator < 0 ? 1 : 0;
    return signed_product_divide_2(numerator, scale, denominator, toward_ceiling, slot);
}

__device__ __forceinline__ wide field_enclosed_product_zero(
    wide left, wide right, uint32_t grain, uint32_t *slot
) {
    return product_shift(left, right, (int)grain,
        ((left < 0) != (right < 0)) ? 1 : 0, slot);
}

__device__ __forceinline__ bool field_enclosed_junction_initialize(
    const int64_t *query, const int64_t *origin, const int64_t *incoming,
    const int64_t *frame, const int64_t *origin_frame,
    uint32_t nodes, uint32_t linked, uint32_t grain,
    const int64_t *covariance, const wide *held,
    int64_t *next_cov_lo, int64_t *next_cov_hi,
    wide *report_lo, wide *report_hi, wide *workspace, uint32_t *slot
) {
    if (slot == nullptr) return false;
    if (!nodes || linked > 1 || grain < 1u || grain > 120u
        || query == nullptr || incoming == nullptr || frame == nullptr || covariance == nullptr
        || held == nullptr || next_cov_lo == nullptr || next_cov_hi == nullptr
        || report_lo == nullptr || report_hi == nullptr || workspace == nullptr) {
        atomicOr(slot, REFUSED_MALFORMED);
        return false;
    }
    if (linked && (origin == nullptr || origin_frame == nullptr)) {
        atomicOr(slot, REFUSED_MALFORMED);
        return false;
    }
    if (nodes > UINT32_MAX / 6u) {
        atomicOr(slot, REFUSED_MALFORMED);
        return false;
    }
    const uint32_t source_width = 4u * nodes;
    const uint32_t dimension = 6u * nodes;
    if (dimension > UINT32_MAX / dimension) {
        atomicOr(slot, REFUSED_MALFORMED);
        return false;
    }
    const size_t matrix_count = (size_t)dimension * dimension;
    const size_t report_segment = (size_t)dimension + 1u;
    const int64_t query_den = query[source_width];
    const int64_t origin_den = linked ? origin[source_width] : 1;
    const int64_t covariance_den_word = covariance[matrix_count];
    const wide held_radius = held[2u * report_segment + dimension];
    const wide prefix_radius = held[3u * report_segment + dimension];
    if (query_den <= 0 || origin_den <= 0 || covariance_den_word <= 0
        || held_radius < 0 || prefix_radius < 0) {
        atomicOr(slot, REFUSED_MALFORMED);
        return false;
    }
    wide *matrix = workspace;
    wide *u = matrix + matrix_count;
    wide *d = u + dimension;
    wide *h = d + dimension;
    wide *solve = h + dimension;
    wide *v = solve + dimension;
    wide *prefix = v + dimension;
    (void)held_radius; (void)prefix_radius;
    wide u_den, d_den;
    if (!field_paired_build_faces(query, origin, incoming, frame, origin_frame,
        nodes, linked, u, d, &u_den, &d_den, slot)) return false;
    if (magnitude(u_den) >= ((uwide)1 << 126)) { atomicOr(slot, REFUSED_CARRIER); return false; }
    wide covariance_den;
    if (!field_paired_build_covariance(covariance, dimension, linked, d, d_den,
        matrix, &covariance_den, slot)) return false;
    for (size_t i = 0; i < matrix_count; ++i) matrix[i] = (wide)to_word(matrix[i], slot);
    wide checked_covariance_den = (wide)to_word(covariance_den, slot);
    if (*slot) return false;
    for (size_t i = 0; i < matrix_count; ++i)
        next_cov_lo[i] = next_cov_hi[i] = (int64_t)matrix[i];
    next_cov_lo[matrix_count] = next_cov_hi[matrix_count] = (int64_t)checked_covariance_den;

    wide error_u = 0;
    for (uint32_t i = 0; i < dimension; ++i) {
        h[i] = held[2u * report_segment + i];
        prefix[i] = held[3u * report_segment + i];
        wide floor_value = signed_product_divide_2(u[i], (wide)1 << (grain - 1u), u_den, 0, slot);
        wide ceil_value = signed_product_divide_2(u[i], (wide)1 << (grain - 1u), u_den, 1, slot);
        u[i] = u[i] < 0 ? ceil_value : floor_value;
        if (floor_value != ceil_value) {
            // E_u is an L1 upper bound in grid quanta.  Toward-zero quantization has error < 1.
            // The count still records every non-exact source coordinate.
            error_u = add_checked(error_u, 1, slot);
        }
    }
    if (*slot) return false;
    for (uint32_t i = 0; i < dimension; ++i) solve[i] = 0;
    wide *c_matrix = matrix;
    wide cden = checked_covariance_den;
    for (uint32_t i = 0; i < dimension; ++i)
        c_matrix[(size_t)i * dimension + i] = add_checked(
            c_matrix[(size_t)i * dimension + i], cden, slot);
    // LDL stores L*S and D*S, so scale the complete exact A_num = C_num + Cden I by
    // S = 2^grain before factorization.  The RHS below remains in grid quanta; this common
    // scaling is what makes the fixed-point products and the later D division dimensionally agree.
    wide scale = (wide)1 << grain;
    for (size_t i = 0; i < matrix_count; ++i)
        c_matrix[i] = product_checked(c_matrix[i], scale, slot);
    if (*slot) return false;
    report_lo[4u * report_segment + dimension] = report_hi[4u * report_segment + dimension] = error_u;
    return true;
}

__device__ __forceinline__ void field_enclosed_junction_finish(
    const int64_t *next_cov_lo, const wide *held,
    uint32_t dimension, uint64_t occurrence, uint32_t grain,
    wide *workspace, wide *report_lo, wide *report_hi, uint32_t *slot
) {
    const size_t matrix_count = (size_t)dimension * dimension;
    const size_t report_segment = (size_t)dimension + 1u;
    wide *matrix = workspace;
    wide *u = matrix + matrix_count;
    wide *d = u + dimension;
    wide *h = d + dimension;
    wide *solve = h + dimension;
    wide *v = solve + dimension;
    wide *prefix = v + dimension;
    wide *diagonal = prefix + dimension;
    wide *residual = diagonal + dimension;
    (void)d; (void)diagonal;
    wide *c_matrix = matrix;
    const wide held_radius = held[2u * report_segment + dimension];
    const wide prefix_radius = held[3u * report_segment + dimension];
    wide cden = (wide)next_cov_lo[matrix_count];
    wide error_u = report_lo[4u * report_segment + dimension];
    wide cden_rhs = cden;
    for (uint32_t i = 0; i < dimension; ++i) {
        wide sum = add_checked(u[i], h[i], slot);
        solve[i] = product_checked(2, product_checked(cden_rhs, sum, slot), slot);
    }
    if (*slot) return;
    // L y = rhs, D z = y, L^T v = z, all centers in grid quanta.  The forward substitution
    // uses y_j directly; division by the scaled diagonal occurs exactly once in the following z
    // loop.  For C=0 this gives v=rhs=2(Uhat+H) and a zero exact residual at every grain.
    for (uint32_t i = 0; i < dimension; ++i) {
        wide value = solve[i];
        for (uint32_t j = 0; j < i; ++j)
            value = sub_checked(value, field_enclosed_product_zero(
                c_matrix[(size_t)i * dimension + j], solve[j], grain, slot), slot);
        solve[i] = value;
    }
    for (uint32_t i = 0; i < dimension; ++i)
        v[i] = field_enclosed_toward_zero(solve[i], diagonal[i], grain, slot);
    for (int i = (int)dimension - 1; i >= 0; --i) {
        wide value = v[i];
        for (uint32_t j = (uint32_t)i + 1u; j < dimension; ++j)
            value = sub_checked(value, field_enclosed_product_zero(
                c_matrix[(size_t)j * dimension + (uint32_t)i], v[j], grain, slot), slot);
        v[i] = value;
    }
    if (*slot) return;

    // Certify the numerical solve against exact A and the quantized root source.
    wide residual_sum = 0;
    for (uint32_t i = 0; i < dimension; ++i) {
        wide lhs = product_checked(cden, v[i], slot);
        for (uint32_t j = 0; j < dimension; ++j) {
            wide term = product_checked((wide)next_cov_lo[(size_t)i * dimension + j], v[j], slot);
            lhs = add_checked(lhs, term, slot);
        }
        wide rhs_exact = product_checked(2, product_checked(cden,
            add_checked(u[i], h[i], slot), slot), slot);
        residual[i] = sub_checked(lhs, rhs_exact, slot);
        wide magnitude_i = of_magnitude(magnitude(residual[i]), 0, slot);
        residual_sum = add_checked(residual_sum, magnitude_i, slot);
    }
    if (*slot) return;
    wide residual_radius = div_ceil(residual_sum, cden, slot);
    if (*slot) return;
    wide radius_v = add_checked(product_checked(2, held_radius, slot),
        add_checked(product_checked(2, error_u, slot), residual_radius, slot), slot);
    wide radius_b = add_checked(product_checked(2, held_radius, slot),
        add_checked(error_u, residual_radius, slot), slot);
    wide radius_h = add_checked(held_radius,
        add_checked(product_checked(2, error_u, slot), residual_radius, slot), slot);
    wide radius_prefix = add_checked(prefix_radius, radius_v, slot);
    if (*slot) return;

    for (uint32_t i = 0; i < dimension; ++i) {
        solve[i] = sub_checked(v[i], u[i], slot);
        h[i] = sub_checked(add_checked(product_checked(2, u[i], slot), h[i], slot), v[i], slot);
        prefix[i] = (occurrence & 1u) ? sub_checked(prefix[i], v[i], slot)
            : add_checked(prefix[i], v[i], slot);
    }
    if (*slot) return;

    // C was preserved exactly; only the fresh packed dyadic report is now published.
    for (uint32_t i = 0; i < dimension; ++i) {
        report_lo[i] = report_hi[i] = v[i];
        report_lo[report_segment + i] = report_hi[report_segment + i] = solve[i];
        report_lo[2u * report_segment + i] = report_hi[2u * report_segment + i] = h[i];
        report_lo[3u * report_segment + i] = report_hi[3u * report_segment + i] = prefix[i];
        report_lo[4u * report_segment + i] = report_hi[4u * report_segment + i] = u[i];
        report_lo[5u * report_segment + i] = report_hi[5u * report_segment + i] = residual[i];
    }
    report_lo[dimension] = report_hi[dimension] = radius_v;
    report_lo[report_segment + dimension] = report_hi[report_segment + dimension] = radius_b;
    report_lo[2u * report_segment + dimension] = report_hi[2u * report_segment + dimension] = radius_h;
    report_lo[3u * report_segment + dimension] = report_hi[3u * report_segment + dimension] = radius_prefix;
    report_lo[4u * report_segment + dimension] = report_hi[4u * report_segment + dimension] = error_u;
    report_lo[5u * report_segment + dimension] = report_hi[5u * report_segment + dimension] = cden;}

// Collective entry: every thread in the owning block calls this helper. Initialization and
// publication remain serial; only independent LDL off-diagonal rows are distributed.
__device__ __forceinline__ void field_enclosed_junction_prepare(
    const int64_t *query, const int64_t *origin, const int64_t *incoming,
    const int64_t *frame, const int64_t *origin_frame,
    uint32_t nodes, uint32_t linked, uint64_t occurrence, uint32_t grain,
    const int64_t *covariance, const wide *held,
    int64_t *next_cov_lo, int64_t *next_cov_hi,
    wide *report_lo, wide *report_hi,
    wide *workspace, uint32_t *slot
) {
    if (slot == nullptr) return;
    if (blockIdx.x != 0) return;
    if (threadIdx.x == 0) {
        field_enclosed_junction_initialize(query, origin, incoming, frame, origin_frame,
            nodes, linked, grain, covariance, held, next_cov_lo, next_cov_hi,
            report_lo, report_hi, workspace, slot);
    }
    __syncthreads();
    if (*slot) return;
    const uint32_t dimension = 6u * nodes;
    const size_t matrix_count = (size_t)dimension * dimension;
    wide *matrix = workspace;
    wide *u = matrix + matrix_count;
    wide *d = u + dimension;
    wide *h = d + dimension;
    wide *solve = h + dimension;
    wide *v = solve + dimension;
    wide *prefix = v + dimension;
    wide *diagonal = prefix + dimension;
    (void)u; (void)d; (void)h; (void)solve; (void)v; (void)prefix; (void)diagonal;
    for (uint32_t k = 0; k < dimension; ++k) {
        if (threadIdx.x == 0) {
            wide correction = 0;
            for (uint32_t j = 0; j < k; ++j) {
                wide pair = field_enclosed_product_zero(matrix[(size_t)k * dimension + j],
                    matrix[(size_t)k * dimension + j], grain, slot);
                wide term = field_enclosed_product_zero(pair, diagonal[j], grain, slot);
                correction = add_checked(correction, term, slot);
            }
            diagonal[k] = sub_checked(matrix[(size_t)k * dimension + k], correction, slot);
            if (diagonal[k] <= 0) atomicOr(slot, REFUSED_CARRIER);
        }
        __syncthreads();
        if (*slot) return;
        for (uint32_t i = k + 1u + threadIdx.x; i < dimension; i += blockDim.x) {
            wide correction_off = 0;
            for (uint32_t j = 0; j < k; ++j) {
                wide pair = field_enclosed_product_zero(matrix[(size_t)i * dimension + j],
                    matrix[(size_t)k * dimension + j], grain, slot);
                wide term = field_enclosed_product_zero(pair, diagonal[j], grain, slot);
                correction_off = add_checked(correction_off, term, slot);
                if (*slot) break;
            }
            if (!*slot) {
                wide numerator = sub_checked(matrix[(size_t)k * dimension + i], correction_off, slot);
                matrix[(size_t)i * dimension + k] = field_enclosed_toward_zero(
                    numerator, diagonal[k], grain, slot);
            }
        }
        __syncthreads();
        if (*slot) return;
    }
    if (threadIdx.x == 0)
        field_enclosed_junction_finish(next_cov_lo, held, dimension, occurrence, grain,
            workspace, report_lo, report_hi, slot);
    __syncthreads();
}

// Source-neutral paired passive junction for a resident constitutive field.
//
// The helper is a numerical device primitive, not a launch boundary.  `query` and `origin` are
// field reports: their first 4N words are [out.re,out.im,held.re,held.im] per node and word 4N is
// their common denominator.  `incoming` is the N x (re,im,den) root receiving field.  The old
// covariance is a row-major D x D realification of a Hermitian current covariance, followed by
// its positive common denominator.  `held` is the four-segment [v,b,h,P] report, each segment of
// length D+1.  Every destination is fresh staging; the old covariance and report are read-only.

// Common source/contact assembly for exact and enclosed representations.  The returned faces use
// one common denominator each; the target half of u is zero and the target half of d is the
// negative root receiving field.  No covariance or report destination is touched here.
__device__ __forceinline__ bool field_paired_build_faces(
    const int64_t *query, const int64_t *origin, const int64_t *incoming,
    const int64_t *frame, const int64_t *origin_frame,
    uint32_t nodes, uint32_t linked, wide *u, wide *d,
    wide *u_den_out, wide *d_den_out, uint32_t *slot
) {
    if (!nodes || linked > 1 || query == nullptr || incoming == nullptr || frame == nullptr
        || u == nullptr || d == nullptr || u_den_out == nullptr || d_den_out == nullptr) {
        atomicOr(slot, REFUSED_MALFORMED);
        return false;
    }
    if (linked && (origin == nullptr || origin_frame == nullptr)) {
        atomicOr(slot, REFUSED_MALFORMED);
        return false;
    }
    const uint32_t source_width = 4u * nodes;
    const uint32_t dimension = 6u * nodes;
    const int64_t query_den = query[source_width];
    const int64_t origin_den = linked ? origin[source_width] : 1;
    if (query_den <= 0 || origin_den <= 0) {
        atomicOr(slot, REFUSED_MALFORMED);
        return false;
    }
    wide u_den = 1, d_den = 1;
    for (uint32_t node = 0; node < nodes; ++node) {
        const int64_t *now = frame + 3u * node;
        wide now_norm = add_checked(product_checked((wide)now[0], (wide)now[0], slot),
            product_checked((wide)now[1], (wide)now[1], slot), slot);
        wide now_den = product_checked((wide)now[2], (wide)now[2], slot);
        if (*slot) return false;
        if (now[2] <= 0 || now_norm != now_den) {
            atomicOr(slot, REFUSED_MALFORMED);
            return false;
        }
        const int64_t *before = linked ? origin_frame + 3u * node : nullptr;
        if (linked) {
            wide before_norm = add_checked(product_checked((wide)before[0], (wide)before[0], slot),
                product_checked((wide)before[1], (wide)before[1], slot), slot);
            wide before_den = product_checked((wide)before[2], (wide)before[2], slot);
            if (*slot) return false;
            if (before[2] <= 0 || before_norm != before_den) {
                atomicOr(slot, REFUSED_MALFORMED);
                return false;
            }
        }
        for (uint32_t branch = 0; branch < 2u; ++branch) {
            wide turned[3];
            fibre_phase_product((wide)now[0], -(wide)now[1], (wide)now[2],
                (wide)query[4u * node + 2u * branch],
                (wide)query[4u * node + 2u * branch + 1u], (wide)query_den,
                turned, slot);
            if (*slot) return false;
            u_den = fibre_lcm(u_den, turned[2], slot);
            if (linked) {
                wide old_turned[3];
                fibre_phase_product((wide)before[0], -(wide)before[1], (wide)before[2],
                    (wide)origin[4u * node + 2u * branch],
                    (wide)origin[4u * node + 2u * branch + 1u], (wide)origin_den,
                    old_turned, slot);
                if (*slot) return false;
                d_den = fibre_lcm(d_den, old_turned[2], slot);
            }
        }
    }
    for (uint32_t node = 0; node < nodes; ++node) {
        const int64_t *arrived = incoming + 3u * node;
        if (arrived[2] <= 0) {
            atomicOr(slot, REFUSED_MALFORMED);
            return false;
        }
        if (linked) d_den = fibre_lcm(d_den, (wide)arrived[2], slot);
    }
    if (*slot) return false;
    for (uint32_t node = 0; node < nodes; ++node) {
        const int64_t *now = frame + 3u * node;
        const int64_t *before = linked ? origin_frame + 3u * node : nullptr;
        for (uint32_t branch = 0; branch < 2u; ++branch) {
            wide turned[3];
            fibre_phase_product((wide)now[0], -(wide)now[1], (wide)now[2],
                (wide)query[4u * node + 2u * branch],
                (wide)query[4u * node + 2u * branch + 1u], (wide)query_den,
                turned, slot);
            u[4u * node + 2u * branch] = product_checked(turned[0], u_den / turned[2], slot);
            u[4u * node + 2u * branch + 1u] = product_checked(turned[1], u_den / turned[2], slot);
            if (linked) {
                wide old_turned[3];
                fibre_phase_product((wide)before[0], -(wide)before[1], (wide)before[2],
                    (wide)origin[4u * node + 2u * branch],
                    (wide)origin[4u * node + 2u * branch + 1u], (wide)origin_den,
                    old_turned, slot);
                d[4u * node + 2u * branch] = product_checked(old_turned[0], d_den / old_turned[2], slot);
                d[4u * node + 2u * branch + 1u] = product_checked(old_turned[1], d_den / old_turned[2], slot);
            } else {
                d[4u * node + 2u * branch] = d[4u * node + 2u * branch + 1u] = 0;
            }
        }
        const int64_t *arrived = incoming + 3u * node;
        if (linked) {
            d[source_width + 2u * node] = -product_checked((wide)arrived[0], d_den / (wide)arrived[2], slot);
            d[source_width + 2u * node + 1u] = -product_checked((wide)arrived[1], d_den / (wide)arrived[2], slot);
        } else {
            d[source_width + 2u * node] = d[source_width + 2u * node + 1u] = 0;
        }
        u[source_width + 2u * node] = u[source_width + 2u * node + 1u] = 0;
    }
    if (*slot) return false;
    fibre_normalize(u, dimension, &u_den, slot);
    if (linked) fibre_normalize(d, dimension, &d_den, slot);
    if (*slot) return false;
    *u_den_out = u_den;
    *d_den_out = d_den;
    return true;
}

// Common exact covariance update. `matrix` is D² contiguous wide words and receives the normalized
// numerator; the denominator is returned separately so the caller can either solve exactly or
// preserve the same rational C representation in an enclosed path.
__device__ __forceinline__ bool field_paired_build_covariance(
    const int64_t *covariance, uint32_t dimension, uint32_t linked,
    const wide *d, wide d_den, wide *matrix, wide *den_out, uint32_t *slot
) {
    if (covariance == nullptr || d == nullptr || matrix == nullptr || den_out == nullptr
        || !dimension || linked > 1 || dimension > UINT32_MAX / dimension) {
        atomicOr(slot, REFUSED_MALFORMED);
        return false;
    }
    const size_t count = (size_t)dimension * dimension;
    const int64_t old_den_word = covariance[count];
    if (old_den_word <= 0 || d_den <= 0) {
        atomicOr(slot, REFUSED_MALFORMED);
        return false;
    }
    wide old_den = (wide)old_den_word;
    wide residual_square_den = product_checked(d_den, d_den, slot);
    wide next_den = linked ? fibre_lcm(old_den, residual_square_den, slot) : old_den;
    if (*slot) return false;
    for (uint32_t i = 0; i < dimension; ++i) {
        for (uint32_t j = 0; j < dimension; ++j) {
            if (covariance[(size_t)i * dimension + j] != covariance[(size_t)j * dimension + i]) {
                atomicOr(slot, REFUSED_MALFORMED);
                return false;
            }
            wide value = product_checked((wide)covariance[(size_t)i * dimension + j], next_den / old_den, slot);
            if (linked) {
                uint32_t ipair = i / 2u, jpair = j / 2u;
                wide ji = (i & 1u) ? d[2u * ipair] : -d[2u * ipair + 1u];
                wide jj = (j & 1u) ? d[2u * jpair] : -d[2u * jpair + 1u];
                wide gram = add_checked(product_checked(d[i], d[j], slot),
                    product_checked(ji, jj, slot), slot);
                value = add_checked(value, product_checked(gram, next_den / residual_square_den, slot), slot);
            }
            matrix[(size_t)i * dimension + j] = value;
        }
    }
    if (*slot) return false;
    fibre_normalize(matrix, (uint32_t)count, &next_den, slot);
    if (*slot) return false;
    *den_out = next_den;
    return true;
}

__device__ __forceinline__ void field_paired_junction_prepare(
    const int64_t *query, const int64_t *origin, const int64_t *incoming,
    const int64_t *frame, const int64_t *origin_frame,
    uint32_t nodes, uint32_t linked, uint64_t occurrence,
    const int64_t *covariance, const int64_t *held,
    int64_t *next_cov_lo, int64_t *next_cov_hi,
    int64_t *report_lo, int64_t *report_hi,
    wide *workspace, uint32_t *slot
) {
    if (slot == nullptr) return;
    if (!nodes || linked > 1 || query == nullptr || incoming == nullptr
        || frame == nullptr || covariance == nullptr || held == nullptr
        || next_cov_lo == nullptr || next_cov_hi == nullptr
        || report_lo == nullptr || report_hi == nullptr || workspace == nullptr) {
        atomicOr(slot, REFUSED_MALFORMED);
        return;
    }
    if (linked && (origin == nullptr || origin_frame == nullptr)) {
        atomicOr(slot, REFUSED_MALFORMED);
        return;
    }
    if (nodes > UINT32_MAX / 6u) {
        atomicOr(slot, REFUSED_MALFORMED);
        return;
    }
    const uint32_t source_width = 4u * nodes;
    const uint32_t dimension = 6u * nodes;
    const size_t matrix_count = (size_t)dimension * dimension;
    if (dimension > UINT32_MAX / dimension) {
        atomicOr(slot, REFUSED_MALFORMED);
        return;
    }
    const size_t report_segment = (size_t)dimension + 1u;
    const int64_t query_den = query[source_width];
    const int64_t origin_den = linked ? origin[source_width] : 1;
    const int64_t covariance_den_word = covariance[matrix_count];
    const int64_t held_den_word = held[2u * report_segment + dimension];
    const int64_t prefix_den_word = held[3u * report_segment + dimension];
    if (query_den <= 0 || origin_den <= 0 || covariance_den_word <= 0
        || held_den_word <= 0 || prefix_den_word <= 0) {
        atomicOr(slot, REFUSED_MALFORMED);
        return;
    }

    // Six D-word work faces: current root current, linked residual, old held, b, v, and P.
    // The preceding D*D words are the augmented matrix's coefficient block; its RHS occupies the
    // following D words, so the complete allocation is D*(D+1)+6D wide values.
    wide *matrix = workspace;
    wide *rhs = workspace + matrix_count;
    wide *u = rhs + dimension;
    wide *d = u + dimension;
    wide *h = d + dimension;
    wide *b = h + dimension;
    wide *v = b + dimension;
    wide *prefix = v + dimension;
    for (uint32_t i = 0; i < dimension; ++i) rhs[i] = 0;

    wide current_den = 1, residual_den = 1;
    if (!field_paired_build_faces(query, origin, incoming, frame, origin_frame,
        nodes, linked, u, d, &current_den, &residual_den, slot)) return;
    for (uint32_t j = 0; j < dimension; ++j) {
        h[j] = (wide)held[2u * report_segment + j];
        prefix[j] = (wide)held[3u * report_segment + j];
    }
    wide held_den = (wide)held_den_word;
    wide prefix_den = (wide)prefix_den_word;
    fibre_normalize(h, dimension, &held_den, slot);
    fibre_normalize(prefix, dimension, &prefix_den, slot);
    if (*slot) return;
    wide checked_cov_den;
    if (!field_paired_build_covariance(covariance, dimension, linked, d, residual_den,
        matrix, &checked_cov_den, slot)) return;
    if (*slot) return;
    for (size_t j = 0; j < matrix_count; ++j) {
        matrix[j] = (wide)to_word(matrix[j], slot);
    }
    checked_cov_den = (wide)to_word(checked_cov_den, slot);
    if (*slot) return;
    for (size_t j = 0; j < matrix_count; ++j)
        next_cov_lo[j] = next_cov_hi[j] = (int64_t)matrix[j];
    next_cov_lo[matrix_count] = next_cov_hi[matrix_count] = (int64_t)checked_cov_den;

    // Solve (C_new + Cden I) v_num = 2 Cden (u+h)_num with fraction-free Bareiss.  The diagonal
    // is the declared SPD pivot; no pivot search, score, or host choice is admissible.
    wide rhs_den = fibre_lcm(current_den, held_den, slot);
    if (*slot) return;
    for (uint32_t i = 0; i < dimension; ++i) {
        wide combined = add_checked(product_checked(u[i], rhs_den / current_den, slot),
            product_checked(h[i], rhs_den / held_den, slot), slot);
        rhs[i] = product_checked(2, product_checked(checked_cov_den, combined, slot), slot);
    }
    if (*slot) return;
    for (uint32_t i = 0; i < dimension; ++i)
        matrix[(size_t)i * dimension + i] = add_checked(
            matrix[(size_t)i * dimension + i], checked_cov_den, slot);
    if (*slot) return;
    wide previous = 1;
    for (uint32_t k = 0; k + 1u < dimension; ++k) {
        wide pivot = matrix[(size_t)k * dimension + k];
        if (pivot <= 0 || previous <= 0) {
            atomicOr(slot, REFUSED_MALFORMED);
            return;
        }
        for (uint32_t i = k + 1u; i < dimension; ++i) {
            for (uint32_t j = k + 1u; j < dimension; ++j) {
                wide numerator = sub_checked(
                    product_checked(pivot, matrix[(size_t)i * dimension + j], slot),
                    product_checked(matrix[(size_t)i * dimension + k],
                        matrix[(size_t)k * dimension + j], slot), slot);
                if (*slot) return;
                if (numerator % previous != 0) {
                    atomicOr(slot, REFUSED_MALFORMED);
                    return;
                }
                matrix[(size_t)i * dimension + j] = numerator / previous;
            }
            wide rhs_numerator = sub_checked(product_checked(pivot, rhs[i], slot),
                product_checked(matrix[(size_t)i * dimension + k], rhs[k], slot), slot);
            if (*slot) return;
            if (rhs_numerator % previous != 0) {
                atomicOr(slot, REFUSED_MALFORMED);
                return;
            }
            rhs[i] = rhs_numerator / previous;
        }
        previous = pivot;
    }
    wide determinant = matrix[(size_t)(dimension - 1u) * dimension + dimension - 1u];
    if (determinant <= 0) {
        atomicOr(slot, REFUSED_MALFORMED);
        return;
    }
    for (int i = (int)dimension - 1; i >= 0; --i) {
        wide numerator = product_checked(rhs[i], determinant, slot);
        for (uint32_t j = (uint32_t)i + 1u; j < dimension; ++j)
            numerator = sub_checked(numerator,
                product_checked(matrix[(size_t)i * dimension + j], v[j], slot), slot);
        wide diagonal = matrix[(size_t)i * dimension + (uint32_t)i];
        if (*slot) return;
        if (diagonal == 0 || numerator % diagonal != 0) {
            atomicOr(slot, REFUSED_MALFORMED);
            return;
        }
        v[i] = numerator / diagonal;
    }
    wide v_den = product_checked(determinant, rhs_den, slot);
    if (*slot) return;
    fibre_normalize(v, dimension, &v_den, slot);
    if (*slot) return;

    wide reaction_den = fibre_lcm(current_den, held_den, slot);
    reaction_den = fibre_lcm(reaction_den, v_den, slot);
    if (*slot) return;
    for (uint32_t i = 0; i < dimension; ++i) {
        wide vi = product_checked(v[i], reaction_den / v_den, slot);
        wide ui = product_checked(u[i], reaction_den / current_den, slot);
        wide hi = product_checked(h[i], reaction_den / held_den, slot);
        b[i] = sub_checked(vi, ui, slot);
        h[i] = sub_checked(add_checked(product_checked(2, ui, slot), hi, slot), vi, slot);
    }
    wide b_den = reaction_den;
    fibre_normalize(b, dimension, &b_den, slot);
    // `h` shares the pre-normalization reaction denominator, but each output segment is normalized
    // independently so a common-factor reduction of b cannot alter h's denominator.
    wide h_new_den = reaction_den;
    fibre_normalize(h, dimension, &h_new_den, slot);
    wide prefix_new_den = fibre_lcm(prefix_den, v_den, slot);
    for (uint32_t i = 0; i < dimension; ++i) {
        wide old_p = product_checked(prefix[i], prefix_new_den / prefix_den, slot);
        wide new_v = product_checked(v[i], prefix_new_den / v_den, slot);
        prefix[i] = (occurrence & 1u) ? sub_checked(old_p, new_v, slot)
            : add_checked(old_p, new_v, slot);
    }
    fibre_normalize(prefix, dimension, &prefix_new_den, slot);
    if (*slot) return;

    // All arithmetic and normalizations are complete.  Convert every fresh report word before
    // publishing it; the old covariance and held report remain untouched on every refusal path.
    for (uint32_t i = 0; i < dimension; ++i) {
        v[i] = (wide)to_word(v[i], slot);
        b[i] = (wide)to_word(b[i], slot);
        h[i] = (wide)to_word(h[i], slot);
        prefix[i] = (wide)to_word(prefix[i], slot);
    }
    wide checked_v_den = (wide)to_word(v_den, slot);
    wide checked_b_den = (wide)to_word(b_den, slot);
    wide checked_h_den = (wide)to_word(h_new_den, slot);
    wide checked_prefix_den = (wide)to_word(prefix_new_den, slot);
    if (*slot) return;
    for (uint32_t i = 0; i < dimension; ++i) {
        report_lo[i] = report_hi[i] = (int64_t)v[i];
        report_lo[report_segment + i] = report_hi[report_segment + i] = (int64_t)b[i];
        report_lo[2u * report_segment + i] = report_hi[2u * report_segment + i] = (int64_t)h[i];
        report_lo[3u * report_segment + i] = report_hi[3u * report_segment + i] = (int64_t)prefix[i];
    }
    report_lo[dimension] = report_hi[dimension] = (int64_t)checked_v_den;
    report_lo[report_segment + dimension] = report_hi[report_segment + dimension] = (int64_t)checked_b_den;
    report_lo[2u * report_segment + dimension] = report_hi[2u * report_segment + dimension] = (int64_t)checked_h_den;
    report_lo[3u * report_segment + dimension] = report_hi[3u * report_segment + dimension] = (int64_t)checked_prefix_den;
}

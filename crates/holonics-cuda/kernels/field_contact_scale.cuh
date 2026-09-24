// Read-only contact-scale gradient over a pure CSR basis map. The two producing
// factor rows are P0/P1 and C0/C1; no rectangular D coupling is replaced by a
// square normal matrix. One output row is the sum of one contiguous contact-row
// group, and its packet is (lambda_real, 0, radius).
extern "C" __global__ void section_field_contact_scale_gradient(
    const int64_t *offsets, const int64_t *offsets_hi,
    const int64_t *columns, const int64_t *columns_hi,
    const int64_t *values, const int64_t *values_hi,
    const int64_t *basis_bounds, const int64_t *basis_bounds_hi,
    const int64_t *p, const int64_t *p_hi,
    const int64_t *c, const int64_t *c_hi,
    const int64_t *delta_bounds, const int64_t *delta_bounds_hi,
    uint32_t d, uint32_t count, uint32_t nnz, uint32_t group_width,
    uint32_t grain, int64_t *out, int64_t *out_hi, int64_t *flags,
    uint32_t *slot, const uint32_t *census, const uint32_t *lineage,
    uint32_t lineage_count) {
    if (threadIdx.x) return;
    uint32_t group = blockIdx.x;
    uint32_t groups = group_width ? count / group_width : 0;
    if (group >= groups) return;
    uint32_t *status = ec_status(flags, group);
    if (upstream_refused(census, lineage, lineage_count, status)) return;
    if (!d || (d & 1u) || !count || !group_width || count % group_width ||
        grain < 1u || grain > 120u) {
        atomicOr(status, REFUSED_MALFORMED);
        return;
    }
    const size_t offset_words = 2u * ((size_t)count + 1u);
    const size_t column_words = 2u * (size_t)(nnz ? nnz : 1u);
    const size_t value_words = 4u * (size_t)(nnz ? nnz : 1u);
    for (size_t i = 0; i < offset_words; ++i)
        if (offsets[i] != offsets_hi[i]) atomicOr(status, REFUSED_MALFORMED);
    for (size_t i = 0; i < column_words; ++i)
        if (columns[i] != columns_hi[i]) atomicOr(status, REFUSED_MALFORMED);
    for (size_t i = 0; i < value_words; ++i)
        if (values[i] != values_hi[i]) atomicOr(status, REFUSED_MALFORMED);
    for (uint32_t i = 0; i < 4u; ++i) {
        if (basis_bounds[i] != basis_bounds_hi[i] ||
            delta_bounds[i] != delta_bounds_hi[i])
            atomicOr(status, REFUSED_MALFORMED);
    }
    for (size_t i = 0; i < 4u * (size_t)d; ++i)
        if (p[i] != p_hi[i]) atomicOr(status, REFUSED_MALFORMED);
    for (size_t i = 0; i < 8u * (size_t)count; ++i)
        if (c[i] != c_hi[i]) atomicOr(status, REFUSED_MALFORMED);
    const wide r_d = ((const wide *)basis_bounds)[0];
    const wide r_p = ((const wide *)delta_bounds)[0];
    const wide r_c = ((const wide *)delta_bounds)[1];
    if (r_d < 0 || r_p < 0 || r_c < 0) {
        atomicOr(status, REFUSED_MALFORMED);
        return;
    }
    const wide *pv = (const wide *)p;
    const wide *cv = (const wide *)c;
    const uint32_t group_begin = group * group_width;
    const uint32_t group_end = group_begin + group_width;
    // The radii cover both factors jointly. A maximum of the two separate norms
    // is not the Frobenius norm of the two-column factor matrix.
    wide p_norm = complete_norm(pv, 2u * d, status);
    wide c_norm = complete_norm(cv, 4u * count, status);
    wide r_g = add_checked(
        ft_ceil_product(r_p, c_norm, grain, status),
        add_checked(ft_ceil_product(r_c, p_norm, grain, status),
                    ft_ceil_product(r_p, r_c, grain, status), status),
        status);

    int64_t *ow = out + 6u * (size_t)group;
    wide *y = (wide *)ow;
    y[0] = 0;
    y[1] = 0;
    y[2] = 0;
    bool have_term = false;
    wide d_norm = 0;
    wide lo = 0, hi = 0;
    for (uint32_t row = group_begin; row < group_end; ++row) {
        if (offsets[2u * row] < 0 || offsets[2u * (row+1u)] < 0 ||
            (uint64_t)offsets[2u * row] > nnz || (uint64_t)offsets[2u * (row+1u)] > nnz) {
            atomicOr(status, REFUSED_MALFORMED); return;
        }
        uint32_t begin = (uint32_t)offsets[2u * row];
        uint32_t end = (uint32_t)offsets[2u * (row + 1u)];
        if (offsets[2u * row + 1u] != 0 || offsets[2u * (row + 1u) + 1u] != 0 ||
            begin > end || end > nnz) {
            atomicOr(status, REFUSED_MALFORMED);
            return;
        }
        for (uint32_t at = begin; at < end; ++at) {
            int64_t column_word = columns[2u * at];
            if (columns[2u * at + 1u] != 0 || column_word < 0 ||
                (column_word & 1) || (uint64_t)column_word + 1u >= d) {
                atomicOr(status, REFUSED_MALFORMED);
                return;
            }
            uint32_t column = (uint32_t)column_word;
            const wide *dv = (const wide *)values + 2u * at;
            d_norm = add_checked(
                d_norm,
                add_checked(ft_abs(dv[0], status), ft_abs(dv[1], status), status),
                status);
            const wide p0r = pv[column], p0i = pv[column + 1u];
            const wide p1r = pv[d + column], p1i = pv[d + column + 1u];
            const wide c0r = cv[2u * row], c0i = cv[2u * row + 1u];
            const wide c1r = cv[2u * count + 2u * row];
            const wide c1i = cv[2u * count + 2u * row + 1u];
            // G=P0 conj(C0)+P1 conj(C1), then Re(conj(G)D).
            MaterialInterval gr = mp_add(
                mp_add(mp_mul(mp_point(p0r), mp_point(c0r), grain, status),
                       mp_mul(mp_point(p0i), mp_point(c0i), grain, status), status),
                mp_add(mp_mul(mp_point(p1r), mp_point(c1r), grain, status),
                       mp_mul(mp_point(p1i), mp_point(c1i), grain, status), status),
                status);
            MaterialInterval gi = mp_add(
                mp_add(mp_mul(mp_point(p0i), mp_point(c0r), grain, status),
                       mp_neg(mp_mul(mp_point(p0r), mp_point(c0i), grain, status), status),
                       status),
                mp_add(mp_mul(mp_point(p1i), mp_point(c1r), grain, status),
                       mp_neg(mp_mul(mp_point(p1r), mp_point(c1i), grain, status), status),
                       status),
                status);
            MaterialInterval term = mp_add(
                mp_mul(gr, mp_point(dv[0]), grain, status),
                mp_mul(gi, mp_point(dv[1]), grain, status),
                status);
            if (!have_term) {
                lo = term.lo;
                hi = term.hi;
                have_term = true;
            } else {
                lo = add_checked(lo, term.lo, status);
                hi = add_checked(hi, term.hi, status);
            }
        }
    }
    if ((uint32_t)offsets[2u * count] != nnz) {
        atomicOr(status, REFUSED_MALFORMED);
        return;
    }
    // A zero centre group may still contain a nonzero true basis when r_d>0.
    wide numerical = add_checked(sub_checked(hi, lo, status), 1, status) >> 1;
    wide center = add_checked(lo, numerical, status);
    wide coupling = add_checked(ft_ceil_product(r_g, d_norm, grain, status),
        ft_ceil_product(add_checked(ft_ceil_product(p_norm, c_norm, grain, status), r_g, status),
                        r_d, grain, status), status);
    y[0] = center;
    y[1] = 0;
    y[2] = add_checked(numerical, coupling, status);
    ec_seal(ow, out_hi + 6u * (size_t)group, 2u, status);
}

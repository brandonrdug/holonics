// **The return through the body: the receiver return and the adjoint of every reaction.**
//
// Included by `exact_resident_section.cu` after its helpers; every kernel here reads the same
// wide carrier, directed placements, and census discipline that file states.  Nothing here is a
// second arithmetic.

// ---------------------------------------------------------------------------------------------
// the receiver return: the emitted face meets its next occurrence, and the differential of the
// normalized exponential receiver returns through the terminal reactions onto the cross-section
// ---------------------------------------------------------------------------------------------
//
// One block per emitted row `j`. The emission `e` and the reacted carrier `t = tanh(c/30)` are
// read from their resident tiles through a pointer table `tiles[4t..4t+4] = e_lo, e_hi, t_lo, t_hi`
// of `tile_count` tiles each `tile_width` wide, so no wide copy of the face is ever made. Three
// exact passes over the row: the null (the row's greatest upper endpoint, as the contact's), the
// partition `Z = Σ exp(e − null)`, and per coordinate
//
//   p   = exp(e − null) / Z                      the normalized exponential receiver face
//   d   = p − [o = next_j]                       its differential against the next occurrence
//   g   = 1 − t²                                 the adjoint of scale · tanh · scale (30 · 1/30)
//   u   = −(d · g)                               the deposit word, at grain 2^-F; the declared
//                                                learning shift enters only as the exponent of
//                                                the readout the host mounts over these words
//
// Written as an enclosure `[u_lo, u_hi]` into a `[width × rows]` section in the factorized
// map's `u[o · rank + j]` layout; the passage seals it to its midpoint under its own census.
extern "C" __global__ void section_receiver_return(
    const uint64_t *tiles, uint32_t tile_count, uint32_t tile_width,
    uint32_t rows, uint32_t width, const uint32_t *next,
    int32_t grain, uint32_t terms, uint32_t deposit_shift,
    int64_t *u_lo, int64_t *u_hi, int64_t *dpre_lo, int64_t *dpre_hi,
    uint32_t *refused, const uint32_t *census, const uint32_t *lineage, uint32_t lineage_count
) {
    extern __shared__ unsigned char shared_raw[];
    wide *scratch_lo = (wide *)shared_raw;
    wide *scratch_hi = scratch_lo + blockDim.x;
    __shared__ int stopped;
    __shared__ wide null_value, total_lo, total_hi;
    uint32_t j = blockIdx.x;
    if (j >= rows) return;
    if (threadIdx.x == 0) stopped = upstream_refused(census, lineage, lineage_count, refused);
    __syncthreads();
    if (stopped) return;
    if (tile_width == 0 || (uint64_t)tile_count * (uint64_t)tile_width != (uint64_t)width || next[j] >= width) {
        if (threadIdx.x == 0) atomicOr(refused, REFUSED_MALFORMED);
        return;
    }
    wide unit = (wide)1 << grain;
    // (a) the null: the row's greatest upper endpoint, one exact maximum reduction.
    wide local_null = -(((wide)1) << 126);
    for (uint32_t o = threadIdx.x; o < width; o += blockDim.x) {
        uint32_t tile = o / tile_width, within = o % tile_width;
        const int64_t *e_hi = (const int64_t *)tiles[4 * tile + 1];
        wide h = (wide)e_hi[(size_t)j * tile_width + within];
        if (h > local_null) local_null = h;
    }
    scratch_hi[threadIdx.x] = local_null;
    __syncthreads();
    for (uint32_t stride = blockDim.x / 2; stride > 0; stride >>= 1) {
        if (threadIdx.x < stride && scratch_hi[threadIdx.x + stride] > scratch_hi[threadIdx.x]) {
            scratch_hi[threadIdx.x] = scratch_hi[threadIdx.x + stride];
        }
        __syncthreads();
    }
    if (threadIdx.x == 0) null_value = scratch_hi[0];
    __syncthreads();
    // (b) the partition: every exponential enclosure contributes once, directed at both ends.
    wide part_lo = 0, part_hi = 0;
    for (uint32_t o = threadIdx.x; o < width; o += blockDim.x) {
        uint32_t tile = o / tile_width, within = o % tile_width;
        const int64_t *e_lo = (const int64_t *)tiles[4 * tile];
        const int64_t *e_hi = (const int64_t *)tiles[4 * tile + 1];
        size_t at = (size_t)j * tile_width + within;
        wide a_lo = (wide)e_lo[at] - null_value, a_hi = (wide)e_hi[at] - null_value;
        if (a_lo > 0) a_lo = 0;
        if (a_hi > 0) a_hi = 0;
        wide x_lo_lo, x_lo_hi, x_hi_lo, x_hi_hi;
        exp_nonpositive(a_lo, grain, terms, &x_lo_lo, &x_lo_hi, refused);
        exp_nonpositive(a_hi, grain, terms, &x_hi_lo, &x_hi_hi, refused);
        part_lo += x_lo_lo;
        part_hi += x_hi_hi;
    }
    scratch_lo[threadIdx.x] = part_lo;
    scratch_hi[threadIdx.x] = part_hi;
    __syncthreads();
    for (uint32_t stride = blockDim.x / 2; stride > 0; stride >>= 1) {
        if (threadIdx.x < stride) {
            scratch_lo[threadIdx.x] += scratch_lo[threadIdx.x + stride];
            scratch_hi[threadIdx.x] += scratch_hi[threadIdx.x + stride];
        }
        __syncthreads();
    }
    if (threadIdx.x == 0) { total_lo = scratch_lo[0]; total_hi = scratch_hi[0]; }
    __syncthreads();
    wide z_lo = total_lo, z_hi = total_hi;
    if (z_lo <= 0) {
        if (threadIdx.x == 0) atomicOr(refused, REFUSED_MALFORMED);
        return;
    }
    // (c) the differential, its adjoint through the terminal reactions, and the deposit word.
    uint32_t target = next[j];
    for (uint32_t o = threadIdx.x; o < width; o += blockDim.x) {
        uint32_t tile = o / tile_width, within = o % tile_width;
        const int64_t *e_lo = (const int64_t *)tiles[4 * tile];
        const int64_t *e_hi = (const int64_t *)tiles[4 * tile + 1];
        const int64_t *t_lo = (const int64_t *)tiles[4 * tile + 2];
        const int64_t *t_hi = (const int64_t *)tiles[4 * tile + 3];
        size_t at = (size_t)j * tile_width + within;
        wide a_lo = (wide)e_lo[at] - null_value, a_hi = (wide)e_hi[at] - null_value;
        if (a_lo > 0) a_lo = 0;
        if (a_hi > 0) a_hi = 0;
        wide x_lo_lo, x_lo_hi, x_hi_lo, x_hi_hi;
        exp_nonpositive(a_lo, grain, terms, &x_lo_lo, &x_lo_hi, refused);
        exp_nonpositive(a_hi, grain, terms, &x_hi_lo, &x_hi_hi, refused);
        // the face: the numerator at 2^-F lifted by F over the partition at 2^-F is p at 2^-F
        wide p_lo, p_hi;
        interval_quotient(x_lo_lo, x_hi_hi, z_lo, z_hi, grain, &p_lo, &p_hi, refused);
        if (p_hi > unit) p_hi = unit;
        if (p_lo < 0) p_lo = 0;
        wide d_lo = p_lo, d_hi = p_hi;
        if (o == target) { d_lo -= unit; d_hi -= unit; }
        // the adjoint factor g = 1 − t², the square taken as a square, not as four corners
        wide tl = (wide)t_lo[at], th = (wide)t_hi[at];
        wide sq_lo, sq_hi;
        if (tl >= 0)      { sq_lo = tl * tl; sq_hi = th * th; }
        else if (th <= 0) { sq_lo = th * th; sq_hi = tl * tl; }
        else              { wide a = tl * tl, b = th * th; sq_lo = 0; sq_hi = a > b ? a : b; }
        sq_lo = shift_floor(sq_lo, -grain, refused);
        sq_hi = shift_ceil(sq_hi, -grain, refused);
        wide g_lo = unit - sq_hi, g_hi = unit - sq_lo;
        if (g_lo < 0) g_lo = 0;
        if (g_hi > unit) g_hi = unit;
        wide dg_lo, dg_hi;
        corners(d_lo, d_hi, g_lo, g_hi, &dg_lo, &dg_hi, refused);
        dg_lo = shift_floor(dg_lo, -grain, refused);
        dg_hi = shift_ceil(dg_hi, -grain, refused);
        // the deposit word is −d·g at the grain coarsened by the derived deposit shift; the
        // learning shift is the mounted exponent, not a product here
        size_t out_at = (size_t)o * (size_t)rows + (size_t)j;
        u_lo[out_at] = to_word(shift_floor(-dg_hi, -(int)deposit_shift, refused), refused);
        u_hi[out_at] = to_word(shift_ceil(-dg_lo, -(int)deposit_shift, refused), refused);
        // the differential itself, at the contraction's output, for the return through the body
        size_t d_at = (size_t)j * (size_t)width + (size_t)o;
        dpre_lo[d_at] = to_word(dg_lo, refused);
        dpre_hi[d_at] = to_word(dg_hi, refused);
    }
}

// ---------------------------------------------------------------------------------------------
// the adjoint of the contraction: the returning differential crosses the map transposed
// ---------------------------------------------------------------------------------------------

// `partial[slot_base + a][t, i] = Σ_{o ∈ split a} map[o,i] · d[t,o]` over one aligned tile of
// `tile_rows` map rows, the tile's rows divided into `sub_splits` equal spans: the exact transpose
// of the contraction, kept as WIDE PARTIALS in the split-K standing (four words per coordinate,
// nothing rounded) so that `section_contract_join` folds every tile's and every split's partial
// under one fixed tree and rounds ONCE.  The partial standing's layout is the join's:
// `((slot · rows) + t) · inner + i`.
extern "C" __global__ void section_contract_transposed_partial(
    const int64_t *lo, const int64_t *hi, uint32_t rows, uint32_t tile_rows,
    const int64_t *map, uint32_t inner, uint32_t sub_splits, uint32_t slot_base,
    int64_t *partial, uint32_t admitted_node_octaves,
    uint32_t *slot, const uint32_t *census, const uint32_t *lineage, uint32_t lineage_count
) {
    uint32_t flat = blockIdx.x * blockDim.x + threadIdx.x;
    uint32_t per_split = rows * inner;
    if (flat >= per_split * sub_splits) return;
    if (upstream_refused(census, lineage, lineage_count, slot)) return;
    uint32_t a = flat / per_split, within = flat % per_split;
    uint32_t t = within / inner, i = within % inner;
    uint32_t span = (tile_rows + sub_splits - 1u) / sub_splits;
    uint32_t o0 = a * span;
    uint32_t o1 = (o0 + span) < tile_rows ? (o0 + span) : tile_rows;
    const int64_t *dlo = lo + (size_t)t * (size_t)tile_rows;
    const int64_t *dhi = hi + (size_t)t * (size_t)tile_rows;
    wide acc_lo = 0, acc_hi = 0;
    for (uint32_t o = o0; o < o1; ++o) {
        wide w = map[(size_t)o * (size_t)inner + i];
        if (w >= 0) { acc_lo += w * (wide)dlo[o]; acc_hi += w * (wide)dhi[o]; }
        else        { acc_lo += w * (wide)dhi[o]; acc_hi += w * (wide)dlo[o]; }
    }
    node_aperture(acc_lo, acc_hi, admitted_node_octaves, slot);
    size_t p = (((size_t)(slot_base + a) * (size_t)rows) + (size_t)t) * (size_t)inner + (size_t)i;
    partial[4 * p + 0] = (int64_t)(uint64_t)((uwide)acc_lo);
    partial[4 * p + 1] = (int64_t)(uint64_t)((uwide)acc_lo >> 64);
    partial[4 * p + 2] = (int64_t)(uint64_t)((uwide)acc_hi);
    partial[4 * p + 3] = (int64_t)(uint64_t)((uwide)acc_hi >> 64);
}

// The deposit factor of a differential: `u[o,t] = −mid(d[t,o]) · 2^-shift`, the returning
// differential transposed into the factorized map's `u` layout, sealed to its midpoint and
// coarsened by the derived shift. Written as a point enclosure; the learning shift is the mounted
// exponent, never a product here.
extern "C" __global__ void section_transpose_seal(
    const int64_t *lo, const int64_t *hi, uint32_t rows, uint32_t width, uint32_t shift,
    int64_t *out_lo, int64_t *out_hi, uint32_t *refused, const uint32_t *census, const uint32_t *lineage, uint32_t lineage_count
) {
    uint32_t flat = blockIdx.x * blockDim.x + threadIdx.x;
    if (flat >= rows * width) return;
    if (upstream_refused(census, lineage, lineage_count, refused)) return;
    uint32_t t = flat / width, o = flat % width;
    wide m = shift_floor(-((wide)lo[flat] + (wide)hi[flat]), -1, refused);
    wide word = shift_floor(m, -(int)shift, refused);
    size_t at = (size_t)o * (size_t)rows + (size_t)t;
    out_lo[at] = to_word(word, refused);
    out_hi[at] = to_word(word, refused);
}

// ---------------------------------------------------------------------------------------------
// the adjoints of the reactions: derivative factors as certified enclosures at the grain
// ---------------------------------------------------------------------------------------------

// The square of an enclosure taken as a square: `[lo,hi]²` is `[0, max²]` across zero and the
// ordered endpoint squares otherwise.
__device__ __forceinline__ void square_enclosure(wide a, wide b, wide *lo, wide *hi, uint32_t *refused) {
    wide aa = product_checked(a, a, refused), bb = product_checked(b, b, refused);
    if (a <= 0 && b >= 0) { *lo = 0; *hi = aa > bb ? aa : bb; }
    else { *lo = aa < bb ? aa : bb; *hi = aa > bb ? aa : bb; }
}

// `g = 1 − t²` for a reacted carrier `t = tanh(·)` at the grain: the adjoint factor of the
// hyperbolic-tangent reaction, clamped to `[0, 1]` because `|tanh| ≤ 1` holds of the value.
extern "C" __global__ void section_one_minus_square(
    const int64_t *lo, const int64_t *hi, uint32_t count, int32_t grain,
    int64_t *out_lo, int64_t *out_hi, uint32_t *refused, const uint32_t *census, const uint32_t *lineage, uint32_t lineage_count
) {
    uint32_t at = blockIdx.x * blockDim.x + threadIdx.x;
    if (at >= count) return;
    if (upstream_refused(census, lineage, lineage_count, refused)) return;
    wide unit = (wide)1 << grain;
    wide sq_lo, sq_hi;
    square_enclosure((wide)lo[at], (wide)hi[at], &sq_lo, &sq_hi, refused);
    sq_lo = shift_floor(sq_lo, -grain, refused);
    sq_hi = shift_ceil(sq_hi, -grain, refused);
    wide g_lo = unit - sq_hi, g_hi = unit - sq_lo;
    if (g_lo < 0) g_lo = 0;
    if (g_hi > unit) g_hi = unit;
    if (g_hi < 0) g_hi = 0;
    if (g_lo > g_hi) g_lo = g_hi;
    out_lo[at] = to_word(g_lo, refused);
    out_hi[at] = to_word(g_hi, refused);
}

// The derivative of the source's `gelu_pytorch_tanh`:
//   y  = ½ x (1 + tanh u),  u = c1 (x + c2 x³)
//   y' = ½ (1 + tanh u) + ½ x (1 − tanh² u) c1 (1 + 3 c2 x²)
// Every factor is a certified enclosure at the grain, composed through corners with directed
// placement; the constants are the exact dyadic values of the source's binary64 words.
extern "C" __global__ void section_gelu_tanh_derivative(
    const int64_t *lo, const int64_t *hi, uint32_t count,
    int64_t c1_m, int32_t c1_e, int64_t c2_m, int32_t c2_e, int32_t grain, uint32_t terms,
    int64_t *out_lo, int64_t *out_hi, uint32_t *refused, const uint32_t *census, const uint32_t *lineage, uint32_t lineage_count
) {
    uint32_t at = blockIdx.x * blockDim.x + threadIdx.x;
    if (at >= count) return;
    if (upstream_refused(census, lineage, lineage_count, refused)) return;
    wide unit = (wide)1 << grain;
    wide a = lo[at], b = hi[at];
    // x² and x³ exactly as the forward forms them.
    wide sq_lo, sq_hi;
    square_enclosure(a, b, &sq_lo, &sq_hi, refused);
    sq_lo = shift_floor(sq_lo, -grain, refused); sq_hi = shift_ceil(sq_hi, -grain, refused);
    uint32_t oa = octaves_of(magnitude(a) > magnitude(b) ? magnitude(a) : magnitude(b));
    uint32_t osq = octaves_of(magnitude(sq_lo) > magnitude(sq_hi) ? magnitude(sq_lo) : magnitude(sq_hi));
    int s = (oa + osq + 1 > 126u) ? (int)(oa + osq + 1 - 126u) : 0;
    wide sqs_lo = shift_floor(sq_lo, -s, refused), sqs_hi = shift_ceil(sq_hi, -s, refused);
    wide cube_lo, cube_hi;
    corners(a, b, sqs_lo, sqs_hi, &cube_lo, &cube_hi, refused);
    cube_lo = shift_floor(cube_lo, -(grain - s), refused); cube_hi = shift_ceil(cube_hi, -(grain - s), refused);
    wide tll, tlh, thl, thh;
    dyadic_scale(cube_lo, c2_m, c2_e, &tll, &tlh, refused);
    dyadic_scale(cube_hi, c2_m, c2_e, &thl, &thh, refused);
    wide t_lo = tll < thl ? tll : thl, t_hi = tlh > thh ? tlh : thh;
    wide in_lo = a + t_lo, in_hi = b + t_hi;
    wide ull, ulh, uhl, uhh;
    dyadic_scale(in_lo, c1_m, c1_e, &ull, &ulh, refused);
    dyadic_scale(in_hi, c1_m, c1_e, &uhl, &uhh, refused);
    wide u_lo = ull < uhl ? ull : uhl, u_hi = ulh > uhh ? ulh : uhh;
    // tanh u as an enclosure, monotone in u.
    wide th_lo, th_hi, d_lo, d_hi;
    if (u_lo >= 0) { tanh_nonnegative(u_lo, grain, terms, &th_lo, &d_hi, refused); }
    else { wide l, h; tanh_nonnegative(-u_lo, grain, terms, &l, &h, refused); th_lo = -h; }
    if (u_hi >= 0) { tanh_nonnegative(u_hi, grain, terms, &d_lo, &th_hi, refused); }
    else { wide l, h; tanh_nonnegative(-u_hi, grain, terms, &l, &h, refused); th_hi = -l; }
    (void)d_lo; (void)d_hi;
    // A = ½ (1 + tanh u) ∈ [0, 1]
    wide A_lo = shift_floor(unit + th_lo, -1, refused), A_hi = shift_ceil(unit + th_hi, -1, refused);
    if (A_lo < 0) A_lo = 0;
    if (A_hi > unit) A_hi = unit;
    // G = 1 − tanh² u ∈ [0, 1]
    wide thsq_lo, thsq_hi;
    square_enclosure(th_lo, th_hi, &thsq_lo, &thsq_hi, refused);
    thsq_lo = shift_floor(thsq_lo, -grain, refused); thsq_hi = shift_ceil(thsq_hi, -grain, refused);
    wide G_lo = unit - thsq_hi, G_hi = unit - thsq_lo;
    if (G_lo < 0) G_lo = 0;
    if (G_hi > unit) G_hi = unit;
    // P = 1 + 3 c2 x²: `3 c2` is the dyadic `3 c2_m · 2^c2_e`.
    wide pll, plh, phl, phh;
    dyadic_scale(sq_lo, 3 * c2_m, c2_e, &pll, &plh, refused);
    dyadic_scale(sq_hi, 3 * c2_m, c2_e, &phl, &phh, refused);
    wide P_lo = unit + (pll < phl ? pll : phl), P_hi = unit + (plh > phh ? plh : phh);
    // B = ½ · x · G · c1 · P, every product placed back at the grain.
    wide xg_lo, xg_hi;
    corners(a, b, G_lo, G_hi, &xg_lo, &xg_hi, refused);
    xg_lo = shift_floor(xg_lo, -grain, refused); xg_hi = shift_ceil(xg_hi, -grain, refused);
    wide xgp_lo, xgp_hi;
    corners(xg_lo, xg_hi, P_lo, P_hi, &xgp_lo, &xgp_hi, refused);
    xgp_lo = shift_floor(xgp_lo, -grain, refused); xgp_hi = shift_ceil(xgp_hi, -grain, refused);
    wide bll, blh, bhl, bhh;
    dyadic_scale(xgp_lo, c1_m, c1_e, &bll, &blh, refused);
    dyadic_scale(xgp_hi, c1_m, c1_e, &bhl, &bhh, refused);
    wide B_lo = shift_floor(bll < bhl ? bll : bhl, -1, refused);
    wide B_hi = shift_ceil(blh > bhh ? blh : bhh, -1, refused);
    wide y_lo = A_lo + B_lo, y_hi = A_hi + B_hi;
    if (y_lo > y_hi) atomicOr(refused, REFUSED_INVERTED);
    out_lo[at] = to_word(y_lo, refused);
    out_hi[at] = to_word(y_hi, refused);
}

// Place one contiguous face of every row into a wider zero section: the adjoint of
// `section_select_columns`. Every coordinate of the output is written — the placed face or zero —
// so nothing is read from an unfounded word.
extern "C" __global__ void section_place_columns(
    const int64_t *lo, const int64_t *hi, uint32_t rows, uint32_t span, uint32_t out_width, uint32_t at,
    int64_t *out_lo, int64_t *out_hi, uint32_t *refused, const uint32_t *census, const uint32_t *lineage, uint32_t lineage_count
) {
    uint32_t flat = blockIdx.x * blockDim.x + threadIdx.x;
    if (flat >= rows * out_width) return;
    if (upstream_refused(census, lineage, lineage_count, refused)) return;
    uint32_t row = flat / out_width, column = flat % out_width;
    if (column >= at && column < at + span) {
        size_t source = (size_t)row * (size_t)span + (size_t)(column - at);
        out_lo[flat] = lo[source];
        out_hi[flat] = hi[source];
    } else {
        out_lo[flat] = 0;
        out_hi[flat] = 0;
    }
}

// The product of two enclosures placed at `2^-k`, each corner through the 256-bit product with
// directed rounding: the enclosure product where `corners` would leave the wide carrier.
__device__ __forceinline__ void interval_product_shift(
    wide al, wide ah, wide bl, wide bh, int k, wide *lo, wide *hi, uint32_t *refused
) {
    wide c1 = product_shift(al, bl, k, 0, refused), c2 = product_shift(al, bh, k, 0, refused);
    wide c3 = product_shift(ah, bl, k, 0, refused), c4 = product_shift(ah, bh, k, 0, refused);
    wide l = c1; if (c2 < l) l = c2; if (c3 < l) l = c3; if (c4 < l) l = c4;
    wide d1 = product_shift(al, bl, k, 1, refused), d2 = product_shift(al, bh, k, 1, refused);
    wide d3 = product_shift(ah, bl, k, 1, refused), d4 = product_shift(ah, bh, k, 1, refused);
    wide h = d1; if (d2 > h) h = d2; if (d3 > h) h = d3; if (d4 > h) h = d4;
    *lo = l; *hi = h;
}

// The adjoint of the RMS rebase.  With `r = (mean(x²) + eps)^{-1/2}` over the group of `n`,
//
//   dx_j = r · g_j · dy_j  −  (r³ / n) · x_j · Σ_i g_i x_i dy_i.
//
// One block per `(row, group)`, as the forward.  The root is re-derived exactly as the forward
// derives it (its own shift and grain from the group's census); the sum `Σ g x dy` is a second
// named barrier realized as a block reduction; `r²` and `r³` are placed at the root's grain; every
// product is directed and every enclosure is placed back at the section's grain.
extern "C" __global__ void section_rms_rebase_adjoint(
    const int64_t *lo, const int64_t *hi, const int64_t *d_lo, const int64_t *d_hi,
    uint32_t rows, uint32_t width, uint32_t group,
    const int64_t *gain, int32_t gain_e, int64_t eps_m, int32_t eps_e, int32_t grain,
    int64_t *out_lo, int64_t *out_hi, uint32_t *refused, const uint32_t *census, const uint32_t *lineage, uint32_t lineage_count
) {
    extern __shared__ unsigned char shared_raw[];
    wide *sum_lo = (wide *)shared_raw;
    wide *sum_hi = sum_lo + blockDim.x;
    uint32_t *oct = (uint32_t *)(sum_hi + blockDim.x);
    __shared__ wide r_lo, r_hi, c_lo, c_hi, r3_lo, r3_hi;
    __shared__ int32_t square_shift_s, rg_s, sum_shift_s;

    uint32_t groups_per_row = width / group;
    uint32_t row = blockIdx.x / groups_per_row;
    uint32_t which = blockIdx.x % groups_per_row;
    if (row >= rows) return;
    if (threadIdx.x == 0 && upstream_refused(census, lineage, lineage_count, refused)) { square_shift_s = -1; }
    else if (threadIdx.x == 0) { square_shift_s = 0; }
    __syncthreads();
    if (square_shift_s < 0) return;
    size_t base = (size_t)row * (size_t)width + (size_t)which * (size_t)group;

    // (a) the widest octave over the presented carrier, the differential, and the gain.
    uint32_t widest = 0, widest_gain = 0;
    for (uint32_t i = threadIdx.x; i < group; i += blockDim.x) {
        uwide ma = magnitude((wide)lo[base + i]), mb = magnitude((wide)hi[base + i]);
        uwide mc = magnitude((wide)d_lo[base + i]), md = magnitude((wide)d_hi[base + i]);
        uint32_t o = octaves_of(ma > mb ? ma : mb);
        uint32_t od = octaves_of(mc > md ? mc : md);
        if (o > widest) widest = o;
        if (od > widest) widest = od;
        if (gain != NULL) {
            uint32_t og = octaves_of(magnitude((wide)gain[i]));
            if (og > widest_gain) widest_gain = og;
        }
    }
    oct[threadIdx.x] = (widest << 8) | (widest_gain & 0xffu);
    __syncthreads();
    for (uint32_t stride = blockDim.x / 2; stride > 0; stride >>= 1) {
        if (threadIdx.x < stride) {
            uint32_t a = oct[threadIdx.x], b = oct[threadIdx.x + stride];
            uint32_t w = (a >> 8) > (b >> 8) ? (a >> 8) : (b >> 8);
            uint32_t g = (a & 0xffu) > (b & 0xffu) ? (a & 0xffu) : (b & 0xffu);
            oct[threadIdx.x] = (w << 8) | g;
        }
        __syncthreads();
    }
    if (threadIdx.x == 0) {
        uint32_t o = oct[0] >> 8, og = oct[0] & 0xffu;
        uint32_t lg = 0; while ((1u << lg) < group) ++lg;
        uint32_t squares = 2 * o + lg + 1;
        int32_t s = squares > 126u ? (int32_t)((squares - 126u + 1u) / 2u) : 0;
        // the sum Σ g x dy needs the gain's octaves beside two carrier octaves
        uint32_t sums = 2 * o + og + lg + 2;
        int32_t s2 = sums > 126u ? (int32_t)((sums - 126u + 1u) / 2u) : 0;
        if (s >= grain || s2 >= grain) { atomicOr(refused, REFUSED_CARRIER); s = -1; }
        square_shift_s = s;
        sum_shift_s = s2;
        int32_t f_prime = grain - (s < 0 ? 0 : s);
        int32_t rg = 126 - f_prime; if (rg > 60) rg = 60; if (rg < 0) rg = 0;
        rg_s = rg;
    }
    __syncthreads();
    int32_t square_shift = square_shift_s;
    if (square_shift < 0) return;
    int32_t rg = rg_s;
    int32_t sum_shift = sum_shift_s;
    int f_prime = grain - square_shift;

    // (b) the root, exactly as the forward derives it.
    wide part_lo = 0, part_hi = 0;
    for (uint32_t i = threadIdx.x; i < group; i += blockDim.x) {
        wide a = lo[base + i], b = hi[base + i];
        uwide least, greatest;
        if (a <= 0 && b >= 0) { least = 0; greatest = magnitude(a) > magnitude(b) ? magnitude(a) : magnitude(b); }
        else if (a > 0) { least = (uwide)a; greatest = (uwide)b; }
        else { least = magnitude(b); greatest = magnitude(a); }
        uwide ls = least >> square_shift;
        uwide gs = (greatest + (((uwide)1 << square_shift) - 1)) >> square_shift;
        part_lo += (wide)(ls * ls); part_hi += (wide)(gs * gs);
    }
    sum_lo[threadIdx.x] = part_lo; sum_hi[threadIdx.x] = part_hi;
    __syncthreads();
    for (uint32_t stride = blockDim.x / 2; stride > 0; stride >>= 1) {
        if (threadIdx.x < stride) { sum_lo[threadIdx.x] += sum_lo[threadIdx.x + stride]; sum_hi[threadIdx.x] += sum_hi[threadIdx.x + stride]; }
        __syncthreads();
    }
    if (threadIdx.x == 0) {
        wide mean_lo = div_floor(sum_lo[0], (wide)group, refused);
        wide mean_hi = div_ceil(sum_hi[0], (wide)group, refused);
        wide eps_lo = shift_floor((wide)eps_m, eps_e + 2 * f_prime, refused);
        wide eps_hi = shift_ceil((wide)eps_m, eps_e + 2 * f_prime, refused);
        wide a_lo = mean_lo + eps_lo, a_hi = mean_hi + eps_hi;
        if (a_lo <= 0) { atomicOr(refused, REFUSED_MALFORMED); a_lo = 1; if (a_hi < a_lo) a_hi = a_lo; }
        wide scale = (wide)1 << (f_prime + rg);
        r_lo = div_floor(scale, isqrt_ceil(a_hi), refused);
        r_hi = div_ceil(scale, isqrt_floor(a_lo), refused);
        // r² and r³ at the root's own grain, directed; r ≥ 0 so the endpoints are monotone.
        wide r2_lo = product_shift(r_lo, r_lo, rg, 0, refused), r2_hi = product_shift(r_hi, r_hi, rg, 1, refused);
        r3_lo = product_shift(r2_lo, r_lo, rg, 0, refused);
        r3_hi = product_shift(r2_hi, r_hi, rg, 1, refused);
    }
    __syncthreads();

    // (c) the second barrier: S = Σ_i g_i x_i dy_i at 2^-(2 f'' − gain_e), f'' = F − sum_shift.
    part_lo = 0; part_hi = 0;
    for (uint32_t i = threadIdx.x; i < group; i += blockDim.x) {
        wide xl = shift_floor(lo[base + i], -sum_shift, refused), xh = shift_ceil(hi[base + i], -sum_shift, refused);
        wide dl = shift_floor(d_lo[base + i], -sum_shift, refused), dh = shift_ceil(d_hi[base + i], -sum_shift, refused);
        wide gl = xl, gh = xh;
        if (gain != NULL) {
            wide g = gain[i];
            if (g >= 0) { gl = product_checked(xl, g, refused); gh = product_checked(xh, g, refused); }
            else { gl = product_checked(xh, g, refused); gh = product_checked(xl, g, refused); }
        }
        wide pl, ph;
        corners(gl, gh, dl, dh, &pl, &ph, refused);
        part_lo += pl; part_hi += ph;
    }
    sum_lo[threadIdx.x] = part_lo; sum_hi[threadIdx.x] = part_hi;
    __syncthreads();
    for (uint32_t stride = blockDim.x / 2; stride > 0; stride >>= 1) {
        if (threadIdx.x < stride) { sum_lo[threadIdx.x] += sum_lo[threadIdx.x + stride]; sum_hi[threadIdx.x] += sum_hi[threadIdx.x + stride]; }
        __syncthreads();
    }
    if (threadIdx.x == 0) {
        c_lo = div_floor(sum_lo[0], (wide)group, refused);
        c_hi = div_ceil(sum_hi[0], (wide)group, refused);
    }
    __syncthreads();
    wide rl = r_lo, rh = r_hi, r3l = r3_lo, r3h = r3_hi, cl = c_lo, ch = c_hi;
    int f2 = grain - sum_shift;

    // (d) per coordinate: A = r · g_j · dy_j and B = r³ · x_j · c, both placed at 2^-F.
    for (uint32_t i = threadIdx.x; i < group; i += blockDim.x) {
        wide dl = d_lo[base + i], dh = d_hi[base + i];
        wide xg_lo = dl, xg_hi = dh;
        int shift = rg;
        if (gain != NULL) {
            wide g = gain[i];
            if (g >= 0) { xg_lo = product_checked(dl, g, refused); xg_hi = product_checked(dh, g, refused); }
            else { xg_lo = product_checked(dh, g, refused); xg_hi = product_checked(dl, g, refused); }
            shift = rg - gain_e;
        }
        wide A_lo, A_hi;
        if (xg_lo >= 0) { A_lo = product_shift(xg_lo, rl, shift, 0, refused); A_hi = product_shift(xg_hi, rh, shift, 1, refused); }
        else if (xg_hi <= 0) { A_lo = product_shift(xg_lo, rh, shift, 0, refused); A_hi = product_shift(xg_hi, rl, shift, 1, refused); }
        else { A_lo = product_shift(xg_lo, rh, shift, 0, refused); A_hi = product_shift(xg_hi, rh, shift, 1, refused); }
        // t = x_j · c placed at 2^-F: x at 2^-F times c at 2^-(2 f2 − gain_e) shifted by 2 f2 − gain_e.
        wide t_lo, t_hi;
        interval_product_shift((wide)lo[base + i], (wide)hi[base + i], cl, ch, 2 * f2 - gain_e, &t_lo, &t_hi, refused);
        // B = t · r³ placed at 2^-F: r³ at 2^-rg, r³ ≥ 0.
        wide B_lo, B_hi;
        if (t_lo >= 0) { B_lo = product_shift(t_lo, r3l, rg, 0, refused); B_hi = product_shift(t_hi, r3h, rg, 1, refused); }
        else if (t_hi <= 0) { B_lo = product_shift(t_lo, r3h, rg, 0, refused); B_hi = product_shift(t_hi, r3l, rg, 1, refused); }
        else { B_lo = product_shift(t_lo, r3h, rg, 0, refused); B_hi = product_shift(t_hi, r3h, rg, 1, refused); }
        wide y_lo = A_lo - B_hi, y_hi = A_hi - B_lo;
        if (y_lo > y_hi) atomicOr(refused, REFUSED_INVERTED);
        out_lo[base + i] = to_word(y_lo, refused);
        out_hi[base + i] = to_word(y_hi, refused);
    }
}

// ---------------------------------------------------------------------------------------------
// the adjoint of the contact: the returning differential of the carried construction meets the
// same null, partition, and certified ratio family, and returns to the queries, keys, and values
// ---------------------------------------------------------------------------------------------
//
// With `w_tj = exp(s_tj − null_t) / Z_t` the founded weights and `o_t = Σ_j w_tj v_j`,
//
//   dw_tj = ⟨do_t, v_j⟩,   M_t = Σ_j w_tj dw_tj,   ds_tj = w_tj (dw_tj − M_t),
//   dq_t = Σ_j ds_tj k_j,  dk_j = Σ_t ds_tj q_t,   dv_j = Σ_t w_tj do_t.
//
// The queries kernel re-founds the weights exactly as the contact does (one block per `(t, h)`,
// the same bracket shift, null, partition, and ratio), writes `w_tj` and `ds_tj` at the grain
// into two resident scratch sections indexed `(t·heads + h)·reach_max + (j − start_t)`, and
// returns `dq_t`. The key and value kernels read those weights and return `dk_j` and `dv_j`
// with one thread per output coordinate: no atomic ever joins two occurrences.
extern "C" __global__ void section_contact_adjoint_queries(
    const int64_t *q_lo, const int64_t *q_hi, const int64_t *k_lo, const int64_t *k_hi,
    const int64_t *v_lo, const int64_t *v_hi, const int64_t *do_lo, const int64_t *do_hi,
    uint32_t rows, uint32_t heads, uint32_t kv_heads, uint32_t head_width, uint32_t window, uint32_t reach_max,
    int32_t grain, uint32_t terms,
    int64_t *dq_lo, int64_t *dq_hi, int64_t *w_lo, int64_t *w_hi, int64_t *ds_lo, int64_t *ds_hi,
    uint32_t *refused, uint32_t *reach_census, const uint32_t *census, const uint32_t *lineage, uint32_t lineage_count
) {
    extern __shared__ unsigned char shared_raw[];
    wide *scratch_lo = (wide *)shared_raw;
    wide *scratch_hi = scratch_lo + blockDim.x;
    wide *wl = scratch_hi + blockDim.x;
    wide *wh = wl + reach_max;
    wide *dsl = wh + reach_max;
    wide *dsh = dsl + reach_max;
    __shared__ int stopped;
    __shared__ wide null_value, total_lo, total_hi, m_lo, m_hi;
    __shared__ uint32_t oct_s[1024];
    __shared__ int bracket_shift;
    uint32_t t = blockIdx.x / heads;
    uint32_t h = blockIdx.x % heads;
    if (t >= rows) return;
    if (threadIdx.x == 0) stopped = upstream_refused(census, lineage, lineage_count, refused);
    __syncthreads();
    if (stopped) return;
    uint32_t group = heads / kv_heads;
    uint32_t g = h / group;
    uint32_t start = (t + 1 > window) ? (t + 1 - window) : 0;
    uint32_t reach = t - start + 1;
    if (reach > reach_max) { if (threadIdx.x == 0) atomicOr(refused, REFUSED_MALFORMED); return; }
    wide unit = (wide)1 << grain;
    size_t q_base = ((size_t)t * heads + h) * head_width;
    size_t do_base = q_base;
    // (a0) the bracket shift, as the contact derives it.
    {
        uint32_t widest = 0;
        for (uint32_t d = threadIdx.x; d < head_width; d += blockDim.x) {
            uwide a = magnitude((wide)q_lo[q_base + d]), b = magnitude((wide)q_hi[q_base + d]);
            uint32_t o = octaves_of(a > b ? a : b);
            if (o > widest) widest = o;
        }
        for (uint32_t r = 0; r < reach; ++r) {
            size_t k_base = ((size_t)(start + r) * kv_heads + g) * head_width;
            for (uint32_t d = threadIdx.x; d < head_width; d += blockDim.x) {
                uwide a = magnitude((wide)k_lo[k_base + d]), b = magnitude((wide)k_hi[k_base + d]);
                uint32_t o = octaves_of(a > b ? a : b);
                if (o > widest) widest = o;
            }
        }
        oct_s[threadIdx.x] = widest;
        __syncthreads();
        for (uint32_t stride = blockDim.x / 2; stride > 0; stride >>= 1) {
            if (threadIdx.x < stride && oct_s[threadIdx.x + stride] > oct_s[threadIdx.x]) oct_s[threadIdx.x] = oct_s[threadIdx.x + stride];
            __syncthreads();
        }
        if (threadIdx.x == 0) {
            uint32_t lg = 0; while ((1u << lg) < head_width) ++lg;
            uint32_t need = 2 * oct_s[0] + lg + 2;
            bracket_shift = need > 126u ? (int)((need - 126u + 1u) / 2u) : 0;
        }
        __syncthreads();
    }
    int bs = bracket_shift;
    // (a) the null.
    wide local_null = -(((wide)1) << 126);
    for (uint32_t r = threadIdx.x; r < reach; r += blockDim.x) {
        size_t k_base = ((size_t)(start + r) * kv_heads + g) * head_width;
        wide sl, sh;
        contact_bracket(q_lo, q_hi, k_lo, k_hi, q_base, k_base, head_width, bs, grain, &sl, &sh, refused);
        if (sh > local_null) local_null = sh;
    }
    scratch_hi[threadIdx.x] = local_null;
    __syncthreads();
    for (uint32_t stride = blockDim.x / 2; stride > 0; stride >>= 1) {
        if (threadIdx.x < stride && scratch_hi[threadIdx.x + stride] > scratch_hi[threadIdx.x]) scratch_hi[threadIdx.x] = scratch_hi[threadIdx.x + stride];
        __syncthreads();
    }
    if (threadIdx.x == 0) { null_value = scratch_hi[0]; atomicMax(reach_census, reach); }
    __syncthreads();
    // (b) the exponentials into the weight scratch and the partition.
    wide part_lo = 0, part_hi = 0;
    for (uint32_t r = threadIdx.x; r < reach; r += blockDim.x) {
        size_t k_base = ((size_t)(start + r) * kv_heads + g) * head_width;
        wide sl, sh;
        contact_bracket(q_lo, q_hi, k_lo, k_hi, q_base, k_base, head_width, bs, grain, &sl, &sh, refused);
        wide lo_arg = sl - null_value, hi_arg = sh - null_value;
        if (hi_arg > 0) hi_arg = 0;
        if (lo_arg > 0) lo_arg = 0;
        wide e_lo_lo, e_lo_hi, e_hi_lo, e_hi_hi;
        exp_nonpositive(lo_arg, grain, terms, &e_lo_lo, &e_lo_hi, refused);
        exp_nonpositive(hi_arg, grain, terms, &e_hi_lo, &e_hi_hi, refused);
        wl[r] = e_lo_lo; wh[r] = e_hi_hi;
        part_lo += e_lo_lo; part_hi += e_hi_hi;
    }
    scratch_lo[threadIdx.x] = part_lo; scratch_hi[threadIdx.x] = part_hi;
    __syncthreads();
    for (uint32_t stride = blockDim.x / 2; stride > 0; stride >>= 1) {
        if (threadIdx.x < stride) { scratch_lo[threadIdx.x] += scratch_lo[threadIdx.x + stride]; scratch_hi[threadIdx.x] += scratch_hi[threadIdx.x + stride]; }
        __syncthreads();
    }
    if (threadIdx.x == 0) { total_lo = scratch_lo[0]; total_hi = scratch_hi[0]; }
    __syncthreads();
    wide zl = total_lo, zh = total_hi;
    if (zl <= 0) { if (threadIdx.x == 0) atomicOr(refused, REFUSED_MALFORMED); return; }
    // (c) the weights and the carried differentials dw, and the sum M = Σ w dw.
    part_lo = 0; part_hi = 0;
    for (uint32_t r = threadIdx.x; r < reach; r += blockDim.x) {
        wide w_l, w_h;
        interval_quotient(wl[r], wh[r], zl, zh, grain, &w_l, &w_h, refused);
        if (w_l < 0) w_l = 0;
        if (w_h > unit) w_h = unit;
        wl[r] = w_l; wh[r] = w_h;
        size_t v_base = ((size_t)(start + r) * kv_heads + g) * head_width;
        wide acc_lo = 0, acc_hi = 0;
        for (uint32_t d = 0; d < head_width; ++d) {
            wide pl, ph;
            corners((wide)do_lo[do_base + d], (wide)do_hi[do_base + d], (wide)v_lo[v_base + d], (wide)v_hi[v_base + d], &pl, &ph, refused);
            acc_lo += pl; acc_hi += ph;
        }
        wide dw_l = shift_floor(acc_lo, -grain, refused), dw_h = shift_ceil(acc_hi, -grain, refused);
        dsl[r] = dw_l; dsh[r] = dw_h;
        wide pl, ph;
        corners(w_l, w_h, dw_l, dw_h, &pl, &ph, refused);
        part_lo += shift_floor(pl, -grain, refused); part_hi += shift_ceil(ph, -grain, refused);
    }
    scratch_lo[threadIdx.x] = part_lo; scratch_hi[threadIdx.x] = part_hi;
    __syncthreads();
    for (uint32_t stride = blockDim.x / 2; stride > 0; stride >>= 1) {
        if (threadIdx.x < stride) { scratch_lo[threadIdx.x] += scratch_lo[threadIdx.x + stride]; scratch_hi[threadIdx.x] += scratch_hi[threadIdx.x + stride]; }
        __syncthreads();
    }
    if (threadIdx.x == 0) { m_lo = scratch_lo[0]; m_hi = scratch_hi[0]; }
    __syncthreads();
    wide ml = m_lo, mh = m_hi;
    // (d) ds = w (dw − M), written beside w into the resident scratch.
    for (uint32_t r = threadIdx.x; r < reach; r += blockDim.x) {
        wide diff_l = dsl[r] - mh, diff_h = dsh[r] - ml;
        wide pl, ph;
        corners(wl[r], wh[r], diff_l, diff_h, &pl, &ph, refused);
        dsl[r] = shift_floor(pl, -grain, refused); dsh[r] = shift_ceil(ph, -grain, refused);
        size_t at = ((size_t)t * heads + h) * reach_max + r;
        w_lo[at] = to_word(wl[r], refused); w_hi[at] = to_word(wh[r], refused);
        ds_lo[at] = to_word(dsl[r], refused); ds_hi[at] = to_word(dsh[r], refused);
    }
    __syncthreads();
    // (e) dq_t = Σ_j ds_tj k_j, one thread per coordinate of the query.
    for (uint32_t d = threadIdx.x; d < head_width; d += blockDim.x) {
        wide acc_lo = 0, acc_hi = 0;
        for (uint32_t r = 0; r < reach; ++r) {
            size_t k_at = ((size_t)(start + r) * kv_heads + g) * head_width + d;
            wide pl, ph;
            corners(dsl[r], dsh[r], (wide)k_lo[k_at], (wide)k_hi[k_at], &pl, &ph, refused);
            acc_lo += pl; acc_hi += ph;
        }
        dq_lo[q_base + d] = to_word(shift_floor(acc_lo, -grain, refused), refused);
        dq_hi[q_base + d] = to_word(shift_ceil(acc_hi, -grain, refused), refused);
    }
}

// `dk_j = Σ_{t ≥ j, h ∈ g} ds_tj q_t`: one thread per coordinate of the key.
extern "C" __global__ void section_contact_adjoint_keys(
    const int64_t *q_lo, const int64_t *q_hi, const int64_t *ds_lo, const int64_t *ds_hi,
    uint32_t rows, uint32_t heads, uint32_t kv_heads, uint32_t head_width, uint32_t window, uint32_t reach_max,
    int32_t grain, int64_t *dk_lo, int64_t *dk_hi,
    uint32_t *refused, const uint32_t *census, const uint32_t *lineage, uint32_t lineage_count
) {
    uint32_t flat = blockIdx.x * blockDim.x + threadIdx.x;
    if (flat >= rows * kv_heads * head_width) return;
    if (upstream_refused(census, lineage, lineage_count, refused)) return;
    uint32_t j = flat / (kv_heads * head_width);
    uint32_t g = (flat / head_width) % kv_heads;
    uint32_t d = flat % head_width;
    uint32_t group = heads / kv_heads;
    uint32_t t_end = (j + window < rows) ? (j + window) : rows;
    wide acc_lo = 0, acc_hi = 0;
    for (uint32_t t = j; t < t_end; ++t) {
        uint32_t start = (t + 1 > window) ? (t + 1 - window) : 0;
        if (j < start) continue;
        for (uint32_t h = g * group; h < (g + 1) * group; ++h) {
            size_t at = ((size_t)t * heads + h) * reach_max + (j - start);
            size_t q_at = ((size_t)t * heads + h) * head_width + d;
            wide pl, ph;
            corners((wide)ds_lo[at], (wide)ds_hi[at], (wide)q_lo[q_at], (wide)q_hi[q_at], &pl, &ph, refused);
            acc_lo += pl; acc_hi += ph;
        }
    }
    dk_lo[flat] = to_word(shift_floor(acc_lo, -grain, refused), refused);
    dk_hi[flat] = to_word(shift_ceil(acc_hi, -grain, refused), refused);
}

// `dv_j = Σ_{t ≥ j, h ∈ g} w_tj do_t`: one thread per coordinate of the value.
extern "C" __global__ void section_contact_adjoint_values(
    const int64_t *do_lo, const int64_t *do_hi, const int64_t *w_lo, const int64_t *w_hi,
    uint32_t rows, uint32_t heads, uint32_t kv_heads, uint32_t head_width, uint32_t window, uint32_t reach_max,
    int32_t grain, int64_t *dv_lo, int64_t *dv_hi,
    uint32_t *refused, const uint32_t *census, const uint32_t *lineage, uint32_t lineage_count
) {
    uint32_t flat = blockIdx.x * blockDim.x + threadIdx.x;
    if (flat >= rows * kv_heads * head_width) return;
    if (upstream_refused(census, lineage, lineage_count, refused)) return;
    uint32_t j = flat / (kv_heads * head_width);
    uint32_t g = (flat / head_width) % kv_heads;
    uint32_t d = flat % head_width;
    uint32_t group = heads / kv_heads;
    uint32_t t_end = (j + window < rows) ? (j + window) : rows;
    wide acc_lo = 0, acc_hi = 0;
    for (uint32_t t = j; t < t_end; ++t) {
        uint32_t start = (t + 1 > window) ? (t + 1 - window) : 0;
        if (j < start) continue;
        for (uint32_t h = g * group; h < (g + 1) * group; ++h) {
            size_t at = ((size_t)t * heads + h) * reach_max + (j - start);
            size_t do_at = ((size_t)t * heads + h) * head_width + d;
            wide pl, ph;
            corners((wide)w_lo[at], (wide)w_hi[at], (wide)do_lo[do_at], (wide)do_hi[do_at], &pl, &ph, refused);
            acc_lo += pl; acc_hi += ph;
        }
    }
    dv_lo[flat] = to_word(shift_floor(acc_lo, -grain, refused), refused);
    dv_hi[flat] = to_word(shift_ceil(acc_hi, -grain, refused), refused);
}


// [definition; theory, November 13, the design record of that day §4.4a; P60 item 2] **The opening's comparison at every place, on the card**: bit
// for bit the host's `moment::cavity_moment_parts_exact`, `Field::cavity_forward` (the cavity openings), `moment::cavity_moment_return_exact`,
// `moment::cavity_pace_return` and their consumers in `Field::opening_compare_return`. The opening's read (the lane chart, the lift `R⁰`, `tied`, the
// face, its covector and their returns) runs through the field's own entries with the batch's words' open-site mask set to the compared places, so
// only the cavity's own operands are here: the cavity moments, the cavity openings, the cavity's far prefixes, its return and its clocks' covector.
//
// Included by `field.cu` after the paced moment kernels (`PacedMode`, `paced_mode`, `paced_absolute`, `moment_skin_back`, `re_pair`, `turn_dev`,
// `skin_dev`, `turn_rate_dev`, `turned_back_dev`), which it reuses and does not restate.
//
// A place `t` (batch site `g`) is read silent: its own two terms are absent (no distance-zero term on either strand) and its own stride is bare, so
// the sources before it are read from its cavity clock `τ_c = τ_(t−1) + 1`, `σ_c = σ_(t−1) + 1` (zero at a region's first place), and those after it
// at their standing phases relative to its standing clock (both move together past `t`). A plain region (every rate one) reads the resident ring at
// the byte place, where the cavity clock is the standing one. Faces are formed directly from the clocks (`turn_dev`, `skin_dev`: the integers the
// host's `Field::turn` and `Field::skin` form), never from a store a fill left for another clock.

#pragma once

#ifndef MOMENT_REFUSED_SHAPE
#error "field_cavity.cuh is included after field_moment.cuh"
#endif

// `ζ^ρ` of turned slot `slot` at a clock `ρ` on `2^(−24)` (`Field::turn`).
__device__ __forceinline__ MomentGauss cavity_turn(const FieldWords &w, uint32_t slot, wide rho) {
    wide re, im;
    turn_dev(w, slot, rho, &re, &im);
    return mg_make(re, im);
}

// The cavity clock of paced head `p` at batch site `g`, place `t`: `τ_(g−1) + 1` (`σ` alike), zero at a region's first place.
__device__ __forceinline__ wide cavity_tau(const FieldWords &w, int32_t p, uint64_t g, uint32_t t) {
    return t == 0 ? 0 : (wide)w.tau[(uint64_t)p * w.T + g - 1] + ((wide)1 << PACE_BITS);
}

__device__ __forceinline__ wide cavity_sigma(const FieldWords &w, int32_t p, uint64_t g, uint32_t t) {
    return t == 0 ? 0 : (wide)w.sigma[(uint64_t)p * w.T + g - 1] + ((wide)1 << PACE_BITS);
}

// The standing clocks.
__device__ __forceinline__ wide paced_tau(const FieldWords &w, int32_t p, uint64_t g) {
    return (wide)w.tau[(uint64_t)p * w.T + g];
}

__device__ __forceinline__ wide paced_sigma(const FieldWords &w, int32_t p, uint64_t g) {
    return (wide)w.sigma[(uint64_t)p * w.T + g];
}

// [definition; theory, November 13, §4.4a] **The cavity moments' two sides** of every moment mode at every site (the host's
// `cavity_moment_parts_exact`), from the standing strands `before`, `after` and their exact prefixes `up`, `down` (the forward's, `moments`):
// `sb[u][g]`, `sa[u][g]` each released to `2^(−16)` (the clocks' covector reads them apart), and their sum released once into the cavity moment
// `cmoment[g][2M]` at the unframed value's mode. A refused region's (the forward's admission) and a depth ring's are zero. Grid `(cells, modes)`.
extern "C" __global__ void field_cavity_moment_all(const MomentWords *ws, const uint32_t *cmap, FieldWords fw, const int64_t *befores, const int64_t *afters, const wide *ups, const wide *downs, int64_t *sbs, int64_t *sas, int64_t *cmoment, uint64_t stride, uint64_t pre_stride) {
    const uint32_t u = blockIdx.y;
    const MomentWords &w = ws[u];
    const int64_t *before = befores + (uint64_t)u * stride, *after = afters + (uint64_t)u * stride;
    const wide *up0 = ups + (uint64_t)u * pre_stride, *down0 = downs + (uint64_t)u * pre_stride;
    int64_t *sb_out = sbs + (uint64_t)u * stride, *sa_out = sas + (uint64_t)u * stride;
    const bool dead = cmap[u] >> 31;
    const uint32_t cm = cmap[u] & 0x7FFFFFFFu;
    for (uint64_t g = (uint64_t)blockIdx.x * blockDim.x + threadIdx.x; g < w.T; g += (uint64_t)gridDim.x * blockDim.x) {
        const uint32_t r = w.site_region[g], t = w.site_pos[g];
        if (!w.ok[r] || dead) {
            sb_out[2 * g] = sb_out[2 * g + 1] = sa_out[2 * g] = sa_out[2 * g + 1] = 0;
            cmoment[g * fw.M2 + cm] = 0;
            cmoment[g * fw.M2 + fw.M + cm] = 0;
            continue;
        }
        const uint64_t first = w.region_off[r];
        const uint32_t sites = w.region_off[r + 1] - (uint32_t)first;
        const wide *up = up0 + 2 * (first + r), *down = down0 + 2 * (first + r);
        const PacedMode pm = paced_mode(fw, cmap[u], r);
        const uint32_t forward = t + 1 < (uint32_t)NEAR ? t + 1 : (uint32_t)NEAR;
        const uint32_t backward = sites - t < (uint32_t)NEAR ? sites - t : (uint32_t)NEAR;
        MomentGauss sb = mg_make(0, 0), sa = mg_make(0, 0);
        if (pm.plain) {
            bool ok = true;
            for (uint32_t d = 1; d < forward; ++d) {
                MomentGauss z;
                ok = moment_zeta(w.ring, w.n, w.ring_len, -(int64_t)d, &z) && ok;
                sb = mg_add(sb, moment_near(z, (wide)w.decay[d], mg_load(before, g - d)));
            }
            for (uint32_t d = 1; d < backward; ++d) {
                MomentGauss z;
                ok = moment_zeta(w.ring, w.n, w.ring_len, (int64_t)d, &z) && ok;
                sa = mg_add(sa, moment_near(z, (wide)w.decay[d], mg_load(after, g + d)));
            }
            if (!ok) {
                atomicOr(fw.status, MOMENT_REFUSED_SHAPE);
            }
            const MomentGauss home = mg_conj(moment_absolute(w.ring, w.n, t));
            for (uint32_t level = 2; ((uint64_t)1 << level) < sites; ++level) {
                uint32_t lo, hi;
                const wide dk = (wide)w.decay[(uint64_t)1 << level];
                if (moment_octave(t, sites, level, false, &lo, &hi)) {
                    sb = mg_add(sb, mg_scale(mg_mul(home, mg_sub(mg_load_wide(up, hi + 1), mg_load_wide(up, lo))), dk));
                }
                if (moment_octave(t, sites, level, true, &lo, &hi)) {
                    sa = mg_add(sa, mg_scale(mg_mul(home, mg_sub(mg_load_wide(down, hi + 1), mg_load_wide(down, lo))), dk));
                }
            }
        } else {
            const wide tc = cavity_tau(fw, pm.p, g, t), sc = cavity_sigma(fw, pm.p, g, t);
            const wide tt = paced_tau(fw, pm.p, g), st = paced_sigma(fw, pm.p, g);
            for (uint32_t d = 1; d < forward; ++d) {
                const uint64_t k = g - d;
                sb = mg_add(sb, moment_near(cavity_turn(fw, pm.slot, paced_tau(fw, pm.p, k) - tc), skin_dev(fw, pm.slot, sc - paced_sigma(fw, pm.p, k)), mg_load(before, k)));
            }
            for (uint32_t d = 1; d < backward; ++d) {
                const uint64_t k = g + d;
                sa = mg_add(sa, moment_near(cavity_turn(fw, pm.slot, paced_tau(fw, pm.p, k) - tt), skin_dev(fw, pm.slot, st - paced_sigma(fw, pm.p, k)), mg_load(after, k)));
            }
            const MomentGauss home_c = mg_conj(cavity_turn(fw, pm.slot, tc));
            const MomentGauss home = mg_conj(paced_absolute(fw, w, pm, g));
            for (uint32_t level = 2; ((uint64_t)1 << level) < sites; ++level) {
                uint32_t lo, hi;
                if (moment_octave(t, sites, level, false, &lo, &hi)) {
                    const wide skin = skin_dev(fw, pm.slot, sc - paced_sigma(fw, pm.p, g - ((uint64_t)1 << level)));
                    sb = mg_add(sb, mg_scale(mg_mul(home_c, mg_sub(mg_load_wide(up, hi + 1), mg_load_wide(up, lo))), skin));
                }
                if (moment_octave(t, sites, level, true, &lo, &hi)) {
                    const wide skin = skin_dev(fw, pm.slot, st - paced_sigma(fw, pm.p, g + ((uint64_t)1 << level)));
                    sa = mg_add(sa, mg_scale(mg_mul(home, mg_sub(mg_load_wide(down, hi + 1), mg_load_wide(down, lo))), skin));
                }
            }
        }
        sb_out[2 * g] = fit64(rel(sb.re, MOMENT_COEFFICIENT_BITS), fw.status);
        sb_out[2 * g + 1] = fit64(rel(sb.im, MOMENT_COEFFICIENT_BITS), fw.status);
        sa_out[2 * g] = fit64(rel(sa.re, MOMENT_COEFFICIENT_BITS), fw.status);
        sa_out[2 * g + 1] = fit64(rel(sa.im, MOMENT_COEFFICIENT_BITS), fw.status);
        cmoment[g * fw.M2 + cm] = fit64(rel(sb.re + sa.re, MOMENT_COEFFICIENT_BITS), fw.status);
        cmoment[g * fw.M2 + fw.M + cm] = fit64(rel(sb.im + sa.im, MOMENT_COEFFICIENT_BITS), fw.status);
    }
}

// [definition; theory, November 13, §4.4] **Each place's cavity opening's rows** (the host's `Field::cavity_forward` before the moment's chart):
// `E(∗) + E₋(u_(t−1)) + E₊(u_(t+1))`, the unresolved row in place of the place's own, a neighbour only within the site's own region, a carried
// neighbour by its mixture (`opening_term`). The moment's chart on the cavity moment is added after it by `affine`. One thread a word.
extern "C" __global__ void field_cavity_open(FieldWords w, int64_t *cx) {
    const uint64_t cells = (uint64_t)w.T * w.D;
    for (uint64_t c = (uint64_t)blockIdx.x * blockDim.x + threadIdx.x; c < cells; c += (uint64_t)gridDim.x * blockDim.x) {
        const uint64_t t = c / w.D, i = c % w.D;
        int64_t x = w.theta[w.enc + (uint64_t)w.A * w.D + i];
        if (w.site_pos[t] > 0) {
            x += opening_term(w, w.enc_before, t - 1, i);
        }
        if (t + 1 < w.T && w.site_pos[t + 1] > 0) {
            x += opening_term(w, w.enc_after, t + 1, i);
        }
        cx[c] = x;
    }
}

// [definition; theory, November 13, P60 item 1e] **The cavity's far prefixes** (the host's `cavity_moment_return_exact`'s `sides`): for each moment
// mode, paced region, octave level `ℓ` and side, `sk[2(ℓ − 2) + left][j] = Σ_(t<j, t reads its octave on that side) D_t release(ζ_t δs_t, 30)`, the
// receivers that read their octave on the left at their cavity clocks (`ζ^(τ_c)`, `e^(−2π|σ_c − σ_(t−2^ℓ)|/n)`), those on the right at their standing
// ones. `sk` is `[u][row][T + R][2]`, a region's prefix at `first + r`, zero there.
//
// [realization; theory, November 13, G141 (G139's rule (d))] Formed in two passes, every bit the walk's: each term by one thread a mode, row and
// site (`field_cavity_terms_all`, its face, skin and release as the walk formed them), then the region's terms summed in order into the
// prefixes by one warp a mode, row and region (`field_cavity_scan_all`, integer sums, so any order gives the walk's bits). Where one thread a
// mode, region and row walked its region, 62,420 threads a section held the card for 10 ms forming their faces one after another.
extern "C" __global__ void field_cavity_terms_all(const MomentWords *ws, const uint32_t *cmap, FieldWords fw, const int64_t *dss, wide *sks, uint64_t stride, uint64_t sk_stride, uint32_t levels, uint32_t tm) {
    const uint64_t rows = 2 * (uint64_t)levels, cells = (uint64_t)tm * rows * fw.T;
    for (uint64_t c = (uint64_t)blockIdx.x * blockDim.x + threadIdx.x; c < cells; c += (uint64_t)gridDim.x * blockDim.x) {
        const uint64_t gt = c % fw.T;
        const uint32_t row = (uint32_t)((c / fw.T) % rows);
        const uint32_t u = (uint32_t)(c / (fw.T * rows));
        const uint32_t r = fw.site_region[gt];
        const MomentWords &w = ws[u];
        const PacedMode pm = paced_mode(fw, cmap[u], r);
        if (!w.ok[r] || pm.plain) {
            continue;
        }
        const uint32_t level = 2 + row / 2;
        const bool left = row % 2 == 1;
        const uint64_t first = w.region_off[r];
        const uint32_t sites = w.region_off[r + 1] - (uint32_t)first;
        const uint32_t t = (uint32_t)(gt - first);
        const int64_t *ds = dss + (uint64_t)u * stride;
        wide *out = sks + (uint64_t)u * sk_stride + ((uint64_t)row * (fw.T + fw.R) + first + r) * 2;
        const uint64_t pow = (uint64_t)1 << level;
        if (t == 0) {
            out[0] = 0;
            out[1] = 0;
        }
        const bool reads = pow < sites && (left ? t >= pow : (uint64_t)t + pow < sites);
        MomentGauss term = mg_make(0, 0);
        if (reads) {
            const MomentGauss face = left ? cavity_turn(fw, pm.slot, cavity_tau(fw, pm.p, gt, t)) : paced_absolute(fw, w, pm, gt);
            const MomentGauss turned = mg_mul(face, mg_load(ds, gt));
            const wide skin = left ? skin_dev(fw, pm.slot, cavity_sigma(fw, pm.p, gt, t) - paced_sigma(fw, pm.p, gt - pow)) : skin_dev(fw, pm.slot, paced_sigma(fw, pm.p, gt) - paced_sigma(fw, pm.p, gt + pow));
            term = mg_scale(mg_make(rel(turned.re, MOVE_BITS), rel(turned.im, MOVE_BITS)), skin);
        }
        out[2 * (uint64_t)(t + 1)] = term.re;
        out[2 * (uint64_t)(t + 1) + 1] = term.im;
    }
}

__device__ __forceinline__ wide shfl_up_ring(wide v, unsigned d) {
    const uwide u = (uwide)v;
    const uint64_t lo = __shfl_up_sync(0xffffffffu, (uint64_t)u, d);
    const uint64_t hi = __shfl_up_sync(0xffffffffu, (uint64_t)(u >> 64), d);
    return (wide)(((uwide)hi << 64) | lo);
}

__device__ __forceinline__ wide shfl_last_ring(wide v) {
    const uwide u = (uwide)v;
    const uint64_t lo = __shfl_sync(0xffffffffu, (uint64_t)u, 31);
    const uint64_t hi = __shfl_sync(0xffffffffu, (uint64_t)(u >> 64), 31);
    return (wide)(((uwide)hi << 64) | lo);
}

extern "C" __global__ void field_cavity_scan_all(const MomentWords *ws, const uint32_t *cmap, FieldWords fw, wide *sks, uint64_t sk_stride, uint32_t levels, uint32_t tm) {
    const uint32_t lane = threadIdx.x & 31;
    const uint64_t rows = 2 * (uint64_t)levels, cells = (uint64_t)tm * rows * fw.R;
    const uint64_t warps = (uint64_t)gridDim.x * (blockDim.x >> 5);
    for (uint64_t c = ((uint64_t)blockIdx.x * blockDim.x + threadIdx.x) >> 5; c < cells; c += warps) {
        const uint32_t row = (uint32_t)(c % rows);
        const uint32_t r = (uint32_t)((c / rows) % fw.R);
        const uint32_t u = (uint32_t)(c / (rows * fw.R));
        const MomentWords &w = ws[u];
        const PacedMode pm = paced_mode(fw, cmap[u], r);
        if (!w.ok[r] || pm.plain) {
            continue;
        }
        const uint64_t first = w.region_off[r];
        const uint32_t sites = w.region_off[r + 1] - (uint32_t)first;
        wide *out = sks + (uint64_t)u * sk_stride + ((uint64_t)row * (fw.T + fw.R) + first + r) * 2;
        wide carry_re = 0, carry_im = 0;
        for (uint32_t base = 0; base < sites; base += 32) {
            const uint32_t i = base + lane;
            wide re = i < sites ? out[2 * (uint64_t)(i + 1)] : 0, im = i < sites ? out[2 * (uint64_t)(i + 1) + 1] : 0;
            for (unsigned d = 1; d < 32; d <<= 1) {
                const wide nre = shfl_up_ring(re, d), nim = shfl_up_ring(im, d);
                if (lane >= d) {
                    re += nre;
                    im += nim;
                }
            }
            re += carry_re;
            im += carry_im;
            if (i < sites) {
                out[2 * (uint64_t)(i + 1)] = re;
                out[2 * (uint64_t)(i + 1) + 1] = im;
            }
            carry_re = shfl_last_ring(re);
            carry_im = shfl_last_ring(im);
        }
    }
}

// [definition; theory, November 13, P60 item 1e] **The cavity moments' return** of every moment mode (the host's `cavity_moments_return`): a source
// `k` returns to every place that reads it except itself, `δE⁺_k` from the places after it on their cavity clocks, `δE⁻_k` from those before it on
// their standing ones; the far part from the standing released prefix `q` on a plain region, from the cavity's far prefixes on a paced one; released
// once, `rel(Δ, 60)`. One thread a site; stored, not added. A refused region's return is zero.
extern "C" __global__ void field_cavity_return_paced_all(const MomentWords *ws, const uint32_t *cmap, FieldWords fw, const int64_t *dss, const wide *qs, const wide *sks, wide *d_before, wide *d_after, uint64_t stride, uint64_t pre_stride, uint64_t sk_stride) {
    const uint32_t u = blockIdx.y;
    const MomentWords &w = ws[u];
    const int64_t *ds = dss + (uint64_t)u * stride;
    d_before += (uint64_t)u * stride;
    d_after += (uint64_t)u * stride;
    const wide *q0 = qs + (uint64_t)u * pre_stride;
    const wide *sk = sks + (uint64_t)u * sk_stride;
    for (uint64_t g = (uint64_t)blockIdx.x * blockDim.x + threadIdx.x; g < w.T; g += (uint64_t)gridDim.x * blockDim.x) {
        const uint32_t r = w.site_region[g], k = w.site_pos[g];
        if (!w.ok[r]) {
            d_before[2 * g] = d_before[2 * g + 1] = d_after[2 * g] = d_after[2 * g + 1] = 0;
            continue;
        }
        const uint64_t first = w.region_off[r];
        const uint32_t sites = w.region_off[r + 1] - (uint32_t)first;
        const PacedMode pm = paced_mode(fw, cmap[u], r);
        const uint32_t forward = sites - k < (uint32_t)NEAR ? sites - k : (uint32_t)NEAR;
        const uint32_t backward = k + 1 < (uint32_t)NEAR ? k + 1 : (uint32_t)NEAR;
        MomentGauss plus = mg_make(0, 0), minus = mg_make(0, 0);
        if (pm.plain) {
            const wide *q = q0 + 2 * (first + r);
            bool ok = true;
            for (uint32_t d = 1; d < forward; ++d) {
                MomentGauss z;
                ok = moment_zeta(w.ring, w.n, w.ring_len, -(int64_t)d, &z) && ok;
                plus = mg_add(plus, moment_near_back(z, (wide)w.decay[d], mg_load(ds, g + d)));
            }
            for (uint32_t d = 1; d < backward; ++d) {
                MomentGauss z;
                ok = moment_zeta(w.ring, w.n, w.ring_len, (int64_t)d, &z) && ok;
                minus = mg_add(minus, moment_near_back(z, (wide)w.decay[d], mg_load(ds, g - d)));
            }
            if (!ok) {
                atomicOr(fw.status, MOMENT_REFUSED_SHAPE);
            }
            const MomentGauss home = mg_conj(moment_absolute(w.ring, w.n, k));
            for (uint32_t level = 2; ((uint64_t)1 << level) < sites; ++level) {
                uint32_t lo, hi;
                const wide dk = (wide)w.decay[(uint64_t)1 << level];
                if (moment_octave(k, sites, level, true, &lo, &hi)) {
                    plus = mg_add(plus, mg_scale(mg_mul(home, mg_sub(mg_load_wide(q, hi + 1), mg_load_wide(q, lo))), dk));
                }
                if (moment_octave(k, sites, level, false, &lo, &hi)) {
                    minus = mg_add(minus, mg_scale(mg_mul(home, mg_sub(mg_load_wide(q, hi + 1), mg_load_wide(q, lo))), dk));
                }
            }
        } else {
            const wide tk = paced_tau(fw, pm.p, g), sk_ = paced_sigma(fw, pm.p, g);
            for (uint32_t d = 1; d < forward; ++d) {
                const uint64_t gt = g + d;
                const uint32_t t = k + d;
                plus = mg_add(plus, moment_near_back(cavity_turn(fw, pm.slot, tk - cavity_tau(fw, pm.p, gt, t)), skin_dev(fw, pm.slot, cavity_sigma(fw, pm.p, gt, t) - sk_), mg_load(ds, gt)));
            }
            for (uint32_t d = 1; d < backward; ++d) {
                const uint64_t gt = g - d;
                minus = mg_add(minus, moment_near_back(cavity_turn(fw, pm.slot, tk - paced_tau(fw, pm.p, gt)), skin_dev(fw, pm.slot, paced_sigma(fw, pm.p, gt) - sk_), mg_load(ds, gt)));
            }
            const MomentGauss home = mg_conj(paced_absolute(fw, w, pm, g));
            for (uint32_t level = 2; ((uint64_t)1 << level) < sites; ++level) {
                uint32_t lo, hi;
                for (uint32_t side = 0; side < 2; side++) {
                    const bool right = side == 1;
                    if (!moment_octave(k, sites, level, right, &lo, &hi)) {
                        continue;
                    }
                    // The receivers right of `k` read it on their left (row `left`, their cavity clocks), those left of it on their right.
                    const uint32_t row = 2 * (level - 2) + (right ? 1 : 0);
                    const wide *pre = sk + ((uint64_t)row * (fw.T + fw.R) + first + r) * 2;
                    const MomentGauss far = mg_mul(home, mg_sub(mg_load_wide(pre, hi + 1), mg_load_wide(pre, lo)));
                    if (right) {
                        plus = mg_add(plus, far);
                    } else {
                        minus = mg_add(minus, far);
                    }
                }
            }
        }
        d_before[2 * g] = rel(plus.re, MOMENT_RETURN_RELEASE_BITS);
        d_before[2 * g + 1] = rel(plus.im, MOMENT_RETURN_RELEASE_BITS);
        d_after[2 * g] = rel(minus.re, MOMENT_RETURN_RELEASE_BITS);
        d_after[2 * g + 1] = rel(minus.im, MOMENT_RETURN_RELEASE_BITS);
    }
}

// One skin term of the cavity's clock covector whose receiver end is the cavity clock (`σ_c = sr`, the clock of site `rt = g − 1`), the other end
// site `gk` (the host's `cavity_pace_return`'s `skin` with `rt = t − 1`): as `moment_skin_back`, `sgn = sgn(σ_c − σ_k)`.
__device__ __forceinline__ void cavity_skin_back(const FieldWords &w, int32_t p, uint64_t rt, wide sr, uint64_t gk, wide decay, wide inner, wide b) {
    const wide sk = (wide)w.sigma[(uint64_t)p * w.T + gk];
    if (sr == sk) {
        return;
    }
    wide x = 0, y = 0;
    if (!mul_fits(inner, decay, &x) || !mul_fits(rel(x, MOVE_BITS), b, &y)) {
        atomicOr(w.status, REFUSED_CARRIER);
    }
    const wide at = rel(rel(y, MOVE_BITS), MOVE_BITS + FACE_BITS);
    const wide signed_at = sr > sk ? at : -at;
    add_wide(w.gsig + (uint64_t)p * w.T + rt, -signed_at);
    add_wide(w.gsig + (uint64_t)p * w.T + gk, signed_at);
}

// [definition; theory, November 13, P60 item 1e] **The cavity moments' clock covector** (the host's `moment::cavity_pace_return`), one thread a site
// and a moment mode of a paced head, every region (plain or not, as the standing clocks' covector), added into `gtau` and `gsig`: the receiver's
// before side to site `g − 1`'s clocks, its after side and its sources' to their own.
extern "C" __global__ void field_cavity_pace_back_all(const MomentWords *ws, const uint32_t *cmap, FieldWords fw, const int64_t *befores, const int64_t *afters, const int64_t *sbs, const int64_t *sas, const int64_t *dss, const wide *d_befores, const wide *d_afters, const wide *ups, const wide *downs, uint64_t stride, uint64_t pre_stride) {
    const uint32_t u = blockIdx.y;
    const MomentWords &w = ws[u];
    const int64_t *before = befores + (uint64_t)u * stride, *after = afters + (uint64_t)u * stride, *ds = dss + (uint64_t)u * stride;
    const int64_t *sb = sbs + (uint64_t)u * stride, *sa = sas + (uint64_t)u * stride;
    const wide *db = d_befores + (uint64_t)u * stride, *da = d_afters + (uint64_t)u * stride;
    const wide *up0 = ups + (uint64_t)u * pre_stride, *down0 = downs + (uint64_t)u * pre_stride;
    const bool dead = cmap[u] >> 31;
    const uint32_t cm = cmap[u] & 0x7FFFFFFFu;
    for (uint64_t g = (uint64_t)blockIdx.x * blockDim.x + threadIdx.x; g < w.T; g += (uint64_t)gridDim.x * blockDim.x) {
        const uint32_t r = w.site_region[g], t = w.site_pos[g];
        const PacedMode own = paced_mode(fw, cm, r);
        if (own.p < 0 || dead || !w.ok[r]) {
            continue;
        }
        const uint64_t first = w.region_off[r];
        const uint32_t sites = w.region_off[r + 1] - (uint32_t)first;
        const wide *up = up0 + 2 * (first + r), *down = down0 + 2 * (first + r);
        const int32_t p = own.p;
        const uint32_t slot = own.slot;
        const wide b = turn_rate_dev(fw, slot);
        const wide dr = (wide)ds[2 * g], di = (wide)ds[2 * g + 1];
        if (t > 0) {
            add_wide(fw.gtau + (uint64_t)p * fw.T + g - 1, -turned_back_dev(fw, b, dr, di, (wide)sb[2 * g], (wide)sb[2 * g + 1]));
        }
        wide dtau = -turned_back_dev(fw, b, dr, di, (wide)sa[2 * g], (wide)sa[2 * g + 1]);
        wide x = 0, y = 0;
        if (!mul_fits(db[2 * g + 1], (wide)before[2 * g], &x) || !mul_fits(db[2 * g], (wide)before[2 * g + 1], &y)) {
            atomicOr(fw.status, REFUSED_CARRIER);
        }
        const wide cb = x - y;
        if (!mul_fits(da[2 * g + 1], (wide)after[2 * g], &x) || !mul_fits(da[2 * g], (wide)after[2 * g + 1], &y)) {
            atomicOr(fw.status, REFUSED_CARRIER);
        }
        const wide ca = x - y;
        wide both = 0;
        if (!mul_fits(cb + ca, b, &both)) {
            atomicOr(fw.status, REFUSED_CARRIER);
        }
        dtau += rel(both, MOVE_BITS + FACE_BITS);
        add_wide(fw.gtau + (uint64_t)p * fw.T + g, dtau);
        // The skins, at the paced law on every region (the plain region's are the same law at whole variations).
        PacedMode pm = own;
        pm.plain = false;
        const wide tc = cavity_tau(fw, p, g, t), sc = cavity_sigma(fw, p, g, t);
        const wide tt = paced_tau(fw, p, g), st = paced_sigma(fw, p, g);
        const uint32_t forward = t + 1 < (uint32_t)NEAR ? t + 1 : (uint32_t)NEAR;
        for (uint32_t d = 1; d < forward; ++d) {
            const uint64_t gk = g - d;
            const MomentGauss face = cavity_turn(fw, slot, paced_tau(fw, p, gk) - tc);
            cavity_skin_back(fw, p, g - 1, sc, gk, skin_dev(fw, slot, sc - paced_sigma(fw, p, gk)), re_pair(fw, dr, di, mg_mul(face, mg_load(before, gk))), b);
        }
        const uint32_t backward = sites - t < (uint32_t)NEAR ? sites - t : (uint32_t)NEAR;
        for (uint32_t d = 1; d < backward; ++d) {
            const uint64_t gk = g + d;
            const MomentGauss face = cavity_turn(fw, slot, paced_tau(fw, p, gk) - tt);
            moment_skin_back(fw, pm, g, gk, skin_dev(fw, slot, st - paced_sigma(fw, p, gk)), re_pair(fw, dr, di, mg_mul(face, mg_load(after, gk))), b);
        }
        const MomentGauss home = mg_conj(paced_absolute(fw, w, own, g));
        const MomentGauss home_c = mg_conj(cavity_turn(fw, slot, tc));
        for (uint32_t level = 2; ((uint64_t)1 << level) < sites; ++level) {
            uint32_t lo, hi;
            const uint64_t pow = (uint64_t)1 << level;
            if (moment_octave(t, sites, level, true, &lo, &hi)) {
                const MomentGauss f = mg_mul(home, mg_sub(mg_load_wide(down, hi + 1), mg_load_wide(down, lo)));
                const MomentGauss face = mg_make(rel(f.re, MOVE_BITS), rel(f.im, MOVE_BITS));
                moment_skin_back(fw, pm, g, g + pow, skin_dev(fw, slot, st - paced_sigma(fw, p, g + pow)), re_pair(fw, dr, di, face), b);
            }
            if (moment_octave(t, sites, level, false, &lo, &hi)) {
                const MomentGauss f = mg_mul(home_c, mg_sub(mg_load_wide(up, hi + 1), mg_load_wide(up, lo)));
                const MomentGauss face = mg_make(rel(f.re, MOVE_BITS), rel(f.im, MOVE_BITS));
                cavity_skin_back(fw, p, g - 1, sc, g - pow, skin_dev(fw, slot, sc - paced_sigma(fw, p, g - pow)), re_pair(fw, dr, di, face), b);
            }
        }
    }
}

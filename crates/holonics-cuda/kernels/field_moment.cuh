// The field's site moment on the card (`holonics::hnn::tower::field::moment`, record
// `2026-11-01_THE_FIELD_DISPERSES_A_SITE_MEETS_ITS_RESONANCE_CLASS_AT_ITS_FALLOFF_AND_THE_ANSWER_LOCKS_UNDER_THE_PUMP`,
// §15.1): bit for bit the host's `moment_exact`, `moments`, `moment_return_exact` and `moments_return`
// (the return is the released law of `moment.rs`, not the exact transpose).
//
// Included by `field.cu` AFTER its integer prelude (`wide`, `uwide`, `rel`, `fit64`, `mag64`,
// `REFUSED_CARRIER`, `NEAR`, `FACE_BITS`, `MOVE_BITS`, `COVECTOR_BITS`), which it reuses and does not
// restate. It is not included anywhere yet; the driver integrates it with its host-card parity.
//
// [definition; agent-inferred, November 1] **A site carries its helical moment.** One turned ring slot
// has period `n`, resident phasors `ring[r] = e^(2πi r/n)` on `2^(−30)` for `r < ring_len = min(n,
// reach)` and skin decay `decay[d] = e^(−2π d/n)` on `2^(−30)` for `d < dreach = reach`. Write `ζ^r`
// for `ring[r rem_euclid n]`. A region of `S` sites carries two complex encodings a site on
// `2^(−16)`, `E⁺_k = before[k]` (read by every later site) and `E⁻_k = after[k]` (read by every
// earlier site), and
//
//   s_t = Σ_(k ≤ t, t−k < NEAR) ζ^(k−t) D(t−k) E⁺_k  +  Σ_(k ≥ t, k−t < NEAR) ζ^(k−t) D(k−t) E⁻_k
//       + Σ_(octaves (lo,hi,ℓ) of t, hi < t) D(2^ℓ) conj(ζ^t) Σ_(k=lo..hi) ζ^k E⁺_k
//       + Σ_(octaves (lo,hi,ℓ) of t, lo > t) D(2^ℓ) conj(ζ^t) Σ_(k=lo..hi) ζ^k E⁻_k
//
// (the field's contact turns a source at `k` seen from `t` by `ζ^(k−t)`: the framed word is `ζ^t w_t`).
// The octaves are `crowd_ranges(t, S)`: each `(lo, hi, ℓ)` one side of `t`, the places with `|t − k| ≥
// NEAR`, `⌊log₂ |t − k|⌋ = ℓ ≥ 2`, `2^ℓ < S` (`moment_octave`). The far sums are prefix sums `P[j] =
// Σ_(k<j) ζ^k E_k` of exact complex integers on `2^(−46)`: an octave is two reads.
//
// **One release.** Every term is carried on `2^(−106)` (a near term `ζ D E` is on `2^(−76)`, shifted
// up 30; a far term `D · conj(ζ^t) · P` is on `2^(−106)`), summed as integers (any order, any
// partition, the same bits), and released once to `2^(−16)`: `rel(s, 90)`, nearest, half away from zero.
//
// **The return** is the forward map's transpose with the turned covector released once a term. The
// exact transpose (multiplication by a Gaussian integer `W` transposes to multiplication by `conj(W)`)
// carries `conj(W) δs` on `2^(−114)`, and a covector's components reach tens of units (the value
// covector summed over the ticks at a 406-site crib region had l1 `2^28.1`), so its carrier
// `(S + 1) · 2^91 · l1(δs) < 2^127` admits only about `2^27.3`. A released reverse is the field's norm
// (every reverse product is released at its grain): the far part's prefix is of the covector turned and
// released once, one declared crossing a term at the covector's own grain. With `δs` on `2^(−24)`:
//
//   r_u   = rel(ζ^u δs_u, 30)                                        on 2^(−24)
//   Q[j]  = Σ_(u<j) r_u                                              on 2^(−24)
//   Δ⁺_k  = Σ_(t ≥ k, t−k < NEAR) conj(ζ^(k−t)) D(t−k) δs_t
//         + conj(ζ^k) Σ_(right octaves (lo,hi,ℓ) of k) D(2^ℓ) (Q[hi+1] − Q[lo])        on 2^(−84)
//   Δ⁻_k  = the same over t ≤ k and the left octaves of k
//   δE±_k = rel(Δ±_k, 60)                                            on 2^(−24)
//
// (`t` is in the right octave ℓ of `k` exactly when `k` is in the left octave ℓ of `t`; the single
// released prefix `Q` serves both). The near term has no shift up 30. The forward stays exact.
//
// **The carrier.** Forward: the l1 certificate `(S+1) · max(D̂,1) · R · max(R, 2^30) · Ê < 2^127` (`D̂`
// the largest decay over `d < S`, `R` the largest l1 of the resident ring, `Ê` the largest l1 of an
// encoding, `moment_certificate`) keeps every term and every partial sum of every order inside a signed
// 128-bit word. Return: `max(D̂,1) · R · (NEAR · G + S · (⌊R G / 2^30⌋ + 1)) < 2^127` (`G` the largest l1
// of a covector entry, `moment_return_certificate`): the turned term has l1 at most `R G`, the released
// term `⌊R G / 2^30⌋ + 1`, a range sum of the prefix at most `S` of them, a near term `D̂ R G`, and the
// far sources of a side are disjoint; with the founded rings it is below `2^61 (NEAR + 3 S) G`, so l1(δs)
// up to about `2^66 / (NEAR + 3 S)` is admitted (`2^55.7` at 406 sites). Both are properties of the
// exact inputs alone, so the card refuses the same regions as the host (`field_moment_admit`,
// `field_moment_return_admit`): a refused region's outputs are zero and `REFUSED_CARRIER` is set. A region
// whose shape the law cannot read (`n = 0`, `ring_len < min(n, S)`, `dreach < S`) is refused with
// `MOMENT_REFUSED_SHAPE`.
//
// **The launch** (one ring slot a launch; the driver sets `ring`, `n`, `ring_len`, `decay`, `dreach`):
//   forward   admit(before, after) → prefix(before → up) → prefix(after → down) → moment
//   return    return_admit(ds)     → return_prefix(ds → q)                      → moment_return
// `field_moment_admit`, `field_moment_return_admit` and the two prefix kernels run one block a region (a
// power-of-two block of threads); `field_moment` and `field_moment_return` one thread a site. The kernels
// take `blockDim.x` threads and the dynamic shared memory stated on each; the `wide` arrays are 16-byte
// aligned. Integer sums: the scan's partition (chunks of a region, in any number) changes no bit.

#pragma once

#ifndef REFUSED_CARRIER
#error "field_moment.cuh is included after field.cu's integer prelude"
#endif
#ifndef MOMENT_REFUSED_SHAPE
#define MOMENT_REFUSED_SHAPE 16u
#endif

static_assert(MOVE_BITS == 30 && FACE_BITS == 16 && COVECTOR_BITS == 24, "the moment's grains are the host's");
// The coefficient's grain, three faces on `2^(−30)` (`COEFFICIENT_BITS`): a moment is released this many bits.
#define MOMENT_COEFFICIENT_BITS (3 * MOVE_BITS)
// The return's grain, two faces on `2^(−30)` and a covector on `2^(−24)`: `2^(−84)`, released this many
// bits to the covector's own grain (the host's `RETURN_RELEASE_BITS`).
#define MOMENT_RETURN_BITS (2 * MOVE_BITS + COVECTOR_BITS)
#define MOMENT_RETURN_RELEASE_BITS (MOMENT_RETURN_BITS - COVECTOR_BITS)

// A Gaussian integer.
struct MomentGauss {
    wide re, im;
};

__host__ __device__ __forceinline__ MomentGauss mg_make(wide re, wide im) {
    MomentGauss g;
    g.re = re;
    g.im = im;
    return g;
}

__host__ __device__ __forceinline__ MomentGauss mg_add(MomentGauss a, MomentGauss b) {
    return mg_make(a.re + b.re, a.im + b.im);
}

__host__ __device__ __forceinline__ MomentGauss mg_sub(MomentGauss a, MomentGauss b) {
    return mg_make(a.re - b.re, a.im - b.im);
}

__host__ __device__ __forceinline__ MomentGauss mg_conj(MomentGauss a) {
    return mg_make(a.re, -a.im);
}

// `a · b`.
__host__ __device__ __forceinline__ MomentGauss mg_mul(MomentGauss a, MomentGauss b) {
    return mg_make(a.re * b.re - a.im * b.im, a.re * b.im + a.im * b.re);
}

// `conj(a) · b`.
__host__ __device__ __forceinline__ MomentGauss mg_mul_conj(MomentGauss a, MomentGauss b) {
    return mg_make(a.re * b.re + a.im * b.im, a.re * b.im - a.im * b.re);
}

__host__ __device__ __forceinline__ MomentGauss mg_scale(MomentGauss a, wide k) {
    return mg_make(a.re * k, a.im * k);
}

// An int64 pair at `p[2 i]`, `p[2 i + 1]`.
__host__ __device__ __forceinline__ MomentGauss mg_load(const int64_t *p, uint64_t i) {
    return mg_make((wide)p[2 * i], (wide)p[2 * i + 1]);
}

// A prefix entry at `p[2 j]`, `p[2 j + 1]`.
__host__ __device__ __forceinline__ MomentGauss mg_load_wide(const wide *p, uint64_t j) {
    return mg_make(p[2 * j], p[2 * j + 1]);
}

// `ζ^r` for a near difference `|r| < S` (the host's `Law::zeta`): the resident `ring[r rem_euclid n]`,
// or the conjugate of the resident `ring[−r]` where the ring holds fewer than `n` phasors (`n` past the
// reach): the ring is closed under conjugation bit for bit. False where neither is resident (never,
// in an admitted region).
__host__ __device__ __forceinline__ bool moment_zeta(const int64_t *ring, uint64_t n, uint64_t ring_len, int64_t r, MomentGauss *z) {
    int64_t m = r % (int64_t)n;
    if (m < 0) {
        m += (int64_t)n;
    }
    if ((uint64_t)m < ring_len) {
        *z = mg_load(ring, (uint64_t)m);
        return true;
    }
    const uint64_t c = n - (uint64_t)m;
    if (c < ring_len) {
        *z = mg_conj(mg_load(ring, c));
        return true;
    }
    *z = mg_make(0, 0);
    return false;
}

// `ζ^k` for an absolute place `k < S`: the resident `ring[k mod n]` (`k mod n < min(n, S) ≤ ring_len`).
__host__ __device__ __forceinline__ MomentGauss moment_absolute(const int64_t *ring, uint64_t n, uint32_t k) {
    return mg_load(ring, (uint64_t)k % n);
}

// A near term `ζ D x 2^30`: on `grain(x) − 30` (an encoding on `2^(−16)` gives `2^(−106)`).
__host__ __device__ __forceinline__ MomentGauss moment_near(MomentGauss z, wide decay, MomentGauss x) {
    return mg_scale(mg_scale(mg_mul(z, x), decay), (wide)1 << MOVE_BITS);
}

// A near term of the return, `conj(ζ) D x`: two faces and a covector on `2^(−24)`, so on `2^(−84)`, with
// no shift up.
__host__ __device__ __forceinline__ MomentGauss moment_near_back(MomentGauss z, wide decay, MomentGauss x) {
    return mg_scale(mg_mul_conj(z, x), decay);
}

// The octave `level ≥ 2` of place `i` in a region of `sites`, on its left (`right = false`: the places
// `[i − far, i − near]`, clipped at 0) or right (`[i + near, min(i + far, sites − 1)]`), with `near =
// max(2^level, NEAR)`, `far = 2^(level+1) − 1` (the host's `crowd_ranges`). False where the side is empty.
__host__ __device__ __forceinline__ bool moment_octave(uint32_t i, uint32_t sites, uint32_t level, bool right, uint32_t *lo, uint32_t *hi) {
    const uint64_t pow = (uint64_t)1 << level;
    const uint64_t near = pow > NEAR ? pow : (uint64_t)NEAR;
    const uint64_t far = (pow << 1) - 1;
    if (!right) {
        if ((uint64_t)i < near) {
            return false;
        }
        *hi = (uint32_t)(i - near);
        *lo = (uint64_t)i > far ? (uint32_t)(i - far) : 0u;
        return true;
    }
    if ((uint64_t)i + near >= sites) {
        return false;
    }
    *lo = (uint32_t)(i + near);
    *hi = (uint32_t)((uint64_t)i + far < (uint64_t)sites - 1 ? (uint64_t)i + far : (uint64_t)sites - 1);
    return true;
}

// The unreleased moment `S_t` of the site at place `t` on `2^(−106)`: `before`, `after` the region's
// strands (`sites` int64 pairs), `up`, `down` their prefix sums (`sites + 1` entries of two `wide`).
// False where a near phase is outside the resident ring.
__host__ __device__ __forceinline__ bool moment_site_exact(const int64_t *before, const int64_t *after, const wide *up, const wide *down, const int64_t *ring, uint64_t n, uint64_t ring_len, const int64_t *decay, uint32_t sites, uint32_t t, MomentGauss *out) {
    MomentGauss s = mg_make(0, 0);
    bool ok = true;
    const uint32_t forward = t + 1 < (uint32_t)NEAR ? t + 1 : (uint32_t)NEAR;
    for (uint32_t d = 0; d < forward; ++d) {
        MomentGauss z;
        ok = moment_zeta(ring, n, ring_len, -(int64_t)d, &z) && ok;
        s = mg_add(s, moment_near(z, (wide)decay[d], mg_load(before, t - d)));
    }
    const uint32_t backward = sites - t < (uint32_t)NEAR ? sites - t : (uint32_t)NEAR;
    for (uint32_t d = 0; d < backward; ++d) {
        MomentGauss z;
        ok = moment_zeta(ring, n, ring_len, (int64_t)d, &z) && ok;
        s = mg_add(s, moment_near(z, (wide)decay[d], mg_load(after, t + d)));
    }
    const MomentGauss home = mg_conj(moment_absolute(ring, n, t));
    for (uint32_t level = 2; ((uint64_t)1 << level) < sites; ++level) {
        uint32_t lo, hi;
        const wide d = (wide)decay[(uint64_t)1 << level];
        if (moment_octave(t, sites, level, false, &lo, &hi)) {
            const MomentGauss sum = mg_sub(mg_load_wide(up, hi + 1), mg_load_wide(up, lo));
            s = mg_add(s, mg_scale(mg_mul(home, sum), d));
        }
        if (moment_octave(t, sites, level, true, &lo, &hi)) {
            const MomentGauss sum = mg_sub(mg_load_wide(down, hi + 1), mg_load_wide(down, lo));
            s = mg_add(s, mg_scale(mg_mul(home, sum), d));
        }
    }
    *out = s;
    return ok;
}

// The unreleased return of the site at place `k` on `2^(−84)`: `plus = Δ⁺_k`, `minus = Δ⁻_k`, `ds` the
// region's covector (`sites` int64 pairs on `2^(−24)`), `q` the prefix sums of its turned, released
// terms `Σ_(u<j) rel(ζ^u δs_u, 30)` on `2^(−24)`.
__host__ __device__ __forceinline__ bool moment_return_site(const int64_t *ds, const wide *q, const int64_t *ring, uint64_t n, uint64_t ring_len, const int64_t *decay, uint32_t sites, uint32_t k, MomentGauss *plus, MomentGauss *minus) {
    MomentGauss p = mg_make(0, 0), m = mg_make(0, 0);
    bool ok = true;
    // δE⁺_k reads the sites t = k + d at ζ^(k−t) = ζ^(−d); δE⁻_k the sites t = k − d at ζ^d.
    const uint32_t forward = sites - k < (uint32_t)NEAR ? sites - k : (uint32_t)NEAR;
    for (uint32_t d = 0; d < forward; ++d) {
        MomentGauss z;
        ok = moment_zeta(ring, n, ring_len, -(int64_t)d, &z) && ok;
        p = mg_add(p, moment_near_back(z, (wide)decay[d], mg_load(ds, k + d)));
    }
    const uint32_t backward = k + 1 < (uint32_t)NEAR ? k + 1 : (uint32_t)NEAR;
    for (uint32_t d = 0; d < backward; ++d) {
        MomentGauss z;
        ok = moment_zeta(ring, n, ring_len, (int64_t)d, &z) && ok;
        m = mg_add(m, moment_near_back(z, (wide)decay[d], mg_load(ds, k - d)));
    }
    const MomentGauss home = mg_conj(moment_absolute(ring, n, k));
    for (uint32_t level = 2; ((uint64_t)1 << level) < sites; ++level) {
        uint32_t lo, hi;
        const wide d = (wide)decay[(uint64_t)1 << level];
        if (moment_octave(k, sites, level, true, &lo, &hi)) {
            p = mg_add(p, mg_scale(mg_mul(home, mg_sub(mg_load_wide(q, hi + 1), mg_load_wide(q, lo))), d));
        }
        if (moment_octave(k, sites, level, false, &lo, &hi)) {
            m = mg_add(m, mg_scale(mg_mul(home, mg_sub(mg_load_wide(q, hi + 1), mg_load_wide(q, lo))), d));
        }
    }
    *plus = p;
    *minus = m;
    return ok;
}

// A chunk `[lo, hi)` of a region's places scanned sequentially from zero: `out[k + 1] = Σ_(lo ≤ u ≤ k)
// ζ^u x_u` (the entries `lo + 1 ..= hi`), the chunk's total returned. The partition into chunks is
// arbitrary: integer sums.
__host__ __device__ __forceinline__ MomentGauss moment_scan_chunk(const int64_t *ring, uint64_t n, const int64_t *x, uint32_t lo, uint32_t hi, wide *out) {
    MomentGauss running = mg_make(0, 0);
    for (uint32_t k = lo; k < hi; ++k) {
        running = mg_add(running, mg_mul(moment_absolute(ring, n, k), mg_load(x, k)));
        out[2 * (uint64_t)(k + 1)] = running.re;
        out[2 * (uint64_t)(k + 1) + 1] = running.im;
    }
    return running;
}

// The chunk's entries `lo + 1 ..= hi` raised by the sum of the chunks before it.
__host__ __device__ __forceinline__ void moment_offset_chunk(uint32_t lo, uint32_t hi, MomentGauss offset, wide *out) {
    for (uint32_t k = lo; k < hi; ++k) {
        out[2 * (uint64_t)(k + 1)] += offset.re;
        out[2 * (uint64_t)(k + 1) + 1] += offset.im;
    }
}

// The same scan of the covector turned and released once a term to its own grain: `out[k + 1] = Σ_(lo ≤ u
// ≤ k) rel(ζ^u x_u, 30)` on `2^(−24)`, the chunk's total returned (device only: `rel` is).
__device__ __forceinline__ MomentGauss moment_scan_chunk_released(const int64_t *ring, uint64_t n, const int64_t *x, uint32_t lo, uint32_t hi, wide *out) {
    MomentGauss running = mg_make(0, 0);
    for (uint32_t k = lo; k < hi; ++k) {
        const MomentGauss turned = mg_mul(moment_absolute(ring, n, k), mg_load(x, k));
        running = mg_add(running, mg_make(rel(turned.re, MOVE_BITS), rel(turned.im, MOVE_BITS)));
        out[2 * (uint64_t)(k + 1)] = running.re;
        out[2 * (uint64_t)(k + 1) + 1] = running.im;
    }
    return running;
}

// `a · b < 2^128`: the product and false, or true on overflow (the host's `checked_mul` on `u128`).
__host__ __device__ __forceinline__ bool moment_mul_overflows(uwide a, uwide b, uwide *product) {
    const uint64_t ah = (uint64_t)(a >> 64), bh = (uint64_t)(b >> 64);
    if (ah != 0 && bh != 0) {
        return true;
    }
    const uwide al = (uint64_t)a, bl = (uint64_t)b;
    // One of `ah`, `bh` is zero, so the cross term is one product of two words.
    const uwide cross = (uwide)ah * bl + al * (uwide)bh;
    if ((cross >> 64) != 0) {
        return true;
    }
    const uwide low = al * bl;
    const uwide high = cross << 64;
    const uwide sum = low + high;
    if (sum < low) {
        return true;
    }
    *product = sum;
    return false;
}

// [definition; agent-inferred, November 1] **The l1 certificate** (the host's `certificate`):
// `(sites + 1) · max(decay_max, 1) · ring_l1 · max(ring_l1, 2^30) · input_l1 < 2^127`, the factors
// multiplied in that order and an overflow of a product a refusal.
__host__ __device__ __forceinline__ bool moment_certificate(uwide sites, uwide ring_l1, uwide decay_max, uwide input_l1) {
    const uwide unit = ring_l1 > ((uwide)1 << MOVE_BITS) ? ring_l1 : ((uwide)1 << MOVE_BITS);
    uwide bound = sites + 1;
    const uwide factors[4] = {decay_max > 1 ? decay_max : 1, ring_l1, unit, input_l1};
    for (int i = 0; i < 4; ++i) {
        if (moment_mul_overflows(bound, factors[i], &bound)) {
            return false;
        }
    }
    return bound < ((uwide)1 << 127);
}

// [definition; agent-inferred, November 1] **The return's l1 certificate** (the host's
// `return_certificate`): `max(decay_max, 1) · ring_l1 · (NEAR · input_l1 + sites · (⌊ring_l1 · input_l1 /
// 2^30⌋ + 1)) < 2^127`, the products formed in that order and an overflow of one a refusal.
__host__ __device__ __forceinline__ bool moment_return_certificate(uwide sites, uwide ring_l1, uwide decay_max, uwide input_l1) {
    uwide turned, released, product, inner, bound;
    if (moment_mul_overflows(ring_l1, input_l1, &turned)) {
        return false;
    }
    released = (turned >> MOVE_BITS) + 1;
    if (moment_mul_overflows((uwide)NEAR, input_l1, &product) || moment_mul_overflows(sites, released, &inner) || inner + product < inner) {
        return false;
    }
    inner += product;
    if (moment_mul_overflows(decay_max > 1 ? decay_max : 1, ring_l1, &product) || moment_mul_overflows(product, inner, &bound)) {
        return false;
    }
    return bound < ((uwide)1 << 127);
}

// The batch's regions and the ring slot one launch reads.
struct MomentWords {
    uint32_t R, T;
    const uint32_t *region_off;   // R + 1 offsets of each region's first site
    const uint32_t *site_region;  // T: each site's region
    const uint32_t *site_pos;     // T: each site's place within its region
    // The slot: its resident phasors (`ring_len = min(n, reach)` int64 pairs on `2^(−30)`), its period
    // `n` and its skin decay (`dreach = reach` entries on `2^(−30)`).
    const int64_t *ring;
    uint64_t n, ring_len;
    const int64_t *decay;
    uint64_t dreach;
    uint8_t *ok;                  // R: 1 where `field_moment_admit` / `field_moment_return_admit` admitted the region
    uint32_t *status;             // the batch's status word
};

__device__ __forceinline__ uwide moment_l1(int64_t re, int64_t im) {
    return (uwide)mag64(re) + (uwide)mag64(im);
}

__device__ __forceinline__ uwide moment_max(uwide a, uwide b) {
    return a > b ? a : b;
}

// A region's admission, by the forward certificate (`returning = false`: `x`, `y` the two strands) or the
// return's (`returning = true`: `x` the covector, `y` null), and the shape the law reads. One block a
// region, `blockDim.x` a power of two; dynamic shared memory `3 · blockDim.x · sizeof(uwide)`. Writes
// `w.ok[r]`; a refusal sets `REFUSED_CARRIER` (the certificate) or `MOMENT_REFUSED_SHAPE` in `w.status`.
__device__ __forceinline__ void moment_admit_regions(const MomentWords &w, const int64_t *x, const int64_t *y, bool returning) {
    extern __shared__ __align__(16) unsigned char moment_shared[];
    uwide *peak = (uwide *)moment_shared;
    const uint32_t B = blockDim.x;
    for (uint32_t r = blockIdx.x; r < w.R; r += gridDim.x) {
        const uint64_t first = w.region_off[r];
        const uint32_t sites = w.region_off[r + 1] - (uint32_t)first;
        const bool shape = w.n != 0 && w.ring_len >= (w.n < sites ? w.n : (uint64_t)sites) && w.dreach >= sites;
        uwide input = 0, decay_max = 0, ring_l1 = 0;
        if (shape) {
            for (uint32_t k = threadIdx.x; k < sites; k += B) {
                input = moment_max(input, moment_l1(x[2 * (first + k)], x[2 * (first + k) + 1]));
                if (y != nullptr) {
                    input = moment_max(input, moment_l1(y[2 * (first + k)], y[2 * (first + k) + 1]));
                }
                const int64_t d = w.decay[k];
                decay_max = moment_max(decay_max, (uwide)mag64(d));
            }
            const uint64_t resident = w.ring_len < w.n ? w.ring_len : w.n;
            for (uint64_t m = threadIdx.x; m < resident; m += B) {
                ring_l1 = moment_max(ring_l1, moment_l1(w.ring[2 * m], w.ring[2 * m + 1]));
            }
        }
        peak[threadIdx.x] = input;
        peak[B + threadIdx.x] = decay_max;
        peak[2 * B + threadIdx.x] = ring_l1;
        __syncthreads();
        for (uint32_t stride = B >> 1; stride > 0; stride >>= 1) {
            if (threadIdx.x < stride) {
                for (uint32_t u = 0; u < 3; ++u) {
                    peak[u * B + threadIdx.x] = moment_max(peak[u * B + threadIdx.x], peak[u * B + threadIdx.x + stride]);
                }
            }
            __syncthreads();
        }
        if (threadIdx.x == 0) {
            const bool admitted = shape && (returning ? moment_return_certificate(sites, peak[2 * B], peak[B], peak[0]) : moment_certificate(sites, peak[2 * B], peak[B], peak[0]));
            w.ok[r] = admitted ? 1 : 0;
            if (!shape) {
                atomicOr(w.status, MOMENT_REFUSED_SHAPE);
            } else if (!admitted) {
                atomicOr(w.status, REFUSED_CARRIER);
            }
        }
        __syncthreads();
    }
}

// The forward's admission: the strands `x` = `before`, `y` = `after`, by the forward certificate. Dynamic
// shared memory `3 · blockDim.x · sizeof(uwide)`.
extern "C" __global__ void field_moment_admit(MomentWords w, const int64_t *x, const int64_t *y) {
    moment_admit_regions(w, x, y, false);
}

// The return's admission: the covector `ds`, by the return's certificate. Dynamic shared memory `3 ·
// blockDim.x · sizeof(uwide)`.
extern "C" __global__ void field_moment_return_admit(MomentWords w, const int64_t *ds) {
    moment_admit_regions(w, ds, nullptr, true);
}

// The prefix sums of a strand `x` (`T` int64 pairs), region by region, into `pre` (`T + R` entries of two
// `wide`: region `r`'s `sites + 1` entries start at entry `first + r`): `P[j] = Σ_(k<j) ζ^k x_k` exact
// (`released = false`), or `Q[j] = Σ_(k<j) rel(ζ^k x_k, 30)` (`released = true`, the covector's). Each
// thread scans a chunk of the region; the chunks' totals are summed once and the offsets added: integer
// sums, so the partition changes no bit. One block a region; dynamic shared memory `blockDim.x ·
// sizeof(MomentGauss)`. A refused region's entries are left unwritten (never read).
__device__ __forceinline__ void moment_prefix_regions(const MomentWords &w, const int64_t *x, wide *pre, bool released) {
    extern __shared__ __align__(16) unsigned char moment_shared[];
    MomentGauss *totals = (MomentGauss *)moment_shared;
    const uint32_t B = blockDim.x;
    for (uint32_t r = blockIdx.x; r < w.R; r += gridDim.x) {
        if (!w.ok[r]) {
            continue;
        }
        const uint64_t first = w.region_off[r];
        const uint32_t sites = w.region_off[r + 1] - (uint32_t)first;
        wide *out = pre + 2 * (first + r);
        const int64_t *strand = x + 2 * first;
        const uint32_t length = (sites + B - 1) / B;
        const uint32_t lo = threadIdx.x * length < sites ? threadIdx.x * length : sites;
        const uint32_t hi = lo + length < sites ? lo + length : sites;
        if (threadIdx.x == 0) {
            out[0] = 0;
            out[1] = 0;
        }
        totals[threadIdx.x] = released ? moment_scan_chunk_released(w.ring, w.n, strand, lo, hi, out) : moment_scan_chunk(w.ring, w.n, strand, lo, hi, out);
        __syncthreads();
        if (threadIdx.x == 0) {
            MomentGauss running = mg_make(0, 0);
            for (uint32_t c = 0; c < B; ++c) {
                const MomentGauss total = totals[c];
                totals[c] = running;
                running = mg_add(running, total);
            }
        }
        __syncthreads();
        moment_offset_chunk(lo, hi, totals[threadIdx.x], out);
        __syncthreads();
    }
}

// The forward's prefix sums `P[j] = Σ_(k<j) ζ^k x_k`, exact on `2^(−46)`.
extern "C" __global__ void field_moment_prefix(MomentWords w, const int64_t *x, wide *pre) {
    moment_prefix_regions(w, x, pre, false);
}

// The return's prefix `Q[j] = Σ_(k<j) rel(ζ^k δs_k, 30)` of the covector turned and released once a term,
// on `2^(−24)`.
extern "C" __global__ void field_moment_return_prefix(MomentWords w, const int64_t *ds, wide *q) {
    moment_prefix_regions(w, ds, q, true);
}

// The moments `s_t` on `2^(−16)` (`T` int64 pairs): the unreleased `S_t` released once, `rel(S, 90)`.
// One thread a site. A refused region's moments are zero.
extern "C" __global__ void field_moment(MomentWords w, const int64_t *before, const int64_t *after, const wide *up, const wide *down, int64_t *s) {
    for (uint64_t g = (uint64_t)blockIdx.x * blockDim.x + threadIdx.x; g < w.T; g += (uint64_t)gridDim.x * blockDim.x) {
        const uint32_t r = w.site_region[g], t = w.site_pos[g];
        if (!w.ok[r]) {
            s[2 * g] = 0;
            s[2 * g + 1] = 0;
            continue;
        }
        const uint64_t first = w.region_off[r];
        const uint32_t sites = w.region_off[r + 1] - (uint32_t)first;
        MomentGauss v;
        if (!moment_site_exact(before + 2 * first, after + 2 * first, up + 2 * (first + r), down + 2 * (first + r), w.ring, w.n, w.ring_len, w.decay, sites, t, &v)) {
            atomicOr(w.status, MOMENT_REFUSED_SHAPE);
        }
        s[2 * g] = fit64(rel(v.re, MOMENT_COEFFICIENT_BITS), w.status);
        s[2 * g + 1] = fit64(rel(v.im, MOMENT_COEFFICIENT_BITS), w.status);
    }
}

// The moments' return on `2^(−24)` (`T` pairs of `wide` each): `δE⁺` into `d_before`, `δE⁻` into
// `d_after`, the unreleased return on `2^(−84)` released once, `rel(Δ, 60)`. One thread a site; stored,
// not added. A refused region's return is zero.
extern "C" __global__ void field_moment_return(MomentWords w, const int64_t *ds, const wide *q, wide *d_before, wide *d_after) {
    for (uint64_t g = (uint64_t)blockIdx.x * blockDim.x + threadIdx.x; g < w.T; g += (uint64_t)gridDim.x * blockDim.x) {
        const uint32_t r = w.site_region[g], k = w.site_pos[g];
        if (!w.ok[r]) {
            d_before[2 * g] = d_before[2 * g + 1] = d_after[2 * g] = d_after[2 * g + 1] = 0;
            continue;
        }
        const uint64_t first = w.region_off[r];
        const uint32_t sites = w.region_off[r + 1] - (uint32_t)first;
        MomentGauss plus, minus;
        if (!moment_return_site(ds + 2 * first, q + 2 * (first + r), w.ring, w.n, w.ring_len, w.decay, sites, k, &plus, &minus)) {
            atomicOr(w.status, MOMENT_REFUSED_SHAPE);
        }
        d_before[2 * g] = rel(plus.re, MOMENT_RETURN_RELEASE_BITS);
        d_before[2 * g + 1] = rel(plus.im, MOMENT_RETURN_RELEASE_BITS);
        d_after[2 * g] = rel(minus.re, MOMENT_RETURN_RELEASE_BITS);
        d_after[2 * g + 1] = rel(minus.im, MOMENT_RETURN_RELEASE_BITS);
    }
}

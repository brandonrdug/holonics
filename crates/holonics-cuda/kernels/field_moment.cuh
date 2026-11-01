// The field's site moment on the card (`holonics::hnn::tower::field::moment`, record
// `2026-11-01_THE_FIELD_DISPERSES_A_SITE_MEETS_ITS_RESONANCE_CLASS_AT_ITS_FALLOFF_AND_THE_ANSWER_LOCKS_UNDER_THE_PUMP`,
// §15.1): bit for bit the host's `moment_exact`, `moments`, `moment_return_exact` and `moments_return`.
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
// **The return** is the exact transpose of that integer map: multiplication by a Gaussian integer
// `W` has the real transpose multiplication by `conj(W)`, so with `δs` on `2^(−24)`
//
//   δE⁺_k = rel( Σ_(t ≥ k, t−k < NEAR) conj(ζ^(k−t)) D(t−k) δs_t 2^30
//              + conj(ζ^k) Σ_(right octaves (lo,hi,ℓ) of k) D(2^ℓ) Σ_(t=lo..hi) ζ^t δs_t , 90 )
//   δE⁻_k = rel( the same over t ≤ k and the left octaves of k , 90 )
//
// (`t` is in the right octave ℓ of `k` exactly when `k` is in the left octave ℓ of `t`; the single
// prefix sum `Q[j] = Σ_(u<j) ζ^u δs_u` on `2^(−54)` serves both). The unreleased return is on `2^(−114)`.
//
// **The carrier.** The l1 certificate `(S+1) · max(D̂,1) · R · max(R, 2^30) · Ê < 2^127` (`D̂` the
// largest decay over `d < S`, `R` the largest l1 of the resident ring, `Ê` the largest l1 of the
// input, `moment_certificate`) keeps every term and every partial sum of every order inside a signed
// 128-bit word. It is a property of the exact inputs alone, so the card refuses the same regions as
// the host (`field_moment_admit`): a refused region's outputs are zero and `REFUSED_CARRIER` is set.
// A region whose shape the law cannot read (`n = 0`, `ring_len < min(n, S)`, `dreach < S`) is refused
// with `MOMENT_REFUSED_SHAPE`.
//
// **The launch** (one ring slot a launch; the driver sets `ring`, `n`, `ring_len`, `decay`, `dreach`):
//   forward   admit(before, after) → prefix(before → up) → prefix(after → down) → moment
//   return    admit(ds, null)      → prefix(ds → q)                            → moment_return
// `field_moment_admit` and `field_moment_prefix` run one block a region (a power-of-two block of
// threads); `field_moment` and `field_moment_return` one thread a site. The prefix and extent
// kernels take `blockDim.x` threads and the dynamic shared memory stated on each; the `wide` arrays
// are 16-byte aligned. Integer sums: the scan's partition (chunks of a region, in any number) changes no bit.

#pragma once

#ifndef REFUSED_CARRIER
#error "field_moment.cuh is included after field.cu's integer prelude"
#endif
#ifndef MOMENT_REFUSED_SHAPE
#define MOMENT_REFUSED_SHAPE 16u
#endif

static_assert(MOVE_BITS == 30 && FACE_BITS == 16 && COVECTOR_BITS == 24, "the moment's grains are the host's");
// The coefficient's grain, three faces on `2^(−30)` (`COEFFICIENT_BITS`): a moment or a return is released this many bits.
#define MOMENT_COEFFICIENT_BITS (3 * MOVE_BITS)

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

// The transpose of a near term, `conj(ζ) D x 2^30` (a covector on `2^(−24)` gives `2^(−114)`).
__host__ __device__ __forceinline__ MomentGauss moment_near_back(MomentGauss z, wide decay, MomentGauss x) {
    return mg_scale(mg_scale(mg_mul_conj(z, x), decay), (wide)1 << MOVE_BITS);
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

// The unreleased return of the site at place `k` on `2^(−114)`: `plus = Δ⁺_k`, `minus = Δ⁻_k`, `ds` the
// region's covector (`sites` int64 pairs on `2^(−24)`), `q` its prefix sums `Σ_(u<j) ζ^u δs_u`.
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
    uint8_t *ok;                  // R: 1 where `field_moment_admit` admitted the region
    uint32_t *status;             // the batch's status word
};

__device__ __forceinline__ uwide moment_l1(int64_t re, int64_t im) {
    return (uwide)mag64(re) + (uwide)mag64(im);
}

__device__ __forceinline__ uwide moment_max(uwide a, uwide b) {
    return a > b ? a : b;
}

// A region's admission: the certificate on its inputs `x` (and `y` where not null: the two strands of
// the forward), and the shape the law reads. One block a region, `blockDim.x` a power of two; dynamic
// shared memory `3 · blockDim.x · sizeof(uwide)`. Writes `w.ok[r]`; a refusal sets `REFUSED_CARRIER`
// (the certificate) or `MOMENT_REFUSED_SHAPE` in `w.status`.
extern "C" __global__ void field_moment_admit(MomentWords w, const int64_t *x, const int64_t *y) {
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
            const bool admitted = shape && moment_certificate(sites, peak[2 * B], peak[B], peak[0]);
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

// The prefix sums `P[j] = Σ_(k<j) ζ^k x_k` of a strand `x` (`T` int64 pairs), region by region, into
// `pre` (`T + R` entries of two `wide`: region `r`'s `sites + 1` entries start at entry `first + r`).
// Each thread scans a chunk of the region; the chunks' totals are summed once and the offsets added:
// integer sums, so the partition changes no bit. One block a region; dynamic shared memory
// `blockDim.x · sizeof(MomentGauss)`. A refused region's entries are left unwritten (never read).
extern "C" __global__ void field_moment_prefix(MomentWords w, const int64_t *x, wide *pre) {
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
        totals[threadIdx.x] = moment_scan_chunk(w.ring, w.n, strand, lo, hi, out);
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
// `d_after`, the unreleased return released once, `rel(Δ, 90)`. One thread a site; stored, not added.
// A refused region's return is zero.
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
        d_before[2 * g] = rel(plus.re, MOMENT_COEFFICIENT_BITS);
        d_before[2 * g + 1] = rel(plus.im, MOMENT_COEFFICIENT_BITS);
        d_after[2 * g] = rel(minus.re, MOMENT_COEFFICIENT_BITS);
        d_after[2 * g + 1] = rel(minus.im, MOMENT_COEFFICIENT_BITS);
    }
}

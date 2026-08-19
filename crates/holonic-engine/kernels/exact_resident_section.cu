// **The resident section: a semantic standing that enters an operation on the card and leaves it
// on the card.**
//
// Owner: `crates/holonic-engine/src/resident_section.rs`. Contract:
// `research/records/2026-08-18_THE_SECTION_MUST_STAY_ON_THE_CARD_THE_CONTRACT_BEFORE_THE_RESIDENT_LAYER.md`.
//
// # The carrier, and why it is an interval
//
// A section coordinate is a certified enclosure `[lo, hi]` of two `int64_t` words at one declared
// dyadic grain `2^-F`. Nothing here is a float, nothing here rounds toward a value: every operation
// rounds its lower word DOWN and its upper word UP, so the remainder of every radical, series,
// quotient and product PROPAGATES through every successor to the terminal face rather than being
// stored beside a midpoint.
//
// # No signed value is ever left-shifted here — 2026-08-18
//
// The first form of this file wrote `v << s` on a signed `__int128`. The audit convicted it: that
// is undefined for a negative `v` in the C++ this kernel is compiled as, and compiler parity is not
// proof of defined behaviour. Every shift below is taken on the UNSIGNED MAGNITUDE, checked against
// the carrier before it happens, and the sign is restored under the directed floor/ceiling law:
//
//   floor(v · 2^s)  for v < 0, s < 0   =  −ceil(|v| / 2^k)  =  −((|v| + 2^k − 1) >> k)
//   ceil (v · 2^s)  for v < 0, s < 0   =  −floor(|v| / 2^k) =  −(|v| >> k)
//
// The magnitude of the signed minimum is taken as `(uwide)0 − (uwide)v`, which is exact where a
// signed negation would overflow; the width of a census is taken in the wide carrier so
// `hi − lo` cannot overflow the word. `section_arithmetic_control` exposes these helpers so a
// driver can run them against an independent exact reference on the serial chart.
//
// # The census is per occurrence, and refusals travel along the lineage — never through a shared word
//
// The apparatus hands every occurrence its own twelve-word slot in one resident census array:
//
//   [0]  refused flags        written by the semantic kernel (atomicOr)
//   [1]  reach census         the contact's greatest reach (atomicMax)
//   [2]  written marker       the census kernel writes 1 — proof the reduction/kernel ran
//   [3]  inverted             the census kernel's own reading of `lo > hi`
//   [4]  max octave           the widest word (atomicMax)
//   [5]  bound violated       the census kernel compares [4] against the a-priori bound it was given
//   [6..8] max width          the widest enclosure, as one aligned 64-bit word (atomicMax)
//   [8]  upstream flags       the union of the refusal flags of every refusing predecessor
//   [9]  upstream first       1 + the least refusing predecessor index in the declared lineage; 0 = none
//   [10] upstream count       how many declared predecessors had refused
//   [11] lineage inspected    how many predecessor slots this kernel read — proof the inspection ran
//   [12..14] width sum        the sum of every enclosure's width, as one aligned 64-bit word (atomicAdd):
//                             with [6..8] the collapsed population of a midpoint quotient after it
//   [14] nonzero widths       how many coordinates had width > 0
//   [15] reserved
//
// **There is no global word.** The first form of this file had every kernel read one shared
// refusal word at entry and every census write it. That was unlawful as represented: unrelated
// co-present branches shared mutable standing, so a branch-local refusal could contaminate a
// sibling, whether a sibling saw it depended on the device's scheduling, and a kernel already
// running could see the word change between two of its threads. Now every kernel reads ONLY the
// refusal words of its declared predecessors, `census[lineage[i] * SLOT_WORDS + SLOT_REFUSED]`
// for `i < lineage_count`, where the lineage array is the diagram's own bond structure uploaded
// before the capture opened. The graph's edges place every predecessor's census node before the
// successor's kernel, so every word read is final and every thread reads the same value. The join
// over several predecessors is the union of their flags, the least refusing index and the count —
// commutative and associative — so the reading is one reading under any legal schedule.
//
//   refused bit 1   a word left the signed carrier, or an accumulator would leave the wide one
//   refused bit 2   malformed material: a non-finite stored codeword, a non-positive denominator
//   refused bit 4   an enclosure inverted (`lo > hi`) after a lawful step — a soundness fault
//   refused bit 8   a declared predecessor refused, or its a-priori octave bound was refuted (upstream)
//   refused bit 16  the a-priori octave bound of THIS occurrence was refuted by its census
//
// # Reductions are named barriers, realized here
//
// The RMS quadratic capacity, the contact partition function and the contact hull are
// within-section global couplings. `H.0219`: a term that is not a flux is a barrier. They are
// realized as block reductions on the card and never as serial-chart loops between launches.

#include <stdint.h>

typedef __int128 wide;
typedef unsigned __int128 uwide;

#define REFUSED_CARRIER   1u
#define REFUSED_MALFORMED 2u
#define REFUSED_INVERTED  4u
#define REFUSED_UPSTREAM  8u
#define REFUSED_BOUND     16u

// The census slot layout, in 32-bit words.
#define SLOT_WORDS           16
#define SLOT_REFUSED         0
#define SLOT_REACH           1
#define SLOT_WRITTEN         2
#define SLOT_INVERTED        3
#define SLOT_OCTAVE          4
#define SLOT_BOUND           5
#define SLOT_WIDTH           6
#define SLOT_UPSTREAM_FLAGS  8
#define SLOT_UPSTREAM_FIRST  9
#define SLOT_UPSTREAM_COUNT  10
#define SLOT_LINEAGE         11
#define SLOT_WIDTH_SUM       12
#define SLOT_NONZERO_WIDTHS  14

// ---------------------------------------------------------------------------------------------
// exact helpers over the wide carrier — magnitude first, sign restored under the directed law
// ---------------------------------------------------------------------------------------------

// |v| as an unsigned magnitude. Exact for the signed minimum: `(uwide)0 - (uwide)v` is 2^127.
__device__ __forceinline__ uwide magnitude(wide v) { return v < 0 ? (uwide)0 - (uwide)v : (uwide)v; }

// The octaves a magnitude occupies: the position of its highest set bit plus one.
__device__ __forceinline__ uint32_t octaves_of(uwide m) {
    uint64_t hi = (uint64_t)(m >> 64), lo = (uint64_t)m;
    if (hi != 0) return 128u - (uint32_t)__clzll((long long)hi);
    if (lo != 0) return 64u - (uint32_t)__clzll((long long)lo);
    return 0u;
}

// A magnitude that fits the positive half of the wide carrier, or the carrier refusal.
__device__ __forceinline__ wide of_magnitude(uwide m, int negative, uint32_t *refused) {
    if (m > (((uwide)1 << 127) - 1)) { atomicOr(refused, REFUSED_CARRIER); return 0; }
    wide v = (wide)m;
    return negative ? -v : v;
}

// `v · 2^s` rounded toward −∞.
__device__ __forceinline__ wide shift_floor(wide v, int s, uint32_t *refused) {
    int negative = v < 0;
    uwide m = magnitude(v);
    if (s >= 0) {
        // m · 2^s must stay below 2^127: the bits above position 126 − s must be clear.
        if (s >= 127 || (m >> (127 - s)) != 0) { atomicOr(refused, REFUSED_CARRIER); return 0; }
        return of_magnitude(m << s, negative, refused);
    }
    int k = -s;
    if (k >= 128) return negative ? -1 : 0;
    if (!negative) return (wide)(m >> k);
    // floor of a negative: −ceil(m / 2^k). m ≤ 2^127 and k ≥ 1, so the sum cannot wrap.
    uwide up = (m + (((uwide)1 << k) - 1)) >> k;
    return of_magnitude(up, 1, refused);
}

// `v · 2^s` rounded toward +∞.
__device__ __forceinline__ wide shift_ceil(wide v, int s, uint32_t *refused) {
    int negative = v < 0;
    uwide m = magnitude(v);
    if (s >= 0) {
        if (s >= 127 || (m >> (127 - s)) != 0) { atomicOr(refused, REFUSED_CARRIER); return 0; }
        return of_magnitude(m << s, negative, refused);
    }
    int k = -s;
    if (k >= 128) return (v > 0) ? 1 : 0;
    if (negative) return of_magnitude(m >> k, 1, refused);
    uwide up = (m + (((uwide)1 << k) - 1)) >> k;
    return of_magnitude(up, 0, refused);
}

// Floor and ceiling of an exact quotient of wide integers, `d > 0` required; `d ≤ 0` refuses.
__device__ __forceinline__ wide div_floor(wide n, wide d, uint32_t *refused) {
    if (d <= 0) { atomicOr(refused, REFUSED_MALFORMED); return 0; }
    wide q = n / d;
    if ((n % d != 0) && (n < 0)) q -= 1;
    return q;
}
__device__ __forceinline__ wide div_ceil(wide n, wide d, uint32_t *refused) {
    if (d <= 0) { atomicOr(refused, REFUSED_MALFORMED); return 0; }
    wide q = n / d;
    if ((n % d != 0) && (n > 0)) q += 1;
    return q;
}

// A wide value into the signed word, or the carrier refusal.
__device__ __forceinline__ int64_t to_word(wide v, uint32_t *refused) {
    if (v > (wide)INT64_MAX || v < (wide)INT64_MIN) { atomicOr(refused, REFUSED_CARRIER); return 0; }
    return (int64_t)v;
}

// An exact product of two wide values, refusing one that would leave the wide carrier.
__device__ __forceinline__ wide product_checked(wide a, wide b, uint32_t *refused) {
    uwide ma = magnitude(a), mb = magnitude(b);
    if (ma == 0 || mb == 0) return 0;
    if (octaves_of(ma) + octaves_of(mb) > 127) { atomicOr(refused, REFUSED_CARRIER); return 0; }
    uwide m = ma * mb;
    return of_magnitude(m, (a < 0) != (b < 0), refused);
}

// `v · m · 2^e` rounded toward −∞ / +∞ for a dyadic scalar `m · 2^e`, SELF-SCALING: when the
// exact product would leave the wide carrier, `v` is first shifted down (directed) by the least
// `s` that lets it fit and the result shifted back by `e + s`. The enclosure widens by at most one
// unit of the coarser grain and the arithmetic is sound for any word; nothing is chosen.
__device__ __forceinline__ void dyadic_scale(wide v, int64_t m, int32_t e, wide *out_lo, wide *out_hi, uint32_t *refused) {
    uint32_t ov = octaves_of(magnitude(v)), om = octaves_of(magnitude((wide)m));
    int s = 0;
    if (ov + om + 1 > 126) s = (int)(ov + om + 1 - 126);
    wide v_lo = shift_floor(v, -s, refused), v_hi = shift_ceil(v, -s, refused);
    if (m >= 0) {
        *out_lo = shift_floor(product_checked(v_lo, (wide)m, refused), e + s, refused);
        *out_hi = shift_ceil(product_checked(v_hi, (wide)m, refused), e + s, refused);
    } else {
        *out_lo = shift_floor(product_checked(v_hi, (wide)m, refused), e + s, refused);
        *out_hi = shift_ceil(product_checked(v_lo, (wide)m, refused), e + s, refused);
    }
}

// Floor of the square root of a non-negative wide integer, by integer Newton from an octave
// overestimate. Every iterate after the first is ≥ the floor and the sequence decreases to it.
__device__ wide isqrt_floor(wide a) {
    if (a <= 0) return 0;
    uint32_t bits = octaves_of((uwide)a);
    wide x = (wide)1 << ((bits + 1) / 2);
    while (true) {
        wide y = (x + a / x) >> 1;   // both non-negative: the shift is a floor division
        if (y >= x) break;
        x = y;
    }
    while (x * x > a) x -= 1;
    while ((x + 1) * (x + 1) <= a) x += 1;
    return x;
}
__device__ __forceinline__ wide isqrt_ceil(wide a) {
    wide f = isqrt_floor(a);
    return (f * f == a) ? f : f + 1;
}

// A product of two wide magnitudes as two `unsigned __int128` halves, exactly.
__device__ __forceinline__ void mul_magnitude_256(uwide a, uwide b, uwide *hi, uwide *lo) {
    uint64_t a0 = (uint64_t)a, a1 = (uint64_t)(a >> 64), b0 = (uint64_t)b, b1 = (uint64_t)(b >> 64);
    uwide p00 = (uwide)a0 * b0, p01 = (uwide)a0 * b1, p10 = (uwide)a1 * b0, p11 = (uwide)a1 * b1;
    uwide mid = (p00 >> 64) + (uwide)(uint64_t)p01 + (uwide)(uint64_t)p10;
    *lo = (p00 & (((uwide)1 << 64) - 1)) | (mid << 64);
    *hi = p11 + (p01 >> 64) + (p10 >> 64) + (mid >> 64);
}

// `a · b · 2^-k` rounded toward −∞ (floor) or +∞ (ceil), through the 256-bit product, refusing a
// result that would not fit the wide carrier. `k` in `[0, 255]`.
__device__ wide product_shift(wide a, wide b, int k, int toward_ceiling, uint32_t *refused) {
    int negative = (a < 0) != (b < 0);
    uwide ma = magnitude(a), mb = magnitude(b);
    uwide hi, lo;
    mul_magnitude_256(ma, mb, &hi, &lo);
    uwide q_hi, q_lo; int discarded;
    if (k == 0) { q_hi = hi; q_lo = lo; discarded = 0; }
    else if (k < 128) {
        discarded = (lo & (((uwide)1 << k) - 1)) != 0;
        q_lo = (lo >> k) | (hi << (128 - k));
        q_hi = hi >> k;
    } else {
        int j = k - 128;
        discarded = (lo != 0) || (j > 0 && (hi & (((uwide)1 << j) - 1)) != 0);
        q_lo = j == 0 ? hi : (hi >> j);
        q_hi = 0;
    }
    if (q_hi != 0 || q_lo > ((uwide)1 << 126)) { atomicOr(refused, REFUSED_CARRIER); return 0; }
    wide q = (wide)q_lo;
    // floor of a negative magnitude-truncated quotient is -(q + discarded); ceil of a positive one
    // is q + discarded.
    if (negative) return toward_ceiling ? -q : -(q + (discarded ? 1 : 0));
    return toward_ceiling ? q + (discarded ? 1 : 0) : q;
}

// Interval product of `[a,b]` and `[c,d]`, both at one grain, returned at the doubled grain as the
// exact minimum and maximum of the four corners, each product checked against the carrier.
__device__ __forceinline__ void corners(wide a, wide b, wide c, wide d, wide *lo, wide *hi, uint32_t *refused) {
    wide p1 = product_checked(a, c, refused), p2 = product_checked(a, d, refused);
    wide p3 = product_checked(b, c, refused), p4 = product_checked(b, d, refused);
    wide l = p1, h = p1;
    if (p2 < l) l = p2; if (p2 > h) h = p2;
    if (p3 < l) l = p3; if (p3 > h) h = p3;
    if (p4 < l) l = p4; if (p4 > h) h = p4;
    *lo = l; *hi = h;
}

// The enclosure of `N / D` for `N ∈ [n_lo, n_hi]` and `D ∈ [d_lo, d_hi]` with `d_lo > 0`, `N` first
// lifted by `2^lift`, floor below and ceiling above, CORRECT FOR NEGATIVE NUMERATORS:
//   lo = N_lo / (N_lo < 0 ? D_lo : D_hi)   floor      hi = N_hi / (N_hi < 0 ? D_hi : D_lo)   ceil
__device__ __forceinline__ void interval_quotient(
    wide n_lo, wide n_hi, wide d_lo, wide d_hi, int lift, wide *q_lo, wide *q_hi, uint32_t *refused
) {
    if (d_lo <= 0 || d_hi < d_lo) { atomicOr(refused, REFUSED_MALFORMED); *q_lo = 0; *q_hi = 0; return; }
    wide nl = shift_floor(n_lo, lift, refused), nh = shift_ceil(n_hi, lift, refused);
    *q_lo = div_floor(nl, nl < 0 ? d_lo : d_hi, refused);
    *q_hi = div_ceil(nh, nh < 0 ? d_hi : d_lo, refused);
}

// Every kernel's first act: inspect the refusal word of every DECLARED predecessor, and only
// those. The graph's edges put every predecessor's census before this kernel, so every word read
// here is final and every thread reads the same value. The join over the lineage is the union of
// the predecessors' flags, the least refusing predecessor (the lineage is declared in ascending
// index order) and how many refused — commutative and associative, one reading under any legal
// schedule. A refusing lineage makes this occurrence refuse UPSTREAM and write nothing plausible.
// Returns 1 when the kernel must stop. `slot` is this occurrence's own slot base.
__device__ __forceinline__ int upstream_refused(const uint32_t *census, const uint32_t *lineage, uint32_t lineage_count, uint32_t *slot) {
    uint32_t joined = 0u, first = 0u, refusing = 0u;
    for (uint32_t i = 0; i < lineage_count; ++i) {
        uint32_t flags = census[lineage[i] * SLOT_WORDS + SLOT_REFUSED];
        if (flags != 0u) {
            joined |= flags;
            if (refusing == 0u) first = lineage[i] + 1u;
            refusing += 1u;
        }
    }
    // Every thread computes the same values from the same final words; the stores are identical.
    slot[SLOT_LINEAGE] = lineage_count;
    if (joined == 0u) return 0;
    atomicOr(slot + SLOT_REFUSED, REFUSED_UPSTREAM);
    atomicOr(slot + SLOT_UPSTREAM_FLAGS, joined);
    slot[SLOT_UPSTREAM_FIRST] = first;
    slot[SLOT_UPSTREAM_COUNT] = refusing;
    return 1;
}

// ---------------------------------------------------------------------------------------------
// the BF16 mouth into a section: exact decode, exact dyadic scale, directed placement at the grain
// ---------------------------------------------------------------------------------------------

#define BFLOAT16_STORED_BITS 7
#define BFLOAT16_BIAS 127
#define BFLOAT16_HIDDEN (1u << BFLOAT16_STORED_BITS)
#define BFLOAT16_SUBNORMAL_ULP (1 - BFLOAT16_BIAS - BFLOAT16_STORED_BITS)

__device__ __forceinline__ int decode_bfloat16(uint16_t word, int64_t *significand, int *ulp) {
    int exponent = (int)((word >> BFLOAT16_STORED_BITS) & 0xffu);
    uint16_t mantissa = word & (uint16_t)(BFLOAT16_HIDDEN - 1u);
    if (exponent == 0xff) return 0;
    int64_t mag;
    if (exponent == 0) { mag = (int64_t)mantissa; *ulp = BFLOAT16_SUBNORMAL_ULP; }
    else { mag = (int64_t)(mantissa | (uint16_t)BFLOAT16_HIDDEN); *ulp = exponent - BFLOAT16_BIAS - BFLOAT16_STORED_BITS; }
    *significand = (word & 0x8000u) ? -mag : mag;
    return 1;
}

// `section[i] = words[i] · scale`, with `scale = scale_m · 2^scale_e` an exact dyadic, placed at
// the grain `2^-F`. Exact when the product's own exponent is not finer than the grain; otherwise
// the enclosure is one grain wide.
extern "C" __global__ void section_from_bfloat16(
    const uint16_t *words, uint32_t count, int64_t scale_m, int32_t scale_e, int32_t grain,
    int64_t *lo, int64_t *hi, uint32_t *refused, const uint32_t *census, const uint32_t *lineage, uint32_t lineage_count
) {
    uint32_t at = blockIdx.x * blockDim.x + threadIdx.x;
    if (at >= count) return;
    if (upstream_refused(census, lineage, lineage_count, refused)) return;
    int64_t significand; int ulp;
    if (!decode_bfloat16(words[at], &significand, &ulp)) { atomicOr(refused, REFUSED_MALFORMED); lo[at] = 0; hi[at] = 0; return; }
    wide product = (wide)significand * (wide)scale_m;   // 8 octaves × the scale's, inside the carrier
    int shift = grain + ulp + scale_e;
    lo[at] = to_word(shift_floor(product, shift, refused), refused);
    hi[at] = to_word(shift_ceil(product, shift, refused), refused);
}

// ---------------------------------------------------------------------------------------------
// the contraction: section × stored map, `__int128` accumulation, directed placement
// ---------------------------------------------------------------------------------------------

// `out[t, o] = Σ_i map[o, i] · section[t, i]`. The map is the resident aligned form of a stored BF16
// population — integers on one exponent `map_e`. The caller admitted the octave budget from the
// a-priori bound before launching; the bound itself is enforced by the predecessor's census.
extern "C" __global__ void section_contract(
    const int64_t *lo, const int64_t *hi, uint32_t rows, uint32_t inner,
    const int64_t *map, int32_t map_e, uint32_t out_width, int32_t grain,
    int64_t *out_lo, int64_t *out_hi, uint32_t *refused, const uint32_t *census, const uint32_t *lineage, uint32_t lineage_count
) {
    uint32_t flat = blockIdx.x * blockDim.x + threadIdx.x;
    if (flat >= rows * out_width) return;
    if (upstream_refused(census, lineage, lineage_count, refused)) return;
    uint32_t t = flat / out_width, o = flat % out_width;
    const int64_t *entries = map + (size_t)o * (size_t)inner;
    const int64_t *slo = lo + (size_t)t * (size_t)inner;
    const int64_t *shi = hi + (size_t)t * (size_t)inner;
    wide acc_lo = 0, acc_hi = 0;
    for (uint32_t i = 0; i < inner; ++i) {
        wide w = entries[i];
        if (w >= 0) { acc_lo += w * (wide)slo[i]; acc_hi += w * (wide)shi[i]; }
        else        { acc_lo += w * (wide)shi[i]; acc_hi += w * (wide)slo[i]; }
    }
    // The product sits at 2^(map_e − F); the grain wants 2^-F, so the shift is by map_e.
    out_lo[flat] = to_word(shift_floor(acc_lo, map_e, refused), refused);
    out_hi[flat] = to_word(shift_ceil(acc_hi, map_e, refused), refused);
    (void)grain;
}

// ---------------------------------------------------------------------------------------------
// the RMS rebase: a named barrier — the quadratic capacity — realized as a resident reduction
// ---------------------------------------------------------------------------------------------

// One block per `(row, group)`. The block first reads its group's own widest octave — a
// reduction — and derives the square grain and the root grain FROM THE MATERIAL, so the enclosure
// is as tight as the group admits and no host-supplied level enters; then the squares are reduced,
// thread 0 isolates the reciprocal square root of `mean + eps` by integer Newton with floor and
// ceiling, and every thread rebases its coordinates by that enclosure and the stored gain.
//
//   x_i · (mean(x²) + eps)^{-1/2} · g_i         with eps = eps_m · 2^eps_e exact
//
// `gain == NULL` is the source's `with_scale=False` — the value norm — and is not a default.
extern "C" __global__ void section_rms_rebase(
    const int64_t *lo, const int64_t *hi, uint32_t rows, uint32_t width, uint32_t group,
    const int64_t *gain, int32_t gain_e, int64_t eps_m, int32_t eps_e, int32_t grain,
    int64_t *out_lo, int64_t *out_hi, uint32_t *refused, const uint32_t *census, const uint32_t *lineage, uint32_t lineage_count
) {
    extern __shared__ unsigned char shared_raw[];
    wide *sum_lo = (wide *)shared_raw;
    wide *sum_hi = sum_lo + blockDim.x;
    uint32_t *oct = (uint32_t *)(sum_hi + blockDim.x);
    __shared__ wide r_lo, r_hi;
    __shared__ int32_t square_shift_s, rg_s;

    uint32_t groups_per_row = width / group;
    uint32_t row = blockIdx.x / groups_per_row;
    uint32_t which = blockIdx.x % groups_per_row;
    if (row >= rows) return;
    if (threadIdx.x == 0 && upstream_refused(census, lineage, lineage_count, refused)) { square_shift_s = -1; }
    else if (threadIdx.x == 0) { square_shift_s = 0; }
    __syncthreads();
    if (square_shift_s < 0) return;
    size_t base = (size_t)row * (size_t)width + (size_t)which * (size_t)group;

    // (a) the group's own widest octave.
    uint32_t widest = 0;
    for (uint32_t i = threadIdx.x; i < group; i += blockDim.x) {
        uwide ma = magnitude((wide)lo[base + i]), mb = magnitude((wide)hi[base + i]);
        uint32_t o = octaves_of(ma > mb ? ma : mb);
        if (o > widest) widest = o;
    }
    oct[threadIdx.x] = widest;
    __syncthreads();
    for (uint32_t stride = blockDim.x / 2; stride > 0; stride >>= 1) {
        if (threadIdx.x < stride && oct[threadIdx.x + stride] > oct[threadIdx.x]) oct[threadIdx.x] = oct[threadIdx.x + stride];
        __syncthreads();
    }
    if (threadIdx.x == 0) {
        // The squares are summed at 2^-2(F − s) with s the least shift that fits the wide carrier:
        // 2(oct − s) + log2(group) + 1 ≤ 126. Derived from the material's own census, never chosen.
        uint32_t o = oct[0];
        uint32_t lg = 0; while ((1u << lg) < group) ++lg;
        uint32_t squares = 2 * o + lg + 1;
        int32_t s = squares > 126u ? (int32_t)((squares - 126u + 1u) / 2u) : 0;
        if (s >= grain) { atomicOr(refused, REFUSED_CARRIER); s = -1; }
        square_shift_s = s;
        int32_t f_prime = grain - (s < 0 ? 0 : s);
        int32_t rg = 126 - f_prime; if (rg > 60) rg = 60; if (rg < 0) rg = 0;
        rg_s = rg;
    }
    __syncthreads();
    int32_t square_shift = square_shift_s;
    if (square_shift < 0) return;
    int32_t rg = rg_s;
    int f_prime = grain - square_shift;

    // (b) the squares of the magnitude bounds, at the shifted grain.
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
        // r · 2^Rg = 2^{f' + Rg} / sqrt(a): the reciprocal root at ITS OWN grain, finer than the
        // section's, so that a small radius is not a handful of grains.
        wide scale = (wide)1 << (f_prime + rg);
        r_lo = div_floor(scale, isqrt_ceil(a_hi), refused);
        r_hi = div_ceil(scale, isqrt_floor(a_lo), refused);
    }
    __syncthreads();
    wide rl = r_lo, rh = r_hi;   // r ≥ 0
    for (uint32_t i = threadIdx.x; i < group; i += blockDim.x) {
        wide a = lo[base + i], b = hi[base + i];
        // x·g first, exactly, at 2^-(F − gain_e); then times the root through the 256-bit product,
        // rounded ONCE back to 2^-F: shift by rg − gain_e.
        wide xg_lo = a, xg_hi = b;
        int shift = rg;
        if (gain != NULL) {
            wide g = gain[i];
            if (g >= 0) { xg_lo = product_checked(a, g, refused); xg_hi = product_checked(b, g, refused); }
            else { xg_lo = product_checked(b, g, refused); xg_hi = product_checked(a, g, refused); }
            shift = rg - gain_e;
        }
        wide y_lo, y_hi;
        if (xg_lo >= 0) { y_lo = product_shift(xg_lo, rl, shift, 0, refused); y_hi = product_shift(xg_hi, rh, shift, 1, refused); }
        else if (xg_hi <= 0) { y_lo = product_shift(xg_lo, rh, shift, 0, refused); y_hi = product_shift(xg_hi, rl, shift, 1, refused); }
        else { y_lo = product_shift(xg_lo, rh, shift, 0, refused); y_hi = product_shift(xg_hi, rh, shift, 1, refused); }
        if (y_lo > y_hi) atomicOr(refused, REFUSED_INVERTED);
        out_lo[base + i] = to_word(y_lo, refused);
        out_hi[base + i] = to_word(y_hi, refused);
    }
}

// ---------------------------------------------------------------------------------------------
// the chronology: the site's band group elements, raised to the integer position on the card
// ---------------------------------------------------------------------------------------------

// Compose two enclosed rotations `(c1,s1)·(c2,s2)`, both at grain `2^-Fr`, result at `2^-Fr`.
__device__ __forceinline__ void rotate_compose(
    wide c1l, wide c1h, wide s1l, wide s1h, wide c2l, wide c2h, wide s2l, wide s2h, int fr,
    wide *cl, wide *ch, wide *sl, wide *sh, uint32_t *refused
) {
    wide cc_l, cc_h, ss_l, ss_h, sc_l, sc_h, cs_l, cs_h;
    corners(c1l, c1h, c2l, c2h, &cc_l, &cc_h, refused);
    corners(s1l, s1h, s2l, s2h, &ss_l, &ss_h, refused);
    corners(s1l, s1h, c2l, c2h, &sc_l, &sc_h, refused);
    corners(c1l, c1h, s2l, s2h, &cs_l, &cs_h, refused);
    *cl = shift_floor(cc_l - ss_h, -fr, refused);
    *ch = shift_ceil(cc_h - ss_l, -fr, refused);
    *sl = shift_floor(sc_l + cs_l, -fr, refused);
    *sh = shift_ceil(sc_h + cs_h, -fr, refused);
}

// One thread per `(row, head, band)`. `R_b^p` by binary powering of the band's enclosed element,
// then the pair `(x[b], x[b + D/2])` is turned — the source's `rotate_half` pairing.
extern "C" __global__ void section_chronology(
    const int64_t *lo, const int64_t *hi, uint32_t rows, uint32_t heads, uint32_t head_width,
    const int64_t *cos_lo, const int64_t *cos_hi, const int64_t *sin_lo, const int64_t *sin_hi,
    int32_t rotation_grain, const uint32_t *positions, int32_t grain,
    int64_t *out_lo, int64_t *out_hi, uint32_t *refused, const uint32_t *census, const uint32_t *lineage, uint32_t lineage_count
) {
    uint32_t bands = head_width / 2;
    uint32_t flat = blockIdx.x * blockDim.x + threadIdx.x;
    if (flat >= rows * heads * bands) return;
    if (upstream_refused(census, lineage, lineage_count, refused)) return;
    uint32_t band = flat % bands;
    uint32_t head = (flat / bands) % heads;
    uint32_t row = flat / (bands * heads);
    uint32_t p = positions[row];

    wide cl = (wide)1 << rotation_grain, ch = cl, sl = 0, sh = 0;
    wide bl = cos_lo[band], bh = cos_hi[band], tl = sin_lo[band], th = sin_hi[band];
    uint32_t e = p;
    while (e > 0) {
        if (e & 1u) {
            wide ncl, nch, nsl, nsh;
            rotate_compose(cl, ch, sl, sh, bl, bh, tl, th, rotation_grain, &ncl, &nch, &nsl, &nsh, refused);
            cl = ncl; ch = nch; sl = nsl; sh = nsh;
        }
        e >>= 1;
        if (e > 0) {
            wide nbl, nbh, ntl, nth;
            rotate_compose(bl, bh, tl, th, bl, bh, tl, th, rotation_grain, &nbl, &nbh, &ntl, &nth, refused);
            bl = nbl; bh = nbh; tl = ntl; th = nth;
        }
    }

    size_t base = (size_t)row * (size_t)heads * (size_t)head_width + (size_t)head * (size_t)head_width;
    size_t first = base + band, second = base + band + bands;
    wide x_lo = lo[first], x_hi = hi[first], y_lo = lo[second], y_hi = hi[second];
    wide xc_l, xc_h, ys_l, ys_h, xs_l, xs_h, yc_l, yc_h;
    corners(x_lo, x_hi, cl, ch, &xc_l, &xc_h, refused);
    corners(y_lo, y_hi, sl, sh, &ys_l, &ys_h, refused);
    corners(x_lo, x_hi, sl, sh, &xs_l, &xs_h, refused);
    corners(y_lo, y_hi, cl, ch, &yc_l, &yc_h, refused);
    wide o1_lo = shift_floor(xc_l - ys_h, -rotation_grain, refused);
    wide o1_hi = shift_ceil(xc_h - ys_l, -rotation_grain, refused);
    wide o2_lo = shift_floor(xs_l + yc_l, -rotation_grain, refused);
    wide o2_hi = shift_ceil(xs_h + yc_h, -rotation_grain, refused);
    out_lo[first] = to_word(o1_lo, refused);  out_hi[first] = to_word(o1_hi, refused);
    out_lo[second] = to_word(o2_lo, refused); out_hi[second] = to_word(o2_hi, refused);
    (void)grain;
}

// ---------------------------------------------------------------------------------------------
// the certified exponential: series with an alternating tail, then squarings, all directed
// ---------------------------------------------------------------------------------------------

#define SERIES_GRAIN 60

// `exp(x)` for `x ≤ 0` given at grain `2^-F` as a wide integer, returning `[lo, hi]` at `2^-F`.
__device__ void exp_nonpositive(wide x, int grain, uint32_t terms, wide *out_lo, wide *out_hi, uint32_t *refused) {
    if (x > 0) { atomicOr(refused, REFUSED_MALFORMED); *out_lo = 0; *out_hi = 0; return; }
    wide unit = (wide)1 << grain;
    if (x <= -((wide)grain) * unit) { *out_lo = 0; *out_hi = 1; return; }
    if (x == 0) { *out_lo = unit; *out_hi = unit; return; }
    uint32_t bits = octaves_of(magnitude(x));
    int k = 0;
    if (bits + 4 > (uint32_t)grain) k = (int)(bits + 4 - (uint32_t)grain);
    int lift = SERIES_GRAIN - grain - k;
    wide y_lo = shift_floor(x, lift, refused);
    wide y_hi = shift_ceil(x, lift, refused);
    wide one = (wide)1 << SERIES_GRAIN;
    wide mag_lo = one, mag_hi = one;
    wide ylo_mag = -y_hi, yhi_mag = -y_lo;   // |y| ∈ [ylo_mag, yhi_mag], both ≥ 0 and small
    wide s_lo = one, s_hi = one;
    wide s_lo_prev = one, s_hi_prev = one;
    for (uint32_t n = 1; n <= terms + 1; ++n) {
        s_lo_prev = s_lo; s_hi_prev = s_hi;
        wide p_lo = mag_lo * ylo_mag, p_hi = mag_hi * yhi_mag;   // ≤ 2^60 · 2^56
        mag_lo = div_floor(shift_floor(p_lo, -SERIES_GRAIN, refused), (wide)n, refused);
        mag_hi = div_ceil(shift_ceil(p_hi, -SERIES_GRAIN, refused), (wide)n, refused);
        if (n & 1u) { s_lo -= mag_hi; s_hi -= mag_lo; }
        else        { s_lo += mag_lo; s_hi += mag_hi; }
    }
    wide e_lo = s_lo < s_lo_prev ? s_lo : s_lo_prev;
    wide e_hi = s_hi > s_hi_prev ? s_hi : s_hi_prev;
    if (e_lo < 0) e_lo = 0;
    if (e_hi > one) e_hi = one;
    for (int i = 0; i < k; ++i) {
        e_lo = shift_floor(e_lo * e_lo, -SERIES_GRAIN, refused);
        e_hi = shift_ceil(e_hi * e_hi, -SERIES_GRAIN, refused);
        if (e_hi > one) e_hi = one;
    }
    *out_lo = shift_floor(e_lo, grain - SERIES_GRAIN, refused);
    *out_hi = shift_ceil(e_hi, grain - SERIES_GRAIN, refused);
}

// ---------------------------------------------------------------------------------------------
// the contact: the bracket, the declared null, the certified ratio family, the carried construction
// ---------------------------------------------------------------------------------------------

// One block per `(row, receiver head)`. K/V family `g = h / (H / KH)` serves head `h`, which is the
// source's `repeat_kv`. Shared memory: `reach` slots each of `s_lo, s_hi, w_lo, w_hi` (wide).
extern "C" __global__ void section_contact(
    const int64_t *q_lo, const int64_t *q_hi, const int64_t *k_lo, const int64_t *k_hi,
    const int64_t *v_lo, const int64_t *v_hi,
    uint32_t rows, uint32_t heads, uint32_t kv_heads, uint32_t head_width, uint32_t window,
    int32_t grain, uint32_t terms,
    int64_t *out_lo, int64_t *out_hi, uint32_t *refused, uint32_t *reach_census, const uint32_t *census, const uint32_t *lineage, uint32_t lineage_count
) {
    extern __shared__ unsigned char shared_raw[];
    uint32_t t = blockIdx.x / heads;
    uint32_t h = blockIdx.x % heads;
    if (t >= rows) return;
    __shared__ int stopped;
    if (threadIdx.x == 0) stopped = upstream_refused(census, lineage, lineage_count, refused);
    __syncthreads();
    if (stopped) return;
    uint32_t group = heads / kv_heads;
    uint32_t g = h / group;
    uint32_t start = (t + 1 > window) ? (t + 1 - window) : 0;
    uint32_t reach = t - start + 1;
    wide *s_lo = (wide *)shared_raw;
    wide *s_hi = s_lo + reach;
    wide *w_lo = s_hi + reach;
    wide *w_hi = w_lo + reach;
    __shared__ wide null_value, total_lo, total_hi;

    size_t q_base = ((size_t)t * heads + h) * head_width;
    // (a0) the block's own widest octave over its receiver row and its presented reach — a
    // reduction — so the bracket sum's grain is derived FROM THE MATERIAL: `q` and `k` are shifted
    // down (directed) by the least `s` with `2(oct − s) + log2(D) + 2 ≤ 126`. For the layer's
    // real words `s` is zero; the arithmetic is sound for any word.
    __shared__ uint32_t oct_s[1024];
    __shared__ int bracket_shift;
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
    // (a) the brackets, at grain 2^-2(F − bs), then back to 2^-F
    for (uint32_t r = threadIdx.x; r < reach; r += blockDim.x) {
        uint32_t j = start + r;
        size_t k_base = ((size_t)j * kv_heads + g) * head_width;
        wide acc_lo = 0, acc_hi = 0;
        for (uint32_t d = 0; d < head_width; ++d) {
            wide ql = shift_floor(q_lo[q_base + d], -bs, refused), qh = shift_ceil(q_hi[q_base + d], -bs, refused);
            wide kl = shift_floor(k_lo[k_base + d], -bs, refused), kh = shift_ceil(k_hi[k_base + d], -bs, refused);
            wide l, u;
            corners(ql, qh, kl, kh, &l, &u, refused);
            acc_lo += l; acc_hi += u;
        }
        s_lo[r] = shift_floor(acc_lo, -(grain - 2 * bs), refused);
        s_hi[r] = shift_ceil(acc_hi, -(grain - 2 * bs), refused);
    }
    __syncthreads();
    // (b) the null: the greatest upper bracket, a gauge that enters no ratio.
    if (threadIdx.x == 0) {
        wide c = s_hi[0];
        for (uint32_t r = 1; r < reach; ++r) if (s_hi[r] > c) c = s_hi[r];
        null_value = c;
        atomicMax(reach_census, reach);
    }
    __syncthreads();
    // (c) the certified weights
    for (uint32_t r = threadIdx.x; r < reach; r += blockDim.x) {
        wide lo_arg = s_lo[r] - null_value, hi_arg = s_hi[r] - null_value;
        if (hi_arg > 0) hi_arg = 0;
        wide e_lo_lo, e_lo_hi, e_hi_lo, e_hi_hi;
        exp_nonpositive(lo_arg, grain, terms, &e_lo_lo, &e_lo_hi, refused);
        exp_nonpositive(hi_arg, grain, terms, &e_hi_lo, &e_hi_hi, refused);
        w_lo[r] = e_lo_lo;
        w_hi[r] = e_hi_hi;
    }
    __syncthreads();
    if (threadIdx.x == 0) {
        wide tl = 0, th = 0;
        for (uint32_t r = 0; r < reach; ++r) { tl += w_lo[r]; th += w_hi[r]; }
        total_lo = tl; total_hi = th;
        if (tl <= 0) atomicOr(refused, REFUSED_MALFORMED);
    }
    __syncthreads();
    // (d) the carried construction, one coordinate per thread
    wide tl = total_lo, th = total_hi;
    if (tl <= 0) return;
    for (uint32_t d = threadIdx.x; d < head_width; d += blockDim.x) {
        wide num_lo = 0, num_hi = 0;
        wide hull_lo = 0, hull_hi = 0;
        for (uint32_t r = 0; r < reach; ++r) {
            uint32_t j = start + r;
            size_t v_at = ((size_t)j * kv_heads + g) * head_width + d;
            wide vl = v_lo[v_at], vh = v_hi[v_at];
            wide pl, ph;
            corners(w_lo[r], w_hi[r], vl, vh, &pl, &ph, refused);
            num_lo += pl; num_hi += ph;
            if (r == 0) { hull_lo = vl; hull_hi = vh; }
            else { if (vl < hull_lo) hull_lo = vl; if (vh > hull_hi) hull_hi = vh; }
        }
        // num at 2^-2F over total at 2^-F gives the quotient at 2^-F: the interval quotient with
        // the sign-correct denominator choice, no lift.
        wide q_lo, q_hi;
        interval_quotient(num_lo, num_hi, tl, th, 0, &q_lo, &q_hi, refused);
        // The convex combination lies inside the hull; the enclosure may be tightened to it and
        // never widened past it. An empty intersection is a soundness fault and is reported.
        if (hull_lo > q_lo) q_lo = hull_lo;
        if (hull_hi < q_hi) q_hi = hull_hi;
        if (q_lo > q_hi) atomicOr(refused, REFUSED_INVERTED);
        out_lo[q_base + d] = to_word(q_lo, refused);
        out_hi[q_base + d] = to_word(q_hi, refused);
    }
}

// ---------------------------------------------------------------------------------------------
// the gated passage: the source's constitutive response through the same certified exponential
// ---------------------------------------------------------------------------------------------

__device__ __forceinline__ void tanh_nonnegative(wide u, int grain, uint32_t terms, wide *lo, wide *hi, uint32_t *refused) {
    wide unit = (wide)1 << grain;
    wide q_lo, q_hi;
    // Saturation: for u ≥ F (in value) exp(−2u) < 2^-F is below one grain, so q ∈ [0, 1] grains
    // and no series is needed — and −2u could not be formed for a huge u anyway.
    if (u >= ((wide)grain) * unit) { q_lo = 0; q_hi = 1; }
    else {
        wide arg = -2 * u;
        exp_nonpositive(arg, grain, terms, &q_lo, &q_hi, refused);
    }
    *lo = div_floor((unit - q_hi) * unit, unit + q_hi, refused);
    *hi = div_ceil((unit - q_lo) * unit, unit + q_lo, refused);
}

// `y = ½ x (1 + tanh(c1 (x + c2 x³)))`, the source's `gelu_pytorch_tanh`, with `c1` and `c2` the
// exact dyadic values of the `binary64` words its implementation computes with. Elementwise.
extern "C" __global__ void section_gelu_tanh(
    const int64_t *lo, const int64_t *hi, uint32_t count,
    int64_t c1_m, int32_t c1_e, int64_t c2_m, int32_t c2_e, int32_t grain, uint32_t terms,
    int64_t *out_lo, int64_t *out_hi, uint32_t *refused, const uint32_t *census, const uint32_t *lineage, uint32_t lineage_count
) {
    uint32_t at = blockIdx.x * blockDim.x + threadIdx.x;
    if (at >= count) return;
    if (upstream_refused(census, lineage, lineage_count, refused)) return;
    wide a = lo[at], b = hi[at];
    // x²: two words each below 2^63 multiply inside the wide carrier. Its bracket is taken by sign.
    wide sq_lo, sq_hi;
    { wide aa = product_checked(a, a, refused), bb = product_checked(b, b, refused);
      if (a <= 0 && b >= 0) { sq_lo = 0; sq_hi = aa > bb ? aa : bb; } else { sq_lo = aa < bb ? aa : bb; sq_hi = aa > bb ? aa : bb; } }
    sq_lo = shift_floor(sq_lo, -grain, refused); sq_hi = shift_ceil(sq_hi, -grain, refused);
    // x³ = x · x², SELF-SCALED: the square is shifted down by the least `s` that lets the product
    // fit, and shifted back after — for the layer's real words `s` is zero. Where `x` is large
    // enough for `s` to bite, the argument of tanh saturates and the lost low bits reach nothing.
    uint32_t oa = octaves_of(magnitude(a) > magnitude(b) ? magnitude(a) : magnitude(b));
    uint32_t osq = octaves_of(magnitude(sq_lo) > magnitude(sq_hi) ? magnitude(sq_lo) : magnitude(sq_hi));
    int s = (oa + osq + 1 > 126u) ? (int)(oa + osq + 1 - 126u) : 0;
    wide sqs_lo = shift_floor(sq_lo, -s, refused), sqs_hi = shift_ceil(sq_hi, -s, refused);
    wide cube_lo, cube_hi;
    corners(a, b, sqs_lo, sqs_hi, &cube_lo, &cube_hi, refused);
    cube_lo = shift_floor(cube_lo, -(grain - s), refused); cube_hi = shift_ceil(cube_hi, -(grain - s), refused);
    // c2 · x³ and c1 · (x + c2 x³): dyadic products, self-scaled the same way.
    // The product of an interval by a scalar is the hull of its endpoint products, whichever the
    // scalar's sign.
    wide tll, tlh, thl, thh;
    dyadic_scale(cube_lo, c2_m, c2_e, &tll, &tlh, refused);
    dyadic_scale(cube_hi, c2_m, c2_e, &thl, &thh, refused);
    wide t_lo = tll < thl ? tll : thl, t_hi = tlh > thh ? tlh : thh;
    wide in_lo = a + t_lo, in_hi = b + t_hi;
    wide ull, ulh, uhl, uhh;
    dyadic_scale(in_lo, c1_m, c1_e, &ull, &ulh, refused);
    dyadic_scale(in_hi, c1_m, c1_e, &uhl, &uhh, refused);
    wide u_lo = ull < uhl ? ull : uhl, u_hi = ulh > uhh ? ulh : uhh;
    wide th_lo, th_hi, d_lo, d_hi;
    if (u_lo >= 0) { tanh_nonnegative(u_lo, grain, terms, &th_lo, &d_hi, refused); }
    else { wide l, h; tanh_nonnegative(-u_lo, grain, terms, &l, &h, refused); th_lo = -h; }
    if (u_hi >= 0) { tanh_nonnegative(u_hi, grain, terms, &d_lo, &th_hi, refused); }
    else { wide l, h; tanh_nonnegative(-u_hi, grain, terms, &l, &h, refused); th_hi = -l; }
    (void)d_lo; (void)d_hi;
    wide unit = (wide)1 << grain;
    wide f_lo = unit + th_lo, f_hi = unit + th_hi;
    if (f_lo < 0) f_lo = 0;
    wide p_lo, p_hi;
    corners(a, b, f_lo, f_hi, &p_lo, &p_hi, refused);
    wide y_lo = shift_floor(p_lo, -grain - 1, refused);
    wide y_hi = shift_ceil(p_hi, -grain - 1, refused);
    if (y_lo > y_hi) atomicOr(refused, REFUSED_INVERTED);
    out_lo[at] = to_word(y_lo, refused);
    out_hi[at] = to_word(y_hi, refused);
}

// ---------------------------------------------------------------------------------------------
// elementwise transports: Hadamard, re-entry, an enclosed algebraic scale, a withdrawal, a control
// ---------------------------------------------------------------------------------------------

extern "C" __global__ void section_hadamard(
    const int64_t *a_lo, const int64_t *a_hi, const int64_t *b_lo, const int64_t *b_hi, uint32_t count,
    int32_t grain, int64_t *out_lo, int64_t *out_hi, uint32_t *refused, const uint32_t *census, const uint32_t *lineage, uint32_t lineage_count
) {
    uint32_t at = blockIdx.x * blockDim.x + threadIdx.x;
    if (at >= count) return;
    if (upstream_refused(census, lineage, lineage_count, refused)) return;
    wide l, h;
    corners(a_lo[at], a_hi[at], b_lo[at], b_hi[at], &l, &h, refused);
    out_lo[at] = to_word(shift_floor(l, -grain, refused), refused);
    out_hi[at] = to_word(shift_ceil(h, -grain, refused), refused);
}

extern "C" __global__ void section_re_entry(
    const int64_t *a_lo, const int64_t *a_hi, const int64_t *b_lo, const int64_t *b_hi, uint32_t count,
    int64_t *out_lo, int64_t *out_hi, uint32_t *refused, const uint32_t *census, const uint32_t *lineage, uint32_t lineage_count
) {
    uint32_t at = blockIdx.x * blockDim.x + threadIdx.x;
    if (at >= count) return;
    if (upstream_refused(census, lineage, lineage_count, refused)) return;
    out_lo[at] = to_word((wide)a_lo[at] + (wide)b_lo[at], refused);
    out_hi[at] = to_word((wide)a_hi[at] + (wide)b_hi[at], refused);
}

// `x · s` for an enclosed scalar `s ∈ [s_lo, s_hi] · 2^-Fs` — an algebraic number carried as its
// certified enclosure, never as a float.
extern "C" __global__ void section_scale(
    const int64_t *lo, const int64_t *hi, uint32_t count, int64_t s_lo, int64_t s_hi, int32_t scale_grain,
    int64_t *out_lo, int64_t *out_hi, uint32_t *refused, const uint32_t *census, const uint32_t *lineage, uint32_t lineage_count
) {
    uint32_t at = blockIdx.x * blockDim.x + threadIdx.x;
    if (at >= count) return;
    if (upstream_refused(census, lineage, lineage_count, refused)) return;
    wide l, h;
    corners(lo[at], hi[at], s_lo, s_hi, &l, &h, refused);
    out_lo[at] = to_word(shift_floor(l, -scale_grain, refused), refused);
    out_hi[at] = to_word(shift_ceil(h, -scale_grain, refused), refused);
}

// A declared span of columns withdrawn — the matched-sibling intervention — OUT OF PLACE: the
// predecessor is what the caller still holds; nothing is discarded, and no section is written in
// place, so the write footprint of this occurrence is its own output alone.
extern "C" __global__ void section_withdraw_columns(
    const int64_t *lo, const int64_t *hi, uint32_t rows, uint32_t width, uint32_t from, uint32_t span,
    int64_t *out_lo, int64_t *out_hi, uint32_t *refused, const uint32_t *census, const uint32_t *lineage, uint32_t lineage_count
) {
    uint32_t flat = blockIdx.x * blockDim.x + threadIdx.x;
    if (flat >= rows * width) return;
    if (upstream_refused(census, lineage, lineage_count, refused)) return;
    uint32_t c = flat % width;
    int withdrawn = (c >= from && c < from + span);
    out_lo[flat] = withdrawn ? 0 : lo[flat];
    out_hi[flat] = withdrawn ? 0 : hi[flat];
}

// **A CONTROL, and it is unsound by construction**: every enclosure collapsed to its lower midpoint,
// the widths dropped. It exists so a driver can show that the propagated remainder is load-bearing.
extern "C" __global__ void section_collapse_control(
    const int64_t *lo, const int64_t *hi, uint32_t count, int64_t *out_lo, int64_t *out_hi,
    uint32_t *refused, const uint32_t *census, const uint32_t *lineage, uint32_t lineage_count
) {
    uint32_t at = blockIdx.x * blockDim.x + threadIdx.x;
    if (at >= count) return;
    if (upstream_refused(census, lineage, lineage_count, refused)) return;
    wide mid = shift_floor((wide)lo[at] + (wide)hi[at], -1, refused);
    out_lo[at] = (int64_t)mid;
    out_hi[at] = (int64_t)mid;
}

// **The carry**: a resident standing entering this passage from an earlier one — the residual
// stream of the previous layer, or a shared K/V standing — copied into this passage's own section
// so the graph owns what it reads. No octet crosses the apparatus boundary; the lineage is
// inspected like every other kernel's.
extern "C" __global__ void section_carry(
    const int64_t *in_lo, const int64_t *in_hi, uint32_t count,
    int64_t *out_lo, int64_t *out_hi, uint32_t *refused, const uint32_t *census, const uint32_t *lineage, uint32_t lineage_count
) {
    uint32_t at = blockIdx.x * blockDim.x + threadIdx.x;
    if (at >= count) return;
    if (upstream_refused(census, lineage, lineage_count, refused)) return;
    out_lo[at] = in_lo[at];
    out_hi[at] = in_hi[at];
}

// The census of one written section into the occurrence's own slot: the widest octave, the widest
// enclosure, whether any coordinate inverted, and whether the a-priori octave bound the occurrence
// was admitted under HELD. A refuted bound is written into THIS occurrence's refusal word, which
// every declared successor inspects at entry, so no successor computes on words wider than it was
// admitted for. Writes the marker. Nothing here is shared with an unrelated occurrence.
extern "C" __global__ void section_census(
    const int64_t *lo, const int64_t *hi, uint32_t count, uint32_t admitted_octaves,
    uint32_t *slot
) {
    uint32_t at = blockIdx.x * blockDim.x + threadIdx.x;
    if (at >= count) return;
    // An occurrence whose semantic kernel refused — of its own, or upstream — has no standing face
    // to measure: its words are partially written or never written. The census marks that it ran
    // and measures nothing, so a refused occurrence never acquires a second, spurious refusal from
    // the census reading what allocation left in its section.
    if (slot[SLOT_REFUSED] != 0u) { if (at == 0) slot[SLOT_WRITTEN] = 1u; return; }
    wide a = lo[at], b = hi[at];
    uwide ma = magnitude(a), mb = magnitude(b);
    uint32_t oct = octaves_of(ma > mb ? ma : mb);
    atomicMax(slot + SLOT_OCTAVE, oct);
    if (b >= a) {
        uwide width = (uwide)(b - a);   // b − a of two int64 words: at most 2^64, exact in the wide carrier
        unsigned long long w64 = (unsigned long long)(width > (uwide)UINT64_MAX ? UINT64_MAX : (uint64_t)width);
        atomicMax((unsigned long long *)(slot + SLOT_WIDTH), w64);
        atomicAdd((unsigned long long *)(slot + SLOT_WIDTH_SUM), w64);
        if (w64 != 0ull) atomicAdd(slot + SLOT_NONZERO_WIDTHS, 1u);
    } else {
        atomicOr(slot + SLOT_INVERTED, 1u);
        atomicOr(slot + SLOT_REFUSED, REFUSED_INVERTED);
    }
    if (oct > admitted_octaves) {
        atomicOr(slot + SLOT_BOUND, 1u);
        atomicOr(slot + SLOT_REFUSED, REFUSED_BOUND);
    }
    if (at == 0) slot[SLOT_WRITTEN] = 1u;
}

// ---------------------------------------------------------------------------------------------
// the arithmetic control: the helpers exposed for a serial-chart exact reference to refute
// ---------------------------------------------------------------------------------------------

// For each `i`: `shift_floor(a, s)`, `shift_ceil(a, s)`, `product_shift(a, b, |s|)` both ways,
// `div_floor(a, b)`, `div_ceil(a, b)` where `b > 0`, and the interval quotient of `[a, a+span]`
// over `[b, b+span]` lifted by 1. Inputs are `int64` words (so the signed minimum is reachable),
// results are wide values returned as `(lo64, hi64)` pairs. Refusals land in `refused[i]`.
extern "C" __global__ void section_arithmetic_control(
    const int64_t *a, const int64_t *b, const int32_t *s, const int64_t *span, uint32_t count,
    int64_t *out, uint32_t *refused
) {
    uint32_t i = blockIdx.x * blockDim.x + threadIdx.x;
    if (i >= count) return;
    uint32_t *r = refused + i;
    wide av = a[i], bv = b[i]; int sv = s[i]; wide sp = span[i];
    wide results[10];
    results[0] = shift_floor(av, sv, r);
    results[1] = shift_ceil(av, sv, r);
    int k = sv < 0 ? -sv : sv;
    results[2] = product_shift(av, bv, k, 0, r);
    results[3] = product_shift(av, bv, k, 1, r);
    // The division helpers are called unconditionally: a non-positive denominator is refused BY
    // THEM, which is the property under test.
    results[4] = div_floor(av, bv, r);
    results[5] = div_ceil(av, bv, r);
    wide q_lo = 0, q_hi = 0;
    interval_quotient(av, av + sp, bv, bv + sp, 1, &q_lo, &q_hi, r);
    results[6] = q_lo; results[7] = q_hi;
    wide c_lo, c_hi;
    corners(av, av + sp, bv, bv + sp, &c_lo, &c_hi, r);
    results[8] = c_lo; results[9] = c_hi;
    for (int j = 0; j < 10; ++j) {
        out[((size_t)i * 10 + j) * 2] = (int64_t)(uint64_t)(uwide)results[j];
        out[((size_t)i * 10 + j) * 2 + 1] = (int64_t)(uint64_t)((uwide)results[j] >> 64);
    }
}

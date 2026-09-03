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

__device__ __forceinline__ void node_aperture(wide l, wide h, uint32_t admitted, uint32_t *slot);

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
// derived-rank factorized contraction: shared-wide v reductions and one final i64 front
// ---------------------------------------------------------------------------------------------

// `out[t,o] = sum_j u[o,j] · (v[j] · section[t])`.  Each scalar interval is rounded at `v_e`
// exactly as `section_contract` would and kept wide in shared storage.  Each rank-one atom is then
// placed at `u_e` before the exact atom population is added.  Rank one therefore retains bit
// equality with the original fused law; higher rank is exactly a family of those atoms.  `rank`
// is the mounted junction extent checked by the host shape law, never padding or a tuning bound.
extern "C" __global__ void section_factorized_contract(
    const int64_t *lo, const int64_t *hi, uint32_t rows, uint32_t inner,
    const int64_t *u, int32_t u_e, uint32_t out_width,
    const int64_t *v, int32_t v_e, uint32_t rank, uint32_t v_width, int32_t grain,
    int64_t *out_lo, int64_t *out_hi, uint32_t *refused, const uint32_t *census, const uint32_t *lineage, uint32_t lineage_count
) {
    extern __shared__ unsigned char shared_raw[];
    wide *sum_lo = (wide *)shared_raw;
    wide *sum_hi = sum_lo + blockDim.x;
    wide *scalar_lo = sum_hi + blockDim.x;
    wide *scalar_hi = scalar_lo + rank;
    __shared__ uint32_t stop_s;
    uint32_t row = blockIdx.x;
    if (row >= rows) return;
    if (threadIdx.x == 0) stop_s = upstream_refused(census, lineage, lineage_count, refused) ? 1u : 0u;
    __syncthreads();
    if (stop_s != 0u) return;

    // One block owns one input row.  Every v_j·h interval is reduced once, then all lanes emit the
    // complete u front.  The admitted carrier bound keeps every partial in the same wide domain.
    const int64_t *slo = lo + (size_t)row * (size_t)inner;
    const int64_t *shi = hi + (size_t)row * (size_t)inner;
    for (uint32_t j = 0; j < rank; ++j) {
        wide part_lo = 0, part_hi = 0;
        const int64_t *factor = v + (size_t)j * (size_t)v_width;
        for (uint32_t i = threadIdx.x; i < inner; i += blockDim.x) {
            wide w = (wide)factor[i];
            if (w >= 0) { part_lo += w * (wide)slo[i]; part_hi += w * (wide)shi[i]; }
            else        { part_lo += w * (wide)shi[i]; part_hi += w * (wide)slo[i]; }
        }
        sum_lo[threadIdx.x] = part_lo;
        sum_hi[threadIdx.x] = part_hi;
        __syncthreads();
        for (uint32_t stride = blockDim.x / 2; stride > 0; stride >>= 1) {
            if (threadIdx.x < stride) {
                sum_lo[threadIdx.x] += sum_lo[threadIdx.x + stride];
                sum_hi[threadIdx.x] += sum_hi[threadIdx.x + stride];
            }
            __syncthreads();
        }
        if (threadIdx.x == 0) {
            scalar_lo[j] = shift_floor(sum_lo[0], v_e, refused);
            scalar_hi[j] = shift_ceil(sum_hi[0], v_e, refused);
            stop_s = *refused != 0u ? 1u : 0u;
        }
        __syncthreads();
        if (stop_s != 0u) return;
    }

    for (uint32_t o = threadIdx.x; o < out_width; o += blockDim.x) {
        uint32_t flat = row * out_width + o;
        wide acc_lo = 0, acc_hi = 0;
        for (uint32_t j = 0; j < rank; ++j) {
            wide factor = (wide)u[(size_t)o * (size_t)rank + j];
            if (factor == 0) continue;
            wide product_lo, product_hi;
            if (factor >= 0) {
                product_lo = product_checked(factor, scalar_lo[j], refused);
                product_hi = product_checked(factor, scalar_hi[j], refused);
            } else {
                product_lo = product_checked(factor, scalar_hi[j], refused);
                product_hi = product_checked(factor, scalar_lo[j], refused);
            }
            acc_lo += shift_floor(product_lo, u_e, refused);
            acc_hi += shift_ceil(product_hi, u_e, refused);
        }
        out_lo[flat] = to_word(acc_lo, refused);
        out_hi[flat] = to_word(acc_hi, refused);
    }
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
__device__ __forceinline__ void chronology_body(
    const int64_t *lo, const int64_t *hi, uint32_t rows, uint32_t heads, uint32_t head_width,
    const int64_t *cos_lo, const int64_t *cos_hi, const int64_t *sin_lo, const int64_t *sin_hi,
    int32_t rotation_grain, const uint32_t *positions, int32_t grain, int sign,
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
    // The adjoint of a rotation is the rotation by the opposite angle: the band's sine enclosure
    // is negated (and its endpoints exchanged) under `sign < 0`.
    wide bl = cos_lo[band], bh = cos_hi[band];
    wide tl = sign < 0 ? -(wide)sin_hi[band] : (wide)sin_lo[band];
    wide th = sign < 0 ? -(wide)sin_lo[band] : (wide)sin_hi[band];
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

extern "C" __global__ void section_chronology(
    const int64_t *lo, const int64_t *hi, uint32_t rows, uint32_t heads, uint32_t head_width,
    const int64_t *cos_lo, const int64_t *cos_hi, const int64_t *sin_lo, const int64_t *sin_hi,
    int32_t rotation_grain, const uint32_t *positions, int32_t grain,
    int64_t *out_lo, int64_t *out_hi, uint32_t *refused, const uint32_t *census, const uint32_t *lineage, uint32_t lineage_count
) {
    chronology_body(lo, hi, rows, heads, head_width, cos_lo, cos_hi, sin_lo, sin_hi, rotation_grain,
                    positions, grain, 1, out_lo, out_hi, refused, census, lineage, lineage_count);
}

// The adjoint of the chronology: the same band elements raised to the same positions, turned the
// other way. The returning differential of a rotated pair is the pair rotated back.
extern "C" __global__ void section_chronology_adjoint(
    const int64_t *lo, const int64_t *hi, uint32_t rows, uint32_t heads, uint32_t head_width,
    const int64_t *cos_lo, const int64_t *cos_hi, const int64_t *sin_lo, const int64_t *sin_hi,
    int32_t rotation_grain, const uint32_t *positions, int32_t grain,
    int64_t *out_lo, int64_t *out_hi, uint32_t *refused, const uint32_t *census, const uint32_t *lineage, uint32_t lineage_count
) {
    chronology_body(lo, hi, rows, heads, head_width, cos_lo, cos_hi, sin_lo, sin_hi, rotation_grain,
                    positions, grain, -1, out_lo, out_hi, refused, census, lineage, lineage_count);
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

__device__ __forceinline__ void contact_bracket(
    const int64_t *q_lo, const int64_t *q_hi, const int64_t *k_lo, const int64_t *k_hi,
    size_t q_base, size_t k_base, uint32_t head_width, int bracket_shift, int32_t grain,
    wide *s_lo, wide *s_hi, uint32_t *refused
) {
    wide acc_lo = 0, acc_hi = 0;
    for (uint32_t d = 0; d < head_width; ++d) {
        wide ql = shift_floor(q_lo[q_base + d], -bracket_shift, refused);
        wide qh = shift_ceil(q_hi[q_base + d], -bracket_shift, refused);
        wide kl = shift_floor(k_lo[k_base + d], -bracket_shift, refused);
        wide kh = shift_ceil(k_hi[k_base + d], -bracket_shift, refused);
        wide l, u;
        corners(ql, qh, kl, kh, &l, &u, refused);
        acc_lo += l; acc_hi += u;
    }
    *s_lo = shift_floor(acc_lo, -(grain - 2 * bracket_shift), refused);
    *s_hi = shift_ceil(acc_hi, -(grain - 2 * bracket_shift), refused);
}

// One block per `(row, receiver head)`. K/V family `g = h / (H / KH)` serves head `h`, which is the
// source's `repeat_kv`. The reach is traversed in block-derived tiles. Shared memory is therefore
// `2 * blockDim` exact words, independent of history length: no caller-authored context ceiling and
// no whole-reach staging buffer. The null, partition, and carried construction remain three exact
// passes over the same founded reach.
extern "C" __global__ void section_contact(
    const int64_t *q_lo, const int64_t *q_hi, const int64_t *k_lo, const int64_t *k_hi,
    const int64_t *v_lo, const int64_t *v_hi,
    uint32_t rows, uint32_t heads, uint32_t kv_heads, uint32_t head_width, uint32_t window,
    const uint32_t *partition_boundaries, uint32_t partition_boundary_count,
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
    uint32_t section_start = 0;
    if (partition_boundary_count != 0) {
        bool found = false;
        for (uint32_t section = 0; section + 1 < partition_boundary_count; ++section) {
            uint32_t first = partition_boundaries[section];
            uint32_t after = partition_boundaries[section + 1];
            if (first >= after || after > rows) {
                if (threadIdx.x == 0) atomicOr(refused, REFUSED_MALFORMED);
                return;
            }
            if (t >= first && t < after) {
                section_start = first;
                found = true;
                break;
            }
        }
        if (!found) {
            if (threadIdx.x == 0) atomicOr(refused, REFUSED_MALFORMED);
            return;
        }
    }
    uint32_t start = (t + 1 > window) ? (t + 1 - window) : 0;
    if (start < section_start) start = section_start;
    uint32_t reach = t - start + 1;
    wide *scratch_lo = (wide *)shared_raw;
    wide *scratch_hi = scratch_lo + blockDim.x;
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
    // (a) the null: each lane traverses its part of the reach, then one exact maximum reduction.
    wide local_null = -(((wide)1) << 126);
    for (uint32_t r = threadIdx.x; r < reach; r += blockDim.x) {
        uint32_t j = start + r;
        size_t k_base = ((size_t)j * kv_heads + g) * head_width;
        wide sl, sh;
        contact_bracket(q_lo, q_hi, k_lo, k_hi, q_base, k_base, head_width, bs, grain, &sl, &sh, refused);
        if (sh > local_null) local_null = sh;
    }
    scratch_hi[threadIdx.x] = local_null;
    __syncthreads();
    for (uint32_t stride = blockDim.x / 2; stride > 0; stride >>= 1) {
        if (threadIdx.x < stride && scratch_hi[threadIdx.x + stride] > scratch_hi[threadIdx.x]) {
            scratch_hi[threadIdx.x] = scratch_hi[threadIdx.x + stride];
        }
        __syncthreads();
    }
    if (threadIdx.x == 0) { null_value = scratch_hi[0]; atomicMax(reach_census, reach); }
    __syncthreads();

    // (b) partition and carried construction in one tiled pass. Each founded weight contributes
    // once to the directed partition and simultaneously to every carried coordinate before the
    // scratch row is reused. The null pass remains separate because every ratio shares its gauge.
    if (threadIdx.x == 0) { total_lo = 0; total_hi = 0; }
    __syncthreads();
    uint32_t d = threadIdx.x;
    wide num_lo = 0, num_hi = 0, hull_lo = 0, hull_hi = 0;
    for (uint32_t tile = 0; tile < reach; tile += blockDim.x) {
        uint32_t r = tile + threadIdx.x;
        if (r < reach) {
            uint32_t j = start + r;
            size_t k_base = ((size_t)j * kv_heads + g) * head_width;
            wide sl, sh;
            contact_bracket(q_lo, q_hi, k_lo, k_hi, q_base, k_base, head_width, bs, grain, &sl, &sh, refused);
            wide lo_arg = sl - null_value, hi_arg = sh - null_value;
            if (hi_arg > 0) hi_arg = 0;
            wide e_lo_lo, e_lo_hi, e_hi_lo, e_hi_hi;
            exp_nonpositive(lo_arg, grain, terms, &e_lo_lo, &e_lo_hi, refused);
            exp_nonpositive(hi_arg, grain, terms, &e_hi_lo, &e_hi_hi, refused);
            scratch_lo[threadIdx.x] = e_lo_lo;
            scratch_hi[threadIdx.x] = e_hi_hi;
        }
        __syncthreads();
        uint32_t tile_reach = (reach - tile) < blockDim.x ? (reach - tile) : blockDim.x;
        if (threadIdx.x == 0) {
            wide tile_total_lo = 0, tile_total_hi = 0;
            for (uint32_t within = 0; within < tile_reach; ++within) {
                tile_total_lo += scratch_lo[within];
                tile_total_hi += scratch_hi[within];
            }
            total_lo += tile_total_lo;
            total_hi += tile_total_hi;
        }
        if (d < head_width) {
            for (uint32_t within = 0; within < tile_reach; ++within) {
                uint32_t j = start + tile + within;
                size_t v_at = ((size_t)j * kv_heads + g) * head_width + d;
                wide vl = v_lo[v_at], vh = v_hi[v_at], pl, ph;
                corners(scratch_lo[within], scratch_hi[within], vl, vh, &pl, &ph, refused);
                num_lo += pl; num_hi += ph;
                if (tile == 0 && within == 0) { hull_lo = vl; hull_hi = vh; }
                else { if (vl < hull_lo) hull_lo = vl; if (vh > hull_hi) hull_hi = vh; }
            }
        }
        __syncthreads();
    }
    wide tl = total_lo, th = total_hi;
    if (tl <= 0) {
        if (threadIdx.x == 0) atomicOr(refused, REFUSED_MALFORMED);
        return;
    }
    if (d < head_width) {
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

// The monotone hyperbolic-tangent reaction as one certified interval operation at the section's
// grain. It shares the same exponential owner as contact and GELU but does not smuggle either law.
extern "C" __global__ void section_tanh(
    const int64_t *lo, const int64_t *hi, uint32_t count, int32_t grain, uint32_t terms,
    int64_t *out_lo, int64_t *out_hi, uint32_t *refused, const uint32_t *census, const uint32_t *lineage, uint32_t lineage_count
) {
    uint32_t at = blockIdx.x * blockDim.x + threadIdx.x;
    if (at >= count) return;
    if (upstream_refused(census, lineage, lineage_count, refused)) return;
    wide lower, upper, discard_low = 0, discard_high = 0;
    if (lo[at] >= 0) tanh_nonnegative((wide)lo[at], grain, terms, &lower, &discard_high, refused);
    else { wide l, h; tanh_nonnegative(-(wide)lo[at], grain, terms, &l, &h, refused); lower = -h; }
    if (hi[at] >= 0) tanh_nonnegative((wide)hi[at], grain, terms, &discard_low, &upper, refused);
    else { wide l, h; tanh_nonnegative(-(wide)hi[at], grain, terms, &l, &h, refused); upper = -l; }
    (void)discard_low; (void)discard_high;
    if (lower > upper) atomicOr(refused, REFUSED_INVERTED);
    out_lo[at] = to_word(lower, refused);
    out_hi[at] = to_word(upper, refused);
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

// `x · s` where `s` is one exact aligned resident coefficient, `s[0] · 2^s_e`. The coefficient
// stays on the resident chart; only its address and complete-population frame enter the law.
extern "C" __global__ void section_scale_by_aligned(
    const int64_t *lo, const int64_t *hi, uint32_t count, const int64_t *s, int32_t s_e,
    int64_t *out_lo, int64_t *out_hi, uint32_t *refused, const uint32_t *census, const uint32_t *lineage, uint32_t lineage_count
) {
    uint32_t at = blockIdx.x * blockDim.x + threadIdx.x;
    if (at >= count) return;
    if (upstream_refused(census, lineage, lineage_count, refused)) return;
    wide scalar = (wide)s[0];
    wide lower = scalar >= 0 ? scalar * (wide)lo[at] : scalar * (wide)hi[at];
    wide upper = scalar >= 0 ? scalar * (wide)hi[at] : scalar * (wide)lo[at];
    out_lo[at] = to_word(shift_floor(lower, s_e, refused), refused);
    out_hi[at] = to_word(shift_ceil(upper, s_e, refused), refused);
}

// Select one contiguous coordinate face from every row. The source section remains intact; the
// output is the addressed face itself, with its row lineage and grain unchanged.
extern "C" __global__ void section_select_columns(
    const int64_t *lo, const int64_t *hi, uint32_t rows, uint32_t width, uint32_t from, uint32_t span,
    int64_t *out_lo, int64_t *out_hi, uint32_t *refused, const uint32_t *census, const uint32_t *lineage, uint32_t lineage_count
) {
    uint32_t flat = blockIdx.x * blockDim.x + threadIdx.x;
    if (flat >= rows * span) return;
    if (upstream_refused(census, lineage, lineage_count, refused)) return;
    uint32_t row = flat / span;
    uint32_t column = flat % span;
    size_t source = (size_t)row * (size_t)width + (size_t)from + column;
    out_lo[flat] = lo[source];
    out_hi[flat] = hi[source];
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

// **An intervention, typed as one by the passage**: the rows `[from, from + span)` withdrawn —
// zeroed — so a contact over these standings sees no such positions. Exact.
extern "C" __global__ void section_withdraw_rows(
    const int64_t *lo, const int64_t *hi, uint32_t rows, uint32_t width, uint32_t from, uint32_t span,
    int64_t *out_lo, int64_t *out_hi, uint32_t *refused, const uint32_t *census, const uint32_t *lineage, uint32_t lineage_count
) {
    uint32_t flat = blockIdx.x * blockDim.x + threadIdx.x;
    if (flat >= rows * width) return;
    if (upstream_refused(census, lineage, lineage_count, refused)) return;
    uint32_t r = flat / width;
    int withdrawn = (r >= from && r < from + span);
    out_lo[flat] = withdrawn ? 0 : lo[flat];
    out_hi[flat] = withdrawn ? 0 : hi[flat];
}

// The terminal receiver's exact factorization: retain only the last row of a non-empty section.
// No unrequested row is allocated or zero-filled, and every coordinate preserves its enclosure.
extern "C" __global__ void section_terminal_row(
    const int64_t *lo, const int64_t *hi, uint32_t rows, uint32_t width,
    int64_t *out_lo, int64_t *out_hi, uint32_t *refused, const uint32_t *census, const uint32_t *lineage, uint32_t lineage_count
) {
    uint32_t column = blockIdx.x * blockDim.x + threadIdx.x;
    if (column >= width) return;
    if (upstream_refused(census, lineage, lineage_count, refused)) return;
    size_t source = (size_t)(rows - 1) * width + column;
    out_lo[column] = lo[source];
    out_hi[column] = hi[source];
}

// The receiver-directed terminal of every independent causal section. `boundaries[0] = 0`, the
// final boundary is `rows`, and strict increase is established before launch. No source row is
// averaged or discarded from the reconstruction fibre.
extern "C" __global__ void section_partition_terminal_rows(
    const int64_t *lo, const int64_t *hi, uint32_t rows, uint32_t width,
    const uint32_t *boundaries, uint32_t groups,
    int64_t *out_lo, int64_t *out_hi, uint32_t *refused,
    const uint32_t *census, const uint32_t *lineage, uint32_t lineage_count
) {
    uint32_t flat = blockIdx.x * blockDim.x + threadIdx.x;
    if (flat >= groups * width) return;
    if (upstream_refused(census, lineage, lineage_count, refused)) return;
    uint32_t group = flat / width;
    uint32_t coordinate = flat % width;
    uint32_t first = boundaries[group];
    uint32_t after = boundaries[group + 1];
    if (first >= after || after > rows) {
        atomicOr(refused, REFUSED_MALFORMED);
        out_lo[flat] = 0;
        out_hi[flat] = 0;
        return;
    }
    size_t source = (size_t)(after - 1) * width + coordinate;
    out_lo[flat] = lo[source];
    out_hi[flat] = hi[source];
}

// The receiver-directed integral of each non-empty row block. `boundaries[0] = 0`, the last
// boundary is `rows`, and strict increase is established by the resident law before launch. One
// thread owns one `(block, coordinate)` and returns the directed exact mean; the source section is
// untouched and remains the reconstruction fibre.
extern "C" __global__ void section_partition_mean(
    const int64_t *lo, const int64_t *hi, uint32_t rows, uint32_t width,
    const uint32_t *boundaries, uint32_t groups,
    int64_t *out_lo, int64_t *out_hi, uint32_t *refused,
    const uint32_t *census, const uint32_t *lineage, uint32_t lineage_count
) {
    uint32_t flat = blockIdx.x * blockDim.x + threadIdx.x;
    if (flat >= groups * width) return;
    if (upstream_refused(census, lineage, lineage_count, refused)) return;
    uint32_t group = flat / width;
    uint32_t coordinate = flat % width;
    uint32_t first = boundaries[group];
    uint32_t after = boundaries[group + 1];
    if (first >= after || after > rows) {
        atomicOr(refused, REFUSED_MALFORMED);
        out_lo[flat] = 0;
        out_hi[flat] = 0;
        return;
    }
    wide lower = 0, upper = 0;
    for (uint32_t row = first; row < after; ++row) {
        size_t at = (size_t)row * width + coordinate;
        lower += (wide)lo[at];
        upper += (wide)hi[at];
    }
    wide population = (wide)(after - first);
    out_lo[flat] = to_word(div_floor(lower, population, refused), refused);
    out_hi[flat] = to_word(div_ceil(upper, population, refused), refused);
}

// **An intervention, typed as one by the passage**: the columns permuted in blocks of `block` —
// `out[r, b·block + i] = in[r, perm[b]·block + i]` for a declared permutation `perm` of the
// `width / block` blocks (a head permutation when `block` is the head width). A rebase: invertible,
// exact, width-preserving.
extern "C" __global__ void section_permute_columns(
    const int64_t *lo, const int64_t *hi, uint32_t rows, uint32_t width, uint32_t block, const uint32_t *perm,
    int64_t *out_lo, int64_t *out_hi, uint32_t *refused, const uint32_t *census, const uint32_t *lineage, uint32_t lineage_count
) {
    uint32_t flat = blockIdx.x * blockDim.x + threadIdx.x;
    if (flat >= rows * width) return;
    if (upstream_refused(census, lineage, lineage_count, refused)) return;
    uint32_t r = flat / width;
    uint32_t c = flat % width;
    uint32_t b = c / block, i = c % block;
    uint32_t source = perm[b] * block + i;
    out_lo[flat] = lo[(size_t)r * width + source];
    out_hi[flat] = hi[(size_t)r * width + source];
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

// ---------------------------------------------------------------------------------------------
// the census: six commutative receivers, aggregated in the block and deposited once
// ---------------------------------------------------------------------------------------------
//
// **Every word this census writes is a max, an or, or an add over the coordinates.** Each is
// commutative and associative and each coordinate's contribution is independent of every other, so
// the fold may be taken in any order and by any grouping: warp, then block, then one atomic per
// block per word. The atomics testify for exactly those receivers and for nothing ordered, which is
// the only thing they were ever entitled to testify for.
//
//   SLOT_OCTAVE          max over coordinates of the wider endpoint's octaves
//   SLOT_WIDTH  [6..8]   max over coordinates of `hi - lo`, saturated at the 64-bit word
//   SLOT_WIDTH_SUM       add over coordinates of the same width
//   SLOT_NONZERO_WIDTHS  add over coordinates of `width != 0`
//   SLOT_INVERTED        or  over coordinates of `hi < lo`   (and `REFUSED_INVERTED` with it)
//   SLOT_BOUND           or  over coordinates of `octaves > admitted`  (and `REFUSED_BOUND`)
//   SLOT_WRITTEN         a plain store of 1 by one thread — not a reduction and not an atomic
//
// `section_census_serial_control` below is the per-thread-atomic form this replaces, kept verbatim
// so the equality is measured forever rather than argued once.
//
// **One order-dependence is inherited and is not this aggregation's**: both forms decide whether to
// measure at all by reading `slot[SLOT_REFUSED]`, and both also OR `REFUSED_INVERTED` /
// `REFUSED_BOUND` into that same word. On material where the census itself raises a refusal, a
// thread (control) or a block (this form) that entered before the raise measures its coordinates and
// one that entered after does not. The occurrence refuses either way and its face may not be read;
// what moves is the measured octave/width the receipt displays. Where the census raises nothing —
// every standing occurrence — both forms are exactly order-free.

#define CENSUS_MAX_WARPS 32

__device__ __forceinline__ uint32_t warp_max_u32(uint32_t v) {
    for (int d = 16; d > 0; d >>= 1) { uint32_t o = __shfl_down_sync(0xffffffffu, v, (unsigned)d, 32); if (o > v) v = o; }
    return v;
}
__device__ __forceinline__ uint32_t warp_or_u32(uint32_t v) {
    for (int d = 16; d > 0; d >>= 1) v |= __shfl_down_sync(0xffffffffu, v, (unsigned)d, 32);
    return v;
}
__device__ __forceinline__ uint32_t warp_add_u32(uint32_t v) {
    for (int d = 16; d > 0; d >>= 1) v += __shfl_down_sync(0xffffffffu, v, (unsigned)d, 32);
    return v;
}
__device__ __forceinline__ unsigned long long warp_max_u64(unsigned long long v) {
    for (int d = 16; d > 0; d >>= 1) { unsigned long long o = __shfl_down_sync(0xffffffffu, v, (unsigned)d, 32); if (o > v) v = o; }
    return v;
}
__device__ __forceinline__ unsigned long long warp_add_u64(unsigned long long v) {
    for (int d = 16; d > 0; d >>= 1) v += __shfl_down_sync(0xffffffffu, v, (unsigned)d, 32);
    return v;
}

// The census of one written section into the occurrence's own slot: the widest octave, the widest
// enclosure, whether any coordinate inverted, and whether the a-priori octave bound the occurrence
// was admitted under HELD. A refuted bound is written into THIS occurrence's refusal word, which
// every declared successor inspects at entry, so no successor computes on words wider than it was
// admitted for. Writes the marker. Nothing here is shared with an unrelated occurrence.
//
// The block is a whole number of warps by the surface's own launch derivation; the launcher refuses
// a block that is not, because a warp fold with an incomplete mask is undefined.
extern "C" __global__ void section_census(
    const int64_t *lo, const int64_t *hi, uint32_t count, uint32_t admitted_octaves,
    uint32_t *slot
) {
    __shared__ uint32_t entry_refused;
    __shared__ uint32_t part_oct[CENSUS_MAX_WARPS];
    __shared__ unsigned long long part_wid[CENSUS_MAX_WARPS];
    __shared__ unsigned long long part_sum[CENSUS_MAX_WARPS];
    __shared__ uint32_t part_nz[CENSUS_MAX_WARPS];
    __shared__ uint32_t part_inv[CENSUS_MAX_WARPS];
    __shared__ uint32_t part_bnd[CENSUS_MAX_WARPS];
    // An occurrence whose semantic kernel refused — of its own, or upstream — has no standing face
    // to measure. The reading is taken once per block so the whole block leaves together: a warp
    // fold requires every lane of the warp, so no thread may return early here.
    if (threadIdx.x == 0) entry_refused = slot[SLOT_REFUSED];
    __syncthreads();
    if (entry_refused != 0u) {
        if (blockIdx.x == 0 && threadIdx.x == 0 && count > 0u) slot[SLOT_WRITTEN] = 1u;
        return;
    }
    const uint32_t at = blockIdx.x * blockDim.x + threadIdx.x;
    uint32_t oct = 0u, nonzero = 0u, inverted = 0u, bound = 0u;
    unsigned long long w64 = 0ull, wsum = 0ull;
    if (at < count) {
        wide a = lo[at], b = hi[at];
        uwide ma = magnitude(a), mb = magnitude(b);
        oct = octaves_of(ma > mb ? ma : mb);
        if (b >= a) {
            uwide width = (uwide)(b - a);   // b − a of two int64 words: at most 2^64, exact in the wide carrier
            w64 = (unsigned long long)(width > (uwide)UINT64_MAX ? UINT64_MAX : (uint64_t)width);
            wsum = w64;
            nonzero = (w64 != 0ull) ? 1u : 0u;
        } else {
            inverted = 1u;
        }
        if (oct > admitted_octaves) bound = 1u;
    }
    const uint32_t lane = threadIdx.x & 31u;
    const uint32_t warp = threadIdx.x >> 5;
    const uint32_t warps = (blockDim.x + 31u) >> 5;
    oct = warp_max_u32(oct);
    w64 = warp_max_u64(w64);
    wsum = warp_add_u64(wsum);
    nonzero = warp_add_u32(nonzero);
    inverted = warp_or_u32(inverted);
    bound = warp_or_u32(bound);
    if (lane == 0u && warp < CENSUS_MAX_WARPS) {
        part_oct[warp] = oct; part_wid[warp] = w64; part_sum[warp] = wsum;
        part_nz[warp] = nonzero; part_inv[warp] = inverted; part_bnd[warp] = bound;
    }
    __syncthreads();
    if (threadIdx.x == 0) {
        for (uint32_t w = 1; w < warps && w < CENSUS_MAX_WARPS; ++w) {
            if (part_oct[w] > part_oct[0]) part_oct[0] = part_oct[w];
            if (part_wid[w] > part_wid[0]) part_wid[0] = part_wid[w];
            part_sum[0] += part_sum[w];
            part_nz[0] += part_nz[w];
            part_inv[0] |= part_inv[w];
            part_bnd[0] |= part_bnd[w];
        }
        // One atomic per block per word, and none at all where the block's fold is the identity.
        if (part_oct[0] != 0u) atomicMax(slot + SLOT_OCTAVE, part_oct[0]);
        if (part_wid[0] != 0ull) atomicMax((unsigned long long *)(slot + SLOT_WIDTH), part_wid[0]);
        if (part_sum[0] != 0ull) atomicAdd((unsigned long long *)(slot + SLOT_WIDTH_SUM), part_sum[0]);
        if (part_nz[0] != 0u) atomicAdd(slot + SLOT_NONZERO_WIDTHS, part_nz[0]);
        if (part_inv[0] != 0u) { atomicOr(slot + SLOT_INVERTED, 1u); atomicOr(slot + SLOT_REFUSED, REFUSED_INVERTED); }
        if (part_bnd[0] != 0u) { atomicOr(slot + SLOT_BOUND, 1u); atomicOr(slot + SLOT_REFUSED, REFUSED_BOUND); }
        if (blockIdx.x == 0 && count > 0u) slot[SLOT_WRITTEN] = 1u;
    }
}

// **THE CONTROL, kept verbatim**: the per-thread-atomic census the block-aggregated one above
// replaces. It is never recorded into a passage; a driver launches both on one section and the slot
// words must agree word for word. Deleting it would make the equality an argument instead of a
// measurement.
extern "C" __global__ void section_census_serial_control(
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
// the midpoint quotient, FUSED: the collapse and this occurrence's own census in one node
// ---------------------------------------------------------------------------------------------
//
// **This is an apparatus compression declared per occurrence, never occurrence identity.** The
// quotient remains an occurrence of the diagram with its own law, its own slot and its own census;
// what is compressed is that its collapse and its census are one launch instead of two, and that its
// section is its predecessor's own words rewritten in place instead of a second allocation.
//
// The predecessor's section is therefore GONE — its words are the midpoints after this node — which
// is why the passage refuses the fusion unless the predecessor's only consumer is this quotient and
// no receiver declared its face. The reopening route is the unfused law: bind `MidpointQuotient`
// instead and the predecessor's enclosure stands in its own section, censused and readable.
//
// **Why it is exactly the unfused pair, on every path.**
//   * the collapse originates no refusal: `shift_floor(lo + hi, -1)` on two `int64` words leaves the
//     wide carrier untouched, so the only flag this occurrence can carry is `REFUSED_UPSTREAM`;
//   * the upstream decision is thread-uniform and final at entry, because this node is ordered after
//     the predecessor's census by the graph's own edge — exactly where the unfused collapse kernel
//     sat;
//   * the census of a collapsed section measures `lo == hi`, so every width is zero: `SLOT_WIDTH`,
//     `SLOT_WIDTH_SUM` and `SLOT_NONZERO_WIDTHS` are the identity and `SLOT_INVERTED` is
//     unreachable. Only the octave max and the bound or remain, and both are block-aggregated
//     exactly as the census above aggregates them.
// The predecessor's own census — the PRE-quotient widths, which are the collapsed population this
// chart retains — is untouched: it is its own node on the predecessor's lane and it ran first.
extern "C" __global__ void section_midpoint_seal(
    int64_t *lo, int64_t *hi, uint32_t count, uint32_t admitted_octaves,
    uint32_t *slot, const uint32_t *census, const uint32_t *lineage, uint32_t lineage_count
) {
    __shared__ uint32_t stopped;
    __shared__ uint32_t part_oct[CENSUS_MAX_WARPS];
    __shared__ uint32_t part_bnd[CENSUS_MAX_WARPS];
    if (threadIdx.x == 0) stopped = upstream_refused(census, lineage, lineage_count, slot) ? 1u : 0u;
    __syncthreads();
    if (stopped != 0u) {
        if (blockIdx.x == 0 && threadIdx.x == 0 && count > 0u) slot[SLOT_WRITTEN] = 1u;
        return;
    }
    const uint32_t at = blockIdx.x * blockDim.x + threadIdx.x;
    uint32_t oct = 0u, bound = 0u;
    if (at < count) {
        // IN PLACE, and lawfully so: this thread reads and writes only coordinate `at`, no other
        // thread touches it, and no other occurrence reads this section — the compile refused the
        // fusion otherwise.
        wide m = shift_floor((wide)lo[at] + (wide)hi[at], -1, slot);
        lo[at] = (int64_t)m;
        hi[at] = (int64_t)m;
        oct = octaves_of(magnitude(m));
        if (oct > admitted_octaves) bound = 1u;
    }
    const uint32_t lane = threadIdx.x & 31u;
    const uint32_t warp = threadIdx.x >> 5;
    const uint32_t warps = (blockDim.x + 31u) >> 5;
    oct = warp_max_u32(oct);
    bound = warp_or_u32(bound);
    if (lane == 0u && warp < CENSUS_MAX_WARPS) { part_oct[warp] = oct; part_bnd[warp] = bound; }
    __syncthreads();
    if (threadIdx.x == 0) {
        for (uint32_t w = 1; w < warps && w < CENSUS_MAX_WARPS; ++w) {
            if (part_oct[w] > part_oct[0]) part_oct[0] = part_oct[w];
            part_bnd[0] |= part_bnd[w];
        }
        if (part_oct[0] != 0u) atomicMax(slot + SLOT_OCTAVE, part_oct[0]);
        if (part_bnd[0] != 0u) { atomicOr(slot + SLOT_BOUND, 1u); atomicOr(slot + SLOT_REFUSED, REFUSED_BOUND); }
        if (blockIdx.x == 0 && count > 0u) slot[SLOT_WRITTEN] = 1u;
    }
}

// The return: the receiver return, the adjoints of the contraction and of every reaction, and
// the deposit seal live in their own unit beside this one and share these helpers.
#include "exact_resident_adjoint.cuh"

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

// ---------------------------------------------------------------------------------------------
// the tiled contraction: THE SAME ARITHMETIC, a cooperative geometry
// ---------------------------------------------------------------------------------------------
//
// `section_contract` above is the independent exact reference and is NOT modified. What follows is
// a second realization of the same law: one block owns a disjoint output tile, its lanes cooperate
// over the inner axis, and the map row is walked along `i` so a warp instruction reads contiguous
// octets. Everything semantic is carried over verbatim:
//
//   * the carrier — `int64_t` endpoints at grain `2^-F`, `__int128` accumulation;
//   * the sign rule — `w >= 0 -> (lo*lo, hi*hi)`, `w < 0 -> (lo*hi, hi*lo)`; the map is a POINT, so
//     both endpoints are attained and no widening enters;
//   * NO PARTIAL IS EVER ROUNDED. Every intermediate over any subset `A` of `[0, inner)` is the
//     exact integer `sum_{i in A} w_i x_i^(sel)` at grain `2^(map_e - F)`;
//   * THE ONE OUTWARD ROUNDING sits after the whole K sum — at lane 0 in the K-complete kernel and
//     in the join kernel in the split-K pair — and nowhere else. `shift_floor`/`shift_ceil`/
//     `to_word` appear at exactly one site in each entry;
//   * the census and the lineage — this occurrence's own slot, its declared predecessors only, no
//     new slot word and no new refusal flag.
//
// Three things differ from the scalar owner and each is stated rather than smoothed:
//
//   1. the upstream inspection follows `section_rms_rebase`'s convention, because these kernels
//      carry `__syncthreads()` and a divergent early return is a hazard: thread 0 reads the
//      declared predecessors into a shared sentinel and the whole block leaves together. The tail
//      is a per-write predicate and never an early return;
//   2. a declared per-node aperture `admitted_node_octaves` REFUSES (`REFUSED_CARRIER`) at a node
//      of the reduction tree that exceeds it. The scalar owner has no per-step check at all, so on
//      material outside the a-priori admission the scalar owner wraps silently and this one
//      refuses. That is a behavioural difference and the driver reports it with the fixture that
//      exhibits it; it is never folded into the equality claim. The admission itself needs no new
//      law: for every subset `A` of `[0, inner)`,
//        |sum_{i in A} w_i x_i| <= (sum_{i in A} |w_i|) max_i |x_i| <= (sum_{i in K} |w_i|) max_i |x_i|,
//      which is exactly the row-mass bound the occurrence was already admitted under, so every node
//      of every tree over every K-partition is bounded by the a-priori octaves;
//   3. `tree` selects WHICH fixed word the lanes fold under. `0` is the declared word — descending
//      halving offsets `L/2 .. 1`. `1` is the reversed control — ascending doubling offsets
//      `1 .. L/2`, a genuinely different pairing of the same leaves. Integer addition is exact and
//      associative, so the two must return bit-identical values while their per-node widths need
//      not agree; a divergence there is a defect of the realization and not of the arithmetic.
//
// No float and no division on the wide carrier: the only divisions are `u32` index arithmetic.

// A `__int128` across a warp shuffle, as its four 32-bit words. The tree stays fixed because the
// offsets are the loop's and not the schedule's.
__device__ __forceinline__ wide shfl_down_wide(unsigned mask, wide v, unsigned delta, int width) {
    uwide u = (uwide)v;
    uint32_t w0 = (uint32_t)u, w1 = (uint32_t)(u >> 32), w2 = (uint32_t)(u >> 64), w3 = (uint32_t)(u >> 96);
    w0 = __shfl_down_sync(mask, w0, delta, width);
    w1 = __shfl_down_sync(mask, w1, delta, width);
    w2 = __shfl_down_sync(mask, w2, delta, width);
    w3 = __shfl_down_sync(mask, w3, delta, width);
    return (wide)((uwide)w0 | ((uwide)w1 << 32) | ((uwide)w2 << 64) | ((uwide)w3 << 96));
}

// The per-node overflow aperture. A node past it refuses; nothing wraps and nothing is clamped.
__device__ __forceinline__ void node_aperture(wide l, wide h, uint32_t admitted, uint32_t *slot) {
    if (octaves_of(magnitude(l)) > admitted || octaves_of(magnitude(h)) > admitted) {
        atomicOr(slot + SLOT_REFUSED, REFUSED_CARRIER);
    }
}

// Steps (a), (b) and (c): stage, accumulate exactly, and fold the lanes under the declared word.
// `TILE_ROWS` and `LANES` are template parameters so the accumulators live in registers and the
// tree unrolls; `k_tile == 0` is the unstaged member of the family, which reads `x` straight from
// global and takes no barrier at all.
template <uint32_t TILE_ROWS, uint32_t LANES>
__device__ __forceinline__ void contract_accumulate(
    const int64_t *lo, const int64_t *hi, uint32_t rows, uint32_t inner,
    const int64_t *map, uint32_t out_width,
    uint32_t k_begin, uint32_t k_end, uint32_t k_tile,
    uint32_t t0, uint32_t o, uint32_t admitted_node_octaves, uint32_t tree,
    wide (&acc_lo)[TILE_ROWS], wide (&acc_hi)[TILE_ROWS], uint32_t *slot
) {
    extern __shared__ unsigned char tiled_shared_raw[];
    int64_t *sx_lo = (int64_t *)tiled_shared_raw;
    int64_t *sx_hi = sx_lo + (size_t)TILE_ROWS * (size_t)(k_tile == 0u ? 1u : k_tile);
    const uint32_t lane = threadIdx.x % LANES;

    #pragma unroll
    for (uint32_t r = 0; r < TILE_ROWS; ++r) { acc_lo[r] = 0; acc_hi[r] = 0; }

    if (k_tile == 0u) {
        // (b) unstaged: each lane walks its own stride-LANES slice of `[k_begin, k_end)` and reads
        //     both operands straight from global. Consecutive lanes read consecutive `i`.
        if (o < out_width) {
            const int64_t *w = map + (size_t)o * (size_t)inner;
            for (uint32_t c = k_begin + lane; c < k_end; c += LANES) {
                const wide wv = (wide)w[c];
                #pragma unroll
                for (uint32_t r = 0; r < TILE_ROWS; ++r) {
                    if (t0 + r < rows) {
                        const wide xl = (wide)lo[(size_t)(t0 + r) * (size_t)inner + c];
                        const wide xh = (wide)hi[(size_t)(t0 + r) * (size_t)inner + c];
                        if (wv >= 0) { acc_lo[r] += wv * xl; acc_hi[r] += wv * xh; }
                        else         { acc_lo[r] += wv * xh; acc_hi[r] += wv * xl; }
                    }
                }
            }
        }
    } else {
        for (uint32_t base = k_begin; base < k_end; base += k_tile) {
            const uint32_t take = (k_end - base) < k_tile ? (k_end - base) : k_tile;
            // (a) the block's lanes cooperatively stage the `x` K-tile for its TILE_ROWS rows.
            //     Consecutive lanes read consecutive `i`, so both `lo[]` and `hi[]` coalesce.
            for (uint32_t u = threadIdx.x; u < TILE_ROWS * take; u += blockDim.x) {
                const uint32_t r = u / take, c = u % take;
                const int inside = (t0 + r) < rows;
                sx_lo[(size_t)r * (size_t)k_tile + c] = inside ? lo[(size_t)(t0 + r) * (size_t)inner + base + c] : (int64_t)0;
                sx_hi[(size_t)r * (size_t)k_tile + c] = inside ? hi[(size_t)(t0 + r) * (size_t)inner + base + c] : (int64_t)0;
            }
            __syncthreads();
            // (b) the map row is contiguous along `i` and is read once per group, reused TILE_ROWS
            //     times in registers, so the map is never staged.
            if (o < out_width) {
                const int64_t *w = map + (size_t)o * (size_t)inner + base;
                for (uint32_t c = lane; c < take; c += LANES) {
                    const wide wv = (wide)w[c];
                    #pragma unroll
                    for (uint32_t r = 0; r < TILE_ROWS; ++r) {
                        const wide xl = (wide)sx_lo[(size_t)r * (size_t)k_tile + c];
                        const wide xh = (wide)sx_hi[(size_t)r * (size_t)k_tile + c];
                        if (wv >= 0) { acc_lo[r] += wv * xl; acc_hi[r] += wv * xh; }
                        else         { acc_lo[r] += wv * xh; acc_hi[r] += wv * xl; }
                    }
                }
            }
            __syncthreads();   // before the next tile overwrites the staged x
        }
    }

    // (c) THE FIXED TREE over the LANES lanes of one output group, `log2(LANES)` levels.
    if (tree == 0u) {
        #pragma unroll
        for (uint32_t half = LANES >> 1; half > 0u; half >>= 1) {
            #pragma unroll
            for (uint32_t r = 0; r < TILE_ROWS; ++r) {
                acc_lo[r] += shfl_down_wide(0xffffffffu, acc_lo[r], half, (int)LANES);
                acc_hi[r] += shfl_down_wide(0xffffffffu, acc_hi[r], half, (int)LANES);
            }
            if (lane < half) {
                #pragma unroll
                for (uint32_t r = 0; r < TILE_ROWS; ++r) node_aperture(acc_lo[r], acc_hi[r], admitted_node_octaves, slot);
            }
        }
    } else {
        #pragma unroll
        for (uint32_t half = 1u; half < LANES; half <<= 1) {
            #pragma unroll
            for (uint32_t r = 0; r < TILE_ROWS; ++r) {
                acc_lo[r] += shfl_down_wide(0xffffffffu, acc_lo[r], half, (int)LANES);
                acc_hi[r] += shfl_down_wide(0xffffffffu, acc_hi[r], half, (int)LANES);
            }
            if ((lane % (2u * half)) == 0u) {
                #pragma unroll
                for (uint32_t r = 0; r < TILE_ROWS; ++r) node_aperture(acc_lo[r], acc_hi[r], admitted_node_octaves, slot);
            }
        }
    }
}

// The K-complete realization: one block owns a disjoint output tile and the whole inner extent.
template <uint32_t TILE_ROWS, uint32_t LANES>
__device__ __forceinline__ void section_contract_tiled_body(
    const int64_t *lo, const int64_t *hi, uint32_t rows, uint32_t inner,
    const int64_t *map, int32_t map_e, uint32_t out_width, int32_t grain,
    int64_t *out_lo, int64_t *out_hi,
    uint32_t outs_per_block, uint32_t k_tile, uint32_t admitted_node_octaves, uint32_t tree,
    uint32_t *slot, const uint32_t *census, const uint32_t *lineage, uint32_t lineage_count
) {
    __shared__ int32_t stop;
    if (threadIdx.x == 0) stop = upstream_refused(census, lineage, lineage_count, slot) ? 1 : 0;
    __syncthreads();
    if (stop) return;

    const uint32_t tiles_o = (out_width + outs_per_block - 1u) / outs_per_block;
    const uint32_t o_tile = blockIdx.x % tiles_o;
    const uint32_t t_tile = blockIdx.x / tiles_o;
    const uint32_t o0 = o_tile * outs_per_block;
    const uint32_t t0 = t_tile * TILE_ROWS;
    const uint32_t group = threadIdx.x / LANES;
    const uint32_t lane = threadIdx.x % LANES;
    const uint32_t o = o0 + group;

    wide acc_lo[TILE_ROWS], acc_hi[TILE_ROWS];
    contract_accumulate<TILE_ROWS, LANES>(lo, hi, rows, inner, map, out_width, 0u, inner, k_tile,
                                          t0, o, admitted_node_octaves, tree, acc_lo, acc_hi, slot);

    // (d) THE ONE OUTWARD ROUNDING. The products sit at 2^(map_e - F) and the grain wants 2^-F, so
    //     the shift is by map_e — once per endpoint per output coordinate, and nowhere else.
    if (lane == 0u && o < out_width) {
        #pragma unroll
        for (uint32_t r = 0; r < TILE_ROWS; ++r) {
            if (t0 + r < rows) {
                const size_t at = (size_t)(t0 + r) * (size_t)out_width + o;
                out_lo[at] = to_word(shift_floor(acc_lo[r], map_e, slot), slot);
                out_hi[at] = to_word(shift_ceil(acc_hi[r], map_e, slot), slot);
            }
        }
    }
    (void)grain;
}

// The split-K partial. Its store is EXACT and 128 bits wide: rounding a partial would put `splits`
// roundings on a path the law admits one on. `a = blockIdx.x / (tiles_o * tiles_t)` is the K
// partition index and `[k0, k1)` its half-open slice — contiguous, so the junction's partial
// regions are coordinate regions and the reduction owner can certify them.
template <uint32_t TILE_ROWS, uint32_t LANES>
__device__ __forceinline__ void section_contract_partial_body(
    const int64_t *lo, const int64_t *hi, uint32_t rows, uint32_t inner,
    const int64_t *map, uint32_t out_width, int64_t *partial,
    uint32_t splits, uint32_t outs_per_block, uint32_t k_tile, uint32_t admitted_node_octaves, uint32_t tree,
    uint32_t *slot, const uint32_t *census, const uint32_t *lineage, uint32_t lineage_count
) {
    __shared__ int32_t stop;
    if (threadIdx.x == 0) stop = upstream_refused(census, lineage, lineage_count, slot) ? 1 : 0;
    __syncthreads();
    if (stop) return;

    const uint32_t tiles_o = (out_width + outs_per_block - 1u) / outs_per_block;
    const uint32_t tiles_t = (rows + TILE_ROWS - 1u) / TILE_ROWS;
    const uint32_t o_tile = blockIdx.x % tiles_o;
    const uint32_t t_tile = (blockIdx.x / tiles_o) % tiles_t;
    const uint32_t a = (blockIdx.x / tiles_o) / tiles_t;
    const uint32_t span = (inner + splits - 1u) / splits;
    const uint32_t k0 = a * span;
    const uint32_t k1 = (k0 + span) < inner ? (k0 + span) : inner;
    const uint32_t o0 = o_tile * outs_per_block;
    const uint32_t t0 = t_tile * TILE_ROWS;
    const uint32_t group = threadIdx.x / LANES;
    const uint32_t lane = threadIdx.x % LANES;
    const uint32_t o = o0 + group;

    wide acc_lo[TILE_ROWS], acc_hi[TILE_ROWS];
    contract_accumulate<TILE_ROWS, LANES>(lo, hi, rows, inner, map, out_width, k0, k1, k_tile,
                                          t0, o, admitted_node_octaves, tree, acc_lo, acc_hi, slot);

    if (lane == 0u && o < out_width) {
        #pragma unroll
        for (uint32_t r = 0; r < TILE_ROWS; ++r) {
            if (t0 + r < rows) {
                const size_t p = (((size_t)a * (size_t)rows) + (size_t)(t0 + r)) * (size_t)out_width + o;
                partial[4 * p + 0] = (int64_t)(uint64_t)((uwide)acc_lo[r]);
                partial[4 * p + 1] = (int64_t)(uint64_t)((uwide)acc_lo[r] >> 64);
                partial[4 * p + 2] = (int64_t)(uint64_t)((uwide)acc_hi[r]);
                partial[4 * p + 3] = (int64_t)(uint64_t)((uwide)acc_hi[r] >> 64);
            }
        }
    }
}

// One thread per output coordinate. The tree over the `splits` partials is FIXED: a balanced binary
// fold in ASCENDING partition index, realized as a rank stack, so the intermediate population is
// `log2(splits) + 1` and never `splits`. `tree == 1` relabels the leaves `j -> splits-1-j`, which is
// the reversed control the reduction owner's `ReductionWord::reversed` names. Then, and only then,
// THE ONE OUTWARD ROUNDING.
extern "C" __global__ void section_contract_join(
    const int64_t *partial, uint32_t splits, uint32_t rows, uint32_t out_width,
    int32_t map_e, int32_t grain, uint32_t admitted_node_octaves, uint32_t tree,
    int64_t *out_lo, int64_t *out_hi,
    uint32_t *slot, const uint32_t *census, const uint32_t *lineage, uint32_t lineage_count
) {
    const uint32_t at = blockIdx.x * blockDim.x + threadIdx.x;
    if (at >= rows * out_width) return;
    if (upstream_refused(census, lineage, lineage_count, slot)) return;
    const uint32_t t = at / out_width, o = at % out_width;

    wide st_lo[6], st_hi[6];
    uint32_t st_rank[6];
    int top = 0;
    for (uint32_t j = 0; j < splits; ++j) {
        const uint32_t a = (tree == 0u) ? j : (splits - 1u - j);
        const size_t p = (((size_t)a * (size_t)rows) + (size_t)t) * (size_t)out_width + o;
        wide vl = (wide)((((uwide)(uint64_t)partial[4 * p + 1]) << 64) | (uwide)(uint64_t)partial[4 * p + 0]);
        wide vh = (wide)((((uwide)(uint64_t)partial[4 * p + 3]) << 64) | (uwide)(uint64_t)partial[4 * p + 2]);
        uint32_t rank = 0;
        while (top > 0 && st_rank[top - 1] == rank) {
            top -= 1;
            vl = st_lo[top] + vl;
            vh = st_hi[top] + vh;
            rank += 1;
            node_aperture(vl, vh, admitted_node_octaves, slot);
        }
        st_lo[top] = vl; st_hi[top] = vh; st_rank[top] = rank; top += 1;
    }
    // `splits` is a power of two by declaration, so the stack folds to exactly one node.
    wide fold_lo = st_lo[0], fold_hi = st_hi[0];
    for (int j = 1; j < top; ++j) {
        fold_lo = fold_lo + st_lo[j];
        fold_hi = fold_hi + st_hi[j];
        node_aperture(fold_lo, fold_hi, admitted_node_octaves, slot);
    }
    out_lo[at] = to_word(shift_floor(fold_lo, map_e, slot), slot);
    out_hi[at] = to_word(shift_ceil(fold_hi, map_e, slot), slot);
    (void)grain;
}

// The emitted family: one unmangled `extern "C"` entry per retained candidate, because a template
// cannot carry C linkage and `cuModuleGetFunction` resolves by an unmangled symbol. Every wrapper
// is named in the module's KERNELS list, so the module-wide block derivation inspects every
// instantiation rather than one; `__launch_bounds__(512)` keeps each instantiation's admitted block
// at the module's present minimum, so no other kernel's geometry moves.
#define EMIT_TILED(NAME, TILE_ROWS, LANES)                                                          \
    extern "C" __global__ void __launch_bounds__(512) NAME(                                         \
        const int64_t *lo, const int64_t *hi, uint32_t rows, uint32_t inner,                        \
        const int64_t *map, int32_t map_e, uint32_t out_width, int32_t grain,                       \
        int64_t *out_lo, int64_t *out_hi,                                                           \
        uint32_t outs_per_block, uint32_t k_tile, uint32_t admitted_node_octaves, uint32_t tree,    \
        uint32_t *slot, const uint32_t *census, const uint32_t *lineage, uint32_t lineage_count) {  \
        section_contract_tiled_body<TILE_ROWS, LANES>(                                              \
            lo, hi, rows, inner, map, map_e, out_width, grain, out_lo, out_hi,                      \
            outs_per_block, k_tile, admitted_node_octaves, tree, slot, census, lineage, lineage_count); \
    }

#define EMIT_PARTIAL(NAME, TILE_ROWS, LANES)                                                        \
    extern "C" __global__ void __launch_bounds__(512) NAME(                                         \
        const int64_t *lo, const int64_t *hi, uint32_t rows, uint32_t inner,                        \
        const int64_t *map, uint32_t out_width, int64_t *partial,                                   \
        uint32_t splits, uint32_t outs_per_block, uint32_t k_tile, uint32_t admitted_node_octaves,  \
        uint32_t tree,                                                                              \
        uint32_t *slot, const uint32_t *census, const uint32_t *lineage, uint32_t lineage_count) {  \
        section_contract_partial_body<TILE_ROWS, LANES>(                                            \
            lo, hi, rows, inner, map, out_width, partial, splits, outs_per_block, k_tile,           \
            admitted_node_octaves, tree, slot, census, lineage, lineage_count);                     \
    }

EMIT_TILED  (section_contract_tiled_r1_l32,   1u, 32u)
EMIT_TILED  (section_contract_tiled_r2_l32,   2u, 32u)
EMIT_TILED  (section_contract_tiled_r4_l32,   4u, 32u)
EMIT_TILED  (section_contract_tiled_r1_l16,   1u, 16u)
EMIT_TILED  (section_contract_tiled_r4_l16,   4u, 16u)
EMIT_TILED  (section_contract_tiled_r1_l8,    1u,  8u)
EMIT_PARTIAL(section_contract_partial_r1_l32, 1u, 32u)
EMIT_PARTIAL(section_contract_partial_r4_l32, 4u, 32u)

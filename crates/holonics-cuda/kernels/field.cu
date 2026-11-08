// The field's card realization (`holonics::hnn::tower::field`, records
// `2026-11-01_THE_PROBLEM_IS_ONE_FIELD_EVERY_SITE_READS_EVERY_OTHER_AND_THE_ANSWER_IS_REFINED_NOT_SPOKEN`,
// §7, and `2026-11-01_THE_FIELD_DISPERSES_A_SITE_MEETS_ITS_RESONANCE_CLASS_AT_ITS_FALLOFF_AND_THE_ANSWER_LOCKS_UNDER_THE_PUMP`,
// §6, §12 and §14): one constitution iterated over every site of every region of a batch at once, and
// its exact reverse, bit for bit the host's `Field::pass` and `Field::reverse`.
//
// [definition; agent-inferred, November 1] **The field disperses; only the plates radiate far.** Each
// head reads a key and a probe a site (§16.19: each its own chart, founded apart); a site meets its near
// field (`0 < |i - j| < NEAR`) and the definite sites whose key's class its probe reads (the shells; definite
// is known or locked, §14.1), each at the octave falloff `floor(log2 |i - j|)` bits, and a far source
// held by both ends (§14.2) at the product of their holds. Past the near field it also hears every
// definite source through its octave's crowd (§14.10). The classes are listed by one stable counting
// sort a head and region (`field_classes`), definite members first, and every contact kernel visits
// only the support. The shares and the contact's return keep the dense address `[i][j]` of the region's
// block, written and read only on the support, so a column's reads find `p_ij` without an index.
//
// [definition; agent-inferred, November 1] **The row is a series** (§14.11). A contact row is read in
// two passes over its terms (the least exponent `a_0`; then each term `face * mult * 2^(a - a_0)` summed
// whole into the mass and, times each value entry, into the numerators), in a carrier of
// `FieldDeclaration::row_bits()` bits (`LIMBS` limbs of 64, signed by two's complement), divided once
// by the mass (the exact long division, to the nearest numerator), and each term's share of the mass
// formed once by the same division on `2^-63`. Integer sums: the host's bits in any order, whatever
// the partition of the support over the warp's lanes.
//
// [definition; agent-inferred, November 1] The launch follows regions x sites x heads, never a padded
// window: a site is its global index in the batch (`site_region`, `site_pos`), a contact row is a head
// and a site, and a region's pairs are its own block of the share store (`region_eoff`). Every
// product's remainder below its grain is released to the nearest numerator (`rel`) and every sum is an
// integer sum, so a row read by 32 lanes, a covector summed over sites or a sum over regions gives the
// host's bits whatever the order.

#include <stdint.h>

typedef __int128 wide;
typedef unsigned __int128 uwide;

#define FACE_BITS 16
#define MATERIAL_BITS 24
#define MOVE_BITS 30
#define COVECTOR_BITS 24
#define UNIT_BITS 62
#define CARRIED_BITS 70
#define CONTACT_BACK 32
// The contact's covector grain, `δz` on `2^(−40)` (the host's `CONTACT_BITS`).
#define CONTACT_BITS 40
// A hold's face on `2^(−40)` (the host's `HOLD_BITS`, §14.2) and a term's share of its row's mass on
// `2^(−63)` (the host's `SHARE_BITS`, §14.11).
#define HOLD_BITS 40
#define SHARE_BITS 63
// The most crowds a receiver hears (two an octave, `2 (⌈log₂ reach⌉ − 1)` at most), kept in one warp.
#define MAX_CROWD_SLOTS 32

// The near field, `lcm(2, 3)` (the host's `NEAR`): a site meets the sites closer than it whatever
// their classes, the `2(NEAR − 1)` nearest a site's first support entries.
#define NEAR 6
#define NEAR_SLOTS (2 * (NEAR - 1))

#define REFUSED_CARRIER 1u
#define REFUSED_WORD64 2u
#define REFUSED_WORD32 4u
#define REFUSED_SHIFT 8u
// The moments' shape (`MOMENT_REFUSED_SHAPE`, 16u) is the next bit; a contact's key return past its carrier:
#define REFUSED_KEY 32u
// A temperature past its carrier in its chart (§16.12: `⌈log₂ T⌉ ≤ 7`, `T ≥ 2^(−23)`).
#define REFUSED_TEMPER 64u
// The temperature's carrier and `ln 2`'s grain (`TEMPER_TOP`, `LN2_FACE_BITS` in `field.rs`).
#define TEMPER_TOP 7
#define LN2_FACE_BITS 30

// -------------------------------------------------------------------------------------------
// the host's integer law
//
// [agent-inferred, November 1] The field's image restates the release, the nearest quotient, the
// carriers' refusals, the root and the exponential's face that `tower.cu` carries, so the tower's
// image, read to parity on its own declarations, is left as it was; both are the host's law (`release`,
// `div_nearest`, `fit64`, `fit32`, `u128::isqrt`, `Exponential::below_one` through its resident face), and each image's parity
// against the host reads that equality.

// `x` released `bits` coarser, to the nearest numerator, half away from zero (`release`).
__device__ __forceinline__ wide rel(wide x, unsigned bits) {
    if (bits == 0) {
        return x;
    }
    const wide half = (wide)1 << (bits - 1);
    return x >= 0 ? (x + half) >> bits : -((-x + half) >> bits);
}

// `x / k` to the nearest integer, half away from zero, `k > 0` (`div_nearest`).
__device__ __forceinline__ wide div_nearest(wide x, wide k) {
    const wide n = (x >= 0 ? x : -x) + k / 2;
    if (n <= (wide)INT64_MAX && k <= (wide)INT64_MAX) {
        const wide q = (wide)((uint64_t)n / (uint64_t)k);
        return x >= 0 ? q : -q;
    }
    return x >= 0 ? n / k : -(n / k);
}

// [agent-inferred, November 1] **An exact quotient by an invariant divisor.** A contact row's
// return divides one product a pair by the row's mass; a 128-bit division is a long software routine
// on the card, so the divisor is read once a row as its normalized form `d = k 2^s` and reciprocal
// `v = ⌊(2^128 − 1)/d⌋ − 2^64` (Möller and Granlund, "Improved division by invariant integers",
// 2011, Algorithm 4), and each division is two of its steps: the quotient is the integer `⌊n/k⌋`,
// whatever the route, so the bits are `div_nearest`'s.
struct Divisor {
    uint64_t k, d, v;
    uint32_t s;
};

__device__ __forceinline__ Divisor divisor_of(uint64_t k) {
    Divisor q;
    q.k = k;
    q.s = (uint32_t)__clzll((long long)k);
    q.d = k << q.s;
    // ⌊(2^128 − 1)/d⌋ − 2^64 = ⌊((2^64 − 1 − d) 2^64 + 2^64 − 1)/d⌋, below 2^64 since d ≥ 2^63.
    q.v = (uint64_t)((((uwide)(~q.d)) << 64 | (uwide)UINT64_MAX) / (uwide)q.d);
    return q;
}

// `⌊(u1 2^64 + u0)/d⌋` and its remainder, `u1 < d`, `d` normalized (Algorithm 4).
__device__ __forceinline__ uint64_t divide_word(uint64_t u1, uint64_t u0, const Divisor &q, uint64_t *rem) {
    const uwide p = (uwide)q.v * (uwide)u1 + (((uwide)u1 << 64) | (uwide)u0);
    uint64_t q1 = (uint64_t)(p >> 64) + 1;
    const uint64_t q0 = (uint64_t)p;
    uint64_t r = u0 - q1 * q.d;
    if (r > q0) {
        q1 -= 1;
        r += q.d;
    }
    if (r >= q.d) {
        q1 += 1;
        r -= q.d;
    }
    *rem = r;
    return q1;
}

// `⌊n/k⌋` for a 128-bit `n`.
__device__ __forceinline__ uwide divide_by(uwide n, const Divisor &q) {
    const uint64_t nh = (uint64_t)(n >> 64), nl = (uint64_t)n;
    uint64_t n2 = 0, n1 = nh, n0 = nl;
    if (q.s != 0) {
        n2 = nh >> (64 - q.s);
        n1 = (nh << q.s) | (nl >> (64 - q.s));
        n0 = nl << q.s;
    }
    uint64_t r;
    const uint64_t qh = divide_word(n2, n1, q, &r);
    const uint64_t ql = divide_word(r, n0, q, &r);
    return ((uwide)qh << 64) | (uwide)ql;
}

// `div_nearest(x, k)` by a read divisor.
__device__ __forceinline__ wide div_nearest_by(wide x, const Divisor &q) {
    const uwide n = (uwide)(x >= 0 ? x : -x) + (uwide)(q.k / 2);
    const wide quotient = (wide)divide_by(n, q);
    return x >= 0 ? quotient : -quotient;
}

// The ring sum's atomic step on `Z/2^128` (the host's wrapping `i128` sum): the low word added
// atomically, and the high word with the low word's carry, so any order of additions leaves the same
// 128 bits.
__device__ __forceinline__ void add_wide(wide *at, wide v) {
    unsigned long long *word = (unsigned long long *)at;
    const unsigned long long lo = (unsigned long long)(uint64_t)v;
    const unsigned long long hi = (unsigned long long)(uint64_t)((uwide)v >> 64);
    const unsigned long long old = atomicAdd(word, lo);
    atomicAdd(word + 1, hi + (old + lo < old ? 1ull : 0ull));
}

__device__ __forceinline__ int64_t fit64(wide v, uint32_t *st) {
    if (v > (wide)INT64_MAX || v < (wide)INT64_MIN) {
        atomicOr(st, REFUSED_WORD64);
        return 0;
    }
    return (int64_t)v;
}

__device__ __forceinline__ int32_t fit32(wide v, uint32_t *st) {
    if (v > (wide)INT32_MAX || v < (wide)INT32_MIN) {
        atomicOr(st, REFUSED_WORD32);
        return 0;
    }
    return (int32_t)v;
}

__device__ __forceinline__ uint64_t mag64(int64_t v) {
    return v < 0 ? (uint64_t)0 - (uint64_t)v : (uint64_t)v;
}

__device__ uwide isqrt128(uwide n) {
    uwide res = 0;
    uwide bit = (uwide)1 << 126;
    while (bit > n) {
        bit >>= 2;
    }
    while (bit != 0) {
        if (n >= res + bit) {
            n -= res + bit;
            res = (res >> 1) + bit;
        } else {
            res >>= 1;
        }
        bit >>= 2;
    }
    return res;
}

// `below_one` read through the exponential's resident face (`field_exponential`): the same split into
// whole and fraction, the same shift.
__device__ __forceinline__ uint64_t below_one_face(wide x, const uint64_t *face, uint32_t digits) {
    const wide m = -x;
    const wide whole = m >> digits;
    const uint64_t frac = (uint64_t)(m & (((wide)1 << digits) - 1));
    const wide shift = frac == 0 ? whole : whole + 1;
    const uint64_t rest = frac == 0 ? 0 : ((uint64_t)1 << digits) - frac;
    const uint64_t value = face[rest];
    const uint64_t shifted = shift >= 64 ? 0 : value >> (uint32_t)shift;
    return shifted == 0 ? 1 : shifted;
}

// The binary length of a magnitude (`0` for zero).
__device__ __forceinline__ uint32_t bit_length(uint64_t m) {
    return m == 0 ? 0 : 64 - __clzll((long long)m);
}

// `⌈log₂ x⌉` (`0` for `x ≤ 1`).
__device__ __forceinline__ uint32_t ceil_log2(uint64_t x) {
    return x <= 1 ? 0 : 64 - __clzll((long long)(x - 1));
}

__device__ __forceinline__ uwide shfl_wide(uwide v, int o) {
    const uint64_t lo = __shfl_xor_sync(0xffffffffu, (uint64_t)v, o);
    const uint64_t hi = __shfl_xor_sync(0xffffffffu, (uint64_t)(v >> 64), o);
    return ((uwide)hi << 64) | lo;
}

// The warp's ring sum (`Z/2^128`, the host's wrapping `i128` sum); every lane holds it.
__device__ __forceinline__ wide warp_sum(wide v) {
    uwide u = (uwide)v;
    for (int o = 16; o > 0; o >>= 1) {
        u += shfl_wide(u, o);
    }
    return (wide)u;
}

__device__ __forceinline__ uint64_t warp_sum_u64(uint64_t v) {
    for (int o = 16; o > 0; o >>= 1) {
        v += __shfl_xor_sync(0xffffffffu, v, o);
    }
    return v;
}

__device__ __forceinline__ int64_t warp_max_signed(int64_t v) {
    uint64_t key = (uint64_t)v ^ ((uint64_t)1 << 63);
    for (int o = 16; o > 0; o >>= 1) {
        const uint64_t w = __shfl_xor_sync(0xffffffffu, key, o);
        key = w > key ? w : key;
    }
    return (int64_t)(key ^ ((uint64_t)1 << 63));
}

__device__ __forceinline__ uint64_t warp_max_u64(uint64_t v) {
    for (int o = 16; o > 0; o >>= 1) {
        const uint64_t w = __shfl_xor_sync(0xffffffffu, v, o);
        v = w > v ? w : v;
    }
    return v;
}

// -------------------------------------------------------------------------------------------
// the batch

// The batch's declaration, material, rings, regions and the tick's carriers. Every entry takes it by
// value; a tick's launches set its carriers.
struct FieldWords {
    uint32_t D, H, n, still, f, A, frames;
    // The lanes the face is charted in (§16.40), `D / lanes` coordinates each.
    uint32_t lanes;
    // The gain's shift, negative where it amplifies (`FieldDeclaration::score_shift`), the classes'
    // shells `b` (`class_trits`) and their count `3^b`.
    int32_t beta;
    uint32_t ctrits, nclasses;
    // The contact covector's carrier: `|δs| < 2^dsbits` (`FieldDeclaration::contact_return_bits`).
    uint32_t dsbits;
    uint32_t M, M2, span, digits;
    uint32_t T, R;
    // The crowds' slots a receiver keeps (`2 (levels − 1)` for the reach).
    uint32_t slots, band;
    // A receiver's stride of probed classes (`2^b`, or `2^n` under the width law) and the padding before the next 8-byte field.
    uint32_t pstride, pad_;
    uint64_t E;
    // `ln 2` on `2^(−30)`, the weights' return reads it (two words of a signed 128-bit value).
    uint64_t ln2_lo, ln2_hi;
    const int32_t *theta;
    uint64_t enc, enc_before, enc_after, q, q_bias, v, v_bias, out, out_bias, a, a_bias, b, b_bias, w, w_bias, read, read_bias;
    uint64_t rq, rv, rout, ra, rb, rw, rread;
    const int64_t *phasor;
    const uint64_t *ring_off;
    const uint64_t *ring_n;
    // Each turned slot's skin decay on `2^(−30)` at every distance within the reach, `[slot][d]`
    // with stride `dreach` (`Field::decays`).
    const int64_t *decay;
    uint64_t dreach;
    const uint64_t *roots;
    const uint32_t *site_region;
    const uint32_t *site_pos;
    const uint32_t *region_off;
    const uint64_t *region_eoff;
    const uint32_t *classes;
    const uint8_t *unresolved;
    // A definite site: known (resolved and carrying no mixture) or locked (a foil, §14.1).
    const uint8_t *definite;
    // [E] Each site's row computed (the host's `Region::window`); null where no region of the batch cuts its room.
    const uint8_t *computed;
    // Each site whose blank face a clock reads (the host's `pass`); the blank clock's face kernels read it as the open sites.
    const uint8_t *blank_read;
    // The carried mixtures: site `t`'s shares are `mix_class`, `mix_share` over `mix_off[t]..mix_off[t + 1]`
    // (none where the site is not carried).
    const uint32_t *mix_off;
    const uint32_t *mix_class;
    const uint32_t *mix_share;
    uint32_t *status;
    // The site pairs the contact met (`Σ |S_i^h|` over every row and tick).
    unsigned long long *met;
    // The tick's carriers the frame, the contact and the pair contact read and write (the charts'
    // reads and scales are passed to their own launches).
    int64_t *x;
    int64_t *qkv;
    int64_t *qf, *vf;
    // The tick's classes `[h][t]`, each region's class offsets `[h][r][2·3^b + 1]` (relative to its
    // members; class `c`'s definite members at `2c`, its others at `2c + 1`) and its members `[h][t]`
    // (places within the region, ascending within each).
    uint32_t *cls;
    uint32_t *class_off;
    uint32_t *members;
    // Each definite receiver's probed classes (§15.2's multi-probe, §16.19): their number `pn[h][t]` and the
    // classes `pcls[h][t][2^b]`, its probe's own class first, and the receivers that probe each class: offsets
    // `poff[h][r][3^b + 1]` and members `pmem[h][t]` (places within the region, in the atomic's order).
    uint32_t *pn;
    uint32_t *pcls;
    uint32_t *poff;
    uint32_t *pmem;
    // The dense shares `p_ij` on `2^(−63)` (the support's entries only); while a row is read, its score.
    // `e_prev` is the previous tick's (the echo's round trip, §15.3).
    uint64_t *e;
    const uint64_t *e_prev;
    int64_t *y;
    int64_t *pa, *pb, *pc;
    // The tick's magnitude (the binary length of the largest unit word, `bits[0]`) and the
    // exponential's resident face.
    uint32_t *bits;
    const uint64_t *face;
    // The row's least whole bit `[h][t]` (read by the exposure), each head's prefix sums of the definite
    // sites' unit words and values `[h][row][span]` and their counts `[h][row]` (`row = region_off[r] +
    // r + t`, a region's `S + 1` rows, §14.10), and each receiver's crowd shares `[h][t][slots]`.
    int64_t *amin;
    wide *sw, *sv;
    uint64_t *sc;
    uint64_t *ce;
    // The reverse's scratch: the crowds' difference arrays over the places `[row][span]`.
    wide *cv, *cw;
    // The site moments `[t][2M]` (§15.1), each site's echo `B` and its logits (§15.3) and the round trips
    // `Σ_j p_ij^(t+1) p_ji^(t)` a site (`[t]`, 128 bits).
    int64_t *moment;
    const uint8_t *echo_has;
    const uint64_t *echo_b;
    const int64_t *echo_logits;
    wide *trips;
    // The unit words on 32 bits `[h][t][span]` (what `field_unit` fits them to), and the skins `[h][d][n]` on
    // 32 bits (`D ≤ 2^30`; a still head's the exact 1): the exposure reads a source's whole row as four vector
    // loads, and its skins as two.
    int32_t *qf32;
    const uint32_t *decay_t;
    // The reverse's pair covectors `⟨δỹ_i, D ṽ_j⟩` at the region block's dense address (one head's, each head's
    // rows computing them once for both of their passes).
    wide *dpb;
    // A region's definite sites' places and its open ones' (head-independent, ascending), `dlist[dstart[r] ..
    // dstart[r + 1]]` and `olist[ostart[r] .. ostart[r + 1]]` (§15.9: an open receiver hears every definite site, and
    // a definite source is heard by every open one).
    const uint32_t *dlist;
    const uint32_t *dstart;
    const uint32_t *olist;
    const uint32_t *ostart;
    // The locks' temperatures (§15.10): the material's `temper` family (`theta[temper_at + 2 h + kind]` holds `log₂ T`, kind 0 a
    // class receiver, 1 a listener, on `2^(−24)`), the covector buffer the reverse adds their covectors to, and,
    // on a return, the pairs' locks at unit gain `S` (`sb`, at the dense address, a tick's).
    uint64_t temper_at;
    // The temperatures' fine roots (§16.12): the exponential's roots 17 to 24 on `2^(−62)` (`Field::fine_exponential`).
    const uint64_t *fine_roots;
    wide *gcov;
    int64_t *sb;
    // Every receiver's probe (§16.19): its chart of the read `pr` `[t][2M]`, framed and at unit power by head `pq`
    // `[h][t][span]` (and on 32 bits, `pq32`) with its powers `pscale` `[h][t]`; the reverse's covector of it `dp`.
    int64_t *pr;
    int64_t *pq;
    int32_t *pq32;
    wide *pscale;
    int64_t *dp;
    // (the probe chart's family offsets and reach, read by the launches)
    uint64_t probe, probe_bias, rprobe;
    // The turned heads' own clocks (§16, Law 1): the heads that read a pace (`paced`), the pace family's offset in
    // the material, the half turn on `2^(−46)` (two words), each paced head's rate, clock and variation `[p][t]` on
    // `2^(−24)`, whether its pace is plain over each region `[p][r]` (every rate 1: the byte place), and its frames
    // `[p][t][n]` (int64 pairs on `2^(−30)`); the reverse's clock covectors `[p][t]` (`2^24 ∂/∂τ`, `2^24 ∂/∂σ`).
    uint32_t paced;
    uint64_t pace_at;
    uint64_t pi_lo, pi_hi;
    int64_t *kappa;
    int64_t *tau;
    int64_t *sigma;
    uint8_t *plain;
    int64_t *pframe;
    wide *gtau;
    wide *gsig;
    // The crowds' contact covectors `[h][t][slots]` the reverse keeps for the clock's skin return (§16).
    int64_t *cds;
    // [measurement, §16.20] Where set, the contact covector's magnitude by where its pairs lie, `[h][2]`: `Σ |δs|` over
    // the near pairs (`|i − j| < NEAR`) and over the far ones (the far pairs and the crowds), the host's
    // `Field::covector_shares`.
    wide *dsshare;
    // [§16.44] Where set, a tick's blanks' rates `[p][t]` (`field_blank_rates`), which its clocks run each silent open
    // site at, and the face they were read from (masses `[t][A]` and totals), whose shares the clocks' return reads.
    const int64_t *blank_rate;
    const uint64_t *blank_masses;
    const uwide *blank_totals;
    // [measurement] Where set, every silent place runs its own rate past the last arrival too (`Field::per_blank_clock`).
    uint64_t per_blank;
    // The depth rings' count (`FieldDeclaration::depth`): the last `depth` turned ring sets.
    uint64_t depth;
    // [the unified-theory reading of November 6, 10:31] Where set, past the last arrival a silent place runs at the bare rate
    // (`Field::bare_stretch`): no clamp to the stretch's first place, and no fold of its covector there.
    uint64_t bare_stretch;
};

// [definition; agent-inferred, November 2] **A head's pace index** (§16, `Field::paces`): the heads that carry a moment
// (a turned ring set) in order, `−1` for the rest.
__device__ __forceinline__ int32_t paced_index(const FieldWords &w, uint32_t h) {
    const uint32_t set = h % w.frames;
    if (set < w.still) {
        return -1;
    }
    return (int32_t)((h / w.frames) * (w.frames - w.still) + set - w.still);
}

// [definition; agent-inferred, November 6] A depth ring (`FieldDeclaration::is_depth`): a turned ring set among the last
// `depth`, turning by its located increments alone, with no skin and no moment.
__device__ __forceinline__ bool depth_head(const FieldWords &w, uint32_t h) {
    const uint32_t set = h % w.frames;
    return set >= w.still && set + w.depth >= w.frames;
}

// The frame of local mode `l` of head `h` at the batch's site `g`: the identity in a head of a still ring
// set (`h mod frames < still`), the mode's ring in a turned one (slot `l (frames − still) + set − still`)
// at the site's place.
__device__ __forceinline__ void frame_of(const FieldWords &w, uint64_t g, uint32_t h, uint32_t l, wide *ur, wide *ui) {
    const uint32_t set = h % w.frames;
    if (set < w.still) {
        *ur = (wide)1 << MOVE_BITS;
        *ui = 0;
        return;
    }
    // A turned head's frame is its own clock's (§16, Law 1), the byte place where its pace is plain.
    const int32_t p = paced_index(w, h);
    if (p >= 0 && (!w.plain[(uint64_t)p * w.R + w.site_region[g]] || depth_head(w, h))) {
        const uint64_t at = ((uint64_t)p * w.T + g) * w.n + l;
        *ur = w.pframe[2 * at];
        *ui = w.pframe[2 * at + 1];
        return;
    }
    const uint32_t place = w.site_pos[g];
    const uint32_t slot = l * (w.frames - w.still) + set - w.still;
    const uint64_t at = w.ring_off[slot] + place % w.ring_n[slot];
    *ur = w.phasor[2 * at];
    *ui = w.phasor[2 * at + 1];
}

// [definition; agent-inferred, November 1] **The skin decay of local mode `l` of head `h` across `d`
// sites** (`Field::decay`): `e^(−2π d/n)` on `2^(−30)` in a turned head; a still head's is the exact
// `1`, read by the callers as no decay at all.
__device__ __forceinline__ wide decay_of(const FieldWords &w, uint32_t h, uint32_t l, uint32_t d) {
    const uint32_t set = h % w.frames;
    return w.decay[(uint64_t)(l * (w.frames - w.still) + set - w.still) * w.dreach + d];
}

// A known site: resolved and carrying no mixture (its class arrived). The closure's holders are the
// known sites of a receiver's alphabet class (`holds`).
__device__ __forceinline__ bool known_site(const FieldWords &w, uint64_t g) {
    return w.unresolved[g] == 0 && w.mix_off[g] == w.mix_off[g + 1];
}

// A definite site (§14.1): known, or locked (a foil). Only definite sources are heard past the near
// field, and each class lists its definite members first.
// [E] A receiver outside every window of a cut room meets no source: its row is not met, its current is zero and it returns
// nothing (the host's `Field::tick`).
__device__ __forceinline__ bool skipped_row(const FieldWords &w, uint64_t g) {
    return w.computed != nullptr && w.computed[g] == 0;
}

__device__ __forceinline__ bool definite_site(const FieldWords &w, uint64_t g) {
    return w.definite[g] != 0;
}

// A head of a still ring set (its modes unframed): carrying no skin (`Field::decay` is `(1, 0)`).
__device__ __forceinline__ bool still_head(const FieldWords &w, uint32_t h) {
    return h % w.frames < w.still;
}


// A head carrying no skin (`Field::decay` is `(1, 0)`): a still ring set's, or a depth ring's.
__device__ __forceinline__ bool skinless(const FieldWords &w, uint32_t h) {
    return still_head(w, h) || depth_head(w, h);
}

// A value carried across a pair by its skin decay: `release(D v, 30)` in a turned head, `v` in a still
// one (`decayed`).
__device__ __forceinline__ wide carried(const FieldWords &w, uint32_t h, uint32_t l, uint32_t d, int64_t v) {
    return skinless(w, h) ? (wide)v : rel(decay_of(w, h, l, d) * (wide)v, MOVE_BITS);
}

// The skin decay itself, `D` on `2^(−30)`: the exact `1` of a still head.
__device__ __forceinline__ wide decay_raw(const FieldWords &w, uint32_t h, uint32_t l, uint32_t d) {
    return skinless(w, h) ? (wide)1 : decay_of(w, h, l, d);
}

// A wide value carried across `d` sites by its skin decay: `release(D v, 30)` in a turned head, `v` in
// a still one (`decayed_wide`).
__device__ __forceinline__ wide carried_wide(const FieldWords &w, uint32_t h, uint32_t l, uint32_t d, wide v) {
    return skinless(w, h) ? v : rel(decay_of(w, h, l, d) * v, MOVE_BITS);
}

// The pace's grain (`PACE_BITS`): a rate, a clock and a variation on `2^(−24)`.
#define PACE_BITS 24

// `e^(a + i b)` on `2^(−30)`, `a`, `b` on `2^(−30)` (the host's `exp_series`): the series summed until its term
// releases to zero at the grain.
__device__ void exp_series_dev(wide a, wide b, wide *re_out, wide *im_out) {
    wide tr = (wide)1 << MOVE_BITS, ti = 0, sr = tr, si = 0, k = 1;
    for (;;) {
        const wide re = rel(tr * a - ti * b, MOVE_BITS);
        const wide im = rel(tr * b + ti * a, MOVE_BITS);
        tr = div_nearest(re, k);
        ti = div_nearest(im, k);
        if (tr == 0 && ti == 0) {
            break;
        }
        sr += tr;
        si += ti;
        k += 1;
    }
    *re_out = sr;
    *im_out = si;
}

// [definition; agent-inferred, November 2] **The turn's face at a clock** `ρ` on `2^(−24)` (the host's
// `turn_phasor`): `e^(2πi ρ/n)`, `ρ` in `(−n/2, n/2]`, its four quarter points exact.
__device__ void turn_phasor_dev(const FieldWords &w, wide rho, uint64_t n, wide *re, wide *im) {
    const wide one = (wide)1 << MOVE_BITS;
    const wide period = (wide)n << PACE_BITS;
    wide r = rho % period;
    if (r < 0) {
        r += period;
    }
    const wide c = 2 * r > period ? r - period : r;
    if (c == 0) {
        *re = one;
        *im = 0;
        return;
    }
    if (2 * c == period) {
        *re = -one;
        *im = 0;
        return;
    }
    if (4 * c == period) {
        *re = 0;
        *im = one;
        return;
    }
    if (4 * c == -period) {
        *re = 0;
        *im = -one;
        return;
    }
    const wide pi = (wide)(((uwide)w.pi_hi << 64) | (uwide)w.pi_lo);
    const wide theta = div_nearest(2 * pi * c, period);
    exp_series_dev(0, rel(theta, 16), re, im);
}

// The face of turned slot `slot` at a clock `ρ` (the host's `Field::turn`): the resident ring at a whole place it
// holds, the series otherwise (the same bits).
__device__ void turn_dev(const FieldWords &w, uint32_t slot, wide rho, wide *re, wide *im) {
    const uint64_t n = w.ring_n[slot];
    const uint64_t resident = n < w.dreach ? n : w.dreach;
    if ((rho & (((wide)1 << PACE_BITS) - 1)) == 0) {
        wide r = (rho >> PACE_BITS) % (wide)n;
        if (r < 0) {
            r += (wide)n;
        }
        if ((uint64_t)r < resident) {
            const uint64_t at = w.ring_off[slot] + (uint64_t)r;
            *re = w.phasor[2 * at];
            *im = w.phasor[2 * at + 1];
            return;
        }
    }
    turn_phasor_dev(w, rho, n, re, im);
}

// [definition; agent-inferred, November 2] **The skin across a variation** `s` on `2^(−24)` of turned slot `slot`
// (the host's `Field::skin`, `skin_of`): the resident decay at a whole distance within the reach, otherwise
// `e^(−2π|s|/n)` read through the exponential's face, `release(below_one(−bits), 32)` with `bits = div_nearest(2π |s|,
// (n ln 2) 2^24)` on `2^(−16)`.
__device__ wide skin_dev(const FieldWords &w, uint32_t slot, wide s) {
    s = s < 0 ? -s : s;
    if ((s & (((wide)1 << PACE_BITS) - 1)) == 0 && (uint64_t)(s >> PACE_BITS) < w.dreach) {
        return (wide)w.decay[(uint64_t)slot * w.dreach + (uint64_t)(s >> PACE_BITS)];
    }
    const wide pi = (wide)(((uwide)w.pi_hi << 64) | (uwide)w.pi_lo);
    const wide ln2 = (wide)(((uwide)w.ln2_hi << 64) | (uwide)w.ln2_lo);
    const wide bits = div_nearest(2 * pi * s, ((wide)w.ring_n[slot] * ln2) << PACE_BITS);
    return rel((wide)below_one_face(-bits, w.face, w.digits), UNIT_BITS - MOVE_BITS);
}

// Whether head `h`'s skins and frames read its own clock over the region of batch site `g` (a paced head whose
// pace is not plain there).
__device__ __forceinline__ bool paced_at(const FieldWords &w, uint32_t h, uint64_t g) {
    const int32_t p = paced_index(w, h);
    return p >= 0 && !w.plain[(uint64_t)p * w.R + w.site_region[g]];
}

// [definition; agent-inferred, November 2] **The skin of local mode `l` of head `h` between batch sites `gi` and `gj`**
// (the host's `pair_decay`): on a paced head its variation's, `e^(−2π |σ_i − σ_j|/n)`; else the byte distance's
// `gap`. A still or clock head is the caller's (`still_head`).
__device__ __forceinline__ wide skin_ij(const FieldWords &w, uint32_t h, uint32_t l, uint64_t gi, uint64_t gj, uint32_t gap) {
    if (paced_at(w, h, gi)) {
        const int32_t p = paced_index(w, h);
        const uint32_t slot = l * (w.frames - w.still) + h % w.frames - w.still;
        return skin_dev(w, slot, (wide)w.sigma[(uint64_t)p * w.T + gi] - (wide)w.sigma[(uint64_t)p * w.T + gj]);
    }
    return decay_of(w, h, l, gap);
}

// The skin itself between two sites, the exact `1` of a still head.
__device__ __forceinline__ wide skin_raw(const FieldWords &w, uint32_t h, uint32_t l, uint64_t gi, uint64_t gj, uint32_t gap) {
    return skinless(w, h) ? (wide)1 : skin_ij(w, h, l, gi, gj, gap);
}

// A value carried across a pair by its skin: `release(D v, 30)` in a turned head, `v` in a still one.
__device__ __forceinline__ wide carried_ij(const FieldWords &w, uint32_t h, uint32_t l, uint64_t gi, uint64_t gj, uint32_t gap, int64_t v) {
    return skinless(w, h) ? (wide)v : rel(skin_ij(w, h, l, gi, gj, gap) * (wide)v, MOVE_BITS);
}

// A wide value carried alike.
__device__ __forceinline__ wide carried_wide_ij(const FieldWords &w, uint32_t h, uint32_t l, uint64_t gi, uint64_t gj, uint32_t gap, wide v) {
    return skinless(w, h) ? v : rel(skin_ij(w, h, l, gi, gj, gap) * v, MOVE_BITS);
}

// The site an octave's crowd is skinned to from receiver `gi` (§16): the place `2^level` away on its side.
__device__ __forceinline__ uint64_t octave_edge(uint64_t gi, uint32_t level, bool right) {
    return right ? gi + ((uint64_t)1 << level) : gi - ((uint64_t)1 << level);
}

// [agent-inferred, November 1] **The exponential's resident face**: `face[rest]` is the product of the
// roots `below_one` multiplies for the binary digits of `rest`, each `rest` of the `2^digits` read by
// the same loop on the card, so a weight read through the face is `below_one`'s bits exactly (a
// navigator's resident face at its declared grain, never a table of answers). It replaces up to
// `digits` dependent 64-bit products a pair by one read of `2^digits` words (512 KiB at 16 digits).
extern "C" __global__ void field_exponential(FieldWords w, uint64_t *face) {
    const uint64_t cells = (uint64_t)1 << w.digits;
    for (uint64_t c = (uint64_t)blockIdx.x * blockDim.x + threadIdx.x; c < cells; c += (uint64_t)gridDim.x * blockDim.x) {
        uint64_t value = (uint64_t)1 << UNIT_BITS;
        for (uint32_t i = 0; i < w.digits; i++) {
            if (c & ((uint64_t)1 << (w.digits - 1 - i))) {
                const uint64_t lo = value * w.roots[i];
                const uint64_t hi = __umul64hi(value, w.roots[i]);
                value = (hi << (64 - UNIT_BITS)) | (lo >> UNIT_BITS);
            }
        }
        face[c] = value;
    }
}

// A site's encoding row: its class, or the unresolved row.
__device__ __forceinline__ uint64_t row_of(const FieldWords &w, uint64_t t) {
    return w.unresolved[t] ? w.A : w.classes[t];
}

// Site `s`'s opening term in the encoding at `base`, entry `i`: its row, or the mixture of its carried
// shares' rows `release(Σ_a w_a E(a), 16)` (`Field::opening_term`).
__device__ __forceinline__ int64_t opening_term(const FieldWords &w, uint64_t base, uint64_t s, uint64_t i) {
    const uint32_t from = w.mix_off[s], to = w.mix_off[s + 1];
    if (from == to) {
        return w.theta[base + row_of(w, s) * w.D + i];
    }
    wide sum = 0;
    for (uint32_t k = from; k < to; k++) {
        sum += (wide)w.mix_share[k] * (wide)w.theta[base + (uint64_t)w.mix_class[k] * w.D + i];
    }
    return (int64_t)rel(sum, FACE_BITS);
}

// A site's opening face `x⁰_t = E(u_t) + E₋(u_(t−1)) + E₊(u_(t+1))`: its row of the encoding (or its
// mixture's) with its strand neighbours' rows of theirs, a neighbour only within the site's own region
// (a site at its region's first place has none before it; the next site is the region's own when its
// place is not the first).
extern "C" __global__ void field_open(FieldWords w) {
    const uint64_t cells = (uint64_t)w.T * w.D;
    for (uint64_t c = (uint64_t)blockIdx.x * blockDim.x + threadIdx.x; c < cells; c += (uint64_t)gridDim.x * blockDim.x) {
        const uint64_t t = c / w.D, i = c % w.D;
        int64_t x = opening_term(w, w.enc, t, i);
        if (w.site_pos[t] > 0) {
            x += opening_term(w, w.enc_before, t - 1, i);
        }
        if (t + 1 < w.T && w.site_pos[t + 1] > 0) {
            x += opening_term(w, w.enc_after, t + 1, i);
        }
        w.x[c] = x;
    }
}

// `r̂ = r / ‖r‖_rms` on `2^(−16)` and `‖r‖_rms` (`ratio_to_power`), lane by lane (§16.40, the host's `lane_chart`): each
// lane's `W = D / L` coordinates a ratio to their own power, its scale at `[t][lane]`; one warp a site.
extern "C" __global__ void field_chart(FieldWords w, const int64_t *x, int32_t *read, wide *scale, uint32_t only_unresolved) {
    const uint32_t lane = threadIdx.x & 31;
    const uint64_t warps = (uint64_t)gridDim.x * (blockDim.x >> 5);
    const uint32_t lw = w.D / w.lanes;
    for (uint64_t t = ((uint64_t)blockIdx.x * blockDim.x + threadIdx.x) >> 5; t < w.T; t += warps) {
        if (only_unresolved && !w.unresolved[t]) {
            continue;
        }
        for (uint32_t k = 0; k < w.lanes; ++k) {
            const int64_t *xt = x + t * w.D + k * lw;
            wide power = 0;
            for (uint32_t i = lane; i < lw; i += 32) {
                power += (wide)xt[i] * (wide)xt[i];
            }
            power = warp_sum(power);
            const wide s = (wide)isqrt128((uwide)(power / (wide)lw));
            for (uint32_t i = lane; i < lw; i += 32) {
                read[t * w.D + k * lw + i] = s == 0 ? 0 : fit32(div_nearest((wide)xt[i] << FACE_BITS, s), w.status);
            }
            if (lane == 0) {
                scale[t * w.lanes + k] = s;
            }
        }
    }
}

// The bias offset of an affine map with no bias (the host's `affine(.., None, ..)`: a tangent's chart, linear in its
// direction).
#define NO_BIAS 0xFFFFFFFFFFFFFFFFull

// `out[t][o] = release(Σ_i W[o][i] x[t][i] + bias[o] 2^24, 24)` (`affine`): the host's carrier bound
// `wmax · xmax · (cols + 1)` refused at `2^126`, the sum in 64 bits below `2^62` and in 128 otherwise
// (the same integer either way). With `add`, the result is added to `add[t][o]` (the residual).
template <typename X>
__device__ void affine(const FieldWords &w, uint64_t weight, uint64_t bias, uint64_t wmax, uint32_t rows, uint32_t cols, const X *x, uint64_t x_stride, int64_t *out, uint64_t out_stride, int64_t *add, uint32_t only_unresolved) {
    const uint64_t cells = (uint64_t)w.T * rows;
    for (uint64_t c = (uint64_t)blockIdx.x * blockDim.x + threadIdx.x; c < cells; c += (uint64_t)gridDim.x * blockDim.x) {
        const uint64_t t = c / rows, o = c % rows;
        if (only_unresolved && !w.unresolved[t]) {
            continue;
        }
        const X *xt = x + t * x_stride;
        uint64_t xmax = 0;
        for (uint32_t i = 0; i < cols; i++) {
            const uint64_t m = mag64((int64_t)xt[i]);
            xmax = m > xmax ? m : xmax;
        }
        const uwide terms = (uwide)wmax * (uwide)xmax * (uwide)(cols + 1);
        if (terms >= ((uwide)1 << 126)) {
            atomicOr(w.status, REFUSED_CARRIER);
            continue;
        }
        const int32_t *row = w.theta + weight + o * cols;
        wide sum;
        if (terms < ((uwide)1 << 62)) {
            int64_t s = 0;
            for (uint32_t i = 0; i < cols; i++) {
                s += (int64_t)row[i] * (int64_t)xt[i];
            }
            sum = s;
        } else {
            sum = 0;
            for (uint32_t i = 0; i < cols; i++) {
                sum += (wide)row[i] * (wide)xt[i];
            }
        }
        if (bias != NO_BIAS) {
            sum += (wide)w.theta[bias + o] << MATERIAL_BITS;
        }
        const int64_t v = fit64(rel(sum, MATERIAL_BITS), w.status);
        if (add) {
            add[t * out_stride + o] = fit64((wide)add[t * out_stride + o] + (wide)v, w.status);
        } else {
            out[t * out_stride + o] = v;
        }
    }
}

// [agent-inferred, November 5] **The affine map by tiles** (Brandon, November 5: where the time goes; the profile read the
// one-thread-a-cell `affine` at 42% of a training read's kernel time and 61% of a write's, every cell rereading its site's
// whole row for the carrier bound and its weight row from the card's memory): a block holds `W` and the bias in shared
// memory and walks `per = blockDim / rows` sites a pass, each site's row loaded once into shared memory, each thread one
// `(site, output)` cell. The same integers as `affine`: the carrier bound `wmax · xmax · (cols + 1)` per site, the sum in 64
// bits below `2^62` and in 128 otherwise, the bias at the material's grain, the release and the residual.
template <typename X>
__device__ void affine_tiled(const FieldWords &w, uint64_t weight, uint64_t bias, uint64_t wmax, uint32_t rows, uint32_t cols, const X *x, uint64_t x_stride, int64_t *out, uint64_t out_stride, int64_t *add, uint32_t only_unresolved) {
    extern __shared__ __align__(16) unsigned char affine_shared[];
    // [agent-inferred, November 5, the unified-theory reading of 18:53] Shared memory is a circle of 32 banks: `W`'s rows lie
    // at the stride `cols + 1`, coprime to the banks wherever `cols` is a multiple of 32 (every map of the declaration), so a
    // warp's lanes, one output row each, read one term each from 32 banks at once and not 32 times from one.
    const uint32_t stride = cols + 1;
    int32_t *ws = (int32_t *)affine_shared;
    int32_t *bs = ws + (uint64_t)rows * stride;
    uint64_t *xmaxs = (uint64_t *)(affine_shared + ((((uint64_t)rows * stride + rows) * sizeof(int32_t) + 15) & ~(uint64_t)15));
    const uint32_t per = blockDim.x / rows;
    X *xs = (X *)(xmaxs + per);
    for (uint32_t i = threadIdx.x; i < rows * cols; i += blockDim.x) {
        ws[(i / cols) * stride + i % cols] = w.theta[weight + i];
    }
    for (uint32_t i = threadIdx.x; i < rows; i += blockDim.x) {
        bs[i] = bias == NO_BIAS ? 0 : w.theta[bias + i];
    }
    const uint32_t p = threadIdx.x / rows, o = threadIdx.x % rows;
    for (uint64_t t0 = (uint64_t)blockIdx.x * per; t0 < w.T; t0 += (uint64_t)gridDim.x * per) {
        __syncthreads();
        for (uint32_t i = threadIdx.x; i < per * cols; i += blockDim.x) {
            const uint64_t t = t0 + i / cols;
            xs[i] = t < w.T ? x[t * x_stride + i % cols] : (X)0;
        }
        __syncthreads();
        // Each site's carrier bound read once, by its first output's thread.
        if (o == 0 && p < per) {
            const X *xt = xs + (uint64_t)p * cols;
            uint64_t xmax = 0;
            for (uint32_t i = 0; i < cols; i++) {
                const uint64_t m = mag64((int64_t)xt[i]);
                xmax = m > xmax ? m : xmax;
            }
            xmaxs[p] = xmax;
        }
        __syncthreads();
        const uint64_t t = t0 + p;
        if (p >= per || t >= w.T || (only_unresolved && !w.unresolved[t])) {
            continue;
        }
        const X *xt = xs + (uint64_t)p * cols;
        const uint64_t xmax = xmaxs[p];
        const uwide terms = (uwide)wmax * (uwide)xmax * (uwide)(cols + 1);
        if (terms >= ((uwide)1 << 126)) {
            atomicOr(w.status, REFUSED_CARRIER);
            continue;
        }
        const int32_t *row = ws + (uint64_t)o * stride;
        wide sum;
        if (terms < ((uwide)1 << 62)) {
            int64_t s = 0;
            for (uint32_t i = 0; i < cols; i++) {
                s += (int64_t)row[i] * (int64_t)xt[i];
            }
            sum = s;
        } else {
            sum = 0;
            for (uint32_t i = 0; i < cols; i++) {
                sum += (wide)row[i] * (wide)xt[i];
            }
        }
        sum += (wide)bs[o] << MATERIAL_BITS;
        const int64_t v = fit64(rel(sum, MATERIAL_BITS), w.status);
        if (add) {
            add[t * out_stride + o] = fit64((wide)add[t * out_stride + o] + (wide)v, w.status);
        } else {
            out[t * out_stride + o] = v;
        }
    }
}

extern "C" __global__ void field_affine_tiled_x32(FieldWords w, uint64_t weight, uint64_t bias, uint64_t wmax, uint32_t rows, uint32_t cols, const int32_t *x, uint64_t x_stride, int64_t *out, uint64_t out_stride, int64_t *add, uint32_t only_unresolved) {
    affine_tiled<int32_t>(w, weight, bias, wmax, rows, cols, x, x_stride, out, out_stride, add, only_unresolved);
}

extern "C" __global__ void field_affine_tiled_x64(FieldWords w, uint64_t weight, uint64_t bias, uint64_t wmax, uint32_t rows, uint32_t cols, const int64_t *x, uint64_t x_stride, int64_t *out, uint64_t out_stride, int64_t *add, uint32_t only_unresolved) {
    affine_tiled<int64_t>(w, weight, bias, wmax, rows, cols, x, x_stride, out, out_stride, add, only_unresolved);
}

extern "C" __global__ void field_affine_x32(FieldWords w, uint64_t weight, uint64_t bias, uint64_t wmax, uint32_t rows, uint32_t cols, const int32_t *x, uint64_t x_stride, int64_t *out, uint64_t out_stride, int64_t *add, uint32_t only_unresolved) {
    affine<int32_t>(w, weight, bias, wmax, rows, cols, x, x_stride, out, out_stride, add, only_unresolved);
}

extern "C" __global__ void field_affine_x64(FieldWords w, uint64_t weight, uint64_t bias, uint64_t wmax, uint32_t rows, uint32_t cols, const int64_t *x, uint64_t x_stride, int64_t *out, uint64_t out_stride, int64_t *add, uint32_t only_unresolved) {
    affine<int64_t>(w, weight, bias, wmax, rows, cols, x, x_stride, out, out_stride, add, only_unresolved);
}

// The frame, by head: `w̃ = U ⊙ w` and so for the values, `[h][t][2n]` real parts then imaginary,
// each product released to `2^(−16)`. The word is `qkv[t][0..2M]`, the value `qkv[t][2M..4M]`.
extern "C" __global__ void field_frame(FieldWords w) {
    const uint64_t cells = (uint64_t)w.H * w.T * w.n;
    for (uint64_t c = (uint64_t)blockIdx.x * blockDim.x + threadIdx.x; c < cells; c += (uint64_t)gridDim.x * blockDim.x) {
        const uint32_t li = c % w.n;
        const uint64_t t = (c / w.n) % w.T;
        const uint32_t h = c / ((uint64_t)w.n * w.T);
        const uint32_t m = h * w.n + li;
        wide ur, ui;
        frame_of(w, t, h, li, &ur, &ui);
        const uint64_t at = ((uint64_t)h * w.T + t) * w.span;
        const int64_t *qv = w.qkv + t * 2 * w.M2;
        const wide qr = qv[m], qi = qv[w.M + m];
        const wide vr = qv[w.M2 + m], vi = qv[w.M2 + w.M + m];
        const int64_t q0 = fit64(rel(ur * qr - ui * qi, MOVE_BITS), w.status), q1 = fit64(rel(ui * qr + ur * qi, MOVE_BITS), w.status);
        const int64_t v0 = fit64(rel(ur * vr - ui * vi, MOVE_BITS), w.status), v1 = fit64(rel(ui * vr + ur * vi, MOVE_BITS), w.status);
        w.qf[at + li] = q0;
        w.qf[at + w.n + li] = q1;
        w.vf[at + li] = v0;
        w.vf[at + w.n + li] = v1;
    }
}

// Every receiver's probe framed alike (§16.19): `pr[t][0..2M]` into `pq[h][t][2n]`, each product released to `2^(−16)`.
extern "C" __global__ void field_frame_probe(FieldWords w) {
    const uint64_t cells = (uint64_t)w.H * w.T * w.n;
    for (uint64_t c = (uint64_t)blockIdx.x * blockDim.x + threadIdx.x; c < cells; c += (uint64_t)gridDim.x * blockDim.x) {
        const uint32_t li = c % w.n;
        const uint64_t t = (c / w.n) % w.T;
        const uint32_t h = c / ((uint64_t)w.n * w.T);
        const uint32_t m = h * w.n + li;
        wide ur, ui;
        frame_of(w, t, h, li, &ur, &ui);
        const uint64_t at = ((uint64_t)h * w.T + t) * w.span;
        const int64_t *pv = w.pr + t * w.M2;
        const wide qr = pv[m], qi = pv[w.M + m];
        w.pq[at + li] = fit64(rel(ur * qr - ui * qi, MOVE_BITS), w.status);
        w.pq[at + w.n + li] = fit64(rel(ui * qr + ur * qi, MOVE_BITS), w.status);
    }
}

// [agent-inferred, November 1] **The contact pairs words at unit power** (`Field::tick`): each head's
// framed word read in place as a ratio to its own power over the head's `2n` reals (`ratio_to_power`,
// on `2^(−16)`), its power kept for the return; one warp a head and a site (`[h][t]`). The binary
// length of the largest unit word is raised into `bits[0]`.
__device__ __forceinline__ void unit_body(const FieldWords &w, int64_t *base, int32_t *base32, wide *qscale, bool track) {
    const uint32_t lane = threadIdx.x & 31;
    const uint64_t warps = (uint64_t)gridDim.x * (blockDim.x >> 5);
    const uint64_t rows = (uint64_t)w.H * w.T;
    uint32_t qb = 0;
    for (uint64_t hs = ((uint64_t)blockIdx.x * blockDim.x + threadIdx.x) >> 5; hs < rows; hs += warps) {
        int64_t *c = base + hs * w.span;
        wide power = 0;
        for (uint32_t i = lane; i < w.span; i += 32) {
            power += (wide)c[i] * (wide)c[i];
        }
        power = warp_sum(power);
        const wide s = (wide)isqrt128((uwide)(power / (wide)w.span));
        for (uint32_t i = lane; i < w.span; i += 32) {
            const int64_t r = s == 0 ? 0 : (int64_t)fit32(div_nearest((wide)c[i] << FACE_BITS, s), w.status);
            c[i] = r;
            base32[hs * w.span + i] = (int32_t)r;
            qb = max(qb, bit_length(mag64(r)));
        }
        if (lane == 0) {
            qscale[hs] = s;
        }
    }
    qb = (uint32_t)warp_max_u64(qb);
    if (track && lane == 0) {
        atomicMax(&w.bits[0], qb);
    }
}

extern "C" __global__ void field_unit(FieldWords w, wide *qscale) {
    unit_body(w, w.qf, w.qf32, qscale, true);
}

// Every receiver's probe at unit power alike (§16.19), its powers in `pscale`.
extern "C" __global__ void field_unit_probe(FieldWords w, wide *pscale) {
    unit_body(w, w.pq, w.pq32, pscale, false);
}

// The return through the word's unit power (`ratio_adjoint`), in place on its framed chart's covector
// `[t][2M]` (head `h`'s slots `h n + l` and `M + h n + l`): `δw̃ = (δŵ − ŵ ⟨ŵ, δŵ⟩/2n) / ‖w̃‖_rms`;
// one warp a head and a site.
__device__ __forceinline__ void unit_back_body(const FieldWords &w, const int64_t *unit, const wide *qscale, int64_t *dq) {
    const uint32_t lane = threadIdx.x & 31;
    const uint64_t warps = (uint64_t)gridDim.x * (blockDim.x >> 5);
    const uint64_t rows = (uint64_t)w.H * w.T;
    for (uint64_t hs = ((uint64_t)blockIdx.x * blockDim.x + threadIdx.x) >> 5; hs < rows; hs += warps) {
        const uint32_t h = hs / w.T;
        const uint64_t t = hs % w.T;
        const int64_t *rt = unit + hs * w.span;
        const wide s = qscale[hs];
        wide dot = 0;
        for (uint32_t c = lane; c < w.span; c += 32) {
            const uint64_t slot = t * w.M2 + (c < w.n ? h * w.n + c : w.M + h * w.n + c - w.n);
            dot += (wide)rt[c] * (wide)dq[slot];
        }
        dot = warp_sum(dot);
        const wide mean = div_nearest(dot, (wide)w.span);
        for (uint32_t c = lane; c < w.span; c += 32) {
            const uint64_t slot = t * w.M2 + (c < w.n ? h * w.n + c : w.M + h * w.n + c - w.n);
            dq[slot] = s == 0 ? 0 : fit64(div_nearest(((wide)dq[slot] - rel(mean * (wide)rt[c], 2 * FACE_BITS)) << FACE_BITS, s), w.status);
        }
    }
}

extern "C" __global__ void field_unit_back(FieldWords w, const wide *qscale, int64_t *dq) {
    unit_back_body(w, w.qf, qscale, dq);
}

// The probe's return through its own power, alike (§16.19).
extern "C" __global__ void field_unit_back_probe(FieldWords w, const wide *pscale, int64_t *dp) {
    unit_back_body(w, w.pq, pscale, dp);
}

// ---------------------------------------------------------------------------------------------
// the series row's carrier
//
// [definition; agent-inferred, November 1] **A row is summed whole in `L` limbs of 64 bits**
// (`FieldDeclaration::row_bits()` rounded up to limbs, §14.11): a signed sum is its two's complement
// modulo `2^(64 L)`, exact while the sum's magnitude is below `2^(64 L − 1)` (the declaration's bound,
// which no row passes). A term `face · mult · 2^(a − a_0)` is built once a pair and added whole; the
// current and a share are each one exact long division of such sums, to the nearest numerator.
template <int L>
struct Big {
    uint64_t v[L];
};

template <int L>
__device__ __forceinline__ Big<L> big_zero() {
    Big<L> r;
#pragma unroll
    for (int k = 0; k < L; k++) {
        r.v[k] = 0;
    }
    return r;
}

// `a += b` modulo `2^(64 L)`.
template <int L>
__device__ __forceinline__ void big_add(Big<L> &a, const Big<L> &b) {
    uint64_t carry = 0;
#pragma unroll
    for (int k = 0; k < L; k++) {
        const uint64_t s = a.v[k] + b.v[k];
        const uint64_t c1 = s < a.v[k] ? 1 : 0;
        const uint64_t t = s + carry;
        const uint64_t c2 = t < s ? 1 : 0;
        a.v[k] = t;
        carry = c1 | c2;
    }
}

template <int L>
__device__ __forceinline__ void big_add_small(Big<L> &a, uint64_t x) {
    uint64_t carry = x;
#pragma unroll
    for (int k = 0; k < L; k++) {
        const uint64_t t = a.v[k] + carry;
        carry = t < carry ? 1 : 0;
        a.v[k] = t;
    }
}

// `r = a − b`; returns the borrow out.
template <int L>
__device__ __forceinline__ uint64_t big_sub(Big<L> &r, const Big<L> &a, const Big<L> &b) {
    uint64_t borrow = 0;
#pragma unroll
    for (int k = 0; k < L; k++) {
        const uint64_t d = a.v[k] - b.v[k];
        const uint64_t b1 = a.v[k] < b.v[k] ? 1 : 0;
        const uint64_t e = d - borrow;
        const uint64_t b2 = d < borrow ? 1 : 0;
        r.v[k] = e;
        borrow = b1 | b2;
    }
    return borrow;
}

template <int L>
__device__ __forceinline__ void big_shr1(Big<L> &a) {
#pragma unroll
    for (int k = 0; k < L - 1; k++) {
        a.v[k] = (a.v[k] >> 1) | (a.v[k + 1] << 63);
    }
    a.v[L - 1] >>= 1;
}

template <int L>
__device__ __forceinline__ void big_negate(Big<L> &a) {
#pragma unroll
    for (int k = 0; k < L; k++) {
        a.v[k] = ~a.v[k];
    }
    big_add_small(a, 1);
}

// The binary length (`0` for zero).
template <int L>
__device__ __forceinline__ uint32_t big_bits(const Big<L> &a) {
    uint32_t bits = 0;
#pragma unroll
    for (int k = 0; k < L; k++) {
        if (a.v[k] != 0) {
            bits = 64 * k + bit_length(a.v[k]);
        }
    }
    return bits;
}

// `x << s` (bits shifted past the carrier are lost: the declaration's bound says there are none).
//
// [agent-inferred, November 1] The shift is branch-free: the lanes of a warp are the modes of a row, whose
// terms stand at different whole bits, so a shift by a limb count chosen by a branch ran serially for each
// distinct count (the first realization, measured in the profile: a contact at 14 limbs took 7 ms a launch).
// The bits within a limb shift first (a funnel over the limbs), then the limbs move by the binary digits of
// the count, each step a select.
template <int L>
__device__ __forceinline__ Big<L> big_shl(const Big<L> &x, uint32_t s) {
    const uint32_t q = s >> 6, b = s & 63;
    Big<L> r;
    r.v[0] = x.v[0] << b;
#pragma unroll
    for (int k = 1; k < L; k++) {
        r.v[k] = (x.v[k] << b) | ((x.v[k - 1] >> 1) >> (63 - b));
    }
#pragma unroll
    for (int step = 1; step < L; step <<= 1) {
        const bool take = (q & (uint32_t)step) != 0;
#pragma unroll
        for (int k = L - 1; k >= 0; k--) {
            r.v[k] = take ? (k >= step ? r.v[k - step] : (uint64_t)0) : r.v[k];
        }
    }
    return r;
}

// A term's coefficient `face · mult`, three limbs (`face < 2^62`, `mult < 2^96`).
struct Coef {
    uint64_t c0, c1, c2;
};

__device__ __forceinline__ Coef coef_of(uint64_t face, uwide mult) {
    const uint64_t ml = (uint64_t)mult, mh = (uint64_t)(mult >> 64);
    const uwide p0 = (uwide)face * (uwide)ml;
    const uwide p1 = (uwide)face * (uwide)mh;
    const uwide mid = (p0 >> 64) + (uwide)(uint64_t)p1;
    Coef c;
    c.c0 = (uint64_t)p0;
    c.c1 = (uint64_t)mid;
    c.c2 = (uint64_t)(p1 >> 64) + (uint64_t)(mid >> 64);
    return c;
}

template <int L>
__device__ __forceinline__ Big<L> big_of(const Coef &c) {
    Big<L> r = big_zero<L>();
    r.v[0] = c.c0;
    r.v[1] = c.c1;
    r.v[2] = c.c2;
    return r;
}

// `c · m` with `m` of one limb, or two where `WIDE` (needs `L ≥ 5`).
template <int L, bool WIDE>
__device__ __forceinline__ Big<L> big_mul(const Coef &c, uint64_t m0, uint64_t m1) {
    Big<L> r = big_zero<L>();
    uwide t = (uwide)c.c0 * (uwide)m0;
    r.v[0] = (uint64_t)t;
    uint64_t carry = (uint64_t)(t >> 64);
    t = (uwide)c.c1 * (uwide)m0 + (uwide)carry;
    r.v[1] = (uint64_t)t;
    carry = (uint64_t)(t >> 64);
    t = (uwide)c.c2 * (uwide)m0 + (uwide)carry;
    r.v[2] = (uint64_t)t;
    r.v[3] = (uint64_t)(t >> 64);
    if (WIDE) {
        t = (uwide)c.c0 * (uwide)m1 + (uwide)r.v[1];
        r.v[1] = (uint64_t)t;
        carry = (uint64_t)(t >> 64);
        t = (uwide)c.c1 * (uwide)m1 + (uwide)r.v[2] + (uwide)carry;
        r.v[2] = (uint64_t)t;
        carry = (uint64_t)(t >> 64);
        t = (uwide)c.c2 * (uwide)m1 + (uwide)r.v[3] + (uwide)carry;
        r.v[3] = (uint64_t)t;
        r.v[4] = (uint64_t)(t >> 64);
    }
    return r;
}

template <int L>
__device__ __forceinline__ Big<L> shfl_big(const Big<L> &x, int o) {
    Big<L> r;
#pragma unroll
    for (int k = 0; k < L; k++) {
        r.v[k] = (uint64_t)__shfl_xor_sync(0xffffffffu, (unsigned long long)x.v[k], o);
    }
    return r;
}

__device__ __forceinline__ int64_t warp_min_signed(int64_t v) {
    uint64_t key = (uint64_t)v ^ ((uint64_t)1 << 63);
    for (int o = 16; o > 0; o >>= 1) {
        const uint64_t w = __shfl_xor_sync(0xffffffffu, key, o);
        key = w < key ? w : key;
    }
    return (int64_t)(key ^ ((uint64_t)1 << 63));
}

// A score's term (the host's `Field::face`, §14.11): its whole bits `a = ⌊z⌋` and the face of its
// fraction on `2^(−62)`, in `[2^61, 2^62)`.
__device__ __forceinline__ void term_of(const FieldWords &w, int64_t z, int64_t *a, uint64_t *face) {
    *a = z >> FACE_BITS;
    *face = below_one_face((wide)(z & (((int64_t)1 << FACE_BITS) - 1)) - ((wide)1 << FACE_BITS), w.face, w.digits);
}

// -------------------------------------------------------------------------------------------
// the exact division of a row's sums
//
// [definition; agent-inferred, November 1] **A row's divisor, formed once** (§14.11, §15.2): the mass
// `M` normalized to the top of the carrier (`M 2^sh`, its top bit at `64 L − 1`) with the Möller and
// Granlund reciprocal of its top limb (`Divisor`), so each quotient of that row is one limb: the
// estimate `q̂ = ⌊(x_L 2^64 + x_(L−1)) / m_(L−1)⌋` from the top limbs of the normalized dividend is at
// most two above the quotient (Knuth, algorithm D, one digit), corrected by the exact product `q̂ M`.
// The shares of a row's terms (a division each) and its currents are this division, exact.
template <int L>
struct RowDiv {
    Big<L> mn;
    Big<L> half;
    uint32_t sh, mbits;
    Divisor top;
};

template <int L>
__device__ __forceinline__ RowDiv<L> rowdiv_of(const Big<L> &M) {
    RowDiv<L> d;
    d.mbits = big_bits(M);
    d.sh = d.mbits == 0 ? 0 : 64 * L - d.mbits;
    d.mn = big_shl(M, d.sh);
    d.half = M;
    big_shr1(d.half);
    d.top = divisor_of(d.mbits == 0 ? ((uint64_t)1 << 63) : d.mn.v[L - 1]);
    return d;
}

template <int L, int L2>
__device__ __forceinline__ Big<L2> big_embed(const Big<L> &a) {
    Big<L2> r = big_zero<L2>();
#pragma unroll
    for (int k = 0; k < L; k++) {
        r.v[k] = a.v[k];
    }
    return r;
}

// `a · m` truncated to the carrier (the caller keeps it within).
template <int L>
__device__ __forceinline__ Big<L> big_mul_limb(const Big<L> &a, uint64_t m) {
    Big<L> r;
    uint64_t carry = 0;
#pragma unroll
    for (int k = 0; k < L; k++) {
        const uwide t = (uwide)a.v[k] * (uwide)m + (uwide)carry;
        r.v[k] = (uint64_t)t;
        carry = (uint64_t)(t >> 64);
    }
    return r;
}

// `⌊(x + ⌊M/2⌋) / M⌋`, the nearest quotient on a magnitude, for a row's divisor; false where the quotient
// passes `2^63 + 1` (the 64-bit carrier of what the row releases).
template <int L>
__device__ bool rowdiv_nearest(Big<L> x, const RowDiv<L> &d, uint64_t *quotient) {
    big_add(x, d.half);
    const uint32_t xb = big_bits(x);
    if (xb < d.mbits) {
        *quotient = 0;
        return true;
    }
    if (xb > d.mbits + 63) {
        return false;
    }
    Big<L + 1> xn = big_shl(big_embed<L, L + 1>(x), d.sh);
    const uint64_t u1 = xn.v[L], u0 = xn.v[L - 1];
    uint64_t qh;
    if (u1 >= d.mn.v[L - 1]) {
        qh = UINT64_MAX;
    } else {
        uint64_t rem;
        qh = divide_word(u1, u0, d.top, &rem);
    }
    const Big<L + 1> mm = big_embed<L, L + 1>(d.mn);
    Big<L + 1> prod = big_mul_limb(mm, qh);
    Big<L + 1> t;
    while (big_sub(t, xn, prod) != 0) {
        qh -= 1;
        Big<L + 1> next;
        big_sub(next, prod, mm);
        prod = next;
    }
    *quotient = qh;
    return true;
}

// -------------------------------------------------------------------------------------------
// the resonance classes and their lists

#define WEIGHT_BITS 62
// The contact carriers up to this many limbs add each numerator term where it stands (`add_window`); wider ones
// (rare: a row spread past 512 bits) shift and complement it whole.
#define WINDOW_LIMBS 8
// Blocks a multiprocessor keeps resident (the register file shared among them): 8 blocks of 4 warps.
#define CONTACT_MIN_BLOCKS 8
// The block of `field_spread` (a region a block).
#define SPREAD_THREADS 256
// The most address modes a head's class carries, and the most classes a receiver probes across its seams
// (`2^b − 1`, its own probe class beside them).
#define MAX_CLASS_TRITS 7
// [measurement; theory, November 8 00:25] A receiver's probes held in a row's shared `RowCls` (`cl`, `cum`): 127 keeps the
// contact and reverse kernels' blocks an SM (`ptxas -v` at sm_89: at 255, `field_energy_tangent_rows` rises from 21,664 to
// 25,760 bytes of shared a block, four blocks an SM to three). Under the width law a receiver may probe up to `2^n − 1`
// leaves; until a row's runs are laid out once a batch in global memory, a widened receiver past 127 is refused
// (`energy_widened_lists`).
#define MAX_PROBES 127

// A receiver's stride of probed classes, `2^b` (or `2^n` under the width law): its probe's own class and those across its
// seams.
__device__ __forceinline__ uint32_t probe_stride(const FieldWords &w) {
    return w.pstride;
}
// Warps (rows) a contact block carries.
#define CONTACT_ROWS 4

// A receiver's probes across its seams (the host's `probes`, §15.2): for each address mode whose word lies
// within the band `ε = 2^(−band)` of its light cone, `|re² − im²| 2^band < re² + im²` exactly, the shell
// across that cone (a plate's is the bridge, the bridge's the plate on its in-phase side), and the classes
// every non-empty combination of those crossings reaches. Returns the receiver's own class, the probed
// classes in `out` (their number returned), none of them its own.
__device__ __forceinline__ uint32_t probe_classes(const int64_t *word, uint32_t M, uint32_t b, uint32_t band, uint32_t *own_out, uint32_t *out) {
    uint32_t own = 0, place = 1, cmask = 0;
    int32_t delta[MAX_CLASS_TRITS];
    for (uint32_t l = 0; l < b; l++) {
        const int64_t re = word[l], im = word[M + l];
        const uint64_t quadrature = mag64(im);
        const uint32_t s = (re > 0 && mag64(re) > quadrature) ? 2u : (re < 0 && mag64(re) > quadrature) ? 0u : 1u;
        own += place * s;
        const wide rr = (wide)re * (wide)re, ii = (wide)im * (wide)im;
        const wide diff = rr - ii;
        const uwide mag = (uwide)(diff < 0 ? -diff : diff);
        const bool near_cone = rr + ii > 0 && (mag << band) < (uwide)(rr + ii);
        const uint32_t across = s != 1 ? 1u : (re >= 0 ? 2u : 0u);
        if (near_cone) {
            cmask |= (uint32_t)1 << l;
            delta[l] = (int32_t)place * ((int32_t)across - (int32_t)s);
        }
        place *= 3;
    }
    uint32_t count = 0;
    for (uint32_t sub = cmask; sub != 0; sub = (sub - 1) & cmask) {
        int32_t c = (int32_t)own;
        for (uint32_t l = 0; l < b; l++) {
            if (sub & ((uint32_t)1 << l)) {
                c += delta[l];
            }
        }
        out[count++] = (uint32_t)c;
    }
    *own_out = own;
    return count;
}

// [definition; agent-inferred, November 1] **The resonance classes, the probes and their lists** (the
// dispersing field's §2.2, §6, §12 and §15.2; the host's `ClassLists::of` and `probes`): one block of one
// warp a head and a region. Each site's class is `Σ_l 3^l σ_l` over the shells of its unframed key word's first
// `b` modes (the sharp address: §15.2's memberships were measured and retired), listed under the key `2c`
// where it is definite (known or locked) and `2c + 1` otherwise; a definite receiver's probed classes, its
// unframed probe word's own class and those across its seams (`probe_classes`, §16.19), are kept beside it
// and counted by class. The counts are summed in the block's buckets, read as offsets in
// order, and the members placed by a stable counting sort, the region's sites in chunks of 32 in order, a
// lane its rank among the earlier lanes of its class (`__match_any_sync`), so class `c`'s members stand in
// ascending place exactly as the host lists them; the receivers that probe each class follow, in any order.
extern "C" __global__ void field_classes(FieldWords w) {
    extern __shared__ uint32_t buckets[];
    const uint32_t lane = threadIdx.x & 31;
    const uint32_t classes = w.nclasses;
    const uint32_t b = w.ctrits;
    const uint32_t pstride = probe_stride(w);
    uint32_t *pbuckets = buckets + 2 * classes;
    for (uint64_t u = blockIdx.x; u < (uint64_t)w.H * w.R; u += gridDim.x) {
        const uint32_t h = u / w.R, r = u % w.R;
        const uint64_t first = w.region_off[r];
        const uint32_t sites = w.region_off[r + 1] - (uint32_t)first;
        for (uint32_t c = lane; c < 3 * classes; c += 32) {
            buckets[c] = 0;
        }
        __syncwarp();
        for (uint32_t i = lane; i < sites; i += 32) {
            const uint64_t g = first + i;
            const uint64_t hg = (uint64_t)h * w.T + g;
            const int64_t *key = w.qkv + g * 2 * w.M2 + (uint64_t)h * w.n;
            const int64_t *probe = w.pr + g * w.M2 + (uint64_t)h * w.n;
            uint32_t c, pc, probed[MAX_PROBES];
            probe_classes(key, w.M, b, w.band, &c, probed);
            // (an open site reads no class run, §15.9: its probes are not kept, nor listed among the probers)
            const uint32_t count = probe_classes(probe, w.M, b, w.band, &pc, probed);
            const uint32_t kept = definite_site(w, g) ? 1 + count : 0;
            w.cls[hg] = c;
            w.pn[hg] = kept;
            for (uint32_t k = 0; k < kept; k++) {
                const uint32_t q = k == 0 ? pc : probed[k - 1];
                w.pcls[hg * pstride + k] = q;
                atomicAdd(&pbuckets[q], 1u);
            }
            atomicAdd(&buckets[2 * c + (definite_site(w, g) ? 0u : 1u)], 1u);
        }
        __syncwarp();
        uint32_t *off = w.class_off + ((uint64_t)h * w.R + r) * (2 * classes + 1);
        uint32_t *poff = w.poff + ((uint64_t)h * w.R + r) * (classes + 1);
        if (lane == 0) {
            uint32_t at = 0;
            for (uint32_t c = 0; c < 2 * classes; c++) {
                const uint32_t n = buckets[c];
                off[c] = at;
                buckets[c] = at;
                at += n;
            }
            off[2 * classes] = at;
            at = 0;
            for (uint32_t c = 0; c < classes; c++) {
                const uint32_t n = pbuckets[c];
                poff[c] = at;
                pbuckets[c] = at;
                at += n;
            }
            poff[classes] = at;
        }
        __syncwarp();
        uint32_t *members = w.members + (uint64_t)h * w.T + first;
        uint32_t *pmem = w.pmem + ((uint64_t)h * w.T + first) * pstride;
        for (uint32_t i0 = 0; i0 < sites; i0 += 32) {
            const uint32_t i = i0 + lane;
            const bool live = i < sites;
            const uint32_t c = live ? 2 * w.cls[(uint64_t)h * w.T + first + i] + (definite_site(w, first + i) ? 0u : 1u) : 0xFFFFFFFFu;
            const uint32_t peers = __match_any_sync(0xFFFFFFFFu, c);
            const uint32_t rank = __popc(peers & ((1u << lane) - 1u));
            const uint32_t base = live ? buckets[c] : 0;
            __syncwarp();
            if (live) {
                members[base + rank] = i;
                if (rank == 0) {
                    buckets[c] = base + __popc(peers);
                }
            }
            __syncwarp();
        }
        // The probers of each class (every receiver that probes it), placed by a shared counter: their order
        // within a class is the atomic's, and every consumer sums over them (an exact integer sum, in any order).
        for (uint32_t i = lane; i < sites; i += 32) {
            const uint64_t hg = (uint64_t)h * w.T + first + i;
            for (uint32_t k = 0; k < w.pn[hg]; k++) {
                pmem[atomicAdd(&pbuckets[w.pcls[hg * pstride + k]], 1u)] = i;
            }
        }
        __syncwarp();
    }
}

// [definition; agent-inferred, November 1] **The definite words' and values' prefix sums** (the host's
// `Sums::of`, §14.10), one head and region: `sw[row][x]`, `sv[row][x]` the sums of the definite sites'
// unit words and framed values before place `t` (`row = region_off[r] + r + t`, a region's `S + 1`
// rows), `sc[row]` their number. One thread an entry, each over its region's sites in order.
extern "C" __global__ void field_sums(FieldWords w) {
    const uint64_t per = 2 * (uint64_t)w.span + 1;
    const uint64_t threads = (uint64_t)w.H * w.R * per;
    const uint64_t rows1 = (uint64_t)w.T + w.R;
    for (uint64_t u = (uint64_t)blockIdx.x * blockDim.x + threadIdx.x; u < threads; u += (uint64_t)gridDim.x * blockDim.x) {
        const uint32_t x = u % per;
        const uint64_t hr = u / per;
        const uint32_t r = hr % w.R, h = hr / w.R;
        const uint64_t first = w.region_off[r];
        const uint32_t sites = w.region_off[r + 1] - (uint32_t)first;
        const uint64_t base = (uint64_t)h * rows1 + first + r;
        if (x < 2 * w.span) {
            const uint32_t xx = x % w.span;
            wide *out = (x < w.span ? w.sw : w.sv) + base * w.span + xx;
            const int64_t *src = (x < w.span ? w.qf : w.vf) + ((uint64_t)h * w.T + first) * w.span + xx;
            wide run = 0;
            out[0] = 0;
            for (uint32_t t = 0; t < sites; t++) {
                if (definite_site(w, first + t)) {
                    run += (wide)src[(uint64_t)t * w.span];
                }
                out[(uint64_t)(t + 1) * w.span] = run;
            }
        } else {
            uint64_t *out = w.sc + base;
            uint64_t run = 0;
            out[0] = 0;
            for (uint32_t t = 0; t < sites; t++) {
                run += definite_site(w, first + t) ? 1 : 0;
                out[t + 1] = run;
            }
        }
    }
}

// [definition; agent-inferred, November 1] **A receiver's runs** (the host's `ClassLists::support`, §14.1 and
// §15.2, §16.19): its probe's own class and its probed classes, whose definite runs it reads past the near field. The
// warp keeps the classes and the running offsets of their runs in shared memory; an entry of the support
// is one of the near field's `NEAR_SLOTS` places or an entry of a run, found by the offsets.
struct RowCls {
    // An open receiver (not definite) reads past the near field every definite site of its region, at the full
    // lock, and no class run, probe or crowd (§15.9): `dl` them and `ndef` their number.
    uint32_t open;
    uint32_t ndef;
    const uint32_t *dl;
    uint32_t nc;
    uint32_t cl[MAX_PROBES + 1];
    uint32_t cum[MAX_PROBES + 2];
    // The region's resolutions and carried mixtures from its first site: a near place is a source only where it
    // is keyed, known or carrying a face (§16.20).
    const uint8_t *unres;
    const uint32_t *mixo;
};

// A keyed site (§16.20): known, or carrying a face. A site that carries neither has no word to be met by and is
// no receiver's source, its near field's included.
__device__ __forceinline__ bool keyed_site(const FieldWords &w, uint64_t g) {
    return w.unresolved[g] == 0 || w.mix_off[g] != w.mix_off[g + 1];
}

// Prepare the warp's row `hg` (head `h`, batch site `g`): its classes and their runs' offsets, and return the
// support's length in entries. Called by every lane of the warp.
__device__ __forceinline__ uint32_t row_prepare(const FieldWords &w, uint64_t hg, const uint32_t *off, RowCls &rc, uint32_t lane) {
    __syncwarp();
    if (lane == 0) {
        const uint64_t g = hg % w.T;
        const uint32_t r = w.site_region[g];
        rc.open = definite_site(w, g) ? 0 : 1;
        rc.ndef = w.dstart[r + 1] - w.dstart[r];
        rc.dl = w.dlist + w.dstart[r];
        rc.unres = w.unresolved + w.region_off[r];
        rc.mixo = w.mix_off + w.region_off[r];
        const uint32_t pstride = probe_stride(w);
        rc.nc = rc.open ? 0 : w.pn[hg];
        for (uint32_t k = 0; k < rc.nc; k++) {
            rc.cl[k] = w.pcls[hg * pstride + k];
        }
        uint32_t at = 0;
        rc.cum[0] = 0;
        for (uint32_t q = 0; q < rc.nc; q++) {
            at += off[2 * rc.cl[q] + 1] - off[2 * rc.cl[q]];
            rc.cum[q + 1] = at;
        }
    }
    __syncwarp();
    return NEAR_SLOTS + (rc.open ? rc.ndef : rc.cum[rc.nc]);
}

// Site `i`'s support entry `k` of its region: the near field first (`k < NEAR_SLOTS`, the `NEAR − 1` places
// before and after it, nearest first, each only where it is keyed, §16.20), then the DEFINITE runs of its probe's class and its probed classes past
// the near field. Returns the source's place, or `UINT32_MAX` where the entry meets no site (a near place
// outside the region, or a member inside the near field).
__device__ __forceinline__ uint32_t support_at(const uint32_t *members, const uint32_t *off, const RowCls &rc, uint32_t i, uint32_t sites, uint32_t k) {
    if (k < NEAR_SLOTS) {
        const uint32_t d = k / 2 + 1;
        const uint32_t j = k % 2 == 0 ? (i >= d ? i - d : UINT32_MAX) : (i + d < sites ? i + d : UINT32_MAX);
        return j != UINT32_MAX && (rc.unres[j] == 0 || rc.mixo[j] != rc.mixo[j + 1]) ? j : UINT32_MAX;
    }
    const uint32_t e = k - NEAR_SLOTS;
    if (rc.open) {
        const uint32_t j = rc.dl[e];
        const uint32_t gap = j > i ? j - i : i - j;
        return gap >= NEAR ? j : UINT32_MAX;
    }
    uint32_t q = 0;
    while (e >= rc.cum[q + 1]) {
        q++;
    }
    const uint32_t j = members[off[2 * rc.cl[q]] + (e - rc.cum[q])];
    const uint32_t gap = j > i ? j - i : i - j;
    return gap >= NEAR ? j : UINT32_MAX;
}

// Source `j`'s receiver entry `k`: the near field, and where `j` is definite every definite receiver whose
// support holds it past the near field (the receivers that probe its key's class, their own probe's class
// among them, §16.19) and every open site of the region (§15.9: an open receiver hears every definite site). The support is
// directional: `j` is in `S_i` exactly when `j` is near `i`, or definite and heard by `i`.
__device__ __forceinline__ uint32_t receiver_at(const uint32_t *members, const uint32_t *off, const uint32_t *pmem, const uint32_t *poff, const uint32_t *olist, uint32_t c, uint32_t j, uint32_t sites, uint32_t k) {
    if (k < NEAR_SLOTS) {
        const uint32_t d = k / 2 + 1;
        if (k % 2 == 0) {
            return j >= d ? j - d : UINT32_MAX;
        }
        return j + d < sites ? j + d : UINT32_MAX;
    }
    const uint32_t e = k - NEAR_SLOTS;
    const uint32_t probed = poff[c + 1] - poff[c];
    const uint32_t i = e < probed ? pmem[poff[c] + e] : olist[e - probed];
    const uint32_t gap = j > i ? j - i : i - j;
    return gap >= NEAR ? i : UINT32_MAX;
}

__device__ __forceinline__ uint32_t receiver_len(const uint32_t *off, const uint32_t *poff, uint32_t nopen, uint32_t c, bool definite) {
    return NEAR_SLOTS + (definite ? poff[c + 1] - poff[c] + nopen : 0);
}

// Receiver `i`'s crowd `slot` in a region of `sites` (the host's `crowd_ranges`, §14.10): octave
// `level = 2 + ⌊slot/2⌋`, the nearer side first (even slots before `i`, odd after), the places
// `|i − j| ∈ [max(2^level, NEAR), 2^(level+1) − 1]` within the region. False where the crowd is absent.
__device__ __forceinline__ bool crowd_at(uint32_t i, uint32_t sites, uint32_t slot, uint32_t *lo, uint32_t *hi, uint32_t *level) {
    const uint32_t lv = 2 + slot / 2;
    if (lv >= 31 || ((uint32_t)1 << lv) >= sites) {
        return false;
    }
    const uint32_t near = max((uint32_t)1 << lv, (uint32_t)NEAR), far = ((uint32_t)2 << lv) - 1;
    if (slot % 2 == 0) {
        if (i < near) {
            return false;
        }
        *lo = i > far ? i - far : 0;
        *hi = i - near;
    } else {
        if (i + near >= sites) {
            return false;
        }
        *lo = i + near;
        *hi = min(i + far, sites - 1);
    }
    *level = lv;
    return true;
}

// The crowd slots a region of `sites` can hold (two an octave).
__device__ __forceinline__ uint32_t crowd_slots(uint32_t sites) {
    uint32_t slots = 0;
    for (uint32_t lv = 2; lv < 31 && ((uint32_t)1 << lv) < sites; lv++) {
        slots += 2;
    }
    return slots;
}

// `⌊log₂ d⌋`, `d ≥ 1`: the falloff's octave.
__device__ __forceinline__ int64_t octave(uint32_t d) {
    return 31 - __clz(d);
}

// -------------------------------------------------------------------------------------------
// the head's lock

__device__ __forceinline__ uint32_t wide_bits(wide v) {
    const uwide m = (uwide)(v < 0 ? -v : v);
    const uint64_t hi = (uint64_t)(m >> 64);
    return hi != 0 ? 128 - __clzll((long long)hi) : (m == 0 ? 0 : 64 - __clzll((long long)(uint64_t)m));
}

// `a · b` where it fits `i128` (the host's `checked_mul`).
__device__ __forceinline__ bool mul_fits(wide a, wide b, wide *r) {
    if (wide_bits(a) + wide_bits(b) <= 126) {
        *r = a * b;
        return true;
    }
    const bool neg = (a < 0) != (b < 0);
    const uwide ua = (uwide)(a < 0 ? -a : a), ub = (uwide)(b < 0 ? -b : b);
    const uint64_t a0 = (uint64_t)ua, a1 = (uint64_t)(ua >> 64), b0 = (uint64_t)ub, b1 = (uint64_t)(ub >> 64);
    const uwide p00 = (uwide)a0 * b0, p01 = (uwide)a0 * b1, p10 = (uwide)a1 * b0, p11 = (uwide)a1 * b1;
    const uwide mid = (p00 >> 64) + (uint64_t)p01 + (uint64_t)p10;
    const uwide lo = (uwide)(uint64_t)p00 | (mid << 64);
    const uwide hi = p11 + (p01 >> 64) + (p10 >> 64) + (mid >> 64);
    const uwide limit = neg ? ((uwide)1 << 127) : (((uwide)1 << 127) - 1);
    if (hi != 0 || lo > limit) {
        return false;
    }
    *r = neg ? (wide)(0 - lo) : (wide)lo;
    return true;
}

__device__ __forceinline__ bool add_fits(wide a, wide b, wide *r) {
    const wide s = (wide)((uwide)a + (uwide)b);
    if ((a >= 0) == (b >= 0) && (s >= 0) != (a >= 0)) {
        return false;
    }
    *r = s;
    return true;
}

__device__ __forceinline__ bool sub_fits(wide a, wide b, wide *r) {
    const wide s = (wide)((uwide)a - (uwide)b);
    if ((a >= 0) != (b >= 0) && (s >= 0) != (a >= 0)) {
        return false;
    }
    *r = s;
    return true;
}

// [definition; agent-inferred, November 1] **A mode's lock against the source that arrives** (the host's
// `lock`, §15.2): `2 count D Re(conj(a) b) 2^g − D² |b|²` for the receiver's mode `a` and a source's `b`
// (a crowd's summed word over its `count`) carried by the skin `(D, g)`, every product and sum checked
// against the 128-bit carrier (the status bit is the host's refusal).
__device__ __forceinline__ wide lock_of(wide a0, wide a1, wide b0, wide b1, wide count, wide decay, uint32_t grain, uint32_t *st) {
    wide pairing, power, result;
    bool ok = add_fits(a0 * b0, a1 * b1, &pairing);
    ok = ok && mul_fits(pairing, 2 * count * decay, &pairing);
    ok = ok && mul_fits(pairing, (wide)1 << grain, &pairing);
    ok = ok && add_fits(b0 * b0, b1 * b1, &power);
    ok = ok && mul_fits(power, decay * decay, &power);
    ok = ok && sub_fits(pairing, power, &result);
    if (!ok) {
        atomicOr(st, REFUSED_CARRIER);
        return 0;
    }
    return result;
}

// [agent-inferred, November 1] **A source site's lock, the words on 32 bits** (`lock_of` with `count = 1`): the
// contact's words are the unit words `field_unit` fits to 32 bits (`fit32`, refused past them), so each
// product of two is below `2^62`, a pairing or a power below `2^63`, the skin `D ≤ 2^30`, the grain
// `g ≤ 30`, and `pairing · 2D · 2^g < 2^125`, `power · D² < 2^123` stand inside the 128-bit carrier: none of
// `lock_of`'s checks can fail, and the value is the same integer, formed from 64-bit products.
__device__ __forceinline__ wide lock_pair(int64_t a0, int64_t a1, int64_t b0, int64_t b1, uint64_t decay, uint32_t grain) {
    const wide pairing = (wide)(a0 * b0) + (wide)(a1 * b1);
    const wide power = (wide)(b0 * b0) + (wide)(b1 * b1);
    return ((pairing * (wide)(2 * decay)) << grain) - power * (wide)(decay * decay);
}

// [definition; agent-inferred, November 2] **The temperature of a head's locks** (§15.10, §16.12, `temperature_of`):
// the material holds `ℓ = log₂ T` at the receiver's head and kind entry (`temper`, on `2^(−24)`), and `T = 2^c ·
// 2^(ℓ − c)`, `c = ⌈ℓ⌉`, the fraction read through the exponential's resident face at `ℓ`'s `2^(−16)`, released to
// `2^(−24)`; past its carrier it is refused. A score is `z = release(T S, 24) − falloff` from the lock at unit gain
// `S` (on `2^(−16)`).
__device__ __forceinline__ wide temper_log(const FieldWords &w, wide l);

__device__ __forceinline__ wide temper_of(const FieldWords &w, uint32_t h, bool listens) {
    return temper_log(w, (wide)w.theta[w.temper_at + 2 * h + (listens ? 1 : 0)]);
}

// A temperature from its logarithm `ℓ = log₂ T` on `2^(−24)` (the host's `temperature_of`), read as `temper_of` reads a
// head's: the letters' temperature of an energy field is read through it at `−θ[face_temper]` (`1/T`).
__device__ __forceinline__ wide temper_log(const FieldWords &w, wide l) {
    const wide c = (l + ((wide)1 << MATERIAL_BITS) - 1) >> MATERIAL_BITS;
    if (c > TEMPER_TOP || c < 1 - (wide)MATERIAL_BITS) {
        atomicOr(w.status, REFUSED_TEMPER);
        return 0;
    }
    // `below_one` at the material's grain (`Field::fine_exponential`): the fraction's rest, its sixteen high digits
    // through the resident face (the first sixteen roots, in their order), then the eight fine roots after them.
    const uint64_t frac = (uint64_t)(c * ((wide)1 << MATERIAL_BITS) - l);
    const uint64_t rest = frac == 0 ? 0 : ((uint64_t)1 << MATERIAL_BITS) - frac;
    uint64_t value = w.face[rest >> (MATERIAL_BITS - FACE_BITS)];
    for (uint32_t i = 0; i < MATERIAL_BITS - FACE_BITS; i++) {
        if (rest & ((uint64_t)1 << (MATERIAL_BITS - FACE_BITS - 1 - i))) {
            const uint64_t lo = value * w.fine_roots[i];
            const uint64_t hi = __umul64hi(value, w.fine_roots[i]);
            value = (hi << (64 - UNIT_BITS)) | (lo >> UNIT_BITS);
        }
    }
    const uint64_t shifted = frac == 0 ? value : value >> 1;
    const uint64_t face = shifted == 0 ? 1 : shifted;
    return rel((wide)face, (unsigned)(UNIT_BITS - MATERIAL_BITS - c));
}

// [definition; agent-inferred, November 2] **A row's temperature covector in its own chart** (§16.12,
// `temperature_chain`): the row's `δT = Σ release(δz S, 16)`, carried into `ℓ = log₂ T` as `δℓ = release(δT ·
// release(T ln 2, 30), 24)`, so the rows' covectors sum in any order to the same bits.
__device__ __forceinline__ wide temper_chain(const FieldWords &w, wide temper, wide dt) {
    const wide ln2 = (wide)(((uwide)w.ln2_hi << 64) | (uwide)w.ln2_lo);
    wide carried;
    if (!mul_fits(dt, rel(temper * ln2, LN2_FACE_BITS), &carried)) {
        atomicOr(w.status, REFUSED_CARRIER);
        return 0;
    }
    return rel(carried, MATERIAL_BITS);
}

__device__ __forceinline__ int64_t scored(const FieldWords &w, wide temper, int64_t base, uint32_t octave_of) {
    return fit64(rel(temper * (wide)base, MATERIAL_BITS) - ((wide)octave_of << FACE_BITS), w.status);
}

// The head's lock at unit gain `S` of the word `wi` (at unit power, its `span` reals) against site `j`'s across
// `gap` sites: the sum over its `n` modes of each mode's lock carried by the skin (checked, exact), released
// `16 + 2g + 1` bits (§2.5, §12, §15.2, §15.10); its score is `scored`.
__device__ __forceinline__ int64_t pair_base(const FieldWords &w, uint32_t h, const int64_t *wi, const int64_t *wj, uint64_t gi, uint64_t gj, uint32_t gap) {
    const uint32_t g = skinless(w, h) ? 0 : MOVE_BITS;
    wide s = 0;
    for (uint32_t l = 0; l < w.n; l++) {
        const wide lk = lock_pair(wi[l], wi[w.n + l], wj[l], wj[w.n + l], (uint64_t)skin_raw(w, h, l, gi, gj, gap), g);
        if (!add_fits(s, lk, &s)) {
            atomicOr(w.status, REFUSED_CARRIER);
        }
    }
    return fit64(rel(s, FACE_BITS + 2 * g + 1), w.status);
}

// [agent-inferred, November 1] **The pair lock of a head of eight modes, from the vector rows** (`pair_score`
// for `n = 8`, the same integers): the source's row of sixteen 32-bit words as four `int4` loads (the lanes of
// a warp read different rows, so each load is a gather of one line a lane: sixteen 8-octet loads were
// sixteen such gathers, and the skins another eight), its skins `[h][gap][8]` as two `uint4`.
__device__ __forceinline__ int64_t pair_base8(const FieldWords &w, uint32_t h, const int32_t (&a)[16], const int4 *row, uint64_t gi, uint64_t gj, uint32_t gap) {
    const bool still = skinless(w, h);
    const uint32_t g = still ? 0 : MOVE_BITS;
    int32_t b[16];
#pragma unroll
    for (int q = 0; q < 4; q++) {
        const int4 t = row[q];
        b[4 * q] = t.x;
        b[4 * q + 1] = t.y;
        b[4 * q + 2] = t.z;
        b[4 * q + 3] = t.w;
    }
    uint32_t dec[8];
    if (still) {
#pragma unroll
        for (int l = 0; l < 8; l++) {
            dec[l] = 1;
        }
    } else if (paced_at(w, h, gi)) {
        // A paced head's skins follow its own clock (§16): each mode's from the pair's variation.
#pragma unroll
        for (int l = 0; l < 8; l++) {
            dec[l] = (uint32_t)skin_ij(w, h, l, gi, gj, gap);
        }
    } else {
        const uint4 *d4 = reinterpret_cast<const uint4 *>(w.decay_t + ((uint64_t)h * w.dreach + gap) * 8);
        const uint4 d0 = d4[0], d1 = d4[1];
        dec[0] = d0.x; dec[1] = d0.y; dec[2] = d0.z; dec[3] = d0.w;
        dec[4] = d1.x; dec[5] = d1.y; dec[6] = d1.z; dec[7] = d1.w;
    }
    wide s = 0;
#pragma unroll
    for (int l = 0; l < 8; l++) {
        const wide lk = lock_pair(a[l], a[8 + l], b[l], b[8 + l], (uint64_t)dec[l], g);
        if (!add_fits(s, lk, &s)) {
            atomicOr(w.status, REFUSED_CARRIER);
        }
    }
    return fit64(rel(s, FACE_BITS + 2 * g + 1), w.status);
}

// A crowd's lock at unit gain (§14.10, §15.2, §15.10): the head's locks against its summed word `W` over its
// `count`, `div_nearest(Σ_l lock_l, count² 2^(16 + 2g + 1))`, the words' sum two reads of the prefix sums.
__device__ __forceinline__ int64_t crowd_base(const FieldWords &w, uint32_t h, const int64_t *wi, const wide *swlo, const wide *swhi, uint64_t count, uint32_t level, uint64_t gi, bool right) {
    const uint32_t g = skinless(w, h) ? 0 : MOVE_BITS;
    wide s = 0;
    for (uint32_t l = 0; l < w.n; l++) {
        const wide lk = lock_of(wi[l], wi[w.n + l], swhi[l] - swlo[l], swhi[w.n + l] - swlo[w.n + l], (wide)count, skin_raw(w, h, l, gi, octave_edge(gi, level, right), (uint32_t)1 << level), g, w.status);
        if (!add_fits(s, lk, &s)) {
            atomicOr(w.status, REFUSED_CARRIER);
        }
    }
    const uint32_t bits = FACE_BITS + 2 * g + 1;
    return fit64(div_nearest(s, (wide)(count * count) << bits), w.status);
}

// A crowd's score: `z = release(T S, 24) − level 2^16`.
__device__ __forceinline__ int64_t crowd_score(const FieldWords &w, uint32_t h, const int64_t *wi, const wide *swlo, const wide *swhi, uint64_t count, uint32_t level, wide temper, uint64_t gi, bool right) {
    return scored(w, temper, crowd_base(w, h, wi, swlo, swhi, count, level, gi, right), level);
}

// The lanes that carry one entry of the span, and the parts of a chunk each lane takes: a lane an
// entry, `32 / span` parts where the span divides the warp (a power of two), else one.
__device__ __forceinline__ uint32_t span_parts(uint32_t span) {
    return 32 % span == 0 ? 32 / span : 1;
}

// A lane's partial of one entry summed over its parts (lanes `entry + p span`).
__device__ __forceinline__ wide parts_sum(wide v, uint32_t span, uint32_t parts) {
    uwide u = (uwide)v;
    for (uint32_t o = span; parts > 1 && o < 32; o <<= 1) {
        u += shfl_wide(u, (int)o);
    }
    return (wide)u;
}


// -------------------------------------------------------------------------------------------
// the exposure and the contact

// [definition; agent-inferred, November 1] **The row's exponents, read before its carrier is chosen**
// (§14.11: width is dynamic, never arbitrary). One warp a head and a receiving site, a lane a support
// entry: the row's least whole bit `a_0` over its terms (the support's and the crowds'), kept in
// `amin[h][t]`, and the spread `a − a_0` the row holds, raised into `bits[1]`; the host reads the
// launch's widest row and launches the contact with the carrier it needs.
extern "C" __global__ void __launch_bounds__(CONTACT_ROWS * 32, 8) field_exposure(FieldWords w) {
    __shared__ RowCls rcs[CONTACT_ROWS];
    const uint32_t warp = threadIdx.x >> 5, lane = threadIdx.x & 31;
    const uint32_t S = w.span, classes = w.nclasses;
    const uint64_t rows = (uint64_t)w.H * w.T;
    const uint64_t rows1 = (uint64_t)w.T + w.R;
    for (uint64_t hg = ((uint64_t)blockIdx.x * blockDim.x + threadIdx.x) >> 5; hg < rows; hg += (uint64_t)gridDim.x * (blockDim.x >> 5)) {
        const uint32_t h = hg / w.T;
        const uint64_t g = hg % w.T;
        if (skipped_row(w, g)) {
            continue;
        }
        const uint32_t r = w.site_region[g];
        const uint64_t first = w.region_off[r];
        const uint32_t sites = w.region_off[r + 1] - (uint32_t)first, i = w.site_pos[g];
        const uint32_t *members = w.members + (uint64_t)h * w.T + first;
        const uint32_t *off = w.class_off + ((uint64_t)h * w.R + r) * (2 * classes + 1);
        const uint32_t c = w.cls[hg];
        const uint32_t K = row_prepare(w, hg, off, rcs[warp], lane);
        const int64_t *words = w.qf + ((uint64_t)h * w.T + first) * S;
        // Every receiver probes with its own probe (§16.19); sources answer with their keys.
        const int64_t *wi = w.pq + ((uint64_t)h * w.T + g) * S;
        const uint64_t prow0 = (uint64_t)h * rows1 + first + r;
        const wide *swp = w.sw + prow0 * S;
        const uint64_t *scp = w.sc + prow0;
        const uint32_t nslots = rcs[warp].open ? 0 : crowd_slots(sites);
        const wide temper = temper_of(w, h, rcs[warp].open != 0);
        // The pairs' scores are kept at the region block's dense address `[i][j]` for the contact, which reads
        // them there (a score is computed once; the entries outside the support are never read). On a return
        // the locks at unit gain are kept beside them, for the temperatures' covector.
        uint64_t *erow = w.e + (uint64_t)h * w.E + w.region_eoff[r] + (uint64_t)i * sites;
        int64_t *sbrow = w.sb ? w.sb + (uint64_t)h * w.E + w.region_eoff[r] + (uint64_t)i * sites : nullptr;
        int64_t amin = INT64_MAX, amax = INT64_MIN;
        const bool eight = w.n == 8;
        int32_t ai[16];
        const int4 *rows32 = reinterpret_cast<const int4 *>(w.qf32 + ((uint64_t)h * w.T + first) * 16);
        const int4 *probe32 = reinterpret_cast<const int4 *>(w.pq32 + ((uint64_t)h * w.T + g) * 16);
        if (eight) {
#pragma unroll
            for (int q = 0; q < 4; q++) {
                const int4 t = probe32[q];
                ai[4 * q] = t.x;
                ai[4 * q + 1] = t.y;
                ai[4 * q + 2] = t.z;
                ai[4 * q + 3] = t.w;
            }
        }
        for (uint32_t k = lane; k < K; k += 32) {
            const uint32_t j = support_at(members, off, rcs[warp], i, sites, k);
            if (j != UINT32_MAX) {
                const uint32_t gap = j > i ? j - i : i - j;
                const int64_t base = eight ? pair_base8(w, h, ai, rows32 + (uint64_t)j * 4, g, first + j, gap) : pair_base(w, h, wi, words + (uint64_t)j * S, g, first + j, gap);
                // Conservation of faces (§16.38): a still head reads content at any distance, so its source shares its face's
                // mass with its resonance class's definite sources (its score lowered by the octave of their count) and is
                // not weighed by its distance; a turned head reads place, and the octave of its distance lowers its score.
                uint32_t falloff = (uint32_t)octave(gap);
                if (still_head(w, h)) {
                    const uint32_t cj = w.cls[(uint64_t)h * w.T + first + j];
                    const uint32_t count = off[2 * cj + 1] - off[2 * cj];
                    falloff = (uint32_t)octave(count > 1 ? count : 1);
                }
                const int64_t z = scored(w, temper, base, falloff);
                erow[j] = (uint64_t)z;
                if (sbrow) {
                    sbrow[j] = base;
                }
                const int64_t a = z >> FACE_BITS;
                amin = a < amin ? a : amin;
                amax = a > amax ? a : amax;
            }
        }
        uint32_t lo, hi_, lv;
        if (lane < nslots && crowd_at(i, sites, lane, &lo, &hi_, &lv)) {
            const uint64_t count = scp[hi_ + 1] - scp[lo];
            if (count != 0) {
                const int64_t a = crowd_score(w, h, wi, swp + (uint64_t)lo * S, swp + (uint64_t)(hi_ + 1) * S, count, lv, temper, g, lo > i) >> FACE_BITS;
                amin = a < amin ? a : amin;
                amax = a > amax ? a : amax;
            }
        }
        amin = warp_min_signed(amin);
        amax = warp_max_signed(amax);
        if (amin == INT64_MAX) {
            amin = amax = 0;
        }
        if (lane == 0) {
            w.amin[hg] = amin;
            const uint64_t spread = (uint64_t)(amax - amin);
            atomicMax(&w.bits[1], (uint32_t)(spread > 0xFFFFFFFFull ? 0xFFFFFFFFu : spread));
        }
    }
}

// [definition; agent-inferred, November 1] **The numerators' terms are summed by the limb they stand at**
// (`face · |v| · 2^(62 + s)`, `62 + s = 64 q + b`): the term's shifted face (`face << b`, two limbs, formed once
// a term) times the value's magnitude is three limbs standing at limb `q`. A lane takes the chunk's terms in
// the order of their `q` (the lanes rank them by `q` with ballots), sums those of one `q` as signed numbers of
// four limbs (a negative term as its two's complement, `~x + 1`, its sign limb all ones: `-x 2^(64 q) = (-x)
// 2^(64 q)`), and adds each such sum to the row's numerator once, at limb `q`, the carry rippled up the rest and
// nothing below `q` touched. The sums are the old shift-and-complement's modulo `2^(64 L)` (integer sums, in
// any order), without its `+1` counted apart.
template <int L, int Q>
__device__ __forceinline__ void add_window(Big<L> &N, uint64_t a0, uint64_t a1, uint64_t a2, uint64_t a3, uint64_t ext) {
    uint64_t carry = 0;
#pragma unroll
    for (int k = Q; k < L; k++) {
        const int d = k - Q;
        const uint64_t a = d == 0 ? a0 : d == 1 ? a1 : d == 2 ? a2 : d == 3 ? a3 : ext;
        const uint64_t s1 = N.v[k] + a;
        const uint64_t c1 = s1 < a ? 1 : 0;
        const uint64_t s2 = s1 + carry;
        const uint64_t c2 = s2 < s1 ? 1 : 0;
        N.v[k] = s2;
        carry = c1 | c2;
    }
}

template <int L, int Q>
__device__ __forceinline__ void add_window_at(Big<L> &N, uint32_t q, uint64_t a0, uint64_t a1, uint64_t a2, uint64_t a3, uint64_t ext) {
    if (q == (uint32_t)Q) {
        add_window<L, Q>(N, a0, a1, a2, a3, ext);
        return;
    }
    if constexpr (Q + 1 < L) {
        add_window_at<L, Q + 1>(N, q, a0, a1, a2, a3, ext);
    }
}

// A value carried across `d` sites by its skin decay on 64 bits (`carried`, whose result is below `2^63` in
// magnitude: `D ≤ 2^30`): `release(D v, 30)` from the 64-bit halves of the product, half away from zero.
__device__ __forceinline__ int64_t carry_d(uint64_t D, int64_t v) {
    const bool neg = v < 0;
    const uint64_t m = neg ? (uint64_t)0 - (uint64_t)v : (uint64_t)v;
    const uint64_t lo = m * D + ((uint64_t)1 << (MOVE_BITS - 1));
    const uint64_t hi = __umul64hi(m, D) + (lo < ((uint64_t)1 << (MOVE_BITS - 1)) ? 1 : 0);
    const uint64_t r = (lo >> MOVE_BITS) | (hi << (64 - MOVE_BITS));
    return neg ? -(int64_t)r : (int64_t)r;
}

__device__ __forceinline__ int64_t carried_s(const FieldWords &w, uint32_t h, uint32_t l, uint32_t d, int64_t v) {
    return skinless(w, h) ? v : carry_d((uint64_t)decay_of(w, h, l, d), v);
}

// [definition; agent-inferred, November 1] **The contact, the series row and the current over each
// site's support** (`Field::tick`, §14.10, §14.11, §15.2), one warp a head and a receiving site, the
// carrier `L` limbs the exposure chose. The terms: each support entry's (a lane an entry) and each
// crowd's (a lane a slot), `face · multiplier` shifted by `a − a_0` (the multiplier `2^62` of a source,
// a crowd's count `2^62` in the mass and `2^62` in its value), summed whole into the row's mass (the
// lanes' partials, summed over the warp) and, times each value entry, into the numerators (the lanes
// over the span's entries, a lane an entry and a part of the staged terms). The numerators are divided
// once by the mass (`RowDiv`, the exact division to the nearest numerator) and returned to the
// receiver's frame. With `store`, each term's share of the mass is formed once on `2^(−63)`: the pair's
// at the region block's dense address `[i][j]` (which held its score), a crowd's at `ce[h][t][slot]`.
// The pairs met are counted.
template <int L>
__device__ void contact_body(const FieldWords &w, uint32_t store) {
    __shared__ uint32_t stj[CONTACT_ROWS][32], sts[CONTACT_ROWS][32];
    __shared__ uint64_t st0[CONTACT_ROWS][32], st1[CONTACT_ROWS][32], st2[CONTACT_ROWS][32];
    __shared__ uint32_t crlo[CONTACT_ROWS][32], crhi[CONTACT_ROWS][32], crlv[CONTACT_ROWS][32];
    __shared__ RowCls rcs[CONTACT_ROWS];
    const uint32_t warp = threadIdx.x >> 5, lane = threadIdx.x & 31;
    const uint32_t S = w.span, n = w.n, classes = w.nclasses;
    const uint32_t parts = span_parts(S);
    const bool active = lane < S * parts;
    const uint32_t entry = lane % S, part = lane / S, m = entry % n;
    const uint64_t rows = (uint64_t)w.H * w.T;
    const uint64_t rows1 = (uint64_t)w.T + w.R;
    for (uint64_t hg = ((uint64_t)blockIdx.x * blockDim.x + threadIdx.x) >> 5; hg < rows; hg += (uint64_t)gridDim.x * (blockDim.x >> 5)) {
        const uint32_t h = hg / w.T;
        const uint64_t g = hg % w.T;
        if (skipped_row(w, g)) {
            if (lane < n) {
                const uint32_t mc = h * n + lane;
                w.y[g * w.M2 + mc] = 0;
                w.y[g * w.M2 + w.M + mc] = 0;
            }
            continue;
        }
        const uint32_t r = w.site_region[g];
        const uint64_t first = w.region_off[r];
        const uint32_t sites = w.region_off[r + 1] - (uint32_t)first, i = w.site_pos[g];
        const uint32_t *members = w.members + (uint64_t)h * w.T + first;
        const uint32_t *off = w.class_off + ((uint64_t)h * w.R + r) * (2 * classes + 1);
        const uint32_t c = w.cls[hg];
        const uint32_t K = row_prepare(w, hg, off, rcs[warp], lane);
        const int64_t *words = w.qf + ((uint64_t)h * w.T + first) * S;
        const int64_t *values = w.vf + ((uint64_t)h * w.T + first) * S;
        const int64_t *wi = w.pq + ((uint64_t)h * w.T + g) * S;
        const uint64_t prow0 = (uint64_t)h * rows1 + first + r;
        const wide *swp = w.sw + prow0 * S;
        const wide *svp = w.sv + prow0 * S;
        const uint64_t *scp = w.sc + prow0;
        const uint32_t nslots = rcs[warp].open ? 0 : crowd_slots(sites);
        const wide temper = temper_of(w, h, rcs[warp].open != 0);
        const int64_t amin = w.amin[hg];
        uint64_t *erow = w.e + (uint64_t)h * w.E + w.region_eoff[r] + (uint64_t)i * sites;
        Big<L> M = big_zero<L>();
        Big<L> N = big_zero<L>();
        uint32_t negs = 0, met = 0;
        // The numerators of a staged term: the lanes of an entry add their part of it.
        const bool still_h = skinless(w, h), paced_h = paced_at(w, h, g);
        const auto numerators = [&](bool crowd, uint32_t nvalid) {
            if (!active) {
                return;
            }
            if constexpr (L <= WINDOW_LIMBS) {
                if (!crowd) {
                    // The chunk's terms by limb (`stj`, `sts`, `st0`, `st1` ranked), those of one limb summed.
                    uwide ulo = 0, uhi = 0;
                    uint32_t cq = 0xFFFFFFFFu;
                    // Two terms at a time: their values, skins and products are independent, so the loads and the
                    // multiplications of both are in flight together; they are then added in rank order.
                    const auto product = [&](uint32_t pos, uwide *xlo, uwide *xhi, uint32_t *negative) {
                        const uint32_t j = stj[warp][pos];
                        const uint32_t gap = j > i ? j - i : i - j;
                        const int64_t raw = values[(uint64_t)j * S + entry];
                        // (a head of eight modes reads its skin from the vector table: the eight modes of a gap stand together)
                        const int64_t v = still_h ? raw : paced_h ? carry_d((uint64_t)skin_ij(w, h, m, g, first + j, gap), raw) : w.n == 8 ? carry_d((uint64_t)w.decay_t[((uint64_t)h * w.dreach + gap) * 8 + m], raw) : carried_s(w, h, m, gap, raw);
                        const bool neg = v < 0;
                        const uint64_t mag = neg ? (uint64_t)0 - (uint64_t)v : (uint64_t)v;
                        const uwide lo = (uwide)st0[warp][pos] * (uwide)mag;
                        const uwide mid = (uwide)st1[warp][pos] * (uwide)mag + (lo >> 64);
                        const uwide mask = neg ? ~(uwide)0 : 0;
                        *xlo = ((mid << 64) | (uwide)(uint64_t)lo) ^ mask;
                        *xhi = (uwide)(uint64_t)(mid >> 64) ^ mask;
                        *negative = neg ? 1u : 0u;
                    };
                    const auto accumulate = [&](uint32_t pos, uwide xlo, uwide xhi, uint32_t neg) {
                        const uint32_t q = sts[warp][pos];
                        if (q != cq) {
                            if (cq != 0xFFFFFFFFu) {
                                const uint64_t top = (uint64_t)(uhi >> 64);
                                add_window_at<L, 0>(N, cq, (uint64_t)ulo, (uint64_t)(ulo >> 64), (uint64_t)uhi, top, (top >> 63) != 0 ? ~(uint64_t)0 : 0);
                            }
                            cq = q;
                            ulo = 0;
                            uhi = 0;
                        }
                        const uwide t1 = ulo + xlo;
                        const uwide t2 = t1 + (uwide)neg;
                        const uint64_t carry = (t1 < xlo) | (t2 < t1);
                        ulo = t2;
                        uhi += xhi + (uwide)carry;
                    };
                    uint32_t pos = part;
                    for (; pos + parts < nvalid; pos += 2 * parts) {
                        uwide alo, ahi, blo, bhi;
                        uint32_t an, bn;
                        product(pos, &alo, &ahi, &an);
                        product(pos + parts, &blo, &bhi, &bn);
                        accumulate(pos, alo, ahi, an);
                        accumulate(pos + parts, blo, bhi, bn);
                    }
                    if (pos < nvalid) {
                        uwide alo, ahi;
                        uint32_t an;
                        product(pos, &alo, &ahi, &an);
                        accumulate(pos, alo, ahi, an);
                    }
                    if (cq != 0xFFFFFFFFu) {
                        const uint64_t top = (uint64_t)(uhi >> 64);
                        add_window_at<L, 0>(N, cq, (uint64_t)ulo, (uint64_t)(ulo >> 64), (uint64_t)uhi, top, (top >> 63) != 0 ? ~(uint64_t)0 : 0);
                    }
                    return;
                }
            }
            for (uint32_t jj = part; jj < 32; jj += parts) {
                const uint32_t j = stj[warp][jj];
                if (j == UINT32_MAX) {
                    continue;
                }
                Coef cf;
                cf.c0 = st0[warp][jj];
                cf.c1 = st1[warp][jj];
                cf.c2 = st2[warp][jj];
                Big<L> p;
                bool neg;
                if (!crowd) {
                    const wide v = carried_ij(w, h, m, g, first + j, j > i ? j - i : i - j, values[(uint64_t)j * S + entry]);
                    neg = v < 0;
                    p = big_mul<L, false>(cf, mag64((int64_t)v), 0);
                } else {
                    const uint32_t lo = crlo[warp][jj], hi_ = crhi[warp][jj], lv = crlv[warp][jj];
                    const wide v = carried_wide_ij(w, h, m, g, octave_edge(g, lv, lo > i), (uint32_t)1 << lv, svp[(uint64_t)(hi_ + 1) * S + entry] - svp[(uint64_t)lo * S + entry]);
                    neg = v < 0;
                    const uwide mag = (uwide)(neg ? -v : v);
                    p = big_mul<L, true>(cf, (uint64_t)mag, (uint64_t)(mag >> 64));
                }
                p = big_shl(p, sts[warp][jj]);
                if (neg) {
#pragma unroll
                    for (int k = 0; k < L; k++) {
                        p.v[k] = ~p.v[k];
                    }
                    negs += 1;
                }
                big_add(N, p);
            }
        };
        for (uint32_t k0 = 0; k0 < K; k0 += 32) {
            const uint32_t k = k0 + lane;
            const uint32_t j = k < K ? support_at(members, off, rcs[warp], i, sites, k) : UINT32_MAX;
            Coef cf = {0, 0, 0};
            uint32_t s = 0;
            uint64_t face = 0;
            if (j != UINT32_MAX) {
                // The score the exposure kept (a pair's score is computed once).
                const int64_t z = (int64_t)erow[j];
                int64_t a;
                term_of(w, z, &a, &face);
                const int64_t sh = a - amin;
                if (sh >= (int64_t)(64 * L)) {
                    atomicOr(w.status, REFUSED_CARRIER);
                } else {
                    s = (uint32_t)sh;
                }
                cf = coef_of(face, (uwide)1 << WEIGHT_BITS);
                big_add(M, big_shl(big_of<L>(cf), s));
                met += 1;
            }
            uint32_t nvalid = 32;
            if constexpr (L <= WINDOW_LIMBS) {
                // The numerators add `face |v| 2^(62 + s)` by the limb `q` it stands at: the lanes rank their
                // terms by `q` (ballots), and stage the face shifted by its bits within the limb in that order.
                const uint32_t t = s + WEIGHT_BITS, b = t & 63;
                const uint32_t key = (j != UINT32_MAX && (t >> 6) < (uint32_t)L) ? (t >> 6) : 0xFFFFFFFFu;
                const uint32_t below = lane == 0 ? 0u : 0xFFFFFFFFu >> (32 - lane);
                uint32_t rank = 0;
                nvalid = 0;
#pragma unroll
                for (int c = 0; c < L; c++) {
                    const uint32_t mk = __ballot_sync(0xFFFFFFFFu, key == (uint32_t)c);
                    rank += (key > (uint32_t)c ? __popc(mk) : 0) + (key == (uint32_t)c ? __popc(mk & below) : 0);
                    nvalid += __popc(mk);
                }
                if (key != 0xFFFFFFFFu) {
                    st0[warp][rank] = face << b;
                    st1[warp][rank] = b == 0 ? 0 : face >> (64 - b);
                    sts[warp][rank] = key;
                    stj[warp][rank] = j;
                }
            } else {
                st0[warp][lane] = cf.c0;
                st1[warp][lane] = cf.c1;
                st2[warp][lane] = cf.c2;
                sts[warp][lane] = s;
                stj[warp][lane] = j;
            }
            __syncwarp();
            numerators(false, nvalid);
            __syncwarp();
        }
        // The crowds' chunk: a crowd's value multiplier is `2^62`, its mass multiplier its count `2^62`.
        {
            Coef cf = {0, 0, 0};
            uint32_t s = 0, slot = UINT32_MAX, lo = 0, hi_ = 0, lv = 0;
            if (lane < nslots && crowd_at(i, sites, lane, &lo, &hi_, &lv)) {
                const uint64_t count = scp[hi_ + 1] - scp[lo];
                if (count != 0) {
                    slot = lane;
                    const int64_t z = crowd_score(w, h, wi, swp + (uint64_t)lo * S, swp + (uint64_t)(hi_ + 1) * S, count, lv, temper, g, lo > i);
                    int64_t a;
                    uint64_t face;
                    term_of(w, z, &a, &face);
                    const int64_t sh = a - amin;
                    if (sh >= (int64_t)(64 * L)) {
                        atomicOr(w.status, REFUSED_CARRIER);
                    } else {
                        s = (uint32_t)sh;
                    }
                    big_add(M, big_shl(big_of<L>(coef_of(face, (uwide)count << WEIGHT_BITS)), s));
                    cf = coef_of(face, (uwide)1 << WEIGHT_BITS);
                }
            }
            st0[warp][lane] = cf.c0;
            st1[warp][lane] = cf.c1;
            st2[warp][lane] = cf.c2;
            sts[warp][lane] = s;
            stj[warp][lane] = slot;
            crlo[warp][lane] = lo;
            crhi[warp][lane] = hi_;
            crlv[warp][lane] = lv;
            __syncwarp();
            numerators(true, 32);
            __syncwarp();
        }
        // The mass over the lanes; the numerators over the parts of each entry.
        for (int o = 16; o > 0; o >>= 1) {
            const Big<L> om = shfl_big(M, o);
            big_add(M, om);
        }
        for (uint32_t o = S; parts > 1 && o < 32; o <<= 1) {
            const Big<L> on = shfl_big(N, (int)o);
            big_add(N, on);
            negs += __shfl_xor_sync(0xFFFFFFFFu, negs, (int)o);
        }
        met = (uint32_t)warp_sum_u64(met);
        // The framed current's entry `entry`: the numerator over the row's mass, to the nearest numerator. A row whose
        // support holds no keyed source (§16.20) has no mass and gathers nothing: its current is zero and no share is
        // formed (the host's `SeriesRow::release`).
        const bool empty = big_bits(M) == 0;
        Big<L> Md = M;
        if (empty) {
            Md = big_zero<L>();
            Md.v[0] = 1;
        }
        const RowDiv<L> rd = rowdiv_of(Md);
        int64_t y = 0;
        if (active && part == 0 && !empty) {
            big_add_small(N, negs);
            const bool negative = (N.v[L - 1] >> 63) != 0;
            if (negative) {
                big_negate(N);
            }
            uint64_t q = 0;
            bool ok = rowdiv_nearest(N, rd, &q);
            ok = ok && (negative ? q <= ((uint64_t)1 << 63) : q < ((uint64_t)1 << 63));
            if (ok) {
                y = (int64_t)(negative ? (uint64_t)0 - q : q);
            } else {
                atomicOr(w.status, REFUSED_WORD64);
            }
        }
        const int64_t yi = __shfl_sync(0xFFFFFFFFu, y, (lane + n) % 32);
        if (lane == 0) {
            atomicAdd(w.met, (unsigned long long)met);
        }
        if (lane < n) {
            wide ur, ui;
            frame_of(w, g, h, lane, &ur, &ui);
            const uint32_t mc = h * n + lane;
            w.y[g * w.M2 + mc] = fit64(rel(ur * (wide)y + ui * (wide)yi, MOVE_BITS), w.status);
            w.y[g * w.M2 + w.M + mc] = fit64(rel(ur * (wide)yi - ui * (wide)y, MOVE_BITS), w.status);
        }
        __syncwarp();
        // Pass three: each term's share of the row's mass, once, a lane a term.
        if (store) {
            for (uint32_t k = lane; k < K; k += 32) {
                const uint32_t j = support_at(members, off, rcs[warp], i, sites, k);
                if (j != UINT32_MAX) {
                    int64_t a;
                    uint64_t face;
                    term_of(w, (int64_t)erow[j], &a, &face);
                    const Big<L> x = big_shl(big_of<L>(coef_of(face, (uwide)1 << WEIGHT_BITS)), (uint32_t)(a - amin) + SHARE_BITS);
                    uint64_t p = 0;
                    if (!rowdiv_nearest(x, rd, &p)) {
                        p = UINT64_MAX;
                    }
                    erow[j] = p;
                }
            }
            uint32_t lo, hi_, lv;
            if (lane < nslots) {
                uint64_t p = 0;
                if (crowd_at(i, sites, lane, &lo, &hi_, &lv)) {
                    const uint64_t count = scp[hi_ + 1] - scp[lo];
                    if (count != 0) {
                        int64_t a;
                        uint64_t face;
                        term_of(w, crowd_score(w, h, wi, swp + (uint64_t)lo * S, swp + (uint64_t)(hi_ + 1) * S, count, lv, temper, g, lo > i), &a, &face);
                        const Big<L> x = big_shl(big_of<L>(coef_of(face, (uwide)count << WEIGHT_BITS)), (uint32_t)(a - amin) + SHARE_BITS);
                        if (!rowdiv_nearest(x, rd, &p)) {
                            p = UINT64_MAX;
                        }
                    }
                }
                w.ce[hg * w.slots + lane] = p;
            }
        }
        __syncwarp();
    }
}

#define CONTACT_ENTRY(LL) \
    extern "C" __global__ void __launch_bounds__(CONTACT_ROWS * 32, CONTACT_MIN_BLOCKS) field_contact_l##LL(FieldWords w, uint32_t store) { contact_body<LL>(w, store); }
CONTACT_ENTRY(5)
CONTACT_ENTRY(6)
CONTACT_ENTRY(7)
CONTACT_ENTRY(8)
CONTACT_ENTRY(9)
CONTACT_ENTRY(10)
CONTACT_ENTRY(11)
CONTACT_ENTRY(12)
CONTACT_ENTRY(13)
CONTACT_ENTRY(14)
CONTACT_ENTRY(15)
CONTACT_ENTRY(16)
CONTACT_ENTRY(17)
CONTACT_ENTRY(18)
CONTACT_ENTRY(19)
CONTACT_ENTRY(20)

// -------------------------------------------------------------------------------------------
// the site moments and the echo (§15.1, §15.3)

#include "field_moment.cuh"

// [definition; agent-inferred, November 1] **The moment modes are batched** (§15.1): a launch carries every
// moment mode of the batch, `blockIdx.y` (or the quotient of the thread's cell) naming the mode `u`, whose
// ring slot, skin and admission flags are `ws[u]` (`MomentWords`, one per mode), and whose strands, prefix
// sums and results stand at the mode's stride in one array each. The bodies are `field_moment.cuh`'s
// (`moment_admit_regions`, `moment_prefix_regions`, `moment_site_exact`, `moment_return_site`), so a mode's
// bits are the single-mode launch's; only the launch is shared (the saving: a batch's launches no longer
// grow with its moment modes).

// Site `t`'s strand encoding of the moment mode `idx` (the real part, then the imaginary `T` on): its
// class's row of the family at `base` (`2T` wide), zero at a silent open site, or its carried mixture `release(
// Σ_a w_a E(a), 16)` (the host's `strand_row`).
__device__ __forceinline__ int64_t moment_strand(const FieldWords &w, uint64_t base, uint32_t tm, uint32_t idx, uint64_t t, uint32_t part) {
    const uint32_t from = w.mix_off[t], to = w.mix_off[t + 1];
    const uint32_t col = part == 0 ? idx : tm + idx;
    if (from == to) {
        // A silent open site adds nothing to the strand (§16.28, the host's `Field::silent`).
        return w.unresolved[t] ? 0 : w.theta[base + row_of(w, t) * 2 * tm + col];
    }
    wide sum = 0;
    for (uint32_t k = from; k < to; k++) {
        sum += (wide)w.mix_share[k] * (wide)w.theta[base + (uint64_t)w.mix_class[k] * 2 * tm + col];
    }
    return (int64_t)rel(sum, FACE_BITS);
}

// Every moment mode's strands, `before[u][t]` and `after[u][t]` (pairs of 64 bits, `2T` a mode).
extern "C" __global__ void field_moment_strands_all(FieldWords w, uint64_t base_before, uint64_t base_after, uint32_t tm, int64_t *before, int64_t *after) {
    for (uint64_t c = (uint64_t)blockIdx.x * blockDim.x + threadIdx.x; c < (uint64_t)w.T * tm; c += (uint64_t)gridDim.x * blockDim.x) {
        const uint64_t t = c % w.T;
        const uint32_t u = c / w.T;
        for (uint32_t part = 0; part < 2; part++) {
            before[(uint64_t)u * 2 * w.T + 2 * t + part] = moment_strand(w, base_before, tm, u, t, part);
            after[(uint64_t)u * 2 * w.T + 2 * t + part] = moment_strand(w, base_after, tm, u, t, part);
        }
    }
}

// Every moment mode's admission (the forward's: `x` = before, `y` = after; the return's, `returning`: `x` the
// covector, `y` null). Grid `(regions, modes)`, dynamic shared memory `3 · blockDim.x · 16`.
extern "C" __global__ void field_moment_admit_all(const MomentWords *ws, const int64_t *x, const int64_t *y, uint64_t stride, uint32_t returning) {
    moment_admit_regions(ws[blockIdx.y], x + (uint64_t)blockIdx.y * stride, y ? y + (uint64_t)blockIdx.y * stride : nullptr, returning != 0);
}

// Every moment mode's prefix sums of a strand (`released`: the return's `Q`, else the forward's exact `P`).
// Grid `(regions, modes)`, dynamic shared memory `blockDim.x · 32`.
extern "C" __global__ void field_moment_prefix_all(const MomentWords *ws, const int64_t *x, wide *pre, uint64_t stride, uint64_t pre_stride, uint32_t released) {
    moment_prefix_regions(ws[blockIdx.y], x + (uint64_t)blockIdx.y * stride, pre + (uint64_t)blockIdx.y * pre_stride, released != 0);
}

// Every moment mode's moments `s[u][t]` (the body of `field_moment`). Grid `(cells, modes)`.
extern "C" __global__ void field_moment_all(const MomentWords *ws, const int64_t *before, const int64_t *after, const wide *up, const wide *down, int64_t *s, uint64_t stride, uint64_t pre_stride) {
    const uint32_t u = blockIdx.y;
    const MomentWords &w = ws[u];
    before += (uint64_t)u * stride;
    after += (uint64_t)u * stride;
    s += (uint64_t)u * stride;
    up += (uint64_t)u * pre_stride;
    down += (uint64_t)u * pre_stride;
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

// Every moment mode's moments placed at the unframed value's mode `cmap[u]` (`h n + l` of its head and mode).
extern "C" __global__ void field_moment_scatter_all(FieldWords w, const int64_t *s, const uint32_t *cmap, uint32_t tm) {
    for (uint64_t c = (uint64_t)blockIdx.x * blockDim.x + threadIdx.x; c < (uint64_t)w.T * tm; c += (uint64_t)gridDim.x * blockDim.x) {
        const uint64_t t = c % w.T;
        const uint32_t u = c / w.T;
        // A depth ring's mode (the map's top bit) carries no moment.
        const bool dead = cmap[u] >> 31;
        const uint32_t cm = cmap[u] & 0x7FFFFFFFu;
        w.moment[t * w.M2 + cm] = dead ? 0 : s[(uint64_t)u * 2 * w.T + 2 * t];
        w.moment[t * w.M2 + w.M + cm] = dead ? 0 : s[(uint64_t)u * 2 * w.T + 2 * t + 1];
    }
}

// A value is linear in its site's moment (§15.1), never normalized before it: `v += moment`, checked.
extern "C" __global__ void field_moment_add(FieldWords w) {
    const uint64_t cells = (uint64_t)w.T * w.M2;
    for (uint64_t c = (uint64_t)blockIdx.x * blockDim.x + threadIdx.x; c < cells; c += (uint64_t)gridDim.x * blockDim.x) {
        const uint64_t t = c / w.M2, k = c % w.M2;
        int64_t *v = w.qkv + t * 2 * w.M2 + w.M2 + k;
        *v = fit64((wide)*v + (wide)w.moment[c], w.status);
    }
}

// [definition; §16.20] A receiver asks with what has reached its place: its probe `[t][2M]` reads its moment at the
// turned modes, the moment its value carries (the host's `Field::tick`), `p += moment`, checked.
extern "C" __global__ void field_moment_add_probe(FieldWords w, int64_t *pr) {
    const uint64_t cells = (uint64_t)w.T * w.M2;
    for (uint64_t c = (uint64_t)blockIdx.x * blockDim.x + threadIdx.x; c < cells; c += (uint64_t)gridDim.x * blockDim.x) {
        pr[c] = fit64((wide)pr[c] + (wide)w.moment[c], w.status);
    }
}

// The values' covector summed over the ticks: `dm += dv` (`[t][2M]`, 128 bits); the probes' alike (§16.20).
extern "C" __global__ void field_moment_accumulate(FieldWords w, const int64_t *dv, wide *dm) {
    const uint64_t cells = (uint64_t)w.T * w.M2;
    for (uint64_t c = (uint64_t)blockIdx.x * blockDim.x + threadIdx.x; c < cells; c += (uint64_t)gridDim.x * blockDim.x) {
        dm[c] += (wide)dv[c];
    }
}

// Every moment mode's covector as 64-bit pairs (`fit64`, the host's refusal), `ds[u][t]`.
extern "C" __global__ void field_moment_ds_all(FieldWords w, const wide *dm, const uint32_t *cmap, uint32_t tm, int64_t *ds) {
    for (uint64_t c = (uint64_t)blockIdx.x * blockDim.x + threadIdx.x; c < (uint64_t)w.T * tm; c += (uint64_t)gridDim.x * blockDim.x) {
        const uint64_t t = c % w.T;
        const uint32_t u = c / w.T;
        const bool dead = cmap[u] >> 31;
        const uint32_t cm = cmap[u] & 0x7FFFFFFFu;
        ds[(uint64_t)u * 2 * w.T + 2 * t] = dead ? 0 : fit64(dm[t * w.M2 + cm], w.status);
        ds[(uint64_t)u * 2 * w.T + 2 * t + 1] = dead ? 0 : fit64(dm[t * w.M2 + w.M + cm], w.status);
    }
}

// Every moment mode's return (the body of `field_moment_return`): `d_before[u][t]`, `d_after[u][t]`.
// Grid `(cells, modes)`.
extern "C" __global__ void field_moment_return_all(const MomentWords *ws, const int64_t *ds, const wide *q, wide *d_before, wide *d_after, uint64_t stride, uint64_t pre_stride) {
    const uint32_t u = blockIdx.y;
    const MomentWords &w = ws[u];
    ds += (uint64_t)u * stride;
    d_before += (uint64_t)u * stride;
    d_after += (uint64_t)u * stride;
    q += (uint64_t)u * pre_stride;
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

// The strands' return (`Field::strand_return`) of every moment mode: `d[u][t]` (a pair of 128 bits on
// `2^(−24)`) into site `t`'s row of the family at `base` (`2T` wide), or each carried class's row by its
// share, `release(w d, 16)`; added into `g`.
extern "C" __global__ void field_moment_strand_return_all(FieldWords w, uint64_t base_before, uint64_t base_after, uint32_t tm, const wide *d_before, const wide *d_after, wide *g) {
    for (uint64_t c = (uint64_t)blockIdx.x * blockDim.x + threadIdx.x; c < (uint64_t)w.T * tm; c += (uint64_t)gridDim.x * blockDim.x) {
        const uint64_t t = c % w.T;
        const uint32_t u = c / w.T;
        const uint32_t from = w.mix_off[t], to = w.mix_off[t + 1];
        for (uint32_t side = 0; side < 2; side++) {
            const uint64_t base = side == 0 ? base_before : base_after;
            const wide *d = side == 0 ? d_before : d_after;
            for (uint32_t part = 0; part < 2; part++) {
                const uint32_t col = part == 0 ? u : tm + u;
                const wide v = d[(uint64_t)u * 2 * w.T + 2 * t + part];
                if (v == 0) {
                    continue;
                }
                if (from == to) {
                    if (!w.unresolved[t]) {
                        add_wide(g + base + row_of(w, t) * 2 * tm + col, v);
                    }
                } else {
                    for (uint32_t k = from; k < to; k++) {
                        add_wide(g + base + (uint64_t)w.mix_class[k] * 2 * tm + col, rel((wide)w.mix_share[k] * v, FACE_BITS));
                    }
                }
            }
        }
    }
}

// [definition; agent-inferred, November 1] **The echo's round trips** (the host's `round_trips`, §15.3):
// for each site `i` of a tick after the first, `Σ_j release(p_ij^(t) p_ji^(t−1), 63)` over its row's
// sources, `p_ji^(t−1)` read at the previous tick's dense address (zero where `i` was not in `j`'s row),
// added into `trips[i]` over the heads. One warp a head and a receiving site.
extern "C" __global__ void __launch_bounds__(CONTACT_ROWS * 32) field_echo_trips(FieldWords w) {
    __shared__ RowCls rcs[CONTACT_ROWS];
    const uint32_t warp = threadIdx.x >> 5, lane = threadIdx.x & 31;
    const uint32_t classes = w.nclasses;
    const uint64_t rows = (uint64_t)w.H * w.T;
    for (uint64_t hg = ((uint64_t)blockIdx.x * blockDim.x + threadIdx.x) >> 5; hg < rows; hg += (uint64_t)gridDim.x * (blockDim.x >> 5)) {
        const uint32_t h = hg / w.T;
        const uint64_t g = hg % w.T;
        const uint32_t r = w.site_region[g];
        const uint64_t first = w.region_off[r];
        const uint32_t sites = w.region_off[r + 1] - (uint32_t)first, i = w.site_pos[g];
        const uint32_t *members = w.members + (uint64_t)h * w.T + first;
        const uint32_t *off = w.class_off + ((uint64_t)h * w.R + r) * (2 * classes + 1);
        const uint32_t c = w.cls[hg];
        const uint32_t K = row_prepare(w, hg, off, rcs[warp], lane);
        const uint64_t base = (uint64_t)h * w.E + w.region_eoff[r];
        uwide sum = 0;
        for (uint32_t k = lane; k < K; k += 32) {
            const uint32_t j = support_at(members, off, rcs[warp], i, sites, k);
            if (j != UINT32_MAX) {
                const uwide p = w.e[base + (uint64_t)i * sites + j], back = w.e_prev[base + (uint64_t)j * sites + i];
                sum += (p * back + ((uwide)1 << (SHARE_BITS - 1))) >> SHARE_BITS;
            }
        }
        const wide total = warp_sum((wide)sum);
        if (lane == 0 && total != 0) {
            add_wide(w.trips + g, total);
        }
    }
}

// The cavity field (§15.3): a carried site's read less its own echo, `z_c −= release(B ℓ_c, 63)`, `B` its
// echo and `ℓ` the logits its face was formed from (data, no covector passes); at each unresolved site that
// carries one.
extern "C" __global__ void field_echo_apply(FieldWords w, int64_t *z) {
    const uint64_t cells = (uint64_t)w.T * w.A;
    for (uint64_t c = (uint64_t)blockIdx.x * blockDim.x + threadIdx.x; c < cells; c += (uint64_t)gridDim.x * blockDim.x) {
        const uint64_t t = c / w.A;
        if (w.unresolved[t] && w.echo_has[t]) {
            z[c] = fit64((wide)z[c] - rel((wide)w.echo_b[t] * (wide)w.echo_logits[c], SHARE_BITS), w.status);
        }
    }
}


// [definition; agent-inferred, November 1] **The pair contact is a complex product** (§15.1; the host's
// `tick`): contact `e < f/2` is `a_e + i a_(f/2+e)`, so `c = a b` as complex numbers, each part released to
// `2^(−16)`: `c_re = release(ar br − ai bi, 16)`, `c_im = release(ar bi + ai br, 16)`. Two ring faces then
// compose by adding their phases. One thread a site and a pair of contacts; `f` is even (the host admits no
// other declaration).
// [§16.34] Site `g`'s strand mate for pair contact `e` (the host's `strand_mate`): the site before it at an even `e`, the
// one after at an odd, within its region; `UINT64_MAX` past the region's ends.
__device__ __forceinline__ uint64_t strand_mate(const FieldWords &w, uint64_t g, uint64_t e) {
    const uint32_t r = w.site_region[g];
    const uint32_t sites = w.region_off[r + 1] - w.region_off[r], i = w.site_pos[g];
    if (e % 2 == 0) {
        return i > 0 ? g - 1 : UINT64_MAX;
    }
    return i + 1 < sites ? g + 1 : UINT64_MAX;
}

// The pair contact along the strand (§16.34, the host's tick): `c_g = a_g · b_mate`, zero without a mate.
extern "C" __global__ void field_pair(FieldWords w) {
    const uint32_t half = w.f / 2;
    const uint64_t cells = (uint64_t)w.T * half;
    for (uint64_t c = (uint64_t)blockIdx.x * blockDim.x + threadIdx.x; c < cells; c += (uint64_t)gridDim.x * blockDim.x) {
        const uint64_t t = c / half, e = c % half;
        const uint64_t re = t * w.f + e, im = re + half;
        const uint64_t s = strand_mate(w, t, e);
        const wide ar = w.pa[re], ai = w.pa[im];
        const wide br = s == UINT64_MAX ? 0 : w.pb[s * w.f + e], bi = s == UINT64_MAX ? 0 : w.pb[s * w.f + half + e];
        w.pc[re] = fit64(rel(ar * br - ai * bi, FACE_BITS), w.status);
        w.pc[im] = fit64(rel(ar * bi + ai * br, FACE_BITS), w.status);
    }
}

// Each unresolved site's face from its readout `z` (`[t][A]`): the masses `2^(z − peak)` on `2^(−62)`
// and their total.
extern "C" __global__ void field_face(FieldWords w, const int64_t *z, uint64_t *masses, uwide *totals) {
    const uint32_t lane = threadIdx.x & 31;
    const uint64_t warps = (uint64_t)gridDim.x * (blockDim.x >> 5);
    for (uint64_t t = ((uint64_t)blockIdx.x * blockDim.x + threadIdx.x) >> 5; t < w.T; t += warps) {
        if (!w.unresolved[t]) {
            continue;
        }
        const int64_t *zt = z + t * w.A;
        int64_t peak = INT64_MIN;
        for (uint32_t c = lane; c < w.A; c += 32) {
            peak = zt[c] > peak ? zt[c] : peak;
        }
        peak = warp_max_signed(peak);
        wide total = 0;
        for (uint32_t c = lane; c < w.A; c += 32) {
            const uint64_t m = below_one_face((wide)zt[c] - (wide)peak, w.face, w.digits);
            masses[t * w.A + c] = m;
            total += (wide)m;
        }
        total = warp_sum(total);
        if (lane == 0) {
            totals[t] = (uwide)total;
        }
    }
}

// -------------------------------------------------------------------------------------------
// the reverse

// The face's covector `p̂ − [· = class]` on `2^(−24)` at each unresolved site (`covector`), zero at a
// resolved one.
extern "C" __global__ void field_face_covector(FieldWords w, const uint64_t *masses, const uwide *totals, int64_t *dz) {
    const uint64_t cells = (uint64_t)w.T * w.A;
    for (uint64_t c = (uint64_t)blockIdx.x * blockDim.x + threadIdx.x; c < cells; c += (uint64_t)gridDim.x * blockDim.x) {
        const uint64_t t = c / w.A, cl = c % w.A;
        if (!w.unresolved[t]) {
            dz[c] = 0;
            continue;
        }
        const uwide total = totals[t];
        const uwide p = (((uwide)masses[c] << COVECTOR_BITS) + total / 2) / total;
        dz[c] = (int64_t)p - (cl == w.classes[t] ? ((int64_t)1 << COVECTOR_BITS) : 0);
    }
}

// [definition; agent-inferred, November 2, §16.23] The face covector weighed as its region's state in the joint code:
// `δz ← div_nearest(δz · m, K)` at an unresolved site whose region declares `m ≠ K` (the host's `returned_with`),
// checked as the host's `fit64`.
extern "C" __global__ void field_face_weigh(FieldWords w, const uint64_t *wm, const uint64_t *wk, int64_t *dz) {
    const uint64_t cells = (uint64_t)w.T * w.A;
    for (uint64_t c = (uint64_t)blockIdx.x * blockDim.x + threadIdx.x; c < cells; c += (uint64_t)gridDim.x * blockDim.x) {
        const uint64_t t = c / w.A;
        if (!w.unresolved[t] || wm[t] == wk[t]) {
            continue;
        }
        dz[c] = fit64(div_nearest((wide)dz[c] * (wide)wm[t], (wide)wk[t]), w.status);
    }
}

// [definition; agent-inferred, November 3, §16.26] The face read through the encoding (the host's `Field::tied`): at an
// unresolved site, `z[t][a] = rel(Σ_i E[a][i] y[t][i], 16) + c[a]`, `E` the encoding's rows at `enc`, `y` the lift on
// 2^(−16), `c` the class bias at `bias`. One thread a (site, class).
extern "C" __global__ void field_tied_face(FieldWords w, uint64_t enc, uint64_t bias, const int64_t *y, int64_t *z) {
    const uint64_t cells = (uint64_t)w.T * w.A;
    for (uint64_t c = (uint64_t)blockIdx.x * blockDim.x + threadIdx.x; c < cells; c += (uint64_t)gridDim.x * blockDim.x) {
        const uint64_t t = c / w.A, a = c % w.A;
        if (!w.unresolved[t]) {
            continue;
        }
        const int32_t *row = w.theta + enc + a * w.D;
        const int64_t *yt = y + t * w.D;
        wide sum = 0;
        for (uint32_t i = 0; i < w.D; i++) {
            sum += (wide)row[i] * (wide)yt[i];
        }
        z[c] = fit64(rel(sum, 16) + (wide)w.theta[bias + a], w.status);
    }
}

// The lift's covector (§16.26): `dy[t][i] = rel(Σ_a dz[t][a] E[a][i], 16)` at an unresolved site (zero elsewhere).
extern "C" __global__ void field_tied_back_y(FieldWords w, uint64_t enc, const int64_t *dz, int64_t *dy) {
    const uint64_t cells = (uint64_t)w.T * w.D;
    for (uint64_t c = (uint64_t)blockIdx.x * blockDim.x + threadIdx.x; c < cells; c += (uint64_t)gridDim.x * blockDim.x) {
        const uint64_t t = c / w.D, i = c % w.D;
        if (!w.unresolved[t]) {
            dy[c] = 0;
            continue;
        }
        wide sum = 0;
        for (uint32_t a = 0; a < w.A; a++) {
            sum += (wide)dz[t * w.A + a] * (wide)w.theta[enc + (uint64_t)a * w.D + i];
        }
        dy[c] = fit64(rel(sum, 16), w.status);
    }
}

// The encoding's covector from the face (§16.26): `g[enc + a D + i] += Σ_t rel(dz[t][a] y[t][i], 16)` over the
// unresolved sites, each term released to the encoding's covector grain before the integer sum (any order, the same
// bits). One thread an entry and a tile of `OUTER_TILE` sites, as `outer`.
extern "C" __global__ void field_tied_back_e(FieldWords w, wide *g, uint64_t enc, const int64_t *dz, const int64_t *y) {
    const uint64_t entries = (uint64_t)w.A * w.D;
    const uint64_t tiles = ((uint64_t)w.T + 63) / 64;
    for (uint64_t c = (uint64_t)blockIdx.x * blockDim.x + threadIdx.x; c < entries * tiles; c += (uint64_t)gridDim.x * blockDim.x) {
        const uint64_t entry = c % entries, tile = c / entries;
        const uint64_t a = entry / w.D, i = entry % w.D;
        const uint64_t from = tile * 64;
        const uint64_t to = from + 64 < w.T ? from + 64 : w.T;
        wide sum = 0;
        for (uint64_t t = from; t < to; t++) {
            if (!w.unresolved[t]) {
                continue;
            }
            sum += rel((wide)dz[t * w.A + a] * (wide)y[t * w.D + i], 16);
        }
        if (sum != 0) {
            add_wide(g + enc + entry, sum);
        }
    }
}

// [definition; agent-inferred, November 3, §16.24] A port's places take their coupling's covector, read on the host
// (`port_reading`): row `k` of `rows` written over the face covector of site `at[k]`.
extern "C" __global__ void field_face_set(FieldWords w, const uint32_t *at, const int64_t *rows, uint64_t count, int64_t *dz) {
    const uint64_t cells = count * w.A;
    for (uint64_t c = (uint64_t)blockIdx.x * blockDim.x + threadIdx.x; c < cells; c += (uint64_t)gridDim.x * blockDim.x) {
        dz[(uint64_t)at[c / w.A] * w.A + c % w.A] = rows[c];
    }
}

// `out[t][i] = release(Σ_o W[o][i] y[t][o], 24)` (`transposed`), the weight `rows × cols`; with
// `accumulate` it is added to `out[t][i]` (each addition checked as the host's `fit64`).
extern "C" __global__ void field_transposed(FieldWords w, uint64_t weight, uint32_t rows, uint32_t cols, const int64_t *y, uint64_t y_stride, int64_t *out, uint32_t accumulate, uint32_t only_unresolved) {
    const uint64_t cells = (uint64_t)w.T * cols;
    for (uint64_t c = (uint64_t)blockIdx.x * blockDim.x + threadIdx.x; c < cells; c += (uint64_t)gridDim.x * blockDim.x) {
        const uint64_t t = c / cols, i = c % cols;
        if (only_unresolved && !w.unresolved[t]) {
            continue;
        }
        const int64_t *yt = y + t * y_stride;
        wide sum = 0;
        for (uint32_t o = 0; o < rows; o++) {
            sum += (wide)w.theta[weight + (uint64_t)o * cols + i] * (wide)yt[o];
        }
        const int64_t v = fit64(rel(sum, MATERIAL_BITS), w.status);
        out[c] = accumulate ? fit64((wide)out[c] + (wide)v, w.status) : v;
    }
}

// The adjoint of the chart (`ratio_adjoint`) of each site's covector `cov`, added to `base`, lane by lane (§16.40, the host's
// `lane_adjoint`): `dst = base + (cov − r̂ ⟨r̂, cov⟩/W) / ‖r‖_rms` over each lane's `W` coordinates, one warp a site.
extern "C" __global__ void field_ratio_adjoint(FieldWords w, const int32_t *read, const wide *scale, const int64_t *cov, const int64_t *base, int64_t *dst, uint32_t only_unresolved) {
    const uint32_t lane = threadIdx.x & 31;
    const uint64_t warps = (uint64_t)gridDim.x * (blockDim.x >> 5);
    const uint32_t lw = w.D / w.lanes;
    for (uint64_t t = ((uint64_t)blockIdx.x * blockDim.x + threadIdx.x) >> 5; t < w.T; t += warps) {
        if (only_unresolved && !w.unresolved[t]) {
            for (uint32_t i = lane; i < w.D; i += 32) {
                dst[t * w.D + i] = base ? base[t * w.D + i] : 0;
            }
            continue;
        }
        for (uint32_t k = 0; k < w.lanes; ++k) {
            const uint64_t at = t * w.D + k * lw;
            const int32_t *rt = read + at;
            const int64_t *ct = cov + at;
            const wide s = scale[t * w.lanes + k];
            wide dot = 0;
            for (uint32_t i = lane; i < lw; i += 32) {
                dot += (wide)rt[i] * (wide)ct[i];
            }
            dot = warp_sum(dot);
            const wide mean = div_nearest(dot, (wide)lw);
            for (uint32_t i = lane; i < lw; i += 32) {
                const int64_t back = s == 0 ? 0 : fit64(div_nearest(((wide)ct[i] - rel(mean * (wide)rt[i], 2 * FACE_BITS)) << FACE_BITS, s), w.status);
                dst[at + i] = base ? fit64((wide)base[at + i] + (wide)back, w.status) : back;
            }
        }
    }
}

// The complex product's return (the host's `returned`): `δa = conj(b) δc`, `δb = conj(a) δc`, each part
// released to `2^(−16)`: `δa_re = release(br gr + bi gi, 16)`, `δa_im = release(br gi − bi gr, 16)`, and so
// for `δb` against `a`.
// [§16.34] Along the strand: `δa_g = conj(b_mate) δc_g`, and `δb_g = conj(a_p) δc_p` from the one site `p` whose mate `g` is
// (the site after it at an even `e`, before it at an odd), each zero where there is none.
extern "C" __global__ void field_pair_back(FieldWords w, const int64_t *dc, int64_t *da, int64_t *db) {
    const uint32_t half = w.f / 2;
    const uint64_t cells = (uint64_t)w.T * half;
    for (uint64_t c = (uint64_t)blockIdx.x * blockDim.x + threadIdx.x; c < cells; c += (uint64_t)gridDim.x * blockDim.x) {
        const uint64_t t = c / half, e = c % half;
        const uint64_t re = t * w.f + e, im = re + half;
        const uint64_t s = strand_mate(w, t, e);
        if (s == UINT64_MAX) {
            da[re] = 0;
            da[im] = 0;
        } else {
            const wide gr = dc[re], gi = dc[im];
            const wide br = w.pb[s * w.f + e], bi = w.pb[s * w.f + half + e];
            da[re] = fit64(rel(br * gr + bi * gi, FACE_BITS), w.status);
            da[im] = fit64(rel(br * gi - bi * gr, FACE_BITS), w.status);
        }
        // The site whose mate `t` is: its mate on the other side of `t`, read from `t` itself.
        const uint64_t p = strand_mate(w, t, e ^ 1);
        if (p == UINT64_MAX) {
            db[re] = 0;
            db[im] = 0;
        } else {
            const uint64_t pre = p * w.f + e, pim = pre + half;
            const wide gr = dc[pre], gi = dc[pim];
            const wide ar = w.pa[pre], ai = w.pa[pim];
            db[re] = fit64(rel(ar * gr + ai * gi, FACE_BITS), w.status);
            db[im] = fit64(rel(ar * gi - ai * gr, FACE_BITS), w.status);
        }
    }
}

// The wrapping sum of two drives' returns (the host's `i64` addition).
extern "C" __global__ void field_add(FieldWords w, const int64_t *p, int64_t *q, uint64_t cells) {
    for (uint64_t c = (uint64_t)blockIdx.x * blockDim.x + threadIdx.x; c < cells; c += (uint64_t)gridDim.x * blockDim.x) {
        q[c] = (int64_t)((uint64_t)p[c] + (uint64_t)q[c]);
    }
}

// `δỹ = U ⊙ δy` by head: both `[h][t][2n]`.
extern "C" __global__ void field_current_back(FieldWords w, const int64_t *dy, int64_t *dyh) {
    const uint64_t cells = (uint64_t)w.H * w.T * w.n;
    for (uint64_t c = (uint64_t)blockIdx.x * blockDim.x + threadIdx.x; c < cells; c += (uint64_t)gridDim.x * blockDim.x) {
        const uint32_t li = c % w.n;
        const uint64_t t = (c / w.n) % w.T;
        const uint32_t h = c / ((uint64_t)w.n * w.T);
        const uint32_t m = h * w.n + li;
        wide ur, ui;
        frame_of(w, t, h, li, &ur, &ui);
        const wide gr = dy[t * w.M2 + m], gi = dy[t * w.M2 + w.M + m];
        const uint64_t at = ((uint64_t)h * w.T + t) * w.span;
        dyh[at + li] = fit64(rel(ur * gr - ui * gi, MOVE_BITS), w.status);
        dyh[at + w.n + li] = fit64(rel(ui * gr + ur * gi, MOVE_BITS), w.status);
    }
}

// `v · 2^(−β)` (the host's `gained`): released `β` bits where the gain shifts down, `−β` exact
// doublings where it amplifies, refused past the carrier.
__device__ __forceinline__ wide gained(wide v, int32_t beta, uint32_t *st) {
    if (beta >= 0) {
        return rel(v, (uint32_t)beta);
    }
    // The host's `checked_mul` by `2^(−β)`: in range exactly when `−2^(127+β) ≤ v < 2^(127+β)`.
    const wide limit = (wide)((uwide)1 << (127 + beta));
    if (v >= limit || v < -limit) {
        atomicOr(st, REFUSED_CARRIER);
        return 0;
    }
    return v * ((wide)1 << -beta);
}

// [definition; agent-inferred, November 1] **The contact's return over one head's rows**, one warp a
// receiving site `i` (`Field::returned`, §14.2, §14.10, §14.11, §15.2). Over its support,
// `δp_k = ⟨δỹ_i, D ṽ_k⟩` (a crowd's the same against its decayed mean value), the row's mean `μ =
// release(Σ p δp, 63)`, `δz = release(ln2 release(p (δp − μ), 63), 30)` (the closure retired, §16.19),
// `δs = gained(δz, β)` held at the region block's dense address `[i][j]` for the columns. The
// word's row return (the probe role of the lock) `release(Σ δs D ŵ_j + Σ_C div_nearest(δs_C D W_C,
// |C|), 32)` is written to the framed chart slot; a crowd's share of the values and of the word (the key
// role: `δs_C (D ŵ_i |C| 2^g − D² W_C) / |C|²`) spreads over its members by the difference arrays `cv`,
// `cw`. A lane is a pair for the row's sums and the staged `δs`, and an entry of the span for the row's
// return.
#define REV_ROWS 4
extern "C" __global__ void __launch_bounds__(REV_ROWS * 32, 6) field_contact_rows(FieldWords w, uint32_t h, const int64_t *dyh, int64_t *ds, int64_t *dq) {
    __shared__ uint32_t stj[REV_ROWS][32];
    __shared__ int64_t dss[REV_ROWS][32];
    __shared__ wide dpcs[REV_ROWS][MAX_CROWD_SLOTS];
    __shared__ int64_t dsks[REV_ROWS][MAX_CROWD_SLOTS];
    __shared__ uint64_t cnts[REV_ROWS][32];
    __shared__ uint32_t crlo[REV_ROWS][32], crhi[REV_ROWS][32], crlv[REV_ROWS][32];
    __shared__ Divisor cdiv[REV_ROWS][32], cdiv2[REV_ROWS][32];
    __shared__ RowCls rcs[REV_ROWS];
    const uint32_t warp = threadIdx.x >> 5, lane = threadIdx.x & 31;
    const uint32_t S = w.span, n = w.n, classes = w.nclasses;
    const uint32_t parts = span_parts(S);
    const bool active = lane < S * parts;
    const uint32_t entry = lane % S, part = lane / S, m = entry % n;
    const wide ln2 = (wide)(((uwide)w.ln2_hi << 64) | (uwide)w.ln2_lo);
    const bool still = skinless(w, h);
    const uint32_t g0 = still ? 0 : MOVE_BITS;
    const uint64_t rows1 = (uint64_t)w.T + w.R;
    for (uint64_t g = ((uint64_t)blockIdx.x * blockDim.x + threadIdx.x) >> 5; g < w.T; g += (uint64_t)gridDim.x * (blockDim.x >> 5)) {
        const uint64_t hg = (uint64_t)h * w.T + g;
        if (skipped_row(w, g)) {
            if (lane < S) {
                const uint32_t mc = h * n + lane % n;
                const uint64_t slot = g * w.M2 + (lane < n ? mc : w.M + mc);
                w.dp[slot] = 0;
                dq[slot] = 0;
            }
            continue;
        }
        const uint32_t r = w.site_region[g];
        const uint32_t i = w.site_pos[g];
        const uint64_t first = w.region_off[r];
        const uint32_t sites = w.region_off[r + 1] - (uint32_t)first;
        const uint32_t *members = w.members + (uint64_t)h * w.T + first;
        const uint32_t *off = w.class_off + ((uint64_t)h * w.R + r) * (2 * classes + 1);
        const uint32_t c = w.cls[hg];
        const uint32_t K = row_prepare(w, hg, off, rcs[warp], lane);
        const uint64_t *e = w.e + (uint64_t)h * w.E + w.region_eoff[r] + (uint64_t)i * sites;
        int64_t *dsr = ds + w.region_eoff[r] + (uint64_t)i * sites;
        wide *dpr = w.dpb + w.region_eoff[r] + (uint64_t)i * sites;
        const int64_t *dyi = dyh + hg * S;
        const int64_t *values = w.vf + ((uint64_t)h * w.T + first) * S;
        const int64_t *words = w.qf + ((uint64_t)h * w.T + first) * S;
        const uint64_t prow0 = (uint64_t)h * rows1 + first + r;
        const wide *swp = w.sw + prow0 * S;
        const wide *svp = w.sv + prow0 * S;
        const uint64_t *scp = w.sc + prow0;
        const uint32_t nslots = rcs[warp].open ? 0 : crowd_slots(sites);
        const wide temper = temper_of(w, h, rcs[warp].open != 0);
        const int64_t *sbr = w.sb + (uint64_t)h * w.E + w.region_eoff[r] + (uint64_t)i * sites;
        // The pair's covector `⟨δỹ_i, D ṽ_j⟩` on `2^(−40)`.
        const auto pair_dp = [&](uint32_t j, uint32_t gap) -> wide {
            const int64_t *vj = values + (uint64_t)j * S;
            wide dp = 0;
            for (uint32_t x = 0; x < S; x++) {
                dp += (wide)dyi[x] * carried_ij(w, h, x % n, g, first + j, gap, vj[x]);
            }
            return dp;
        };
        // The same for a head of eight modes, from vector rows: the source's sixteen values as eight 16-octet loads
        // and its skins as two (`pair_score8`).
        const bool eight = w.n == 8;
        const bool still_h = skinless(w, h), paced_h = paced_at(w, h, g);
        const auto pair_dp8 = [&](uint32_t j, uint32_t gap) -> wide {
            const longlong2 *v2 = reinterpret_cast<const longlong2 *>(values + (uint64_t)j * S);
            uint32_t dec[8];
            if (still_h) {
#pragma unroll
                for (int l = 0; l < 8; l++) {
                    dec[l] = 1;
                }
            } else if (paced_h) {
#pragma unroll
                for (int l = 0; l < 8; l++) {
                    dec[l] = (uint32_t)skin_ij(w, h, l, g, first + j, gap);
                }
            } else {
                const uint4 *d4 = reinterpret_cast<const uint4 *>(w.decay_t + ((uint64_t)h * w.dreach + gap) * 8);
                const uint4 d0 = d4[0], d1 = d4[1];
                dec[0] = d0.x; dec[1] = d0.y; dec[2] = d0.z; dec[3] = d0.w;
                dec[4] = d1.x; dec[5] = d1.y; dec[6] = d1.z; dec[7] = d1.w;
            }
            wide dp = 0;
#pragma unroll
            for (int q = 0; q < 8; q++) {
                const longlong2 t = v2[q];
                dp += (wide)dyi[2 * q] * (wide)(still_h ? t.x : carry_d(dec[(2 * q) & 7], t.x));
                dp += (wide)dyi[2 * q + 1] * (wide)(still_h ? t.y : carry_d(dec[(2 * q + 1) & 7], t.y));
            }
            return dp;
        };
        // The crowds: counts, places and their divisors.
        {
            uint64_t count = 0;
            uint32_t lo = 0, hi_ = 0, lv = 0;
            if (lane < nslots && crowd_at(i, sites, lane, &lo, &hi_, &lv)) {
                count = scp[hi_ + 1] - scp[lo];
            }
            cnts[warp][lane] = count;
            crlo[warp][lane] = lo;
            crhi[warp][lane] = hi_;
            crlv[warp][lane] = lv;
            if (count != 0) {
                cdiv[warp][lane] = divisor_of(count);
                cdiv2[warp][lane] = divisor_of(count * count);
            }
        }
        __syncwarp();
        // Pass A: the weighted sum of the pairs' and crowds' covectors.
        wide weighted = 0;
        for (uint32_t k = lane; k < K; k += 32) {
            const uint32_t j = support_at(members, off, rcs[warp], i, sites, k);
            if (j == UINT32_MAX) {
                continue;
            }
            const wide p = (wide)e[j];
            const uint32_t gap = j > i ? j - i : i - j;
            const wide dpj = eight ? pair_dp8(j, gap) : pair_dp(j, gap);
            dpr[j] = dpj;
            weighted += p * dpj;
        }
        if (cnts[warp][lane] != 0) {
            const uint32_t lo = crlo[warp][lane], hi_ = crhi[warp][lane], lv = crlv[warp][lane];
            wide sum = 0;
            for (uint32_t x = 0; x < S; x++) {
                sum += (wide)dyi[x] * carried_wide_ij(w, h, x % n, g, octave_edge(g, lv, lo > i), (uint32_t)1 << lv, svp[(uint64_t)(hi_ + 1) * S + x] - svp[(uint64_t)lo * S + x]);
            }
            const wide dpc = div_nearest_by(sum, cdiv[warp][lane]);
            dpcs[warp][lane] = dpc;
            weighted += (wide)w.ce[hg * w.slots + lane] * dpc;
        }
        const wide mean = rel(warp_sum(weighted), SHARE_BITS);
        // The comparison of a term `p` (its covector `dpk`): the face's.
        const auto compare = [&](wide p, wide dpk) -> wide { return rel(ln2 * rel(p * (dpk - mean), SHARE_BITS), MOVE_BITS); };
        // Pass B: δs over the pairs, in chunks of 32 into the warp's shared chunk, whose sum over the word is
        // read with the lanes over the span's entries (the probe role: `δs D ŵ_j`).
        wide sum = 0;
        // The temperature's covector (§15.10): `δT[h][kind] += release(δz S, 16)` over the row's sources and crowds,
        // each released alone and summed (an exact integer sum, the lanes' partials added over the warp).
        wide tacc = 0;
        // The covector's magnitude near and far (§16.20), where read.
        wide near_ds = 0, far_ds = 0;
        for (uint32_t k0 = 0; k0 < K; k0 += 32) {
            const uint32_t k = k0 + lane;
            const uint32_t j = k < K ? support_at(members, off, rcs[warp], i, sites, k) : UINT32_MAX;
            int64_t dsv = 0;
            if (j != UINT32_MAX) {
                const wide dzj = compare((wide)e[j], dpr[j]);
                tacc += rel(dzj * (wide)sbr[j], FACE_BITS);
                const wide dz = rel(temper * dzj, MATERIAL_BITS);
                if ((dz < 0 ? -dz : dz) >> min(w.dsbits, 63u) != 0) {
                    atomicOr(w.status, REFUSED_CARRIER);
                }
                dsv = (int64_t)dz;
                dsr[j] = dsv;
                const wide mag = dz < 0 ? -dz : dz;
                if ((j > i ? j - i : i - j) < NEAR) {
                    near_ds += mag;
                } else {
                    far_ds += mag;
                }
            }
            dss[warp][lane] = dsv;
            stj[warp][lane] = j;
            __syncwarp();
            if (active) {
                for (uint32_t jj = part; jj < 32; jj += parts) {
                    const uint32_t jx = stj[warp][jj];
                    if (jx != UINT32_MAX) {
                        sum += (wide)dss[warp][jj] * skin_raw(w, h, m, g, first + jx, jx > i ? jx - i : i - jx) * (wide)words[(uint64_t)jx * S + entry];
                    }
                }
            }
            __syncwarp();
        }
        // The crowds' δs, then their share of the row's return and of the values' and the word's member
        // returns through the difference arrays.
        if (cnts[warp][lane] != 0) {
            const wide dzc = compare((wide)w.ce[hg * w.slots + lane], dpcs[warp][lane]);
            const uint32_t clo = crlo[warp][lane], chi = crhi[warp][lane], clv = crlv[warp][lane];
            const int64_t cs = crowd_base(w, h, w.pq + ((uint64_t)h * w.T + g) * S, swp + (uint64_t)clo * S, swp + (uint64_t)(chi + 1) * S, cnts[warp][lane], clv, g, clo > i);
            tacc += rel(dzc * (wide)cs, FACE_BITS);
            const wide dz = rel(temper * dzc, MATERIAL_BITS);
            if ((dz < 0 ? -dz : dz) >> min(w.dsbits, 63u) != 0) {
                atomicOr(w.status, REFUSED_CARRIER);
            }
            dsks[warp][lane] = (int64_t)dz;
            if (w.cds != nullptr) {
                w.cds[hg * w.slots + lane] = (int64_t)dz;
            }
            far_ds += dz < 0 ? -dz : dz;
        }
        if (w.dsshare != nullptr) {
            near_ds = warp_sum(near_ds);
            far_ds = warp_sum(far_ds);
            if (lane == 0) {
                add_wide(w.dsshare + 2 * h, near_ds);
                add_wide(w.dsshare + 2 * h + 1, far_ds);
            }
        }
        tacc = warp_sum(tacc);
        if (lane == 0 && tacc != 0) {
            // Into the temperature's own chart (§16.12): `δℓ = release(δT · release(T ln 2, 30), 24)`, the row's.
            add_wide(w.gcov + w.temper_at + 2 * h + (rcs[warp].open ? 1 : 0), temper_chain(w, temper, tacc));
        }
        __syncwarp();
        if (active) {
            for (uint32_t jj = part; jj < nslots; jj += parts) {
                const uint64_t count = cnts[warp][jj];
                if (count == 0) {
                    continue;
                }
                const uint32_t lo = crlo[warp][jj], hi_ = crhi[warp][jj], lv = crlv[warp][jj];
                const wide d = skin_raw(w, h, m, g, octave_edge(g, lv, lo > i), (uint32_t)1 << lv);
                const wide dsk = dsks[warp][jj];
                const wide wsum = swp[(uint64_t)(hi_ + 1) * S + entry] - swp[(uint64_t)lo * S + entry];
                sum += div_nearest_by(dsk * d * wsum, cdiv[warp][jj]);
                // The key's bracket released by the skin's bits once, its product by the covector checked.
                const wide bracket = rel(((d * (wide)w.pq[((uint64_t)h * w.T + g) * S + entry] * (wide)count) << g0) - d * d * wsum, g0);
                wide prod = 0;
                if (!mul_fits(dsk, bracket, &prod)) {
                    atomicOr(w.status, REFUSED_KEY);
                }
                const wide pw = div_nearest_by(prod, cdiv2[warp][jj]);
                add_wide(w.cw + (first + r + lo) * S + entry, pw);
                add_wide(w.cw + (first + r + hi_ + 1) * S + entry, -pw);
                const wide pv = div_nearest_by((wide)w.ce[hg * w.slots + jj] * carried_ij(w, h, m, g, octave_edge(g, lv, lo > i), (uint32_t)1 << lv, dyi[entry]), cdiv[warp][jj]);
                add_wide(w.cv + (first + r + lo) * S + entry, pv);
                add_wide(w.cv + (first + r + hi_ + 1) * S + entry, -pv);
            }
        }
        sum = parts_sum(active ? sum : 0, S, parts);
        if (lane < S) {
            const uint32_t mc = h * n + lane % n;
            const uint64_t slot = g * w.M2 + (lane < n ? mc : w.M + mc);
            const int64_t probe_role = fit64(rel(sum, CONTACT_BACK + g0), w.status);
            // The probe role goes to the probe chart's covector, the key role (the columns) to the key's (§16.19).
            w.dp[slot] = probe_role;
            dq[slot] = 0;
        }
        __syncwarp();
    }
}

// [definition; agent-inferred, November 1] **The word's column return and the values' over one head**
// (`Field::returned`, §15.2), one warp a source site `j` over its receivers (the support is directional:
// `j` is heard by its near field and, where `j` is definite, by every member of its class):
// `δw̃_j += release(Σ_i δs_ij ((D q_i) 2^g − D² q_j), 32 + 2g)` added to the rows' return in its framed
// chart slot (the key role of the lock), and `δṽ_j = release(Σ_i p_ij D δỹ_i, 63)`, the lanes over the
// span's entries (a lane an entry and a part of the receivers), `p_ij` and `δs_ij` read at the region
// block's dense address `[i][j]`.
extern "C" __global__ void __launch_bounds__(CONTACT_ROWS * 32) field_contact_columns(FieldWords w, uint32_t h, const int64_t *dyh, const int64_t *ds, int64_t *dq, int64_t *dv) {
    const uint32_t lane = threadIdx.x & 31;
    const uint32_t S = w.span, n = w.n, classes = w.nclasses;
    const uint32_t parts = span_parts(S);
    const uint32_t entry = lane % S, part = lane / S, m = entry % n;
    const bool still = skinless(w, h);
    const uint32_t g0 = still ? 0 : MOVE_BITS;
    for (uint64_t g = ((uint64_t)blockIdx.x * blockDim.x + threadIdx.x) >> 5; g < w.T; g += (uint64_t)gridDim.x * (blockDim.x >> 5)) {
        const uint32_t r = w.site_region[g];
        const uint32_t j = w.site_pos[g];
        const uint64_t first = w.region_off[r];
        const uint32_t sites = w.region_off[r + 1] - (uint32_t)first;
        const uint32_t *members = w.members + (uint64_t)h * w.T + first;
        const uint32_t *off = w.class_off + ((uint64_t)h * w.R + r) * (2 * classes + 1);
        const uint32_t c = w.cls[(uint64_t)h * w.T + g];
        const uint32_t *poff = w.poff + ((uint64_t)h * w.R + r) * (classes + 1);
        const uint32_t *pmem = w.pmem + ((uint64_t)h * w.T + first) * probe_stride(w);
        const uint32_t *olist = w.olist + w.ostart[r];
        // A source with no key is in no receiver's support (§16.20).
        const uint32_t K = keyed_site(w, g) ? receiver_len(off, poff, w.ostart[r + 1] - w.ostart[r], c, definite_site(w, g)) : 0;
        const uint64_t *e = w.e + (uint64_t)h * w.E + w.region_eoff[r] + j;
        const int64_t *dsc = ds + w.region_eoff[r] + j;
        const int64_t *words = w.qf + ((uint64_t)h * w.T + first) * S;
        const int64_t *dyr = dyh + ((uint64_t)h * w.T + first) * S;
        wide sk = 0, sv = 0;
        if (part < parts) {
            for (uint32_t k = part; k < K; k += parts) {
                const uint32_t i = receiver_at(members, off, pmem, poff, olist, c, j, sites, k);
                if (i == UINT32_MAX || skipped_row(w, first + i)) {
                    continue;
                }
                const uint64_t at = (uint64_t)i * sites;
                const uint32_t gap = j > i ? j - i : i - j;
                const wide dec = skin_raw(w, h, m, first + i, g, gap);
                // The key's bracket released by the skin's bits once (the probe's grain), then by the covector,
                // against the receiver's probe (§16.19).
                const int64_t probe_i = w.pq[((uint64_t)h * w.T + first + i) * S + entry];
                sk += (wide)dsc[at] * rel(((dec * (wide)probe_i) << g0) - dec * dec * (wide)words[(uint64_t)j * S + entry], g0);
                sv += (wide)e[at] * carried_ij(w, h, m, first + i, g, gap, dyr[(uint64_t)i * S + entry]);
            }
        }
        sk = parts_sum(part < parts ? sk : 0, S, parts);
        sv = parts_sum(part < parts ? sv : 0, S, parts);
        if (lane < S) {
            const uint32_t mc = h * n + lane % n;
            const uint64_t slot = g * w.M2 + (lane < n ? mc : w.M + mc);
            dq[slot] = fit64((wide)dq[slot] + rel(sk, CONTACT_BACK + g0), w.status);
            dv[slot] = fit64(rel(sv, SHARE_BITS), w.status);
        }
    }
}

// The crowds' members' share (§14.10): the difference arrays `cv`, `cw` summed over the places (the
// host's `spread`), added at the definite sites only, each released as its own sum:
// `dv = fit64(dv + release(Σ cv, 63))`, `dq = fit64(dq + release(Σ cw, 32 + 2g))`. One thread an entry of
// the span and a region, each over its region's sites in order.
extern "C" __global__ void field_spread(FieldWords w, uint32_t h, int64_t *dq, int64_t *dv) {
    // A block a region: the span's entries across the block's threads, a thread's chunk of the region's sites
    // (`blockDim / span` chunks) summed, the chunks' sums scanned, and each chunk's prefix walked again to the
    // outputs. The prefix sums are exact integers (the ring `Z/2^128`), so any chunking gives the same bits.
    __shared__ wide psv[SPREAD_THREADS], psw[SPREAD_THREADS];
    const bool still = skinless(w, h);
    const uint32_t g0 = still ? 0 : MOVE_BITS;
    const uint32_t S = w.span;
    const uint32_t nchunk = blockDim.x / S;
    const uint32_t x = threadIdx.x % S, ck = threadIdx.x / S;
    const bool live = ck < nchunk;
    for (uint32_t r = blockIdx.x; r < w.R; r += gridDim.x) {
        const uint64_t first = w.region_off[r];
        const uint32_t sites = w.region_off[r + 1] - (uint32_t)first;
        const uint32_t len = (sites + nchunk - 1) / nchunk;
        const uint32_t lo = ck * len, hi = min(sites, lo + len);
        wide sv = 0, sw = 0;
        if (live) {
            for (uint32_t t = lo; t < hi; t++) {
                const uint64_t row = first + r + t;
                sv += w.cv[row * S + x];
                sw += w.cw[row * S + x];
            }
            psv[threadIdx.x] = sv;
            psw[threadIdx.x] = sw;
        }
        __syncthreads();
        if (live) {
            wide runv = 0, runw = 0;
            for (uint32_t c = 0; c < ck; c++) {
                runv += psv[c * S + x];
                runw += psw[c * S + x];
            }
            for (uint32_t t = lo; t < hi; t++) {
                const uint64_t row = first + r + t;
                runv += w.cv[row * S + x];
                runw += w.cw[row * S + x];
                if (definite_site(w, first + t)) {
                    const uint32_t m = h * w.n + x % w.n;
                    const uint64_t slot = (first + t) * w.M2 + (x < w.n ? m : w.M + m);
                    dq[slot] = fit64((wide)dq[slot] + rel(runw, CONTACT_BACK + g0), w.status);
                    dv[slot] = fit64((wide)dv[slot] + rel(runv, SHARE_BITS), w.status);
                }
            }
        }
        __syncthreads();
    }
}

// [measurement; agent-inferred, November 2] **A held read's rows by where their mass lies** (the host's
// `Field::held_rows`): one warp a head and an unresolved site, over a kept tick's shares at the dense address:
// the rows, the shares of the question group (a definite site before the region's answer start `qstart[r]`), of
// the near field's sources that are not definite, and of the rest (with the crowds'), and the question group's
// current `Σ release(p Σ_x |D ṽ_x|, 63)`; the question's far part (past the near field), and where its collision
// `C = Σ release(p², 63)` is positive the row's effective count `((Σ p)² >> 55) / C` on `2^(−8)` and the row counted.
// The nine sums of a cell `[tick · H + h]` are added to `acc` (exact integers), the ninth the near field's definite
// sources at or past the answer start (§16.31).
extern "C" __global__ void field_held_rows(FieldWords w, const uint32_t *qstart, uint32_t tick, wide *acc) {
    const uint32_t lane = threadIdx.x & 31;
    const uint32_t S = w.span, n = w.n;
    const uint64_t rows = (uint64_t)w.H * w.T;
    for (uint64_t hg = ((uint64_t)blockIdx.x * blockDim.x + threadIdx.x) >> 5; hg < rows; hg += (uint64_t)gridDim.x * (blockDim.x >> 5)) {
        const uint32_t h = hg / w.T;
        const uint64_t g = hg % w.T;
        if (!w.unresolved[g]) {
            continue;
        }
        const uint32_t r = w.site_region[g];
        const uint64_t first = w.region_off[r];
        const uint32_t sites = w.region_off[r + 1] - (uint32_t)first, i = w.site_pos[g];
        const uint32_t question = qstart[r];
        const uint64_t *erow = w.e + (uint64_t)h * w.E + w.region_eoff[r] + (uint64_t)i * sites;
        const int64_t *values = w.vf + ((uint64_t)h * w.T + first) * S;
        wide q = 0, soft = 0, other = 0, cur = 0, far = 0, coll = 0, neard = 0;
        for (uint32_t j = lane; j < sites; j += 32) {
            const wide p = (wide)erow[j];
            if (p == 0) {
                continue;
            }
            const uint32_t gap = j > i ? j - i : i - j;
            const bool definite = definite_site(w, first + j);
            if (definite && j < question) {
                q += p;
                if (gap >= NEAR) {
                    far += p;
                    coll += rel(p * p, SHARE_BITS);
                }
                wide current = 0;
                for (uint32_t x = 0; x < S; x++) {
                    const wide v = carried_ij(w, h, x % n, g, first + j, gap, values[(uint64_t)j * S + x]);
                    current += v < 0 ? -v : v;
                }
                cur += rel(p * current, SHARE_BITS);
            } else if (gap < NEAR && !definite) {
                soft += p;
            } else if (gap < NEAR) {
                neard += p;
            } else {
                other += p;
            }
        }
        if (definite_site(w, g)) {
            for (uint32_t slot = lane; slot < crowd_slots(sites); slot += 32) {
                other += (wide)w.ce[hg * w.slots + slot];
            }
        }
        q = warp_sum(q);
        soft = warp_sum(soft);
        other = warp_sum(other);
        cur = warp_sum(cur);
        far = warp_sum(far);
        coll = warp_sum(coll);
        neard = warp_sum(neard);
        if (lane == 0) {
            wide *cell = acc + ((uint64_t)tick * w.H + h) * 9;
            add_wide(cell, 1);
            add_wide(cell + 1, q);
            add_wide(cell + 2, soft);
            add_wide(cell + 3, other);
            add_wide(cell + 4, cur);
            add_wide(cell + 5, far);
            if (coll > 0) {
                const uwide f = (uwide)far;
                add_wide(cell + 6, (wide)(((f * f) >> (SHARE_BITS - 8)) / (uwide)coll));
                add_wide(cell + 7, 1);
            }
            add_wide(cell + 8, neard);
        }
    }
}

// [measurement; agent-inferred, November 2] **A held answer row's current by where it comes from** (the host's
// `Field::row_currents`, §16.21): one warp a head and an unresolved site, over a kept tick's shares at the dense address:
// the framed current's part from the question past the near field (a definite site before `qstart[r]` at `|i − j| ≥
// NEAR`) and from the near field (every source at `|i − j| < NEAR`), each entry `Σ release(p D ṽ_j, 63)` over the head's
// `S` reals, and the row's largest share. `far[(h T + g) S + x]`, `near` alike, `top[h T + g]`.
#define ROW_CURRENT_SPAN 32
extern "C" __global__ void field_row_currents(FieldWords w, const uint32_t *qstart, wide *far, wide *near, wide *rest, uint64_t *top) {
    const uint32_t lane = threadIdx.x & 31;
    const uint32_t S = w.span, n = w.n;
    const uint64_t rows = (uint64_t)w.H * w.T;
    for (uint64_t hg = ((uint64_t)blockIdx.x * blockDim.x + threadIdx.x) >> 5; hg < rows; hg += (uint64_t)gridDim.x * (blockDim.x >> 5)) {
        const uint32_t h = hg / w.T;
        const uint64_t g = hg % w.T;
        if (!w.unresolved[g] || S > ROW_CURRENT_SPAN) {
            continue;
        }
        const uint32_t r = w.site_region[g];
        const uint64_t first = w.region_off[r];
        const uint32_t sites = w.region_off[r + 1] - (uint32_t)first, i = w.site_pos[g];
        const uint32_t question = qstart[r];
        const uint64_t *erow = w.e + (uint64_t)h * w.E + w.region_eoff[r] + (uint64_t)i * sites;
        const int64_t *values = w.vf + ((uint64_t)h * w.T + first) * S;
        wide f[ROW_CURRENT_SPAN], m[ROW_CURRENT_SPAN], o[ROW_CURRENT_SPAN];
        for (uint32_t x = 0; x < S; x++) {
            f[x] = 0;
            m[x] = 0;
            o[x] = 0;
        }
        int64_t best = 0;
        for (uint32_t j = lane; j < sites; j += 32) {
            const wide p = (wide)erow[j];
            if (p == 0) {
                continue;
            }
            best = (int64_t)p > best ? (int64_t)p : best;
            const uint32_t gap = j > i ? j - i : i - j;
            const bool is_near = gap < NEAR;
            const bool is_far = !is_near && definite_site(w, first + j) && j < question;
            for (uint32_t x = 0; x < S; x++) {
                const wide v = rel(p * carried_ij(w, h, x % n, g, first + j, gap, values[(uint64_t)j * S + x]), SHARE_BITS);
                if (is_near) {
                    m[x] += v;
                } else if (is_far) {
                    f[x] += v;
                } else {
                    o[x] += v;
                }
            }
        }
        for (uint32_t x = 0; x < S; x++) {
            f[x] = warp_sum(f[x]);
            m[x] = warp_sum(m[x]);
            o[x] = warp_sum(o[x]);
        }
        best = warp_max_signed(best);
        if (lane == 0) {
            for (uint32_t x = 0; x < S; x++) {
                far[hg * S + x] = f[x];
                near[hg * S + x] = m[x];
                rest[hg * S + x] = o[x];
            }
            top[hg] = (uint64_t)best;
        }
    }
}

// Undo the frame on a chart's covector: `δq = conj(U) ⊙ δq̃` (`[t][2M]`).
extern "C" __global__ void field_unframe(FieldWords w, int64_t *chart) {
    const uint64_t cells = (uint64_t)w.T * w.M;
    for (uint64_t c = (uint64_t)blockIdx.x * blockDim.x + threadIdx.x; c < cells; c += (uint64_t)gridDim.x * blockDim.x) {
        const uint64_t t = c / w.M;
        const uint32_t m = c % w.M;
        wide ur, ui;
        frame_of(w, t, m / w.n, m % w.n, &ur, &ui);
        const wide gr = chart[t * w.M2 + m], gi = chart[t * w.M2 + w.M + m];
        chart[t * w.M2 + m] = fit64(rel(ur * gr + ui * gi, MOVE_BITS), w.status);
        chart[t * w.M2 + w.M + m] = fit64(rel(ur * gi - ui * gr, MOVE_BITS), w.status);
    }
}

// A family's covector `g[o][i] += Σ_t y_t[o] x_t[i]` over the batch's sites (`outer_sum`); with no
// `x`, the bias `g[o] += Σ_t y_t[o]`. An integer sum: the host's bits in any order.
//
// [agent-inferred, November 1] One thread an entry and a tile of `OUTER_TILE` sites, its partial
// added to the entry by the ring's atomic step (`add_wide`). (The first realization gave one thread
// an entry and every site of the batch, so a bias of 32 entries was summed by 32 threads over
// thousands of sites each.)
#define OUTER_TILE 64
template <typename X>
__device__ void outer(const FieldWords &w, wide *g, uint64_t at, uint32_t rows, uint32_t cols, const int64_t *y, uint64_t y_stride, const X *x, uint64_t x_stride, uint32_t only_unresolved) {
    const uint64_t entries = (uint64_t)rows * (x ? cols : 1);
    const uint64_t tiles = ((uint64_t)w.T + OUTER_TILE - 1) / OUTER_TILE;
    for (uint64_t c = (uint64_t)blockIdx.x * blockDim.x + threadIdx.x; c < entries * tiles; c += (uint64_t)gridDim.x * blockDim.x) {
        const uint64_t entry = c % entries, tile = c / entries;
        const uint64_t o = x ? entry / cols : entry, i = x ? entry % cols : 0;
        const uint64_t from = tile * OUTER_TILE;
        const uint64_t to = from + OUTER_TILE < w.T ? from + OUTER_TILE : w.T;
        wide sum = 0;
        for (uint64_t t = from; t < to; t++) {
            if (only_unresolved && !w.unresolved[t]) {
                continue;
            }
            const wide yv = y[t * y_stride + o];
            sum += x ? yv * (wide)x[t * x_stride + i] : yv;
        }
        if (sum != 0) {
            add_wide(g + at + entry, sum);
        }
    }
}

extern "C" __global__ void field_outer_x32(FieldWords w, wide *g, uint64_t at, uint32_t rows, uint32_t cols, const int64_t *y, uint64_t y_stride, const int32_t *x, uint64_t x_stride, uint32_t only_unresolved) {
    outer<int32_t>(w, g, at, rows, cols, y, y_stride, x, x_stride, only_unresolved);
}

extern "C" __global__ void field_outer_x64(FieldWords w, wide *g, uint64_t at, uint32_t rows, uint32_t cols, const int64_t *y, uint64_t y_stride, const int64_t *x, uint64_t x_stride, uint32_t only_unresolved) {
    outer<int64_t>(w, g, at, rows, cols, y, y_stride, x, x_stride, only_unresolved);
}

// The host's refusal of an outer sum, region by region: `Σ_t max|y_t| max|x_t| ≥ 2^126` refused
// (`outer_sum`'s bound, read per region as the host reads each region's sum). One block a region.
template <typename X>
__device__ void outer_bound(const FieldWords &w, uint32_t rows, uint32_t cols, const int64_t *y, uint64_t y_stride, const X *x, uint64_t x_stride, uint32_t only_unresolved) {
    __shared__ uwide part[32];
    const uint32_t r = blockIdx.x;
    if (r >= w.R) {
        return;
    }
    uwide bound = 0;
    bool over = false;
    for (uint64_t t = w.region_off[r] + threadIdx.x; t < w.region_off[r + 1]; t += blockDim.x) {
        if (only_unresolved && !w.unresolved[t]) {
            continue;
        }
        uint64_t ym = 0, xm = 0;
        for (uint32_t o = 0; o < rows; o++) {
            const uint64_t m = mag64(y[t * y_stride + o]);
            ym = m > ym ? m : ym;
        }
        for (uint32_t i = 0; i < cols; i++) {
            const uint64_t m = mag64((int64_t)x[t * x_stride + i]);
            xm = m > xm ? m : xm;
        }
        const uwide term = (uwide)ym * (uwide)xm;
        over = over || bound + term < bound || bound + term >= ((uwide)1 << 126);
        bound += term;
    }
    // Each thread's partial is below 2^126 unless it is over; the block's sum of 32 such is read in
    // the ring and compared, any partial over refusing.
    const uint32_t lane = threadIdx.x & 31, warp = threadIdx.x >> 5;
    uwide v = bound;
    uint32_t flag = over ? 1u : 0u;
    for (int o = 16; o > 0; o >>= 1) {
        const uwide u = shfl_wide(v, o);
        flag |= __shfl_xor_sync(0xffffffffu, flag, o);
        flag |= (v + u < v) ? 1u : 0u;
        v += u;
    }
    if (lane == 0) {
        part[warp] = v;
        if (flag || v >= ((uwide)1 << 126)) {
            atomicOr(w.status, REFUSED_CARRIER);
        }
    }
    __syncthreads();
    if (threadIdx.x == 0) {
        uwide s = 0;
        for (uint32_t k = 0; k < (blockDim.x >> 5); k++) {
            if (s + part[k] < s || s + part[k] >= ((uwide)1 << 126)) {
                atomicOr(w.status, REFUSED_CARRIER);
            }
            s += part[k];
        }
    }
}

extern "C" __global__ void field_outer_bound_x32(FieldWords w, uint32_t rows, uint32_t cols, const int64_t *y, uint64_t y_stride, const int32_t *x, uint64_t x_stride, uint32_t only_unresolved) {
    outer_bound<int32_t>(w, rows, cols, y, y_stride, x, x_stride, only_unresolved);
}

extern "C" __global__ void field_outer_bound_x64(FieldWords w, uint32_t rows, uint32_t cols, const int64_t *y, uint64_t y_stride, const int64_t *x, uint64_t x_stride, uint32_t only_unresolved) {
    outer_bound<int64_t>(w, rows, cols, y, y_stride, x, x_stride, only_unresolved);
}

// An encoding's covector: each row's `Σ_t release(w_t dx_t, 16)` over the sites that opened on it,
// `w_t` the site's share of that row (`2^16` where it opened on the row itself, so the term is `dx_t`
// exactly; a carried site's shares of its mixture, `Field::opening_return`); `E`'s by their own class,
// `E₋`'s by the site before them, `E₊`'s by the site after; one launch each, `base` the encoding's
// offset), the entries sorted by row (`rows_sites`, `rows_shares`) and cut into segments of at most
// `OUTER_TILE` of one row (`segments`, each its row, first and end in `rows_sites`), one thread a
// segment and a column, its partial added by the ring's atomic step.
extern "C" __global__ void field_encoding(FieldWords w, wide *g, const int64_t *dx, const uint32_t *rows_sites, const uint32_t *rows_shares, const uint32_t *segments, uint32_t count, uint64_t base) {
    const uint64_t cells = (uint64_t)count * w.D;
    for (uint64_t c = (uint64_t)blockIdx.x * blockDim.x + threadIdx.x; c < cells; c += (uint64_t)gridDim.x * blockDim.x) {
        const uint64_t segment = c / w.D, i = c % w.D;
        const uint32_t row = segments[3 * segment];
        wide sum = 0;
        for (uint32_t k = segments[3 * segment + 1]; k < segments[3 * segment + 2]; k++) {
            sum += rel((wide)rows_shares[k] * (wide)dx[(uint64_t)rows_sites[k] * w.D + i], FACE_BITS);
        }
        if (sum != 0) {
            add_wide(g + base + (uint64_t)row * w.D + i, sum);
        }
    }
}

// -------------------------------------------------------------------------------------------
// the turned heads' own clocks (§16, Law 1)

// The head of pace index `p` (the inverse of `paced_index`).
__device__ __forceinline__ uint32_t paced_head(const FieldWords &w, uint32_t p) {
    const uint32_t per = w.frames - w.still;
    return (p / per) * w.frames + w.still + p % per;
}

// A turned slot's rate of turn `b = 2π/n` on `2^(−30)` (the host's `Field::turn_rate`).
__device__ __forceinline__ wide turn_rate_dev(const FieldWords &w, uint32_t slot) {
    const wide pi = (wide)(((uwide)w.pi_hi << 64) | (uwide)w.pi_lo);
    return rel(div_nearest(2 * pi, (wide)w.ring_n[slot]), FACE_BITS);
}

// `release(b (a_i z_r − a_r z_i), 46)`: the turn's covector (the host's `turned_back`).
__device__ __forceinline__ wide turned_back_dev(const FieldWords &w, wide b, wide ar, wide ai, wide zr, wide zi) {
    wide x = 0, y = 0, cross = 0, out = 0;
    if (!mul_fits(ai, zr, &x) || !mul_fits(ar, zi, &y)) {
        atomicOr(w.status, REFUSED_CARRIER);
    }
    cross = x - y;
    if (!mul_fits(b, cross, &out)) {
        atomicOr(w.status, REFUSED_CARRIER);
    }
    return rel(out, MOVE_BITS + FACE_BITS);
}

// The skin's covector on the variation, `release(release(release(E D, 30) b, 30), 16)` (the host's `skin_back`).
__device__ __forceinline__ wide skin_back_dev(const FieldWords &w, wide b, wide decay, wide e) {
    wide x = 0, y = 0;
    if (!mul_fits(e, decay, &x)) {
        atomicOr(w.status, REFUSED_CARRIER);
    }
    if (!mul_fits(rel(x, MOVE_BITS), b, &y)) {
        atomicOr(w.status, REFUSED_CARRIER);
    }
    return rel(rel(y, MOVE_BITS), 16);
}

// A site's rate on paced head `p`'s class sheet (§16.16, the host's `Field::paces`): its own class's entry (zero at a
// silent open site, §16.28), or its carried shares' mixture `release(Σ_a w_a c_p[a], 16)`.
__device__ __forceinline__ wide pace_rate(const FieldWords &w, uint32_t p, uint64_t s) {
    const uint64_t base = w.pace_at + (uint64_t)p * (w.A + 1);
    const uint32_t from = w.mix_off[s], to = w.mix_off[s + 1];
    if (from == to) {
        if (w.unresolved[s]) {
            // A depth ring takes no blank face: a silent site runs at rate zero every tick.
            return w.blank_rate && !depth_head(w, paced_head(w, p)) ? (wide)w.blank_rate[(uint64_t)p * w.T + s] : 0;
        }
        return (wide)w.theta[base + row_of(w, s)];
    }
    wide sum = 0;
    for (uint32_t k = from; k < to; k++) {
        sum += (wide)w.mix_share[k] * (wide)w.theta[base + w.mix_class[k]];
    }
    return rel(sum, FACE_BITS);
}

// A blank's share of class `a` in the face it was read from (the host's `shares`): `⌊(m_a 2^16 + T/2) / T⌋`, zero where
// the face has no mass.
__device__ __forceinline__ uwide blank_share(const FieldWords &w, uint64_t s, uint32_t a) {
    const uwide total = w.blank_totals[s];
    return total == 0 ? 0 : (((uwide)w.blank_masses[s * w.A + a] << FACE_BITS) + total / 2) / total;
}

// [definition; agent-inferred, November 5, §16.44] **A blank's clock returns through its face** (the host's
// `Field::blank_return`), one thread a site and a class: at a silent open site `δz_b 2^30 = Σ_p rel(δκ_p · u_{p,b} · ln 2,
// 24)` with `u_{p,b} = ⌊m_b (c_p[b] − ⌊Σ_a m_a c_p[a] / T⌉) / T⌉`, the face's masses `m` and total `T` its clock read;
// zero elsewhere.
extern "C" __global__ void field_blank_dz(FieldWords w, const wide *dkappa, wide *dz) {
    const uint64_t cells = (uint64_t)w.T * w.A;
    const wide ln2 = (wide)(((uwide)w.ln2_hi << 64) | (uwide)w.ln2_lo);
    for (uint64_t c = (uint64_t)blockIdx.x * blockDim.x + threadIdx.x; c < cells; c += (uint64_t)gridDim.x * blockDim.x) {
        const uint64_t s = c / w.A;
        const uint32_t b = c % w.A;
        dz[c] = 0;
        if (!w.unresolved[s] || w.mix_off[s] != w.mix_off[s + 1] || w.blank_totals[s] == 0) {
            continue;
        }
        const wide total = (wide)w.blank_totals[s];
        wide out = 0;
        for (uint32_t p = 0; p < w.paced; p++) {
            const wide dk = dkappa[(uint64_t)p * w.T + s];
            if (dk == 0 || depth_head(w, paced_head(w, p))) {
                continue;
            }
            const uint64_t base = w.pace_at + (uint64_t)p * (w.A + 1);
            wide sum = 0;
            for (uint32_t a = 0; a < w.A; a++) {
                sum += (wide)w.blank_masses[s * w.A + a] * (wide)w.theta[base + a];
            }
            const wide mean = div_nearest(sum, total);
            const wide u = div_nearest((wide)w.blank_masses[s * w.A + b] * ((wide)w.theta[base + b] - mean), total);
            wide x = 0, y = 0;
            if (!mul_fits(dk, u, &x) || !mul_fits(x, ln2, &y)) {
                atomicOr(w.status, REFUSED_CARRIER);
            }
            out += rel(y, PACE_BITS);
        }
        dz[c] = out;
    }
}

// The encoding's bias and rows from a blank's face covector (held `2^30` finer): `δc_b += Σ_t rel(δz_b, 30)`,
// `δE(b)_i += Σ_t rel(δz_b y_i, 46)` over the silent sites, one thread an entry and a tile of 64 sites.
extern "C" __global__ void field_blank_bias_enc(FieldWords w, wide *g, uint64_t enc, uint64_t bias, const wide *dz, const int64_t *y) {
    const uint64_t entries = (uint64_t)w.A * (w.D + 1);
    const uint64_t tiles = ((uint64_t)w.T + 63) / 64;
    for (uint64_t c = (uint64_t)blockIdx.x * blockDim.x + threadIdx.x; c < entries * tiles; c += (uint64_t)gridDim.x * blockDim.x) {
        const uint64_t entry = c % entries, tile = c / entries;
        const uint64_t b = entry / (w.D + 1), i = entry % (w.D + 1);
        const uint64_t from = tile * 64;
        const uint64_t to = from + 64 < w.T ? from + 64 : w.T;
        wide sum = 0;
        for (uint64_t t = from; t < to; t++) {
            const wide d = dz[t * w.A + b];
            if (d == 0) {
                continue;
            }
            sum += i == w.D ? rel(d, 30) : rel(d * (wide)y[t * w.D + i], FACE_BITS + 30);
        }
        if (sum != 0) {
            add_wide(g + (i == w.D ? bias + b : enc + b * w.D + i), sum);
        }
    }
}

// The lift's covector from a blank's face covector, held `2^16` finer: `δy_i = rel(Σ_b δz_b E(b)_i, 30)` at a silent
// site, zero elsewhere.
extern "C" __global__ void field_blank_dy(FieldWords w, uint64_t enc, const wide *dz, int64_t *dy) {
    const uint64_t cells = (uint64_t)w.T * w.D;
    for (uint64_t c = (uint64_t)blockIdx.x * blockDim.x + threadIdx.x; c < cells; c += (uint64_t)gridDim.x * blockDim.x) {
        const uint64_t t = c / w.D, i = c % w.D;
        wide sum = 0;
        for (uint32_t b = 0; b < w.A; b++) {
            const wide d = dz[t * w.A + b];
            if (d != 0) {
                wide x = 0;
                if (!mul_fits(d, (wide)w.theta[enc + (uint64_t)b * w.D + i], &x)) {
                    atomicOr(w.status, REFUSED_CARRIER);
                }
                sum += x;
            }
        }
        dy[c] = fit64(rel(sum, 30), w.status);
    }
}

// The lift's bias and the read matrix from a blank's lift covector (held `2^16` finer): `δb_i += Σ_t rel(δy_i, 16)`,
// `δR_(i,j) += Σ_t rel(δy_i r̂_j, 16)`, one thread an entry and a tile of 64 sites.
extern "C" __global__ void field_blank_lift_read(FieldWords w, wide *g, uint64_t read, uint64_t bias, const int64_t *dy, const int32_t *r) {
    const uint64_t entries = (uint64_t)w.D * (w.D + 1);
    const uint64_t tiles = ((uint64_t)w.T + 63) / 64;
    for (uint64_t c = (uint64_t)blockIdx.x * blockDim.x + threadIdx.x; c < entries * tiles; c += (uint64_t)gridDim.x * blockDim.x) {
        const uint64_t entry = c % entries, tile = c / entries;
        const uint64_t i = entry / (w.D + 1), j = entry % (w.D + 1);
        const uint64_t from = tile * 64;
        const uint64_t to = from + 64 < w.T ? from + 64 : w.T;
        wide sum = 0;
        for (uint64_t t = from; t < to; t++) {
            const int64_t d = dy[t * w.D + i];
            if (d == 0) {
                continue;
            }
            sum += j == w.D ? rel((wide)d, FACE_BITS) : rel((wide)d * (wide)r[t * w.D + j], FACE_BITS);
        }
        if (sum != 0) {
            add_wide(g + (j == w.D ? bias + i : read + i * w.D + j), sum);
        }
    }
}

// The state's covector at a silent site takes the blank's return, released from its `2^16` finer hold: `dx += rel(back, 16)`.
extern "C" __global__ void field_blank_dx(FieldWords w, const int64_t *back, int64_t *dx) {
    const uint64_t cells = (uint64_t)w.T * w.D;
    for (uint64_t c = (uint64_t)blockIdx.x * blockDim.x + threadIdx.x; c < cells; c += (uint64_t)gridDim.x * blockDim.x) {
        const uint64_t t = c / w.D;
        if (!w.unresolved[t] || w.mix_off[t] != w.mix_off[t + 1]) {
            continue;
        }
        dx[c] = fit64((wide)dx[c] + rel((wide)back[c], FACE_BITS), w.status);
    }
}

// [definition; agent-inferred, November 4, §16.44] **A blank place's expected duration** (the host's `Field::paces_with`),
// one thread a paced head and a site: at a silent open site (unresolved, no carried mixture) `rel(Σ_a w_a c_p[a], 16)` with
// `w_a` the shares of the face the tick before read there, the rate its clock runs it at less one; zero elsewhere.
extern "C" __global__ void field_blank_rates(FieldWords w, int64_t *rates) {
    const uint64_t cells = (uint64_t)w.paced * w.T;
    for (uint64_t c = (uint64_t)blockIdx.x * blockDim.x + threadIdx.x; c < cells; c += (uint64_t)gridDim.x * blockDim.x) {
        const uint32_t p = c / w.T;
        const uint64_t s = c % w.T;
        if (!w.unresolved[s] || w.mix_off[s] != w.mix_off[s + 1]) {
            rates[c] = 0;
            continue;
        }
        const uint64_t base = w.pace_at + (uint64_t)p * (w.A + 1);
        wide sum = 0;
        for (uint32_t a = 0; a < w.A; a++) {
            sum += (wide)blank_share(w, s, a) * (wide)w.theta[base + a];
        }
        rates[c] = fit64(rel(sum, FACE_BITS), w.status);
    }
}

// A silent open site (§16.28, the host's `Field::silent`): unresolved, with no carried mixture.
__device__ __forceinline__ bool silent_at(const FieldWords &w, uint64_t s) {
    return w.unresolved[s] && w.mix_off[s] == w.mix_off[s + 1];
}

// [§16.47] A region's silent stretch past its last arrival (the host's `Field::silent_stretch`): the first silent place
// past its last site that is not silent, zero where every site is silent, the region's length where the last is not.
__device__ __forceinline__ uint32_t silent_stretch(const FieldWords &w, uint64_t first, uint32_t sites) {
    for (uint32_t t = sites; t-- > 0;) {
        if (!silent_at(w, first + t)) {
            return t + 1;
        }
    }
    return 0;
}

// [definition; agent-inferred, November 2] **The turned heads' clocks over each region** (the host's `Field::paces`),
// one thread a paced head and a region over its sites in order: on the class sheet `κ = 2^24 + c_p[u_t]` (§16.16),
// `τ`, `σ` the exact prefix sums from zero at the region's first site, and whether every rate is one (`plain`). Past the
// region's last arrival every place runs at the first silent place's rate (§16.47, one passage).
extern "C" __global__ void field_paces(FieldWords w) {
    const uint64_t cells = (uint64_t)w.paced * w.R;
    for (uint64_t c = (uint64_t)blockIdx.x * blockDim.x + threadIdx.x; c < cells; c += (uint64_t)gridDim.x * blockDim.x) {
        const uint32_t p = c / w.R, r = c % w.R;
        const uint64_t first = w.region_off[r];
        const uint32_t sites = w.region_off[r + 1] - (uint32_t)first;
        const uint32_t stretch = w.per_blank ? sites : silent_stretch(w, first, sites);
        // A depth ring's rate is its located increment alone (base zero).
        const wide one = depth_head(w, paced_head(w, p)) ? (wide)0 : (wide)1 << PACE_BITS;
        wide clock = 0, variation = 0;
        bool plain = true;
        for (uint32_t t = 0; t < sites; t++) {
            const uint64_t g = first + t;
            const wide k = one + pace_rate(w, p, first + (t > stretch && !w.bare_stretch ? stretch : t));
            if (t > 0) {
                clock += k;
                variation += k < 0 ? -k : k;
            }
            plain = plain && k == one;
            const uint64_t at = (uint64_t)p * w.T + g;
            w.kappa[at] = fit64(k, w.status);
            w.tau[at] = fit64(clock, w.status);
            w.sigma[at] = fit64(variation, w.status);
        }
        w.plain[(uint64_t)p * w.R + r] = plain ? 1 : 0;
    }
}

// Each paced head's frames at its clock `[p][t][n]` (`turn_dev`), where its pace is not plain over the region.
extern "C" __global__ void field_pframes(FieldWords w) {
    const uint64_t cells = (uint64_t)w.paced * w.T * w.n;
    for (uint64_t c = (uint64_t)blockIdx.x * blockDim.x + threadIdx.x; c < cells; c += (uint64_t)gridDim.x * blockDim.x) {
        const uint32_t l = c % w.n;
        const uint64_t g = (c / w.n) % w.T;
        const uint32_t p = c / ((uint64_t)w.n * w.T);
        const uint32_t h = paced_head(w, p);
        if (w.plain[(uint64_t)p * w.R + w.site_region[g]] && !depth_head(w, h)) {
            continue;
        }
        const uint32_t slot = l * (w.frames - w.still) + h % w.frames - w.still;
        wide re, im;
        turn_dev(w, slot, (wide)w.tau[(uint64_t)p * w.T + g], &re, &im);
        w.pframe[2 * c] = (int64_t)re;
        w.pframe[2 * c + 1] = (int64_t)im;
    }
}

// A moment mode's view of a region (§16): its pace index, slot, the frames' column, and whether the region's pace is
// plain (the byte place, the resident ring).
struct PacedMode {
    int32_t p;
    uint32_t slot, l;
    bool plain;
};

__device__ __forceinline__ PacedMode paced_mode(const FieldWords &w, uint32_t cm, uint32_t r) {
    PacedMode pm;
    // A depth ring's mode (the map's top bit) is read as a plain one; its moment is discarded and its covector zero.
    const bool dead = cm >> 31;
    cm &= 0x7FFFFFFFu;
    const uint32_t h = cm / w.n;
    pm.l = cm % w.n;
    pm.p = paced_index(w, h);
    pm.slot = pm.l * (w.frames - w.still) + h % w.frames - w.still;
    pm.plain = pm.p < 0 || dead || w.plain[(uint64_t)pm.p * w.R + r] != 0;
    return pm;
}

// `ζ^(τ_g)`: the paced frame (the resident ring at the byte place where plain).
__device__ __forceinline__ MomentGauss paced_absolute(const FieldWords &w, const MomentWords &mw, const PacedMode &pm, uint64_t g) {
    if (pm.plain) {
        return moment_absolute(mw.ring, mw.n, w.site_pos[g]);
    }
    const uint64_t at = ((uint64_t)pm.p * w.T + g) * w.n + pm.l;
    return mg_make((wide)w.pframe[2 * at], (wide)w.pframe[2 * at + 1]);
}

// `ζ^(τ_k − τ_t)` (`Law::phase`, paced).
__device__ __forceinline__ MomentGauss paced_phase(const FieldWords &w, const PacedMode &pm, uint64_t gt, uint64_t gk) {
    wide re, im;
    turn_dev(w, pm.slot, (wide)w.tau[(uint64_t)pm.p * w.T + gk] - (wide)w.tau[(uint64_t)pm.p * w.T + gt], &re, &im);
    return mg_make(re, im);
}

// `e^(−2π|σ_t − σ_k|/n)` (`Law::between`, paced).
__device__ __forceinline__ wide paced_between(const FieldWords &w, const PacedMode &pm, uint64_t gt, uint64_t gk) {
    return skin_dev(w, pm.slot, (wide)w.sigma[(uint64_t)pm.p * w.T + gt] - (wide)w.sigma[(uint64_t)pm.p * w.T + gk]);
}

// The paced region's admission (`Law::new` with a pace): the forward's or the return's certificate with the faces'
// l1 at least `2^31` (`PACED_L1`); a plain region's is the slot's own. Grid `(regions, modes)`, dynamic shared
// memory `3 · blockDim.x · 16`.
extern "C" __global__ void field_moment_admit_paced_all(const MomentWords *ws, const uint32_t *cmap, FieldWords fw, const int64_t *xs, const int64_t *ys, uint64_t stride, uint32_t returning) {
    extern __shared__ __align__(16) unsigned char paced_shared[];
    uwide *peak = (uwide *)paced_shared;
    const uint32_t u = blockIdx.y;
    const MomentWords &w = ws[u];
    const int64_t *x = xs + (uint64_t)u * stride;
    const int64_t *y = ys ? ys + (uint64_t)u * stride : nullptr;
    const uint32_t B = blockDim.x;
    for (uint32_t r = blockIdx.x; r < w.R; r += gridDim.x) {
        const PacedMode pm = paced_mode(fw, cmap[u], r);
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
                decay_max = moment_max(decay_max, (uwide)mag64(w.decay[k]));
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
        for (uint32_t s = B >> 1; s > 0; s >>= 1) {
            if (threadIdx.x < s) {
                for (uint32_t q = 0; q < 3; ++q) {
                    peak[q * B + threadIdx.x] = moment_max(peak[q * B + threadIdx.x], peak[q * B + threadIdx.x + s]);
                }
            }
            __syncthreads();
        }
        if (threadIdx.x == 0) {
            const uwide l1 = pm.plain ? peak[2 * B] : moment_max(peak[2 * B], (uwide)1 << 31);
            const bool admitted = shape && (returning ? moment_return_certificate(sites, l1, peak[B], peak[0]) : moment_certificate(sites, l1, peak[B], peak[0]));
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

// The paced prefix sums `P[j] = Σ_(k<j) ζ^(τ_k) x_k` (`released`: `Q[j] = Σ_(k<j) rel(ζ^(τ_k) x_k, 30)`), region by
// region, a chunk a thread and the chunks' totals offset (integer sums). Grid `(regions, modes)`, dynamic shared
// memory `blockDim.x · 32`.
extern "C" __global__ void field_moment_prefix_paced_all(const MomentWords *ws, const uint32_t *cmap, FieldWords fw, const int64_t *xs, wide *pres, uint64_t stride, uint64_t pre_stride, uint32_t released) {
    extern __shared__ __align__(16) unsigned char paced_shared[];
    MomentGauss *totals = (MomentGauss *)paced_shared;
    const uint32_t u = blockIdx.y;
    const MomentWords &w = ws[u];
    const int64_t *x = xs + (uint64_t)u * stride;
    wide *pre = pres + (uint64_t)u * pre_stride;
    const uint32_t B = blockDim.x;
    for (uint32_t r = blockIdx.x; r < w.R; r += gridDim.x) {
        if (!w.ok[r]) {
            continue;
        }
        const PacedMode pm = paced_mode(fw, cmap[u], r);
        const uint64_t first = w.region_off[r];
        const uint32_t sites = w.region_off[r + 1] - (uint32_t)first;
        wide *out = pre + 2 * (first + r);
        const uint32_t length = (sites + B - 1) / B;
        const uint32_t lo = threadIdx.x * length < sites ? threadIdx.x * length : sites;
        const uint32_t hi = lo + length < sites ? lo + length : sites;
        if (threadIdx.x == 0) {
            out[0] = 0;
            out[1] = 0;
        }
        MomentGauss running = mg_make(0, 0);
        for (uint32_t k = lo; k < hi; ++k) {
            const MomentGauss turned = mg_mul(paced_absolute(fw, w, pm, first + k), mg_load(x, first + k));
            running = mg_add(running, released ? mg_make(rel(turned.re, MOVE_BITS), rel(turned.im, MOVE_BITS)) : turned);
            out[2 * (uint64_t)(k + 1)] = running.re;
            out[2 * (uint64_t)(k + 1) + 1] = running.im;
        }
        totals[threadIdx.x] = running;
        __syncthreads();
        if (threadIdx.x == 0) {
            MomentGauss sum = mg_make(0, 0);
            for (uint32_t c = 0; c < B; ++c) {
                const MomentGauss t = totals[c];
                totals[c] = sum;
                sum = mg_add(sum, t);
            }
        }
        __syncthreads();
        moment_offset_chunk(lo, hi, totals[threadIdx.x], out);
        __syncthreads();
    }
}

// The paced moment of site `g` (place `t`) on `2^(−106)` (`moment_exact` with a pace): near `ζ^(τ_k − τ_t) D(σ)`, far
// `conj(ζ^(τ_t))` at the receiver's skin to the place `2^ℓ` away on each side.
__device__ MomentGauss moment_site_paced(const FieldWords &fw, const PacedMode &pm, const int64_t *before, const int64_t *after, const wide *up, const wide *down, uint64_t first, uint32_t sites, uint32_t t, const MomentWords &w) {
    MomentGauss s = mg_make(0, 0);
    const uint64_t gt = first + t;
    const uint32_t forward = t + 1 < (uint32_t)NEAR ? t + 1 : (uint32_t)NEAR;
    for (uint32_t d = 0; d < forward; ++d) {
        const uint64_t gk = gt - d;
        s = mg_add(s, moment_near(paced_phase(fw, pm, gt, gk), paced_between(fw, pm, gt, gk), mg_load(before, gk)));
    }
    const uint32_t backward = sites - t < (uint32_t)NEAR ? sites - t : (uint32_t)NEAR;
    for (uint32_t d = 0; d < backward; ++d) {
        const uint64_t gk = gt + d;
        s = mg_add(s, moment_near(paced_phase(fw, pm, gt, gk), paced_between(fw, pm, gt, gk), mg_load(after, gk)));
    }
    const MomentGauss home = mg_conj(paced_absolute(fw, w, pm, gt));
    for (uint32_t level = 2; ((uint64_t)1 << level) < sites; ++level) {
        uint32_t lo, hi;
        if (moment_octave(t, sites, level, false, &lo, &hi)) {
            const MomentGauss sum = mg_sub(mg_load_wide(up, hi + 1), mg_load_wide(up, lo));
            s = mg_add(s, mg_scale(mg_mul(home, sum), paced_between(fw, pm, gt, gt - ((uint64_t)1 << level))));
        }
        if (moment_octave(t, sites, level, true, &lo, &hi)) {
            const MomentGauss sum = mg_sub(mg_load_wide(down, hi + 1), mg_load_wide(down, lo));
            s = mg_add(s, mg_scale(mg_mul(home, sum), paced_between(fw, pm, gt, gt + ((uint64_t)1 << level))));
        }
    }
    return s;
}

// Every moment mode's moments on a paced field (`field_moment_all`, the paced regions by `moment_site_paced`).
extern "C" __global__ void field_moment_paced_all(const MomentWords *ws, const uint32_t *cmap, FieldWords fw, const int64_t *before, const int64_t *after, const wide *up, const wide *down, int64_t *s, uint64_t stride, uint64_t pre_stride) {
    const uint32_t u = blockIdx.y;
    const MomentWords &w = ws[u];
    before += (uint64_t)u * stride;
    after += (uint64_t)u * stride;
    s += (uint64_t)u * stride;
    up += (uint64_t)u * pre_stride;
    down += (uint64_t)u * pre_stride;
    for (uint64_t g = (uint64_t)blockIdx.x * blockDim.x + threadIdx.x; g < w.T; g += (uint64_t)gridDim.x * blockDim.x) {
        const uint32_t r = w.site_region[g], t = w.site_pos[g];
        if (!w.ok[r]) {
            s[2 * g] = 0;
            s[2 * g + 1] = 0;
            continue;
        }
        const uint64_t first = w.region_off[r];
        const uint32_t sites = w.region_off[r + 1] - (uint32_t)first;
        const PacedMode pm = paced_mode(fw, cmap[u], r);
        MomentGauss v;
        if (pm.plain) {
            if (!moment_site_exact(before + 2 * first, after + 2 * first, up + 2 * (first + r), down + 2 * (first + r), w.ring, w.n, w.ring_len, w.decay, sites, t, &v)) {
                atomicOr(w.status, MOMENT_REFUSED_SHAPE);
            }
        } else {
            v = moment_site_paced(fw, pm, before, after, up + 2 * (first + r), down + 2 * (first + r), first, sites, t, w);
        }
        s[2 * g] = fit64(rel(v.re, MOMENT_COEFFICIENT_BITS), w.status);
        s[2 * g + 1] = fit64(rel(v.im, MOMENT_COEFFICIENT_BITS), w.status);
    }
}

// [agent-inferred, November 2] **The paced far return's prefixes** (the host's `skinned`): for each moment mode, region
// whose pace is not plain, octave level `ℓ` and side, `sk[2(ℓ − 2) + left][j] = Σ_(t<j, t reads its octave on that side)
// D_(t,ℓ,side) release(ζ^(τ_t) δs_t, 30)` on `2^(−54)`, `left` the receivers that read their octave on the left. One
// thread a mode, region and row, over the region's sites in order. `sk` is `[u][row][T + R][2]`.
extern "C" __global__ void field_moment_skinned_all(const MomentWords *ws, const uint32_t *cmap, FieldWords fw, const int64_t *dss, wide *sks, uint64_t stride, uint64_t sk_stride, uint32_t levels, uint32_t tm) {
    const uint64_t cells = (uint64_t)tm * fw.R * 2 * levels;
    for (uint64_t c = (uint64_t)blockIdx.x * blockDim.x + threadIdx.x; c < cells; c += (uint64_t)gridDim.x * blockDim.x) {
        const uint32_t row = c % (2 * levels);
        const uint32_t r = (c / (2 * levels)) % fw.R;
        const uint32_t u = c / ((uint64_t)2 * levels * fw.R);
        const MomentWords &w = ws[u];
        const PacedMode pm = paced_mode(fw, cmap[u], r);
        if (!w.ok[r] || pm.plain) {
            continue;
        }
        const uint32_t level = 2 + row / 2;
        const bool left = row % 2 == 1;
        const uint64_t first = w.region_off[r];
        const uint32_t sites = w.region_off[r + 1] - (uint32_t)first;
        const int64_t *ds = dss + (uint64_t)u * stride;
        wide *out = sks + (uint64_t)u * sk_stride + ((uint64_t)row * (fw.T + fw.R) + first + r) * 2;
        MomentGauss sum = mg_make(0, 0);
        out[0] = 0;
        out[1] = 0;
        for (uint32_t t = 0; t < sites; t++) {
            const uint64_t gt = first + t;
            const bool reads = ((uint64_t)1 << level) < sites && (left ? t >= ((uint32_t)1 << level) : (uint64_t)t + ((uint64_t)1 << level) < sites);
            if (reads) {
                const MomentGauss turned = mg_mul(paced_absolute(fw, w, pm, gt), mg_load(ds, gt));
                const uint64_t edge = left ? gt - ((uint64_t)1 << level) : gt + ((uint64_t)1 << level);
                sum = mg_add(sum, mg_scale(mg_make(rel(turned.re, MOVE_BITS), rel(turned.im, MOVE_BITS)), paced_between(fw, pm, gt, edge)));
            }
            out[2 * (uint64_t)(t + 1)] = sum.re;
            out[2 * (uint64_t)(t + 1) + 1] = sum.im;
        }
    }
}

// Every moment mode's return on a paced field (`field_moment_return_all`, the paced regions by the paced law: the near
// terms at `ζ^(τ_k − τ_t) D(σ)`, the far ones from the skinned prefixes).
extern "C" __global__ void field_moment_return_paced_all(const MomentWords *ws, const uint32_t *cmap, FieldWords fw, const int64_t *dss, const wide *qs, const wide *sks, wide *d_before, wide *d_after, uint64_t stride, uint64_t pre_stride, uint64_t sk_stride) {
    const uint32_t u = blockIdx.y;
    const MomentWords &w = ws[u];
    const int64_t *ds = dss + (uint64_t)u * stride;
    d_before += (uint64_t)u * stride;
    d_after += (uint64_t)u * stride;
    const wide *q = qs + (uint64_t)u * pre_stride;
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
        MomentGauss plus = mg_make(0, 0), minus = mg_make(0, 0);
        if (pm.plain) {
            if (!moment_return_site(ds + 2 * first, q + 2 * (first + r), w.ring, w.n, w.ring_len, w.decay, sites, k, &plus, &minus)) {
                atomicOr(w.status, MOMENT_REFUSED_SHAPE);
            }
        } else {
            const uint32_t forward = sites - k < (uint32_t)NEAR ? sites - k : (uint32_t)NEAR;
            for (uint32_t d = 0; d < forward; ++d) {
                plus = mg_add(plus, moment_near_back(paced_phase(fw, pm, g + d, g), paced_between(fw, pm, g + d, g), mg_load(ds, g + d)));
            }
            const uint32_t backward = k + 1 < (uint32_t)NEAR ? k + 1 : (uint32_t)NEAR;
            for (uint32_t d = 0; d < backward; ++d) {
                minus = mg_add(minus, moment_near_back(paced_phase(fw, pm, g - d, g), paced_between(fw, pm, g - d, g), mg_load(ds, g - d)));
            }
            const MomentGauss home = mg_conj(paced_absolute(fw, w, pm, g));
            for (uint32_t level = 2; ((uint64_t)1 << level) < sites; ++level) {
                uint32_t lo, hi;
                for (uint32_t side = 0; side < 2; side++) {
                    const bool right = side == 1;
                    if (!moment_octave(k, sites, level, right, &lo, &hi)) {
                        continue;
                    }
                    // The receivers right of `k` read it on their left (row `left`), those left of it on their right.
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

// `Re(conj(a) z)` for a covector pair `a` and a Gaussian `z`.
__device__ __forceinline__ wide re_pair(const FieldWords &w, wide ar, wide ai, MomentGauss z) {
    wide x = 0, y = 0;
    if (!mul_fits(ar, z.re, &x) || !mul_fits(ai, z.im, &y)) {
        atomicOr(w.status, REFUSED_CARRIER);
    }
    return x + y;
}

// One skin term of the moments' clock covector (the host's `pace_return`'s `skin`): `at = release(release(release(inner
// D, 30) b, 30), 46)`, `δσ_t −= sgn at`, `δσ_k += sgn at`, `sgn = sgn(σ_t − σ_k)`.
__device__ __forceinline__ void moment_skin_back(const FieldWords &w, const PacedMode &pm, uint64_t gt, uint64_t gk, wide decay, wide inner, wide b) {
    const wide st = (wide)w.sigma[(uint64_t)pm.p * w.T + gt], sk = (wide)w.sigma[(uint64_t)pm.p * w.T + gk];
    if (st == sk) {
        return;
    }
    wide x = 0, y = 0;
    if (!mul_fits(inner, decay, &x) || !mul_fits(rel(x, MOVE_BITS), b, &y)) {
        atomicOr(w.status, REFUSED_CARRIER);
    }
    const wide at = rel(rel(y, MOVE_BITS), MOVE_BITS + FACE_BITS);
    const wide signed_at = st > sk ? at : -at;
    add_wide(w.gsig + (uint64_t)pm.p * w.T + gt, -signed_at);
    add_wide(w.gsig + (uint64_t)pm.p * w.T + gk, signed_at);
}

// [definition; agent-inferred, November 2] **The moments' clock covector** (the host's `moment::pace_return`), one thread
// a site and a moment mode of a paced head, every region (plain or not: the founding's covector reaches its pace),
// added into `gtau` and `gsig` (integer sums).
extern "C" __global__ void field_moment_pace_back_all(const MomentWords *ws, const uint32_t *cmap, FieldWords fw, const int64_t *befores, const int64_t *afters, const int64_t *dss, const wide *d_befores, const wide *d_afters, const wide *ups, const wide *downs, uint64_t stride, uint64_t pre_stride) {
    const uint32_t u = blockIdx.y;
    const MomentWords &w = ws[u];
    const int64_t *before = befores + (uint64_t)u * stride, *after = afters + (uint64_t)u * stride, *ds = dss + (uint64_t)u * stride;
    const wide *db = d_befores + (uint64_t)u * stride, *da = d_afters + (uint64_t)u * stride;
    const wide *up = ups + (uint64_t)u * pre_stride, *down = downs + (uint64_t)u * pre_stride;
    const bool dead = cmap[u] >> 31;
    const uint32_t cm = cmap[u] & 0x7FFFFFFFu;
    for (uint64_t g = (uint64_t)blockIdx.x * blockDim.x + threadIdx.x; g < w.T; g += (uint64_t)gridDim.x * blockDim.x) {
        const uint32_t r = w.site_region[g], t = w.site_pos[g];
        PacedMode pm = paced_mode(fw, cm, r);
        if (pm.p < 0 || dead || !w.ok[r]) {
            continue;
        }
        const uint64_t first = w.region_off[r];
        const uint32_t sites = w.region_off[r + 1] - (uint32_t)first;
        const wide b = turn_rate_dev(fw, pm.slot);
        const wide sr = (wide)fw.moment[g * fw.M2 + cm], si = (wide)fw.moment[g * fw.M2 + fw.M + cm];
        const wide dr = (wide)ds[2 * g], di = (wide)ds[2 * g + 1];
        wide dtau = -turned_back_dev(fw, b, dr, di, sr, si);
        wide cb = 0, ca = 0, x = 0, y = 0;
        if (!mul_fits(db[2 * g + 1], (wide)before[2 * g], &x) || !mul_fits(db[2 * g], (wide)before[2 * g + 1], &y)) {
            atomicOr(fw.status, REFUSED_CARRIER);
        }
        cb = x - y;
        if (!mul_fits(da[2 * g + 1], (wide)after[2 * g], &x) || !mul_fits(da[2 * g], (wide)after[2 * g + 1], &y)) {
            atomicOr(fw.status, REFUSED_CARRIER);
        }
        ca = x - y;
        wide both = 0;
        if (!mul_fits(cb + ca, b, &both)) {
            atomicOr(fw.status, REFUSED_CARRIER);
        }
        dtau += rel(both, MOVE_BITS + FACE_BITS);
        add_wide(fw.gtau + (uint64_t)pm.p * fw.T + g, dtau);
        // The skins: the plain region's are the same law at whole variations.
        pm.plain = false;
        const uint32_t forward = t + 1 < (uint32_t)NEAR ? t + 1 : (uint32_t)NEAR;
        for (uint32_t d = 0; d < forward; ++d) {
            const uint64_t gk = g - d;
            moment_skin_back(fw, pm, g, gk, paced_between(fw, pm, g, gk), re_pair(fw, dr, di, mg_mul(paced_phase(fw, pm, g, gk), mg_load(before, gk))), b);
        }
        const uint32_t backward = sites - t < (uint32_t)NEAR ? sites - t : (uint32_t)NEAR;
        for (uint32_t d = 0; d < backward; ++d) {
            const uint64_t gk = g + d;
            moment_skin_back(fw, pm, g, gk, paced_between(fw, pm, g, gk), re_pair(fw, dr, di, mg_mul(paced_phase(fw, pm, g, gk), mg_load(after, gk))), b);
        }
        PacedMode own = paced_mode(fw, cm, r);
        const MomentGauss home = mg_conj(paced_absolute(fw, w, own, g));
        for (uint32_t level = 2; ((uint64_t)1 << level) < sites; ++level) {
            uint32_t lo, hi;
            for (uint32_t side = 0; side < 2; side++) {
                const bool right = side == 1;
                if (!moment_octave(t, sites, level, right, &lo, &hi)) {
                    continue;
                }
                const wide *pre = (right ? down : up) + 2 * (first + r);
                const MomentGauss f = mg_mul(home, mg_sub(mg_load_wide(pre, hi + 1), mg_load_wide(pre, lo)));
                const MomentGauss face = mg_make(rel(f.re, MOVE_BITS), rel(f.im, MOVE_BITS));
                const uint64_t edge = right ? g + ((uint64_t)1 << level) : g - ((uint64_t)1 << level);
                moment_skin_back(fw, pm, g, edge, paced_between(fw, pm, g, edge), re_pair(fw, dr, di, face), b);
            }
        }
    }
}

// [definition; agent-inferred, November 2] **The current's return to a paced receiver's frame turns by its clock**
// (the host's `δτ_i −= b Re(conj(δy) i y)`): one thread a paced head and a site, over its modes.
extern "C" __global__ void field_pace_current_back(FieldWords w, const int64_t *dy, const int64_t *y) {
    const uint64_t cells = (uint64_t)w.paced * w.T;
    for (uint64_t c = (uint64_t)blockIdx.x * blockDim.x + threadIdx.x; c < cells; c += (uint64_t)gridDim.x * blockDim.x) {
        const uint64_t g = c % w.T;
        const uint32_t p = c / w.T, h = paced_head(w, p);
        wide acc = 0;
        for (uint32_t l = 0; l < w.n; l++) {
            const uint32_t m = h * w.n + l, slot = l * (w.frames - w.still) + h % w.frames - w.still;
            acc -= turned_back_dev(w, turn_rate_dev(w, slot), dy[g * w.M2 + m], dy[g * w.M2 + w.M + m], y[g * w.M2 + m], y[g * w.M2 + w.M + m]);
        }
        w.gtau[(uint64_t)p * w.T + g] += acc;
    }
}

// [definition; agent-inferred, November 2] **A paced head's frames turn its word, value and probe by its clock** (the
// host's `δτ_t += b Re(conj(δw) i w)` on the unframed charts): one thread a paced head and a site. `qkv` holds the
// unframed word and value (the moment added), `pr` the unframed probe.
extern "C" __global__ void field_pace_frame_back(FieldWords w, const int64_t *dq, const int64_t *dv, const int64_t *dp, const int64_t *qkv, const int64_t *pr) {
    const uint64_t cells = (uint64_t)w.paced * w.T;
    for (uint64_t c = (uint64_t)blockIdx.x * blockDim.x + threadIdx.x; c < cells; c += (uint64_t)gridDim.x * blockDim.x) {
        const uint64_t g = c % w.T;
        const uint32_t p = c / w.T, h = paced_head(w, p);
        wide acc = 0;
        for (uint32_t l = 0; l < w.n; l++) {
            const uint32_t m = h * w.n + l, slot = l * (w.frames - w.still) + h % w.frames - w.still;
            const wide b = turn_rate_dev(w, slot);
            const int64_t *q = qkv + g * 2 * w.M2;
            acc += turned_back_dev(w, b, dq[g * w.M2 + m], dq[g * w.M2 + w.M + m], q[m], q[w.M + m]);
            acc += turned_back_dev(w, b, dv[g * w.M2 + m], dv[g * w.M2 + w.M + m], q[w.M2 + m], q[w.M2 + w.M + m]);
            acc += turned_back_dev(w, b, dp[g * w.M2 + m], dp[g * w.M2 + w.M + m], pr[g * w.M2 + m], pr[g * w.M2 + w.M + m]);
        }
        w.gtau[(uint64_t)p * w.T + g] += acc;
    }
}

// [definition; agent-inferred, November 2] **A paced head's skins return to its variation** (the host's pair and crowd
// skin terms): one warp a receiver of head `h` (paced), a lane a support entry: `E = 2^40 ∂/∂D` from the value
// (`release(p Re(conj(δỹ_i) ṽ_j), 63)`) and the lock (`release(δs (2 (w·k) 2^g − 2 D |k|²), 63)`), then
// `δσ_i −= sgn at`, `δσ_j += sgn at`, `at = skin_back(b, D, E)`; a crowd's alike at the place `2^ℓ` away on its side
// (its value `release(p_C Re(conj(δỹ) V), 63)/|C|`, its lock bracket over `|C|²`).
extern "C" __global__ void __launch_bounds__(CONTACT_ROWS * 32) field_pace_skin_back(FieldWords w, uint32_t h, const int64_t *dyh, const int64_t *ds) {
    __shared__ RowCls rcs[CONTACT_ROWS];
    const uint32_t warp = threadIdx.x >> 5, lane = threadIdx.x & 31;
    const uint32_t S = w.span, n = w.n, classes = w.nclasses;
    const int32_t p = paced_index(w, h);
    if (p < 0) {
        return;
    }
    const uint64_t rows1 = (uint64_t)w.T + w.R;
    for (uint64_t g = ((uint64_t)blockIdx.x * blockDim.x + threadIdx.x) >> 5; g < w.T; g += (uint64_t)gridDim.x * (blockDim.x >> 5)) {
        const uint64_t hg = (uint64_t)h * w.T + g;
        // [E] A row the cut room did not compute met no source: its skins return nothing.
        if (skipped_row(w, g)) {
            continue;
        }
        const uint32_t r = w.site_region[g];
        const uint64_t first = w.region_off[r];
        const uint32_t sites = w.region_off[r + 1] - (uint32_t)first, i = w.site_pos[g];
        const uint32_t *members = w.members + (uint64_t)h * w.T + first;
        const uint32_t *off = w.class_off + ((uint64_t)h * w.R + r) * (2 * classes + 1);
        const uint32_t K = row_prepare(w, hg, off, rcs[warp], lane);
        const uint64_t *e = w.e + (uint64_t)h * w.E + w.region_eoff[r] + (uint64_t)i * sites;
        const int64_t *dsr = ds + w.region_eoff[r] + (uint64_t)i * sites;
        const int64_t *dyi = dyh + hg * S;
        const int64_t *values = w.vf + ((uint64_t)h * w.T + first) * S;
        const int64_t *words = w.qf + ((uint64_t)h * w.T + first) * S;
        const int64_t *wi = w.pq + hg * S;
        const int64_t *sigma = w.sigma + (uint64_t)p * w.T;
        const uint64_t prow0 = (uint64_t)h * rows1 + first + r;
        const wide *swp = w.sw + prow0 * S;
        const wide *svp = w.sv + prow0 * S;
        const uint64_t *scp = w.sc + prow0;
        const uint32_t nslots = rcs[warp].open ? 0 : crowd_slots(sites);
        wide own = 0;
        for (uint32_t k = lane; k < K; k += 32) {
            const uint32_t j = support_at(members, off, rcs[warp], i, sites, k);
            if (j == UINT32_MAX) {
                continue;
            }
            const uint64_t gj = first + j;
            const wide sgn = sigma[g] > sigma[gj] ? 1 : sigma[g] < sigma[gj] ? -1 : 0;
            if (sgn == 0) {
                continue;
            }
            const uint32_t gap = j > i ? j - i : i - j;
            wide at = 0;
            for (uint32_t l = 0; l < n; l++) {
                const uint32_t slot = l * (w.frames - w.still) + h % w.frames - w.still;
                const wide dec = skin_ij(w, h, l, g, gj, gap);
                const wide inner = (wide)dyi[l] * (wide)values[(uint64_t)j * S + l] + (wide)dyi[n + l] * (wide)values[(uint64_t)j * S + n + l];
                wide value = 0;
                if (!mul_fits((wide)e[j], inner, &value)) {
                    atomicOr(w.status, REFUSED_CARRIER);
                }
                value = rel(value, SHARE_BITS);
                const wide kr = words[(uint64_t)j * S + l], ki = words[(uint64_t)j * S + n + l];
                const wide bracket = ((2 * ((wide)wi[l] * kr + (wide)wi[n + l] * ki)) << MOVE_BITS) - 2 * dec * (kr * kr + ki * ki);
                wide lock = 0;
                if (!mul_fits((wide)dsr[j], bracket, &lock)) {
                    atomicOr(w.status, REFUSED_KEY);
                }
                lock = rel(lock, 2 * FACE_BITS + 1 + 2 * MOVE_BITS - MOVE_BITS);
                at = skin_back_dev(w, turn_rate_dev(w, slot), dec, value + lock);
                own -= sgn * at;
                add_wide(w.gsig + (uint64_t)p * w.T + gj, sgn * at);
            }
        }
        if (lane < nslots) {
            uint32_t lo, hi_, lv;
            if (crowd_at(i, sites, lane, &lo, &hi_, &lv)) {
                const uint64_t count = scp[hi_ + 1] - scp[lo];
                const bool right = lo > i;
                const uint64_t ge = octave_edge(g, lv, right);
                const wide sgn = sigma[g] > sigma[ge] ? 1 : sigma[g] < sigma[ge] ? -1 : 0;
                if (count != 0 && sgn != 0) {
                    const wide cnt = (wide)count;
                    for (uint32_t l = 0; l < n; l++) {
                        const uint32_t slot = l * (w.frames - w.still) + h % w.frames - w.still;
                        const wide dec = skin_ij(w, h, l, g, ge, (uint32_t)1 << lv);
                        const wide vr = svp[(uint64_t)(hi_ + 1) * S + l] - svp[(uint64_t)lo * S + l], vi = svp[(uint64_t)(hi_ + 1) * S + n + l] - svp[(uint64_t)lo * S + n + l];
                        wide x = 0, y = 0, value = 0;
                        if (!mul_fits((wide)dyi[l], vr, &x) || !mul_fits((wide)dyi[n + l], vi, &y) || !mul_fits((wide)w.ce[hg * w.slots + lane], x + y, &value)) {
                            atomicOr(w.status, REFUSED_CARRIER);
                        }
                        value = div_nearest(rel(value, SHARE_BITS), cnt);
                        const wide wr = wi[l], wim = wi[n + l];
                        const wide mr = swp[(uint64_t)(hi_ + 1) * S + l] - swp[(uint64_t)lo * S + l], mi = swp[(uint64_t)(hi_ + 1) * S + n + l] - swp[(uint64_t)lo * S + n + l];
                        const wide bracket = div_nearest(((2 * cnt * (wr * mr + wim * mi)) << MOVE_BITS) - 2 * dec * (mr * mr + mi * mi), cnt * cnt);
                        wide lock = 0;
                        if (!mul_fits((wide)w.cds[hg * w.slots + lane], bracket, &lock)) {
                            atomicOr(w.status, REFUSED_KEY);
                        }
                        lock = rel(lock, 2 * FACE_BITS + 1 + MOVE_BITS);
                        const wide at = skin_back_dev(w, turn_rate_dev(w, slot), dec, value + lock);
                        own -= sgn * at;
                        add_wide(w.gsig + (uint64_t)p * w.T + ge, sgn * at);
                    }
                }
            }
        }
        own = warp_sum(own);
        if (lane == 0 && own != 0) {
            add_wide(w.gsig + (uint64_t)p * w.T + g, own);
        }
    }
}

// [definition; agent-inferred, November 2] **The clocks return to their paces** (the host's tail of `returned`): one
// thread a paced head and a region, over its sites from the last: `δκ_k = Σ_(t≥k) δτ_t + sgn(κ_k) Σ_(t≥k) δσ_t` (zero at
// the region's first site, whose rate ticks no step), into `dkappa[p][t]`; past the last arrival the places' covectors
// return to the first silent place, whose rate they ran at (§16.47).
extern "C" __global__ void field_pace_kappa_back(FieldWords w, wide *dkappa) {
    const uint64_t cells = (uint64_t)w.paced * w.R;
    for (uint64_t c = (uint64_t)blockIdx.x * blockDim.x + threadIdx.x; c < cells; c += (uint64_t)gridDim.x * blockDim.x) {
        const uint32_t p = c / w.R, r = c % w.R;
        const uint64_t first = w.region_off[r];
        const uint32_t sites = w.region_off[r + 1] - (uint32_t)first;
        const uint32_t stretch = w.per_blank ? sites : silent_stretch(w, first, sites);
        wide tau = 0, sig = 0, folded = 0;
        for (uint32_t t = sites; t-- > 0;) {
            const uint64_t at = (uint64_t)p * w.T + first + t;
            wide own = 0;
            if (t > 0) {
                tau += w.gtau[at];
                sig += w.gsig[at];
                const int64_t k = w.kappa[at];
                own = tau + (k > 0 ? sig : k < 0 ? -sig : 0);
            }
            if (t > stretch && !w.bare_stretch) {
                folded += own;
                dkappa[at] = 0;
            } else {
                dkappa[at] = own + (t == stretch && !w.bare_stretch ? folded : 0);
            }
        }
    }
}

// `δc_p[u] += Σ_(t: u_t = u) δκ_p(t)` on the class sheet (§16.16; the material's covector grain, a whole class's share
// `2^16`, a carried face's classes by their shares), one thread a paced head and a site, the sums exact in any order.
extern "C" __global__ void field_pace_c_back(FieldWords w, const wide *dkappa, wide *g) {
    const uint64_t cells = (uint64_t)w.paced * w.T;
    for (uint64_t c = (uint64_t)blockIdx.x * blockDim.x + threadIdx.x; c < cells; c += (uint64_t)gridDim.x * blockDim.x) {
        const uint32_t p = c / w.T;
        const uint64_t t = c % w.T;
        const wide dk = dkappa[(uint64_t)p * w.T + t];
        if (dk == 0) {
            continue;
        }
        const uint64_t base = w.pace_at + (uint64_t)p * (w.A + 1);
        const uint32_t from = w.mix_off[t], to = w.mix_off[t + 1];
        if (from == to) {
            if (!w.unresolved[t]) {
                add_wide(g + base + row_of(w, t), dk << FACE_BITS);
            } else if (w.blank_rate && !depth_head(w, paced_head(w, p)) && (w.blank_read == nullptr || w.blank_read[t])) {
                // [§16.44] A blank's rate by the shares of the face its clock read, an operand of that clock (a place that
                // read no face, past the last arrival under the bare stretch, ran at the bare rate and returns nothing).
                for (uint32_t a = 0; a < w.A; a++) {
                    const uwide share = blank_share(w, t, a);
                    if (share != 0) {
                        add_wide(g + base + a, dk * (wide)share);
                    }
                }
            }
        } else {
            for (uint32_t k = from; k < to; k++) {
                add_wide(g + base + w.mix_class[k], dk * (wide)w.mix_share[k]);
            }
        }
    }
}

// -------------------------------------------------------------------------------------------
// the tower of scales (the host's `field::scale`)

// [definition; agent-inferred, November 3] A packet's rows in place order (the host's `padded`): `dst[p][k][i]` is fine site
// `P jl + k` of packet `p`'s region, row `i`, zero past the region's last site. `cw` are the packets' words (their region
// and place within it), `fine_off` the fine sites' region offsets.
extern "C" __global__ void field_scale_gather32(FieldWords cw, const int32_t *src, int32_t *dst, const uint32_t *fine_off, uint32_t width, uint32_t period) {
    const uint64_t per = (uint64_t)period * width;
    const uint64_t cells = (uint64_t)cw.T * per;
    for (uint64_t c = (uint64_t)blockIdx.x * blockDim.x + threadIdx.x; c < cells; c += (uint64_t)gridDim.x * blockDim.x) {
        const uint64_t p = c / per, e = c % per;
        const uint32_t k = e / width, i = e % width;
        const uint32_t r = cw.site_region[p];
        const uint64_t local = (uint64_t)period * cw.site_pos[p] + k;
        const uint64_t len = fine_off[r + 1] - fine_off[r];
        dst[c] = local < len ? src[(fine_off[r] + local) * width + i] : 0;
    }
}

extern "C" __global__ void field_scale_gather64(FieldWords cw, const int64_t *src, int64_t *dst, const uint32_t *fine_off, uint32_t width, uint32_t period) {
    const uint64_t per = (uint64_t)period * width;
    const uint64_t cells = (uint64_t)cw.T * per;
    for (uint64_t c = (uint64_t)blockIdx.x * blockDim.x + threadIdx.x; c < cells; c += (uint64_t)gridDim.x * blockDim.x) {
        const uint64_t p = c / per, e = c % per;
        const uint32_t k = e / width, i = e % width;
        const uint32_t r = cw.site_region[p];
        const uint64_t local = (uint64_t)period * cw.site_pos[p] + k;
        const uint64_t len = fine_off[r + 1] - fine_off[r];
        dst[c] = local < len ? src[(fine_off[r] + local) * width + i] : 0;
    }
}

// Each fine site's part of its packet's rows (`src[p][k][i]`, `k` its place in the packet), added into `dst[t][i]` (`add`)
// or written there. `w` are the fine sites' words, `packet_off` the packets' region offsets.
extern "C" __global__ void field_scale_scatter(FieldWords w, const int64_t *src, int64_t *dst, const uint32_t *packet_off, uint32_t width, uint32_t period, uint32_t add) {
    const uint64_t cells = (uint64_t)w.T * width;
    for (uint64_t c = (uint64_t)blockIdx.x * blockDim.x + threadIdx.x; c < cells; c += (uint64_t)gridDim.x * blockDim.x) {
        const uint64_t t = c / width;
        const uint32_t i = c % width;
        const uint32_t r = w.site_region[t], local = w.site_pos[t];
        const uint64_t p = packet_off[r] + local / period;
        const int64_t v = src[(p * period + local % period) * width + i];
        dst[c] = add ? fit64((wide)dst[c] + (wide)v, w.status) : v;
    }
}

// [measurement; agent-inferred, November 7] **The card's own clock at a point of its stream** (`FIELD_EVENTS`, a reading
// only): `%globaltimer`, the card's nanoseconds as an integer, written to `slot` by one thread. Launched before and after a
// timed launch on the same stream, so the difference is the launch's time on the card with no host synchronization between.
extern "C" __global__ void field_stamp(uint64_t *slot) {
    uint64_t t;
    asm volatile("mov.u64 %0, %%globaltimer;" : "=l"(t));
    *slot = t;
}

// -------------------------------------------------------------------------------------------
// integer products on the tensor cores, by limbs

#include "field_mma.cuh"

// -------------------------------------------------------------------------------------------
// the energy field (`holonics::hnn::tower::field::energy`)

#include "field_energy.cuh"

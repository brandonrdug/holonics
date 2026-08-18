// **The exact scores of one query against a deposited map's whole readout, on the card.**
//
// Record: `research/records/2026-08-13_THE_MAP_DECLARES_ITS_OWN_APERTURES_AND_AN_EMBEDDING_IS_A_DECLARED_RECEIVER.md`.
//
// # What this computes, and what it deliberately does NOT
//
// Given a readout matrix `E` of `rows x dim` exact integers and one query `u` of `dim` exact
// integers, this returns **every** score
//
//     s[v] = <E[v], u>       exactly, as a 128-bit integer
//
// and nothing else. It does not rank, does not take a maximum, does not threshold, and does not
// return a winner.
//
// That refusal is the whole design and it is not fastidiousness. `research/records/
// 2026-08-12_THE_PRETRAINED_TRANSFORMER_IS_ONE_TRANSPORT_ORGAN_THE_REASONING_MACHINE_IS_THE_RETURNING_ECOLOGY.md`
// §1 states the bar directly: *"An autocorrect system adds a receiver which ranks or otherwise
// collapses a candidate population and commits a replacement."* A kernel that returned `argmax`
// would BE that receiver, welded into the hot path where no later caller could decline it. The
// candidate population, its edit lineage, its collapsed pairs and its unresolved exterior are the
// object; a committed replacement is one coarse face of that object and is the caller's to take.
//
// # Exactness
//
// `E` and `u` arrive as integers aligned to one declared power of two by the cpu's float mouth, so
// every product is exact and every sum is exact. Accumulation is `__int128`: a `dim`-term sum of
// products of values bounded by `2^b` needs `2b + ceil(log2(dim))` bits, which for the material this
// was built for -- BF16 entries aligned to a common exponent, `dim = 2560` -- is far inside 128.
// **The cpu checks that bound before dispatch and refuses rather than truncating**; nothing here
// saturates, rounds, or clamps.
//
// A 128-bit value crosses back as two 64-bit halves, low then high, because the cpu carrier is
// `i128` and the driver interface is 64-bit words. The split is a chart, not a loss.

#include <stdint.h>

// One score, returned as its two halves. Low is unsigned because it is a bit pattern, not a
// magnitude; high carries the sign.
struct SplitScore {
    uint64_t low;
    int64_t high;
};

__device__ SplitScore split_of(__int128 value) {
    SplitScore split;
    split.low = (uint64_t)((unsigned __int128)value & (unsigned __int128)0xFFFFFFFFFFFFFFFFULL);
    split.high = (int64_t)(value >> 64);
    return split;
}

// The deed: one row of `E` against `u`, exactly.
//
// One thread per row. `dim` is a stride rather than a compile-time extent, so a map of a different
// width needs no new kernel -- the width is the material's and is never authored here.
extern "C" __global__ void exact_readout_scores(
    const int64_t *readout,   // rows x dim, row-major
    const int64_t *query,     // dim
    uint32_t rows,
    uint32_t dim,
    uint64_t *score_low,      // rows
    int64_t *score_high       // rows
) {
    uint32_t row = blockIdx.x * blockDim.x + threadIdx.x;
    if (row >= rows) {
        return;
    }
    const int64_t *entries = readout + (size_t)row * (size_t)dim;
    __int128 accumulated = 0;
    for (uint32_t at = 0; at < dim; ++at) {
        accumulated += (__int128)entries[at] * (__int128)query[at];
    }
    SplitScore split = split_of(accumulated);
    score_low[row] = split.low;
    score_high[row] = split.high;
}

// **The same deed for a whole declared query population, in one grid.**
//
// `queries x rows` scores, `blockIdx.y` selecting the query. Added 2026-08-13 because the caller
// that asks 4,096 questions of one readout was issuing 4,096 separate launches, each re-uploading
// the same 84 MB operand -- about 343 GB across the bus for a matrix that never changed. That is
// not a kernel problem and it was not fixed by writing a different kernel: `dim` was already a
// stride, so the deed for many queries is the deed for one, indexed.
//
// The readout is the invariant and stays resident; the query population crosses once. Nothing here
// ranks across queries either -- each query gets its own full score population, and no query is
// compared to another.
extern "C" __global__ void exact_readout_scores_batched(
    const int64_t *readout,   // rows x dim, row-major
    const int64_t *queries,   // count x dim, row-major
    uint32_t rows,
    uint32_t dim,
    uint32_t count,
    uint64_t *score_low,      // count x rows
    int64_t *score_high       // count x rows
) {
    uint32_t row = blockIdx.x * blockDim.x + threadIdx.x;
    uint32_t which = blockIdx.y;
    if (row >= rows || which >= count) {
        return;
    }
    const int64_t *entries = readout + (size_t)row * (size_t)dim;
    const int64_t *query = queries + (size_t)which * (size_t)dim;
    __int128 accumulated = 0;
    for (uint32_t at = 0; at < dim; ++at) {
        accumulated += (__int128)entries[at] * (__int128)query[at];
    }
    SplitScore split = split_of(accumulated);
    size_t slot = (size_t)which * (size_t)rows + (size_t)row;
    score_low[slot] = split.low;
    score_high[slot] = split.high;
}

// The same deed against a **declared subpopulation** of rows.
//
// The caller declares which rows it is asking about; the kernel asks about those and no others. A
// row the caller did not name is not scored, not defaulted, and not silently included -- which is
// what lets a caller state an aperture and report what it excluded rather than dropping it.
extern "C" __global__ void exact_readout_scores_addressed(
    const int64_t *readout,
    const int64_t *query,
    const uint32_t *addresses,  // count
    uint32_t count,
    uint32_t dim,
    uint64_t *score_low,        // count
    int64_t *score_high         // count
) {
    uint32_t slot = blockIdx.x * blockDim.x + threadIdx.x;
    if (slot >= count) {
        return;
    }
    const int64_t *entries = readout + (size_t)addresses[slot] * (size_t)dim;
    __int128 accumulated = 0;
    for (uint32_t at = 0; at < dim; ++at) {
        accumulated += (__int128)entries[at] * (__int128)query[at];
    }
    SplitScore split = split_of(accumulated);
    score_low[slot] = split.low;
    score_high[slot] = split.high;
}

// **The exact octave of each score, which is the one face that crosses a frame boundary.**
//
// A score is a magnitude in the query's own frame and `CLAUDE.md`'s horizon law says magnitudes do
// not cross one. What does cross is a `Winding` -- an integer -- and the bit length of an exact
// integer is exactly that: how many doublings the material spent, counted, with nothing rounded.
// `regime_reading` is built on the same reading.
//
// Returned beside the scores rather than instead of them, because a caller that wants the exact
// comparison must still have it. Zero returns octave 0 and negative returns the octave of the
// magnitude with the sign carried separately by `score_high`.
extern "C" __global__ void exact_score_octaves(
    const uint64_t *score_low,
    const int64_t *score_high,
    uint32_t count,
    uint32_t *octaves
) {
    uint32_t slot = blockIdx.x * blockDim.x + threadIdx.x;
    if (slot >= count) {
        return;
    }
    __int128 value = ((__int128)score_high[slot] << 64) | (__int128)(unsigned __int128)score_low[slot];
    unsigned __int128 magnitude = value < 0 ? (unsigned __int128)(-value) : (unsigned __int128)value;
    uint32_t octave = 0;
    while (magnitude != 0) {
        magnitude >>= 1;
        ++octave;
    }
    octaves[slot] = octave;
}

// ---------------------------------------------------------------------------------------------
// **THE MOUTH ITSELF, ON THE SURFACE WHOSE TRANSPORT LAW FITS IT.**
//
// Added 2026-08-18 after a measurement, and the measurement is the whole justification. Contracting
// one 26-million-element stored map cost:
//
//     disk read            26 ms
//     align on the serial chart   271 ms      <- decode and shift, one element at a time
//     upload 209 MB               11 ms
//     the deed                     2.25 ms
//
// The serial chart was spending **a hundred times the deed** preparing an operand, and the operand
// it prepared was four times the size of the material it prepared it from. `CLAUDE.md`: *"a bulk
// reduction left on the wrong surface"* is one of the three named causes of an idle card, and this
// was it. Decoding a stored codeword into a signed significand and shifting it onto one declared
// exponent is per-element, order-free, and has no serial dependence at all -- it is resident work
// by the material's own shape.
//
// Two consequences beyond the arithmetic. The bus now carries the **stored** two-octet codewords
// rather than the eight-octet aligned words, so the transfer falls by four. And the serial chart
// stops allocating a heap image of every map it touches.
//
// The refusals are preserved exactly. A non-finite pattern and an alignment that would leave the
// signed word are both flagged, and the serial chart raises the same named errors it always did --
// this moves the deed, it does not soften the law.

#define BFLOAT16_STORED_BITS 7
#define BFLOAT16_BIAS 127
#define BFLOAT16_HIDDEN (1u << BFLOAT16_STORED_BITS)
#define BFLOAT16_SUBNORMAL_ULP (1 - BFLOAT16_BIAS - BFLOAT16_STORED_BITS)
#define SIGNED_WORD_OCTAVES 63u

// `refused` bits: 1 = a non-finite pattern, 2 = an alignment past the signed word.
__device__ __forceinline__ int decode_bfloat16(uint16_t word, int64_t *significand, int *ulp) {
    int exponent = (int)((word >> BFLOAT16_STORED_BITS) & 0xffu);
    uint16_t mantissa = word & (uint16_t)(BFLOAT16_HIDDEN - 1u);
    if (exponent == 0xff) {
        return 0;
    }
    int64_t magnitude;
    if (exponent == 0) {
        magnitude = (int64_t)mantissa;
        *ulp = BFLOAT16_SUBNORMAL_ULP;
    } else {
        magnitude = (int64_t)(mantissa | (uint16_t)BFLOAT16_HIDDEN);
        *ulp = exponent - BFLOAT16_BIAS - BFLOAT16_STORED_BITS;
    }
    *significand = (word & 0x8000u) ? -magnitude : magnitude;
    return 1;
}

// The lowest unit-in-the-last-place among the nonzero stored words. **A zero contributes no frame**
// -- it has no scale of its own, and letting one drag the common exponent down would widen every
// other entry for nothing.
extern "C" __global__ void bfloat16_lowest_exponent(
    const uint16_t *words,
    uint32_t count,
    int32_t *lowest,      // one slot, pre-set to a ceiling by the caller
    uint32_t *refused     // one slot
) {
    uint32_t at = blockIdx.x * blockDim.x + threadIdx.x;
    if (at >= count) {
        return;
    }
    int64_t significand;
    int ulp;
    if (!decode_bfloat16(words[at], &significand, &ulp)) {
        atomicOr(refused, 1u);
        return;
    }
    if (significand != 0) {
        atomicMin(lowest, (int32_t)ulp);
    }
}

// Decode and shift onto the declared common exponent, and return the material's own octave count
// and hand population as reductions rather than as a second pass.
extern "C" __global__ void bfloat16_align(
    const uint16_t *words,
    uint32_t count,
    int32_t lowest,
    int64_t *entries,        // count
    uint32_t *entry_octaves, // one slot, pre-set to 0
    uint32_t *negatives,     // one slot, pre-set to 0
    uint32_t *refused        // one slot
) {
    uint32_t at = blockIdx.x * blockDim.x + threadIdx.x;
    if (at >= count) {
        return;
    }
    int64_t significand;
    int ulp;
    if (!decode_bfloat16(words[at], &significand, &ulp)) {
        atomicOr(refused, 1u);
        entries[at] = 0;
        return;
    }
    if (significand == 0) {
        entries[at] = 0;
        return;
    }
    uint32_t spread = (uint32_t)(ulp - lowest);
    uint64_t magnitude = (uint64_t)(significand < 0 ? -significand : significand);
    uint32_t octaves = 0;
    uint64_t scan = magnitude;
    while (scan != 0) {
        scan >>= 1;
        ++octaves;
    }
    // The demand is the entry's OWN octaves plus the spread. A shift that would cross the hand is
    // refused rather than wrapped -- the same law the serial chart holds, and for the same reason:
    // a wrapped shift flips a passage's hand and returns a plausible wrong number.
    if (spread >= SIGNED_WORD_OCTAVES || octaves + spread > SIGNED_WORD_OCTAVES) {
        atomicOr(refused, 2u);
        entries[at] = 0;
        return;
    }
    // Shift the unsigned magnitude and restore the hand afterward. Left-shifting a negative
    // signed integer is undefined in C++/CUDA even when the mathematical result fits.
    uint64_t shifted = magnitude << spread;
    entries[at] = significand < 0 ? -(int64_t)shifted : (int64_t)shifted;
    if (significand < 0) {
        atomicAdd(negatives, 1u);
    }
    atomicMax(entry_octaves, octaves + spread);
}

// **The absolute mass of each row**, which is what carries an incoming certified width through a
// contraction. Same shape as the score kernel and for the same reason: one thread per row, exact
// 128-bit accumulation, nothing rounded.
extern "C" __global__ void exact_row_absolute_mass(
    const int64_t *readout,
    uint32_t rows,
    uint32_t dim,
    uint64_t *mass_low,
    int64_t *mass_high
) {
    uint32_t row = blockIdx.x * blockDim.x + threadIdx.x;
    if (row >= rows) {
        return;
    }
    const int64_t *entries = readout + (size_t)row * (size_t)dim;
    __int128 accumulated = 0;
    for (uint32_t at = 0; at < dim; ++at) {
        int64_t value = entries[at];
        accumulated += (__int128)(value < 0 ? -value : value);
    }
    SplitScore split = split_of(accumulated);
    mass_low[row] = split.low;
    mass_high[row] = split.high;
}

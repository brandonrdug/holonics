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
// `E` and `u` arrive as integers aligned to one declared power of two by the host's float mouth, so
// every product is exact and every sum is exact. Accumulation is `__int128`: a `dim`-term sum of
// products of values bounded by `2^b` needs `2b + ceil(log2(dim))` bits, which for the material this
// was built for -- BF16 entries aligned to a common exponent, `dim = 2560` -- is far inside 128.
// **The host checks that bound before dispatch and refuses rather than truncating**; nothing here
// saturates, rounds, or clamps.
//
// A 128-bit value crosses back as two 64-bit halves, low then high, because the host carrier is
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

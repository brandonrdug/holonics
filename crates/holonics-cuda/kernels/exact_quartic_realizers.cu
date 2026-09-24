#include <stdint.h>

// Supported realizers of a quartic model, searched on the card.
//
// A rational point of `y^2 = c4 x^4 + c3 x^3 + c2 x^2 + c1 x + c0` at `x = n/d` in lowest terms
// is exactly an integer pair with
//
//     Q(n, d) = c4 n^4 + c3 n^3 d + c2 n^2 d^2 + c1 n d^3 + c0 d^4        a perfect square,
//
// because `(d^2 y)^2 = Q(n, d)`. Nothing here is approximate and nothing here is a float: the
// card decides a *refusal*, never an admission. A pair survives when `Q(n, d)` is a quadratic
// residue at every declared prime receiver; the exact square test is the caller's, over integers
// wider than this kernel carries. The declared receivers are the aperture and they are reported,
// so a survivor population is a measurement of this prime family and of no other.
//
// The residue tables are byte-per-residue rather than bit-packed: the whole family of primes used
// here sums to a few kilobytes, and a byte load costs one instruction where a bit extract costs
// four. `table[offset + r]` is 1 when `r` is a square in `F_p` (zero included) and 0 otherwise.

#define MAX_RECEIVERS 48

struct QuarticReceiver {
    uint32_t prime;
    uint32_t table_offset;
    uint32_t coefficient[5];  // c0..c4 reduced at `prime`
};

__device__ __forceinline__ uint32_t mul_mod(uint32_t a, uint32_t b, uint32_t p) {
    return (uint32_t)((uint64_t)a * (uint64_t)b % (uint64_t)p);
}

// One `d`, one contiguous run of `n`. `n` runs over the signed window the caller declares, so the
// sign lives in the index arithmetic and never in a branch.
extern "C" __global__ void quartic_realizer_refusal(
    const QuarticReceiver* __restrict__ receivers,
    uint32_t receiver_count,
    const uint8_t* __restrict__ residue_tables,
    int64_t denominator_low,
    int64_t denominator_count,
    int64_t numerator_low,
    int64_t numerator_count,
    int64_t* __restrict__ survivors,      // pairs (n, d) appended
    uint32_t* __restrict__ survivor_count,
    uint32_t survivor_capacity) {
    // Per-block: the denominator is fixed, so every `d`-dependent reduction is hoisted here.
    __shared__ uint32_t folded[MAX_RECEIVERS][4];
    __shared__ uint32_t prime_cache[MAX_RECEIVERS];
    __shared__ uint32_t offset_cache[MAX_RECEIVERS];
    __shared__ uint32_t leading_cache[MAX_RECEIVERS];

    const int64_t denominator = denominator_low + (int64_t)blockIdx.y;
    if (blockIdx.y >= denominator_count) {
        return;
    }

    for (uint32_t k = threadIdx.x; k < receiver_count; k += blockDim.x) {
        const uint32_t p = receivers[k].prime;
        const uint32_t dp = (uint32_t)(denominator % (int64_t)p);
        const uint32_t d2 = mul_mod(dp, dp, p);
        const uint32_t d3 = mul_mod(d2, dp, p);
        const uint32_t d4 = mul_mod(d3, dp, p);
        folded[k][0] = mul_mod(receivers[k].coefficient[3], dp, p);
        folded[k][1] = mul_mod(receivers[k].coefficient[2], d2, p);
        folded[k][2] = mul_mod(receivers[k].coefficient[1], d3, p);
        folded[k][3] = mul_mod(receivers[k].coefficient[0], d4, p);
        prime_cache[k] = p;
        offset_cache[k] = receivers[k].table_offset;
        leading_cache[k] = receivers[k].coefficient[4];
    }
    __syncthreads();

    const int64_t stride = (int64_t)blockDim.x * (int64_t)gridDim.x;
    for (int64_t index = (int64_t)blockIdx.x * blockDim.x + threadIdx.x; index < numerator_count;
         index += stride) {
        const int64_t numerator = numerator_low + index;
        bool refused = false;
        for (uint32_t k = 0; k < receiver_count && !refused; ++k) {
            const uint32_t p = prime_cache[k];
            int64_t reduced = numerator % (int64_t)p;
            if (reduced < 0) {
                reduced += (int64_t)p;
            }
            const uint32_t np = (uint32_t)reduced;
            uint32_t value = leading_cache[k];
            value = mul_mod(value, np, p) + folded[k][0];
            if (value >= p) value -= p;
            value = mul_mod(value, np, p) + folded[k][1];
            if (value >= p) value -= p;
            value = mul_mod(value, np, p) + folded[k][2];
            if (value >= p) value -= p;
            value = mul_mod(value, np, p) + folded[k][3];
            if (value >= p) value -= p;
            refused = residue_tables[offset_cache[k] + value] == 0;
        }
        if (!refused) {
            const uint32_t slot = atomicAdd(survivor_count, 1u);
            if (slot < survivor_capacity) {
                survivors[2 * slot] = numerator;
                survivors[2 * slot + 1] = denominator;
            }
        }
    }
}

// The integral-`x` face of the same law, `d = 1`, where the window is one dimensional and long.
// Kept separate because the folded reductions are then constants and the inner loop is half the
// instructions; the caller reports the two searches as distinct apertures, never as one.
extern "C" __global__ void quartic_realizer_refusal_integral(
    const QuarticReceiver* __restrict__ receivers,
    uint32_t receiver_count,
    const uint8_t* __restrict__ residue_tables,
    int64_t numerator_low,
    int64_t numerator_count,
    int64_t* __restrict__ survivors,
    uint32_t* __restrict__ survivor_count,
    uint32_t survivor_capacity) {
    __shared__ uint32_t coefficient[MAX_RECEIVERS][5];
    __shared__ uint32_t prime_cache[MAX_RECEIVERS];
    __shared__ uint32_t offset_cache[MAX_RECEIVERS];

    for (uint32_t k = threadIdx.x; k < receiver_count; k += blockDim.x) {
        for (int j = 0; j < 5; ++j) {
            coefficient[k][j] = receivers[k].coefficient[j];
        }
        prime_cache[k] = receivers[k].prime;
        offset_cache[k] = receivers[k].table_offset;
    }
    __syncthreads();

    const int64_t stride = (int64_t)blockDim.x * (int64_t)gridDim.x;
    for (int64_t index = (int64_t)blockIdx.x * blockDim.x + threadIdx.x; index < numerator_count;
         index += stride) {
        const int64_t numerator = numerator_low + index;
        bool refused = false;
        for (uint32_t k = 0; k < receiver_count && !refused; ++k) {
            const uint32_t p = prime_cache[k];
            int64_t reduced = numerator % (int64_t)p;
            if (reduced < 0) {
                reduced += (int64_t)p;
            }
            const uint32_t np = (uint32_t)reduced;
            uint32_t value = coefficient[k][4];
            for (int j = 3; j >= 0; --j) {
                value = mul_mod(value, np, p) + coefficient[k][j];
                if (value >= p) value -= p;
            }
            refused = residue_tables[offset_cache[k] + value] == 0;
        }
        if (!refused) {
            const uint32_t slot = atomicAdd(survivor_count, 1u);
            if (slot < survivor_capacity) {
                survivors[2 * slot] = numerator;
                survivors[2 * slot + 1] = 1;
            }
        }
    }
}

// ---------------------------------------------------------------------------------------------
// The specialization wheel.
//
// `a_p` of the specialized quartic depends only on `T mod p`. So specialization space partitions,
// one partition per prime receiver, into `p` residue classes, and every quantity read off the
// local point counts is a **sum over the partition** — a table lookup per receiver rather than a
// curve construction per `T`. This is the prime wheel with the curve's own local populations in
// the cells.
//
// The cell value stored is `round(SCALE * log(p / #E(F_p)))` as a signed 32-bit integer. The
// logarithm is a declared receiver quotient taken once, at table-build time, on the host; the
// card only adds integers, so the sweep itself carries no float and its ordering is exact.
// A cell whose specialization is singular carries zero: it refuses rather than contributing.

extern "C" __global__ void specialization_wheel_score(
    const int32_t* __restrict__ cells,     // concatenated, one run of length `prime` per receiver
    const uint32_t* __restrict__ primes,
    const uint32_t* __restrict__ offsets,
    uint32_t receiver_count,
    int64_t parameter_low,
    int64_t parameter_count,
    int32_t* __restrict__ scores) {
    const int64_t stride = (int64_t)blockDim.x * (int64_t)gridDim.x;
    for (int64_t index = (int64_t)blockIdx.x * blockDim.x + threadIdx.x; index < parameter_count;
         index += stride) {
        const int64_t parameter = parameter_low + index;
        int32_t total = 0;
        for (uint32_t k = 0; k < receiver_count; ++k) {
            const uint32_t p = primes[k];
            int64_t residue = parameter % (int64_t)p;
            if (residue < 0) {
                residue += (int64_t)p;
            }
            total += cells[offsets[k] + (uint32_t)residue];
        }
        scores[index] = total;
    }
}

// Build the wheel's cells on the card: one thread per (receiver, residue class).
//
// Each cell needs `a_p` of the quartic specialized at `T ≡ residue`, which is one pass over
// `F_p`. The work is `Σ p^2` over the receiver family — a few hundred million independent
// evaluations, which is what the card is for. The host reduces the five coefficient polynomials
// at each prime and takes the logarithm of the returned order; the card returns the integer
// trace and nothing else, so no float crosses this boundary.
extern "C" __global__ void specialization_wheel_traces(
    const uint32_t* __restrict__ primes,
    const uint32_t* __restrict__ cell_offsets,     // into the trace / residue-sign arrays
    const uint32_t* __restrict__ polynomial_offsets, // into `polynomials`, 5 runs per receiver
    const uint32_t* __restrict__ polynomial_degree,  // shared by all five, per receiver
    const uint32_t* __restrict__ polynomials,        // 5 * (degree+1) coefficients per receiver
    const int8_t* __restrict__ residue_signs,        // p entries per receiver
    uint32_t receiver_count,
    int32_t* __restrict__ traces) {
    const uint32_t receiver = blockIdx.y;
    if (receiver >= receiver_count) {
        return;
    }
    const uint32_t p = primes[receiver];
    const uint32_t cell_base = cell_offsets[receiver];
    const uint32_t poly_base = polynomial_offsets[receiver];
    const uint32_t degree = polynomial_degree[receiver];
    const int8_t* signs = residue_signs + cell_base;

    for (uint32_t residue = blockIdx.x * blockDim.x + threadIdx.x; residue < p;
         residue += blockDim.x * gridDim.x) {
        uint32_t coefficient[5];
        bool all_zero = true;
        for (int k = 0; k < 5; ++k) {
            const uint32_t* run = polynomials + poly_base + (uint32_t)k * (degree + 1);
            uint32_t value = 0;
            for (int j = (int)degree; j >= 0; --j) {
                value = mul_mod(value, residue, p) + run[j];
                if (value >= p) value -= p;
            }
            coefficient[k] = value;
            if (value != 0) all_zero = false;
        }
        if (all_zero) {
            traces[cell_base + residue] = INT32_MIN;  // singular class, refused by the host
            continue;
        }
        int32_t total = 0;
        for (uint32_t x = 0; x < p; ++x) {
            uint32_t value = coefficient[4];
            for (int k = 3; k >= 0; --k) {
                value = mul_mod(value, x, p) + coefficient[k];
                if (value >= p) value -= p;
            }
            total += signs[value];
        }
        // a_p = -(Σ χ(q(x)) + χ(leading))
        traces[cell_base + residue] = -(total + signs[coefficient[4]]);
    }
}

// ---------------------------------------------------------------------------------------------
// The surface, swept once, and coarse-grained by its fibration.
//
// A Mestre family is not a list of curves — it is one elliptic surface `y^2 = r(x, T)`, and `T` is
// a fibration of it. A realizer of the fibre over `T` is a point of the surface lying in that
// fibre. So the population that decides rank is measured by sweeping the *surface* once and
// partitioning its points by which fibre they fell into, rather than by scoring each fibre and
// then searching it. The partition is the receiver; the fibre population is the measurement; no
// heuristic stands between them.
//
// The five coefficients of `r` are polynomials in `T`. They are hoisted per fibre exactly as the
// rational kernel hoists its denominator, so the inner sweep over `x` costs the same four
// multiplications as before.
extern "C" __global__ void surface_realizer_refusal(
    const uint32_t* __restrict__ primes,
    const uint32_t* __restrict__ table_offsets,
    const uint32_t* __restrict__ polynomial_offsets,
    uint32_t polynomial_degree,
    const uint32_t* __restrict__ polynomials,   // 5 runs of (degree+1) per receiver
    const uint8_t* __restrict__ residue_tables,
    uint32_t receiver_count,
    int64_t fibre_low,
    int64_t fibre_count,
    int64_t abscissa_low,
    int64_t abscissa_count,
    int64_t* __restrict__ survivors,            // pairs (x, T)
    uint32_t* __restrict__ survivor_count,
    uint32_t survivor_capacity) {
    __shared__ uint32_t coefficient[MAX_RECEIVERS][5];
    __shared__ uint32_t prime_cache[MAX_RECEIVERS];
    __shared__ uint32_t offset_cache[MAX_RECEIVERS];

    if (blockIdx.y >= fibre_count) {
        return;
    }
    const int64_t fibre = fibre_low + (int64_t)blockIdx.y;

    for (uint32_t k = threadIdx.x; k < receiver_count; k += blockDim.x) {
        const uint32_t p = primes[k];
        int64_t reduced = fibre % (int64_t)p;
        if (reduced < 0) reduced += (int64_t)p;
        const uint32_t tp = (uint32_t)reduced;
        for (int j = 0; j < 5; ++j) {
            const uint32_t* run =
                polynomials + polynomial_offsets[k] + (uint32_t)j * (polynomial_degree + 1);
            uint32_t value = 0;
            for (int i = (int)polynomial_degree; i >= 0; --i) {
                value = mul_mod(value, tp, p) + run[i];
                if (value >= p) value -= p;
            }
            coefficient[k][j] = value;
        }
        prime_cache[k] = p;
        offset_cache[k] = table_offsets[k];
    }
    __syncthreads();

    const int64_t stride = (int64_t)blockDim.x * (int64_t)gridDim.x;
    for (int64_t index = (int64_t)blockIdx.x * blockDim.x + threadIdx.x; index < abscissa_count;
         index += stride) {
        const int64_t abscissa = abscissa_low + index;
        bool refused = false;
        for (uint32_t k = 0; k < receiver_count && !refused; ++k) {
            const uint32_t p = prime_cache[k];
            int64_t reduced = abscissa % (int64_t)p;
            if (reduced < 0) reduced += (int64_t)p;
            const uint32_t np = (uint32_t)reduced;
            uint32_t value = coefficient[k][4];
            for (int j = 3; j >= 0; --j) {
                value = mul_mod(value, np, p) + coefficient[k][j];
                if (value >= p) value -= p;
            }
            refused = residue_tables[offset_cache[k] + value] == 0;
        }
        if (!refused) {
            const uint32_t slot = atomicAdd(survivor_count, 1u);
            if (slot < survivor_capacity) {
                survivors[2 * slot] = abscissa;
                survivors[2 * slot + 1] = fibre;
            }
        }
    }
}

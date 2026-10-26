// **The gated tower's training pass on the card** (#404, #76; owner `src/hnn/tower.rs`).
//
// The forward and the reverse scan of `holonics::hnn::tower` (its module law; the host owner is
// `Tower::step` and `Tower::reverse_joined`) for the declaration the card carries: gated modes,
// rectifying contacts, no turn, no pump, no pair or ring face, no passage credit. Every quantity
// is the host's integer numerator on the host's grain, every product's remainder released to the
// nearest numerator (half away from zero), every quotient the host's, every sum exact: a sum runs
// in 64 bits where the host's bound on its terms admits it and in 128 bits otherwise, and either
// gives the integer sum, so the card's bits are the host's whatever the order of its threads.
// No float.
//
// The kernels (realization reported by `src/hnn/tower.rs`):
// - `tower_transpose`: each matrix family copied transposed beside the material, so a thread that
//   owns one output of a forward read walks its row's weights at consecutive addresses across the
//   warp. The reverse reads the material as it is (its outputs are the columns).
// - `tower_forward`: one block a stream; the block runs the stream's cells in order (each cell's
//   state moves from the one before: time is sequential within a stream) and, within a cell, its
//   threads own the outputs of each read (the pushes and gates, the modes, the reads, the contacts,
//   the return, the readout), the stages ordered by barriers. The modes' states stay in shared
//   memory across the cells. With `keep`, the cell's temporaries are written for the reverse.
// - `tower_reverse_top`, `tower_reverse_contacts`, `tower_reverse_dx`: one block a cell of a stream
//   (cells are independent there: each reads its own forward temporaries and covector).
// - `tower_reverse_modes`: one block a stream, one thread a mode, the cells in reverse order (the
//   scan `G_h(t) = read covector + conj(λ_(t+1)) G_h(t+1)`), with each cell's gated move adjoint.
// - `tower_outer`: the families' outer sums `Σ_(s,t) y_(s,t) x_(s,t)ᵀ` over every stream's cells,
//   a tile of 16 × 64 outputs a block, four a thread; summed per stream in 64 bits when that
//   stream's bound `Σ_t max|y_t| max(max|x_t|, 1)` is below 2^63, in 128 bits otherwise.
// - `tower_encoding`, `tower_moves`: the encoding's covector (each cell's bottom covector at its
//   class) and the moves' Cartesian covectors summed over the streams.

#include <stdint.h>

typedef __int128 wide;
typedef unsigned __int128 uwide;

#define TOWER_MAX_LEVELS 4
#define TOWER_THREADS 256

// Refusal bits (`src/hnn/tower.rs` names them).
#define TOWER_REFUSED_CARRIER 1u
#define TOWER_REFUSED_WORD64 2u
#define TOWER_REFUSED_WORD32 4u
#define TOWER_REFUSED_UNIT 8u
#define TOWER_REFUSED_CLASS 16u

// The grains (`holonics::hnn::tower`).
#define FACE_BITS 16
#define MATERIAL_BITS 24
#define MOVE_BITS 30
#define STATE_BITS 24
#define COVECTOR_BITS 24
#define UNIT_BITS 62
#define MARGIN 12
#define GATE_REACH 2

struct TowerLevel {
    uint64_t move_re, move_im, push_re, push_im, read_re, read_im, contact, contact_bias, ret,
        ret_bias, gate, gate_bias;
    // max |w| of push (re, im), read (re, im), contact, return, gate
    uint64_t reach[7];
};

struct TowerLaw {
    uint32_t alphabet, width, modes, contacts, levels, cells, streams, face_digits;
    uint32_t move_digits, families, pad0, pad1;
    uint64_t encoding, readout, readout_bias, readout_reach;
    int64_t ln2_square;
    TowerLevel level[TOWER_MAX_LEVELS];
};

// The section's resident buffers ([s][t][l][…] row-major; `q = s·T + t` a cell of a stream).
struct TowerFrame {
    const int32_t *theta;
    int32_t *theta_t;
    const uint64_t *families; // [families][3]: offset, rows, cols
    const int64_t *gates;     // [L][N][4]: unit re, unit im, |λ|, log₂|λ| on 2^(−30)
    const uint64_t *roots;    // the face's roots, then the moves'
    const uint32_t *classes;  // [S][T + 1]
    const int32_t *targets;   // [S][T], −1 where compared with nothing
    const int64_t *opening;   // [S][L][N][2]
    int64_t *ends;            // [S][L][N][2]
    uint64_t *faces;          // [S][T][3]: the target's mass, the total's low and high words
    uint64_t *swell;          // [L][4]
    uint32_t *status;         // [S]
    int32_t *input;           // [S][T][L][W]
    int64_t *push;            // [S][T][L][2N] re block, im block
    int64_t *state;           // [S][T][L][N][2]
    int64_t *face;            // [S][T][L][2N] re block, im block
    int32_t *read;            // [S][T][L][W]
    int64_t *scale;           // [S][T][L]
    int32_t *drive;           // [S][T][L][F]
    int32_t *conduct;         // [S][T][L][F]
    int64_t *moves;           // [S][T][L][N][6]: open, ρ, γ, λ re, λ im, held
    int32_t *top;             // [S][T][W]
    uint64_t *masses;         // [S][T][A]
    uint64_t *totals;         // [S][T][2]
    uint64_t *r_input, *r_face_re, *r_face_im, *r_read, *r_conduct; // [S][T][L]
    uint64_t *r_top;                                                  // [S][T]
    int64_t *dz;                                                      // [S][T][A]
    int64_t *dx;                                                      // [S][T][W]
    int64_t *dy;                                                      // [S][T][L][W]
    int64_t *da;                                                      // [S][T][L][F]
    int64_t *dread;                                                   // [S][T][L][W]
    int64_t *readcov;                                                 // [S][T][L][2N]
    int64_t *gre, *gim, *dq;                                          // [S][T][L][N]
    uint64_t *r_dz;                                                   // [S][T]
    uint64_t *r_dy, *r_da, *r_dread, *r_gre, *r_gim, *r_dq;           // [S][T][L]
    wide *moves_g;                                                    // [S][L][N][2]
    wide *gradient;                                                   // [len]
};

// -------------------------------------------------------------------------------------------
// the host's integer law

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
    return x >= 0 ? (x + k / 2) / k : -((-x + k / 2) / k);
}

__device__ __forceinline__ uint64_t magnitude(int64_t v) {
    return v < 0 ? (uint64_t)0 - (uint64_t)v : (uint64_t)v;
}

__device__ __forceinline__ int64_t fit64(wide v, uint32_t *st) {
    if (v > (wide)INT64_MAX || v < (wide)INT64_MIN) {
        atomicOr(st, TOWER_REFUSED_WORD64);
        return 0;
    }
    return (int64_t)v;
}

__device__ __forceinline__ int32_t fit32(wide v, uint32_t *st) {
    if (v > (wide)INT32_MAX || v < (wide)INT32_MIN) {
        atomicOr(st, TOWER_REFUSED_WORD32);
        return 0;
    }
    return (int32_t)v;
}

// The host's affine bound `wmax · xmax · (cols + 1)` in `u128` (its wrapping product): refused at
// `2^126`, narrow below `2^62`.
__device__ __forceinline__ bool narrow_terms(uint64_t wmax, uint64_t xmax, uint32_t cols, uint32_t *st) {
    const uwide terms = (uwide)wmax * (uwide)xmax * (uwide)(cols + 1);
    if (terms >= ((uwide)1 << 126)) {
        atomicOr(st, TOWER_REFUSED_CARRIER);
    }
    return terms < ((uwide)1 << 62);
}

// The host's transposed bound `wmax · ymax · (rows + 1) < 2^62` (no refusal: its sum runs in 128 bits).
__device__ __forceinline__ bool narrow_rows(uint64_t wmax, uint64_t ymax, uint32_t rows) {
    return (uwide)wmax * (uwide)ymax * (uwide)(rows + 1) < ((uwide)1 << 62);
}

// `Σ_k base[k · stride] · v[k]`, in 64 bits when `narrow` and in 128 otherwise.
template <typename V>
__device__ __forceinline__ wide dot(const int32_t *base, uint64_t stride, uint32_t count, const V *v, bool narrow) {
    if (narrow) {
        // Four partial sums carry independent loads in flight; under the narrow bound each is
        // exact in 64 bits and so is their sum.
        int64_t s0 = 0, s1 = 0, s2 = 0, s3 = 0;
        uint32_t k = 0;
        for (; k + 4 <= count; k += 4) {
            s0 += (int64_t)base[k * stride] * (int64_t)v[k];
            s1 += (int64_t)base[(k + 1) * stride] * (int64_t)v[k + 1];
            s2 += (int64_t)base[(k + 2) * stride] * (int64_t)v[k + 2];
            s3 += (int64_t)base[(k + 3) * stride] * (int64_t)v[k + 3];
        }
        for (; k < count; k++) {
            s0 += (int64_t)base[k * stride] * (int64_t)v[k];
        }
        return (wide)s0 + s1 + s2 + s3;
    }
    wide s = 0;
    for (uint32_t k = 0; k < count; k++) {
        s += (wide)base[k * stride] * (wide)v[k];
    }
    return s;
}

// The exact floor square roots.
__device__ uint64_t isqrt64(uint64_t n) {
    uint64_t res = 0;
    uint64_t bit = (uint64_t)1 << 62;
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

// `2^(x / 2^X)` for `x ≤ 0` on `2^(−62)`, at least one grain (`Exponential::below_one`): the
// navigator's roots selected by the binary digits of the fraction, each product released at
// `2^(−62)`. Every root lies below `2^63` and the value at most `2^62`, so a product is below `2^125`.
__device__ uint64_t below_one(wide x, const uint64_t *roots, uint32_t digits) {
    const wide m = -x;
    const wide whole = m >> digits;
    const wide frac = m & (((wide)1 << digits) - 1);
    wide shift;
    wide rest;
    if (frac == 0) {
        shift = whole;
        rest = 0;
    } else {
        shift = whole + 1;
        rest = ((wide)1 << digits) - frac;
    }
    uint64_t value = (uint64_t)1 << UNIT_BITS;
    for (uint32_t i = 0; i < digits; i++) {
        if (rest & ((wide)1 << (digits - 1 - i))) {
            const uint64_t lo = value * roots[i];
            const uint64_t hi = __umul64hi(value, roots[i]);
            value = (hi << (64 - UNIT_BITS)) | (lo >> UNIT_BITS);
        }
    }
    const uint64_t shifted = shift >= 64 ? 0 : value >> (uint32_t)shift;
    return shifted == 0 ? 1 : shifted;
}

// `r = 1/(1 + 2^(−q))` on `2^(−30)`, `q` on `2^(−16)` (`logistic`).
__device__ wide logistic(int64_t q, const uint64_t *roots, uint32_t digits) {
    const wide unit = (wide)1 << UNIT_BITS;
    if (q >= 0) {
        const wide e = below_one(-(wide)q, roots, digits);
        return div_nearest((wide)1 << (UNIT_BITS + MOVE_BITS), unit + e);
    }
    const wide e = below_one((wide)q, roots, digits);
    return div_nearest(e << MOVE_BITS, unit + e);
}

// -------------------------------------------------------------------------------------------
// block reductions (every thread of the block calls them; the result is the block's)

__device__ uint64_t block_max(uint64_t v, uint64_t *red) {
    for (int o = 16; o > 0; o >>= 1) {
        const uint64_t w = __shfl_xor_sync(0xffffffffu, v, o);
        v = w > v ? w : v;
    }
    __syncthreads();
    if ((threadIdx.x & 31) == 0) {
        red[threadIdx.x >> 5] = v;
    }
    __syncthreads();
    uint64_t r = 0;
    for (uint32_t i = 0; i < (blockDim.x + 31) / 32; i++) {
        r = red[i] > r ? red[i] : r;
    }
    return r;
}

__device__ int64_t block_max_signed(int64_t v, uint64_t *red) {
    // Order-preserving map of the signed words onto the unsigned ones.
    const uint64_t key = (uint64_t)v ^ ((uint64_t)1 << 63);
    return (int64_t)(block_max(key, red) ^ ((uint64_t)1 << 63));
}

__device__ uwide shfl_wide(uwide v, int o) {
    const uint64_t lo = __shfl_xor_sync(0xffffffffu, (uint64_t)v, o);
    const uint64_t hi = __shfl_xor_sync(0xffffffffu, (uint64_t)(v >> 64), o);
    return ((uwide)hi << 64) | lo;
}

// The ring sum of the block's words (`Z/2^128`, the host's wrapping `i128`/`u128` sum).
__device__ uwide block_sum(uwide v, uwide *red) {
    for (int o = 16; o > 0; o >>= 1) {
        v += shfl_wide(v, o);
    }
    __syncthreads();
    if ((threadIdx.x & 31) == 0) {
        red[threadIdx.x >> 5] = v;
    }
    __syncthreads();
    uwide r = 0;
    for (uint32_t i = 0; i < (blockDim.x + 31) / 32; i++) {
        r += red[i];
    }
    return r;
}

// -------------------------------------------------------------------------------------------
// the transposed material

extern "C" __global__ void tower_transpose(TowerLaw law, TowerFrame fr) {
    const uint64_t *family = fr.families + 3 * blockIdx.y;
    const uint64_t offset = family[0], rows = family[1], cols = family[2];
    for (uint64_t e = (uint64_t)blockIdx.x * blockDim.x + threadIdx.x; e < rows * cols;
         e += (uint64_t)gridDim.x * blockDim.x) {
        const uint64_t o = e / cols, j = e % cols;
        fr.theta_t[offset + j * rows + o] = fr.theta[offset + e];
    }
}

// -------------------------------------------------------------------------------------------
// the forward

__device__ __forceinline__ unsigned char *carve(unsigned char *&at, uint64_t octets) {
    unsigned char *p = at;
    at += (octets + 15) & ~(uint64_t)15;
    return p;
}

extern "C" __global__ void __launch_bounds__(TOWER_THREADS) tower_forward(TowerLaw law, TowerFrame fr, uint32_t keep) {
    const uint32_t s = blockIdx.x, tid = threadIdx.x, B = blockDim.x;
    const uint32_t A = law.alphabet, W = law.width, N = law.modes, F = law.contacts, L = law.levels,
                   T = law.cells;
    const uint32_t G = B / W > 0 ? B / W : 1;
    extern __shared__ __align__(16) unsigned char smem[];
    unsigned char *at = smem;
    wide *part = (wide *)carve(at, sizeof(wide) * G * W);
    uwide *redw = (uwide *)carve(at, sizeof(uwide) * 32);
    int64_t *h = (int64_t *)carve(at, 8ull * L * 2 * N);
    int64_t *pq = (int64_t *)carve(at, 8ull * 3 * N);
    int64_t *fc = (int64_t *)carve(at, 8ull * 2 * N);
    int64_t *rab = (int64_t *)carve(at, 8ull * 2 * W);
    int64_t *raw = (int64_t *)carve(at, 8ull * W);
    int64_t *z = (int64_t *)carve(at, 8ull * A);
    uint64_t *ms = (uint64_t *)carve(at, 8ull * A);
    uint64_t *red = (uint64_t *)carve(at, 8ull * 32);
    int32_t *x = (int32_t *)carve(at, 4ull * W);
    int32_t *nx = (int32_t *)carve(at, 4ull * W);
    int32_t *rd = (int32_t *)carve(at, 4ull * W);
    int32_t *dv = (int32_t *)carve(at, 4ull * F);
    int32_t *cd = (int32_t *)carve(at, 4ull * F);
    __shared__ uint32_t st;
    __shared__ int64_t scale_s;
    if (tid == 0) {
        st = 0;
    }
    for (uint32_t i = tid; i < L * 2 * N; i += B) {
        h[i] = fr.opening[(uint64_t)s * L * 2 * N + i];
    }
    uint64_t sw[TOWER_MAX_LEVELS][4] = {};
    const int32_t *th = fr.theta;
    const int32_t *tt = fr.theta_t;
    const uint64_t *face_roots = fr.roots;
    const uint64_t *move_roots = fr.roots + law.face_digits;
    const wide radius = ((wide)1 << MOVE_BITS) - ((wide)1 << (MOVE_BITS - MARGIN));
    __syncthreads();
    for (uint32_t t = 0; t < T; t++) {
        const uint64_t qc = (uint64_t)s * T + t;
        uint32_t u = fr.classes[(uint64_t)s * (T + 1) + t];
        if (u >= A) {
            if (tid == 0) {
                atomicOr(&st, TOWER_REFUSED_CLASS);
            }
            u = 0;
        }
        for (uint32_t j = tid; j < W; j += B) {
            x[j] = th[law.encoding + (uint64_t)u * W + j];
        }
        __syncthreads();
        uint64_t m = 0;
        for (uint32_t j = tid; j < W; j += B) {
            const uint64_t v = magnitude(x[j]);
            m = v > m ? v : m;
        }
        uint64_t xmax = block_max(m, red);
        for (uint32_t l = 0; l < L; l++) {
            const TowerLevel &lv = law.level[l];
            const uint64_t q = qc * L + l;
            // The pushes on 2^(−40) released to the state's 2^(−24), and the gate's logit.
            const bool n_re = narrow_terms(lv.reach[0], xmax, W, &st);
            const bool n_im = narrow_terms(lv.reach[1], xmax, W, &st);
            const bool n_gate = narrow_terms(lv.reach[6], xmax, W, &st);
            for (uint32_t o = tid; o < 3 * N; o += B) {
                const uint32_t fam = o / N, k = o % N;
                if (fam == 2) {
                    wide sum = dot(tt + lv.gate + k, N, W, x, n_gate);
                    sum += (wide)th[lv.gate_bias + k] << MATERIAL_BITS;
                    pq[o] = fit64(rel(sum, MATERIAL_BITS), &st);
                } else {
                    const wide sum = dot(tt + (fam == 0 ? lv.push_re : lv.push_im) + k, N, W, x, fam == 0 ? n_re : n_im);
                    pq[o] = fit64(rel(sum, MATERIAL_BITS + FACE_BITS - STATE_BITS), &st);
                }
            }
            __syncthreads();
            // The gated move λ_t = |λ|^(c r) u, held at the margin, and the state h = λ_t h + γ_t B x.
            for (uint32_t k = tid; k < N; k += B) {
                const int64_t *gf = fr.gates + ((uint64_t)l * N + k) * 4;
                const wide open = logistic(pq[2 * N + k], face_roots, law.face_digits);
                const wide exponent = rel((wide)GATE_REACH * open * gf[3], MOVE_BITS);
                wide rho = rel((wide)below_one(exponent, move_roots, law.move_digits), UNIT_BITS - MOVE_BITS);
                const bool held = rho > radius;
                if (held) {
                    rho = radius;
                }
                const wide lr = rel(rho * gf[0], MOVE_BITS);
                const wide li = rel(rho * gf[1], MOVE_BITS);
                wide gap = ((wide)1 << (2 * MOVE_BITS)) - (lr * lr + li * li);
                gap = gap < 0 ? 0 : gap;
                uint64_t gamma = isqrt64((uint64_t)gap);
                if (gamma == 0) {
                    atomicOr(&st, TOWER_REFUSED_UNIT);
                    gamma = 1;
                }
                const wide hr = h[(l * N + k) * 2], hi = h[(l * N + k) * 2 + 1];
                const wide pr = rel((wide)gamma * pq[k], MOVE_BITS);
                const wide pi = rel((wide)gamma * pq[N + k], MOVE_BITS);
                const int64_t nr = fit64(rel(lr * hr - li * hi, MOVE_BITS) + pr, &st);
                const int64_t ni = fit64(rel(lr * hi + li * hr, MOVE_BITS) + pi, &st);
                h[(l * N + k) * 2] = nr;
                h[(l * N + k) * 2 + 1] = ni;
                fc[k] = fit64(rel(nr, STATE_BITS - FACE_BITS), &st);
                fc[N + k] = fit64(rel(ni, STATE_BITS - FACE_BITS), &st);
                if (keep) {
                    fr.push[q * 2 * N + k] = pq[k];
                    fr.push[q * 2 * N + N + k] = pq[N + k];
                    fr.state[(q * N + k) * 2] = nr;
                    fr.state[(q * N + k) * 2 + 1] = ni;
                    fr.face[q * 2 * N + k] = fc[k];
                    fr.face[q * 2 * N + N + k] = fc[N + k];
                    int64_t *mv = fr.moves + (q * N + k) * 6;
                    mv[0] = (int64_t)open;
                    mv[1] = (int64_t)rho;
                    mv[2] = (int64_t)gamma;
                    mv[3] = (int64_t)lr;
                    mv[4] = (int64_t)li;
                    mv[5] = held ? 1 : 0;
                }
            }
            __syncthreads();
            uint64_t mre = 0, mim = 0;
            for (uint32_t k = tid; k < N; k += B) {
                const uint64_t a = magnitude(fc[k]), b = magnitude(fc[N + k]);
                mre = a > mre ? a : mre;
                mim = b > mim ? b : mim;
            }
            const uint64_t fre = block_max(mre, red);
            const uint64_t fim = block_max(mim, red);
            // The read Re(C h) = C_re h_re − C_im h_im on 2^(−40), released to 2^(−16).
            const bool n_a = narrow_terms(lv.reach[2], fre, N, &st);
            const bool n_b = narrow_terms(lv.reach[3], fim, N, &st);
            for (uint32_t o = tid; o < 2 * W; o += B) {
                const uint32_t j = o % W;
                const bool im = o >= W;
                const wide sum = dot(tt + (im ? lv.read_im : lv.read_re) + j, W, N, fc + (im ? N : 0), im ? n_b : n_a);
                rab[o] = fit64(sum, &st);
            }
            __syncthreads();
            uwide power = 0;
            for (uint32_t j = tid; j < W; j += B) {
                const int64_t r = fit64(rel((wide)rab[j] - (wide)rab[W + j], MATERIAL_BITS), &st);
                raw[j] = r;
                power += (uwide)((wide)r * (wide)r);
            }
            power = block_sum(power, redw);
            if (tid == 0) {
                const uwide root = isqrt128((uwide)((wide)power / (wide)W));
                if (root > (uwide)INT64_MAX) {
                    atomicOr(&st, TOWER_REFUSED_WORD64);
                }
                scale_s = root > (uwide)INT64_MAX ? 0 : (int64_t)root;
            }
            __syncthreads();
            const int64_t scale = scale_s;
            m = 0;
            for (uint32_t j = tid; j < W; j += B) {
                rd[j] = scale == 0 ? 0 : fit32(div_nearest((wide)raw[j] << FACE_BITS, scale), &st);
                const uint64_t v = magnitude(rd[j]);
                m = v > m ? v : m;
            }
            const uint64_t rmax = block_max(m, red);
            // The rectifying contacts.
            const bool n_c = narrow_terms(lv.reach[4], rmax, W, &st);
            m = 0;
            uint64_t mc = 0;
            for (uint32_t o = tid; o < F; o += B) {
                wide sum = dot(tt + lv.contact + o, F, W, rd, n_c);
                sum += (wide)th[lv.contact_bias + o] << MATERIAL_BITS;
                const int32_t d = fit32(fit64(rel(sum, MATERIAL_BITS), &st), &st);
                dv[o] = d;
                cd[o] = d > 0 ? d : 0;
                const uint64_t v = magnitude(d);
                m = v > m ? v : m;
                mc = (uint64_t)cd[o] > mc ? (uint64_t)cd[o] : mc;
            }
            const uint64_t dmax = block_max(m, red);
            const uint64_t cmax = block_max(mc, red);
            // The return, its sum split over `G` groups of the contacts.
            const bool n_r = narrow_terms(lv.reach[5], cmax, F, &st);
            for (uint32_t idx = tid; idx < G * W; idx += B) {
                const uint32_t g = idx / W, j = idx % W;
                const uint32_t from = (uint32_t)((uint64_t)F * g / G), to = (uint32_t)((uint64_t)F * (g + 1) / G);
                part[idx] = dot(tt + lv.ret + (uint64_t)from * W + j, W, to - from, cd + from, n_r);
            }
            __syncthreads();
            for (uint32_t j = tid; j < W; j += B) {
                wide sum = 0;
                for (uint32_t g = 0; g < G; g++) {
                    sum += part[g * W + j];
                }
                sum += (wide)th[lv.ret_bias + j] << MATERIAL_BITS;
                const int64_t r = fit64(rel(sum, MATERIAL_BITS), &st);
                nx[j] = fit32((wide)x[j] + (wide)r, &st);
            }
            if (keep) {
                for (uint32_t j = tid; j < W; j += B) {
                    fr.input[q * W + j] = x[j];
                    fr.read[q * W + j] = rd[j];
                }
                for (uint32_t o = tid; o < F; o += B) {
                    fr.drive[q * F + o] = dv[o];
                    fr.conduct[q * F + o] = cd[o];
                }
                if (tid == 0) {
                    fr.scale[q] = scale;
                    fr.r_input[q] = xmax;
                    fr.r_face_re[q] = fre;
                    fr.r_face_im[q] = fim;
                    fr.r_read[q] = rmax;
                    fr.r_conduct[q] = cmax;
                }
            }
            if (tid == 0 && l < TOWER_MAX_LEVELS) {
                const uint64_t fmax = fre > fim ? fre : fim;
                sw[l][0] = xmax > sw[l][0] ? xmax : sw[l][0];
                sw[l][1] = fmax > sw[l][1] ? fmax : sw[l][1];
                sw[l][2] = (uint64_t)scale > sw[l][2] ? (uint64_t)scale : sw[l][2];
                sw[l][3] = dmax > sw[l][3] ? dmax : sw[l][3];
            }
            __syncthreads();
            m = 0;
            for (uint32_t j = tid; j < W; j += B) {
                x[j] = nx[j];
                const uint64_t v = magnitude(nx[j]);
                m = v > m ? v : m;
            }
            xmax = block_max(m, red);
        }
        // The readout's face z = U x + c, and the masses 2^(z − z_max) on 2^(−62).
        const bool n_z = narrow_terms(law.readout_reach, xmax, W, &st);
        int64_t zm = INT64_MIN;
        for (uint32_t c = tid; c < A; c += B) {
            wide sum = dot(tt + law.readout + c, A, W, x, n_z);
            sum += (wide)th[law.readout_bias + c] << MATERIAL_BITS;
            z[c] = fit64(rel(sum, MATERIAL_BITS), &st);
            zm = z[c] > zm ? z[c] : zm;
        }
        const int64_t zmax = block_max_signed(zm, red);
        uwide total = 0;
        for (uint32_t c = tid; c < A; c += B) {
            ms[c] = below_one((wide)z[c] - (wide)zmax, face_roots, law.face_digits);
            total += ms[c];
        }
        total = block_sum(total, redw);
        if (tid == 0) {
            const int32_t target = fr.targets[qc];
            fr.faces[qc * 3] = target >= 0 && (uint32_t)target < A ? ms[target] : 0;
            fr.faces[qc * 3 + 1] = (uint64_t)total;
            fr.faces[qc * 3 + 2] = (uint64_t)(total >> 64);
        }
        if (keep) {
            for (uint32_t c = tid; c < A; c += B) {
                fr.masses[qc * A + c] = ms[c];
            }
            for (uint32_t j = tid; j < W; j += B) {
                fr.top[qc * W + j] = x[j];
            }
            if (tid == 0) {
                fr.totals[qc * 2] = (uint64_t)total;
                fr.totals[qc * 2 + 1] = (uint64_t)(total >> 64);
                fr.r_top[qc] = xmax;
            }
        }
        __syncthreads();
    }
    for (uint32_t i = tid; i < L * 2 * N; i += B) {
        fr.ends[(uint64_t)s * L * 2 * N + i] = h[i];
    }
    if (tid == 0) {
        if (st != 0) {
            atomicOr(fr.status + s, st);
        }
        if (keep) {
            for (uint32_t l = 0; l < L && l < TOWER_MAX_LEVELS; l++) {
                for (uint32_t i = 0; i < 4; i++) {
                    atomicMax((unsigned long long *)(fr.swell + l * 4 + i), (unsigned long long)sw[l][i]);
                }
            }
        }
    }
}

// -------------------------------------------------------------------------------------------
// the reverse

// The face's covector `p̂ − [· = target]` on 2^(−24) and the readout's covector to the top face.
extern "C" __global__ void __launch_bounds__(TOWER_THREADS) tower_reverse_top(TowerLaw law, TowerFrame fr) {
    const uint64_t q = blockIdx.x;
    const uint32_t s = (uint32_t)(q / law.cells), tid = threadIdx.x, B = blockDim.x;
    const uint32_t A = law.alphabet, W = law.width;
    const uint32_t G = B / W > 0 ? B / W : 1;
    extern __shared__ __align__(16) unsigned char smem[];
    unsigned char *at = smem;
    wide *part = (wide *)carve(at, sizeof(wide) * G * W);
    int64_t *dz = (int64_t *)carve(at, 8ull * A);
    uint64_t *red = (uint64_t *)carve(at, 8ull * 32);
    __shared__ uint32_t st;
    if (tid == 0) {
        st = 0;
    }
    const int32_t target = fr.targets[q];
    const uwide total = ((uwide)fr.totals[q * 2 + 1] << 64) | fr.totals[q * 2];
    uint64_t m = 0;
    for (uint32_t c = tid; c < A; c += B) {
        int64_t v = 0;
        if (target >= 0) {
            const uwide p = (((uwide)fr.masses[q * A + c] << COVECTOR_BITS) + total / 2) / total;
            v = (int64_t)(uint64_t)p - ((int32_t)c == target ? ((int64_t)1 << COVECTOR_BITS) : 0);
        }
        dz[c] = v;
        fr.dz[q * A + c] = v;
        const uint64_t a = magnitude(v);
        m = a > m ? a : m;
    }
    const uint64_t ymax = block_max(m, red);
    if (tid == 0) {
        fr.r_dz[q] = ymax;
    }
    const bool narrow = narrow_rows(law.readout_reach, ymax, A);
    for (uint32_t idx = tid; idx < G * W; idx += B) {
        const uint32_t g = idx / W, j = idx % W;
        const uint32_t from = (uint32_t)((uint64_t)A * g / G), to = (uint32_t)((uint64_t)A * (g + 1) / G);
        part[idx] = dot(fr.theta + law.readout + (uint64_t)from * W + j, W, to - from, dz + from, narrow);
    }
    __syncthreads();
    for (uint32_t j = tid; j < W; j += B) {
        wide sum = 0;
        for (uint32_t g = 0; g < G; g++) {
            sum += part[g * W + j];
        }
        fr.dx[q * W + j] = fit64(rel(sum, MATERIAL_BITS), &st);
    }
    __syncthreads();
    if (tid == 0 && st != 0) {
        atomicOr(fr.status + s, st);
    }
}

// One level's contacts and read, cell by cell: the covector reaching the level's output `dy`,
// the return's and the rectifier's adjoints, the ratio's adjoint and the modes' read covector.
extern "C" __global__ void __launch_bounds__(TOWER_THREADS) tower_reverse_contacts(TowerLaw law, TowerFrame fr, uint32_t l) {
    const uint64_t q = blockIdx.x, ql = q * law.levels + l;
    const uint32_t s = (uint32_t)(q / law.cells), tid = threadIdx.x, B = blockDim.x;
    const uint32_t W = law.width, N = law.modes, F = law.contacts;
    const uint32_t G = B / W > 0 ? B / W : 1;
    const TowerLevel &lv = law.level[l];
    extern __shared__ __align__(16) unsigned char smem[];
    unsigned char *at = smem;
    wide *part = (wide *)carve(at, sizeof(wide) * G * W);
    uwide *redw = (uwide *)carve(at, sizeof(uwide) * 32);
    int64_t *dy = (int64_t *)carve(at, 8ull * W);
    int64_t *da = (int64_t *)carve(at, 8ull * F);
    int64_t *dr = (int64_t *)carve(at, 8ull * W);
    int64_t *dread = (int64_t *)carve(at, 8ull * W);
    uint64_t *red = (uint64_t *)carve(at, 8ull * 32);
    __shared__ uint32_t st;
    if (tid == 0) {
        st = 0;
    }
    uint64_t m = 0;
    for (uint32_t j = tid; j < W; j += B) {
        const int64_t v = fr.dx[q * W + j];
        dy[j] = v;
        fr.dy[ql * W + j] = v;
        const uint64_t a = magnitude(v);
        m = a > m ? a : m;
    }
    const uint64_t ymax = block_max(m, red);
    // dv = Rᵀ dy, and the rectifier passes it where the drive conducts.
    const bool n_v = narrow_rows(lv.reach[5], ymax, W);
    m = 0;
    for (uint32_t i = tid; i < F; i += B) {
        const int64_t v = fit64(rel(dot(fr.theta + lv.ret + i, F, W, dy, n_v), MATERIAL_BITS), &st);
        const int64_t a = fr.drive[ql * F + i] > 0 ? v : 0;
        da[i] = a;
        fr.da[ql * F + i] = a;
        const uint64_t mag = magnitude(a);
        m = mag > m ? mag : m;
    }
    const uint64_t amax = block_max(m, red);
    // dr = Kᵀ da, split over `G` groups of the contacts.
    const bool n_r = narrow_rows(lv.reach[4], amax, F);
    for (uint32_t idx = tid; idx < G * W; idx += B) {
        const uint32_t g = idx / W, j = idx % W;
        const uint32_t from = (uint32_t)((uint64_t)F * g / G), to = (uint32_t)((uint64_t)F * (g + 1) / G);
        part[idx] = dot(fr.theta + lv.contact + (uint64_t)from * W + j, W, to - from, da + from, n_r);
    }
    __syncthreads();
    for (uint32_t j = tid; j < W; j += B) {
        wide sum = 0;
        for (uint32_t g = 0; g < G; g++) {
            sum += part[g * W + j];
        }
        dr[j] = fit64(rel(sum, MATERIAL_BITS), &st);
    }
    __syncthreads();
    // The ratio's adjoint ∂r = (∂r̂ − r̂ ⟨r̂, ∂r̂⟩/d) / ‖r‖_rms.
    const int64_t scale = fr.scale[ql];
    uwide dot_part = 0;
    for (uint32_t j = tid; j < W; j += B) {
        dot_part += (uwide)((wide)fr.read[ql * W + j] * (wide)dr[j]);
    }
    const wide dotv = (wide)block_sum(dot_part, redw);
    const wide mean = div_nearest(dotv, (wide)W);
    m = 0;
    for (uint32_t j = tid; j < W; j += B) {
        int64_t v = 0;
        if (scale != 0) {
            const wide read = fr.read[ql * W + j];
            v = fit64(div_nearest(((wide)dr[j] - rel(mean * read, 2 * FACE_BITS)) << FACE_BITS, scale), &st);
        }
        dread[j] = v;
        fr.dread[ql * W + j] = v;
        const uint64_t a = magnitude(v);
        m = a > m ? a : m;
    }
    const uint64_t dmax = block_max(m, red);
    if (tid == 0) {
        fr.r_dy[ql] = ymax;
        fr.r_da[ql] = amax;
        fr.r_dread[ql] = dmax;
    }
    // The modes' read covector: C_reᵀ ∂r and C_imᵀ (−∂r).
    const bool n_re = narrow_rows(lv.reach[2], dmax, W);
    const bool n_im = narrow_rows(lv.reach[3], dmax, W);
    for (uint32_t o = tid; o < 2 * N; o += B) {
        const uint32_t k = o % N;
        const bool im = o >= N;
        const wide sum = dot(fr.theta + (im ? lv.read_im : lv.read_re) + k, N, W, dread, im ? n_im : n_re);
        fr.readcov[ql * 2 * N + o] = fit64(rel(im ? -sum : sum, MATERIAL_BITS), &st);
    }
    __syncthreads();
    if (tid == 0 && st != 0) {
        atomicOr(fr.status + s, st);
    }
}

// The modes' reverse scan of one level of one stream, one thread a mode, and each cell's gated move
// adjoint: G_h(t) = read covector + conj(λ_(t+1)) G_h(t+1); the covectors of |λ| and arg λ summed
// over the cells; the gate's logit covector δq; and γ_t G_h, what the pushes return.
extern "C" __global__ void tower_reverse_modes(TowerLaw law, TowerFrame fr, uint32_t l) {
    const uint32_t s = blockIdx.x, B = blockDim.x;
    const uint32_t N = law.modes, L = law.levels, T = law.cells;
    const TowerLevel &lv = law.level[l];
    const wide one = (wide)1 << MOVE_BITS;
    __shared__ uint32_t st;
    if (threadIdx.x == 0) {
        st = 0;
    }
    __syncthreads();
    for (uint32_t k = threadIdx.x; k < N; k += B) {
        const int64_t *gf = fr.gates + ((uint64_t)l * N + k) * 4;
        const wide ur = gf[0], ui = gf[1], modulus = gf[2] > 0 ? gf[2] : 1, log = gf[3];
        wide cr = 0, ci = 0, along = 0, around = 0;
        for (uint32_t step = 0; step < T; step++) {
            const uint32_t t = T - 1 - step;
            const uint64_t q = (uint64_t)s * T + t, ql = q * L + l;
            wide lr, li;
            if (t + 1 < T) {
                const int64_t *later = fr.moves + (((q + 1) * L + l) * N + k) * 6;
                lr = later[3];
                li = later[4];
            } else {
                lr = fr.theta[lv.move_re + k];
                li = fr.theta[lv.move_im + k];
            }
            const int64_t gr = fit64((wide)fr.readcov[ql * 2 * N + k] + rel(lr * cr + li * ci, MOVE_BITS), &st);
            const int64_t gi = fit64((wide)fr.readcov[ql * 2 * N + N + k] + rel(lr * ci - li * cr, MOVE_BITS), &st);
            cr = gr;
            ci = gi;
            const int64_t *previous = t == 0 ? fr.opening + (((uint64_t)s * L + l) * N + k) * 2 : fr.state + (((q - 1) * L + l) * N + k) * 2;
            const wide hr = previous[0], hi = previous[1];
            const wide glr = hr * gr + hi * gi;
            const wide gli = hr * gi - hi * gr;
            const wide through = (wide)gr * fr.push[ql * 2 * N + k] + (wide)gi * fr.push[ql * 2 * N + N + k];
            const int64_t *mv = fr.moves + (ql * N + k) * 6;
            const wide open = mv[0], rho = mv[1], gamma = mv[2];
            around += rel((wide)mv[3] * gli - (wide)mv[4] * glr, MOVE_BITS);
            int64_t dq = 0;
            if (mv[5] == 0) {
                const wide g_rho = rel(ur * glr + ui * gli, MOVE_BITS) - div_nearest(rho * through, gamma);
                along += rel(g_rho * div_nearest((wide)GATE_REACH * open * rho, modulus), MOVE_BITS);
                wide f = rel(rho * log, MOVE_BITS);
                f = rel(f * (wide)law.ln2_square, MOVE_BITS);
                f = rel(f * open, MOVE_BITS);
                f = rel(f * (one - open), MOVE_BITS);
                dq = fit64(rel(g_rho * GATE_REACH * f, COVECTOR_BITS + MOVE_BITS), &st);
            }
            fr.gre[ql * N + k] = fit64(rel(gamma * gr, MOVE_BITS), &st);
            fr.gim[ql * N + k] = fit64(rel(gamma * gi, MOVE_BITS), &st);
            fr.dq[ql * N + k] = dq;
        }
        // The Cartesian covector of the founded move: G_λ = u G_|λ| + i u G_φ/|λ|.
        const wide turn = div_nearest(around << MOVE_BITS, modulus);
        wide *out = fr.moves_g + (((uint64_t)s * L + l) * N + k) * 2;
        out[0] = rel(ur * along - ui * turn, MOVE_BITS);
        out[1] = rel(ui * along + ur * turn, MOVE_BITS);
    }
    __syncthreads();
    if (threadIdx.x == 0 && st != 0) {
        atomicOr(fr.status + s, st);
    }
}

// What the pushes and the gate return to the level's input: dx += P_reᵀ γG_re + P_imᵀ γG_im + W_gᵀ δq.
extern "C" __global__ void __launch_bounds__(TOWER_THREADS) tower_reverse_dx(TowerLaw law, TowerFrame fr, uint32_t l) {
    const uint64_t q = blockIdx.x, ql = q * law.levels + l;
    const uint32_t s = (uint32_t)(q / law.cells), tid = threadIdx.x, B = blockDim.x;
    const uint32_t W = law.width, N = law.modes;
    const TowerLevel &lv = law.level[l];
    extern __shared__ __align__(16) unsigned char smem[];
    unsigned char *at = smem;
    int64_t *v = (int64_t *)carve(at, 8ull * 3 * N);
    int64_t *back = (int64_t *)carve(at, 8ull * 3 * W);
    uint64_t *red = (uint64_t *)carve(at, 8ull * 32);
    __shared__ uint32_t st;
    if (tid == 0) {
        st = 0;
    }
    uint64_t m0 = 0, m1 = 0, m2 = 0;
    for (uint32_t k = tid; k < N; k += B) {
        v[k] = fr.gre[ql * N + k];
        v[N + k] = fr.gim[ql * N + k];
        v[2 * N + k] = fr.dq[ql * N + k];
        const uint64_t a = magnitude(v[k]), b = magnitude(v[N + k]), c = magnitude(v[2 * N + k]);
        m0 = a > m0 ? a : m0;
        m1 = b > m1 ? b : m1;
        m2 = c > m2 ? c : m2;
    }
    const uint64_t r0 = block_max(m0, red);
    const uint64_t r1 = block_max(m1, red);
    const uint64_t r2 = block_max(m2, red);
    if (tid == 0) {
        fr.r_gre[ql] = r0;
        fr.r_gim[ql] = r1;
        fr.r_dq[ql] = r2;
    }
    const bool n0 = narrow_rows(lv.reach[0], r0, N);
    const bool n1 = narrow_rows(lv.reach[1], r1, N);
    const bool n2 = narrow_rows(lv.reach[6], r2, N);
    for (uint32_t o = tid; o < 3 * W; o += B) {
        const uint32_t fam = o / W, j = o % W;
        const uint64_t base = fam == 0 ? lv.push_re : fam == 1 ? lv.push_im : lv.gate;
        const wide sum = dot(fr.theta + base + j, W, N, v + fam * N, fam == 0 ? n0 : fam == 1 ? n1 : n2);
        back[o] = fit64(rel(sum, MATERIAL_BITS), &st);
    }
    __syncthreads();
    for (uint32_t j = tid; j < W; j += B) {
        const wide sum = (wide)fr.dx[q * W + j] + back[j] + back[W + j] + back[2 * W + j];
        fr.dx[q * W + j] = fit64(sum, &st);
    }
    __syncthreads();
    if (tid == 0 && st != 0) {
        atomicOr(fr.status + s, st);
    }
}

// -------------------------------------------------------------------------------------------
// the outer sums

struct TowerOuter {
    const int64_t *y;
    uint64_t y_stride;
    const void *x;
    uint64_t x_stride;
    const uint64_t *y_reach;
    const uint64_t *x_reach;
    uint64_t reach_stride;
    uint32_t rows, cols, streams, cells;
    int32_t negate;
    uint32_t bias;
    wide *out;
    wide *bias_out;
    uint32_t *status;
    // The streams are split over `groups` blocks along `grid.z`; with more than one, each group
    // writes its sum to `partial[z][row][col]` (`cols + bias` columns) and `tower_outer_reduce`
    // sums the groups.
    uint32_t groups;
    uint32_t pad;
    wide *partial;
};

#define OUTER_ROWS 16
#define OUTER_COLS 64
#define OUTER_CELLS 32

template <typename X>
__device__ void outer(const TowerOuter &f) {
    const uint32_t tid = threadIdx.x;
    const uint32_t tc = tid % OUTER_COLS, tr = (tid / OUTER_COLS) * 4;
    const uint32_t row0 = blockIdx.y * OUTER_ROWS, col0 = blockIdx.x * OUTER_COLS;
    const uint32_t c = col0 + tc;
    const X *xs = (const X *)f.x;
    __shared__ int64_t ys_t[OUTER_CELLS][OUTER_ROWS];
    __shared__ int64_t xs_t[OUTER_CELLS][OUTER_COLS];
    __shared__ uwide bounds[2][32];
    __shared__ uint32_t fast_s;
    wide acc[4] = {0, 0, 0, 0};
    const uwide cap = (uwide)1 << 127;
    const uint32_t from = (uint32_t)((uint64_t)f.streams * blockIdx.z / f.groups);
    const uint32_t to = (uint32_t)((uint64_t)f.streams * (blockIdx.z + 1) / f.groups);
    for (uint32_t s = from; s < to; s++) {
        // The stream's bounds: the host's `Σ_t max|y_t| max|x_t|` (refused at 2^126) and the
        // 64-bit admission `Σ_t max|y_t| max(max|x_t|, 1) < 2^63`, each saturated at 2^127.
        if (tid < 32) {
            uwide host = 0, wide_bound = 0;
            for (uint32_t t = tid; t < f.cells; t += 32) {
                const uint64_t qs = (uint64_t)s * f.cells + t;
                const uint64_t yr = f.y_reach[qs * f.reach_stride], xr = f.x_reach[qs * f.reach_stride];
                const uwide a = (uwide)yr * xr, b = (uwide)yr * (xr > 0 ? xr : 1);
                host = host + a >= cap || a >= cap ? cap : host + a;
                wide_bound = wide_bound + b >= cap || b >= cap ? cap : wide_bound + b;
            }
            bounds[0][tid] = host;
            bounds[1][tid] = wide_bound;
        }
        __syncthreads();
        if (tid == 0) {
            uwide host = 0, wide_bound = 0;
            for (uint32_t i = 0; i < 32; i++) {
                host = host + bounds[0][i] >= cap ? cap : host + bounds[0][i];
                wide_bound = wide_bound + bounds[1][i] >= cap ? cap : wide_bound + bounds[1][i];
            }
            if (host >= ((uwide)1 << 126)) {
                atomicOr(f.status + s, TOWER_REFUSED_CARRIER);
            }
            fast_s = wide_bound < ((uwide)1 << 63) ? 1 : 0;
        }
        __syncthreads();
        const bool fast = fast_s != 0;
        int64_t acc64[4] = {0, 0, 0, 0};
        for (uint32_t t0 = 0; t0 < f.cells; t0 += OUTER_CELLS) {
            for (uint32_t idx = tid; idx < OUTER_CELLS * OUTER_ROWS; idx += blockDim.x) {
                const uint32_t kk = idx / OUTER_ROWS, r = idx % OUTER_ROWS, row = row0 + r;
                const uint64_t qs = (uint64_t)s * f.cells + t0 + kk;
                ys_t[kk][r] = (t0 + kk < f.cells && row < f.rows) ? f.y[qs * f.y_stride + row] : 0;
            }
            for (uint32_t idx = tid; idx < OUTER_CELLS * OUTER_COLS; idx += blockDim.x) {
                const uint32_t kk = idx / OUTER_COLS, cc = idx % OUTER_COLS, col = col0 + cc;
                const uint64_t qs = (uint64_t)s * f.cells + t0 + kk;
                int64_t v = 0;
                if (t0 + kk < f.cells) {
                    if (col < f.cols) {
                        v = (int64_t)xs[qs * f.x_stride + col];
                    } else if (col == f.cols && f.bias) {
                        v = 1;
                    }
                }
                xs_t[kk][cc] = v;
            }
            __syncthreads();
            if (fast) {
                for (uint32_t kk = 0; kk < OUTER_CELLS; kk++) {
                    const int64_t xv = xs_t[kk][tc];
                    for (uint32_t i = 0; i < 4; i++) {
                        acc64[i] += ys_t[kk][tr + i] * xv;
                    }
                }
            } else {
                for (uint32_t kk = 0; kk < OUTER_CELLS; kk++) {
                    const wide xv = xs_t[kk][tc];
                    for (uint32_t i = 0; i < 4; i++) {
                        acc[i] += (wide)ys_t[kk][tr + i] * xv;
                    }
                }
            }
            __syncthreads();
        }
        if (fast) {
            for (uint32_t i = 0; i < 4; i++) {
                acc[i] += acc64[i];
            }
        }
    }
    const uint32_t width = f.cols + f.bias;
    for (uint32_t i = 0; i < 4; i++) {
        const uint32_t row = row0 + tr + i;
        if (row >= f.rows || c >= width) {
            continue;
        }
        const wide v = f.negate ? -acc[i] : acc[i];
        if (f.groups > 1) {
            f.partial[((uint64_t)blockIdx.z * f.rows + row) * width + c] = v;
        } else if (c < f.cols) {
            f.out[(uint64_t)row * f.cols + c] = v;
        } else {
            f.bias_out[row] = v;
        }
    }
}

extern "C" __global__ void __launch_bounds__(TOWER_THREADS) tower_outer_x32(TowerOuter f) {
    outer<int32_t>(f);
}

extern "C" __global__ void __launch_bounds__(TOWER_THREADS) tower_outer_x64(TowerOuter f) {
    outer<int64_t>(f);
}

// The groups' sums of one family summed into its covector (integer addition: any order).
extern "C" __global__ void tower_outer_reduce(TowerOuter f) {
    const uint32_t width = f.cols + f.bias;
    const uint64_t outputs = (uint64_t)f.rows * width;
    for (uint64_t e = (uint64_t)blockIdx.x * blockDim.x + threadIdx.x; e < outputs; e += (uint64_t)gridDim.x * blockDim.x) {
        wide sum = 0;
        for (uint32_t z = 0; z < f.groups; z++) {
            sum += f.partial[(uint64_t)z * outputs + e];
        }
        const uint64_t row = e / width, c = e % width;
        if (c < f.cols) {
            f.out[row * f.cols + c] = sum;
        } else {
            f.bias_out[row] = sum;
        }
    }
}

// The encoding's covector: each cell's bottom covector summed at the class that arrived there.
extern "C" __global__ void tower_encoding(TowerLaw law, TowerFrame fr) {
    const uint32_t u = blockIdx.x, W = law.width, T = law.cells;
    const uint64_t cells = (uint64_t)law.streams * T;
    for (uint32_t j = threadIdx.x; j < W; j += blockDim.x) {
        wide acc = 0;
        for (uint64_t q = 0; q < cells; q++) {
            const uint64_t s = q / T, t = q % T;
            if (fr.classes[s * (T + 1) + t] == u) {
                acc += fr.dx[q * W + j];
            }
        }
        fr.gradient[law.encoding + (uint64_t)u * W + j] = acc;
    }
}

// The moves' covectors summed over the streams.
extern "C" __global__ void tower_moves(TowerLaw law, TowerFrame fr) {
    const uint32_t l = blockIdx.x, N = law.modes, L = law.levels;
    const TowerLevel &lv = law.level[l];
    for (uint32_t k = threadIdx.x; k < N; k += blockDim.x) {
        wide re = 0, im = 0;
        for (uint32_t s = 0; s < law.streams; s++) {
            const wide *g = fr.moves_g + (((uint64_t)s * L + l) * N + k) * 2;
            re += g[0];
            im += g[1];
        }
        fr.gradient[lv.move_re + k] = re;
        fr.gradient[lv.move_im + k] = im;
    }
}

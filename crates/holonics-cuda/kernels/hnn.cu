// **The resident HNN's kernels** (rebuild step 5, #76; owners `src/hnn/{lattice,moment,word}.rs`).
//
// Each entry realizes one law of `holonics::hnn` on the card with exact integers and no float; the
// only rounding is the word's nearest-point split (Decision 24), whose remainder is carried or
// bounded, never dropped unreported. Each entry's parity test against an exact host oracle is in
// `src/hnn/tests.rs`. The launch of each is derived from the card's census by its owner
// (`src/hnn/card.rs`), which also reports the realization.

#include "exact_integer.cuh"

// Each launch's dynamic shared surface, sized by its layout (`src/hnn/card.rs`).
extern __shared__ __align__(16) unsigned char hnn_shared[];

// -------------------------------------------------------------------------------------------------
// the lattice read
// -------------------------------------------------------------------------------------------------
//
// [definition] A locus of the constitution carried on its lattice (`holonics::hnn::Lattice`,
// Decision 22) is `A = a · 2^(−L_A)` with integer coordinates `a`; a vector on its own lattice is
// `x = ξ · 2^(−L_x)` (the moment's counts have `L_x = 0`). The read is
//
//   y_b = A x_b = (Σ_j a_ij ξ_b,γ_b(j)) · 2^(−(L_A + L_x))
//
// with `γ_b` an optional gather of the vector's coordinates (a ring's rotation `P_R^(τ_R)` is a
// permutation of the realified coordinates, so `R P x` is read as `R` against the gathered `x`).
// The sum is taken in the ring Z/2^128 and read under its l1 certificate (`exact_integer.cuh`):
// every entry is exact or refused, never rounded.
//
// Realization: block `(i, b)` is the output entry of row `i` and vector `b`; its `blockDim.x`
// threads divide the row's columns (thread `t` takes `j ≡ t mod blockDim.x`), and the block
// reduces the ring words and their certificates by a shared-memory tree. No thread loops over
// rows. `blockDim.x` is a power of two.
//
// Shared: 2 · blockDim.x words of 16 octets (the ring words, then the certificates).
extern "C" __global__ void hnn_lattice_read(
    const int64_t *a, uint32_t rows, uint32_t columns,
    const int64_t *x, uint32_t vectors, uint32_t width,
    const uint32_t *gather,
    wide *y, uint32_t *status
) {
    uwide *ring = (uwide *)hnn_shared;
    uwide *bound = ring + blockDim.x;
    __shared__ uint32_t malformed;
    const uint32_t row = blockIdx.x, vector = blockIdx.y, t = threadIdx.x;
    if (row >= rows || vector >= vectors) {
        return;  // uniform over the block
    }
    if (t == 0) {
        malformed = 0;
    }
    __syncthreads();
    const int64_t *coordinates = a + (size_t)row * columns;
    const int64_t *operand = x + (size_t)vector * width;
    const uint32_t *order = gather ? gather + (size_t)vector * columns : nullptr;
    uwide word = 0, certificate = 0;
    for (uint32_t j = t; j < columns; j += blockDim.x) {
        const uint32_t k = order ? order[j] : j;
        if (k >= width) {
            atomicOr(&malformed, 1u);
            continue;
        }
        const wide product = hnn_word_product(coordinates[j], operand[k]);
        word += (uwide)product;
        certificate = hnn_certify(certificate, hnn_magnitude(product));
    }
    ring[t] = word;
    bound[t] = certificate;
    __syncthreads();
    hnn_block_sum(ring, bound, t);
    if (t == 0) {
        uint32_t read = malformed ? HNN_REFUSED_MALFORMED : HNN_EXACT;
        const wide value = hnn_certified(ring[0], bound[0], &read);
        const size_t at = (size_t)vector * rows + row;
        y[at] = read == HNN_EXACT ? value : (wide)0;
        status[at] = read;
    }
}

// -------------------------------------------------------------------------------------------------
// the moment ingest
// -------------------------------------------------------------------------------------------------
//
// [definition] `holonics::hnn::SourceMoment::ingest` with `Field::selective_step`: on each cell
// `x_k`, in carry order, ring `g` advances `c_g(x_k) = [port_g(x_k) ∈ N_g]` plus its
// predecessor's carry, and carries when its phase before the step plus the advance reaches its
// period; then on every source ring, at its phase `c` after the step, `M_g[c][x_k] += 1` and, for
// each declared offset `δ` whose earlier cell exists, `C_g(δ)[c][x_k][x_(k−δ)] += 1`; the window
// keeps the last `max Δ` cells. Ingest stops after the cell whose step carries the last ring out
// (the joint clock's carry-out) and reports it.
//
// The lock chart `fits[g][code] = [port_g(code) ∈ N_g]` is the field's, read off the host owner at
// the moment's open (`Ring::fits`, `Ring::port`); the kernel reads it and states no port law.
//
// Realization: one block carries the cell sequence. Thread `t` is cell `start + t` of each tile of
// `blockDim.x` cells; the block loops over the tiles in order, carrying each ring's phase from
// tile to tile. Within a tile, each ring's advances are one inclusive block scan, rings in carry
// order (a ring's advance reads its predecessor's carry at the same cell). The carry-out's first
// lane is an atomic minimum. The counts are atomic additions into the resident moment: integer
// addition commutes, and the moment's cell count certifies that no count leaves its 64-bit word.
//
// Window: `window[0]` is the number of valid cells, `window[1 …]` the cells, oldest first.
// Receipt: `[consumed, carried out, advance_0, …, advance_(G−1)]`.
//
// Shared: `rings` 8-octet advance totals, `rings` 4-octet phases, `rings · blockDim.x` 4-octet
// scans.
extern "C" __global__ void hnn_moment_ingest(
    const uint32_t *codes, uint32_t cells,
    uint32_t rings, const uint32_t *periods, const uint8_t *fits, uint32_t alphabet,
    uint32_t sources, const uint32_t *source_rings,
    uint32_t offsets, const uint32_t *offset_values,
    uint32_t *window, uint32_t window_extent,
    uint32_t *phases,
    unsigned long long *first, const unsigned long long *first_base,
    unsigned long long *paired, const unsigned long long *paired_base,
    unsigned long long *receipt
) {
    unsigned long long *advance = (unsigned long long *)hnn_shared;
    uint32_t *base = (uint32_t *)(advance + rings);
    uint32_t *inclusive = base + rings;
    __shared__ uint32_t stop;
    __shared__ uint32_t valid;
    const uint32_t t = threadIdx.x, lanes = blockDim.x;
    for (uint32_t g = t; g < rings; g += lanes) {
        advance[g] = 0;
        base[g] = phases[g];
    }
    if (t == 0) {
        valid = window[0];
    }
    __syncthreads();
    uint32_t consumed = 0;
    bool carried = false;
    for (uint32_t start = 0; start < cells && !carried; start += lanes) {
        const uint32_t k = start + t;
        const bool active = k < cells;
        const uint32_t code = active ? codes[k] : 0;
        if (t == 0) {
            stop = lanes;
        }
        uint32_t carry = 0;
        for (uint32_t g = 0; g < rings; ++g) {
            const uint32_t period = periods[g];
            const uint32_t step =
                active ? (uint32_t)fits[(size_t)g * alphabet + code] + carry : 0u;
            uint32_t *scan = inclusive + (size_t)g * lanes;
            scan[t] = step;
            __syncthreads();
            for (uint32_t reach = 1; reach < lanes; reach <<= 1) {
                const uint32_t earlier = t >= reach ? scan[t - reach] : 0u;
                __syncthreads();
                scan[t] += earlier;
                __syncthreads();
            }
            const uint32_t before = (base[g] + scan[t] - step) % period;
            carry = (active && before + step >= period) ? 1u : 0u;
        }
        if (carry) {
            atomicMin(&stop, t);
        }
        __syncthreads();
        const uint32_t tile = cells - start < lanes ? cells - start : lanes;
        const uint32_t last = stop < lanes ? stop : tile - 1;
        if (active && t <= last) {
            for (uint32_t s = 0; s < sources; ++s) {
                const uint32_t g = source_rings[s];
                const uint32_t phase = (base[g] + inclusive[(size_t)g * lanes + t]) % periods[g];
                const size_t cell = (size_t)phase * alphabet + code;
                atomicAdd(first + first_base[s] + cell, 1ull);
                for (uint32_t o = 0; o < offsets; ++o) {
                    const uint32_t offset = offset_values[o];
                    uint32_t earlier = 0;
                    bool present = false;
                    if (k >= offset) {
                        earlier = codes[k - offset];
                        present = true;
                    } else if (offset - k <= valid) {
                        earlier = window[1 + valid - (offset - k)];
                        present = true;
                    }
                    if (present) {
                        atomicAdd(
                            paired + paired_base[(size_t)s * offsets + o] + cell * alphabet + earlier,
                            1ull
                        );
                    }
                }
            }
        }
        __syncthreads();
        if (t == 0) {
            for (uint32_t g = 0; g < rings; ++g) {
                const uint32_t moved = inclusive[(size_t)g * lanes + last];
                advance[g] += moved;
                base[g] = (base[g] + moved) % periods[g];
            }
        }
        consumed = start + last + 1;
        carried = stop < lanes;
        __syncthreads();
    }
    if (t == 0) {
        // The window's overwrite: the last cells of (window ++ consumed cells), copied forward in
        // place (each read lies at or after the position it fills).
        const uint32_t total = valid + consumed;
        const uint32_t keep = total < window_extent ? total : window_extent;
        for (uint32_t i = 0; i < keep; ++i) {
            const uint32_t at = total - keep + i;
            window[1 + i] = at < valid ? window[1 + at] : codes[at - valid];
        }
        window[0] = keep;
        for (uint32_t g = 0; g < rings; ++g) {
            phases[g] = base[g];
            receipt[2 + g] = advance[g];
        }
        receipt[0] = consumed;
        receipt[1] = carried ? 1ull : 0ull;
    }
}

// -------------------------------------------------------------------------------------------------
// the word: the carried tick and its adjoint
// -------------------------------------------------------------------------------------------------
//
// [definition] Decision 24, Lean `HNN/LatticeWord.{feedback_tick, feedback_accounting,
// executed_adjoint_pairing}`. A region `g` of a word (a ring or a contact) carries a chart
// `Q_g = q · 2^(−L_c)` (`n × n` signed 64-bit words), a state `x_g = ξ · 2^(−L_w)` (`n` words) and a
// remainder `r_g` (`n` words on the fine lattice `2^(−(L_c + L_w))ℤ`). One tick is
//
//   s_i = Σ_j q_ij ξ_j + r_i           exact; its certificate is Σ_j |q_ij ξ_j| + |r_i|
//   s_i = ξ'_i · 2^(L_c) + r'_i        the nearest-point split, ties upward
//
// so `ξ'_i 2^(L_c) + r'_i = (qξ)_i + r_i` exactly and `−2^(L_c−1) ≤ r'_i < 2^(L_c−1)`; `L_c ≤ 64`
// keeps the remainder a word. The adjoint tick splits `Σ_j q_ji λ_j + ρ_i`: the transpose of the
// executed chart, the only covector that pairs exactly with it. `L_w` never enters the integers.
//
// Refusals, per entry, in this order: an entry whose region's state has a refused coordinate
// (operand); a certificate reaching 2^127 (carrier); a `ξ'_i` outside the signed 64-bit word
// (word). A refused entry's state and remainder are zero.
//
// Realization: block `e` is one output entry, row `i` of region `g = row_region[e]` with
// `e = state_base[g] + i`; its `blockDim.x` threads divide the row (thread `t` takes `j ≡ t`), the
// block reduces the ring words and certificates by the shared tree, and thread 0 adds the
// remainder and splits. Every block reads the immutable charts and the state it is handed and
// writes only its own entry of the next state, its status and its own remainder, so the blocks
// commute; the state alternates between two buffers from tick to tick, the remainder stays in
// place.
//
// Region tables: `widths[g]`, `chart_base[g]` (offset of `q_g`, row-major), `state_base[g]`,
// `shifts[g] = L_c`. Shared: 2 · blockDim.x words of 16 octets.
template <bool TRANSPOSED>
__device__ __forceinline__ void hnn_word_tick_entry(
    const int64_t *charts, const uint32_t *widths, const unsigned long long *chart_base,
    const unsigned long long *state_base, const uint32_t *shifts,
    const uint32_t *row_region, uint32_t entries,
    const int64_t *state, const uint32_t *state_status,
    int64_t *next, uint32_t *next_status, int64_t *remainder
) {
    uwide *ring = (uwide *)hnn_shared;
    uwide *bound = ring + blockDim.x;
    __shared__ uint32_t inherited;
    const uint32_t e = blockIdx.x, t = threadIdx.x;
    if (e >= entries) {
        return;  // uniform over the block
    }
    if (t == 0) {
        inherited = 0;
    }
    __syncthreads();
    const uint32_t g = row_region[e];
    const uint32_t n = widths[g];
    const unsigned long long base = state_base[g];
    const uint32_t i = (uint32_t)(e - base);
    const int64_t *q = charts + chart_base[g];
    uwide word = 0, certificate = 0;
    uint32_t refused = 0;
    for (uint32_t j = t; j < n; j += blockDim.x) {
        const int64_t coefficient = TRANSPOSED ? q[(size_t)j * n + i] : q[(size_t)i * n + j];
        refused |= state_status[base + j];
        const wide product = hnn_word_product(coefficient, state[base + j]);
        word += (uwide)product;
        certificate = hnn_certify(certificate, hnn_magnitude(product));
    }
    if (refused) {
        atomicOr(&inherited, 1u);
    }
    ring[t] = word;
    bound[t] = certificate;
    __syncthreads();
    hnn_block_sum(ring, bound, t);
    if (t == 0) {
        const int64_t carried = remainder[e];
        uint32_t read = inherited ? HNN_REFUSED_OPERAND : HNN_EXACT;
        int64_t x = 0, r = 0;
        if (read == HNN_EXACT) {
            const wide s = hnn_certified(
                ring[0] + (uwide)(wide)carried,
                hnn_certify(bound[0], hnn_magnitude((wide)carried)),
                &read
            );
            if (read == HNN_EXACT) {
                wide split;
                const wide quotient = hnn_nearest(s, shifts[g], &split);
                if (hnn_is_word(quotient)) {
                    x = (int64_t)quotient;
                    r = (int64_t)split;
                } else {
                    read = HNN_REFUSED_WORD;
                }
            }
        }
        next[e] = x;
        next_status[e] = read;
        remainder[e] = r;
    }
}

extern "C" __global__ void hnn_word_tick(
    const int64_t *charts, const uint32_t *widths, const unsigned long long *chart_base,
    const unsigned long long *state_base, const uint32_t *shifts,
    const uint32_t *row_region, uint32_t entries,
    const int64_t *state, const uint32_t *state_status,
    int64_t *next, uint32_t *next_status, int64_t *remainder
) {
    hnn_word_tick_entry<false>(
        charts, widths, chart_base, state_base, shifts, row_region, entries,
        state, state_status, next, next_status, remainder
    );
}

extern "C" __global__ void hnn_word_adjoint_tick(
    const int64_t *charts, const uint32_t *widths, const unsigned long long *chart_base,
    const unsigned long long *state_base, const uint32_t *shifts,
    const uint32_t *row_region, uint32_t entries,
    const int64_t *state, const uint32_t *state_status,
    int64_t *next, uint32_t *next_status, int64_t *remainder
) {
    hnn_word_tick_entry<true>(
        charts, widths, chart_base, state_base, shifts, row_region, entries,
        state, state_status, next, next_status, remainder
    );
}

// -------------------------------------------------------------------------------------------------
// the inverse charts: the Newton–Schulz refinement and the certificate
// -------------------------------------------------------------------------------------------------
//
// [definition] Decision 24, Lean `HNN/LatticeWord.{nsStep, newton_schulz_right,
// rounded_refinement_certificate}`. A pair `g` carries an operator `A = a · 2^(−L_A)` and its
// inverse chart `X̂ = ξ · 2^(−L_c)` (`n × n` signed 64-bit words each), with `S = L_A + L_c ≤ 126`
// so that `2^S` is a carrier word. The residual `R = 1 − A X̂` on `2^(−S)ℤ` is
//
//   ρ_ij = 2^S δ_ij − Σ_k a_ik ξ_kj ,    certificate 2^S δ_ij + Σ_k |a_ik ξ_kj|
//
// The refinement `X̂(2 − A X̂) = X̂ + X̂R` on `2^(−(S + L_c))ℤ` is `2^S ξ + ξρ`, and its split at
// `2^S` onto `2^(−L_c)ℤ` (ties upward; the split commutes with adding the lattice point `2^S ξ`) is
//
//   Σ_k ξ_ik ρ_kj = q_ij 2^S + e_ij ,    ξ''_ij = ξ_ij + q_ij ,    −2^(S−1) ≤ e_ij < 2^(S−1)
//
// with `e` discarded: the rounding term `|Δ_ij| ≤ 2^(−L_c)/2` of `rounded_refinement_certificate`.
// Each term `ξ_ik ρ_kj` is a word times a carrier word, certified by `hnn_bounded_product`. The
// certificate of a chart is the exact rational `‖1 − A X̂‖∞ = max_i Σ_j |ρ_ij| / 2^S`.
//
// Refusals, per entry, in this order: an entry reading a refused chart or residual coordinate
// (operand); a certificate reaching 2^127 (carrier); a `ξ''_ij` outside the signed 64-bit word
// (word).
//
// Realization (residual and refinement): block `(e, j)` is one output entry, flattened row `e`
// (row `i = e − row_base[g]` of pair `g = row_region[e]`) and column `j`; a block with `j ≥ n_g`
// returns at once. Its threads divide the contraction index (`k ≡ t`) and reduce by the shared
// tree. Every block reads the immutable operator, chart and residual and writes only its own
// entry (the refinement writes the other of two chart buffers), so the blocks commute.
//
// Pair tables: `widths[g]`, `chart_base[g]` (offset of the `n × n` block, one for `a`, `ξ` and `ρ`),
// `row_base[g]`, `shifts[g] = S`. Shared: 2 · blockDim.x words of 16 octets.
extern "C" __global__ void hnn_inverse_residual(
    const int64_t *operators, const int64_t *charts, const uint32_t *chart_status,
    const uint32_t *widths, const unsigned long long *chart_base,
    const unsigned long long *row_base, const uint32_t *shifts,
    const uint32_t *row_region, uint32_t rows,
    wide *residual, uint32_t *residual_status
) {
    uwide *ring = (uwide *)hnn_shared;
    uwide *bound = ring + blockDim.x;
    __shared__ uint32_t inherited;
    const uint32_t e = blockIdx.x, j = blockIdx.y, t = threadIdx.x;
    if (e >= rows) {
        return;  // uniform over the block
    }
    const uint32_t g = row_region[e];
    const uint32_t n = widths[g];
    if (j >= n) {
        return;  // uniform over the block
    }
    if (t == 0) {
        inherited = 0;
    }
    __syncthreads();
    const uint32_t i = (uint32_t)(e - row_base[g]);
    const unsigned long long at = chart_base[g];
    const int64_t *a = operators + at;
    const int64_t *x = charts + at;
    const uint32_t *x_status = chart_status + at;
    uwide word = 0, certificate = 0;
    uint32_t refused = 0;
    for (uint32_t k = t; k < n; k += blockDim.x) {
        refused |= x_status[(size_t)k * n + j];
        const wide product = hnn_word_product(a[(size_t)i * n + k], x[(size_t)k * n + j]);
        word += (uwide)product;
        certificate = hnn_certify(certificate, hnn_magnitude(product));
    }
    if (refused) {
        atomicOr(&inherited, 1u);
    }
    ring[t] = word;
    bound[t] = certificate;
    __syncthreads();
    hnn_block_sum(ring, bound, t);
    if (t == 0) {
        const uwide diagonal = i == j ? (uwide)1 << shifts[g] : (uwide)0;
        uint32_t read = inherited ? HNN_REFUSED_OPERAND : HNN_EXACT;
        wide value = 0;
        if (read == HNN_EXACT) {
            value = hnn_certified(diagonal - ring[0], hnn_certify(bound[0], diagonal), &read);
        }
        const size_t out = at + (size_t)i * n + j;
        residual[out] = read == HNN_EXACT ? value : (wide)0;
        residual_status[out] = read;
    }
}

extern "C" __global__ void hnn_inverse_refine(
    const int64_t *charts, const uint32_t *chart_status,
    const wide *residual, const uint32_t *residual_status,
    const uint32_t *widths, const unsigned long long *chart_base,
    const unsigned long long *row_base, const uint32_t *shifts,
    const uint32_t *row_region, uint32_t rows,
    int64_t *next, uint32_t *next_status
) {
    uwide *ring = (uwide *)hnn_shared;
    uwide *bound = ring + blockDim.x;
    __shared__ uint32_t inherited;
    const uint32_t e = blockIdx.x, j = blockIdx.y, t = threadIdx.x;
    if (e >= rows) {
        return;  // uniform over the block
    }
    const uint32_t g = row_region[e];
    const uint32_t n = widths[g];
    if (j >= n) {
        return;  // uniform over the block
    }
    if (t == 0) {
        inherited = 0;
    }
    __syncthreads();
    const uint32_t i = (uint32_t)(e - row_base[g]);
    const unsigned long long at = chart_base[g];
    const int64_t *x = charts + at;
    const uint32_t *x_status = chart_status + at;
    const wide *rho = residual + at;
    const uint32_t *rho_status = residual_status + at;
    uwide word = 0, certificate = 0;
    uint32_t refused = 0;
    for (uint32_t k = t; k < n; k += blockDim.x) {
        refused |= x_status[(size_t)i * n + k] | rho_status[(size_t)k * n + j];
        uwide magnitude;
        const wide product =
            hnn_bounded_product(x[(size_t)i * n + k], rho[(size_t)k * n + j], &magnitude);
        word += (uwide)product;
        certificate = hnn_certify(certificate, magnitude);
    }
    if (refused) {
        atomicOr(&inherited, 1u);
    }
    ring[t] = word;
    bound[t] = certificate;
    __syncthreads();
    hnn_block_sum(ring, bound, t);
    if (t == 0) {
        uint32_t read = inherited ? HNN_REFUSED_OPERAND : HNN_EXACT;
        int64_t refined = 0;
        if (read == HNN_EXACT) {
            const wide s = hnn_certified(ring[0], bound[0], &read);
            if (read == HNN_EXACT) {
                wide discarded;
                const wide q = hnn_nearest(s, shifts[g], &discarded);
                // |q| < 2^64 keeps ξ + q below 2^65 in magnitude, with no wrap; |q| ≥ 2^64 already
                // puts ξ + q outside the word.
                const bool near = hnn_magnitude(q) < ((uwide)1 << 64);
                const wide moved = near ? (wide)x[(size_t)i * n + j] + q : (wide)0;
                if (near && hnn_is_word(moved)) {
                    refined = (int64_t)moved;
                } else {
                    read = HNN_REFUSED_WORD;
                }
            }
        }
        const size_t out = at + (size_t)i * n + j;
        next[out] = refined;
        next_status[out] = read;
    }
}

// Realization (certificate): block `g` is one chart; thread `t` takes the rows `i ≡ t`, each summing
// `|ρ_ij|` over the row's `n` columns with the saturated addition, and the block keeps the largest
// row sum by a shared tree of maxima (associative and commutative). A sum reaching 2^127 is refused
// (carrier); a refused residual entry refuses its chart (operand). The reading is `2 · charts`
// words: the numerators, then the status words, so the host reads it in one transfer. Shared:
// blockDim.x words of 16 octets.
extern "C" __global__ void hnn_inverse_certificate(
    const wide *residual, const uint32_t *residual_status,
    const uint32_t *widths, const unsigned long long *chart_base, uint32_t charts,
    uwide *reading
) {
    uwide *largest = (uwide *)hnn_shared;
    __shared__ uint32_t inherited;
    const uint32_t g = blockIdx.x, t = threadIdx.x;
    if (g >= charts) {
        return;  // uniform over the block
    }
    if (t == 0) {
        inherited = 0;
    }
    __syncthreads();
    const uint32_t n = widths[g];
    const unsigned long long at = chart_base[g];
    uwide best = 0;
    uint32_t refused = 0;
    for (uint32_t i = t; i < n; i += blockDim.x) {
        uwide row = 0;
        for (uint32_t j = 0; j < n; ++j) {
            const size_t entry = at + (size_t)i * n + j;
            refused |= residual_status[entry];
            row = hnn_certify(row, hnn_magnitude(residual[entry]));
        }
        best = row > best ? row : best;
    }
    if (refused) {
        atomicOr(&inherited, 1u);
    }
    largest[t] = best;
    __syncthreads();
    for (uint32_t stride = blockDim.x >> 1; stride > 0; stride >>= 1) {
        if (t < stride && largest[t + stride] > largest[t]) {
            largest[t] = largest[t + stride];
        }
        __syncthreads();
    }
    if (t == 0) {
        const uint32_t read = inherited
            ? HNN_REFUSED_OPERAND
            : (largest[0] >= HNN_CARRIER_BOUND ? HNN_REFUSED_CARRIER : HNN_EXACT);
        reading[g] = read == HNN_EXACT ? largest[0] : (uwide)0;
        reading[charts + g] = (uwide)read;
    }
}

// **The resident HNN's kernels** (rebuild step 5, #76; owners `src/hnn/{lattice,moment}.rs`).
//
// Each entry realizes one law of `holonics::hnn` on the card, with no float and no rounding, and
// its host-parity test is in `src/hnn/tests.rs`. The launch of each is derived from the card's
// census by its owner (`src/hnn/card.rs`), which also reports the realization.

#include "exact_integer.cuh"

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
    extern __shared__ __align__(16) unsigned char hnn_shared[];
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
    for (uint32_t stride = blockDim.x >> 1; stride > 0; stride >>= 1) {
        if (t < stride) {
            ring[t] += ring[t + stride];
            bound[t] = hnn_certify(bound[t], bound[t + stride]);
        }
        __syncthreads();
    }
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
    extern __shared__ __align__(16) unsigned char hnn_shared[];
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

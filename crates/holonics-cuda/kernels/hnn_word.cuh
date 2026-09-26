// **The executed word on the card: its open, its ticks, its receiving read and its return**
// (rebuild step 5, #76; Decision 24; owner `src/hnn/execute.rs`, port `src/hnn/port.rs`).
//
// [definition] The host law is `holonics::hnn::{word, propagation, receiving, port}`: a word opens
// at zero change with `s_g(0) = P_g^(τ_g) Σ_c P_g^(−c)(E_g M_g[c] + Σ_δ E_g^(δ) C_g(δ)[c])` on the
// source rings, runs `e_max − 1` full ticks (junction Swing, ring element, contact transit) and a
// last junction, every transient carried on `2^(−L_w)ℤ` with error feedback (the nearest-point
// split, ties upward, `hnn_nearest`), every inverse applied as its certified lattice chart, and is
// read at the receiving epochs as `f_j = R · P_R^(τ_R) v_R(e_j)`. Its return runs the ticks in
// reverse through the transposes of the executed maps, its own transients carried the same way.
// These kernels execute exactly that law in integers: every value `x` is an integer `X` on a
// declared scale, `x = X · 2^(−σ)`, and every scale is fixed by the host before the launch (the
// plan). The only rounding is the split, whose remainder is carried in the word and released at its
// end; nothing else is rounded, and every sum is read under its l1 certificate (`exact_integer.cuh`)
// or refused.
//
// [definition] **The scales** (σ; `L_c` the charts', `L_w` the transients'):
//
// ```text
// storage, arrivals, anchors, u, w, ζ      L_w                          (i64 words)
// junction image  ŵ_s s + Σ ŵ_a a           L_c + L_w                    split at L_c
// element operand 2b + W_c c                σ_Wc + L_w                   b = 2v − s, c = v − s
// element image   X̂·operand − b             L_c + σ_Wc + L_w             split onto L_w at ρ_s
// element midpoint x̄ = ½(b + image)         L_c + σ_Wc + L_w + 1
// transit right   h(α_g − α_h) + 2Cw − hKu  σ_R = L_w + max(H, σ_C, σ_K + H)
// transit image   m̂·right                   L_c + σ_R                    split onto L_w
// ω = (G/2h) ζ                              L_w + e_g
// w′ = 2ω − w                               L_w + e_g                    split
// u′ = u + hω                               L_w + e_g + H                split
// a′ = o ∓ ζ/h on the channel               L_w + X                      split
// ```
//
// with `h = 2^η`, `H = max(0, −η)` (and `h = H_mul·2^(−H)`), `X = max(0, η)` (and
// `1/h = X_mul·2^(−X)`). The storage remainder carries at `ρ_s = max(σ_open, L_c + σ_Wc + L_w)`,
// the opening's own scale `σ_open` included, so the opening split and every element split carry
// one remainder.
//
// [definition] **Realization** (the hardware law): one block carries a whole word, its threads
// dividing the rows of each stage (`row ≡ t mod blockDim.x`): the junctions over every ring's rows
// together, then the elements' operands with the transits' right sides, then the elements' images
// with the transits' solves, then the arrivals, each stage closed by a barrier. Within a stage every
// row reads operands no row of the stage writes, and writes only its own entries (a row's in-place
// update reads only its own entry first), so the rows commute. The word's transients never leave the
// card between its ticks; one launch runs the open, every tick and the receiving read, and the host
// reads the record once.

// -------------------------------------------------------------------------------------------------
// the plan's layout (mirrored by `src/hnn/execute.rs`)
// -------------------------------------------------------------------------------------------------

#define WP_RINGS 0
#define WP_CONTACTS 1
#define WP_STEPS 2
#define WP_LC 3
#define WP_LW 4
#define WP_RING_ROWS 5
#define WP_ARRIVALS 6
#define WP_CONTACT_ROWS 7
#define WP_H_MUL 8
#define WP_H_SHIFT 9
#define WP_X_MUL 10
#define WP_X_SHIFT 11
#define WP_RING_TABLE 12
#define WP_CONTACT_TABLE 13
#define WP_INCIDENCE 14
#define WP_ROW_RING 15
#define WP_ROW_CONTACT 16
#define WP_ARRIVAL_TABLE 17
#define WP_RECEIVER 18
#define WP_EPOCH 19
#define WP_APERTURE 20
#define WP_MAP_ROWS 21
#define WP_GATHER 22
#define WP_SOURCES 23
#define WP_SOURCE_TABLE 24
#define WP_ALPHABET 25
#define WP_PAIR_TABLE 26
#define WP_INCIDENCES 27
#define WP_MAP 28

#define WR_STRIDE 12
#define WR_WIDTH 0
#define WR_ROWS 1
#define WR_CHART 2
#define WR_WC 3
#define WR_WC_EXP 4
#define WR_STORAGE_EXP 5
#define WR_DEGREE 6
#define WR_INCIDENCE 7
#define WR_WEIGHTS 8
#define WR_ANCHOR_EXP 9

#define WI_STRIDE 3
#define WI_CONTACT 0
#define WI_SLOT 1
#define WI_ARRIVAL 2

#define WC_STRIDE 20
#define WC_WIDTH 0
#define WC_FROM 1
#define WC_TO 2
#define WC_ROWS 3
#define WC_ARRIVAL_FROM 4
#define WC_ARRIVAL_TO 5
#define WC_SELECTION 6
#define WC_CHART 7
#define WC_C 8
#define WC_C_EXP 9
#define WC_K 10
#define WC_K_EXP 11
#define WC_GAIN 12
#define WC_GAIN_EXP 13
#define WC_RIGHT_EXP 14
#define WC_RATE_GAIN 15
#define WC_RATE_GAIN_EXP 16
#define WC_SHIFT_GAIN 17
#define WC_SHIFT_GAIN_EXP 18
#define WC_ZETA_EXP 19

#define WA_STRIDE 5
#define WA_CONTACT 0
#define WA_END 1
#define WA_RING 2
#define WA_COORD 3
#define WA_CHANNEL 4

#define WS_STRIDE 10
#define WS_RING 0
#define WS_PHASES 1
#define WS_E 2
#define WS_COUNTS 3
#define WS_GATHER 4
#define WS_OPEN_EXP 5
#define WS_E_SHIFT 6
#define WS_PAIRS 7
#define WS_PAIR_BASE 8
#define WS_NU 9

#define WQ_STRIDE 8
#define WQ_RANK 0
#define WQ_OUTPUTS 1
#define WQ_CURRENT 2
#define WQ_EARLIER 3
#define WQ_COUNTS 4
#define WQ_WEIGHTS 5
#define WQ_SHIFT 6
#define WQ_PHASES 7

// The word's buffer: octet offsets of its arrays (`src/hnn/execute.rs`, `WordLayout`).
#define WL_STORAGE 0
#define WL_ARRIVALS 1
#define WL_U 2
#define WL_W 3
#define WL_REM_ANCHOR 4
#define WL_REM_STORAGE 5
#define WL_REM_SOLVE 6
#define WL_REM_ARRIVAL 7
#define WL_REM_DISP 8
#define WL_REM_RATE 9
#define WL_ANCHOR 10
#define WL_OPERAND 11
#define WL_RIGHT 12
#define WL_ZETA 13
#define WL_REC_STORAGE 14
#define WL_REC_ARRIVALS 15
#define WL_REC_U 16
#define WL_REC_W 17
#define WL_REC_ANCHOR 18
#define WL_REC_MID 19
#define WL_REC_RIGHT 20
#define WL_REC_ZETA 21
#define WL_REC_OMEGA 22
#define WL_LOGITS 23
#define WL_STATUS 24
#define WL_BAR_STORAGE 25
#define WL_BAR_ARRIVAL 26
#define WL_BAR_DISP 27
#define WL_BAR_RATE 28
#define WL_REV_EL 29
#define WL_REV_ZETA 30
#define WL_REV_SOLVED 31
#define WL_REV_RATE 32
#define WL_REV_DISP 33
#define WL_REV_STORAGE 34
#define WL_REV_ARRIVAL 35
#define WL_ADJ_U 36
#define WL_WAVE 37
#define WL_CONTRAST 38
#define WL_OUTGOING 39
#define WL_EXCHANGE 40
#define WL_ZETA_BAR 41
#define WL_SOLVED 42
#define WL_ANCHOR_BAR 43
#define WL_REC_ADJ_U 44
#define WL_REC_SOLVED 45
#define WL_DOTS1 46
#define WL_DOTS2 47
#define WL_DOTS3 48
#define WL_READS 49
#define WL_REV_STATUS 50

// The status block: the refusal bits, the first refused stage, and the row it refused.
#define WSTATUS_BITS 0
#define WSTATUS_STAGE 1
#define WSTATUS_ROW 2

// -------------------------------------------------------------------------------------------------
// the certified accumulator and the scale moves
// -------------------------------------------------------------------------------------------------

// A sum in the ring with its l1 certificate (`exact_integer.cuh`): read only below 2^127.
struct HnnSum {
    uwide ring;
    uwide bound;
};

__device__ __forceinline__ HnnSum hnn_sum() {
    HnnSum s;
    s.ring = 0;
    s.bound = 0;
    return s;
}

__device__ __forceinline__ void hnn_add_term(HnnSum &s, wide value, uwide magnitude) {
    s.ring += (uwide)value;
    s.bound = hnn_certify(s.bound, magnitude);
}

__device__ __forceinline__ void hnn_add(HnnSum &s, wide value) {
    hnn_add_term(s, value, hnn_magnitude(value));
}

__device__ __forceinline__ void hnn_add_words(HnnSum &s, int64_t a, int64_t b) {
    const wide p = hnn_word_product(a, b);
    hnn_add_term(s, p, hnn_magnitude(p));
}

__device__ __forceinline__ void hnn_add_scaled(HnnSum &s, int64_t a, wide b) {
    uwide magnitude;
    const wide p = hnn_bounded_product(a, b, &magnitude);
    hnn_add_term(s, p, magnitude);
}

__device__ __forceinline__ wide hnn_read(const HnnSum &s, uint32_t *status) {
    return hnn_certified(s.ring, s.bound, status);
}

// `v · 2^s` on the carrier, refused (carrier) when it would reach 2^127; a negative shift is a
// malformed plan.
__device__ __forceinline__ wide hnn_shifted(wide v, long long s, uint32_t *status) {
    if (s < 0) {
        *status |= HNN_REFUSED_MALFORMED;
        return 0;
    }
    if (s == 0 || v == 0) {
        return v;
    }
    if (s >= 127 || hnn_magnitude(v) >= (HNN_CARRIER_BOUND >> s)) {
        *status |= HNN_REFUSED_CARRIER;
        return 0;
    }
    return (wide)((uwide)v << s);
}

// The split onto a state word: `s = q·2^shift + r`, ties upward; `q` kept only as a signed 64-bit
// word (refused, word, otherwise).
__device__ __forceinline__ int64_t hnn_split(wide s, long long shift, wide *remainder,
                                             uint32_t *status) {
    if (shift < 0 || shift > 127) {
        *status |= HNN_REFUSED_MALFORMED;
        *remainder = 0;
        return 0;
    }
    const wide q = hnn_nearest(s, (uint32_t)shift, remainder);
    if (!hnn_is_word(q)) {
        *status |= HNN_REFUSED_WORD;
        *remainder = 0;
        return 0;
    }
    return (int64_t)q;
}

// A difference of two words on the carrier (exact: its magnitude is below 2^65).
__device__ __forceinline__ wide hnn_minus(int64_t a, int64_t b) {
    return (wide)a - (wide)b;
}

// A carrier word as a state word, refused (word) outside it.
__device__ __forceinline__ int64_t hnn_word_of(wide v, uint32_t *status) {
    if (!hnn_is_word(v)) {
        *status |= HNN_REFUSED_WORD;
        return 0;
    }
    return (int64_t)v;
}

// Join a thread's refusal into the block's, remembering the first refused stage and row.
__device__ __forceinline__ void hnn_note(uint32_t status, uint32_t stage, uint32_t row,
                                         uint32_t *bits, unsigned long long *first) {
    if (status) {
        atomicOr(bits, status);
        atomicMin(first, ((unsigned long long)stage << 32) | row);
    }
}

// -------------------------------------------------------------------------------------------------
// copies between resident arrays
// -------------------------------------------------------------------------------------------------
//
// [definition] `table` holds `copies` triples `(from, to, words)` of 8-octet offsets: each copy
// moves `words` words of `source` into `target`. Block `b` is copy `b`; its threads stride the
// words. The copies write disjoint ranges of the target, so they commute. It gathers a word's
// charts from the chart store into the word's own operands in one launch.
extern "C" __global__ void hnn_copy_words(
    const int64_t *source, int64_t *target, const unsigned long long *table, uint32_t copies
) {
    const uint32_t b = blockIdx.x;
    if (b >= copies) {
        return;
    }
    const unsigned long long from = table[3 * b], to = table[3 * b + 1], words = table[3 * b + 2];
    for (unsigned long long w = threadIdx.x; w < words; w += blockDim.x) {
        target[to + w] = source[from + w];
    }
}

// [definition] The moved words of a publication: `values[i]` into `target[indices[i]]`. Thread `i`
// (of a grid striding the count) writes its own index; the indices are distinct, so the writes
// commute.
extern "C" __global__ void hnn_scatter_words(
    int64_t *target, const unsigned long long *indices, const int64_t *values, uint32_t count
) {
    for (uint32_t i = blockIdx.x * blockDim.x + threadIdx.x; i < count;
         i += gridDim.x * blockDim.x) {
        target[indices[i]] = values[i];
    }
}

// -------------------------------------------------------------------------------------------------
// the pair port's weights at the open
// -------------------------------------------------------------------------------------------------
//
// [definition] `holonics::hnn::PairPort::apply`: at phase `c`, rank `ρ`, the weight
// `w_(c,ρ) = Σ_(x,y) C_c[x, y] a_ρ[x] b_ρ[y]` of the offset counts (row the current cell, column the
// earlier), exact at the pair port's scale `2σ` (`a`, `b` on `2^(−σ)ℤ`). Block `(c, ρ)`; thread `t`
// takes the current cells `x ≡ t` and loops over the earlier cells, summing `C·(a b)` as a word
// times a carrier word; the block joins the sums by the shared tree. Every block writes its own
// weight and status. Shared: 2 · blockDim.x words of 16 octets.
extern "C" __global__ void hnn_pair_weights(
    const unsigned long long *counts, const int64_t *current, const int64_t *earlier,
    uint32_t alphabet, uint32_t rank, uint32_t phases, uint32_t address, unsigned long long nu,
    wide *weights, uint32_t *status
) {
    uwide *ring = (uwide *)hnn_shared;
    uwide *bound = ring + blockDim.x;
    const uint32_t c = blockIdx.x, rho = blockIdx.y, t = threadIdx.x;
    if (c >= phases || rho >= rank) {
        return;
    }
    const unsigned long long *phase = counts + (size_t)c * alphabet * alphabet;
    const int64_t *a = current + (size_t)rho * alphabet;
    const int64_t *b = earlier + (size_t)rho * alphabet;
    uwide word = 0, certificate = 0;
    // The indexed normalized column (ruling B): only the earlier cell at the address, each count
    // times the column's population chart numerator (zero at an unsupported fibre).
    for (uint32_t x = t; x < alphabet && nu != 0; x += blockDim.x) {
        const unsigned long long count = phase[(size_t)x * alphabet + address];
        if (count == 0) {
            continue;
        }
        uwide magnitude;
        // A column's count is at most its population N_a, so count · ⌊2^L/N_a + ½⌋ < 2^(L+1) + N_a,
        // within the signed word.
        const wide p = hnn_bounded_product(
            (int64_t)(count * nu), hnn_word_product(a[x], b[address]), &magnitude
        );
        word += (uwide)p;
        certificate = hnn_certify(certificate, magnitude);
    }
    ring[t] = word;
    bound[t] = certificate;
    __syncthreads();
    hnn_block_sum(ring, bound, t);
    if (t == 0) {
        uint32_t read = HNN_EXACT;
        const wide value = hnn_certified(ring[0], bound[0], &read);
        weights[(size_t)c * rank + rho] = read == HNN_EXACT ? value : (wide)0;
        status[(size_t)c * rank + rho] = read;
    }
}

// -------------------------------------------------------------------------------------------------
// the forward word
// -------------------------------------------------------------------------------------------------

#define HNN_AT(type, name) ((type *)(word + layout[name]))

// The stages, for the first refusal's report.
#define STAGE_OPEN 1
#define STAGE_JUNCTION 2
#define STAGE_OPERAND 3
#define STAGE_RIGHT 4
#define STAGE_ELEMENT 5
#define STAGE_SOLVE 6
#define STAGE_ARRIVAL 7
#define STAGE_LAST 8
#define STAGE_READ 9

extern "C" __global__ void hnn_word_forward(
    const long long *plan, const int64_t *operands, const int64_t *published,
    const unsigned long long *moment, const wide *pair_weights,
    unsigned char *word, const unsigned long long *layout
) {
    __shared__ uint32_t bits;
    __shared__ unsigned long long first;
    const uint32_t t = threadIdx.x, T = blockDim.x;
    if (t == 0) {
        bits = 0;
        first = ~0ull;
    }
    const long long R = plan[WP_RINGS], C = plan[WP_CONTACTS], steps = plan[WP_STEPS];
    const long long Lc = plan[WP_LC], Lw = plan[WP_LW];
    const long long N = plan[WP_RING_ROWS], NA = plan[WP_ARRIVALS], K = plan[WP_CONTACT_ROWS];
    const long long h_mul = plan[WP_H_MUL], h_shift = plan[WP_H_SHIFT];
    const long long x_mul = plan[WP_X_MUL], x_shift = plan[WP_X_SHIFT];
    const long long *rings = plan + plan[WP_RING_TABLE];
    const long long *contacts = plan + plan[WP_CONTACT_TABLE];
    const long long *incidence = plan + plan[WP_INCIDENCE];
    const long long *row_ring = plan + plan[WP_ROW_RING];
    const long long *row_contact = plan + plan[WP_ROW_CONTACT];
    const long long *arrival_table = plan + plan[WP_ARRIVAL_TABLE];
    (void)R;
    (void)C;

    int64_t *storage = HNN_AT(int64_t, WL_STORAGE);
    int64_t *arrivals = HNN_AT(int64_t, WL_ARRIVALS);
    int64_t *u = HNN_AT(int64_t, WL_U);
    int64_t *w = HNN_AT(int64_t, WL_W);
    wide *rem_anchor = HNN_AT(wide, WL_REM_ANCHOR);
    wide *rem_storage = HNN_AT(wide, WL_REM_STORAGE);
    wide *rem_solve = HNN_AT(wide, WL_REM_SOLVE);
    wide *rem_arrival = HNN_AT(wide, WL_REM_ARRIVAL);
    wide *rem_disp = HNN_AT(wide, WL_REM_DISP);
    wide *rem_rate = HNN_AT(wide, WL_REM_RATE);
    int64_t *anchor = HNN_AT(int64_t, WL_ANCHOR);
    wide *operand = HNN_AT(wide, WL_OPERAND);
    wide *right = HNN_AT(wide, WL_RIGHT);
    int64_t *zeta = HNN_AT(int64_t, WL_ZETA);
    int64_t *rec_storage = HNN_AT(int64_t, WL_REC_STORAGE);
    int64_t *rec_arrivals = HNN_AT(int64_t, WL_REC_ARRIVALS);
    int64_t *rec_u = HNN_AT(int64_t, WL_REC_U);
    int64_t *rec_w = HNN_AT(int64_t, WL_REC_W);
    int64_t *rec_anchor = HNN_AT(int64_t, WL_REC_ANCHOR);
    wide *rec_mid = HNN_AT(wide, WL_REC_MID);
    wide *rec_right = HNN_AT(wide, WL_REC_RIGHT);
    int64_t *rec_zeta = HNN_AT(int64_t, WL_REC_ZETA);
    wide *rec_omega = HNN_AT(wide, WL_REC_OMEGA);
    wide *logits = HNN_AT(wide, WL_LOGITS);
    uint32_t *status_block = HNN_AT(uint32_t, WL_STATUS);

    // ---- the open: zero change everywhere, then the source rings' storage.
    for (long long e = t; e < N; e += T) {
        storage[e] = 0;
        rem_anchor[e] = 0;
        rem_storage[e] = 0;
    }
    for (long long p = t; p < NA; p += T) {
        arrivals[p] = 0;
        rem_arrival[p] = 0;
    }
    for (long long q = t; q < K; q += T) {
        u[q] = 0;
        w[q] = 0;
        rem_solve[q] = 0;
        rem_disp[q] = 0;
        rem_rate[q] = 0;
    }
    __syncthreads();
    {
        const long long sources = plan[WP_SOURCES];
        const long long *source_table = plan + plan[WP_SOURCE_TABLE];
        const long long *pair_table = plan + plan[WP_PAIR_TABLE];
        const long long alphabet = plan[WP_ALPHABET];
        for (long long s = 0; s < sources; ++s) {
            const long long *src = source_table + s * WS_STRIDE;
            const long long g = src[WS_RING];
            const long long *ring = rings + g * WR_STRIDE;
            const long long n = ring[WR_WIDTH], base = ring[WR_ROWS];
            const long long d = src[WS_PHASES];
            const int64_t *E = published + src[WS_E];
            const unsigned long long *counts = moment + src[WS_COUNTS];
            const long long *gather = plan + src[WS_GATHER];
            // The marginal's population chart numerator (ruling B): M[c, x] ν̂ on the lattice.
            const long long nu = src[WS_NU];
            for (long long i = t; i < n; i += T) {
                uint32_t st = 0;
                HnnSum image = hnn_sum();
                for (long long c = 0; c < d; ++c) {
                    const long long j = gather[c * n + i];
                    HnnSum em = hnn_sum();
                    const int64_t *row = E + j * alphabet;
                    const unsigned long long *m = counts + c * alphabet;
                    for (long long x = 0; x < alphabet; ++x) {
                        if (m[x] != 0) {
                            // m[x] ≤ n, so m[x] · ⌊2^L/n + ½⌋ < 2^(L+1) + n, within the word.
                            hnn_add_words(em, row[x], (int64_t)m[x] * (int64_t)nu);
                        }
                    }
                    hnn_add(image, hnn_shifted(hnn_read(em, &st), src[WS_E_SHIFT], &st));
                    for (long long pp = 0; pp < src[WS_PAIRS]; ++pp) {
                        const long long *pair = pair_table + (src[WS_PAIR_BASE] + pp) * WQ_STRIDE;
                        const long long rank = pair[WQ_RANK];
                        const int64_t *outputs = published + pair[WQ_OUTPUTS];
                        const wide *pw = pair_weights + pair[WQ_WEIGHTS] + c * rank;
                        HnnSum driven = hnn_sum();
                        for (long long rho = 0; rho < rank; ++rho) {
                            hnn_add_scaled(driven, outputs[rho * n + j], pw[rho]);
                        }
                        hnn_add(image, hnn_shifted(hnn_read(driven, &st), pair[WQ_SHIFT], &st));
                    }
                }
                const wide value = hnn_read(image, &st);
                wide remainder = 0;
                const int64_t opened = hnn_split(value, src[WS_OPEN_EXP] - Lw, &remainder, &st);
                storage[base + i] = opened;
                rem_storage[base + i] =
                    hnn_shifted(remainder, ring[WR_STORAGE_EXP] - src[WS_OPEN_EXP], &st);
                hnn_note(st, STAGE_OPEN, (uint32_t)(base + i), &bits, &first);
            }
        }
    }
    __syncthreads();

    for (long long step = 0; step < steps; ++step) {
        // The change at the step's start, recorded for the balance and the return.
        for (long long e = t; e < N; e += T) {
            rec_storage[step * N + e] = storage[e];
        }
        for (long long p = t; p < NA; p += T) {
            rec_arrivals[step * NA + p] = arrivals[p];
        }
        for (long long q = t; q < K; q += T) {
            rec_u[step * K + q] = u[q];
            rec_w[step * K + q] = w[q];
        }
        // The junctions: v = ŵ_s s + Σ ŵ_a a + r, split at L_c.
        for (long long e = t; e < N; e += T) {
            uint32_t st = 0;
            const long long r = row_ring[e];
            const long long *ring = rings + r * WR_STRIDE;
            const long long i = e - ring[WR_ROWS];
            const int64_t *weights = operands + ring[WR_WEIGHTS];
            HnnSum image = hnn_sum();
            hnn_add_words(image, weights[0], storage[e]);
            for (long long k = 0; k < ring[WR_DEGREE]; ++k) {
                const long long *entry = incidence + (ring[WR_INCIDENCE] + k) * WI_STRIDE;
                hnn_add_words(image, weights[k + 1], arrivals[entry[WI_ARRIVAL] + i]);
            }
            hnn_add(image, rem_anchor[e]);
            wide remainder = 0;
            const int64_t v = hnn_split(hnn_read(image, &st), Lc, &remainder, &st);
            anchor[e] = v;
            rem_anchor[e] = remainder;
            rec_anchor[step * N + e] = v;
            hnn_note(st, STAGE_JUNCTION, (uint32_t)e, &bits, &first);
        }
        __syncthreads();
        if (step + 1 < steps) {
            // The elements' operands 2b + W_c c, and the transits' right sides.
            for (long long e = t; e < N; e += T) {
                uint32_t st = 0;
                const long long r = row_ring[e];
                const long long *ring = rings + r * WR_STRIDE;
                const long long base = ring[WR_ROWS], n = ring[WR_WIDTH], i = e - base;
                const wide b = 2 * (wide)anchor[e] - (wide)storage[e];
                HnnSum op = hnn_sum();
                hnn_add(op, hnn_shifted(b, ring[WR_WC_EXP] + 1, &st));
                if (ring[WR_WC] >= 0) {
                    const int64_t *wc = published + ring[WR_WC] + i * n;
                    for (long long j = 0; j < n; ++j) {
                        hnn_add_scaled(op, wc[j], hnn_minus(anchor[base + j], storage[base + j]));
                    }
                }
                operand[e] = hnn_read(op, &st);
                hnn_note(st, STAGE_OPERAND, (uint32_t)e, &bits, &first);
            }
            for (long long q = t; q < K; q += T) {
                uint32_t st = 0;
                const long long a = row_contact[q];
                const long long *contact = contacts + a * WC_STRIDE;
                const long long crow = contact[WC_ROWS], k = contact[WC_WIDTH], kk = q - crow;
                const long long *selection = plan + contact[WC_SELECTION];
                const long long *from = rings + contact[WC_FROM] * WR_STRIDE;
                const long long *to = rings + contact[WC_TO] * WR_STRIDE;
                const long long sf = selection[kk], sto = selection[k + kk];
                const wide alpha_g = 2 * (wide)anchor[from[WR_ROWS] + sf]
                    - (wide)arrivals[contact[WC_ARRIVAL_FROM] + sf];
                const wide alpha_h = 2 * (wide)anchor[to[WR_ROWS] + sto]
                    - (wide)arrivals[contact[WC_ARRIVAL_TO] + sto];
                const long long sr = contact[WC_RIGHT_EXP];
                HnnSum rs = hnn_sum();
                {
                    HnnSum term = hnn_sum();
                    hnn_add_scaled(term, (int64_t)h_mul, alpha_g - alpha_h);
                    hnn_add(rs, hnn_shifted(hnn_read(term, &st), sr - Lw - h_shift, &st));
                }
                if (contact[WC_C] >= 0) {
                    const int64_t *cf = published + contact[WC_C] + kk * k;
                    HnnSum cw = hnn_sum();
                    for (long long j = 0; j < k; ++j) {
                        hnn_add_words(cw, cf[j], w[crow + j]);
                    }
                    const wide stored = hnn_read(cw, &st);
                    hnn_add(rs, hnn_shifted(stored, sr - contact[WC_C_EXP] - Lw + 1, &st));
                }
                if (contact[WC_K] >= 0) {
                    const int64_t *kf = published + contact[WC_K] + kk * k;
                    HnnSum ku = hnn_sum();
                    for (long long j = 0; j < k; ++j) {
                        hnn_add_words(ku, kf[j], u[crow + j]);
                    }
                    HnnSum hk = hnn_sum();
                    hnn_add_scaled(hk, (int64_t)h_mul, hnn_read(ku, &st));
                    const wide stiffened = hnn_read(hk, &st);
                    hnn_add(rs, -hnn_shifted(stiffened, sr - contact[WC_K_EXP] - Lw - h_shift, &st));
                }
                const wide value = hnn_read(rs, &st);
                right[q] = value;
                rec_right[step * K + q] = value;
                hnn_note(st, STAGE_RIGHT, (uint32_t)q, &bits, &first);
            }
            __syncthreads();
            // The elements' images X̂·operand − b, split onto L_w with the storage remainder; the
            // transits' solves m̂·right, split, with ω, w′ and u′.
            for (long long e = t; e < N; e += T) {
                uint32_t st = 0;
                const long long r = row_ring[e];
                const long long *ring = rings + r * WR_STRIDE;
                const long long base = ring[WR_ROWS], n = ring[WR_WIDTH], i = e - base;
                const int64_t *chart = operands + ring[WR_CHART] + i * n;
                const wide b = 2 * (wide)anchor[e] - (wide)storage[e];
                const long long swc = ring[WR_WC_EXP];
                HnnSum im = hnn_sum();
                for (long long j = 0; j < n; ++j) {
                    hnn_add_scaled(im, chart[j], operand[base + j]);
                }
                const wide lifted = hnn_shifted(b, Lc + swc, &st);
                hnn_add(im, -lifted);
                const wide image = hnn_read(im, &st);
                HnnSum mid = hnn_sum();
                hnn_add(mid, lifted);
                hnn_add(mid, image);
                rec_mid[step * N + e] = hnn_read(mid, &st);
                HnnSum carried = hnn_sum();
                hnn_add(carried, hnn_shifted(image, ring[WR_STORAGE_EXP] - (Lc + swc + Lw), &st));
                hnn_add(carried, rem_storage[e]);
                wide remainder = 0;
                const int64_t next =
                    hnn_split(hnn_read(carried, &st), ring[WR_STORAGE_EXP] - Lw, &remainder, &st);
                storage[e] = next;
                rem_storage[e] = remainder;
                hnn_note(st, STAGE_ELEMENT, (uint32_t)e, &bits, &first);
            }
            for (long long q = t; q < K; q += T) {
                uint32_t st = 0;
                const long long a = row_contact[q];
                const long long *contact = contacts + a * WC_STRIDE;
                const long long crow = contact[WC_ROWS], k = contact[WC_WIDTH], kk = q - crow;
                const int64_t *chart = operands + contact[WC_CHART] + kk * k;
                HnnSum im = hnn_sum();
                for (long long j = 0; j < k; ++j) {
                    hnn_add_scaled(im, chart[j], right[crow + j]);
                }
                hnn_add(im, rem_solve[q]);
                wide remainder = 0;
                const int64_t z = hnn_split(
                    hnn_read(im, &st), Lc + contact[WC_RIGHT_EXP] - Lw, &remainder, &st
                );
                zeta[q] = z;
                rem_solve[q] = remainder;
                rec_zeta[step * K + q] = z;
                const long long eg = contact[WC_GAIN_EXP];
                const wide omega = hnn_word_product((int64_t)contact[WC_GAIN], z);
                rec_omega[step * K + q] = omega;
                HnnSum rate = hnn_sum();
                hnn_add(rate, hnn_shifted(omega, 1, &st));
                hnn_add(rate, -hnn_shifted((wide)w[q], eg, &st));
                hnn_add(rate, rem_rate[q]);
                wide rate_remainder = 0;
                const int64_t next_w = hnn_split(hnn_read(rate, &st), eg, &rate_remainder, &st);
                HnnSum disp = hnn_sum();
                hnn_add(disp, hnn_shifted((wide)u[q], eg + h_shift, &st));
                hnn_add_scaled(disp, (int64_t)h_mul, omega);
                hnn_add(disp, rem_disp[q]);
                wide disp_remainder = 0;
                const int64_t next_u =
                    hnn_split(hnn_read(disp, &st), eg + h_shift, &disp_remainder, &st);
                w[q] = next_w;
                u[q] = next_u;
                rem_rate[q] = rate_remainder;
                rem_disp[q] = disp_remainder;
                hnn_note(st, STAGE_SOLVE, (uint32_t)q, &bits, &first);
            }
            __syncthreads();
            // The arrivals: each wave reflects to its own ring, the channel exchanging ∓ζ/h.
            for (long long p = t; p < NA; p += T) {
                uint32_t st = 0;
                const long long *entry = arrival_table + p * WA_STRIDE;
                const long long *ring = rings + entry[WA_RING] * WR_STRIDE;
                const wide outgoing =
                    2 * (wide)anchor[ring[WR_ROWS] + entry[WA_COORD]] - (wide)arrivals[p];
                HnnSum value = hnn_sum();
                hnn_add(value, hnn_shifted(outgoing, x_shift, &st));
                if (entry[WA_CHANNEL] >= 0) {
                    const long long *contact = contacts + entry[WA_CONTACT] * WC_STRIDE;
                    const int64_t z = zeta[contact[WC_ROWS] + entry[WA_CHANNEL]];
                    const wide exchange = hnn_word_product((int64_t)x_mul, z);
                    hnn_add(value, entry[WA_END] == 0 ? -exchange : exchange);
                }
                hnn_add(value, rem_arrival[p]);
                wide remainder = 0;
                const int64_t next = hnn_split(hnn_read(value, &st), x_shift, &remainder, &st);
                arrivals[p] = next;
                rem_arrival[p] = remainder;
                hnn_note(st, STAGE_ARRIVAL, (uint32_t)p, &bits, &first);
            }
            __syncthreads();
        } else {
            // The last junction: the storage and outgoing waves become the change, unsplit.
            for (long long e = t; e < N; e += T) {
                uint32_t st = 0;
                storage[e] = hnn_word_of(2 * (wide)anchor[e] - (wide)storage[e], &st);
                hnn_note(st, STAGE_LAST, (uint32_t)e, &bits, &first);
            }
            for (long long p = t; p < NA; p += T) {
                uint32_t st = 0;
                const long long *entry = arrival_table + p * WA_STRIDE;
                const long long *ring = rings + entry[WA_RING] * WR_STRIDE;
                arrivals[p] = hnn_word_of(
                    2 * (wide)anchor[ring[WR_ROWS] + entry[WA_COORD]] - (wide)arrivals[p], &st
                );
                hnn_note(st, STAGE_LAST, (uint32_t)p, &bits, &first);
            }
            __syncthreads();
        }
    }

    // The receiving read f_j = R · P_R^(τ_R) v_R(e_j), each logit a certified sum.
    const long long receiver = plan[WP_RECEIVER];
    if (receiver >= 0) {
        const long long *ring = rings + receiver * WR_STRIDE;
        const long long n = ring[WR_WIDTH], base = ring[WR_ROWS];
        const long long rows = plan[WP_MAP_ROWS], aperture = plan[WP_APERTURE];
        const long long epoch = plan[WP_EPOCH];
        const long long *gather = plan + plan[WP_GATHER];
        const int64_t *map = published + plan[WP_MAP];
        for (long long entry = t; entry < aperture * rows; entry += T) {
            uint32_t st = 0;
            const long long j = entry / rows, row = entry % rows;
            const int64_t *v = rec_anchor + (epoch + j) * N + base;
            HnnSum logit = hnn_sum();
            for (long long k = 0; k < n; ++k) {
                hnn_add_words(logit, map[row * n + k], v[gather[k]]);
            }
            logits[entry] = hnn_read(logit, &st);
            hnn_note(st, STAGE_READ, (uint32_t)entry, &bits, &first);
        }
    }
    __syncthreads();
    if (t == 0) {
        status_block[WSTATUS_BITS] = bits;
        status_block[WSTATUS_STAGE] = bits ? (uint32_t)(first >> 32) : 0u;
        status_block[WSTATUS_ROW] = bits ? (uint32_t)(first & 0xffffffffu) : 0u;
    }
}

// -------------------------------------------------------------------------------------------------
// the word's return
// -------------------------------------------------------------------------------------------------
//
// [definition] `holonics::hnn::port::Word::pull_back` (the executed adjoint, Lean
// `HNN/LatticeWord.executed_adjoint_unique`): per step in reverse, the elements through their
// charts' transposes, the transits through theirs, then the junctions' reverse Swings at their
// executed weights, every carried covector split onto `2^(−L_w)ℤ` with its own remainder. Scales:
//
// ```text
// element  u = split(X̂ᵀ s̄ + r)                     L_c + L_w                 onto L_w
//          wave = 2u − s̄ (L_w),  contrast = W_cᵀ u  (σ_Wc + L_w)
// transit  ζ̄ = split((G/h) w̄ + (G/2) ū + (ā_h − ā_g)/h + r)   σ_Z              onto L_w
//          solved = split(m̂ᵀ ζ̄ + r)                 L_c + L_w                 onto L_w
//          outgoing = ā ± h·solved on the channel     L_w + H
//          w̄′ = split(−w̄ + 2 C solved + r)          σ_C + L_w                 onto L_w
//          ū′ = split(ū − h K solved + r)            σ_K + L_w + H             onto L_w
// junction anchor = 2 wave + contrast + 2 Σ outgoing + read     σ_A = L_w + max(σ_Wc, H)
//          s̄′ = split(ŵ_s anchor − (wave + contrast) + r)       L_c + σ_A        onto L_w
//          ā′ = split(ŵ_a anchor − outgoing + r)                  L_c + σ_A        onto L_w
// ```
//
// and the conductance covector's dyadic parts, which the host divides and sums: per step and
// contact `⟨solved, ω⟩` and `⟨exchange, ω⟩` (`2L_w + e_g`), and per step and incidence
// `⟨anchor, a − v⟩` (`σ_A + L_w`), each read over its own rows by one thread.
// Realization as the forward word's: one block, the stages' rows striding its threads, a barrier
// between stages.

#define RSTAGE_ELEMENT 1
#define RSTAGE_ZETA 2
#define RSTAGE_CONTRAST 3
#define RSTAGE_SOLVED 4
#define RSTAGE_STATE 5
#define RSTAGE_OUTGOING 6
#define RSTAGE_DOTS 7
#define RSTAGE_JUNCTION 8

extern "C" __global__ void hnn_word_reverse(
    const long long *plan, const int64_t *operands, const int64_t *published,
    unsigned char *word, const unsigned long long *layout
) {
    __shared__ uint32_t bits;
    __shared__ unsigned long long first;
    const uint32_t t = threadIdx.x, T = blockDim.x;
    if (t == 0) {
        bits = 0;
        first = ~0ull;
    }
    const long long C = plan[WP_CONTACTS], steps = plan[WP_STEPS];
    const long long Lc = plan[WP_LC], Lw = plan[WP_LW];
    const long long N = plan[WP_RING_ROWS], NA = plan[WP_ARRIVALS], K = plan[WP_CONTACT_ROWS];
    const long long NI = plan[WP_INCIDENCES];
    const long long h_mul = plan[WP_H_MUL], h_shift = plan[WP_H_SHIFT];
    const long long x_mul = plan[WP_X_MUL], x_shift = plan[WP_X_SHIFT];
    const long long *rings = plan + plan[WP_RING_TABLE];
    const long long *contacts = plan + plan[WP_CONTACT_TABLE];
    const long long *incidence = plan + plan[WP_INCIDENCE];
    const long long *row_ring = plan + plan[WP_ROW_RING];
    const long long *row_contact = plan + plan[WP_ROW_CONTACT];
    const long long *arrival_table = plan + plan[WP_ARRIVAL_TABLE];
    const long long receiver = plan[WP_RECEIVER];
    const long long epoch = plan[WP_EPOCH], aperture = plan[WP_APERTURE];

    // The forward word's record.
    const int64_t *rec_arrivals = HNN_AT(int64_t, WL_REC_ARRIVALS);
    const int64_t *rec_anchor = HNN_AT(int64_t, WL_REC_ANCHOR);
    const wide *rec_omega = HNN_AT(wide, WL_REC_OMEGA);
    // The return's carried covectors, remainders and scratch.
    int64_t *storage_bar = HNN_AT(int64_t, WL_BAR_STORAGE);
    int64_t *arrival_bar = HNN_AT(int64_t, WL_BAR_ARRIVAL);
    int64_t *disp_bar = HNN_AT(int64_t, WL_BAR_DISP);
    int64_t *rate_bar = HNN_AT(int64_t, WL_BAR_RATE);
    wide *rem_el = HNN_AT(wide, WL_REV_EL);
    wide *rem_zeta = HNN_AT(wide, WL_REV_ZETA);
    wide *rem_solved = HNN_AT(wide, WL_REV_SOLVED);
    wide *rem_rate = HNN_AT(wide, WL_REV_RATE);
    wide *rem_disp = HNN_AT(wide, WL_REV_DISP);
    wide *rem_storage = HNN_AT(wide, WL_REV_STORAGE);
    wide *rem_arrival = HNN_AT(wide, WL_REV_ARRIVAL);
    int64_t *adj_u = HNN_AT(int64_t, WL_ADJ_U);
    wide *wave = HNN_AT(wide, WL_WAVE);
    wide *contrast = HNN_AT(wide, WL_CONTRAST);
    wide *outgoing = HNN_AT(wide, WL_OUTGOING);
    wide *exchange = HNN_AT(wide, WL_EXCHANGE);
    int64_t *zeta_bar = HNN_AT(int64_t, WL_ZETA_BAR);
    int64_t *solved = HNN_AT(int64_t, WL_SOLVED);
    wide *anchor_bar = HNN_AT(wide, WL_ANCHOR_BAR);
    int64_t *rec_adj_u = HNN_AT(int64_t, WL_REC_ADJ_U);
    int64_t *rec_solved = HNN_AT(int64_t, WL_REC_SOLVED);
    wide *dots1 = HNN_AT(wide, WL_DOTS1);
    wide *dots2 = HNN_AT(wide, WL_DOTS2);
    wide *dots3 = HNN_AT(wide, WL_DOTS3);
    const int64_t *reads = HNN_AT(int64_t, WL_READS);
    uint32_t *status_block = HNN_AT(uint32_t, WL_REV_STATUS);

    for (long long e = t; e < N; e += T) {
        storage_bar[e] = 0;
        rem_el[e] = 0;
        rem_storage[e] = 0;
    }
    for (long long p = t; p < NA; p += T) {
        arrival_bar[p] = 0;
        rem_arrival[p] = 0;
    }
    for (long long q = t; q < K; q += T) {
        disp_bar[q] = 0;
        rate_bar[q] = 0;
        rem_zeta[q] = 0;
        rem_solved[q] = 0;
        rem_rate[q] = 0;
        rem_disp[q] = 0;
    }
    __syncthreads();

    for (long long step = steps - 1; step >= 0; --step) {
        for (long long e = t; e < N; e += T) {
            wave[e] = 0;
            contrast[e] = 0;
        }
        for (long long p = t; p < NA; p += T) {
            outgoing[p] = 0;
        }
        __syncthreads();
        if (step + 1 < steps) {
            // The elements: u = split(X̂ᵀ s̄ + r); wave = 2u − s̄.
            for (long long e = t; e < N; e += T) {
                uint32_t st = 0;
                const long long r = row_ring[e];
                const long long *ring = rings + r * WR_STRIDE;
                const long long base = ring[WR_ROWS], n = ring[WR_WIDTH], i = e - base;
                const int64_t *chart = operands + ring[WR_CHART];
                HnnSum image = hnn_sum();
                for (long long j = 0; j < n; ++j) {
                    hnn_add_words(image, chart[j * n + i], storage_bar[base + j]);
                }
                hnn_add(image, rem_el[e]);
                wide remainder = 0;
                const int64_t adjoint = hnn_split(hnn_read(image, &st), Lc, &remainder, &st);
                rem_el[e] = remainder;
                adj_u[e] = adjoint;
                rec_adj_u[step * N + e] = adjoint;
                wave[e] = 2 * (wide)adjoint - (wide)storage_bar[e];
                hnn_note(st, RSTAGE_ELEMENT, (uint32_t)e, &bits, &first);
            }
            // The transits' exchange and ζ̄.
            for (long long q = t; q < K; q += T) {
                uint32_t st = 0;
                const long long a = row_contact[q];
                const long long *contact = contacts + a * WC_STRIDE;
                const long long crow = contact[WC_ROWS], k = contact[WC_WIDTH], kk = q - crow;
                const long long *selection = plan + contact[WC_SELECTION];
                const wide ex = hnn_minus(
                    arrival_bar[contact[WC_ARRIVAL_TO] + selection[k + kk]],
                    arrival_bar[contact[WC_ARRIVAL_FROM] + selection[kk]]
                );
                exchange[q] = ex;
                const long long sz = contact[WC_ZETA_EXP];
                HnnSum image = hnn_sum();
                hnn_add(image, hnn_shifted(
                    hnn_word_product((int64_t)contact[WC_RATE_GAIN], rate_bar[q]),
                    sz - Lw - contact[WC_RATE_GAIN_EXP], &st
                ));
                hnn_add(image, hnn_shifted(
                    hnn_word_product((int64_t)contact[WC_SHIFT_GAIN], disp_bar[q]),
                    sz - Lw - contact[WC_SHIFT_GAIN_EXP], &st
                ));
                {
                    HnnSum term = hnn_sum();
                    hnn_add_scaled(term, (int64_t)x_mul, ex);
                    hnn_add(image, hnn_shifted(hnn_read(term, &st), sz - Lw - x_shift, &st));
                }
                hnn_add(image, rem_zeta[q]);
                wide remainder = 0;
                zeta_bar[q] = hnn_split(hnn_read(image, &st), sz - Lw, &remainder, &st);
                rem_zeta[q] = remainder;
                hnn_note(st, RSTAGE_ZETA, (uint32_t)q, &bits, &first);
            }
            __syncthreads();
            // The elements' contrast W_cᵀ u; the transits' solved = split(m̂ᵀ ζ̄ + r).
            for (long long e = t; e < N; e += T) {
                uint32_t st = 0;
                const long long r = row_ring[e];
                const long long *ring = rings + r * WR_STRIDE;
                const long long base = ring[WR_ROWS], n = ring[WR_WIDTH], i = e - base;
                if (ring[WR_WC] >= 0) {
                    const int64_t *wc = published + ring[WR_WC];
                    HnnSum drive = hnn_sum();
                    for (long long j = 0; j < n; ++j) {
                        hnn_add_words(drive, wc[j * n + i], adj_u[base + j]);
                    }
                    contrast[e] = hnn_read(drive, &st);
                }
                hnn_note(st, RSTAGE_CONTRAST, (uint32_t)e, &bits, &first);
            }
            for (long long q = t; q < K; q += T) {
                uint32_t st = 0;
                const long long a = row_contact[q];
                const long long *contact = contacts + a * WC_STRIDE;
                const long long crow = contact[WC_ROWS], k = contact[WC_WIDTH], kk = q - crow;
                const int64_t *chart = operands + contact[WC_CHART];
                HnnSum image = hnn_sum();
                for (long long j = 0; j < k; ++j) {
                    hnn_add_words(image, chart[j * k + kk], zeta_bar[crow + j]);
                }
                hnn_add(image, rem_solved[q]);
                wide remainder = 0;
                const int64_t value = hnn_split(hnn_read(image, &st), Lc, &remainder, &st);
                rem_solved[q] = remainder;
                solved[q] = value;
                rec_solved[step * K + q] = value;
                hnn_note(st, RSTAGE_SOLVED, (uint32_t)q, &bits, &first);
            }
            __syncthreads();
            // The transits' previous state covectors and the outgoing covectors at their ends.
            for (long long q = t; q < K; q += T) {
                uint32_t st = 0;
                const long long a = row_contact[q];
                const long long *contact = contacts + a * WC_STRIDE;
                const long long crow = contact[WC_ROWS], k = contact[WC_WIDTH], kk = q - crow;
                const long long sc = contact[WC_C] >= 0 ? contact[WC_C_EXP] : 0;
                const long long sk = contact[WC_K] >= 0 ? contact[WC_K_EXP] : 0;
                HnnSum rate = hnn_sum();
                hnn_add(rate, -hnn_shifted((wide)rate_bar[q], sc, &st));
                if (contact[WC_C] >= 0) {
                    const int64_t *cf = published + contact[WC_C] + kk * k;
                    HnnSum stored = hnn_sum();
                    for (long long j = 0; j < k; ++j) {
                        hnn_add_words(stored, cf[j], solved[crow + j]);
                    }
                    hnn_add(rate, hnn_shifted(hnn_read(stored, &st), 1, &st));
                }
                hnn_add(rate, rem_rate[q]);
                wide rate_remainder = 0;
                const int64_t rate_prev = hnn_split(hnn_read(rate, &st), sc, &rate_remainder, &st);
                HnnSum disp = hnn_sum();
                hnn_add(disp, hnn_shifted((wide)disp_bar[q], sk + h_shift, &st));
                if (contact[WC_K] >= 0) {
                    const int64_t *kf = published + contact[WC_K] + kk * k;
                    HnnSum stiffened = hnn_sum();
                    for (long long j = 0; j < k; ++j) {
                        hnn_add_words(stiffened, kf[j], solved[crow + j]);
                    }
                    HnnSum hk = hnn_sum();
                    hnn_add_scaled(hk, (int64_t)h_mul, hnn_read(stiffened, &st));
                    hnn_add(disp, -hnn_read(hk, &st));
                }
                hnn_add(disp, rem_disp[q]);
                wide disp_remainder = 0;
                const int64_t disp_prev =
                    hnn_split(hnn_read(disp, &st), sk + h_shift, &disp_remainder, &st);
                rate_bar[q] = rate_prev;
                disp_bar[q] = disp_prev;
                rem_rate[q] = rate_remainder;
                rem_disp[q] = disp_remainder;
                hnn_note(st, RSTAGE_STATE, (uint32_t)q, &bits, &first);
            }
            for (long long p = t; p < NA; p += T) {
                uint32_t st = 0;
                const long long *entry = arrival_table + p * WA_STRIDE;
                HnnSum value = hnn_sum();
                hnn_add(value, hnn_shifted((wide)arrival_bar[p], h_shift, &st));
                if (entry[WA_CHANNEL] >= 0) {
                    const long long *contact = contacts + entry[WA_CONTACT] * WC_STRIDE;
                    const int64_t z = solved[contact[WC_ROWS] + entry[WA_CHANNEL]];
                    const wide pushed = hnn_word_product((int64_t)h_mul, z);
                    hnn_add(value, entry[WA_END] == 0 ? pushed : -pushed);
                }
                outgoing[p] = hnn_read(value, &st);
                hnn_note(st, RSTAGE_OUTGOING, (uint32_t)p, &bits, &first);
            }
            __syncthreads();
            // The transits' conductance parts, each over its own channel.
            for (long long a = t; a < C; a += T) {
                uint32_t st = 0;
                const long long *contact = contacts + a * WC_STRIDE;
                const long long crow = contact[WC_ROWS], k = contact[WC_WIDTH];
                HnnSum d1 = hnn_sum(), d2 = hnn_sum();
                for (long long j = 0; j < k; ++j) {
                    const wide omega = rec_omega[step * K + crow + j];
                    hnn_add_scaled(d1, solved[crow + j], omega);
                    const int64_t ex = hnn_word_of(exchange[crow + j], &st);
                    hnn_add_scaled(d2, ex, omega);
                }
                dots1[step * C + a] = hnn_read(d1, &st);
                dots2[step * C + a] = hnn_read(d2, &st);
                hnn_note(st, RSTAGE_DOTS, (uint32_t)a, &bits, &first);
            }
        }
        // The junctions' reverse Swings.
        for (long long e = t; e < N; e += T) {
            uint32_t st = 0;
            const long long r = row_ring[e];
            const long long *ring = rings + r * WR_STRIDE;
            const long long base = ring[WR_ROWS], i = e - base;
            const long long sa = ring[WR_ANCHOR_EXP];
            const long long swc = ring[WR_WC] >= 0 ? ring[WR_WC_EXP] : 0;
            const int64_t *weights = operands + ring[WR_WEIGHTS];
            HnnSum an = hnn_sum();
            hnn_add(an, hnn_shifted(2 * wave[e], sa - Lw, &st));
            hnn_add(an, hnn_shifted(contrast[e], sa - Lw - swc, &st));
            for (long long k = 0; k < ring[WR_DEGREE]; ++k) {
                const long long *entry = incidence + (ring[WR_INCIDENCE] + k) * WI_STRIDE;
                hnn_add(an, hnn_shifted(2 * outgoing[entry[WI_ARRIVAL] + i], sa - Lw - h_shift, &st));
            }
            if (r == receiver && step >= epoch && step < epoch + aperture) {
                const int64_t read = reads[(step - epoch) * ring[WR_WIDTH] + i];
                hnn_add(an, hnn_shifted((wide)read, sa - Lw, &st));
            }
            const wide anchor = hnn_read(an, &st);
            anchor_bar[e] = anchor;
            HnnSum sbar = hnn_sum();
            hnn_add_scaled(sbar, weights[0], anchor);
            hnn_add(sbar, -hnn_shifted(wave[e], Lc + sa - Lw, &st));
            hnn_add(sbar, -hnn_shifted(contrast[e], Lc + sa - Lw - swc, &st));
            hnn_add(sbar, rem_storage[e]);
            wide remainder = 0;
            storage_bar[e] = hnn_split(hnn_read(sbar, &st), Lc + sa - Lw, &remainder, &st);
            rem_storage[e] = remainder;
            for (long long k = 0; k < ring[WR_DEGREE]; ++k) {
                const long long *entry = incidence + (ring[WR_INCIDENCE] + k) * WI_STRIDE;
                const long long p = entry[WI_ARRIVAL] + i;
                HnnSum abar = hnn_sum();
                hnn_add_scaled(abar, weights[k + 1], anchor);
                hnn_add(abar, -hnn_shifted(outgoing[p], Lc + sa - Lw - h_shift, &st));
                hnn_add(abar, rem_arrival[p]);
                wide arrival_remainder = 0;
                arrival_bar[p] =
                    hnn_split(hnn_read(abar, &st), Lc + sa - Lw, &arrival_remainder, &st);
                rem_arrival[p] = arrival_remainder;
            }
            hnn_note(st, RSTAGE_JUNCTION, (uint32_t)e, &bits, &first);
        }
        __syncthreads();
        // The junctions' conductance parts ⟨anchor, a − v⟩, one incidence per thread.
        for (long long x = t; x < NI; x += T) {
            uint32_t st = 0;
            const long long *entry = incidence + x * WI_STRIDE;
            // The incidence's ring: the entry lies in its ring's range of the table.
            long long r = 0;
            while (!(x >= rings[r * WR_STRIDE + WR_INCIDENCE]
                     && x < rings[r * WR_STRIDE + WR_INCIDENCE] + rings[r * WR_STRIDE + WR_DEGREE])) {
                ++r;
            }
            const long long *ring = rings + r * WR_STRIDE;
            const long long base = ring[WR_ROWS], n = ring[WR_WIDTH];
            HnnSum d3 = hnn_sum();
            for (long long i = 0; i < n; ++i) {
                const wide offset = hnn_minus(
                    rec_arrivals[step * NA + entry[WI_ARRIVAL] + i], rec_anchor[step * N + base + i]
                );
                const int64_t off = hnn_word_of(offset, &st);
                hnn_add_scaled(d3, off, anchor_bar[base + i]);
            }
            dots3[step * NI + x] = hnn_read(d3, &st);
            hnn_note(st, RSTAGE_DOTS, (uint32_t)x, &bits, &first);
        }
        __syncthreads();
    }
    if (t == 0) {
        status_block[WSTATUS_BITS] = bits;
        status_block[WSTATUS_STAGE] = bits ? (uint32_t)(first >> 32) : 0u;
        status_block[WSTATUS_ROW] = bits ? (uint32_t)(first & 0xffffffffu) : 0u;
    }
}

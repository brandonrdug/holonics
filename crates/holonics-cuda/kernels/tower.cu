// **The gated tower's training pass on the card** (#404, #76; owner `src/hnn/tower.rs`).
//
// The forward and the reverse scan of `holonics::hnn::tower` (its module law; the host owner is
// `Tower::step` and `Tower::reverse_joined`) for the declaration the card carries (with or without
// a news clock, `NewsClock`: each level's modes take their step once a tick of its own clock with
// the arrival held, the ticks read by thread 0 from the arriving class's code under the open
// face): gated modes,
// turned or not (each cell's founded unit turned by `e^(iπ s_t)`, `s_t = 2^(−spread)(W_φ x + b_φ)`
// composed from the ladder's dyadic turns), pumped or not (a turned mode's move the parametron's,
// `h ← α_t h + β_t conj(h) + γ_t P x_t`, `α_t = ρ_t (1 − |κ_t|) U_t`, `β_t = ρ_t κ_t e^(iπ p_t)`,
// `κ_t = 2r − 1` with `r` the logistic of `W_κ x + b_κ` and `p_t = 2^(−spread)(W_ψ x + b_ψ)`;
// never beside a news clock), with or without a rotor (`Rotor`: before a level's move each arriving
// class steps the level's rings and turns their modes, `h' = T P^σ h`, mode `m` taking mode `s(m)`
// turned by `e^(2πi r/q)` from the rotor's resident keys; never beside the ring face or a news
// clock), contacts rectifying (`v = max(a, 0)`), the pair contact (`v = a ⊙ b`, `b = W_b r̂ + b_b`)
// or its foil (`v = a b_b + b_a (b − b_b)`), no passage credit, with or without the pair face
// (`x⁰ = E(u) + P c(p)` and `z += V c(p)` at the pair of the class before and the class arriving)
// and with or without the ring face (`RingFace`: its ranks advanced at their level after the move,
// their faces read through the pair contact with the top face, `z += W (x̂ ⊗ ρ)`; the products the
// host widens to a big integer released here through 256 bits). Every quantity
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
// - `tower_pair_biases`: the pair contact's foil only, one thread a bias entry summing its own
//   covector over every cell (the pair contact's and the rectifier's biases ride their drive's
//   outer sum).
// - `tower_reverse_modes`: one block a stream, one thread a mode, the cells in reverse order (the
//   scan `G_h(t) = read covector + conj(λ_(t+1)) G_h(t+1)`, `+ β_(t+1) conj(G_h(t+1))` when
//   pumped, carried back through the rotor's adjoint at the later cell when one is joined, the
//   block's threads exchanging it through shared memory, every covector of the move reading the
//   stepped state `h'`), with each cell's gated move adjoint, a turned level's turn covector `δs` and a pumped
//   level's depth and axis covectors `δκ`, `δp`, which `tower_reverse_dx` returns through `W_φᵀ`,
//   `W_κᵀ` and `W_ψᵀ` and `tower_outer` sums against the level's input.
// - `tower_reverse_ring`: one block a stream, the ring's scan over the cells in reverse order (one
//   thread a rank), the carried face's covector onto the read covector before the modes' scan, and
//   each factor's covector; `tower_ring_factors` sums the factors' over the streams.
// - `tower_outer`: the families' outer sums `Σ_(s,t) y_(s,t) x_(s,t)ᵀ` over every stream's cells,
//   a tile of 16 × 64 outputs a block, four a thread; summed per stream in 64 bits when that
//   stream's bound `Σ_t max|y_t| max(max|x_t|, 1)` is below 2^63, in 128 bits otherwise.
// - `tower_encoding`, `tower_moves`: the encoding's covector (each cell's bottom covector at its
//   class) and the moves' Cartesian covectors summed over the streams. The pair face's readout and
//   lift take theirs through `tower_outer` (`Σ δz c(p)ᵀ` and `Σ δx⁰ c(p)ᵀ`).

#include <stdint.h>

typedef __int128 wide;
typedef unsigned __int128 uwide;

#define TOWER_MAX_LEVELS 4
#define TOWER_THREADS 256
// The turned modes' ladder e^(iπ/2^i), i = 0..=TURN_BITS.
#define TOWER_LADDER 17

// Refusal bits (`src/hnn/tower.rs` names them).
#define TOWER_REFUSED_CARRIER 1u
#define TOWER_REFUSED_WORD64 2u
#define TOWER_REFUSED_WORD32 4u
#define TOWER_REFUSED_UNIT 8u
#define TOWER_REFUSED_CLASS 16u
#define TOWER_REFUSED_NEWS 32u

// The grains (`holonics::hnn::tower`).
#define FACE_BITS 16
#define MATERIAL_BITS 24
#define MOVE_BITS 30
#define STATE_BITS 24
#define COVECTOR_BITS 24
#define UNIT_BITS 62
#define MARGIN 12
#define GATE_REACH 2
#define TURN_BITS 16
#define READ_BITS 20

struct TowerLevel {
    uint64_t move_re, move_im, push_re, push_im, read_re, read_im, contact, contact_bias, ret,
        ret_bias, gate, gate_bias, turn, turn_bias, pump, pump_bias, pump_axis, pump_axis_bias,
        pair, pair_bias;
    // max |w| of push (re, im), read (re, im), contact, return, gate, turn, pump depth, pump axis,
    // the pair contact's second drive
    uint64_t reach[11];
    // Participation's families (zero without it): the charts probe, key, current (re, im), the
    // current's read (re, im), the contacts' W₁ᵃ and the heads' friction; max |w| of the first nine.
    uint64_t pa[10];
    uint64_t pa_reach[9];
};

struct TowerLaw {
    uint32_t alphabet, width, modes, contacts, levels, cells, streams, face_digits;
    // The contact law: 0 rectifying, 1 the pair contact, 2 its foil.
    uint32_t move_digits, families, forms, contact;
    uint64_t encoding, readout, readout_bias, readout_reach;
    int64_t ln2_square;
    // The pair face (`forms = 0` without one): its readout V (A × k) and lift P (W × k), and their
    // reaches max |V|, max |P|.
    uint64_t pair_readout, pair_lift, pair_reach[2];
    // The ring face (`ring_ranks = 0` without one): the level and mode it rides, its ranks R and
    // the harmonics H its readout reads, the places of its readout W (A × (W + 1)·2RH) and of its
    // factors (R ranks of 6N + 2W + 3: a₀, a₁ over 2N, b₀, b₁ over W + 1, g over 2N + 1), and max |W|.
    uint32_t ring_level, ring_mode, ring_ranks, ring_harmonics;
    uint64_t ring_readout, ring_factors, ring_reach;
    // The turned modes (`turned = 0` when not): the half turn π on 2^(−30), the turn's spread
    // ⌈log₂ W⌉, and the ladder e^(iπ/2^i) on 2^(−30), i = 0..=TURN_BITS.
    int64_t half_turn;
    uint32_t turned, turn_spread;
    int64_t ladder[TOWER_LADDER][2];
    // The pumped modes (`pumped = 0` when not; a pumped mode is turned): ln 2 on 2^(−30), which
    // the depth's covector reads.
    uint32_t pumped;
    // The rotor's moving modes a level (`moving = 0` without a rotor).
    uint32_t moving;
    int64_t ln2;
    TowerLevel level[TOWER_MAX_LEVELS];
    // The news clock (`news = 0` without one, every level then moving once a cell): each level's
    // section `B r^(l−1)` on 2^(−20) bits (level 0's unread: it ticks at every arrival) and the
    // clock's period, the coarsest section (`NewsClock`).
    uint32_t news, pad1;
    uint64_t sections[TOWER_MAX_LEVELS];
    uint64_t period;
    // The strands (`strand_rings = 0` without them): the level whose contacts read them, their
    // rings R, the places of W_sa and W_sb (F × 6R each, W_sb under a pair law) and max |W_sa|,
    // max |W_sb|.
    uint32_t strand_level, strand_rings;
    uint64_t strand_contact, strand_pair, strand_reach[2];
    // Participation (`participation = 0` without it): its heads, the section that admits sites,
    // the pairing's scale 2^(−beta) and log₂ of the margin radius on 2^(−16) (a held move's met
    // dissipation). `ln2` is set beside it.
    uint32_t participation, pa_heads, pa_section, pa_beta;
    int64_t pa_held_log;
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
    // The pair face: its resident values c(prev, cur) at ((prev·A + cur)·k + v), prev over the
    // alphabet and the start A; each stream's class before its first cell; the face read at each
    // cell, max |c| there, and max |δx⁰| (the bottom covector, what the lift's covector reads).
    const int32_t *pair_values; // [(A + 1)·A·k]
    const uint32_t *previous;   // [S]
    int32_t *pair;              // [S][T][k]
    uint64_t *r_pair, *r_dx;    // [S][T]
    // The ring face: the encoding E₀ its pools read; each rank's releases of a, b and g, its push
    // and read shifts; its restarting class (−1 for none); its founded pair moves (rank r's rows
    // at [index[r], index[r + 1]), each prev, cur, Re λ, Im λ, Re β, Im β on 2^(−30), ascending by
    // pair); each stream's rings and hands before its first cell and after its last. Kept for the
    // reverse at each cell: each rank's ring after the cell, its factors α, β, γ, the move it rode
    // and its hand (bit 0 the hand it reads after its move, bit 1 re-based by its restart, bit 2 a
    // founded pair move); the face ρ with its harmonics and each rank's scale; the top's ratio and
    // scale; the pair read φ = x̂ ⊗ ρ and max |φ|. The reverse's own: each rank's read covector,
    // the covector of the mode's move the ring rode (Re, Im), each stream's factor covector.
    const int32_t *ring_opening;  // [A][W]
    const uint32_t *ring_shifts;  // [R][5]
    const int32_t *ring_restarts; // [R]
    const uint32_t *ring_index;   // [R + 1]
    const int64_t *ring_table;    // [M][6]
    const wide *ring_open;        // [S][R][2]
    const uint32_t *hands_open;   // [S][R]
    wide *ring_ends;              // [S][R][2]
    uint32_t *hands_ends;         // [S][R]
    wide *ring_after;             // [S][T][R][2]
    wide *ring_factor;            // [S][T][R][5]: α re, α im, β re, β im, γ
    int64_t *ring_move;           // [S][T][R][4]
    uint32_t *ring_hand;          // [S][T][R]
    int32_t *ring_rho;            // [S][T][2RH]
    int64_t *ring_scale;          // [S][T][R]
    int32_t *top_hat;             // [S][T][W]
    int64_t *top_scale;           // [S][T]
    int32_t *ring_pair;           // [S][T][(W + 1)·2RH]
    uint64_t *r_ring_pair;        // [S][T]
    int64_t *ring_cov;            // [S][T][2R]
    wide *ring_dmove;             // [S][T][4]: λ re, λ im, β re, β im
    wide *ring_g;                 // [S][R·(6N + 2W + 3)]
    // The turned modes: each cell's unit u e^(iπ s_t) on 2^(−30), the turn's covector δs, and
    // max |δs| (each empty when unturned).
    int64_t *units;   // [S][T][L][N][2]
    int64_t *ds;      // [S][T][L][N]
    uint64_t *r_ds;   // [S][T][L]
    // The news clock: each stream's open face before its first cell and after its last (whether
    // it has one, the total's low and high words, the clock's phase, then the masses), and each
    // cell's ticks a level (empty without a clock).
    const uint64_t *news_open; // [S][A + 4]
    uint64_t *news_ends;       // [S][A + 4]
    uint32_t *ticks;           // [S][T][L]
    // The pumped modes: each cell's pump (its opening r and depth κ on 2^(−30), its axis face
    // e^(iπ p_t) and β_t), the depth's and the axis's covectors δκ, δp, and their max |·| (each
    // empty when unpumped). A pumped cell's moves row holds its turn α_t as λ.
    int64_t *pumps;   // [S][T][L][N][6]: r, κ, axis re, axis im, β re, β im
    int64_t *dk, *dp; // [S][T][L][N]
    uint64_t *r_dk, *r_dp; // [S][T][L]
    // The rotor's keys (empty without one): for each level, class and moving mode m, the source
    // mode s(m), the mode m' with s(m') = m, and m's turn e^(2πi r/q) on 2^(−30) (the unit where the
    // key is zero, which carries the mode exactly).
    const int64_t *rotor; // [L][A][moving][4]
    // The pair contact's second drive b at each cell, its covector δb and max |δb| (each empty
    // under rectifying contacts), and the foil's bias covectors δb_a, δb_b (empty but under it).
    int32_t *second;           // [S][T][L][F]
    int64_t *db;               // [S][T][L][F]
    uint64_t *r_db;            // [S][T][L]
    int64_t *da_bias, *db_bias; // [S][T][L][F]
    // The strands (each empty without them): their resident table (`ResidentStrands`: the laws,
    // where each part begins, each ring's modulus, multiplier and faces, each byte's act, the
    // digits' turns, the keys, the classes' words and each ring's faces e^(2πi r/q) on 2^(−16));
    // each stream's residues (strand-major) and orientation before its first cell and after its
    // last; the faces the strands' level reads at each cell, and their max |s| at that level.
    const int32_t *strands;       // the table
    const uint32_t *strand_open;  // [S][3R + 1]
    uint32_t *strand_ends;        // [S][3R + 1]
    int32_t *strand_faces;        // [S][T][6R]
    uint64_t *r_strand;           // [S][T][L]
    // Participation (each empty without it, `participation`): the heads' starts; each cell's rotated
    // probe, key and current charts and the frame it was rotated by ([S][T][L][N][2]), its heads'
    // dissipation ([S][T][L][H]), the current y (re block, im block, [S][T][L][2N]), its ratio read
    // ([S][T][L][W]) and scale ([S][T][L]); each stream's running frame and met dissipation
    // ([S][L][N][2], [S][L][N]); one head's faces and weights at the cell being read ([S][T] each);
    // the reverse's ∂r̂ᵃ through its ratio ([S][T][L][W]) and the current's covector ([S][T][L][2N]),
    // the probe, key and current covectors of the level being returned ([S][T][N][2]), the chart
    // covectors turned forward by their frames ([S][T][L][6][N]) and the friction's ([S][L][H]);
    // the reaches of the ratio read, of y (re, im), of ∂r̂ᵃ ([S][T][L] each) and of the six chart
    // covectors ([6][S][T][L]).
    const uint32_t *pa_heads;     // [H + 1]
    int64_t *pa_probe, *pa_key, *pa_value, *pa_frame;
    int64_t *pa_diss;
    int64_t *pa_current;
    int32_t *pa_read;
    int64_t *pa_scale;
    int64_t *pa_run, *pa_met;
    int64_t *pa_z;
    uint64_t *pa_e;
    int64_t *pa_dra, *pa_gy;
    wide *pa_gq, *pa_gk, *pa_gw;
    int64_t *pa_gchart;
    wide *pa_gfric;
    uint64_t *r_pa_read, *r_pa_yre, *r_pa_yim, *r_pa_dra;
    uint64_t *r_pa_g;
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

// A class's code `−log₂(mass/total)` on `2^(−20)` bits (`face_code`): `p = mass 2^62 / total`, at
// least one grain, its whole part from its width and twenty binary digits of its mantissa's
// logarithm, each read by squaring the mantissa released at `2^(−62)` and halving it past two
// (`log2_face`). The opening's masses are checked `≤ total` before upload and the forward's own
// are, so `p ≤ 2^62`.
__device__ int64_t face_code(uint64_t mass, uwide total) {
    uwide p = ((uwide)mass << UNIT_BITS) / total;
    if (p == 0) {
        p = 1;
    }
    const uint64_t lo = (uint64_t)p;
    const int64_t width = 64 - __clzll((long long)lo);
    const int64_t whole = width - 1 - UNIT_BITS;
    uwide mantissa = (uwide)lo << (uint32_t)(UNIT_BITS + 1 - width);
    int64_t fraction = 0;
    for (uint32_t i = 0; i < READ_BITS; i++) {
        mantissa = (mantissa * mantissa) >> UNIT_BITS;
        fraction <<= 1;
        if (mantissa >= ((uwide)2 << UNIT_BITS)) {
            fraction |= 1;
            mantissa >>= 1;
        }
    }
    return -(whole * ((int64_t)1 << READ_BITS) + fraction);
}

// `e^(iπ s)` on `2^(−30)` for a turn `s` in half turns on `2^(−16)` (`turn_face`): `s` read
// modulo the full turn and composed from the ladder's dyadic turns, its binary digits from the
// half turn down.
__device__ void turn_face(int64_t s, const TowerLaw &law, wide *re, wide *im) {
    const int64_t full = (int64_t)1 << (TURN_BITS + 1);
    int64_t m = s % full;
    const uint64_t j = (uint64_t)(m < 0 ? m + full : m);
    wide vr = (wide)1 << MOVE_BITS, vi = 0;
    for (uint32_t i = 0; i < TOWER_LADDER; i++) {
        if (j & ((uint64_t)1 << (TURN_BITS - i))) {
            const wide cr = law.ladder[i][0], ci = law.ladder[i][1];
            const wide nr = rel(vr * cr - vi * ci, MOVE_BITS);
            vi = rel(vr * ci + vi * cr, MOVE_BITS);
            vr = nr;
        }
    }
    *re = vr;
    *im = vi;
}

// -------------------------------------------------------------------------------------------
// the ring face's wide law (`holonics::hnn::tower::RingFace`): its checked products and its
// products released through 256 bits, where the host widens to a big integer

__device__ __forceinline__ uwide mag128(wide x) {
    return x < 0 ? (uwide)0 - (uwide)x : (uwide)x;
}

struct u256 {
    uwide lo, hi;
};

// `a b` over 256 bits.
__device__ __forceinline__ u256 mul_u128(uwide a, uwide b) {
    const uint64_t a0 = (uint64_t)a, a1 = (uint64_t)(a >> 64), b0 = (uint64_t)b, b1 = (uint64_t)(b >> 64);
    const uwide p00 = (uwide)a0 * b0, p01 = (uwide)a0 * b1, p10 = (uwide)a1 * b0, p11 = (uwide)a1 * b1;
    const uwide mid = (p00 >> 64) + (uint64_t)p01 + (uint64_t)p10;
    u256 r;
    r.lo = (mid << 64) | (uint64_t)p00;
    r.hi = p11 + (p01 >> 64) + (p10 >> 64) + (mid >> 64);
    return r;
}

// `x y` where it lies in 128 bits (`checked_mul`), the refusal otherwise.
__device__ wide mul_checked(wide x, wide y, uint32_t *st) {
    const u256 p = mul_u128(mag128(x), mag128(y));
    const bool neg = (x < 0) != (y < 0);
    const uwide limit = ((uwide)1 << 127) - (neg ? 0 : 1);
    if (p.hi != 0 || p.lo > limit) {
        atomicOr(st, TOWER_REFUSED_CARRIER);
        return 0;
    }
    return neg ? (wide)((uwide)0 - p.lo) : (wide)p.lo;
}

// `x + y` and `x − y` where they lie in 128 bits (`checked_add`, `checked_sub`).
__device__ wide add_checked(wide x, wide y, uint32_t *st) {
    const wide r = (wide)((uwide)x + (uwide)y);
    if ((x >= 0) == (y >= 0) && (r >= 0) != (x >= 0)) {
        atomicOr(st, TOWER_REFUSED_CARRIER);
        return 0;
    }
    return r;
}

__device__ wide sub_checked(wide x, wide y, uint32_t *st) {
    const wide r = (wide)((uwide)x - (uwide)y);
    if ((x >= 0) != (y >= 0) && (r >= 0) != (x >= 0)) {
        atomicOr(st, TOWER_REFUSED_CARRIER);
        return 0;
    }
    return r;
}

// `x y` released by `bits`, half away from zero, exactly (`wide_release`): through 128 bits where
// the product lies there, through 256 otherwise, refused where the released value leaves 128 bits.
__device__ wide release_product(wide x, wide y, unsigned bits, uint32_t *st) {
    u256 p = mul_u128(mag128(x), mag128(y));
    const bool neg = (x < 0) != (y < 0);
    const bool narrow = p.hi == 0 && p.lo <= ((uwide)1 << 127) - (neg ? 0 : 1);
    if (bits > 0 && bits <= 256) {
        // add the half, 2^(bits − 1), with its carry
        if (bits - 1 < 128) {
            const uwide half = (uwide)1 << (bits - 1);
            const uwide lo = p.lo + half;
            p.hi += lo < p.lo ? 1 : 0;
            p.lo = lo;
        } else {
            p.hi += (uwide)1 << (bits - 1 - 128);
        }
        if (bits < 128) {
            p.lo = (p.lo >> bits) | (p.hi << (128 - bits));
            p.hi >>= bits;
        } else if (bits == 128) {
            p.lo = p.hi;
            p.hi = 0;
        } else {
            p.lo = bits - 128 < 128 ? p.hi >> (bits - 128) : 0;
            p.hi = 0;
        }
    } else if (bits > 256) {
        p.lo = 0;
        p.hi = 0;
    }
    const uwide limit = ((uwide)1 << 127) - (narrow && neg ? 0 : 1);
    if (p.hi != 0 || p.lo > limit) {
        atomicOr(st, TOWER_REFUSED_CARRIER);
        return 0;
    }
    return neg ? (wide)((uwide)0 - p.lo) : (wide)p.lo;
}

// The ring carried by one move `h ↦ λh + βh̄`, `m = [Re λ, Im λ, Re β, Im β]` on 2^(−30)
// (`ring_carry`), and its adjoint (`ring_carry_adjoint`).
__device__ __forceinline__ void ring_carry(const wide *m, wide re, wide im, wide *out) {
    out[0] = rel((m[0] + m[2]) * re + (m[3] - m[1]) * im, MOVE_BITS);
    out[1] = rel((m[1] + m[3]) * re + (m[0] - m[2]) * im, MOVE_BITS);
}

__device__ __forceinline__ void ring_carry_adjoint(const wide *m, wide gx, wide gy, wide *out) {
    out[0] = rel((m[0] + m[2]) * gx + (m[1] + m[3]) * gy, MOVE_BITS);
    out[1] = rel((m[3] - m[1]) * gx + (m[0] - m[2]) * gy, MOVE_BITS);
}

// The ring's hand after a move (`hand_after`): kept where |λ| > |β|, reversed where below, and
// the given hand restarted where they are equal.
__device__ __forceinline__ bool hand_after(const wide *m, bool hand) {
    const wide l = m[0] * m[0] + m[1] * m[1], b = m[2] * m[2] + m[3] * m[3];
    return l > b ? hand : l < b ? !hand : false;
}

// `r / ‖r‖_rms` on 2^(−16) and `‖r‖_rms` of a rank's read `(re, im)` (`ratio_to_power`), then its
// harmonics `q_h = q_(h−1) ρ / |ρ|` (`harmonics_of`), `2H` words into `q`. Returns the scale.
__device__ int64_t ring_face(int64_t re, int64_t im, uint32_t harmonics, int32_t *q, uint32_t *st) {
    const wide power = (wide)re * re + (wide)im * im;
    const wide scale = (wide)isqrt128((uwide)(power / 2));
    if (scale == 0) {
        for (uint32_t i = 0; i < 2 * harmonics; i++) {
            q[i] = 0;
        }
        return 0;
    }
    const wide r0 = fit32(div_nearest((wide)re << FACE_BITS, scale), st);
    const wide r1 = fit32(div_nearest((wide)im << FACE_BITS, scale), st);
    q[0] = (int32_t)r0;
    q[1] = (int32_t)r1;
    const wide modulus = (wide)isqrt128((uwide)(r0 * r0 + r1 * r1));
    wide x = r0, y = r1;
    for (uint32_t h = 1; h < harmonics; h++) {
        if (modulus == 0) {
            q[2 * h] = 0;
            q[2 * h + 1] = 0;
            continue;
        }
        const wide nx = div_nearest(x * r0 - y * r1, modulus);
        const wide ny = div_nearest(x * r1 + y * r0, modulus);
        x = nx;
        y = ny;
        q[2 * h] = fit32(x, st);
        q[2 * h + 1] = fit32(y, st);
    }
    return fit64(scale, st);
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
    const uint32_t FAMS = 3 + law.turned + 2 * law.pumped;
    int64_t *pq = (int64_t *)carve(at, 8ull * FAMS * N);
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
    int32_t *pc = (int32_t *)carve(at, 4ull * law.forms);
    const uint32_t K = law.forms;
    // The ring face: each rank's ring and hand, the carried face it pushes from, the face ρ with
    // its harmonics, the top's ratio and the pair read φ.
    const uint32_t R = law.ring_ranks, H = law.ring_harmonics, K2 = 2 * R * H, KP = (W + 1) * K2;
    wide *rg = (wide *)carve(at, sizeof(wide) * 2 * R);
    uint32_t *hd = (uint32_t *)carve(at, 4ull * R);
    int64_t *rs = (int64_t *)carve(at, 8ull * 2 * N * (R > 0));
    int32_t *rho = (int32_t *)carve(at, 4ull * K2);
    int32_t *hat = (int32_t *)carve(at, 4ull * W * (R > 0));
    int32_t *phi = (int32_t *)carve(at, 4ull * KP);
    // The rotor's stepped and turned state h' of the level's moving modes.
    int64_t *hs = (int64_t *)carve(at, 8ull * 2 * law.moving);
    // The strands' residues (strand-major) and the faces their level reads.
    const uint32_t SR = law.strand_rings;
    uint32_t *sr = (uint32_t *)carve(at, 4ull * 3 * SR);
    int32_t *sp = (int32_t *)carve(at, 4ull * 6 * SR);
    // Participation: each mode's unit and log₂ ρ at the cell, the charts, the frame, the rotated
    // probe, the current y (re block, im block), its raw read and ratio read, the heads' dissipation.
    const uint32_t P = law.participation != 0, HH = law.pa_heads;
    int64_t *pu = (int64_t *)carve(at, 8ull * 2 * N * P);
    int64_t *pl = (int64_t *)carve(at, 8ull * N * P);
    int64_t *pcs = (int64_t *)carve(at, 8ull * 6 * N * P);
    int64_t *pfr = (int64_t *)carve(at, 8ull * 2 * N * P);
    int64_t *ppr = (int64_t *)carve(at, 8ull * 2 * N * P);
    int64_t *py = (int64_t *)carve(at, 8ull * 2 * N * P);
    int64_t *praw = (int64_t *)carve(at, 8ull * W * P);
    int32_t *prd = (int32_t *)carve(at, 4ull * W * P);
    int64_t *pdis = (int64_t *)carve(at, 8ull * HH * P);
    __shared__ uint32_t st;
    __shared__ int64_t scale_s;
    __shared__ wide ring_lam[4];
    // The news clock: the open face (its masses in `ms`, its total, whether there is one), the
    // clock's phase, and each level's ticks at the arriving class.
    __shared__ uwide news_total;
    __shared__ uint64_t news_phase;
    __shared__ uint32_t news_has;
    __shared__ uint32_t tk[TOWER_MAX_LEVELS];
    if (tid == 0) {
        st = 0;
        for (uint32_t l = 0; l < TOWER_MAX_LEVELS; l++) {
            tk[l] = 1;
        }
        news_has = 0;
        news_total = 0;
        news_phase = 0;
        if (law.news) {
            const uint64_t *open = fr.news_open + (uint64_t)s * (A + 4);
            news_has = open[0] != 0;
            news_total = (uwide)open[1] | ((uwide)open[2] << 64);
            news_phase = open[3];
        }
    }
    if (law.news) {
        for (uint32_t c = tid; c < A; c += B) {
            ms[c] = fr.news_open[(uint64_t)s * (A + 4) + 4 + c];
        }
    }
    for (uint32_t i = tid; i < L * 2 * N; i += B) {
        h[i] = fr.opening[(uint64_t)s * L * 2 * N + i];
    }
    for (uint32_t r = tid; r < R; r += B) {
        rg[2 * r] = fr.ring_open[((uint64_t)s * R + r) * 2];
        rg[2 * r + 1] = fr.ring_open[((uint64_t)s * R + r) * 2 + 1];
        hd[r] = fr.hands_open[(uint64_t)s * R + r];
    }
    // Each thread carries the strands' orientation alike; ring k's residues are thread k's.
    const int32_t *tb = fr.strands;
    bool reversed = SR > 0 && fr.strand_open[(uint64_t)s * (3 * SR + 1) + 3 * SR] != 0;
    for (uint32_t k = tid; k < SR; k += B) {
        for (uint32_t j = 0; j < 3; j++) {
            sr[j * SR + k] = fr.strand_open[(uint64_t)s * (3 * SR + 1) + j * SR + k];
        }
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
        // The news clock: the arrival's code under the open face (none at rest) advances the
        // phase, and each level above 0 ticks by the sections the running news crosses
        // (`NewsClock::ticks`).
        if (law.news) {
            if (tid == 0) {
                uint64_t code = 0;
                if (news_has) {
                    if (news_total == 0) {
                        atomicOr(&st, TOWER_REFUSED_NEWS);
                    } else {
                        const int64_t c = face_code(ms[u], news_total);
                        if (c < 0) {
                            atomicOr(&st, TOWER_REFUSED_NEWS);
                        } else {
                            code = (uint64_t)c;
                        }
                    }
                }
                const uint64_t sum = news_phase + code;
                if (sum < code || news_phase >= law.period) {
                    atomicOr(&st, TOWER_REFUSED_NEWS);
                }
                for (uint32_t l = 1; l < L && l < TOWER_MAX_LEVELS; l++) {
                    const uint64_t section = law.sections[l];
                    const uint64_t advanced = section == 0 ? 0 : sum / section - news_phase / section;
                    if (section == 0 || advanced > UINT32_MAX) {
                        atomicOr(&st, TOWER_REFUSED_NEWS);
                    }
                    tk[l] = advanced > UINT32_MAX ? 0 : (uint32_t)advanced;
                }
                news_phase = law.period == 0 ? 0 : sum % law.period;
                if (keep) {
                    for (uint32_t l = 0; l < L; l++) {
                        fr.ticks[qc * L + l] = tk[l];
                    }
                }
            }
            __syncthreads();
        }
        for (uint32_t j = tid; j < W; j += B) {
            x[j] = th[law.encoding + (uint64_t)u * W + j];
        }
        // The seam: the class before this one, the start A at rest (what the pair face and the
        // ring's founded pair moves read beside the class arriving).
        uint32_t prev = A;
        if (K > 0 || R > 0) {
            prev = t == 0 ? fr.previous[s] : fr.classes[(uint64_t)s * (T + 1) + t - 1];
            if (prev > A) {
                if (tid == 0) {
                    atomicOr(&st, TOWER_REFUSED_CLASS);
                }
                prev = A;
            }
        }
        // The pair face read at (the class before, the class arriving): c(p), lifted into the
        // encoding, x⁰ = E(u) + P c(p) on 2^(−40) released to the face's 2^(−16).
        uint64_t pmax = 0;
        if (K > 0) {
            for (uint32_t v = tid; v < K; v += B) {
                pc[v] = fr.pair_values[((uint64_t)prev * A + u) * K + v];
            }
            __syncthreads();
            uint64_t mp = 0;
            for (uint32_t v = tid; v < K; v += B) {
                const uint64_t a = magnitude(pc[v]);
                mp = a > mp ? a : mp;
            }
            pmax = block_max(mp, red);
            const bool n_lift = narrow_terms(law.pair_reach[1], pmax, K, &st);
            for (uint32_t j = tid; j < W; j += B) {
                const int64_t lift = fit64(rel(dot(th + law.pair_lift + (uint64_t)j * K, 1, K, pc, n_lift), MATERIAL_BITS), &st);
                x[j] = fit32((wide)x[j] + (wide)lift, &st);
            }
            if (keep) {
                for (uint32_t v = tid; v < K; v += B) {
                    fr.pair[qc * K + v] = pc[v];
                }
                if (tid == 0) {
                    fr.r_pair[qc] = pmax;
                }
            }
        }
        __syncthreads();
        // The strands hear the arriving word, each byte in turn (`Strands::hear_byte`), one thread
        // a ring: a located digit steps and turns each strand by its law, a located key transfers,
        // reflects or clears each strand and sets the orientation, any other byte moves nothing.
        // Their faces e^(2πi r/q) are then read off the rings' resident faces.
        uint64_t smax = 0;
        if (SR > 0) {
            const uint32_t from = (uint32_t)tb[tb[6] + u], to = (uint32_t)tb[tb[6] + u + 1];
            for (uint32_t b = from; b < to; b++) {
                const int32_t act = tb[tb[3] + tb[tb[7] + b]];
                if (act > 0) {
                    const int32_t *turns = tb + tb[4] + (uint64_t)(act - 1) * SR;
                    for (uint32_t k = tid; k < SR; k += B) {
                        const uint64_t q = (uint64_t)tb[8 + 3 * k], mu = (uint64_t)tb[8 + 3 * k + 1];
                        const uint64_t theta = (uint64_t)turns[k] % q;
                        const uint64_t turn = reversed ? (q - theta) % q : theta;
                        for (uint32_t j = 0; j < 3; j++) {
                            const uint32_t at_law = (uint32_t)tb[j];
                            const uint64_t r = sr[j * SR + k];
                            if (at_law == 0) {
                                sr[j * SR + k] = (uint32_t)((r * mu % q + turn) % q);
                            } else if (at_law == 1) {
                                sr[j * SR + k] = (uint32_t)(r * mu % q);
                            }
                        }
                    }
                } else if (act < 0) {
                    const int32_t *key = tb + tb[5] + (uint64_t)(-act - 1) * 4;
                    for (uint32_t k = tid; k < SR; k += B) {
                        const uint32_t q = (uint32_t)tb[8 + 3 * k];
                        const uint32_t old[3] = {sr[k], sr[SR + k], sr[2 * SR + k]};
                        for (uint32_t j = 0; j < 3; j++) {
                            const int32_t v = key[j];
                            sr[j * SR + k] = v == 0 ? 0 : v > 0 ? old[v - 1] : (q - old[-v - 1] % q) % q;
                        }
                    }
                    reversed = key[3] == 0 ? reversed : key[3] == 1 ? !reversed : key[3] == 3;
                }
            }
            uint64_t ms_ = 0;
            for (uint32_t k = tid; k < SR; k += B) {
                for (uint32_t j = 0; j < 3; j++) {
                    const int32_t *face = tb + tb[8 + 3 * k + 2] + 2 * (uint64_t)sr[j * SR + k];
                    const uint64_t at_part = 2 * ((uint64_t)j * SR + k);
                    sp[at_part] = face[0];
                    sp[at_part + 1] = face[1];
                    const uint64_t a = magnitude(face[0]), c = magnitude(face[1]);
                    ms_ = a > ms_ ? a : ms_;
                    ms_ = c > ms_ ? c : ms_;
                }
            }
            smax = block_max(ms_, red);
            if (keep) {
                for (uint32_t i = tid; i < 6 * SR; i += B) {
                    fr.strand_faces[qc * 6 * SR + i] = sp[i];
                }
            }
        }
        uint64_t m = 0;
        for (uint32_t j = tid; j < W; j += B) {
            const uint64_t v = magnitude(x[j]);
            m = v > m ? v : m;
        }
        uint64_t xmax = block_max(m, red);
        for (uint32_t l = 0; l < L; l++) {
            const TowerLevel &lv = law.level[l];
            const uint64_t q = qc * L + l;
            const bool ringed = R > 0 && l == law.ring_level;
            // The ring's carried face before the move, each mode's (re, im) on 2^(−16)
            // (`carried_face`).
            if (ringed) {
                for (uint32_t i = tid; i < 2 * N; i += B) {
                    rs[i] = fit64(rel(h[l * 2 * N + i], STATE_BITS - FACE_BITS), &st);
                }
            }
            // The pushes on 2^(−40) released to the state's 2^(−24), and the gate's logit.
            const bool n_re = narrow_terms(lv.reach[0], xmax, W, &st);
            const bool n_im = narrow_terms(lv.reach[1], xmax, W, &st);
            const bool n_gate = narrow_terms(lv.reach[6], xmax, W, &st);
            const bool n_turn = law.turned && narrow_terms(lv.reach[7], xmax, W, &st);
            const bool n_depth = law.pumped && narrow_terms(lv.reach[8], xmax, W, &st);
            const bool n_axis = law.pumped && narrow_terms(lv.reach[9], xmax, W, &st);
            // A turned level's arriving turn s_t = 2^(−spread) (W_φ x + b_φ), in half turns on
            // 2^(−16), beside the gate's logit; a pumped level's depth logit W_κ x + b_κ on
            // 2^(−16) and its axis p_t = 2^(−spread) (W_ψ x + b_ψ) in half turns on 2^(−16).
            for (uint32_t o = tid; o < FAMS * N; o += B) {
                const uint32_t fam = o / N, k = o % N;
                if (fam == 2) {
                    wide sum = dot(tt + lv.gate + k, N, W, x, n_gate);
                    sum += (wide)th[lv.gate_bias + k] << MATERIAL_BITS;
                    pq[o] = fit64(rel(sum, MATERIAL_BITS), &st);
                } else if (fam == 4) {
                    wide sum = dot(tt + lv.pump + k, N, W, x, n_depth);
                    sum += (wide)th[lv.pump_bias + k] << MATERIAL_BITS;
                    pq[o] = fit64(rel(sum, MATERIAL_BITS), &st);
                } else if (fam == 3 || fam == 5) {
                    const bool axis = fam == 5;
                    wide sum = dot(tt + (axis ? lv.pump_axis : lv.turn) + k, N, W, x, axis ? n_axis : n_turn);
                    sum += (wide)th[(axis ? lv.pump_axis_bias : lv.turn_bias) + k] << MATERIAL_BITS;
                    const int64_t turn = fit64(rel(sum, MATERIAL_BITS), &st);
                    pq[o] = fit64(rel((wide)turn, law.turn_spread), &st);
                } else {
                    const wide sum = dot(tt + (fam == 0 ? lv.push_re : lv.push_im) + k, N, W, x, fam == 0 ? n_re : n_im);
                    pq[o] = fit64(rel(sum, MATERIAL_BITS + FACE_BITS - STATE_BITS), &st);
                }
            }
            __syncthreads();
            // The rotor's step and turn h' = T P^σ h before the move (`Rotor::moved`): moving mode m
            // takes mode s(m) of the state as it stood, turned by its key's face.
            if (law.moving) {
                const int64_t *keys = fr.rotor + ((uint64_t)l * A + u) * law.moving * 4;
                for (uint32_t m = tid; m < law.moving; m += B) {
                    const int64_t *key = keys + m * 4;
                    const wide x = h[(l * N + (uint32_t)key[0]) * 2], y = h[(l * N + (uint32_t)key[0]) * 2 + 1];
                    hs[2 * m] = fit64(rel(key[2] * x - key[3] * y, MOVE_BITS), &st);
                    hs[2 * m + 1] = fit64(rel(key[2] * y + key[3] * x, MOVE_BITS), &st);
                }
                __syncthreads();
            }
            // The gated move λ_t = |λ|^(c r) u, held at the margin (its unit turned by e^(iπ s_t)
            // when the level is turned), and the state h = λ_t h + γ_t B x (on h' under a rotor).
            for (uint32_t k = tid; k < N; k += B) {
                const int64_t *gf = fr.gates + ((uint64_t)l * N + k) * 4;
                const wide open = logistic(pq[2 * N + k], face_roots, law.face_digits);
                const wide exponent = rel((wide)GATE_REACH * open * gf[3], MOVE_BITS);
                wide rho = rel((wide)below_one(exponent, move_roots, law.move_digits), UNIT_BITS - MOVE_BITS);
                const bool held = rho > radius;
                if (held) {
                    rho = radius;
                }
                wide ur = gf[0], ui = gf[1];
                if (law.turned) {
                    wide tr, ti;
                    turn_face(pq[3 * N + k], law, &tr, &ti);
                    const wide nr = rel(ur * tr - ui * ti, MOVE_BITS);
                    ui = rel(ur * ti + ui * tr, MOVE_BITS);
                    ur = nr;
                }
                if (P) {
                    pu[2 * k] = (int64_t)ur;
                    pu[2 * k + 1] = (int64_t)ui;
                    pl[k] = held ? law.pa_held_log : fit64(rel(exponent, MOVE_BITS - FACE_BITS), &st);
                }
                wide lr = rel(rho * ur, MOVE_BITS);
                wide li = rel(rho * ui, MOVE_BITS);
                wide gap = ((wide)1 << (2 * MOVE_BITS)) - (lr * lr + li * li);
                gap = gap < 0 ? 0 : gap;
                uint64_t gamma = isqrt64((uint64_t)gap);
                if (gamma == 0) {
                    atomicOr(&st, TOWER_REFUSED_UNIT);
                    gamma = 1;
                }
                // A pumped mode's turn α_t = ρ_t (1 − |κ|) U_t and pump β_t = ρ_t κ P_t: |α| + |β|
                // = ρ_t, so γ_t is kept.
                wide pump_open = 0, kappa = 0, axr = 0, axi = 0, br = 0, bi = 0;
                if (law.pumped) {
                    const wide one = (wide)1 << MOVE_BITS;
                    pump_open = logistic(pq[4 * N + k], face_roots, law.face_digits);
                    kappa = 2 * pump_open - one;
                    turn_face(pq[5 * N + k], law, &axr, &axi);
                    const wide keep_ = one - (kappa < 0 ? -kappa : kappa);
                    const wide depth = rel(rho * kappa, MOVE_BITS);
                    const wide ar = rel(keep_ * lr, MOVE_BITS);
                    li = rel(keep_ * li, MOVE_BITS);
                    lr = ar;
                    br = rel(depth * axr, MOVE_BITS);
                    bi = rel(depth * axi, MOVE_BITS);
                }
                // The step h ← λ_t h + γ_t P x_t (h ← α_t h + β_t conj(h) + γ_t P x_t when
                // pumped) acts once a tick of the level's clock (once without a news clock), the
                // arrival held through its ticks; an arrival that ticks no time moves nothing.
                const wide pr = rel((wide)gamma * pq[k], MOVE_BITS);
                const wide pi = rel((wide)gamma * pq[N + k], MOVE_BITS);
                wide hr = h[(l * N + k) * 2], hi = h[(l * N + k) * 2 + 1];
                if (k < law.moving) {
                    hr = hs[2 * k];
                    hi = hs[2 * k + 1];
                }
                for (uint32_t j = 0; j < tk[l]; j++) {
                    const wide ar = rel(lr * hr - li * hi + br * hr + bi * hi, MOVE_BITS);
                    hi = fit64(rel(lr * hi + li * hr + bi * hr - br * hi, MOVE_BITS) + pi, &st);
                    hr = fit64(ar + pr, &st);
                }
                const int64_t nr = (int64_t)hr;
                const int64_t ni = (int64_t)hi;
                h[(l * N + k) * 2] = nr;
                h[(l * N + k) * 2 + 1] = ni;
                if (ringed && k == law.ring_mode) {
                    ring_lam[0] = lr;
                    ring_lam[1] = li;
                    ring_lam[2] = br;
                    ring_lam[3] = bi;
                }
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
                    if (law.turned) {
                        fr.units[(q * N + k) * 2] = (int64_t)ur;
                        fr.units[(q * N + k) * 2 + 1] = (int64_t)ui;
                    }
                    if (law.pumped) {
                        int64_t *pm = fr.pumps + (q * N + k) * 6;
                        pm[0] = (int64_t)pump_open;
                        pm[1] = (int64_t)kappa;
                        pm[2] = (int64_t)axr;
                        pm[3] = (int64_t)axi;
                        pm[4] = (int64_t)br;
                        pm[5] = (int64_t)bi;
                    }
                }
            }
            __syncthreads();
            // The ring rides its mode's move at this cell (its founded pair move where it has
            // one), pushed from the face it carried before (`RingFace::advance`), each rank by one
            // thread; then its face, a ratio to its own power with its harmonics (`RingFace::face`).
            if (ringed) {
                const uint32_t dims = 2 * N, hatn = W + 1, RM = 6 * N + 2 * W + 3;
                for (uint32_t r = tid; r < R; r += B) {
                    const int32_t *fac = th + law.ring_factors + (uint64_t)r * RM;
                    const uint32_t *sh = fr.ring_shifts + 5 * r;
                    wide sa0 = 0, sa1 = 0, sg = 0, sb0 = 0, sb1 = 0;
                    for (uint32_t j = 0; j < dims; j++) {
                        sa0 += (wide)fac[j] * rs[j];
                        sa1 += (wide)fac[dims + j] * rs[j];
                        sg += (wide)fac[2 * dims + 2 * hatn + j] * rs[j];
                    }
                    sg += (wide)fac[2 * dims + 2 * hatn + dims] << FACE_BITS;
                    for (uint32_t j = 0; j < W; j++) {
                        const wide e = fr.ring_opening[(uint64_t)u * W + j];
                        sb0 += (wide)fac[2 * dims + j] * e;
                        sb1 += (wide)fac[2 * dims + hatn + j] * e;
                    }
                    sb0 += (wide)fac[2 * dims + W] << FACE_BITS;
                    sb1 += (wide)fac[2 * dims + hatn + W] << FACE_BITS;
                    const wide a0 = rel(sa0, sh[0]), a1 = rel(sa1, sh[0]);
                    const wide b0 = rel(sb0, sh[1]), b1 = rel(sb1, sh[1]);
                    const wide gamma = rel(sg, sh[2]);
                    // the push v = αβγ, released by the push shift
                    const wide pre = sub_checked(mul_checked(a0, b0, &st), mul_checked(a1, b1, &st), &st);
                    const wide pim = add_checked(mul_checked(a0, b1, &st), mul_checked(a1, b0, &st), &st);
                    const wide vre = rel(mul_checked(pre, gamma, &st), sh[3]);
                    const wide vim = rel(mul_checked(pim, gamma, &st), sh[3]);
                    // the move: the rank's founded pair move at (prev, u), or the mode's
                    wide m[4] = {ring_lam[0], ring_lam[1], ring_lam[2], ring_lam[3]};
                    bool founded = false;
                    uint32_t lo = fr.ring_index[r], hi = fr.ring_index[r + 1];
                    while (lo < hi) {
                        const uint32_t mid = lo + (hi - lo) / 2;
                        const int64_t *row = fr.ring_table + 6ull * mid;
                        const uint64_t key = ((uint64_t)row[0] << 32) | (uint64_t)row[1];
                        const uint64_t want = ((uint64_t)prev << 32) | (uint64_t)u;
                        if (key == want) {
                            m[0] = row[2];
                            m[1] = row[3];
                            m[2] = row[4];
                            m[3] = row[5];
                            founded = true;
                            break;
                        }
                        if (key < want) {
                            lo = mid + 1;
                        } else {
                            hi = mid;
                        }
                    }
                    wide carried[2];
                    ring_carry(m, rg[2 * r], rg[2 * r + 1], carried);
                    wide hre = carried[0] + vre, him = carried[1] + vim;
                    const bool read_hand = hand_after(m, hd[r] != 0);
                    const int64_t qre = fit64(rel(hre, sh[4]), &st);
                    const int64_t qim = fit64(rel(him, sh[4]), &st);
                    const bool rebased = read_hand && fr.ring_restarts[r] == (int32_t)u;
                    if (rebased) {
                        him = -him;
                    }
                    rg[2 * r] = hre;
                    rg[2 * r + 1] = him;
                    hd[r] = read_hand && !rebased ? 1 : 0;
                    const int64_t scale = ring_face(qre, read_hand ? -qim : qim, H, rho + 2 * H * r, &st);
                    if (keep) {
                        const uint64_t qr = qc * R + r;
                        fr.ring_after[qr * 2] = hre;
                        fr.ring_after[qr * 2 + 1] = him;
                        wide *fa = fr.ring_factor + qr * 5;
                        fa[0] = a0;
                        fa[1] = a1;
                        fa[2] = b0;
                        fa[3] = b1;
                        fa[4] = gamma;
                        for (uint32_t i = 0; i < 4; i++) {
                            fr.ring_move[qr * 4 + i] = (int64_t)m[i];
                        }
                        fr.ring_hand[qr] = (read_hand ? 1u : 0u) | (rebased ? 2u : 0u) | (founded ? 4u : 0u);
                        fr.ring_scale[qr] = scale;
                        for (uint32_t i = 0; i < 2 * H; i++) {
                            fr.ring_rho[qc * K2 + 2 * H * r + i] = rho[2 * H * r + i];
                        }
                    }
                }
            }
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
            // Participation (`Tower::step`, `participation`): the cell's move advances each mode's
            // frame and met dissipation (from rest at the section's opening), the level's input
            // presents its rotated charts as the section's newest site and probes every admitted
            // site head by head (the Gibbs face of the pairing less the friction, carried as the
            // integer (mass, current) pair), and the current is read like the modes' face, its ratio
            // read offered to the contacts through W₁ᵃ.
            uint64_t prmax = 0;
            if (P) {
                for (uint32_t o = tid; o < 6 * N; o += B) {
                    const uint32_t fam = o / N, k = o % N;
                    const bool nar = narrow_terms(lv.pa_reach[fam], xmax, W, &st);
                    pcs[o] = fit64(rel(dot(tt + lv.pa[fam] + k, N, W, x, nar), MATERIAL_BITS), &st);
                }
                __syncthreads();
                for (uint32_t k = tid; k < N; k += B) {
                    int64_t *run = fr.pa_run + (((uint64_t)s * L + l) * N + k) * 2;
                    int64_t *met = fr.pa_met + ((uint64_t)s * L + l) * N + k;
                    const wide fre_ = t == 0 ? ((wide)1 << MOVE_BITS) : (wide)run[0];
                    const wide fim_ = t == 0 ? 0 : (wide)run[1];
                    const int64_t mt = (t == 0 ? 0 : *met) - pl[k];
                    const wide ur = pu[2 * k], ui = pu[2 * k + 1];
                    const int64_t nr = fit64(rel(fre_ * ur - fim_ * ui, MOVE_BITS), &st);
                    const int64_t ni = fit64(rel(fre_ * ui + fim_ * ur, MOVE_BITS), &st);
                    run[0] = nr;
                    run[1] = ni;
                    *met = mt;
                    pfr[2 * k] = nr;
                    pfr[2 * k + 1] = ni;
                    fr.pa_frame[(q * N + k) * 2] = nr;
                    fr.pa_frame[(q * N + k) * 2 + 1] = ni;
                    for (uint32_t c = 0; c < 3; c++) {
                        const wide cr = pcs[(2 * c) * N + k], ci = pcs[(2 * c + 1) * N + k];
                        const int64_t rr = fit64(rel((wide)nr * cr + (wide)ni * ci, MOVE_BITS), &st);
                        const int64_t ri = fit64(rel((wide)nr * ci - (wide)ni * cr, MOVE_BITS), &st);
                        if (c == 0) {
                            ppr[2 * k] = rr;
                            ppr[2 * k + 1] = ri;
                        } else {
                            int64_t *dst = (c == 1 ? fr.pa_key : fr.pa_value) + (q * N + k) * 2;
                            dst[0] = rr;
                            dst[1] = ri;
                        }
                    }
                }
                __syncthreads();
                for (uint32_t hh = tid; hh < HH; hh += B) {
                    const uint32_t from = fr.pa_heads[hh], to = fr.pa_heads[hh + 1];
                    wide sum = 0;
                    for (uint32_t k = from; k < to; k++) {
                        sum += fr.pa_met[((uint64_t)s * L + l) * N + k];
                    }
                    const int64_t dis = fit64(div_nearest(sum, (wide)(to - from)), &st);
                    pdis[hh] = dis;
                    fr.pa_diss[q * HH + hh] = dis;
                }
                __syncthreads();
                const uint64_t site0 = (uint64_t)s * T;
                for (uint32_t hh = 0; hh < HH; hh++) {
                    const uint32_t from = fr.pa_heads[hh], to = fr.pa_heads[hh + 1];
                    const wide friction = th[lv.pa[9] + hh];
                    int64_t zm = INT64_MIN;
                    for (uint32_t j = tid; j <= t; j += B) {
                        const uint64_t qj = (site0 + j) * L + l;
                        wide pairing = 0;
                        for (uint32_t k = from; k < to; k++) {
                            const int64_t *kj = fr.pa_key + (qj * N + k) * 2;
                            pairing += (wide)ppr[2 * k] * kj[0] + (wide)ppr[2 * k + 1] * kj[1];
                        }
                        const wide met = (wide)pdis[hh] - (wide)fr.pa_diss[qj * HH + hh];
                        const int64_t z = fit64(rel(pairing, FACE_BITS + law.pa_beta) - rel(friction * met, FACE_BITS), &st);
                        fr.pa_z[site0 + j] = z;
                        zm = z > zm ? z : zm;
                    }
                    const int64_t peak = block_max_signed(zm, red);
                    uwide msum = 0;
                    for (uint32_t j = tid; j <= t; j += B) {
                        const int64_t z = fr.pa_z[site0 + j];
                        const uint64_t e = (wide)peak - (wide)z >= ((wide)UNIT_BITS << FACE_BITS) ? 0 : below_one((wide)z - (wide)peak, face_roots, law.face_digits);
                        fr.pa_e[site0 + j] = e;
                        msum += e;
                    }
                    const uwide mass = block_sum(msum, redw);
                    __syncthreads();
                    for (uint32_t k = from + tid; k < to; k += B) {
                        wide jr = 0, ji = 0;
                        for (uint32_t j = 0; j <= t; j++) {
                            const uint64_t qj = (site0 + j) * L + l;
                            const wide e = (wide)fr.pa_e[site0 + j];
                            jr += e * fr.pa_value[(qj * N + k) * 2];
                            ji += e * fr.pa_value[(qj * N + k) * 2 + 1];
                        }
                        const wide mr = fit64(div_nearest(jr, (wide)mass), &st), mi = fit64(div_nearest(ji, (wide)mass), &st);
                        const wide ur = pfr[2 * k], ui = pfr[2 * k + 1];
                        py[k] = fit64(rel(ur * mr - ui * mi, MOVE_BITS), &st);
                        py[N + k] = fit64(rel(ur * mi + ui * mr, MOVE_BITS), &st);
                    }
                    __syncthreads();
                }
                // Re(Cᵃ y) = Cᵃ_re y_re − Cᵃ_im y_im on 2^(−40), released to 2^(−16), read as a ratio.
                uint64_t mya = 0, myb = 0;
                for (uint32_t k = tid; k < N; k += B) {
                    const uint64_t a = magnitude(py[k]), b = magnitude(py[N + k]);
                    mya = a > mya ? a : mya;
                    myb = b > myb ? b : myb;
                }
                const uint64_t yra = block_max(mya, red);
                const uint64_t yrb = block_max(myb, red);
                const bool n_ya = narrow_terms(lv.pa_reach[6], yra, N, &st);
                const bool n_yb = narrow_terms(lv.pa_reach[7], yrb, N, &st);
                for (uint32_t o = tid; o < 2 * W; o += B) {
                    const uint32_t j = o % W;
                    const bool im = o >= W;
                    rab[o] = fit64(dot(tt + (im ? lv.pa[7] : lv.pa[6]) + j, W, N, py + (im ? N : 0), im ? n_yb : n_ya), &st);
                }
                __syncthreads();
                uwide ppow = 0;
                for (uint32_t j = tid; j < W; j += B) {
                    const int64_t r = fit64(rel((wide)rab[j] - (wide)rab[W + j], MATERIAL_BITS), &st);
                    praw[j] = r;
                    ppow += (uwide)((wide)r * (wide)r);
                }
                ppow = block_sum(ppow, redw);
                if (tid == 0) {
                    const uwide root = isqrt128((uwide)((wide)ppow / (wide)W));
                    if (root > (uwide)INT64_MAX) {
                        atomicOr(&st, TOWER_REFUSED_WORD64);
                    }
                    scale_s = root > (uwide)INT64_MAX ? 0 : (int64_t)root;
                }
                __syncthreads();
                const int64_t pscale = scale_s;
                uint64_t pm = 0;
                for (uint32_t j = tid; j < W; j += B) {
                    prd[j] = pscale == 0 ? 0 : fit32(div_nearest((wide)praw[j] << FACE_BITS, pscale), &st);
                    const uint64_t v = magnitude(prd[j]);
                    pm = v > pm ? v : pm;
                }
                prmax = block_max(pm, red);
                if (keep) {
                    for (uint32_t k = tid; k < N; k += B) {
                        fr.pa_probe[(q * N + k) * 2] = ppr[2 * k];
                        fr.pa_probe[(q * N + k) * 2 + 1] = ppr[2 * k + 1];
                        fr.pa_current[q * 2 * N + k] = py[k];
                        fr.pa_current[q * 2 * N + N + k] = py[N + k];
                    }
                    for (uint32_t j = tid; j < W; j += B) {
                        fr.pa_read[q * W + j] = prd[j];
                    }
                    if (tid == 0) {
                        fr.pa_scale[q] = pscale;
                        fr.r_pa_read[q] = prmax;
                        fr.r_pa_yre[q] = yra;
                        fr.r_pa_yim[q] = yrb;
                    }
                }
                __syncthreads();
            }
            // The contacts: the drive a = W r̂ + b_a, rectified, v = max(a, 0); or beside it the pair
            // contact's second drive b = W_b r̂ + b_b and v = a ⊙ b on 2^(−32) released to the face
            // (the foil: a b_b + b_a (b − b_b), the product's block held at zero).
            // At the strands' level each drive also reads their faces, `W_s s` released on its own.
            const bool stranded = SR > 0 && l == law.strand_level;
            const bool n_c = narrow_terms(lv.reach[4], rmax, W, &st);
            const bool n_p = law.contact != 0 && narrow_terms(lv.reach[10], rmax, W, &st);
            const bool n_sa = stranded && narrow_terms(law.strand_reach[0], smax, 6 * SR, &st);
            const bool n_sb = stranded && law.contact != 0 && narrow_terms(law.strand_reach[1], smax, 6 * SR, &st);
            const bool n_pc = P && narrow_terms(lv.pa_reach[8], prmax, W, &st);
            m = 0;
            uint64_t mc = 0;
            for (uint32_t o = tid; o < F; o += B) {
                wide sum = dot(tt + lv.contact + o, F, W, rd, n_c);
                sum += (wide)th[lv.contact_bias + o] << MATERIAL_BITS;
                int64_t a64 = fit64(rel(sum, MATERIAL_BITS), &st);
                if (stranded) {
                    a64 = fit64((wide)a64 + (wide)fit64(rel(dot(tt + law.strand_contact + o, F, 6 * SR, sp, n_sa), MATERIAL_BITS), &st), &st);
                }
                if (P) {
                    a64 = fit64((wide)a64 + (wide)fit64(rel(dot(tt + lv.pa[8] + o, F, W, prd, n_pc), MATERIAL_BITS), &st), &st);
                }
                const int32_t d = fit32(a64, &st);
                dv[o] = d;
                uint64_t v = magnitude(d);
                int32_t c = d > 0 ? d : 0;
                if (law.contact != 0) {
                    wide second = dot(tt + lv.pair + o, F, W, rd, n_p);
                    second += (wide)th[lv.pair_bias + o] << MATERIAL_BITS;
                    int64_t b64 = fit64(rel(second, MATERIAL_BITS), &st);
                    if (stranded) {
                        b64 = fit64((wide)b64 + (wide)fit64(rel(dot(tt + law.strand_pair + o, F, 6 * SR, sp, n_sb), MATERIAL_BITS), &st), &st);
                    }
                    const int32_t e = fit32(b64, &st);
                    const wide ba = th[lv.contact_bias + o], bb = th[lv.pair_bias + o];
                    const wide product = law.contact == 1 ? (wide)d * e : (wide)d * bb + ba * ((wide)e - bb);
                    c = fit32(rel(product, FACE_BITS), &st);
                    if (keep) {
                        fr.second[q * F + o] = e;
                    }
                    const uint64_t ve = magnitude(e);
                    v = ve > v ? ve : v;
                }
                cd[o] = c;
                m = v > m ? v : m;
                const uint64_t vc = magnitude(c);
                mc = vc > mc ? vc : mc;
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
                    if (stranded) {
                        fr.r_strand[q] = smax;
                    }
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
        // The ring read through its pair contact with the top face (`RingFace::pair_read`):
        // x̂ = (x / ‖x‖_rms, 1) on 2^(−16) and φ = x̂ ⊗ ρ released to 2^(−16), row j of x̂ by
        // column k of ρ.
        uint64_t phimax = 0;
        if (R > 0) {
            uwide power = 0;
            for (uint32_t j = tid; j < W; j += B) {
                power += (uwide)((wide)x[j] * (wide)x[j]);
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
            const int64_t top_scale = scale_s;
            for (uint32_t j = tid; j < W; j += B) {
                hat[j] = top_scale == 0 ? 0 : fit32(div_nearest((wide)x[j] << FACE_BITS, top_scale), &st);
            }
            __syncthreads();
            uint64_t mph = 0;
            for (uint32_t i = tid; i < KP; i += B) {
                const uint32_t j = i / K2, k = i % K2;
                const wide xj = j < W ? (wide)hat[j] : (wide)1 << FACE_BITS;
                phi[i] = fit32(rel(xj * (wide)rho[k], FACE_BITS), &st);
                const uint64_t a = magnitude(phi[i]);
                mph = a > mph ? a : mph;
            }
            phimax = block_max(mph, red);
            if (keep) {
                for (uint32_t i = tid; i < KP; i += B) {
                    fr.ring_pair[qc * KP + i] = phi[i];
                }
                for (uint32_t j = tid; j < W; j += B) {
                    fr.top_hat[qc * W + j] = hat[j];
                }
                if (tid == 0) {
                    fr.top_scale[qc] = top_scale;
                    fr.r_ring_pair[qc] = phimax;
                }
            }
        }
        // The readout's face z = U x + c, and the masses 2^(z − z_max) on 2^(−62).
        // The pair face read by its own readout, z += V c(p), and the ring's, z += W φ, each
        // released to 2^(−16) beside it.
        const bool n_z = narrow_terms(law.readout_reach, xmax, W, &st);
        const bool n_v = K > 0 && narrow_terms(law.pair_reach[0], pmax, K, &st);
        const bool n_w = R > 0 && narrow_terms(law.ring_reach, phimax, KP, &st);
        int64_t zm = INT64_MIN;
        for (uint32_t c = tid; c < A; c += B) {
            wide sum = dot(tt + law.readout + c, A, W, x, n_z);
            sum += (wide)th[law.readout_bias + c] << MATERIAL_BITS;
            z[c] = fit64(rel(sum, MATERIAL_BITS), &st);
            if (K > 0) {
                const int64_t read = fit64(rel(dot(th + law.pair_readout + (uint64_t)c * K, 1, K, pc, n_v), MATERIAL_BITS), &st);
                z[c] = fit64((wide)z[c] + (wide)read, &st);
            }
            if (R > 0) {
                const int64_t read = fit64(rel(dot(th + law.ring_readout + (uint64_t)c * KP, 1, KP, phi, n_w), MATERIAL_BITS), &st);
                z[c] = fit64((wide)z[c] + (wide)read, &st);
            }
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
            // The face the next arrival is read against.
            news_total = total;
            news_has = 1;
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
    for (uint32_t r = tid; r < R; r += B) {
        fr.ring_ends[((uint64_t)s * R + r) * 2] = rg[2 * r];
        fr.ring_ends[((uint64_t)s * R + r) * 2 + 1] = rg[2 * r + 1];
        fr.hands_ends[(uint64_t)s * R + r] = hd[r];
    }
    for (uint32_t k = tid; k < SR; k += B) {
        for (uint32_t j = 0; j < 3; j++) {
            fr.strand_ends[(uint64_t)s * (3 * SR + 1) + j * SR + k] = sr[j * SR + k];
        }
    }
    if (SR > 0 && tid == 0) {
        fr.strand_ends[(uint64_t)s * (3 * SR + 1) + 3 * SR] = reversed;
    }
    if (law.news) {
        uint64_t *end = fr.news_ends + (uint64_t)s * (A + 4);
        for (uint32_t c = tid; c < A; c += B) {
            end[4 + c] = ms[c];
        }
        if (tid == 0) {
            end[0] = news_has;
            end[1] = (uint64_t)news_total;
            end[2] = (uint64_t)(news_total >> 64);
            end[3] = news_phase;
        }
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
    // The ring's pair read: the readout's covector `back = Wᵀ δz` over φ, then `∂ρ` and `∂x̂`.
    const uint32_t R = law.ring_ranks, H = law.ring_harmonics, K2 = 2 * R * H, KP = (W + 1) * K2;
    uwide *redw = (uwide *)carve(at, sizeof(uwide) * 32 * (R > 0));
    int64_t *dxs = (int64_t *)carve(at, 8ull * W);
    int64_t *back = (int64_t *)carve(at, 8ull * KP);
    int64_t *drho = (int64_t *)carve(at, 8ull * K2);
    int64_t *dhat = (int64_t *)carve(at, 8ull * W * (R > 0));
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
        dxs[j] = fit64(rel(sum, MATERIAL_BITS), &st);
    }
    __syncthreads();
    if (R > 0) {
        // `back = Wᵀ δz` released by the material's grain (`transposed`).
        const bool n_w = narrow_rows(law.ring_reach, ymax, A);
        for (uint32_t k = tid; k < KP; k += B) {
            back[k] = fit64(rel(dot(fr.theta + law.ring_readout + k, KP, A, dz, n_w), MATERIAL_BITS), &st);
        }
        __syncthreads();
        // ∂ρ_k = Σ_j ∂φ_jk x̂_j and ∂x̂_j = Σ_k ∂φ_jk ρ_k, each released by the face's grain.
        const int32_t *rho = fr.ring_rho + q * K2;
        const int32_t *hat = fr.top_hat + q * W;
        for (uint32_t k = tid; k < K2; k += B) {
            wide sum = 0;
            for (uint32_t j = 0; j <= W; j++) {
                const wide xj = j < W ? (wide)hat[j] : (wide)1 << FACE_BITS;
                sum += (wide)back[j * K2 + k] * xj;
            }
            drho[k] = fit64(rel(sum, FACE_BITS), &st);
        }
        for (uint32_t j = tid; j < W; j += B) {
            wide sum = 0;
            for (uint32_t k = 0; k < K2; k++) {
                sum += (wide)back[j * K2 + k] * (wide)rho[k];
            }
            dhat[j] = fit64(rel(sum, FACE_BITS), &st);
        }
        __syncthreads();
        // Each rank's read covector: the harmonics' adjoint to the turn (`harmonics_adjoint`),
        // then the ratio's (`ratio_adjoint`), one thread a rank.
        for (uint32_t r = tid; r < R; r += B) {
            const int32_t *qr = rho + 2 * H * r;
            const int64_t *gq = drho + 2 * H * r;
            const wide re = qr[0], im = qr[1];
            const wide n2 = re * re + im * im;
            wide d0 = gq[0], d1 = gq[1];
            if (n2 != 0 && H > 1) {
                wide turn = 0;
                for (uint32_t h = 1; h < H; h++) {
                    const wide a = sub_checked((wide)gq[2 * h + 1] * qr[2 * h], (wide)gq[2 * h] * qr[2 * h + 1], &st);
                    turn = add_checked(turn, mul_checked(a, (wide)(h + 1), &st), &st);
                }
                d0 = fit64(d0 + div_nearest(mul_checked(turn, -im, &st), n2), &st);
                d1 = fit64(d1 + div_nearest(mul_checked(turn, re, &st), n2), &st);
            }
            const int64_t scale = fr.ring_scale[q * R + r];
            int64_t c0 = 0, c1 = 0;
            if (scale != 0) {
                const wide mean = div_nearest(re * d0 + im * d1, 2);
                c0 = fit64(div_nearest((d0 - rel(mean * re, 2 * FACE_BITS)) << FACE_BITS, scale), &st);
                c1 = fit64(div_nearest((d1 - rel(mean * im, 2 * FACE_BITS)) << FACE_BITS, scale), &st);
            }
            fr.ring_cov[q * 2 * R + 2 * r] = c0;
            fr.ring_cov[q * 2 * R + 2 * r + 1] = c1;
        }
        // The top's covector through x̂'s ratio (`ratio_adjoint`).
        const int64_t top_scale = fr.top_scale[q];
        uwide dot_part = 0;
        for (uint32_t j = tid; j < W; j += B) {
            dot_part += (uwide)((wide)hat[j] * (wide)dhat[j]);
        }
        const wide mean = div_nearest((wide)block_sum(dot_part, redw), (wide)W);
        for (uint32_t j = tid; j < W; j += B) {
            int64_t e = 0;
            if (top_scale != 0) {
                e = fit64(div_nearest(((wide)dhat[j] - rel(mean * (wide)hat[j], 2 * FACE_BITS)) << FACE_BITS, top_scale), &st);
            }
            dxs[j] = fit64((wide)dxs[j] + (wide)e, &st);
        }
        __syncthreads();
    }
    for (uint32_t j = tid; j < W; j += B) {
        fr.dx[q * W + j] = dxs[j];
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
    int64_t *db = (int64_t *)carve(at, 8ull * F * (law.contact != 0));
    int64_t *dr = (int64_t *)carve(at, 8ull * W);
    int64_t *dread = (int64_t *)carve(at, 8ull * W);
    uint64_t *red = (uint64_t *)carve(at, 8ull * 32);
    const uint32_t P = law.participation != 0;
    int64_t *pdh = (int64_t *)carve(at, 8ull * W * P);
    int64_t *pdra = (int64_t *)carve(at, 8ull * W * P);
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
    // dv = Rᵀ dy; the rectifier passes it where the drive conducts, the pair contact to each drive
    // through its partner (δa = dv ⊙ b, δb = dv ⊙ a, each bias the same), the foil to each drive's
    // material through the other drive's bias (δa = dv b_b, δb = dv b_a) and to each bias through
    // the other drive (dv ⊙ b, dv ⊙ a), each on 2^(−32) released to the material's convention.
    const bool n_v = narrow_rows(lv.reach[5], ymax, W);
    m = 0;
    uint64_t mb = 0;
    for (uint32_t i = tid; i < F; i += B) {
        const int64_t v = fit64(rel(dot(fr.theta + lv.ret + i, F, W, dy, n_v), MATERIAL_BITS), &st);
        const int32_t a = fr.drive[ql * F + i];
        int64_t ga = a > 0 ? v : 0;
        if (law.contact != 0) {
            const int32_t b = fr.second[ql * F + i];
            const wide ya = law.contact == 1 ? b : fr.theta[lv.pair_bias + i];
            const wide yb = law.contact == 1 ? a : fr.theta[lv.contact_bias + i];
            ga = fit64(rel((wide)v * ya, FACE_BITS), &st);
            const int64_t gb = fit64(rel((wide)v * yb, FACE_BITS), &st);
            db[i] = gb;
            fr.db[ql * F + i] = gb;
            if (law.contact == 2) {
                fr.da_bias[ql * F + i] = fit64(rel((wide)v * b, FACE_BITS), &st);
                fr.db_bias[ql * F + i] = fit64(rel((wide)v * a, FACE_BITS), &st);
            }
            const uint64_t mag = magnitude(gb);
            mb = mag > mb ? mag : mb;
        }
        da[i] = ga;
        fr.da[ql * F + i] = ga;
        const uint64_t mag = magnitude(ga);
        m = mag > m ? mag : m;
    }
    const uint64_t amax = block_max(m, red);
    const uint64_t bmax = block_max(mb, red);
    // dr = Kᵀ da (and + K_bᵀ db, each released on its own), split over `G` groups of the contacts.
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
    if (law.contact != 0) {
        const bool n_b = narrow_rows(lv.reach[10], bmax, F);
        for (uint32_t idx = tid; idx < G * W; idx += B) {
            const uint32_t g = idx / W, j = idx % W;
            const uint32_t from = (uint32_t)((uint64_t)F * g / G), to = (uint32_t)((uint64_t)F * (g + 1) / G);
            part[idx] = dot(fr.theta + lv.pair + (uint64_t)from * W + j, W, to - from, db + from, n_b);
        }
        __syncthreads();
        for (uint32_t j = tid; j < W; j += B) {
            wide sum = 0;
            for (uint32_t g = 0; g < G; g++) {
                sum += part[g * W + j];
            }
            dr[j] = fit64((wide)dr[j] + (wide)fit64(rel(sum, MATERIAL_BITS), &st), &st);
        }
        __syncthreads();
    }
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
        if (law.contact != 0) {
            fr.r_db[ql] = bmax;
        }
    }
    // Participation's current: ∂r̂ᵃ = W₁ᵃᵀ δa, through its ratio, and the current's covector
    // Cᵃ_reᵀ ∂rᵃ and Cᵃ_imᵀ (−∂rᵃ).
    if (P) {
        const bool n_pa = narrow_rows(lv.pa_reach[8], amax, F);
        for (uint32_t idx = tid; idx < G * W; idx += B) {
            const uint32_t g = idx / W, j = idx % W;
            const uint32_t from = (uint32_t)((uint64_t)F * g / G), to = (uint32_t)((uint64_t)F * (g + 1) / G);
            part[idx] = dot(fr.theta + lv.pa[8] + (uint64_t)from * W + j, W, to - from, da + from, n_pa);
        }
        __syncthreads();
        for (uint32_t j = tid; j < W; j += B) {
            wide sum = 0;
            for (uint32_t g = 0; g < G; g++) {
                sum += part[g * W + j];
            }
            pdh[j] = fit64(rel(sum, MATERIAL_BITS), &st);
        }
        __syncthreads();
        const int64_t pscale = fr.pa_scale[ql];
        uwide pdot = 0;
        for (uint32_t j = tid; j < W; j += B) {
            pdot += (uwide)((wide)fr.pa_read[ql * W + j] * (wide)pdh[j]);
        }
        const wide pmean = div_nearest((wide)block_sum(pdot, redw), (wide)W);
        uint64_t pm = 0;
        for (uint32_t j = tid; j < W; j += B) {
            int64_t v = 0;
            if (pscale != 0) {
                const wide read = fr.pa_read[ql * W + j];
                v = fit64(div_nearest(((wide)pdh[j] - rel(pmean * read, 2 * FACE_BITS)) << FACE_BITS, pscale), &st);
            }
            pdra[j] = v;
            fr.pa_dra[ql * W + j] = v;
            const uint64_t a = magnitude(v);
            pm = a > pm ? a : pm;
        }
        const uint64_t pdmax = block_max(pm, red);
        if (tid == 0) {
            fr.r_pa_dra[ql] = pdmax;
        }
        const bool n_ga = narrow_rows(lv.pa_reach[6], pdmax, W);
        const bool n_gb = narrow_rows(lv.pa_reach[7], pdmax, W);
        for (uint32_t o = tid; o < 2 * N; o += B) {
            const uint32_t k = o % N;
            const bool im = o >= N;
            const wide sum = rel(dot(fr.theta + (im ? lv.pa[7] : lv.pa[6]) + k, N, W, pdra, im ? n_gb : n_ga), MATERIAL_BITS);
            fr.pa_gy[ql * 2 * N + o] = fit64(im ? -sum : sum, &st);
        }
        __syncthreads();
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

// The ring's reverse over one stream (`RingFace::reverse`), one block a stream, the cells in
// reverse order, every rank's scan carried together: at cell t each rank's covector
// `G_t = (g_ρx, o_t g_ρy) + Mᵀ_(t+1) G_(t+1)` (one thread a rank, the restart's re-basing carrying
// it back), its move's covector, and `e`, `h`, `f`; then the carried face's covector `∂ŝ_t` summed
// over the ranks in their order (one thread a coordinate), added to the read covector of the
// state it was pushed from (the cell before's, the opening's not being material), and each
// factor's covector summed over the cells (one thread a factor entry); at the end each sum is
// carried to the material's convention by `2^(24 − release)`. Runs after the level's contacts
// (which write the read covector) and before its modes' scan (which reads it, and the move's
// covector the ring returns where no rank rode a founded pair move).
extern "C" __global__ void __launch_bounds__(TOWER_THREADS) tower_reverse_ring(TowerLaw law, TowerFrame fr) {
    const uint32_t s = blockIdx.x, tid = threadIdx.x, B = blockDim.x;
    const uint32_t W = law.width, N = law.modes, L = law.levels, T = law.cells, R = law.ring_ranks;
    const uint32_t l = law.ring_level, dims = 2 * N, hatn = W + 1, RM = 6 * N + 2 * W + 3;
    extern __shared__ __align__(16) unsigned char smem[];
    unsigned char *at = smem;
    wide *gs = (wide *)carve(at, sizeof(wide) * 2 * R);
    wide *ehf = (wide *)carve(at, sizeof(wide) * 5 * R);
    wide *dm = (wide *)carve(at, sizeof(wide) * 4 * R);
    int64_t *sf = (int64_t *)carve(at, 8ull * dims);
    uint32_t *rode = (uint32_t *)carve(at, 4ull * R);
    __shared__ uint32_t st;
    if (tid == 0) {
        st = 0;
    }
    wide *gsum = fr.ring_g + (uint64_t)s * R * RM;
    for (uint32_t e = tid; e < R * RM; e += B) {
        gsum[e] = 0;
    }
    for (uint32_t i = tid; i < 2 * R; i += B) {
        gs[i] = 0;
    }
    __syncthreads();
    for (uint32_t step = 0; step < T; step++) {
        const uint32_t t = T - 1 - step;
        const uint64_t q = (uint64_t)s * T + t;
        const uint32_t arrived = fr.classes[(uint64_t)s * (T + 1) + t];
        const uint32_t u = arrived < law.alphabet ? arrived : 0; // the forward refused it
        // ŝ_t, the carried face of the state the push read (the cell before's, or the opening's).
        const int64_t *before = t == 0 ? fr.opening + ((uint64_t)s * L + l) * dims : fr.state + ((q - 1) * L + l) * dims;
        for (uint32_t j = tid; j < dims; j += B) {
            sf[j] = fit64(rel(before[j], STATE_BITS - FACE_BITS), &st);
        }
        for (uint32_t r = tid; r < R; r += B) {
            const uint64_t qr = q * R + r;
            const uint32_t *sh = fr.ring_shifts + 5 * r;
            const uint32_t sigma = sh[4], total = sh[3] + sigma;
            wide back[2] = {0, 0};
            if (t + 1 < T) {
                const int64_t *mn = fr.ring_move + (qr + R) * 4;
                const wide m[4] = {mn[0], mn[1], mn[2], mn[3]};
                ring_carry_adjoint(m, gs[2 * r], gs[2 * r + 1], back);
            }
            const uint32_t hand = fr.ring_hand[qr];
            if (hand & 2u) {
                back[1] = -back[1];
            }
            const wide gy0 = fr.ring_cov[q * 2 * R + 2 * r + 1];
            const wide gx = (wide)fr.ring_cov[q * 2 * R + 2 * r] + back[0];
            const wide gy = ((hand & 1u) ? -gy0 : gy0) + back[1];
            gs[2 * r] = gx;
            gs[2 * r + 1] = gy;
            const wide x = t == 0 ? fr.ring_open[((uint64_t)s * R + r) * 2] : fr.ring_after[(qr - R) * 2];
            const wide y = t == 0 ? fr.ring_open[((uint64_t)s * R + r) * 2 + 1] : fr.ring_after[(qr - R) * 2 + 1];
            // The move's covector on the modes' convention: (x gx + y gy, x gy − y gx, x gx − y gy,
            // x gy + y gx) 2^(8−σ).
            wide xgx, ygy, xgy, ygx;
            if (sigma >= 8) {
                xgx = release_product(x, gx, sigma - 8, &st);
                ygy = release_product(y, gy, sigma - 8, &st);
                xgy = release_product(x, gy, sigma - 8, &st);
                ygx = release_product(y, gx, sigma - 8, &st);
            } else {
                const wide up = (wide)1 << (8 - sigma);
                xgx = mul_checked(mul_checked(x, gx, &st), up, &st);
                ygy = mul_checked(mul_checked(y, gy, &st), up, &st);
                xgy = mul_checked(mul_checked(x, gy, &st), up, &st);
                ygx = mul_checked(mul_checked(y, gx, &st), up, &st);
            }
            dm[4 * r] = add_checked(xgx, ygy, &st);
            dm[4 * r + 1] = add_checked(xgy, -ygx, &st);
            dm[4 * r + 2] = add_checked(xgx, -ygy, &st);
            dm[4 * r + 3] = add_checked(xgy, ygx, &st);
            rode[r] = hand & 4u;
            // conj(G) β and conj(G) α, then their products with γ and α, released by the push and σ.
            const wide *fa = fr.ring_factor + qr * 5;
            const wide a0 = fa[0], a1 = fa[1], b0 = fa[2], b1 = fa[3], gamma = fa[4];
            const wide cb0 = add_checked(mul_checked(gx, b0, &st), mul_checked(gy, b1, &st), &st);
            const wide cb1 = sub_checked(mul_checked(gx, b1, &st), mul_checked(gy, b0, &st), &st);
            const wide ca0 = add_checked(mul_checked(gx, a0, &st), mul_checked(gy, a1, &st), &st);
            const wide ca1 = sub_checked(mul_checked(gx, a1, &st), mul_checked(gy, a0, &st), &st);
            wide *o = ehf + 5 * r;
            o[0] = release_product(cb0, gamma, total, &st);
            o[1] = release_product(cb1, gamma, total, &st);
            o[2] = release_product(ca0, gamma, total, &st);
            o[3] = release_product(ca1, gamma, total, &st);
            o[4] = sub_checked(release_product(cb0, a0, total, &st), release_product(cb1, a1, total, &st), &st);
        }
        __syncthreads();
        // ∂ŝ_t, the ranks in their order, onto the read covector of the state before.
        for (uint32_t j = tid; j < dims; j += B) {
            wide sum = 0;
            for (uint32_t r = 0; r < R; r++) {
                const int32_t *fac = fr.theta + law.ring_factors + (uint64_t)r * RM;
                const uint32_t *sh = fr.ring_shifts + 5 * r;
                const wide *o = ehf + 5 * r;
                const wide through_a = rel(sub_checked(mul_checked(o[0], fac[j], &st), mul_checked(o[1], fac[dims + j], &st), &st), sh[0]);
                const wide through_g = rel(mul_checked(o[4], fac[2 * dims + 2 * hatn + j], &st), sh[2]);
                sum = add_checked(add_checked(sum, through_a, &st), through_g, &st);
            }
            const int64_t v = fit64(sum, &st);
            if (t > 0) {
                // ŝ's (re, im) of mode j/2 onto the read covector's re and im blocks.
                int64_t *rc = fr.readcov + ((q - 1) * L + l) * dims + (j & 1u) * N + j / 2;
                *rc = fit64((wide)*rc + (wide)v, &st);
            }
        }
        // Each factor's covector: ∂a = Σ (Re e, −Im e) ŝ, ∂b = Σ (Re h, −Im h) x̂, ∂g = Σ f (ŝ, 2^16).
        for (uint32_t e = tid; e < R * RM; e += B) {
            const uint32_t r = e / RM, i = e % RM;
            const wide *o = ehf + 5 * r;
            wide term;
            if (i < 2 * dims) {
                const wide sj = sf[i % dims];
                term = i < dims ? mul_checked(o[0], sj, &st) : mul_checked(o[1], -sj, &st);
            } else if (i < 2 * dims + 2 * hatn) {
                const uint32_t k = i - 2 * dims, j = k % hatn;
                const wide xj = j < W ? (wide)fr.ring_opening[(uint64_t)u * W + j] : (wide)1 << FACE_BITS;
                term = k < hatn ? mul_checked(o[2], xj, &st) : mul_checked(o[3], -xj, &st);
            } else {
                const uint32_t j = i - 2 * dims - 2 * hatn;
                term = mul_checked(o[4], j < dims ? (wide)sf[j] : (wide)1 << FACE_BITS, &st);
            }
            gsum[e] = add_checked(gsum[e], term, &st);
        }
        // The mode's move (its λ, and its β when pumped) takes the covector of every rank that
        // rode it, not a founded pair move.
        if (tid == 0) {
            wide d[4] = {0, 0, 0, 0};
            for (uint32_t r = 0; r < R; r++) {
                if (rode[r] == 0) {
                    for (uint32_t i = 0; i < 4; i++) {
                        d[i] += dm[4 * r + i];
                    }
                }
            }
            for (uint32_t i = 0; i < 4; i++) {
                fr.ring_dmove[q * 4 + i] = d[i];
            }
        }
        __syncthreads();
    }
    // Each sum on the material's convention: 2^40 per unit of 2^(−24), from its factor's release.
    for (uint32_t e = tid; e < R * RM; e += B) {
        const uint32_t r = e / RM, i = e % RM;
        const uint32_t *sh = fr.ring_shifts + 5 * r;
        const uint32_t bits = i < 2 * dims ? sh[0] : i < 2 * dims + 2 * hatn ? sh[1] : sh[2];
        gsum[e] = bits >= MATERIAL_BITS ? rel(gsum[e], bits - MATERIAL_BITS) : mul_checked(gsum[e], (wide)1 << (MATERIAL_BITS - bits), &st);
    }
    __syncthreads();
    if (tid == 0 && st != 0) {
        atomicOr(fr.status + s, st);
    }
}

// The ring's factor covector summed over the streams into the gradient.
extern "C" __global__ void tower_ring_factors(TowerLaw law, TowerFrame fr) {
    const uint64_t entries = (uint64_t)law.ring_ranks * (6 * law.modes + 2 * law.width + 3);
    for (uint64_t e = (uint64_t)blockIdx.x * blockDim.x + threadIdx.x; e < entries; e += (uint64_t)gridDim.x * blockDim.x) {
        uwide sum = 0;
        for (uint32_t s = 0; s < law.streams; s++) {
            sum += (uwide)fr.ring_g[s * entries + e];
        }
        fr.gradient[law.ring_factors + e] += (wide)sum;
    }
}

// The modes' reverse scan of one level of one stream, one thread a mode, and each cell's gated move
// adjoint: G_h(t) = read covector + conj(λ_(t+1)) G_h(t+1) (+ β_(t+1) conj(G_h(t+1)) when
// pumped); the covectors of |λ| and arg λ summed over the cells; the gate's logit covector δq; a
// turned level's turn covector δs = 2^(−spread) π Re(conj(iλ_t) G_λ), through ∂θ/∂s = π; a pumped
// level's axis covector δp = 2^(−spread) π Re(conj(iβ_t) G_β) and depth covector
// δκ = (−sgn(κ) Re(conj(ρU) G_λ) + Re(conj(ρP) G_β)) 2 ln 2 r (1 − r), with G_β = h_(t−1) G_h(t);
// and γ_t G_h, what the pushes return.
extern "C" __global__ void tower_reverse_modes(TowerLaw law, TowerFrame fr, uint32_t l) {
    const uint32_t s = blockIdx.x, B = blockDim.x;
    const uint32_t A = law.alphabet, N = law.modes, L = law.levels, T = law.cells;
    const TowerLevel &lv = law.level[l];
    const wide one = (wide)1 << MOVE_BITS;
    // Under a rotor the block holds exactly one thread a mode, and each step's carried covector is
    // exchanged here between the modes of a ring.
    extern __shared__ __align__(16) unsigned char smem[];
    wide *xb = (wide *)smem;
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
            wide lr, li, pbr = 0, pbi = 0;
            if (t + 1 < T) {
                const int64_t *later = fr.moves + (((q + 1) * L + l) * N + k) * 6;
                lr = later[3];
                li = later[4];
                if (law.pumped) {
                    const int64_t *pump = fr.pumps + (((q + 1) * L + l) * N + k) * 6;
                    pbr = pump[4];
                    pbi = pump[5];
                }
            } else {
                lr = fr.theta[lv.move_re + k];
                li = fr.theta[lv.move_im + k];
            }
            // The later cell's move acted once a tick of the level's clock (once without one):
            // conj(λ_(t+1)) carried back that many times (with β_(t+1) conj(·) when pumped, never
            // beside a clock).
            const uint32_t later_ticks = law.news && t + 1 < T ? fr.ticks[(q + 1) * L + l] : 1;
            wide br = cr, bi = ci;
            for (uint32_t j = 0; j < later_ticks; j++) {
                const wide ar = rel(lr * br + li * bi + pbr * br + pbi * bi, MOVE_BITS);
                bi = rel(lr * bi - li * br + pbi * br - pbr * bi, MOVE_BITS);
                br = ar;
            }
            // The rotor's step and turn at the later cell carried back by the monomial's adjoint
            // (`Rotor::back`): mode m of h'_(t+1) took mode s(m) of h_t turned by its key, so mode k
            // takes the covector of the m' with s(m') = k, turned back by m''s key.
            if (law.moving) {
                xb[2 * k] = br;
                xb[2 * k + 1] = bi;
                __syncthreads();
                if (t + 1 < T && k < law.moving) {
                    uint32_t un = fr.classes[(uint64_t)s * (T + 1) + t + 1];
                    un = un < A ? un : 0;
                    const int64_t *keys = fr.rotor + ((uint64_t)l * A + un) * law.moving * 4;
                    const uint32_t from = (uint32_t)keys[k * 4 + 1];
                    const wide a = keys[from * 4 + 2], b = keys[from * 4 + 3];
                    const wide x = xb[2 * from], y = xb[2 * from + 1];
                    br = rel(a * x + b * y, MOVE_BITS);
                    bi = rel(a * y - b * x, MOVE_BITS);
                }
                __syncthreads();
            }
            const int64_t gr = fit64((wide)fr.readcov[ql * 2 * N + k] + br, &st);
            const int64_t gi = fit64((wide)fr.readcov[ql * 2 * N + N + k] + bi, &st);
            cr = gr;
            ci = gi;
            const int64_t *previous = t == 0 ? fr.opening + (((uint64_t)s * L + l) * N + k) * 2 : fr.state + (((q - 1) * L + l) * N + k) * 2;
            wide hr = previous[0], hi = previous[1];
            // The covectors of the move read the state it acted on, h' = T P^σ h under a rotor.
            if (k < law.moving) {
                uint32_t uc = fr.classes[(uint64_t)s * (T + 1) + t];
                uc = uc < A ? uc : 0;
                const int64_t *key = fr.rotor + (((uint64_t)l * A + uc) * law.moving + k) * 4;
                const int64_t *src = previous + ((int64_t)key[0] - (int64_t)k) * 2;
                const wide x = src[0], y = src[1];
                hr = fit64(rel(key[2] * x - key[3] * y, MOVE_BITS), &st);
                hi = fit64(rel(key[2] * y + key[3] * x, MOVE_BITS), &st);
            }
            const int64_t *mv = fr.moves + (ql * N + k) * 6;
            const uint32_t ticks = law.news ? fr.ticks[ql] : 1;
            const wide push_r = fr.push[ql * 2 * N + k], push_i = fr.push[ql * 2 * N + N + k];
            const wide open = mv[0], rho = mv[1], gamma = mv[2];
            // The covectors of λ_t and γ_t, and of the push γ_t P x_t summed over the steps it
            // entered.
            // h_(t−1) G_h(t), the covector of β_t, on 2^(−48) (read when pumped).
            wide glr, gli, through, pgr = gr, pgi = gi, gbr = 0, gbi = 0;
            if (ticks == 1) {
                glr = hr * gr + hi * gi;
                gli = hr * gi - hi * gr;
                if (law.pumped) {
                    gbr = hr * gr - hi * gi;
                    gbi = hr * gi + hi * gr;
                }
                // The ring's covector of the move it rode, on the same convention.
                if (law.ring_ranks > 0 && l == law.ring_level && k == law.ring_mode) {
                    glr += fr.ring_dmove[q * 4];
                    gli += fr.ring_dmove[q * 4 + 1];
                    gbr += fr.ring_dmove[q * 4 + 2];
                    gbi += fr.ring_dmove[q * 4 + 3];
                }
                through = (wide)gr * push_r + (wide)gi * push_i;
            } else {
                // The step acted Δτ times with the arrival held: the covector of λ_t is the sum over
                // its sub-steps of conj(h⁽ʲ⁻¹⁾) G⁽ʲ⁾, of γ_t the sum of Re(conj(G⁽ʲ⁾) P x) and of the
                // push the sum of G⁽ʲ⁾, each state between them read again by the forward's law from
                // h_(t−1) and the covector carried back through each, G⁽ʲ⁻¹⁾ = conj(λ_t) G⁽ʲ⁾; no
                // tick sends none (`Tower::reverse_joined`; the card carries no ring beside the
                // clock).
                const wide mr = mv[3], mi = mv[4];
                const wide pr = rel(gamma * push_r, MOVE_BITS), pi = rel(gamma * push_i, MOVE_BITS);
                wide sr = 0, si = 0, gcr = gr, gci = gi;
                through = 0;
                pgr = 0;
                pgi = 0;
                for (uint32_t j = ticks; j >= 1; j--) {
                    wide ar = hr, ai = hi;
                    for (uint32_t i = 1; i < j; i++) {
                        const wide nr = rel(mr * ar - mi * ai, MOVE_BITS) + pr;
                        ai = rel(mr * ai + mi * ar, MOVE_BITS) + pi;
                        ar = nr;
                    }
                    sr += ar * gcr + ai * gci;
                    si += ar * gci - ai * gcr;
                    through += gcr * push_r + gci * push_i;
                    pgr += gcr;
                    pgi += gci;
                    const wide nc = rel(mr * gcr + mi * gci, MOVE_BITS);
                    gci = rel(mr * gci - mi * gcr, MOVE_BITS);
                    gcr = nc;
                }
                glr = sr;
                gli = si;
            }
            const wide turning = rel((wide)mv[3] * gli - (wide)mv[4] * glr, MOVE_BITS);
            around += turning;
            // The cell's unit: the founded one, turned by the cell's own turn when the level is.
            const wide cu_r = law.turned ? (wide)fr.units[(ql * N + k) * 2] : ur;
            const wide cu_i = law.turned ? (wide)fr.units[(ql * N + k) * 2 + 1] : ui;
            if (law.turned) {
                fr.ds[ql * N + k] = fit64(rel((wide)law.half_turn * turning, MOVE_BITS + COVECTOR_BITS + law.turn_spread), &st);
            }
            // A pumped cell's pump: its opening r, depth κ, axis face P and β.
            wide popen = 0, kappa = 0, axr = 0, axi = 0;
            if (law.pumped) {
                const int64_t *pm = fr.pumps + (ql * N + k) * 6;
                popen = pm[0];
                kappa = pm[1];
                axr = pm[2];
                axi = pm[3];
                // Re(conj(iβ) G_β): the covector of the pump axis's turn, through ∂θ/∂p = π.
                const wide axis_turning = rel((wide)pm[4] * gbi - (wide)pm[5] * gbr, MOVE_BITS);
                fr.dp[ql * N + k] = fit64(rel((wide)law.half_turn * axis_turning, MOVE_BITS + COVECTOR_BITS + law.turn_spread), &st);
                // −sgn(κ) Re(conj(ρU) G_λ) + Re(conj(ρP) G_β), the covector of κ, on 2^(−48).
                const wide vr = rel(rho * cu_r, MOVE_BITS), vi = rel(rho * cu_i, MOVE_BITS);
                const wide qr = rel(rho * axr, MOVE_BITS), qi = rel(rho * axi, MOVE_BITS);
                const wide sign = (kappa > 0) - (kappa < 0);
                const wide g_kappa = rel(qr * gbr + qi * gbi - sign * (vr * glr + vi * gli), MOVE_BITS);
                // ∂κ/∂q = 2 ln 2 r (1 − r), on 2^(−30).
                const wide f = rel(rel((wide)law.ln2 * popen, MOVE_BITS) * (one - popen), MOVE_BITS);
                fr.dk[ql * N + k] = fit64(rel(g_kappa * 2 * f, COVECTOR_BITS + MOVE_BITS), &st);
            }
            int64_t dq = 0;
            if (mv[5] == 0) {
                // ∂α/∂ρ = (1 − |κ|) U and ∂β/∂ρ = κ P (U alone when unpumped).
                const wide keep_ = one - (kappa < 0 ? -kappa : kappa);
                const wide kur = rel(keep_ * cu_r, MOVE_BITS), kui = rel(keep_ * cu_i, MOVE_BITS);
                const wide kr = rel(kappa * axr, MOVE_BITS), ki = rel(kappa * axi, MOVE_BITS);
                const wide g_rho = rel(kur * glr + kui * gli + kr * gbr + ki * gbi, MOVE_BITS) - div_nearest(rho * through, gamma);
                along += rel(g_rho * div_nearest((wide)GATE_REACH * open * rho, modulus), MOVE_BITS);
                wide f = rel(rho * log, MOVE_BITS);
                f = rel(f * (wide)law.ln2_square, MOVE_BITS);
                f = rel(f * open, MOVE_BITS);
                f = rel(f * (one - open), MOVE_BITS);
                dq = fit64(rel(g_rho * GATE_REACH * f, COVECTOR_BITS + MOVE_BITS), &st);
            }
            fr.gre[ql * N + k] = fit64(rel(gamma * pgr, MOVE_BITS), &st);
            fr.gim[ql * N + k] = fit64(rel(gamma * pgi, MOVE_BITS), &st);
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

// What the pushes, the gate, a turned level's turn and a pumped level's depth and axis return to
// the level's input: dx += P_reᵀ γG_re + P_imᵀ γG_im + W_gᵀ δq (+ W_φᵀ δs) (+ W_κᵀ δκ + W_ψᵀ δp).
extern "C" __global__ void __launch_bounds__(TOWER_THREADS) tower_reverse_dx(TowerLaw law, TowerFrame fr, uint32_t l) {
    const uint64_t q = blockIdx.x, ql = q * law.levels + l;
    const uint32_t s = (uint32_t)(q / law.cells), tid = threadIdx.x, B = blockDim.x;
    const uint32_t W = law.width, N = law.modes;
    const TowerLevel &lv = law.level[l];
    extern __shared__ __align__(16) unsigned char smem[];
    unsigned char *at = smem;
    const uint32_t own = 3 + law.turned + 2 * law.pumped;
    const uint32_t fams = own + 6 * (law.participation != 0);
    int64_t *v = (int64_t *)carve(at, 8ull * fams * N);
    int64_t *back = (int64_t *)carve(at, 8ull * fams * W);
    uint64_t *red = (uint64_t *)carve(at, 8ull * 32);
    __shared__ uint32_t st;
    if (tid == 0) {
        st = 0;
    }
    uint64_t m0 = 0, m1 = 0, m2 = 0, m3 = 0, m4 = 0, m5 = 0;
    for (uint32_t k = tid; k < N; k += B) {
        v[k] = fr.gre[ql * N + k];
        v[N + k] = fr.gim[ql * N + k];
        v[2 * N + k] = fr.dq[ql * N + k];
        const uint64_t a = magnitude(v[k]), b = magnitude(v[N + k]), c = magnitude(v[2 * N + k]);
        m0 = a > m0 ? a : m0;
        m1 = b > m1 ? b : m1;
        m2 = c > m2 ? c : m2;
        if (law.turned) {
            v[3 * N + k] = fr.ds[ql * N + k];
            const uint64_t d = magnitude(v[3 * N + k]);
            m3 = d > m3 ? d : m3;
        }
        if (law.pumped) {
            v[4 * N + k] = fr.dk[ql * N + k];
            v[5 * N + k] = fr.dp[ql * N + k];
            const uint64_t d = magnitude(v[4 * N + k]), e = magnitude(v[5 * N + k]);
            m4 = d > m4 ? d : m4;
            m5 = e > m5 ? e : m5;
        }
    }
    const uint64_t r0 = block_max(m0, red);
    const uint64_t r1 = block_max(m1, red);
    const uint64_t r2 = block_max(m2, red);
    const uint64_t r3 = law.turned ? block_max(m3, red) : 0;
    const uint64_t r4 = law.pumped ? block_max(m4, red) : 0;
    const uint64_t r5 = law.pumped ? block_max(m5, red) : 0;
    if (tid == 0) {
        fr.r_gre[ql] = r0;
        fr.r_gim[ql] = r1;
        fr.r_dq[ql] = r2;
        if (law.turned) {
            fr.r_ds[ql] = r3;
        }
        if (law.pumped) {
            fr.r_dk[ql] = r4;
            fr.r_dp[ql] = r5;
        }
    }
    // The families in `v`'s order: push (re, im), gate, then the turn and the pump's depth and
    // axis where present, then participation's six charts.
    bool narrow[12] = {narrow_rows(lv.reach[0], r0, N), narrow_rows(lv.reach[1], r1, N), narrow_rows(lv.reach[6], r2, N)};
    uint64_t bases[12] = {lv.push_re, lv.push_im, lv.gate};
    uint32_t at_fam = 3;
    if (law.turned) {
        narrow[at_fam] = narrow_rows(lv.reach[7], r3, N);
        bases[at_fam++] = lv.turn;
    }
    if (law.pumped) {
        narrow[at_fam] = narrow_rows(lv.reach[8], r4, N);
        bases[at_fam++] = lv.pump;
        narrow[at_fam] = narrow_rows(lv.reach[9], r5, N);
        bases[at_fam++] = lv.pump_axis;
    }
    if (law.participation) {
        const uint64_t QL = (uint64_t)law.streams * law.cells * law.levels;
        for (uint32_t f = 0; f < 6; f++) {
            for (uint32_t k = tid; k < N; k += B) {
                v[(own + f) * N + k] = fr.pa_gchart[(ql * 6 + f) * N + k];
            }
            narrow[own + f] = narrow_rows(lv.pa_reach[f], fr.r_pa_g[f * QL + ql], N);
            bases[own + f] = lv.pa[f];
        }
        __syncthreads();
    }
    for (uint32_t o = tid; o < fams * W; o += B) {
        const uint32_t fam = o / W, j = o % W;
        const wide sum = dot(fr.theta + bases[fam] + j, W, N, v + fam * N, narrow[fam]);
        back[o] = fit64(rel(sum, MATERIAL_BITS), &st);
    }
    __syncthreads();
    uint64_t mx = 0;
    for (uint32_t j = tid; j < W; j += B) {
        wide sum = (wide)fr.dx[q * W + j];
        for (uint32_t fam = 0; fam < fams; fam++) {
            sum += back[fam * W + j];
        }
        const int64_t v = fit64(sum, &st);
        fr.dx[q * W + j] = v;
        const uint64_t a = magnitude(v);
        mx = a > mx ? a : mx;
    }
    // The bottom level's dx is the cell's input covector δx⁰, what the pair face's lift reads.
    if (l == 0) {
        const uint64_t rx = block_max(mx, red);
        if (tid == 0) {
            fr.r_dx[q] = rx;
        }
    }
    __syncthreads();
    if (tid == 0 && st != 0) {
        atomicOr(fr.status + s, st);
    }
}

// Participation's return over one stream (`participation_return`, `Tower::reverse_joined`), one
// block a stream, at level `l`: at each cell its current's covector, turned back by the cell's
// frame, returns through every head's Gibbs face (recomputed from the kept probe, keys and
// dissipation, the forward's own bits) into the probe, every admitted site's key and current, and
// the head's friction; then each cell's three covectors are turned forward by its frame into the
// six chart covectors `tower_reverse_dx` returns to the input, with their reaches. Runs after the
// level's contacts (which write the current's covector) and before its `tower_reverse_dx`.
extern "C" __global__ void __launch_bounds__(TOWER_THREADS) tower_reverse_participation(TowerLaw law, TowerFrame fr, uint32_t l) {
    const uint32_t s = blockIdx.x, tid = threadIdx.x, B = blockDim.x;
    const uint32_t N = law.modes, L = law.levels, T = law.cells, HH = law.pa_heads;
    const TowerLevel &lv = law.level[l];
    extern __shared__ __align__(16) unsigned char smem[];
    unsigned char *at = smem;
    int64_t *gb = (int64_t *)carve(at, 8ull * 2 * N);
    uwide *redw = (uwide *)carve(at, sizeof(uwide) * 32);
    uint64_t *red = (uint64_t *)carve(at, 8ull * 32);
    __shared__ uint32_t st;
    if (tid == 0) {
        st = 0;
    }
    const uint64_t site0 = (uint64_t)s * T;
    const uint64_t QL = (uint64_t)law.streams * T * L;
    const uint32_t scale_bits = FACE_BITS + law.pa_beta;
    const uint64_t *face_roots = fr.roots;
    wide *gq = fr.pa_gq + site0 * N * 2, *gk = fr.pa_gk + site0 * N * 2, *gw = fr.pa_gw + site0 * N * 2;
    for (uint64_t i = tid; i < (uint64_t)T * N * 2; i += B) {
        gq[i] = 0;
        gk[i] = 0;
        gw[i] = 0;
    }
    __syncthreads();
    for (uint32_t i = 0; i < T; i++) {
        const uint64_t qi = (site0 + i) * L + l;
        for (uint32_t k = tid; k < N; k += B) {
            const wide ur = fr.pa_frame[(qi * N + k) * 2], ui = fr.pa_frame[(qi * N + k) * 2 + 1];
            const wide gr = fr.pa_gy[qi * 2 * N + k], gi = fr.pa_gy[qi * 2 * N + N + k];
            gb[2 * k] = fit64(rel(ur * gr + ui * gi, MOVE_BITS), &st);
            gb[2 * k + 1] = fit64(rel(ur * gi - ui * gr, MOVE_BITS), &st);
        }
        __syncthreads();
        for (uint32_t hh = 0; hh < HH; hh++) {
            const uint32_t from = fr.pa_heads[hh], to = fr.pa_heads[hh + 1];
            const wide friction = fr.theta[lv.pa[9] + hh];
            const wide dis_i = fr.pa_diss[qi * HH + hh];
            int64_t zm = INT64_MIN;
            for (uint32_t j = tid; j <= i; j += B) {
                const uint64_t qj = (site0 + j) * L + l;
                wide pairing = 0;
                for (uint32_t k = from; k < to; k++) {
                    const int64_t *kj = fr.pa_key + (qj * N + k) * 2;
                    pairing += (wide)fr.pa_probe[(qi * N + k) * 2] * kj[0] + (wide)fr.pa_probe[(qi * N + k) * 2 + 1] * kj[1];
                }
                const int64_t z = fit64(rel(pairing, scale_bits) - rel(friction * (dis_i - (wide)fr.pa_diss[qj * HH + hh]), FACE_BITS), &st);
                fr.pa_z[site0 + j] = z;
                zm = z > zm ? z : zm;
            }
            const int64_t peak = block_max_signed(zm, red);
            uwide msum = 0;
            for (uint32_t j = tid; j <= i; j += B) {
                const int64_t z = fr.pa_z[site0 + j];
                const uint64_t e = (wide)peak - (wide)z >= ((wide)UNIT_BITS << FACE_BITS) ? 0 : below_one((wide)z - (wide)peak, face_roots, law.face_digits);
                fr.pa_e[site0 + j] = e;
                msum += e;
            }
            const wide mass = (wide)block_sum(msum, redw);
            // g_a_j = Re⟨w_j, g'⟩ and its weighted mean.
            uwide asum = 0;
            for (uint32_t j = tid; j <= i; j += B) {
                const uint64_t qj = (site0 + j) * L + l;
                wide dotv = 0;
                for (uint32_t k = from; k < to; k++) {
                    const int64_t *wj = fr.pa_value + (qj * N + k) * 2;
                    dotv += (wide)wj[0] * gb[2 * k] + (wide)wj[1] * gb[2 * k + 1];
                }
                const int64_t ga = fit64(rel(dotv, FACE_BITS), &st);
                fr.pa_z[site0 + j] = ga;
                asum += (uwide)((wide)fr.pa_e[site0 + j] * (wide)ga);
            }
            const wide mean = div_nearest((wide)block_sum(asum, redw), mass);
            // g_z_j, and the friction's covector.
            uwide fsum = 0;
            for (uint32_t j = tid; j <= i; j += B) {
                const uint64_t qj = (site0 + j) * L + l;
                const wide e = fr.pa_e[site0 + j];
                const wide gz = rel((wide)law.ln2 * div_nearest(e * ((wide)fr.pa_z[site0 + j] - mean), mass), MOVE_BITS);
                fr.pa_z[site0 + j] = fit64(gz, &st);
                fsum += (uwide)(-rel(gz * (dis_i - (wide)fr.pa_diss[qj * HH + hh]), FACE_BITS));
            }
            const wide fric = (wide)block_sum(fsum, redw);
            if (tid == 0) {
                fr.pa_gfric[((uint64_t)s * L + l) * HH + hh] += fric;
            }
            __syncthreads();
            // Every admitted site's key and current covectors, and the probe's.
            const uint32_t span = to - from;
            for (uint32_t idx = tid; idx < (i + 1) * span; idx += B) {
                const uint32_t j = idx / span, k = from + idx % span;
                const wide gz = fr.pa_z[site0 + j], e = fr.pa_e[site0 + j];
                wide *kk = gk + ((uint64_t)j * N + k) * 2, *ww = gw + ((uint64_t)j * N + k) * 2;
                kk[0] += fit64(rel(gz * fr.pa_probe[(qi * N + k) * 2], scale_bits), &st);
                kk[1] += fit64(rel(gz * fr.pa_probe[(qi * N + k) * 2 + 1], scale_bits), &st);
                ww[0] += fit64(div_nearest(e * gb[2 * k], mass), &st);
                ww[1] += fit64(div_nearest(e * gb[2 * k + 1], mass), &st);
            }
            for (uint32_t k = from + tid; k < to; k += B) {
                wide ar = 0, ai = 0;
                for (uint32_t j = 0; j <= i; j++) {
                    const uint64_t qj = (site0 + j) * L + l;
                    const wide gz = fr.pa_z[site0 + j];
                    ar += gz * fr.pa_key[(qj * N + k) * 2];
                    ai += gz * fr.pa_key[(qj * N + k) * 2 + 1];
                }
                gq[((uint64_t)i * N + k) * 2] += fit64(rel(ar, scale_bits), &st);
                gq[((uint64_t)i * N + k) * 2 + 1] += fit64(rel(ai, scale_bits), &st);
            }
            __syncthreads();
        }
    }
    // Each cell's covectors turned forward by its frame: the six chart covectors and their reaches.
    for (uint32_t j = 0; j < T; j++) {
        const uint64_t qj = (site0 + j) * L + l;
        uint64_t mx[6] = {0, 0, 0, 0, 0, 0};
        for (uint32_t k = tid; k < N; k += B) {
            const wide ur = fr.pa_frame[(qj * N + k) * 2], ui = fr.pa_frame[(qj * N + k) * 2 + 1];
            const wide *src[3] = {gq + ((uint64_t)j * N + k) * 2, gk + ((uint64_t)j * N + k) * 2, gw + ((uint64_t)j * N + k) * 2};
            for (uint32_t c = 0; c < 3; c++) {
                const wide gr = src[c][0], gi = src[c][1];
                const int64_t re = fit64(rel(ur * gr - ui * gi, MOVE_BITS), &st);
                const int64_t im = fit64(rel(ur * gi + ui * gr, MOVE_BITS), &st);
                fr.pa_gchart[(qj * 6 + 2 * c) * N + k] = re;
                fr.pa_gchart[(qj * 6 + 2 * c + 1) * N + k] = im;
                const uint64_t a = magnitude(re), b = magnitude(im);
                mx[2 * c] = a > mx[2 * c] ? a : mx[2 * c];
                mx[2 * c + 1] = b > mx[2 * c + 1] ? b : mx[2 * c + 1];
            }
        }
        for (uint32_t f = 0; f < 6; f++) {
            const uint64_t r = block_max(mx[f], red);
            if (tid == 0) {
                fr.r_pa_g[f * QL + qj] = r;
            }
        }
    }
    __syncthreads();
    if (tid == 0 && st != 0) {
        atomicOr(fr.status + s, st);
    }
}

// The heads' friction covectors summed over the streams, one block a level.
extern "C" __global__ void tower_pa_friction(TowerLaw law, TowerFrame fr) {
    const uint32_t l = blockIdx.x, L = law.levels, HH = law.pa_heads;
    const TowerLevel &lv = law.level[l];
    for (uint32_t hh = threadIdx.x; hh < HH; hh += blockDim.x) {
        wide sum = 0;
        for (uint32_t s = 0; s < law.streams; s++) {
            sum += fr.pa_gfric[((uint64_t)s * L + l) * HH + hh];
        }
        fr.gradient[lv.pa[9] + hh] = sum;
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

// The pair contact's foil: each level's biases b_a, b_b take covectors of their own (dv ⊙ b,
// dv ⊙ a), summed over every cell (integer addition: any order). Entry e is level e / 2F, its
// second bias when (e mod 2F) ≥ F.
extern "C" __global__ void tower_pair_biases(TowerLaw law, TowerFrame fr) {
    const uint32_t F = law.contacts, L = law.levels;
    const uint64_t cells = (uint64_t)law.streams * law.cells;
    for (uint32_t e = blockIdx.x * blockDim.x + threadIdx.x; e < 2 * F * L; e += gridDim.x * blockDim.x) {
        const uint32_t l = e / (2 * F), i = e % F;
        const bool second = e % (2 * F) >= F;
        const int64_t *y = second ? fr.db_bias : fr.da_bias;
        wide acc = 0;
        for (uint64_t q = 0; q < cells; q++) {
            acc += y[(q * L + l) * F + i];
        }
        const TowerLevel &lv = law.level[l];
        fr.gradient[(second ? lv.pair_bias : lv.contact_bias) + i] = acc;
    }
}

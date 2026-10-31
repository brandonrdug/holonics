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
// or its foil (`v = a b_b + b_a (b − b_b)`), with or without the clocked levels' passage credit
// under a news clock (`LevelCredit`: `tower_forward` moves its per-mode moments by each move's
// sub-steps and keeps each cell's turn and coefficients, `tower_credit` sums its material moments in
// closed form, `tower_reverse_modes` and `tower_credit_meet` meet them at the opening), with or
// without the pair face
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
//   memory across the cells. Its `read` is 1 for the opening read, whose cell temporaries are
//   written for the reverse (`keep`), 0 for a reread, and 2 for a reread whose clocked levels tick
//   where the opening read ticked (`Slot::OpeningTicks`), reading the opening's ticks.
// - `tower_reverse_top`, `tower_reverse_ahead`, `tower_reverse_contacts`, `tower_reverse_dx`: one
//   block a cell of a stream (cells are independent there: each reads its own forward temporaries
//   and covector).
// - `tower_split_read`: the paired contacts' split read (`Tower::split_read_of`), one block a
//   dormant pair of one level, over every stream's cells in chunks of the block.
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
// A split read's score term is refused at 2^SCORE_BITS (`split::SCORE_BITS`).
#define SCORE_BITS 48

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
    // The passage's W₁ˣ (F × W) and max |W₁ˣ| (zero without it).
    uint64_t passage, passage_reach;
    // A clocked level's section `B r^(l−F)` on 2^(−20) bits (unread below the clock's first
    // clocked level F and without a clock).
    uint64_t section;
    // The heading (zero without it and below the clock's first clocked level,
    // `Tower::join_heading`): its read C^→ (re, im, W × N), its descent D (W × W) and its descent
    // into the stream D↓ (W × W, zero without the motive, `Tower::join_motive`), and max |w| of each.
    uint64_t heading_re, heading_im, descent, fine_descent, heading_reach[4];
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
    // Each level's words, resident on the card (`[L]`), so the law's parameter words do not grow
    // with the tower's levels.
    const TowerLevel *level;
    // The news clock (`news = 0` without one, every level then moving once a cell): its first
    // clocked level F (the levels below it tick at every arrival; each level's section is in its
    // words) and the clock's period, the coarsest section (`NewsClock`).
    uint32_t news, news_first;
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
    // The mutual contact (`mutual = 0` without it): the readout's place holds its geometry J
    // (W × W), and the face is z_a = release(2⟨y, E_a⟩ − ‖E_a‖², 16 + b) + c_a, y = J x, b the
    // shift (`Tower::join_mutual_contact`).
    uint32_t mutual, mutual_shift;
    // The passage (`passage = 0` without it): every level's contacts read the passing current,
    // `a = W r̂ + W₁ˣ x + b` (`Tower::join_passage`). The packets (`packets = 0` without them;
    // else the clocked levels L − F that carry one, `Tower::join_packets`): a clocked level's push,
    // gate and turn read the ratio of the packet its fine level moved since its last tick.
    uint32_t passage, packets;
    // The split read (`split = 0` without it): the pair contact's reverse keeps each contact's
    // covector δv at its product (`tower_reverse_contacts`), which `tower_split_read` reads
    // against each dormant pair's direction (`holonics::hnn::tower::split`).
    uint32_t split, split_pad;
    // The heading (`heading = 0` without it; else the clocked levels L − F that carry one,
    // `Tower::join_heading`): each clocked level's heading after a cell enters the top through its
    // descent, the face reading it, and a tick's heading is paired with the traces of the stream's
    // ticks at that level in the section, `z_ji = 2^(−heading_shift) ⟨ĥ_j, τ_i⟩` on 2^(−16).
    uint32_t heading, heading_shift;
    // The clocked levels' credit (`credit = 0` without it; else the credited levels L − F,
    // `LevelCredit`, record §22) and whether each credited level below the top carries the moments
    // of the packet its moves carry up (`credit_packet`).
    uint32_t credit, credit_packet;
    // Whether this forward reads the heading's closure (the opening read, or a reread under the
    // declared reading, record §23) and whether it advances the credit (the read a carry keeps; the
    // reverse meets the opening's credit whatever the forward did).
    uint32_t closure, credit_advance;
    // The first credited level (the record's §24: every level's from 0; the clocked levels' from the
    // clock's first clocked level).
    uint32_t credit_from;
    // The motive (`motive = 0` without it, `Tower::join_motive`, record §29): each clocked level's
    // heading before an arrival enters the stream's opening through D↓, x⁰ += D↓ ĥ, and the reverse
    // is the series of the loop through the heading; `term` is the series' term this reverse reads
    // (0 the face's comparison; a later term's sums are added to the earlier terms').
    uint32_t motive;
    uint32_t term, term_pad;
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
    // The transport: each cell's covector of its heads' mean met dissipation ([S][T][H]), and the
    // later sums the modes' scan reads, of each cell's unit-move turn and log₂ ρ ([S][T][N] each).
    wide *pa_gmet, *pa_tturn, *pa_tlog;
    uint64_t *r_pa_read, *r_pa_yre, *r_pa_yim, *r_pa_dra;
    uint64_t *r_pa_g;
    // The sites a stream carries open into the call at each level ([S][L]), each at its place in the section
    // ([S][section][L][N][2] keys and currents, [S][section][L][H] dissipations), uploaded at the
    // opening with the stream's running frame and met dissipation (`pa_run`, `pa_met`).
    const uint32_t *pa_open;
    const int64_t *pa_open_key, *pa_open_value, *pa_open_diss;
    // Each level's held current, uploaded at the opening and carried through the call
    // ([S][L][2N], re block then im block); each level's open section at the call's end, its lead
    // and members ([S][L][2]), and the cells of its members ([S][L][section]), which the reverse
    // rebuilds as it reads them; and, in the reverse, each cell's site at the level returned (zero
    // where the level is still, one at a site, two at a site that closes its section, [S][T]).
    int64_t *pa_hold;
    uint32_t *pa_sect, *pa_member, *pa_mark;
    // The mutual contact (each empty without it): the produced face through it, y = J x on
    // 2^(−16), and its covector G_y on 2^(−24) ([S][T][W] each), and max |G_y| ([S][T]).
    int64_t *contact_y, *contact_gy;
    uint64_t *r_contact_gy;
    // The packets (each empty without them; `PK` the clocked levels L − F that hear one, a level's
    // place among them l − F): each stream's packets before its first cell and after its last
    // ([S][PK][N][2]); each cell's packet as the level that hears it finds it, the fine level's
    // move made and before a tick rests it ([S][T][PK][N][2]); the ratio x̃ = r̂(Re(C a)) a clocked
    // level reads at its tick and its scale ([S][T][PK][W], [S][T][PK]); the packet's face, re
    // block then im block ([S][T][PK][2N]); the reverse's: the covector of x̃ (what the push, gate
    // and turn return, [S][T][PK][W]), its ratio's adjoint ([S][T][PK][W]) and the packet's
    // covector at the tick ([S][T][PK][2N]); and the reaches of x̃, of the face (re, im) and of the
    // adjoint ([S][T][L], so they pair with each level's other reaches in the outer sums).
    const int64_t *pk_open;
    int64_t *pk_ends;
    int64_t *pk_state;
    int32_t *pk_read;
    int64_t *pk_scale;
    int64_t *pk_face;
    int64_t *pk_dx, *pk_dread;
    int64_t *pk_cov;
    uint64_t *r_pk_read, *r_pk_face_re, *r_pk_face_im, *r_pk_dread;
    // The split read (each empty without it): each contact's covector δv on 2^(−24)
    // ([S][T][L][F]); each pair's direction on 2^(−16) ([L][H][W], H = F/2, zero where the pair is
    // founded); and each pair's read: its score, its squares and its turned sum ([L][H][2 + W]).
    int64_t *split_dv;
    const int32_t *split_dir;
    wide *split_out;
    // The heading (each empty without it, `Tower::join_heading`; `HD` its clocked levels): each
    // stream's open traces before its first cell and after its last ([S][HD][W]); each cell's
    // heading ratio before its arrival, which the closure reads ([S][T][HD][W]); the trace a tick
    // closed, its ratio (at the ticks, [S][T][HD][W]); each level's tick cells in order and their
    // count ([S][HD][T], [S][HD]); each tick's closure face e_jj, Σ_i e_ji (low, high words) and
    // max_i z_ji ([S][HD][T][4]); a stream's scratch ([S][T]). The heading after each cell, which the
    // face reads through the descent: its ratio and scale ([S][T][HD][W], [S][T][HD]) and the
    // face it read ([S][T][HD][2N]); the reverse's: its raw read's covector ([S][T][HD][W]) and
    // the top's covector it was read against ([S][T][W]); and the reaches of its ratio, its face
    // (re, im) and its covector ([HD][S][T]) and of the top's covector ([S][T]).
    const int64_t *tr_open;
    int64_t *tr_ends;
    int32_t *hd_read;
    int32_t *tr_read;
    uint32_t *hd_list;
    uint32_t *hd_count;
    uint64_t *hd_close;
    int64_t *hd_g;
    int32_t *ah_read;
    int64_t *ah_scale;
    int64_t *ah_face;
    int64_t *ah_dread, *ah_top;
    uint64_t *r_ah_read, *r_ah_face_re, *r_ah_face_im, *r_ah_dread, *r_ah_top;
    // The clocked levels' credit (each empty without it; `CL` the credited levels L − F, a level's
    // place among them l − F; `LevelCredit`): each stream's credit at the opening and the credit
    // this read advances it to, in its canonical blocks ([S][E], `cr_block`: each credited level's
    // own block, then its packet's; a block push 2NW, along 2N, around 2N, gate bias 2N, gate 2NW,
    // `(re, im)` interleaved); each cell's turn λ^Δτ, push coefficient γ Σ λ^j, gate coefficient
    // Σ λ^(Δτ−j) d⁽ʲ⁾ and the packet's gate coefficient ([S][T][CL][N][2] each; `tower_credit`
    // turns the first into each cell's later turn and the rest into their rows), the input the push
    // and gate read ([S][T][CL][W]) and whether the packet the level carries rested there
    // ([S][T][CL]); and the reverse's opening covectors of the carried modes and packet
    // ([S][CL][2][N][2]).
    const int64_t *cr_open;
    int64_t *cr_next;
    int64_t *cr_turn, *cr_push, *cr_gate, *cr_pgate;
    int32_t *cr_x;
    uint32_t *cr_rest;
    int64_t *cr_cov;
    // Each cell's ticks at each credited level for the read that advances the credit ([S][T][CL];
    // its moves, pushes and states, and the carried packets, are kept in the frame's own buffers for
    // that read, `tower_credit_moments`).
    uint32_t *cr_tick;
    // The motive (each empty without it, `Tower::join_motive`): each clocked level's heading before
    // each cell, its ratio and scale ([S][T][HD][W], [S][T][HD]), and its reach ([HD][S][T]); the
    // carried modes' face at the opening ([S][HD][2N]) and its reaches ([HD][S] re, im); a later
    // term's covector of the heading before the first cell's raw read ([S][HD][W], its reach
    // [HD][S]) and of the carried modes it reaches ([S][HD][N][2]), which the credit meets; and
    // whether a term's source is not zero ([1]).
    int32_t *mo_read;
    int64_t *mo_scale;
    int64_t *mo_face;
    int64_t *mo_dr0;
    int64_t *mo_open;
    uint32_t *mo_flag;
    uint64_t *r_mo_read, *r_mo_face_re, *r_mo_face_im, *r_mo_dr0;
    // The force (record §30): each cell's f = Σ D↓ ĥ ([S][T][W]) with its reach at each level
    // ([S][T][L], what the reads' outer sums pair with each arrival level's push covector), and a
    // term's force covector δf = Σ_(l<F) (C_re γG_re − C_im γG_im) ([S][T][W]) with its reach ([S][T]).
    int64_t *mo_f;
    uint64_t *r_mo_f;
    int64_t *mo_df;
    uint64_t *r_mo_df;
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

// `x / k` to the nearest integer, half away from zero, `k > 0` (`div_nearest`); in 64 bits when the
// rounded magnitude and the divisor fit (the same quotient, record §28).
__device__ __forceinline__ wide div_nearest(wide x, wide k) {
    const wide n = (x >= 0 ? x : -x) + k / 2;
    if (n <= (wide)INT64_MAX && k <= (wide)INT64_MAX) {
        const wide q = (wide)((uint64_t)n / (uint64_t)k);
        return x >= 0 ? q : -q;
    }
    return x >= 0 ? n / k : -(n / k);
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

// The warp's own reductions (every lane of the warp calls them; every lane holds the result).
__device__ int64_t warp_max_signed(int64_t v) {
    uint64_t key = (uint64_t)v ^ ((uint64_t)1 << 63);
    for (int o = 16; o > 0; o >>= 1) {
        const uint64_t w = __shfl_xor_sync(0xffffffffu, key, o);
        key = w > key ? w : key;
    }
    return (int64_t)(key ^ ((uint64_t)1 << 63));
}

// The ring sum of the warp's words (`Z/2^128`, as [`block_sum`]).
__device__ uwide warp_sum(uwide v) {
    for (int o = 16; o > 0; o >>= 1) {
        v += shfl_wide(v, o);
    }
    return v;
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

// The credit's blocks (`LevelCredit`, `Tower::credit_words`): one block's words, the stream's, and
// where credited level `ci`'s own (`set` 0) or packet (`set` 1) block begins.
__device__ __forceinline__ uint64_t cr_block_words(const TowerLaw &law) {
    return 4ull * law.modes * law.width + 6ull * law.modes;
}
// Whether credited level `l`'s moves carry the packet the level above hears, which then carries a
// credit block of its own.
__device__ __forceinline__ bool cr_packet(const TowerLaw &law, uint32_t l) {
    return law.credit_packet && law.packets && l + 1 >= law.news_first && l + 1 < law.levels;
}
// The blocks before credited level `l`'s own: one a credited level below it, and one more for each
// that carries a packet.
__device__ __forceinline__ uint64_t cr_blocks_before(const TowerLaw &law, uint32_t l) {
    uint64_t b = 0;
    for (uint32_t m = law.credit_from; m < l; m++) {
        b += cr_packet(law, m) ? 2 : 1;
    }
    return b;
}
// The packet-carrying credited levels below `l`: a level's place among them indexes the packet's
// gate coefficients, which only they keep; at `l = L` their count.
__device__ __forceinline__ uint32_t cr_packet_index(const TowerLaw &law, uint32_t l) {
    uint32_t p = 0;
    for (uint32_t m = law.credit_from; m < l; m++) {
        p += cr_packet(law, m) ? 1 : 0;
    }
    return p;
}
__device__ __forceinline__ uint64_t cr_stream_words(const TowerLaw &law) {
    return cr_blocks_before(law, law.levels) * cr_block_words(law);
}
__device__ __forceinline__ uint64_t cr_block(const TowerLaw &law, uint32_t s, uint32_t ci, uint32_t set) {
    return s * cr_stream_words(law) + (cr_blocks_before(law, law.credit_from + ci) + set) * cr_block_words(law);
}
// A complex product released to 2^(−30) (`product` in `Tower::advance_moments`).
__device__ __forceinline__ void cmul(wide ar, wide ai, wide br, wide bi, wide *r, wide *i) {
    *r = rel(ar * br - ai * bi, MOVE_BITS);
    *i = rel(ar * bi + ai * br, MOVE_BITS);
}
// The exact product of two 64-bit words (its high word `mul.hi.s64`, record §28).
__device__ __forceinline__ wide mul64(int64_t a, int64_t b) {
    return (wide)(((uwide)(uint64_t)__mul64hi(a, b) << 64) | (uwide)((uint64_t)a * (uint64_t)b));
}
// `cmul` of 64-bit operands.
__device__ __forceinline__ void cmul64(int64_t ar, int64_t ai, int64_t br, int64_t bi, wide *r, wide *i) {
    *r = rel(mul64(ar, br) - mul64(ai, bi), MOVE_BITS);
    *i = rel(mul64(ar, bi) + mul64(ai, br), MOVE_BITS);
}

__device__ __forceinline__ unsigned char *carve(unsigned char *&at, uint64_t octets) {
    unsigned char *p = at;
    at += (octets + 15) & ~(uint64_t)15;
    return p;
}

// Two blocks a multiprocessor (record §25): the stage's shared memory admits two, and the credit's
// arithmetic would otherwise take every register and halve the streams in flight.
extern "C" __global__ void __launch_bounds__(TOWER_THREADS, 2) tower_forward(TowerLaw law, TowerFrame fr, uint32_t read) {
    const uint32_t keep = read == 1, opening_ticks = read == 2;
    // The credit's advance (`tower_credit` sums it at the carry) and the closure's read.
    const bool advancing = law.credit && law.credit_advance;
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
    // The mutual contact's produced face y = J x.
    int64_t *yc = (int64_t *)carve(at, 8ull * W * (law.mutual != 0));
    // Each level's ticks at the arriving class; participation's open section at each level: the
    // sites carried open into the call that it still reads (`lead`, zero once the level's section
    // has closed in the call) and the sites it has admitted since, whose cells `pa_member` lists;
    // and each level's swell, the maxima the opening read keeps (`[L][4]`).
    uint32_t *tk = (uint32_t *)carve(at, 4ull * L);
    uint32_t *pa_lead = (uint32_t *)carve(at, 4ull * L);
    uint32_t *pa_members = (uint32_t *)carve(at, 4ull * L);
    uint64_t *sw = (uint64_t *)carve(at, 8ull * 4 * L);
    // The packets (`Tower::join_packets`): each clocked level's open packet from F up, on the modes'
    // grain, and the ratio x̃ = r̂(Re(C_(l−1) a)) a level reads at its tick. Under a news clock
    // without participation, each level's read as it was last computed (`hrd`; its face maxima,
    // scale and read maximum in `hv`): a level's state moves only at its ticks, so between them
    // its face and read stand, and the level computes only its contacts.
    const uint32_t F0 = law.news_first, PK = law.packets;
    int64_t *pk = (int64_t *)carve(at, 8ull * PK * 2 * N);
    int32_t *xp = (int32_t *)carve(at, 4ull * W * (PK > 0));
    const uint32_t HOLD = law.news != 0 && P == 0;
    int32_t *hrd = (int32_t *)carve(at, 4ull * L * W * HOLD);
    uint64_t *hv = (uint64_t *)carve(at, 8ull * 4 * L * HOLD);
    uint32_t *hready = (uint32_t *)carve(at, 4ull * L * HOLD);
    // The heading (`Tower::join_heading`): each clocked level's open trace on the face's 2^(−16)
    // and its ticks in the section so far.
    const uint32_t HD = law.heading;
    int64_t *tro = (int64_t *)carve(at, 8ull * HD * W);
    uint32_t *hc = (uint32_t *)carve(at, 4ull * HD);
    // The heading each clocked level holds between its ticks (record §19): its ratio, its lift
    // through the descent, and its face's maxima, scale and ratio maximum (`hh_v`); `hh` is 0 with
    // nothing held, 1 with the ratio held, 2 with the lift held too.
    int32_t *hh_rd = (int32_t *)carve(at, 4ull * HD * W);
    int64_t *hh_lift = (int64_t *)carve(at, 8ull * HD * W);
    uint64_t *hh_v = (uint64_t *)carve(at, 8ull * 4 * HD);
    uint32_t *hh = (uint32_t *)carve(at, 4ull * HD);
    // The motive (`Tower::join_motive`): each clocked level's lift into the stream's opening,
    // D↓ ĥ, held while its heading stands.
    const uint32_t MO = law.motive != 0 ? 1 : 0;
    int64_t *hm_lift = (int64_t *)carve(at, 8ull * HD * W * MO);
    // The force the arrival levels' pushes read at this cell, f = Σ_l D↓_l ĥ_l (record §30).
    int64_t *mf = (int64_t *)carve(at, 8ull * W * MO);
    __shared__ uint64_t mf_max;
    __shared__ uint32_t st;
    __shared__ int64_t scale_s;
    __shared__ wide ring_lam[4];
    // The news clock: the open face (its masses in `ms`, its total, whether there is one) and the
    // clock's phase.
    __shared__ uwide news_total;
    __shared__ uint64_t news_phase;
    __shared__ uint32_t news_has;
    if (tid == 0) {
        st = 0;
        for (uint32_t l = 0; l < L; l++) {
            tk[l] = 1;
            pa_lead[l] = P ? fr.pa_open[(uint64_t)s * L + l] : 0;
            pa_members[l] = 0;
            if (HOLD) {
                hready[l] = 0;
            }
            for (uint32_t i = 0; i < 4; i++) {
                sw[l * 4 + i] = 0;
            }
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
    for (uint32_t i = tid; i < PK * 2 * N; i += B) {
        pk[i] = fr.pk_open[(uint64_t)s * PK * 2 * N + i];
    }
    for (uint32_t i = tid; i < HD * W; i += B) {
        tro[i] = fr.tr_open[(uint64_t)s * HD * W + i];
    }
    for (uint32_t i = tid; i < HD; i += B) {
        hc[i] = 0;
        hh[i] = 0;
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
    const int32_t *th = fr.theta;
    const int32_t *tt = fr.theta_t;
    const uint64_t *face_roots = fr.roots;
    const uint64_t *move_roots = fr.roots + law.face_digits;
    const wide radius = ((wide)1 << MOVE_BITS) - ((wide)1 << (MOVE_BITS - MARGIN));
    // The heading a clocked level holds (`Tower::join_heading`), read from its modes in `h`: their
    // face on 2^(−16) into `fc` (re block, then im block) with its maxima, the raw read
    // Re(C^→ h) = C^→_re h_re − C^→_im h_im on 2^(−40) released to 2^(−16), and its ratio
    // ĥ = r̂(Re(C^→ h)) into `rd`, complete for every thread at the return; returns its scale.
    const auto heading_read = [&](uint32_t l, uint64_t &fre, uint64_t &fim) -> int64_t {
        const TowerLevel lv = law.level[l];
        uint64_t mre = 0, mim = 0;
        for (uint32_t k = tid; k < N; k += B) {
            fc[k] = fit64(rel(h[(l * N + k) * 2], STATE_BITS - FACE_BITS), &st);
            fc[N + k] = fit64(rel(h[(l * N + k) * 2 + 1], STATE_BITS - FACE_BITS), &st);
            const uint64_t ma = magnitude(fc[k]), mb = magnitude(fc[N + k]);
            mre = ma > mre ? ma : mre;
            mim = mb > mim ? mb : mim;
        }
        fre = block_max(mre, red);
        fim = block_max(mim, red);
        const bool n_a = narrow_terms(lv.heading_reach[0], fre, N, &st);
        const bool n_b = narrow_terms(lv.heading_reach[1], fim, N, &st);
        for (uint32_t o = tid; o < 2 * W; o += B) {
            const uint32_t j = o % W;
            const bool im = o >= W;
            rab[o] = fit64(dot(tt + (im ? lv.heading_im : lv.heading_re) + j, W, N, fc + (im ? N : 0), im ? n_b : n_a), &st);
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
        const int64_t hscale = scale_s;
        for (uint32_t j = tid; j < W; j += B) {
            rd[j] = hscale == 0 ? 0 : fit32(div_nearest((wide)raw[j] << FACE_BITS, hscale), &st);
        }
        __syncthreads();
        return hscale;
    };
    // The heading a clocked level holds (record §19): its state has not moved since the heading was
    // read, so the ratio, scale and maxima stand, and its face is released from the standing state
    // into `fc` as `heading_read` releases it; returns its scale.
    const auto heading_held = [&](uint32_t l, uint32_t i, uint64_t &fre, uint64_t &fim) -> int64_t {
        for (uint32_t k = tid; k < N; k += B) {
            fc[k] = fit64(rel(h[(l * N + k) * 2], STATE_BITS - FACE_BITS), &st);
            fc[N + k] = fit64(rel(h[(l * N + k) * 2 + 1], STATE_BITS - FACE_BITS), &st);
        }
        for (uint32_t j = tid; j < W; j += B) {
            rd[j] = hh_rd[(uint64_t)i * W + j];
        }
        fre = hh_v[i * 4];
        fim = hh_v[i * 4 + 1];
        __syncthreads();
        return (int64_t)hh_v[i * 4 + 2];
    };
    // Hold the heading `heading_read` has just read for the `i`th clocked level.
    const auto heading_keep = [&](uint32_t i, uint64_t fre, uint64_t fim, int64_t hscale) {
        for (uint32_t j = tid; j < W; j += B) {
            hh_rd[(uint64_t)i * W + j] = rd[j];
        }
        if (tid == 0) {
            hh_v[i * 4] = fre;
            hh_v[i * 4 + 1] = fim;
            hh_v[i * 4 + 2] = (uint64_t)hscale;
            hh[i] = 1;
        }
    };
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
                for (uint32_t l = 1; l < L; l++) {
                    // The levels below the first clocked level tick at every arrival.
                    if (l < law.news_first) {
                        tk[l] = 1;
                        continue;
                    }
                    const uint64_t section = law.level[l].section;
                    const uint64_t advanced = section == 0 ? 0 : sum / section - news_phase / section;
                    if (section == 0 || advanced > UINT32_MAX) {
                        atomicOr(&st, TOWER_REFUSED_NEWS);
                    }
                    tk[l] = advanced > UINT32_MAX ? 0 : (uint32_t)advanced;
                    // A reread on the opening's ticks: the level ticks where the opening read did.
                    if (opening_ticks) {
                        tk[l] = fr.ticks[qc * L + l];
                    }
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
        // The heading (`Tower::join_heading`): each clocked level's heading, read from its modes
        // before this arrival, ĥ_l = r̂(Re(C^→_l h_l)), is what its closure compares at a tick; the
        // arrival's encoded face joins each clocked level's open trace, and a tick of the level
        // closes the trace, τ_l = r̂(o_l), rests it and lists the tick for the section's closure.
        // The heading's ratio and the trace are kept at every read (the closure reads them at the
        // section's end). The heading before this arrival is the one the level held after the last
        // cell (`ĥ_l(t) = ĥ⁺_l(t−1)`, record §19); it is read only at the forward's opening.
        for (uint32_t i = 0; i < HD; i++) {
            const uint32_t l = law.news_first + i;
            const uint64_t qh = qc * HD + i;
            uint64_t fre = 0, fim = 0;
            int64_t bscale;
            if (hh[i] != 0) {
                bscale = heading_held(l, i, fre, fim);
            } else {
                bscale = heading_read(l, fre, fim);
                heading_keep(i, fre, fim, bscale);
            }
            // The motive (`Tower::join_motive`, record §29): the stream's opening reads the heading
            // before this arrival through D↓, x⁰ += D↓ ĥ on 2^(−40) released to 2^(−16), the lift
            // read at the forward's opening and after each cell at which the level ticked, and held
            // between (record §19).
            if (MO) {
                const TowerLevel lv = law.level[l];
                uint64_t mx = 0;
                for (uint32_t j = tid; j < W; j += B) {
                    const uint64_t v = magnitude(rd[j]);
                    mx = v > mx ? v : mx;
                }
                const uint64_t bmax = block_max(mx, red);
                if (t == 0) {
                    const bool n_f = narrow_terms(lv.heading_reach[3], bmax, W, &st);
                    for (uint32_t j = tid; j < W; j += B) {
                        hm_lift[(uint64_t)i * W + j] = fit64(rel(dot(th + lv.fine_descent + (uint64_t)j * W, 1, W, rd, n_f), MATERIAL_BITS), &st);
                    }
                }
                if (keep) {
                    for (uint32_t j = tid; j < W; j += B) {
                        fr.mo_read[qh * W + j] = rd[j];
                    }
                    if (tid == 0) {
                        fr.mo_scale[qh] = bscale;
                        fr.r_mo_read[(uint64_t)i * law.streams * T + qc] = bmax;
                    }
                    if (t == 0) {
                        for (uint32_t o = tid; o < 2 * N; o += B) {
                            fr.mo_face[((uint64_t)s * HD + i) * 2 * N + o] = fc[o];
                        }
                        if (tid == 0) {
                            fr.r_mo_face_re[(uint64_t)i * law.streams + s] = fre;
                            fr.r_mo_face_im[(uint64_t)i * law.streams + s] = fim;
                        }
                    }
                }
                __syncthreads();
            }
            if (law.closure) {
                for (uint32_t j = tid; j < W; j += B) {
                    fr.hd_read[qh * W + j] = rd[j];
                }
            }
            int64_t *open = tro + (uint64_t)i * W;
            for (uint32_t j = tid; j < W; j += B) {
                open[j] = fit64((wide)open[j] + (wide)th[law.encoding + (uint64_t)u * W + j], &st);
            }
            if (tk[l] > 0 && !law.closure) {
                // A tick closes the span and rests its trace; only the closure reads the trace.
                for (uint32_t j = tid; j < W; j += B) {
                    open[j] = 0;
                }
            } else if (tk[l] > 0) {
                uwide tp = 0;
                for (uint32_t j = tid; j < W; j += B) {
                    tp += (uwide)((wide)open[j] * (wide)open[j]);
                }
                tp = block_sum(tp, redw);
                if (tid == 0) {
                    const uwide root = isqrt128((uwide)((wide)tp / (wide)W));
                    if (root > (uwide)INT64_MAX) {
                        atomicOr(&st, TOWER_REFUSED_WORD64);
                    }
                    scale_s = root > (uwide)INT64_MAX ? 0 : (int64_t)root;
                }
                __syncthreads();
                const int64_t tscale = scale_s;
                for (uint32_t j = tid; j < W; j += B) {
                    fr.tr_read[qh * W + j] = tscale == 0 ? 0 : fit32(div_nearest((wide)open[j] << FACE_BITS, tscale), &st);
                    open[j] = 0;
                }
                if (tid == 0) {
                    fr.hd_list[((uint64_t)s * HD + i) * T + hc[i]] = t;
                    hc[i] += 1;
                }
            }
            __syncthreads();
        }
        // The motive's force at this cell (record §30): the lifts summed level by level, each released
        // as the host releases it; each arrival level's push reads it through its read's adjoint.
        if (MO) {
            uint64_t mx = 0;
            for (uint32_t j = tid; j < W; j += B) {
                wide f = 0;
                for (uint32_t i = 0; i < HD; i++) {
                    f = fit64(f + (wide)hm_lift[(uint64_t)i * W + j], &st);
                }
                mf[j] = (int64_t)f;
                const uint64_t a = magnitude(mf[j]);
                mx = a > mx ? a : mx;
            }
            const uint64_t fmax = block_max(mx, red);
            if (tid == 0) {
                mf_max = fmax;
            }
            if (keep) {
                for (uint32_t j = tid; j < W; j += B) {
                    fr.mo_f[qc * W + j] = mf[j];
                }
                for (uint32_t l = tid; l < L; l += B) {
                    fr.r_mo_f[qc * L + l] = fmax;
                }
            }
            __syncthreads();
        }
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
            const TowerLevel lv = law.level[l];
            const uint64_t q = qc * L + l;
            const bool ringed = R > 0 && l == law.ring_level;
            // The ring's carried face before the move, each mode's (re, im) on 2^(−16)
            // (`carried_face`).
            if (ringed) {
                for (uint32_t i = tid; i < 2 * N; i += B) {
                    rs[i] = fit64(rel(h[l * 2 * N + i], STATE_BITS - FACE_BITS), &st);
                }
            }
            // An arrival that ticks the level no time moves nothing (`NewsClock`): its push, gate
            // and turn are not read, and its state, face and read stand as at its last tick.
            const bool still = law.news && tk[l] == 0;
            const bool held_read = HOLD && still && hready[l] != 0;
            // The packet (`Tower::join_packets`): at a tick of a level that hears one, its push,
            // gate and turn read the packet the fine level's moves left since its last tick,
            // x̃ = r̂(Re(C_(l−1) a)) through the fine level's own read, and the packet rests;
            // elsewhere they read the passing current. Its face takes `fc` until the modes' move.
            const int32_t *xin = x;
            uint64_t xinmax = xmax;
            if (PK > 0 && l >= F0) {
                int64_t *a = pk + (uint64_t)(l - F0) * 2 * N;
                // The level's place among those that hear a packet.
                const uint64_t qp = qc * PK + (l - F0);
                uint64_t mre = 0, mim = 0;
                // The packet as this level finds it is kept for the read that advances the credit of
                // the fine level that carries it (`tower_credit_moments`).
                const bool credited_packet = advancing && l - 1 >= law.credit_from && cr_packet(law, l - 1);
                for (uint32_t k = tid; k < N; k += B) {
                    if (keep || credited_packet) {
                        fr.pk_state[(qp * N + k) * 2] = a[2 * k];
                        fr.pk_state[(qp * N + k) * 2 + 1] = a[2 * k + 1];
                    }
                    if (!still) {
                        fc[k] = fit64(rel(a[2 * k], STATE_BITS - FACE_BITS), &st);
                        fc[N + k] = fit64(rel(a[2 * k + 1], STATE_BITS - FACE_BITS), &st);
                        const uint64_t ma = magnitude(fc[k]), mb = magnitude(fc[N + k]);
                        mre = ma > mre ? ma : mre;
                        mim = mb > mim ? mb : mim;
                        a[2 * k] = 0;
                        a[2 * k + 1] = 0;
                    }
                }
                if (!still) {
                    const uint64_t pre = block_max(mre, red);
                    const uint64_t pim = block_max(mim, red);
                    const TowerLevel lf = law.level[l - 1];
                    const bool n_pa = narrow_terms(lf.reach[2], pre, N, &st);
                    const bool n_pb = narrow_terms(lf.reach[3], pim, N, &st);
                    for (uint32_t o = tid; o < 2 * W; o += B) {
                        const uint32_t j = o % W;
                        const bool im = o >= W;
                        rab[o] = fit64(dot(tt + (im ? lf.read_im : lf.read_re) + j, W, N, fc + (im ? N : 0), im ? n_pb : n_pa), &st);
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
                    const int64_t pscale = scale_s;
                    uint64_t mx = 0;
                    for (uint32_t j = tid; j < W; j += B) {
                        xp[j] = pscale == 0 ? 0 : fit32(div_nearest((wide)raw[j] << FACE_BITS, pscale), &st);
                        const uint64_t v = magnitude(xp[j]);
                        mx = v > mx ? v : mx;
                    }
                    xinmax = block_max(mx, red);
                    xin = xp;
                    if (keep) {
                        for (uint32_t j = tid; j < W; j += B) {
                            fr.pk_read[qp * W + j] = xp[j];
                        }
                        for (uint32_t i = tid; i < 2 * N; i += B) {
                            fr.pk_face[qp * 2 * N + i] = fc[i];
                        }
                        if (tid == 0) {
                            fr.pk_scale[qp] = pscale;
                            fr.r_pk_read[q] = xinmax;
                            fr.r_pk_face_re[q] = pre;
                            fr.r_pk_face_im[q] = pim;
                        }
                    }
                } else if (keep) {
                    for (uint32_t j = tid; j < W; j += B) {
                        fr.pk_read[qp * W + j] = 0;
                    }
                    for (uint32_t i = tid; i < 2 * N; i += B) {
                        fr.pk_face[qp * 2 * N + i] = 0;
                    }
                    if (tid == 0) {
                        fr.pk_scale[qp] = 0;
                        fr.r_pk_read[q] = 0;
                        fr.r_pk_face_re[q] = 0;
                        fr.r_pk_face_im[q] = 0;
                    }
                }
            }
            // The input the credited level's push and gate read at this cell (`tower_credit`).
            if (advancing && l >= law.credit_from) {
                const uint64_t qx = qc * law.credit + (l - law.credit_from);
                for (uint32_t j = tid; j < W; j += B) {
                    fr.cr_x[qx * W + j] = still ? 0 : xin[j];
                }
                if (tid == 0) {
                    fr.cr_tick[qx] = tk[l];
                }
            }
            // The pushes on 2^(−40) released to the state's 2^(−24), and the gate's logit.
            const bool n_re = !still && narrow_terms(lv.reach[0], xinmax, W, &st);
            const bool n_im = !still && narrow_terms(lv.reach[1], xinmax, W, &st);
            const bool n_gate = !still && narrow_terms(lv.reach[6], xinmax, W, &st);
            const bool n_turn = !still && law.turned && narrow_terms(lv.reach[7], xinmax, W, &st);
            const bool n_depth = !still && law.pumped && narrow_terms(lv.reach[8], xinmax, W, &st);
            const bool n_axis = !still && law.pumped && narrow_terms(lv.reach[9], xinmax, W, &st);
            // A turned level's arriving turn s_t = 2^(−spread) (W_φ x + b_φ), in half turns on
            // 2^(−16), beside the gate's logit; a pumped level's depth logit W_κ x + b_κ on
            // 2^(−16) and its axis p_t = 2^(−spread) (W_ψ x + b_ψ) in half turns on 2^(−16).
            for (uint32_t o = tid; o < FAMS * N && !still; o += B) {
                const uint32_t fam = o / N, k = o % N;
                if (fam == 2) {
                    wide sum = dot(tt + lv.gate + k, N, W, xin, n_gate);
                    sum += (wide)th[lv.gate_bias + k] << MATERIAL_BITS;
                    pq[o] = fit64(rel(sum, MATERIAL_BITS), &st);
                } else if (fam == 4) {
                    wide sum = dot(tt + lv.pump + k, N, W, xin, n_depth);
                    sum += (wide)th[lv.pump_bias + k] << MATERIAL_BITS;
                    pq[o] = fit64(rel(sum, MATERIAL_BITS), &st);
                } else if (fam == 3 || fam == 5) {
                    const bool axis = fam == 5;
                    wide sum = dot(tt + (axis ? lv.pump_axis : lv.turn) + k, N, W, xin, axis ? n_axis : n_turn);
                    sum += (wide)th[(axis ? lv.pump_axis_bias : lv.turn_bias) + k] << MATERIAL_BITS;
                    const int64_t turn = fit64(rel(sum, MATERIAL_BITS), &st);
                    pq[o] = fit64(rel((wide)turn, law.turn_spread), &st);
                } else {
                    const wide sum = dot(tt + (fam == 0 ? lv.push_re : lv.push_im) + k, N, W, xin, fam == 0 ? n_re : n_im);
                    int64_t p = fit64(rel(sum, MATERIAL_BITS + FACE_BITS - STATE_BITS), &st);
                    // The force at an arrival level (record §30): p += C̄ᵀ f, (C_reᵀ f, −C_imᵀ f).
                    if (MO && l < law.news_first) {
                        const bool n_f = narrow_rows(fam == 0 ? lv.reach[2] : lv.reach[3], mf_max, W);
                        const wide fsum = dot(th + (fam == 0 ? lv.read_re : lv.read_im) + k, N, W, mf, n_f);
                        p = fit64((wide)p + (wide)fit64(rel(fam == 0 ? fsum : -fsum, MATERIAL_BITS + FACE_BITS - STATE_BITS), &st), &st);
                    }
                    pq[o] = p;
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
                // A still level's state stands (a news clock carries no rotor, ring or pump); its
                // push and moves rest at zero, as the host's empty gate.
                if (still) {
                    const int64_t nr = h[(l * N + k) * 2], ni = h[(l * N + k) * 2 + 1];
                    fc[k] = fit64(rel(nr, STATE_BITS - FACE_BITS), &st);
                    fc[N + k] = fit64(rel(ni, STATE_BITS - FACE_BITS), &st);
                    // The read that advances a credited level's credit keeps its state for
                    // `tower_credit_moments` (a still cell moves no moment).
                    if (!keep && advancing && l >= law.credit_from) {
                        fr.state[(q * N + k) * 2] = nr;
                        fr.state[(q * N + k) * 2 + 1] = ni;
                    }
                    if (keep) {
                        fr.push[q * 2 * N + k] = 0;
                        fr.push[q * 2 * N + N + k] = 0;
                        fr.state[(q * N + k) * 2] = nr;
                        fr.state[(q * N + k) * 2 + 1] = ni;
                        fr.face[q * 2 * N + k] = fc[k];
                        fr.face[q * 2 * N + N + k] = fc[N + k];
                        int64_t *mv = fr.moves + (q * N + k) * 6;
                        for (uint32_t i = 0; i < 6; i++) {
                            mv[i] = 0;
                        }
                        if (law.turned) {
                            fr.units[(q * N + k) * 2] = 0;
                            fr.units[(q * N + k) * 2 + 1] = 0;
                        }
                    }
                    continue;
                }
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
                // The packet the next level hears moves with this level's step, from rest since
                // that level's last tick (`Tower::join_packets`).
                if (PK > 0 && l + 1 >= F0 && l + 1 < L) {
                    int64_t *a = pk + ((uint64_t)(l + 1 - F0) * N + k) * 2;
                    wide ar = a[0], ai = a[1];
                    for (uint32_t j = 0; j < tk[l]; j++) {
                        const wide nr_ = rel(lr * ar - li * ai + br * ar + bi * ai, MOVE_BITS);
                        ai = fit64(rel(lr * ai + li * ar + bi * ar - br * ai, MOVE_BITS) + pi, &st);
                        ar = fit64(nr_ + pr, &st);
                    }
                    a[0] = (int64_t)ar;
                    a[1] = (int64_t)ai;
                }
                if (ringed && k == law.ring_mode) {
                    ring_lam[0] = lr;
                    ring_lam[1] = li;
                    ring_lam[2] = br;
                    ring_lam[3] = bi;
                }
                fc[k] = fit64(rel(nr, STATE_BITS - FACE_BITS), &st);
                fc[N + k] = fit64(rel(ni, STATE_BITS - FACE_BITS), &st);
                // The read that advances a credited level's credit keeps its push, state and move
                // for `tower_credit_moments`.
                if (!keep && advancing && l >= law.credit_from) {
                    fr.push[q * 2 * N + k] = pq[k];
                    fr.push[q * 2 * N + N + k] = pq[N + k];
                    fr.state[(q * N + k) * 2] = nr;
                    fr.state[(q * N + k) * 2 + 1] = ni;
                    int64_t *mv = fr.moves + (q * N + k) * 6;
                    mv[0] = (int64_t)open;
                    mv[1] = (int64_t)rho;
                    mv[2] = (int64_t)gamma;
                    mv[3] = (int64_t)lr;
                    mv[4] = (int64_t)li;
                    mv[5] = held ? 1 : 0;
                }
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
            uint64_t fre, fim, rmax;
            int64_t scale;
            if (held_read) {
                // A still level's read stands as last computed (its state has not moved since).
                for (uint32_t j = tid; j < W; j += B) {
                    rd[j] = hrd[(uint64_t)l * W + j];
                }
                fre = hv[l * 4];
                fim = hv[l * 4 + 1];
                scale = (int64_t)hv[l * 4 + 2];
                rmax = hv[l * 4 + 3];
                __syncthreads();
            } else {
                uint64_t mre = 0, mim = 0;
                for (uint32_t k = tid; k < N; k += B) {
                    const uint64_t a = magnitude(fc[k]), b = magnitude(fc[N + k]);
                    mre = a > mre ? a : mre;
                    mim = b > mim ? b : mim;
                }
                fre = block_max(mre, red);
                fim = block_max(mim, red);
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
                scale = scale_s;
                m = 0;
                for (uint32_t j = tid; j < W; j += B) {
                    rd[j] = scale == 0 ? 0 : fit32(div_nearest((wide)raw[j] << FACE_BITS, scale), &st);
                    const uint64_t v = magnitude(rd[j]);
                    m = v > m ? v : m;
                }
                rmax = block_max(m, red);
                if (HOLD) {
                    for (uint32_t j = tid; j < W; j += B) {
                        hrd[(uint64_t)l * W + j] = rd[j];
                    }
                    if (tid == 0) {
                        hv[l * 4] = fre;
                        hv[l * 4 + 1] = fim;
                        hv[l * 4 + 2] = (uint64_t)scale;
                        hv[l * 4 + 3] = rmax;
                        hready[l] = 1;
                    }
                }
            }
            // Participation (`Tower::step`, `participation`): at each tick of the level's clock
            // (every arrival without a news clock) the cell's move advances each mode's frame and
            // met dissipation as often as it acts (from rest at the section's opening), the level's
            // input presents its rotated charts as the section's newest site and probes every
            // admitted site head by head (the Gibbs face of the pairing less the friction, carried
            // as the integer (mass, current) pair), and the current is read like the modes' face,
            // its ratio read offered to the contacts through W₁ᵃ. An arrival that ticks no time
            // admits no site and reads the current held from the level's last site (record
            // `2026-10-29_A_COARSE_LEVELS_SITES_ARE_ITS_OWN_TICKS…`).
            uint64_t prmax = 0;
            if (P) {
                const uint32_t moves = tk[l];
                int64_t *hold = fr.pa_hold + ((uint64_t)s * L + l) * 2 * N;
                const uint32_t lead = pa_lead[l], members = pa_members[l], place = lead + members;
                uint32_t *member = fr.pa_member + ((uint64_t)s * L + l) * law.pa_section;
                if (moves == 0) {
                    for (uint32_t k = tid; k < 2 * N; k += B) {
                        py[k] = hold[k];
                    }
                } else {
                for (uint32_t o = tid; o < 6 * N; o += B) {
                    const uint32_t fam = o / N, k = o % N;
                    const bool nar = narrow_terms(lv.pa_reach[fam], xmax, W, &st);
                    pcs[o] = fit64(rel(dot(tt + lv.pa[fam] + k, N, W, x, nar), MATERIAL_BITS), &st);
                }
                __syncthreads();
                // The cell's place in its section: after the sites the stream carried open into
                // the call (until the level's section closes) and the sites admitted since, so a
                // section read across calls runs on as one. The move acted `Δτ` times, so the
                // frame turns and the dissipation meets it as often.
                if (tid == 0) {
                    member[members] = t;
                }
                for (uint32_t k = tid; k < N; k += B) {
                    int64_t *run = fr.pa_run + (((uint64_t)s * L + l) * N + k) * 2;
                    int64_t *met = fr.pa_met + ((uint64_t)s * L + l) * N + k;
                    wide fre_ = place == 0 ? ((wide)1 << MOVE_BITS) : (wide)run[0];
                    wide fim_ = place == 0 ? 0 : (wide)run[1];
                    const int64_t mt = fit64((wide)(place == 0 ? 0 : *met) - (wide)moves * pl[k], &st);
                    const wide ur = pu[2 * k], ui = pu[2 * k + 1];
                    for (uint32_t j = 1; j < moves; j++) {
                        const wide ar = fit64(rel(fre_ * ur - fim_ * ui, MOVE_BITS), &st);
                        fim_ = fit64(rel(fre_ * ui + fim_ * ur, MOVE_BITS), &st);
                        fre_ = ar;
                    }
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
                // Site j of the section: carried open into the call (j < lead) at its place, else
                // read at the cell `pa_member` lists for it. One warp a head, the warps taking the
                // heads in turn, so the heads read together: each lane takes every 32nd admitted
                // site and the face's peak, the mass and each mode's current are warp reductions
                // (integer sums, the same in any order). A head's faces and weights take its own row.
                const uint64_t site0 = (uint64_t)s * T, row = (uint64_t)s * law.pa_section;
                const uint32_t lane = tid & 31, warps = B >> 5;
                const uint64_t stride = T > law.pa_section ? T : law.pa_section;
                for (uint32_t hh = tid >> 5; hh < HH; hh += warps) {
                    const uint32_t from = fr.pa_heads[hh], to = fr.pa_heads[hh + 1];
                    const wide friction = th[lv.pa[9] + hh];
                    int64_t *zrow = fr.pa_z + ((uint64_t)s * HH + hh) * stride;
                    uint64_t *erow = fr.pa_e + ((uint64_t)s * HH + hh) * stride;
                    int64_t zm = INT64_MIN;
                    for (uint32_t j = lane; j <= place; j += 32) {
                        const bool carried = j < lead;
                        const uint64_t qj = (carried ? row + j : site0 + member[j - lead]) * L + l;
                        const int64_t *keys = carried ? fr.pa_open_key : fr.pa_key;
                        wide pairing = 0;
                        for (uint32_t k = from; k < to; k++) {
                            const int64_t *kj = keys + (qj * N + k) * 2;
                            pairing += (wide)ppr[2 * k] * kj[0] + (wide)ppr[2 * k + 1] * kj[1];
                        }
                        const wide met = (wide)pdis[hh] - (wide)(carried ? fr.pa_open_diss : fr.pa_diss)[qj * HH + hh];
                        const int64_t z = fit64(rel(pairing, FACE_BITS + law.pa_beta) - rel(friction * met, FACE_BITS), &st);
                        zrow[j] = z;
                        zm = z > zm ? z : zm;
                    }
                    const int64_t peak = warp_max_signed(zm);
                    uwide msum = 0;
                    for (uint32_t j = lane; j <= place; j += 32) {
                        const int64_t z = zrow[j];
                        const uint64_t e = (wide)peak - (wide)z >= ((wide)UNIT_BITS << FACE_BITS) ? 0 : below_one((wide)z - (wide)peak, face_roots, law.face_digits);
                        erow[j] = e;
                        msum += e;
                    }
                    const uwide mass = warp_sum(msum);
                    __syncwarp();
                    for (uint32_t k = from; k < to; k++) {
                        wide jr = 0, ji = 0;
                        for (uint32_t j = lane; j <= place; j += 32) {
                            const bool carried = j < lead;
                            const uint64_t qj = (carried ? row + j : site0 + member[j - lead]) * L + l;
                            const int64_t *values = carried ? fr.pa_open_value : fr.pa_value;
                            const wide e = (wide)erow[j];
                            jr += e * values[(qj * N + k) * 2];
                            ji += e * values[(qj * N + k) * 2 + 1];
                        }
                        jr = (wide)warp_sum((uwide)jr);
                        ji = (wide)warp_sum((uwide)ji);
                        if (lane == 0) {
                            const wide mr = fit64(div_nearest(jr, (wide)mass), &st), mi = fit64(div_nearest(ji, (wide)mass), &st);
                            const wide ur = pfr[2 * k], ui = pfr[2 * k + 1];
                            py[k] = fit64(rel(ur * mr - ui * mi, MOVE_BITS), &st);
                            py[N + k] = fit64(rel(ur * mi + ui * mr, MOVE_BITS), &st);
                        }
                    }
                    __syncwarp();
                }
                __syncthreads();
                // Under a news clock the current is held through the arrivals that tick no time
                // (without one every arrival ticks and nothing is held). The section closes with its
                // last site: its sites are released and its frames rest, so the level's next tick
                // opens the next section.
                if (law.news) {
                    for (uint32_t k = tid; k < 2 * N; k += B) {
                        hold[k] = py[k];
                    }
                }
                if (tid == 0) {
                    const bool closes = place + 1 >= law.pa_section;
                    pa_lead[l] = closes ? 0 : lead;
                    pa_members[l] = closes ? 0 : members + 1;
                }
                }
                __syncthreads();
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
                        fr.pa_probe[(q * N + k) * 2] = moves == 0 ? 0 : ppr[2 * k];
                        fr.pa_probe[(q * N + k) * 2 + 1] = moves == 0 ? 0 : ppr[2 * k + 1];
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
            const bool hears = law.passage != 0 && l >= law.news_first;
            const bool n_x = hears && narrow_terms(lv.passage_reach, xmax, W, &st);
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
                // The passage: the contacts meet the current passing the level, W₁ˣ x released on
                // its own.
                if (hears) {
                    a64 = fit64((wide)a64 + (wide)fit64(rel(dot(tt + lv.passage + o, F, W, x, n_x), MATERIAL_BITS), &st), &st);
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
            if (tid == 0) {
                const uint64_t fmax = fre > fim ? fre : fim;
                uint64_t *sl = sw + l * 4;
                sl[0] = xmax > sl[0] ? xmax : sl[0];
                sl[1] = fmax > sl[1] ? fmax : sl[1];
                sl[2] = (uint64_t)scale > sl[2] ? (uint64_t)scale : sl[2];
                sl[3] = dmax > sl[3] ? dmax : sl[3];
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
        // The face reads each clocked level's heading after the arrival (`Tower::join_heading`):
        // ĥ⁺_l = r̂(Re(C^→_l h_l)) read from the level's modes after the cell, the heading it holds
        // for the arrival the face predicts, enters the top through its descent,
        // x += D_l ĥ⁺_l on 2^(−40) released to 2^(−16), in level order. A level the arrival ticked
        // no time holds its heading and its lift as after its last tick (record §19).
        if (HD > 0) {
            for (uint32_t i = 0; i < HD; i++) {
                const uint32_t l = law.news_first + i;
                const TowerLevel lv = law.level[l];
                const uint64_t qh = qc * HD + i;
                const uint32_t held = law.news && tk[l] == 0 ? hh[i] : 0;
                uint64_t fre = 0, fim = 0;
                int64_t hscale;
                if (held != 0) {
                    hscale = heading_held(l, i, fre, fim);
                } else {
                    hscale = heading_read(l, fre, fim);
                    heading_keep(i, fre, fim, hscale);
                }
                uint64_t hmax;
                if (held == 2) {
                    hmax = hh_v[i * 4 + 3];
                    for (uint32_t j = tid; j < W; j += B) {
                        x[j] = fit32((wide)x[j] + (wide)hh_lift[(uint64_t)i * W + j], &st);
                    }
                } else {
                    uint64_t mx = 0;
                    for (uint32_t j = tid; j < W; j += B) {
                        const uint64_t v = magnitude(rd[j]);
                        mx = v > mx ? v : mx;
                    }
                    hmax = block_max(mx, red);
                    const bool n_d = narrow_terms(lv.heading_reach[2], hmax, W, &st);
                    for (uint32_t j = tid; j < W; j += B) {
                        const int64_t lift = fit64(rel(dot(th + lv.descent + (uint64_t)j * W, 1, W, rd, n_d), MATERIAL_BITS), &st);
                        hh_lift[(uint64_t)i * W + j] = lift;
                        x[j] = fit32((wide)x[j] + (wide)lift, &st);
                    }
                    // A re-read heading is the next arrival's heading before it: its lift into the
                    // stream's opening is read again (`Tower::join_motive`).
                    if (MO && held == 0) {
                        const bool n_f = narrow_terms(lv.heading_reach[3], hmax, W, &st);
                        for (uint32_t j = tid; j < W; j += B) {
                            hm_lift[(uint64_t)i * W + j] = fit64(rel(dot(th + lv.fine_descent + (uint64_t)j * W, 1, W, rd, n_f), MATERIAL_BITS), &st);
                        }
                    }
                    if (tid == 0) {
                        hh_v[i * 4 + 3] = hmax;
                        hh[i] = 2;
                    }
                }
                if (keep) {
                    for (uint32_t j = tid; j < W; j += B) {
                        fr.ah_read[qh * W + j] = rd[j];
                    }
                    for (uint32_t o = tid; o < 2 * N; o += B) {
                        fr.ah_face[qh * 2 * N + o] = fc[o];
                    }
                    if (tid == 0) {
                        const uint64_t at_reach = (uint64_t)i * law.streams * T + qc;
                        fr.ah_scale[qh] = hscale;
                        fr.r_ah_read[at_reach] = hmax;
                        fr.r_ah_face_re[at_reach] = fre;
                        fr.r_ah_face_im[at_reach] = fim;
                    }
                }
                __syncthreads();
            }
            m = 0;
            for (uint32_t j = tid; j < W; j += B) {
                const uint64_t v = magnitude(x[j]);
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
        // released to 2^(−16) beside it. Under a mutual contact the face is the contact's:
        // y = J x released to 2^(−16), then z_a = release(2⟨y, E_a⟩ − ‖E_a‖², 16 + b) + c_a.
        const bool n_z = narrow_terms(law.readout_reach, xmax, W, &st);
        const bool n_v = K > 0 && narrow_terms(law.pair_reach[0], pmax, K, &st);
        const bool n_w = R > 0 && narrow_terms(law.ring_reach, phimax, KP, &st);
        if (law.mutual) {
            for (uint32_t j = tid; j < W; j += B) {
                yc[j] = fit64(rel(dot(tt + law.readout + j, W, W, x, n_z), MATERIAL_BITS), &st);
            }
            __syncthreads();
            if (keep) {
                for (uint32_t j = tid; j < W; j += B) {
                    fr.contact_y[qc * W + j] = yc[j];
                }
            }
        }
        int64_t zm = INT64_MIN;
        for (uint32_t c = tid; c < A; c += B) {
            if (law.mutual) {
                const int32_t *ec = th + law.encoding + (uint64_t)c * W;
                wide sum = 0;
                for (uint32_t j = 0; j < W; j++) {
                    sum += ((wide)2 * (wide)yc[j] - (wide)ec[j]) * (wide)ec[j];
                }
                z[c] = fit64(rel(sum, FACE_BITS + law.mutual_shift) + (wide)th[law.readout_bias + c], &st);
                zm = z[c] > zm ? z[c] : zm;
                continue;
            }
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
    for (uint32_t i = tid; i < PK * 2 * N; i += B) {
        fr.pk_ends[(uint64_t)s * PK * 2 * N + i] = pk[i];
    }
    for (uint32_t i = tid; i < HD * W; i += B) {
        fr.tr_ends[(uint64_t)s * HD * W + i] = tro[i];
    }
    // The closure over the stream's section (`Tower::closures`): at each clocked level, each
    // tick's heading paired with the trace of every tick of the section, its menu,
    // z_ji = release(⟨ĥ(t_j), τ(i)⟩, 16 + heading_shift), and the tick's face over the menu, the
    // masses 2^(z_ji − max_i z_ji) on 2^(−62) and their total, compared at the tick's own trace:
    // e_jj, the total and max_i z_ji are kept for the reverse. One thread a trace; the stream's
    // scratch holds the tick's z row.
    for (uint32_t i = 0; i < HD && law.closure; i++) {
        __syncthreads();
        const uint32_t n = hc[i];
        const uint32_t *list = fr.hd_list + ((uint64_t)s * HD + i) * T;
        int64_t *zs = fr.hd_g + (uint64_t)s * T;
        for (uint32_t j = 0; j < n; j++) {
            const int32_t *heading = fr.hd_read + (((uint64_t)s * T + list[j]) * HD + i) * W;
            int64_t zm = INT64_MIN;
            for (uint32_t a = tid; a < n; a += B) {
                const int32_t *trace = fr.tr_read + (((uint64_t)s * T + list[a]) * HD + i) * W;
                wide sum = 0;
                for (uint32_t k = 0; k < W; k++) {
                    sum += (wide)heading[k] * (wide)trace[k];
                }
                zs[a] = fit64(rel(sum, FACE_BITS + law.heading_shift), &st);
                zm = zs[a] > zm ? zs[a] : zm;
            }
            const int64_t zmax = block_max_signed(zm, red);
            uwide total = 0;
            for (uint32_t a = tid; a < n; a += B) {
                const uint64_t e = below_one((wide)zs[a] - (wide)zmax, face_roots, law.face_digits);
                total += e;
                if (a == j) {
                    scale_s = (int64_t)e;
                }
            }
            total = block_sum(total, redw);
            if (tid == 0) {
                uint64_t *out = fr.hd_close + (((uint64_t)s * HD + i) * T + j) * 4;
                out[0] = (uint64_t)scale_s;
                out[1] = (uint64_t)total;
                out[2] = (uint64_t)(total >> 64);
                out[3] = (uint64_t)zmax;
            }
            __syncthreads();
        }
        if (tid == 0) {
            fr.hd_count[(uint64_t)s * HD + i] = n;
        }
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
        if (P) {
            for (uint32_t l = 0; l < L; l++) {
                fr.pa_sect[((uint64_t)s * L + l) * 2] = pa_lead[l];
                fr.pa_sect[((uint64_t)s * L + l) * 2 + 1] = pa_members[l];
            }
        }
        if (keep) {
            for (uint32_t l = 0; l < L; l++) {
                for (uint32_t i = 0; i < 4; i++) {
                    atomicMax((unsigned long long *)(fr.swell + l * 4 + i), (unsigned long long)sw[l * 4 + i]);
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
    // The mutual contact's covector of the produced face, G_y.
    int64_t *gyc = (int64_t *)carve(at, 8ull * W * (law.mutual != 0));
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
    if (law.mutual) {
        // The mutual contact's return (`Tower::mutual_return`): G_y = 2β Σ_a δz_a E_a on 2^(−40)
        // released by 15 + b, then Jᵀ G_y (J row-major, W × W) in the readout's place.
        __syncthreads();
        uint64_t gm = 0;
        for (uint32_t j = tid; j < W; j += B) {
            wide sum = 0;
            for (uint32_t c = 0; c < A; c++) {
                sum += (wide)dz[c] * (wide)fr.theta[law.encoding + (uint64_t)c * W + j];
            }
            gyc[j] = fit64(rel(sum, FACE_BITS - 1 + law.mutual_shift), &st);
            fr.contact_gy[q * W + j] = gyc[j];
            const uint64_t a = magnitude(gyc[j]);
            gm = a > gm ? a : gm;
        }
        const uint64_t gmax = block_max(gm, red);
        if (tid == 0) {
            fr.r_contact_gy[q] = gmax;
        }
        const bool n_j = narrow_rows(law.readout_reach, gmax, W);
        for (uint32_t idx = tid; idx < G * W; idx += B) {
            const uint32_t g = idx / W, j = idx % W;
            const uint32_t from = (uint32_t)((uint64_t)W * g / G), to = (uint32_t)((uint64_t)W * (g + 1) / G);
            part[idx] = dot(fr.theta + law.readout + (uint64_t)from * W + j, W, to - from, gyc + from, n_j);
        }
    } else {
        const bool narrow = narrow_rows(law.readout_reach, ymax, A);
        for (uint32_t idx = tid; idx < G * W; idx += B) {
            const uint32_t g = idx / W, j = idx % W;
            const uint32_t from = (uint32_t)((uint64_t)A * g / G), to = (uint32_t)((uint64_t)A * (g + 1) / G);
            part[idx] = dot(fr.theta + law.readout + (uint64_t)from * W + j, W, to - from, dz + from, narrow);
        }
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
    const TowerLevel lv = law.level[l];
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
        if (law.split != 0) {
            fr.split_dv[ql * F + i] = v;
        }
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
    // The passage: the passing current's covector gains W₁ˣᵀ δa, released on its own (the level's
    // output covector dy was kept above for the return's material), on the levels the clock holds.
    if (law.passage != 0 && l >= law.news_first) {
        const bool n_x = narrow_rows(lv.passage_reach, amax, F);
        for (uint32_t idx = tid; idx < G * W; idx += B) {
            const uint32_t g = idx / W, j = idx % W;
            const uint32_t from = (uint32_t)((uint64_t)F * g / G), to = (uint32_t)((uint64_t)F * (g + 1) / G);
            part[idx] = dot(fr.theta + lv.passage + (uint64_t)from * W + j, W, to - from, da + from, n_x);
        }
        __syncthreads();
        for (uint32_t j = tid; j < W; j += B) {
            wide sum = 0;
            for (uint32_t g = 0; g < G; g++) {
                sum += part[g * W + j];
            }
            fr.dx[q * W + j] = fit64((wide)dy[j] + (wide)fit64(rel(sum, MATERIAL_BITS), &st), &st);
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
// A state the move carries and its covector after the move (`carry` in `Tower::reverse_joined`):
// their covectors of λ_t (re, im), of γ_t (`Re(conj(G) P x)`) and of the push (re, im), the step
// having acted `ticks` times with the arrival held, the states between read again by the step's own
// law from `(hr, hi)` and the covector carried back through each, G⁽ʲ⁻¹⁾ = conj(λ_t) G⁽ʲ⁾ (none
// when no tick). Unpumped: the packet's carry, which a news clock (never beside a pump) brings.
__device__ void carried_covectors(wide hr, wide hi, wide gr, wide gi, uint32_t ticks, wide mr, wide mi, wide pr, wide pi, wide push_r, wide push_i, wide *out) {
    wide sr = 0, si = 0, through = 0, pgr = 0, pgi = 0, gcr = gr, gci = gi;
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
    out[0] = sr;
    out[1] = si;
    out[2] = through;
    out[3] = pgr;
    out[4] = pgi;
}

extern "C" __global__ void tower_reverse_modes(TowerLaw law, TowerFrame fr, uint32_t l) {
    const uint32_t s = blockIdx.x, B = blockDim.x;
    const uint32_t A = law.alphabet, N = law.modes, L = law.levels, T = law.cells;
    const TowerLevel lv = law.level[l];
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
        // The packet the next level hears moves with these modes (`Tower::join_packets`), so its
        // covector is carried back by the same moves, G_a(t) = G_a,tick(t) + conj(λ_(t+1))^(Δτ)
        // G_a(t+1), cut where that level ticked and the packet rested.
        const bool carrying = law.packets && l + 1 >= law.news_first && l + 1 < L;
        const uint32_t PK = law.packets, F0 = law.news_first;
        wide car = 0, cai = 0;
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
            wide gar = 0, gai = 0;
            if (carrying) {
                if (fr.ticks[ql + 1] == 0) {
                    gar = car;
                    gai = cai;
                    for (uint32_t j = 0; j < later_ticks; j++) {
                        const wide ar = rel(lr * gar + li * gai, MOVE_BITS);
                        gai = rel(lr * gai - li * gar, MOVE_BITS);
                        gar = ar;
                    }
                }
                const uint64_t qp = q * PK + (l + 1 - F0);
                gar = fit64(gar + (wide)fr.pk_cov[qp * 2 * N + k], &st);
                gai = fit64(gai + (wide)fr.pk_cov[qp * 2 * N + N + k], &st);
                car = gar;
                cai = gai;
            }
            // An arrival that ticked the level no time moved nothing: its covectors are zero (its
            // push and gate were not read; the covector passes it unturned, above).
            const uint32_t ticks = law.news ? fr.ticks[ql] : 1;
            if (ticks == 0) {
                fr.gre[ql * N + k] = 0;
                fr.gim[ql * N + k] = 0;
                fr.dq[ql * N + k] = 0;
                if (law.turned) {
                    fr.ds[ql * N + k] = 0;
                }
                continue;
            }
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
            // The packet shares the move: its covectors of λ_t, γ_t and the push are summed with the
            // modes', from the packet before this cell's move (the opening's, at rest after the
            // next level's tick, or as the cell before left it).
            if (carrying) {
                wide abr = 0, abi = 0;
                if (t == 0) {
                    const int64_t *open_a = fr.pk_open + (((uint64_t)s * PK + (l + 1 - F0)) * N + k) * 2;
                    abr = open_a[0];
                    abi = open_a[1];
                } else if (fr.ticks[(q - 1) * L + l + 1] == 0) {
                    const int64_t *before = fr.pk_state + (((q - 1) * PK + (l + 1 - F0)) * N + k) * 2;
                    abr = before[0];
                    abi = before[1];
                }
                wide pc[5];
                carried_covectors(abr, abi, gar, gai, ticks, mv[3], mv[4], rel(gamma * push_r, MOVE_BITS), rel(gamma * push_i, MOVE_BITS), push_r, push_i, pc);
                glr += pc[0];
                gli += pc[1];
                through += pc[2];
                pgr += pc[3];
                pgi += pc[4];
            }
            // A participating level's turn also carries the transport's later sum (the participation's
            // reverse wrote it before this scan).
            const wide turning = rel((wide)mv[3] * gli - (wide)mv[4] * glr, MOVE_BITS) + (law.pa_heads > 0 ? fr.pa_tturn[q * N + k] : 0);
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
                // The transport's covector of log₂ ρ_t = c r ℓ: ∂/∂q = c ℓ ln 2 r (1 − r) and
                // ∂/∂|λ| = c r/(|λ| ln 2), each on 2^(−30).
                const wide met = law.pa_heads > 0 ? fr.pa_tlog[q * N + k] : 0;
                if (met != 0) {
                    const wide by_open = rel(rel(rel(log * (wide)law.ln2, MOVE_BITS) * open, MOVE_BITS) * (one - open), MOVE_BITS);
                    dq = fit64((wide)dq + rel(met * GATE_REACH * by_open, COVECTOR_BITS + MOVE_BITS), &st);
                    const wide lm = rel(modulus * (wide)law.ln2, MOVE_BITS);
                    along += rel(met * div_nearest(((wide)GATE_REACH * open) * ((wide)1 << MOVE_BITS), lm > 0 ? lm : 1), MOVE_BITS);
                }
            }
            fr.gre[ql * N + k] = fit64(rel(gamma * pgr, MOVE_BITS), &st);
            fr.gim[ql * N + k] = fit64(rel(gamma * pgi, MOVE_BITS), &st);
            fr.dq[ql * N + k] = dq;
        }
        // The opening's credit (`LevelCredit`): the covector of the carried modes,
        // a = conj(λ_0)^(Δτ(0)) G_h(0), and of the carried packet, meet the moments their history
        // carried; the per-mode moments here, the material moments in `tower_credit_meet`, which
        // reads the covectors kept.
        if (law.credit && l >= law.credit_from) {
            const uint32_t cx = l - law.credit_from;
            const uint64_t ql0 = (uint64_t)s * T * L + l;
            const uint32_t ticks0 = law.news ? fr.ticks[ql0] : 1;
            const int64_t *mv0 = fr.moves + (ql0 * N + k) * 6;
            const bool with_packet = carrying && cr_packet(law, l);
            for (uint32_t set = 0; set < (with_packet ? 2u : 1u); set++) {
                wide ar = set == 0 ? cr : car, ai = set == 0 ? ci : cai;
                for (uint32_t j = 0; j < ticks0; j++) {
                    const wide nr_ = rel((wide)mv0[3] * ar + (wide)mv0[4] * ai, MOVE_BITS);
                    ai = rel((wide)mv0[3] * ai - (wide)mv0[4] * ar, MOVE_BITS);
                    ar = nr_;
                }
                // A later term of the motive's series reaches the carried modes themselves through
                // the heading before the first cell (`tower_motive_return`, `Tower::join_motive`).
                if (set == 0 && law.motive && law.heading > 0 && l >= law.news_first) {
                    const int64_t *mo = fr.mo_open + (((uint64_t)s * law.heading + (l - law.news_first)) * N + k) * 2;
                    ar += mo[0];
                    ai += mo[1];
                }
                int64_t *cov = fr.cr_cov + ((((uint64_t)s * law.credit + cx) * 2 + set) * N + k) * 2;
                cov[0] = fit64(ar, &st);
                cov[1] = fit64(ai, &st);
                const int64_t *blk = fr.cr_open + cr_block(law, s, cx, set) + 2ull * N * law.width;
                along += ar * (wide)blk[2 * k] + ai * (wide)blk[2 * k + 1];
                around += ar * (wide)blk[2 * N + 2 * k] + ai * (wide)blk[2 * N + 2 * k + 1];
            }
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
    const TowerLevel lv = law.level[l];
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
    // A cell the level is still at returns nothing: its covectors are zero (a news clock carries no
    // pump, and participation's charts are zero there too).
    if (law.news && fr.ticks[ql] == 0) {
        if (tid == 0) {
            fr.r_gre[ql] = 0;
            fr.r_gim[ql] = 0;
            fr.r_dq[ql] = 0;
            if (law.turned) {
                fr.r_ds[ql] = 0;
            }
        }
        return;
    }
    // At a tick of a level that hears a packet, its push, gate and turn read the packet, so their
    // covectors return to the packet's read (`pk_dx`), not to the passing current.
    const bool heard = law.packets && l >= law.news_first;
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
        wide sum = heard ? 0 : (wide)fr.dx[q * W + j];
        for (uint32_t fam = 0; fam < fams; fam++) {
            sum += back[fam * W + j];
        }
        const int64_t v = fit64(sum, &st);
        if (heard) {
            fr.pk_dx[(q * law.packets + (l - law.news_first)) * W + j] = v;
            continue;
        }
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

// The packet's return at a level `l` that hears one (`Tower::reverse_joined`), one block a cell: at
// a tick the covector its push, gate and turn returned to the packet's read (`pk_dx`) passes the
// ratio's adjoint ∂r = (∂r̂ − r̂ ⟨r̂, ∂r̂⟩/d) / ‖r‖_rms, and the fine level's read returns the
// packet's covector G_a = C_reᵀ ∂r and C_imᵀ (−∂r), which the fine level's scan carries back through
// the moves that built the packet; zero at a cell the level is still at. Runs after the level's
// `tower_reverse_dx` and before the fine level's scan.
extern "C" __global__ void __launch_bounds__(TOWER_THREADS) tower_reverse_packet(TowerLaw law, TowerFrame fr, uint32_t l) {
    const uint64_t q = blockIdx.x, ql = q * law.levels + l, qp = q * law.packets + (l - law.news_first);
    const uint32_t s = (uint32_t)(q / law.cells), tid = threadIdx.x, B = blockDim.x;
    const uint32_t W = law.width, N = law.modes;
    extern __shared__ __align__(16) unsigned char smem[];
    unsigned char *at = smem;
    uwide *redw = (uwide *)carve(at, sizeof(uwide) * 32);
    uint64_t *red = (uint64_t *)carve(at, 8ull * 32);
    int64_t *dread = (int64_t *)carve(at, 8ull * W);
    __shared__ uint32_t st;
    if (tid == 0) {
        st = 0;
    }
    if (fr.ticks[ql] == 0) {
        for (uint32_t o = tid; o < 2 * N; o += B) {
            fr.pk_cov[qp * 2 * N + o] = 0;
        }
        for (uint32_t j = tid; j < W; j += B) {
            fr.pk_dread[qp * W + j] = 0;
        }
        if (tid == 0) {
            fr.r_pk_dread[ql] = 0;
        }
        return;
    }
    const TowerLevel lf = law.level[l - 1];
    const int64_t scale = fr.pk_scale[qp];
    uwide dot_part = 0;
    for (uint32_t j = tid; j < W; j += B) {
        dot_part += (uwide)((wide)fr.pk_read[qp * W + j] * (wide)fr.pk_dx[qp * W + j]);
    }
    const wide mean = div_nearest((wide)block_sum(dot_part, redw), (wide)W);
    uint64_t m = 0;
    for (uint32_t j = tid; j < W; j += B) {
        int64_t v = 0;
        if (scale != 0) {
            const wide read = fr.pk_read[qp * W + j];
            v = fit64(div_nearest(((wide)fr.pk_dx[qp * W + j] - rel(mean * read, 2 * FACE_BITS)) << FACE_BITS, scale), &st);
        }
        dread[j] = v;
        fr.pk_dread[qp * W + j] = v;
        const uint64_t a = magnitude(v);
        m = a > m ? a : m;
    }
    const uint64_t dmax = block_max(m, red);
    if (tid == 0) {
        fr.r_pk_dread[ql] = dmax;
    }
    const bool n_re = narrow_rows(lf.reach[2], dmax, W);
    const bool n_im = narrow_rows(lf.reach[3], dmax, W);
    for (uint32_t o = tid; o < 2 * N; o += B) {
        const uint32_t k = o % N;
        const bool im = o >= N;
        const wide sum = dot(fr.theta + (im ? lf.read_im : lf.read_re) + k, N, W, dread, im ? n_im : n_re);
        fr.pk_cov[qp * 2 * N + o] = fit64(rel(im ? -sum : sum, MATERIAL_BITS), &st);
    }
    __syncthreads();
    if (tid == 0 && st != 0) {
        atomicOr(fr.status + s, st);
    }
}

// The face's read of the heading returned (`Tower::reverse_joined`), one block a cell of a stream.
// The top's covector δx, known before any level's reverse, is kept for the descent's outer sum
// `Σ δx ĥ⁺ᵀ` (`ah_top`) and reaches each clocked level's heading after the cell through `Dᵀ`, then
// through its ratio's adjoint the covector of the raw read `Re(C^→ h)` (`ah_dread`), which
// `tower_reverse_heading` returns through C^→ to the read covector of the cell's own state. Runs
// after `tower_reverse_top` and before the top level's contacts.
extern "C" __global__ void __launch_bounds__(TOWER_THREADS) tower_reverse_ahead(TowerLaw law, TowerFrame fr) {
    const uint64_t q = blockIdx.x;
    const uint32_t s = (uint32_t)(q / law.cells), tid = threadIdx.x, B = blockDim.x;
    const uint32_t W = law.width, HD = law.heading;
    const uint64_t SQ = (uint64_t)law.streams * law.cells;
    extern __shared__ __align__(16) unsigned char smem[];
    unsigned char *at = smem;
    uwide *redw = (uwide *)carve(at, sizeof(uwide) * 32);
    uint64_t *red = (uint64_t *)carve(at, 8ull * 32);
    int64_t *top = (int64_t *)carve(at, 8ull * W);
    int64_t *dv = (int64_t *)carve(at, 8ull * W);
    __shared__ uint32_t st;
    if (tid == 0) {
        st = 0;
    }
    uint64_t m = 0;
    for (uint32_t j = tid; j < W; j += B) {
        const int64_t v = fr.dx[q * W + j];
        top[j] = v;
        fr.ah_top[q * W + j] = v;
        const uint64_t a = magnitude(v);
        m = a > m ? a : m;
    }
    const uint64_t tmax = block_max(m, red);
    if (tid == 0) {
        fr.r_ah_top[q] = tmax;
    }
    for (uint32_t i = 0; i < HD; i++) {
        const TowerLevel lv = law.level[law.news_first + i];
        const uint64_t qh = q * HD + i;
        const bool n_t = narrow_rows(lv.heading_reach[2], tmax, W);
        for (uint32_t k = tid; k < W; k += B) {
            dv[k] = fit64(rel(dot(fr.theta + lv.descent + k, W, W, top, n_t), MATERIAL_BITS), &st);
        }
        __syncthreads();
        // The ratio's adjoint ∂r = (∂r̂ − r̂ ⟨r̂, ∂r̂⟩/d) / ‖r‖_rms at the kept ratio and scale.
        const int32_t *r = fr.ah_read + qh * W;
        const int64_t scale = fr.ah_scale[qh];
        uwide dot_part = 0;
        for (uint32_t k = tid; k < W; k += B) {
            dot_part += (uwide)((wide)r[k] * (wide)dv[k]);
        }
        const wide mean = div_nearest((wide)block_sum(dot_part, redw), (wide)W);
        uint64_t mr = 0;
        for (uint32_t k = tid; k < W; k += B) {
            int64_t v = 0;
            if (scale != 0) {
                v = fit64(div_nearest(((wide)dv[k] - rel(mean * (wide)r[k], 2 * FACE_BITS)) << FACE_BITS, scale), &st);
            }
            fr.ah_dread[qh * W + k] = v;
            const uint64_t a = magnitude(v);
            mr = a > mr ? a : mr;
        }
        const uint64_t dmax = block_max(mr, red);
        if (tid == 0) {
            fr.r_ah_dread[(uint64_t)i * SQ + q] = dmax;
        }
        __syncthreads();
    }
    if (tid == 0 && st != 0) {
        atomicOr(fr.status + s, st);
    }
}

// [agent-inferred, October 31] **One term's return at the motive** (`Tower::motive_return`, record
// §29–§30), one block a cell of a stream: the term's force covector, δf = Σ_(l<F) (C_re γG_re −
// C_im γG_im) over the arrival levels whose pushes read the force (kept with its reach for D↓'s
// outer sum), reaches each clocked level's heading before the cell through D↓ᵀ, then its ratio's
// adjoint at the kept ratio and scale, the
// covector of the raw read Re(C^→ h) of the modes before the cell, which is the next term's only
// source: the modes after the cell before (written as that cell's `ah_dread`, which
// `tower_reverse_heading` returns through C^→ and the outer sums pair with that cell's face), or
// at the first cell the carried modes (`mo_dr0`, and `mo_open` = C_reᵀ ∂r, C_imᵀ (−∂r), which the
// modes' scan adds to the opening's covector the credit meets). The last cell's `ah_dread` is zero:
// nothing in the section reads its heading. `mo_flag` is set where a source is not zero.
extern "C" __global__ void __launch_bounds__(TOWER_THREADS) tower_motive_return(TowerLaw law, TowerFrame fr) {
    const uint64_t q = blockIdx.x;
    const uint32_t s = (uint32_t)(q / law.cells), t = (uint32_t)(q % law.cells), tid = threadIdx.x, B = blockDim.x;
    const uint32_t W = law.width, N = law.modes, HD = law.heading;
    const uint64_t SQ = (uint64_t)law.streams * law.cells;
    extern __shared__ __align__(16) unsigned char smem[];
    unsigned char *at = smem;
    uwide *redw = (uwide *)carve(at, sizeof(uwide) * 32);
    uint64_t *red = (uint64_t *)carve(at, 8ull * 32);
    int64_t *dxs = (int64_t *)carve(at, 8ull * W);
    int64_t *dv = (int64_t *)carve(at, 8ull * W);
    int64_t *dr = (int64_t *)carve(at, 8ull * W);
    __shared__ uint32_t st;
    __shared__ uint32_t any;
    if (tid == 0) {
        st = 0;
        any = 0;
    }
    const uint32_t L = law.levels, N0 = law.modes;
    uint64_t m = 0;
    for (uint32_t j = tid; j < W; j += B) {
        wide acc = 0;
        for (uint32_t l = 0; l < law.news_first; l++) {
            const TowerLevel fl = law.level[l];
            const uint64_t ql = q * L + l;
            const bool n_a = narrow_rows(fl.reach[2], fr.r_gre[ql], N0);
            const bool n_b = narrow_rows(fl.reach[3], fr.r_gim[ql], N0);
            const int64_t fa = fit64(rel(dot(fr.theta + fl.read_re + (uint64_t)j * N0, 1, N0, fr.gre + ql * N0, n_a), MATERIAL_BITS), &st);
            const int64_t fb = fit64(rel(dot(fr.theta + fl.read_im + (uint64_t)j * N0, 1, N0, fr.gim + ql * N0, n_b), MATERIAL_BITS), &st);
            acc = fit64(acc + (wide)fa - (wide)fb, &st);
        }
        const int64_t v = (int64_t)acc;
        dxs[j] = v;
        fr.mo_df[q * W + j] = v;
        const uint64_t a = magnitude(v);
        m = a > m ? a : m;
    }
    const uint64_t xmax = block_max(m, red);
    if (tid == 0) {
        fr.r_mo_df[q] = xmax;
    }
    for (uint32_t i = 0; i < HD; i++) {
        const TowerLevel lv = law.level[law.news_first + i];
        const uint64_t qh = q * HD + i;
        const bool n_t = narrow_rows(lv.heading_reach[3], xmax, W);
        for (uint32_t k = tid; k < W; k += B) {
            dv[k] = fit64(rel(dot(fr.theta + lv.fine_descent + k, W, W, dxs, n_t), MATERIAL_BITS), &st);
        }
        __syncthreads();
        // The ratio's adjoint ∂r = (∂r̂ − r̂ ⟨r̂, ∂r̂⟩/d) / ‖r‖_rms at the kept ratio and scale.
        const int32_t *r = fr.mo_read + qh * W;
        const int64_t scale = fr.mo_scale[qh];
        uwide dot_part = 0;
        for (uint32_t k = tid; k < W; k += B) {
            dot_part += (uwide)((wide)r[k] * (wide)dv[k]);
        }
        const wide mean = div_nearest((wide)block_sum(dot_part, redw), (wide)W);
        uint64_t mr = 0;
        for (uint32_t k = tid; k < W; k += B) {
            int64_t v = 0;
            if (scale != 0) {
                v = fit64(div_nearest(((wide)dv[k] - rel(mean * (wide)r[k], 2 * FACE_BITS)) << FACE_BITS, scale), &st);
            }
            dr[k] = v;
            const uint64_t a = magnitude(v);
            mr = a > mr ? a : mr;
        }
        const uint64_t dmax = block_max(mr, red);
        if (tid == 0 && dmax != 0) {
            any = 1;
        }
        if (t > 0) {
            const uint64_t qb = (q - 1) * HD + i;
            for (uint32_t k = tid; k < W; k += B) {
                fr.ah_dread[qb * W + k] = dr[k];
            }
            if (tid == 0) {
                fr.r_ah_dread[(uint64_t)i * SQ + q - 1] = dmax;
            }
        } else {
            const uint64_t qs = (uint64_t)s * HD + i;
            for (uint32_t k = tid; k < W; k += B) {
                fr.mo_dr0[qs * W + k] = dr[k];
            }
            if (tid == 0) {
                fr.r_mo_dr0[(uint64_t)i * law.streams + s] = dmax;
            }
            const bool n_re = narrow_rows(lv.heading_reach[0], dmax, W);
            const bool n_im = narrow_rows(lv.heading_reach[1], dmax, W);
            for (uint32_t o = tid; o < 2 * N; o += B) {
                const uint32_t k = o % N;
                const bool im = o >= N;
                const wide sum = dot(fr.theta + (im ? lv.heading_im : lv.heading_re) + k, N, W, dr, im ? n_im : n_re);
                fr.mo_open[(qs * N + k) * 2 + (im ? 1 : 0)] = fit64(rel(im ? -sum : sum, MATERIAL_BITS), &st);
            }
        }
        if (t == law.cells - 1) {
            for (uint32_t k = tid; k < W; k += B) {
                fr.ah_dread[qh * W + k] = 0;
            }
            if (tid == 0) {
                fr.r_ah_dread[(uint64_t)i * SQ + q] = 0;
            }
        }
        __syncthreads();
    }
    if (tid == 0 && any != 0) {
        atomicOr(fr.mo_flag, 1u);
    }
    if (tid == 0 && st != 0) {
        atomicOr(fr.status + s, st);
    }
}

// The heading's return at a clocked level `l` over one stream (`Tower::reverse_joined`), one block a
// stream: the face's covector of the heading after each cell (`tower_reverse_ahead`, `ah_dread`)
// reaches through C^→, C_reᵀ ∂r and C_imᵀ (−∂r), the read covector of that cell's own state. The
// closure is read, not learned. Runs after the level's contacts (which write the read covector)
// and before its modes' scan (which reads it).
extern "C" __global__ void __launch_bounds__(TOWER_THREADS) tower_reverse_heading(TowerLaw law, TowerFrame fr, uint32_t l) {
    const uint32_t s = blockIdx.x, tid = threadIdx.x, B = blockDim.x;
    const uint32_t W = law.width, N = law.modes, L = law.levels, T = law.cells, HD = law.heading;
    const uint32_t i = l - law.news_first;
    const TowerLevel lv = law.level[l];
    const uint64_t SQ = (uint64_t)law.streams * T;
    __shared__ uint32_t st;
    if (tid == 0) {
        st = 0;
    }
    __syncthreads();
    for (uint32_t t = 0; t < T; t++) {
        const int64_t *da = fr.ah_dread + (((uint64_t)s * T + t) * HD + i) * W;
        const uint64_t dmax = fr.r_ah_dread[(uint64_t)i * SQ + (uint64_t)s * T + t];
        const bool n_re = narrow_rows(lv.heading_reach[0], dmax, W);
        const bool n_im = narrow_rows(lv.heading_reach[1], dmax, W);
        const uint64_t row = ((uint64_t)s * T + t) * L + l;
        for (uint32_t o = tid; o < 2 * N; o += B) {
            const uint32_t k = o % N;
            const bool im = o >= N;
            const wide sum = dot(fr.theta + (im ? lv.heading_im : lv.heading_re) + k, N, W, da, im ? n_im : n_re);
            int64_t *rc = fr.readcov + row * 2 * N + o;
            *rc = fit64((wide)*rc + (wide)fit64(rel(im ? -sum : sum, MATERIAL_BITS), &st), &st);
        }
    }
    __syncthreads();
    if (tid == 0 && st != 0) {
        atomicOr(fr.status + s, st);
    }
}

// Participation's return over one stream (`participation_return`, `Tower::reverse_joined`), one
// block a stream, at level `l`: a held cell's current covector first joins its level's last site's
// (one before the call's first site is the opening's, a constant, and is dropped); then at each
// site its current's covector, turned back by the site's frame, returns through every head's Gibbs
// face (recomputed from the kept probe, keys and dissipation, the forward's own bits) into the
// probe, every admitted site's key and current, and the head's friction, the sites carried open
// into the call read as constants until the level's section closes; then each site's three
// covectors are turned forward by its frame into the six chart covectors `tower_reverse_dx` returns
// to the input, with their reaches (zero at a cell the level is still at). Runs after the level's
// contacts (which write the current's covector) and before its `tower_reverse_dx`.
extern "C" __global__ void __launch_bounds__(TOWER_THREADS) tower_reverse_participation(TowerLaw law, TowerFrame fr, uint32_t l) {
    const uint32_t s = blockIdx.x, tid = threadIdx.x, B = blockDim.x;
    const uint32_t N = law.modes, L = law.levels, T = law.cells, HH = law.pa_heads;
    const TowerLevel lv = law.level[l];
    extern __shared__ __align__(16) unsigned char smem[];
    unsigned char *at = smem;
    int64_t *gb = (int64_t *)carve(at, 8ull * 2 * N);
    uwide *redw = (uwide *)carve(at, sizeof(uwide) * 32);
    uint64_t *red = (uint64_t *)carve(at, 8ull * 32);
    __shared__ uint32_t st;
    __shared__ uint32_t lead_s, members_s;
    if (tid == 0) {
        st = 0;
        lead_s = fr.pa_open[(uint64_t)s * L + l];
        members_s = 0;
    }
    const uint64_t site0 = (uint64_t)s * T, row = (uint64_t)s * law.pa_section;
    const uint64_t QL = (uint64_t)law.streams * T * L;
    const uint32_t scale_bits = FACE_BITS + law.pa_beta;
    const uint64_t stride = T > law.pa_section ? T : law.pa_section;
    const uint64_t *face_roots = fr.roots;
    wide *gq = fr.pa_gq + site0 * N * 2, *gk = fr.pa_gk + site0 * N * 2, *gw = fr.pa_gw + site0 * N * 2;
    wide *gmet = fr.pa_gmet + site0 * HH;
    uint32_t *member = fr.pa_member + ((uint64_t)s * L + l) * law.pa_section;
    uint32_t *mark = fr.pa_mark + site0;
    for (uint64_t i = tid; i < (uint64_t)T * N * 2; i += B) {
        gq[i] = 0;
        gk[i] = 0;
        gw[i] = 0;
    }
    for (uint64_t i = tid; i < (uint64_t)T * HH; i += B) {
        gmet[i] = 0;
    }
    // A held cell's current covector joins its last site's: one thread a coordinate, the cells in
    // reverse order.
    for (uint32_t o = tid; o < 2 * N; o += B) {
        wide held = 0;
        for (uint32_t step = 0; step < T; step++) {
            const uint32_t i = T - 1 - step;
            const uint64_t qi = (site0 + i) * L + l;
            held += fr.pa_gy[qi * 2 * N + o];
            if (!law.news || fr.ticks[qi] > 0) {
                fr.pa_gy[qi * 2 * N + o] = fit64(held, &st);
                held = 0;
            }
        }
    }
    __syncthreads();
    for (uint32_t i = 0; i < T; i++) {
        const uint64_t qi = (site0 + i) * L + l;
        if (law.news && fr.ticks[qi] == 0) {
            if (tid == 0) {
                mark[i] = 0;
            }
            continue;
        }
        // The site's place: after the carried sites its section still reads (`lead`) and the
        // sites admitted since, whose cells `member` lists.
        const uint32_t lead = lead_s, members = members_s, count = lead + members + 1;
        if (tid == 0) {
            member[members] = i;
        }
        for (uint32_t k = tid; k < N; k += B) {
            const wide ur = fr.pa_frame[(qi * N + k) * 2], ui = fr.pa_frame[(qi * N + k) * 2 + 1];
            const wide gr = fr.pa_gy[qi * 2 * N + k], gi = fr.pa_gy[qi * 2 * N + N + k];
            gb[2 * k] = fit64(rel(ur * gr + ui * gi, MOVE_BITS), &st);
            gb[2 * k + 1] = fit64(rel(ur * gi - ui * gr, MOVE_BITS), &st);
        }
        __syncthreads();
        // One warp a head, the warps taking the heads in turn: a lane takes every 32nd admitted
        // site, the peak, mass, mean and friction are warp reductions, and the head's modes take
        // their key, current and probe covectors (disjoint from every other head's). A carried site
        // is read as a constant: it takes no key, current or met covector.
        for (uint32_t hh = tid >> 5; hh < HH; hh += B >> 5) {
            const uint32_t lane = tid & 31;
            const uint32_t from = fr.pa_heads[hh], to = fr.pa_heads[hh + 1];
            const wide friction = fr.theta[lv.pa[9] + hh];
            const wide dis_i = fr.pa_diss[qi * HH + hh];
            int64_t *zrow = fr.pa_z + ((uint64_t)s * HH + hh) * stride;
            uint64_t *erow = fr.pa_e + ((uint64_t)s * HH + hh) * stride;
            int64_t zm = INT64_MIN;
            for (uint32_t j = lane; j < count; j += 32) {
                const bool carried = j < lead;
                const uint64_t qj = (carried ? row + j : site0 + member[j - lead]) * L + l;
                const int64_t *keys = carried ? fr.pa_open_key : fr.pa_key;
                const int64_t *diss = carried ? fr.pa_open_diss : fr.pa_diss;
                wide pairing = 0;
                for (uint32_t k = from; k < to; k++) {
                    const int64_t *kj = keys + (qj * N + k) * 2;
                    pairing += (wide)fr.pa_probe[(qi * N + k) * 2] * kj[0] + (wide)fr.pa_probe[(qi * N + k) * 2 + 1] * kj[1];
                }
                const int64_t z = fit64(rel(pairing, scale_bits) - rel(friction * (dis_i - (wide)diss[qj * HH + hh]), FACE_BITS), &st);
                zrow[j] = z;
                zm = z > zm ? z : zm;
            }
            const int64_t peak = warp_max_signed(zm);
            uwide msum = 0;
            for (uint32_t j = lane; j < count; j += 32) {
                const int64_t z = zrow[j];
                const uint64_t e = (wide)peak - (wide)z >= ((wide)UNIT_BITS << FACE_BITS) ? 0 : below_one((wide)z - (wide)peak, face_roots, law.face_digits);
                erow[j] = e;
                msum += e;
            }
            const wide mass = (wide)warp_sum(msum);
            // g_a_j = Re⟨w_j, g'⟩ and its weighted mean.
            uwide asum = 0;
            for (uint32_t j = lane; j < count; j += 32) {
                const bool carried = j < lead;
                const uint64_t qj = (carried ? row + j : site0 + member[j - lead]) * L + l;
                const int64_t *values = carried ? fr.pa_open_value : fr.pa_value;
                wide dotv = 0;
                for (uint32_t k = from; k < to; k++) {
                    const int64_t *wj = values + (qj * N + k) * 2;
                    dotv += (wide)wj[0] * gb[2 * k] + (wide)wj[1] * gb[2 * k + 1];
                }
                const int64_t ga = fit64(rel(dotv, FACE_BITS), &st);
                zrow[j] = ga;
                asum += (uwide)((wide)erow[j] * (wide)ga);
            }
            const wide mean = div_nearest((wide)warp_sum(asum), mass);
            // g_z_j, the friction's covector, and the sites' and the probe's met covectors κ g_z_j
            // and −κ Σ_j g_z_j (the transport's, on 2^(−40)).
            uwide fsum = 0, msum_met = 0;
            for (uint32_t j = lane; j < count; j += 32) {
                const bool carried = j < lead;
                const uint64_t qj = (carried ? row + j : site0 + member[j - lead]) * L + l;
                const wide e = erow[j];
                const wide gz = rel((wide)law.ln2 * div_nearest(e * ((wide)zrow[j] - mean), mass), MOVE_BITS);
                zrow[j] = fit64(gz, &st);
                fsum += (uwide)(-rel(gz * (dis_i - (wide)(carried ? fr.pa_open_diss : fr.pa_diss)[qj * HH + hh]), FACE_BITS));
                const wide shared = gz * friction;
                if (!carried) {
                    gmet[(uint64_t)member[j - lead] * HH + hh] += shared;
                }
                msum_met += (uwide)shared;
            }
            const wide fric = (wide)warp_sum(fsum);
            const wide probe_met = (wide)warp_sum(msum_met);
            __syncwarp();
            if (lane == 0) {
                fr.pa_gfric[((uint64_t)s * L + l) * HH + hh] += fric;
                gmet[(uint64_t)i * HH + hh] -= probe_met;
            }
            __syncwarp();
            // Every admitted site's key and current covectors (the carried sites' none), and the
            // probe's.
            const uint32_t span = to - from;
            for (uint32_t idx = lane; idx < (count - lead) * span; idx += 32) {
                const uint32_t j = lead + idx / span, k = from + idx % span;
                const uint32_t c = member[j - lead];
                const wide gz = zrow[j], e = erow[j];
                wide *kk = gk + ((uint64_t)c * N + k) * 2, *ww = gw + ((uint64_t)c * N + k) * 2;
                kk[0] += fit64(rel(gz * fr.pa_probe[(qi * N + k) * 2], scale_bits), &st);
                kk[1] += fit64(rel(gz * fr.pa_probe[(qi * N + k) * 2 + 1], scale_bits), &st);
                ww[0] += fit64(div_nearest(e * gb[2 * k], mass), &st);
                ww[1] += fit64(div_nearest(e * gb[2 * k + 1], mass), &st);
            }
            for (uint32_t k = from; k < to; k++) {
                wide ar = 0, ai = 0;
                for (uint32_t j = lane; j < count; j += 32) {
                    const bool carried = j < lead;
                    const uint64_t qj = (carried ? row + j : site0 + member[j - lead]) * L + l;
                    const int64_t *keys = carried ? fr.pa_open_key : fr.pa_key;
                    const wide gz = zrow[j];
                    ar += gz * keys[(qj * N + k) * 2];
                    ai += gz * keys[(qj * N + k) * 2 + 1];
                }
                ar = (wide)warp_sum((uwide)ar);
                ai = (wide)warp_sum((uwide)ai);
                if (lane == 0) {
                    gq[((uint64_t)i * N + k) * 2] += fit64(rel(ar, scale_bits), &st);
                    gq[((uint64_t)i * N + k) * 2 + 1] += fit64(rel(ai, scale_bits), &st);
                }
            }
            __syncwarp();
        }
        __syncthreads();
        // The section closes with its last site: the later sites are the next section's.
        if (tid == 0) {
            const bool closes = count >= law.pa_section;
            mark[i] = closes ? 2 : 1;
            lead_s = closes ? 0 : lead;
            members_s = closes ? 0 : members + 1;
        }
        __syncthreads();
    }
    __syncthreads();
    // Each site's covectors turned forward by its frame: the six chart covectors and their reaches.
    for (uint32_t j = 0; j < T; j++) {
        const uint64_t qj = (site0 + j) * L + l;
        const bool site = mark[j] != 0;
        uint64_t mx[6] = {0, 0, 0, 0, 0, 0};
        for (uint32_t k = tid; k < N; k += B) {
            const wide ur = site ? fr.pa_frame[(qj * N + k) * 2] : 0, ui = site ? fr.pa_frame[(qj * N + k) * 2 + 1] : 0;
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
    // The transport covector (`Tower::reverse_joined`): each site's turn covector
    // g_φ(i) = Im(conj(G_q) q) + Im(conj(G_k) k) + Im(conj(G_w) w) − Im(conj(g_y) y), summed over the
    // later sites of its section, is the covector of each cell's unit-move turn, and the later sites'
    // met covectors, shared over the head's modes and negated, that of its log₂ ρ; each counted as
    // often as the move acted (`Δτ`, none at a cell the level is still at); both on 2^(−48). A
    // section that closes at a site parts the sums there. A thread takes a mode (then a head), its
    // cells in reverse order.
    for (uint32_t k = tid; k < N; k += B) {
        wide after = 0;
        for (uint32_t step = 0; step < T; step++) {
            const uint32_t i = T - 1 - step;
            const uint64_t qi = (site0 + i) * L + l;
            if (mark[i] != 0) {
                if (mark[i] == 2) {
                    after = 0;
                }
                const int64_t *pq = fr.pa_probe + (qi * N + k) * 2, *pk = fr.pa_key + (qi * N + k) * 2, *pw = fr.pa_value + (qi * N + k) * 2;
                const wide *cq = gq + ((uint64_t)i * N + k) * 2, *ck = gk + ((uint64_t)i * N + k) * 2, *cw = gw + ((uint64_t)i * N + k) * 2;
                const wide yr = fr.pa_current[qi * 2 * N + k], yi = fr.pa_current[qi * 2 * N + N + k];
                const wide gyr = fr.pa_gy[qi * 2 * N + k], gyi = fr.pa_gy[qi * 2 * N + N + k];
                const wide phi = (cq[0] * pq[1] - cq[1] * pq[0]) + (ck[0] * pk[1] - ck[1] * pk[0]) + (cw[0] * pw[1] - cw[1] * pw[0]) - (gyr * yi - gyi * yr);
                after += phi * ((wide)1 << (STATE_BITS - FACE_BITS));
            }
            const wide moves = law.news ? (wide)fr.ticks[qi] : 1;
            fr.pa_tturn[(site0 + i) * N + k] = moves * after;
        }
    }
    for (uint32_t hh = tid; hh < HH; hh += B) {
        const uint32_t from = fr.pa_heads[hh], to = fr.pa_heads[hh + 1];
        wide after = 0;
        for (uint32_t step = 0; step < T; step++) {
            const uint32_t i = T - 1 - step;
            const uint64_t qi = (site0 + i) * L + l;
            if (mark[i] == 2) {
                after = 0;
            }
            after += gmet[(uint64_t)i * HH + hh];
            const wide share = -div_nearest(after * ((wide)1 << (STATE_BITS - FACE_BITS)), (wide)(to - from));
            const wide moves = law.news ? (wide)fr.ticks[qi] : 1;
            for (uint32_t k = from; k < to; k++) {
                fr.pa_tlog[(site0 + i) * N + k] = moves * share;
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
    const TowerLevel lv = law.level[l];
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
    // sums the groups. With `accumulate` the family's sum is added to what `out` (and `bias_out`)
    // already hold, a second family on the same material (a packet's read on its fine level's).
    uint32_t groups;
    uint32_t accumulate;
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
            f.out[(uint64_t)row * f.cols + c] = f.accumulate ? f.out[(uint64_t)row * f.cols + c] + v : v;
        } else {
            f.bias_out[row] = f.accumulate ? f.bias_out[row] + v : v;
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
            f.out[row * f.cols + c] = f.accumulate ? f.out[row * f.cols + c] + sum : sum;
        } else {
            f.bias_out[row] = f.accumulate ? f.bias_out[row] + sum : sum;
        }
    }
}

// The encoding's covector: each cell's bottom covector summed at the class that arrived there (the
// closure's covector leaves the traces' encoding to the arrivals, `tower_reverse_heading`). Under a
// mutual contact the class's encoding is also the target the contact compares, and takes
// the contact's reaction G_E_u = 2β δz_u (y − E_u) at every cell, released entry by entry by
// 15 + b; the contact's constants take Σ δz_u (`Tower::mutual_return`).
extern "C" __global__ void tower_encoding(TowerLaw law, TowerFrame fr) {
    const uint32_t u = blockIdx.x, W = law.width, T = law.cells, A = law.alphabet;
    const uint64_t cells = (uint64_t)law.streams * T;
    for (uint32_t j = threadIdx.x; j < W; j += blockDim.x) {
        wide acc = 0;
        const wide e = fr.theta[law.encoding + (uint64_t)u * W + j];
        for (uint64_t q = 0; q < cells; q++) {
            const uint64_t s = q / T, t = q % T;
            if (fr.classes[s * (T + 1) + t] == u) {
                acc += fr.dx[q * W + j];
            }
            if (law.mutual) {
                const wide dzu = fr.dz[q * A + u];
                if (dzu != 0) {
                    acc += rel(dzu * ((wide)fr.contact_y[q * W + j] - e), FACE_BITS - 1 + law.mutual_shift);
                }
            }
        }
        // A later term of the motive's series adds to the earlier terms' sums.
        fr.gradient[law.encoding + (uint64_t)u * W + j] = law.term ? fr.gradient[law.encoding + (uint64_t)u * W + j] + acc : acc;
    }
    if (law.mutual && threadIdx.x == 0) {
        wide acc = 0;
        for (uint64_t q = 0; q < cells; q++) {
            acc += fr.dz[q * A + u];
        }
        fr.gradient[law.readout_bias + u] = acc;
    }
}

// [agent-inferred, October 31] **The credit's per-mode moments, moved beside the forward** (record
// §27; `Tower::advance_moments`): one block a stream (`blockIdx.x`) and credited level
// (`blockIdx.y`), one thread a mode, the read's cells in order. From the move, push and state the
// forward kept for the read that advances the credit (and the packet as the level above found it),
// each moment takes the move's sub-steps (`v`, `K` and the gate's drive reading the state between
// them; the packet's moments the packet's, rested where the level above ticked), and each cell's
// turn and coefficients are written for `tower_credit`; the moments' end goes to the advance.
// The two sets are unrolled so their moments stay in registers, a cell's push quotients `ρ p / γ`
// and gate factors are read once a cell, not once a sub-step, and the products of 64-bit words
// (the move, the state, the moments) are taken as such (`mul64`, record §28).
extern "C" __global__ void tower_credit_moments(TowerLaw law, TowerFrame fr) {
    const uint32_t s = blockIdx.x, cx = blockIdx.y, B = blockDim.x;
    const uint32_t N = law.modes, W = law.width, T = law.cells, L = law.levels, CL = law.credit;
    const uint32_t l = law.credit_from + cx, F0 = law.news_first, PK = law.packets;
    const bool with_packet = cr_packet(law, l);
    const uint32_t NP = cr_packet_index(law, L), px = cr_packet_index(law, l);
    const wide one = (wide)1 << MOVE_BITS;
    __shared__ uint32_t st;
    if (threadIdx.x == 0) {
        st = 0;
    }
    __syncthreads();
    for (uint32_t k = threadIdx.x; k < N; k += B) {
        const int64_t *gf = fr.gates + ((uint64_t)l * N + k) * 4;
        const int64_t g0 = gf[0], g1 = gf[1];
        const wide g3 = gf[3];
        const wide modulus = gf[2] > 0 ? gf[2] : 1;
        int64_t M[2][6] = {{0, 0, 0, 0, 0, 0}, {0, 0, 0, 0, 0, 0}};
#pragma unroll
        for (uint32_t set = 0; set < 2; set++) {
            if (set == 1 && !with_packet) {
                continue;
            }
            const int64_t *blk = fr.cr_open + cr_block(law, s, cx, set) + 2ull * N * W;
#pragma unroll
            for (uint32_t i = 0; i < 3; i++) {
                M[set][2 * i] = blk[2ull * i * N + 2 * k];
                M[set][2 * i + 1] = blk[2ull * i * N + 2 * k + 1];
            }
        }
        for (uint32_t t = 0; t < T; t++) {
            const uint64_t qc = (uint64_t)s * T + t, q = qc * L + l, qk = ((qc * CL + cx) * N + k) * 2;
            const uint32_t ticks = fr.cr_tick[qc * CL + cx];
            // Where the packet this level carries rested: the level above ticked at this cell.
            const bool rests = with_packet && fr.cr_tick[qc * CL + cx + 1] > 0;
            if (with_packet && k == 0) {
                fr.cr_rest[qc * CL + cx] = rests ? 1u : 0u;
            }
            wide tr = one, ti = 0, cpr = 0, cpi = 0, cw[2][2] = {{0, 0}, {0, 0}};
            if (ticks > 0) {
                const int64_t *mv = fr.moves + (q * N + k) * 6;
                const wide open = mv[0], rho = mv[1], gamma = mv[2];
                const int64_t lr = mv[3], li = mv[4];
                const bool held = mv[5] != 0;
                const wide p_r = fr.push[q * 2 * N + k], p_i = fr.push[q * 2 * N + N + k];
                const wide pr = rel(gamma * p_r, MOVE_BITS), pi = rel(gamma * p_i, MOVE_BITS);
                wide by_modulus = 0, by_gate = 0, ur = 0, ui = 0;
                if (!held) {
                    by_modulus = div_nearest((wide)GATE_REACH * open * rho, modulus);
                    by_gate = rel(rho * g3, MOVE_BITS);
                    by_gate = rel(by_gate * (wide)law.ln2_square, MOVE_BITS);
                    by_gate = rel(by_gate * open, MOVE_BITS);
                    by_gate = (wide)GATE_REACH * rel(by_gate * (one - open), MOVE_BITS);
                    ur = div_nearest(rho * p_r, gamma);
                    ui = div_nearest(rho * p_i, gamma);
                }
#pragma unroll
                for (uint32_t set = 0; set < 2; set++) {
                    if (set == 1 && !with_packet) {
                        continue;
                    }
                    // The state the moments follow before this cell: the modes', or the packet's.
                    int64_t sr, si;
                    if (set == 0) {
                        const int64_t *h0 = t == 0 ? fr.opening + (((uint64_t)s * L + l) * N + k) * 2 : fr.state + (((qc - 1) * L + l) * N + k) * 2;
                        sr = h0[0];
                        si = h0[1];
                    } else if (t == 0) {
                        const int64_t *a = fr.pk_open + (((uint64_t)s * PK + (l + 1 - F0)) * N + k) * 2;
                        sr = a[0];
                        si = a[1];
                    } else if (fr.cr_tick[(qc - 1) * CL + cx + 1] > 0) {
                        sr = 0;
                        si = 0;
                    } else {
                        const int64_t *a = fr.pk_state + ((((qc - 1) * PK + (l + 1 - F0)) * N + k) * 2);
                        sr = a[0];
                        si = a[1];
                    }
                    int64_t *A = M[set];
                    for (uint32_t j = 0; j < ticks; j++) {
                        wide a0, a1, xr, xi, nr_, ni_, a4, a5;
                        cmul64(lr, li, A[0], A[1], &a0, &a1);
                        cmul64(lr, li, A[2], A[3], &xr, &xi);
                        cmul64(lr, li, sr, si, &nr_, &ni_);
                        A[2] = fit64(xr - ni_, &st);
                        A[3] = fit64(xi + nr_, &st);
                        cmul64(lr, li, A[4], A[5], &a4, &a5);
                        cmul(lr, li, cw[set][0], cw[set][1], &cw[set][0], &cw[set][1]);
                        if (!held) {
                            const wide vr = rel(mul64(g0, sr) - mul64(g1, si), MOVE_BITS) - ur;
                            const wide vi = rel(mul64(g0, si) + mul64(g1, sr), MOVE_BITS) - ui;
                            A[0] = fit64(a0 + rel(vr * by_modulus, MOVE_BITS), &st);
                            A[1] = fit64(a1 + rel(vi * by_modulus, MOVE_BITS), &st);
                            const wide dr = rel(vr * by_gate, MOVE_BITS), di = rel(vi * by_gate, MOVE_BITS);
                            A[4] = fit64(a4 + dr, &st);
                            A[5] = fit64(a5 + di, &st);
                            cw[set][0] += dr;
                            cw[set][1] += di;
                        } else {
                            A[0] = fit64(a0, &st);
                            A[1] = fit64(a1, &st);
                            A[4] = fit64(a4, &st);
                            A[5] = fit64(a5, &st);
                        }
                        if (set == 0) {
                            cmul(lr, li, cpr, cpi, &cpr, &cpi);
                            cpr += gamma;
                            cmul(tr, ti, lr, li, &tr, &ti);
                        }
                        const int64_t sn = fit64(rel(mul64(lr, sr) - mul64(li, si), MOVE_BITS) + pr, &st);
                        si = fit64(rel(mul64(lr, si) + mul64(li, sr), MOVE_BITS) + pi, &st);
                        sr = sn;
                    }
                }
            }
            // The packet rests at the level above's tick, and its moments with it.
            if (rests) {
#pragma unroll
                for (uint32_t i = 0; i < 6; i++) {
                    M[1][i] = 0;
                }
            }
            fr.cr_turn[qk] = (int64_t)tr;
            fr.cr_turn[qk + 1] = (int64_t)ti;
            fr.cr_push[qk] = (int64_t)cpr;
            fr.cr_push[qk + 1] = (int64_t)cpi;
            fr.cr_gate[qk] = fit64(cw[0][0], &st);
            fr.cr_gate[qk + 1] = fit64(cw[0][1], &st);
            if (with_packet) {
                const uint64_t qp = ((qc * NP + px) * N + k) * 2;
                fr.cr_pgate[qp] = fit64(cw[1][0], &st);
                fr.cr_pgate[qp + 1] = fit64(cw[1][1], &st);
            }
        }
#pragma unroll
        for (uint32_t set = 0; set < 2; set++) {
            if (set == 1 && !with_packet) {
                continue;
            }
            int64_t *blk = fr.cr_next + cr_block(law, s, cx, set) + 2ull * N * W;
#pragma unroll
            for (uint32_t i = 0; i < 3; i++) {
                blk[2ull * i * N + 2 * k] = M[set][2 * i];
                blk[2ull * i * N + 2 * k + 1] = M[set][2 * i + 1];
            }
        }
    }
    __syncthreads();
    if (threadIdx.x == 0 && st != 0) {
        atomicOr(fr.status + s, st);
    }
}

// A row's halves against inputs (record §28): `r = h·2^32 + l' + 2^31` with `h = r >> 32` and
// `l' = (r mod 2^32) − 2^31` both signed 32-bit, so `Σ r x = 2^32 Σ h x + Σ l' x + 2^31 Σ x`; with
// `T max|x| < 2^32` each half's sum is below 2^63 whatever the rows' magnitude.
struct Halves {
    int32_t h, l;
};
__device__ __forceinline__ Halves halves(int64_t r) {
    return {(int32_t)(r >> 32), (int32_t)((uint32_t)r ^ 0x80000000u)};
}
// `c + a·b` for signed 32-bit `a`, `b` in one wide multiply-add (the compiler otherwise widens the
// operands and corrects their signs, five instructions for one).
__device__ __forceinline__ int64_t mad_wide(int32_t a, int32_t b, int64_t c) {
    int64_t d;
    asm("mad.wide.s32 %0, %1, %2, %3;" : "=l"(d) : "r"(a), "r"(b), "l"(c));
    return d;
}
__device__ __forceinline__ void halves_mac(int64_t *acc, Halves r, int32_t x) {
    acc[0] = mad_wide(r.h, x, acc[0]);
    acc[1] = mad_wide(r.l, x, acc[1]);
}
__device__ __forceinline__ wide halves_sum(const int64_t *acc, int64_t sx) {
    return (wide)acc[0] * ((wide)1 << 32) + (wide)acc[1] + (wide)sx * ((wide)1 << 31);
}

// The credit's staged chunk (record §28): `CREDIT_CELLS` cells of one warp's mode each, a
// warp a mode.
#define CREDIT_CELLS 32

// The entries' sums in the rows' halves, staged: the block takes its modes a warp's worth at a
// time (one mode a warp) and the cells `CREDIT_CELLS` at a time; every thread stages one cell of
// one mode, reading its turn and coefficients and computing its rows π_t c_t (the push's, the
// gate's, the packet gate's) into shared memory, with the chunk's inputs beside them; then each
// lane sums its two entries `j`, `j + 1` against the staged rows. The cells before the packet's
// rest sum the push's rows apart from those after it, and the packet gate's rows only from it.
// Each entry's output is M_T = whole·M_0 + release(Σ), as `tower_credit` states.
__device__ void credit_halves(const TowerLaw &law, const TowerFrame &fr, uint32_t s, uint32_t cx, bool with_packet, uint32_t NP, uint32_t px, uint32_t rest, const wide *whole, int64_t *rows, int32_t *xc, uint32_t *st) {
    const uint32_t N = law.modes, W = law.width, T = law.cells, CL = law.credit;
    const uint32_t tid = threadIdx.x, B = blockDim.x, G = B >> 5, lane = tid & 31, warp = tid >> 5;
    const uint32_t pairs = (W + 1) / 2, sets = with_packet ? 2 : 1;
    for (uint32_t k0 = 0; k0 < N; k0 += G) {
        for (uint32_t jp0 = 0; jp0 < pairs; jp0 += 32) {
            const uint32_t k = k0 + warp, j = 2 * (jp0 + lane);
            const bool mine = k < N && j < W, second = j + 1 < W;
            // [entry][re, im][high, low]: the push's before the rest and after it, the gate's, the
            // packet gate's; each entry's inputs' sums before and after the rest.
            int64_t before[2][2][2] = {}, after[2][2][2] = {}, gate[2][2][2] = {}, pg[2][2][2] = {};
            int64_t sb[2] = {0, 0}, sa[2] = {0, 0};
            for (uint32_t c = 0; c < T; c += CREDIT_CELLS) {
                __syncthreads();
                // Stage: one cell of one mode a thread, consecutive threads consecutive modes.
                for (uint32_t i = tid; i < CREDIT_CELLS * G; i += B) {
                    const uint32_t tt = i / G, kk = i % G, t = c + tt, m = k0 + kk;
                    int64_t *r = rows + (uint64_t)i * 6;
                    if (t < T && m < N) {
                        const uint64_t qk = ((((uint64_t)s * T + t) * CL + cx) * N + m) * 2;
                        const wide ar = fr.cr_turn[qk], ai = fr.cr_turn[qk + 1];
                        wide re, im;
                        cmul(ar, ai, fr.cr_push[qk], fr.cr_push[qk + 1], &re, &im);
                        r[0] = fit64(re, st);
                        r[1] = fit64(im, st);
                        cmul(ar, ai, fr.cr_gate[qk], fr.cr_gate[qk + 1], &re, &im);
                        r[2] = fit64(re, st);
                        r[3] = fit64(im, st);
                        r[4] = 0;
                        r[5] = 0;
                        if (with_packet) {
                            const uint64_t qp = ((((uint64_t)s * T + t) * NP + px) * N + m) * 2;
                            cmul(ar, ai, fr.cr_pgate[qp], fr.cr_pgate[qp + 1], &re, &im);
                            r[4] = fit64(re, st);
                            r[5] = fit64(im, st);
                        }
                    } else {
                        for (uint32_t f = 0; f < 6; f++) {
                            r[f] = 0;
                        }
                    }
                }
                for (uint32_t i = tid; i < CREDIT_CELLS * W; i += B) {
                    const uint32_t tt = i / W, jj = i % W, t = c + tt;
                    xc[i] = t < T ? fr.cr_x[(((uint64_t)s * T + t) * CL + cx) * W + jj] : 0;
                }
                __syncthreads();
                if (!mine) {
                    continue;
                }
                const uint32_t span = min((uint32_t)CREDIT_CELLS, T - c);
                for (uint32_t u = 0; u < span; u++) {
                    const uint32_t t = c + u;
                    const int64_t *r = rows + ((uint64_t)u * G + warp) * 6;
                    const int32_t x0 = xc[u * W + j], x1 = second ? xc[u * W + j + 1] : 0;
                    const Halves pr = halves(r[0]), pi = halves(r[1]), gr = halves(r[2]), gi = halves(r[3]);
                    halves_mac(gate[0][0], gr, x0);
                    halves_mac(gate[0][1], gi, x0);
                    halves_mac(gate[1][0], gr, x1);
                    halves_mac(gate[1][1], gi, x1);
                    if (t < rest) {
                        sb[0] += x0;
                        sb[1] += x1;
                        halves_mac(before[0][0], pr, x0);
                        halves_mac(before[0][1], pi, x0);
                        halves_mac(before[1][0], pr, x1);
                        halves_mac(before[1][1], pi, x1);
                    } else {
                        sa[0] += x0;
                        sa[1] += x1;
                        halves_mac(after[0][0], pr, x0);
                        halves_mac(after[0][1], pi, x0);
                        halves_mac(after[1][0], pr, x1);
                        halves_mac(after[1][1], pi, x1);
                        if (with_packet) {
                            const Halves qr = halves(r[4]), qi = halves(r[5]);
                            halves_mac(pg[0][0], qr, x0);
                            halves_mac(pg[0][1], qi, x0);
                            halves_mac(pg[1][0], qr, x1);
                            halves_mac(pg[1][1], qi, x1);
                        }
                    }
                }
            }
            if (!mine) {
                continue;
            }
#pragma unroll
            for (uint32_t e = 0; e < 2; e++) {
                if (e == 1 && !second) {
                    continue;
                }
                for (uint32_t set = 0; set < sets; set++) {
                    const uint32_t t0 = set == 1 ? rest : 0;
                    for (uint32_t fam = 0; fam < 2; fam++) {
                        wide sr, si;
                        if (fam == 0) {
                            sr = halves_sum(after[e][0], sa[e]);
                            si = halves_sum(after[e][1], sa[e]);
                            if (set == 0) {
                                sr += halves_sum(before[e][0], sb[e]);
                                si += halves_sum(before[e][1], sb[e]);
                            }
                        } else if (set == 0) {
                            sr = halves_sum(gate[e][0], sb[e] + sa[e]);
                            si = halves_sum(gate[e][1], sb[e] + sa[e]);
                        } else {
                            sr = halves_sum(pg[e][0], sa[e]);
                            si = halves_sum(pg[e][1], sa[e]);
                        }
                        const unsigned shift = fam == 0 ? MOVE_BITS + FACE_BITS - STATE_BITS : FACE_BITS;
                        const uint64_t place = (fam == 0 ? 0 : 2ull * N * W + 6ull * N) + ((uint64_t)k * W + j + e) * 2;
                        const int64_t *m0 = fr.cr_open + cr_block(law, s, cx, set) + place;
                        int64_t *m1 = fr.cr_next + cr_block(law, s, cx, set) + place;
                        wide er = 0, ei = 0;
                        if (t0 == 0) {
                            cmul(whole[2 * k], whole[2 * k + 1], m0[0], m0[1], &er, &ei);
                        }
                        m1[0] = fit64(er + rel(sr, shift), st);
                        m1[1] = fit64(ei + rel(si, shift), st);
                    }
                }
            }
        }
    }
}

// The entries' sums in 128 bits (inputs too large for the halves): one output a thread.
__device__ void credit_wide(const TowerLaw &law, const TowerFrame &fr, uint32_t s, uint32_t cx, bool with_packet, uint32_t NP, uint32_t px, uint32_t rest, const int32_t *xs, uint64_t xstep, const wide *whole, uint32_t *st) {
    const uint32_t N = law.modes, W = law.width, T = law.cells, CL = law.credit;
    const uint32_t sets = with_packet ? 2 : 1;
    const uint64_t outputs = (uint64_t)sets * 2 * N * W;
    for (uint64_t o = threadIdx.x; o < outputs; o += blockDim.x) {
        const uint32_t set = (uint32_t)(o / (2ull * N * W));
        const uint32_t fam = (uint32_t)((o / ((uint64_t)N * W)) % 2);
        const uint32_t k = (uint32_t)((o / W) % N), j = (uint32_t)(o % W);
        const uint32_t t0 = set == 1 ? rest : 0;
        const bool packet_rows = fam == 1 && set == 1;
        const int64_t *rows = fam == 0 ? fr.cr_push : (set == 0 ? fr.cr_gate : fr.cr_pgate);
        wide sr = 0, si = 0;
        for (uint32_t t = t0; t < T; t++) {
            const uint64_t qc = ((uint64_t)s * T + t) * CL + cx;
            const uint64_t qr = packet_rows ? ((uint64_t)s * T + t) * NP + px : qc;
            const wide x = xs[t * xstep + j];
            sr += (wide)rows[(qr * N + k) * 2] * x;
            si += (wide)rows[(qr * N + k) * 2 + 1] * x;
        }
        const unsigned shift = fam == 0 ? MOVE_BITS + FACE_BITS - STATE_BITS : FACE_BITS;
        const uint64_t place = (fam == 0 ? 0 : 2ull * N * W + 6ull * N) + ((uint64_t)k * W + j) * 2;
        const int64_t *m0 = fr.cr_open + cr_block(law, s, cx, set) + place;
        int64_t *m1 = fr.cr_next + cr_block(law, s, cx, set) + place;
        wide er = 0, ei = 0;
        if (t0 == 0) {
            cmul(whole[2 * k], whole[2 * k + 1], m0[0], m0[1], &er, &ei);
        }
        m1[0] = fit64(er + rel(sr, shift), st);
        m1[1] = fit64(ei + rel(si, shift), st);
    }
}

// The credit's material moments moved through the read's cells in closed form
// (`Tower::advance_moments`): one block a stream (`blockIdx.x`) and credited level (`blockIdx.y`).
// Each mode's thread turns its cells' turns into the turn after each cell, π_s, kept in place of
// the cell's turn, and the whole section's; then each output P_kj (and W_kj, and the packet's) is
// M_T = whole·M_0 + release(Σ_s π_s c_s x_s) (`credit_halves`, its rows staged as they are
// computed, or `credit_wide`), the packet's sums from after its last rest and its opening moments
// kept only when it never rested.
extern "C" __global__ void __launch_bounds__(TOWER_THREADS, 2) tower_credit(TowerLaw law, TowerFrame fr) {
    const uint32_t s = blockIdx.x, cx = blockIdx.y, tid = threadIdx.x, B = blockDim.x;
    const uint32_t N = law.modes, W = law.width, T = law.cells, CL = law.credit;
    const uint32_t l = law.credit_from + cx;
    const bool with_packet = cr_packet(law, l);
    const uint32_t NP = cr_packet_index(law, law.levels), px = cr_packet_index(law, l);
    const wide one = (wide)1 << MOVE_BITS;
    // [N][2] whole turns, then the staged chunk's rows [CREDIT_CELLS][B/32][6] and inputs
    // [CREDIT_CELLS][W] (`credit_shared`).
    extern __shared__ __align__(16) unsigned char smem[];
    wide *whole = (wide *)smem;
    int64_t *rows = (int64_t *)(smem + 32ull * N);
    int32_t *xc = (int32_t *)(smem + 32ull * N + 48ull * CREDIT_CELLS * (B >> 5));
    __shared__ uint32_t st, from;
    // The inputs' largest magnitude: below 2^32 / T the sums run in the rows' halves.
    __shared__ unsigned long long x_max;
    if (tid == 0) {
        x_max = 0;
        st = 0;
        from = 0;
        if (with_packet) {
            for (uint32_t t = T; t > 0; t--) {
                if (fr.cr_rest[((uint64_t)s * T + t - 1) * CL + cx]) {
                    from = t;
                    break;
                }
            }
        }
    }
    __syncthreads();
    {
        uint64_t mx = 0;
        for (uint32_t i = tid; i < T * W; i += B) {
            const uint32_t t = i / W, j = i % W;
            mx = max(mx, magnitude(fr.cr_x[(((uint64_t)s * T + t) * CL + cx) * W + j]));
        }
        atomicMax(&x_max, (unsigned long long)mx);
    }
    // The turn after each cell, in place of the cell's own.
    for (uint32_t k = tid; k < N; k += B) {
        wide ar = one, ai = 0;
        for (uint32_t step = 0; step < T; step++) {
            const uint32_t t = T - 1 - step;
            int64_t *turn = fr.cr_turn + ((((uint64_t)s * T + t) * CL + cx) * N + k) * 2;
            const wide tr = turn[0], ti = turn[1];
            turn[0] = fit64(ar, &st);
            turn[1] = fit64(ai, &st);
            cmul(ar, ai, tr, ti, &ar, &ai);
        }
        whole[2 * k] = ar;
        whole[2 * k + 1] = ai;
    }
    __syncthreads();
    if ((uwide)x_max * (uwide)T < ((uwide)1 << 32)) {
        credit_halves(law, fr, s, cx, with_packet, NP, px, from, whole, rows, xc, &st);
    } else {
        // The cells' rows π_t c_t in place of the coefficients, then the sums in 128 bits.
        for (uint32_t i = tid; i < T * N; i += B) {
            const uint32_t t = i / N, k = i % N;
            const uint64_t qk = ((((uint64_t)s * T + t) * CL + cx) * N + k) * 2;
            const wide ar = fr.cr_turn[qk], ai = fr.cr_turn[qk + 1];
            wide r, im;
            cmul(ar, ai, fr.cr_push[qk], fr.cr_push[qk + 1], &r, &im);
            fr.cr_push[qk] = fit64(r, &st);
            fr.cr_push[qk + 1] = fit64(im, &st);
            cmul(ar, ai, fr.cr_gate[qk], fr.cr_gate[qk + 1], &r, &im);
            fr.cr_gate[qk] = fit64(r, &st);
            fr.cr_gate[qk + 1] = fit64(im, &st);
            if (with_packet) {
                const uint64_t qp = ((((uint64_t)s * T + t) * NP + px) * N + k) * 2;
                cmul(ar, ai, fr.cr_pgate[qp], fr.cr_pgate[qp + 1], &r, &im);
                fr.cr_pgate[qp] = fit64(r, &st);
                fr.cr_pgate[qp + 1] = fit64(im, &st);
            }
        }
        __syncthreads();
        credit_wide(law, fr, s, cx, with_packet, NP, px, from, fr.cr_x + ((uint64_t)s * T * CL + cx) * W, (uint64_t)CL * W, whole, &st);
    }
    __syncthreads();
    if (tid == 0 && st != 0) {
        atomicOr(fr.status + s, st);
    }
}

// The opening's credit meets the material moments (`Tower::reverse_joined`): one thread an entry of
// a credited level's push (re and im) and gate, or of its gate bias, summing over the streams and
// the level's sets (its own moments and its packet's) each stream's release, added to the covector
// the outer sums wrote (integer sums: any order).
extern "C" __global__ void tower_credit_meet(TowerLaw law, TowerFrame fr) {
    const uint32_t cx = blockIdx.y, N = law.modes, W = law.width, CL = law.credit;
    const uint32_t l = law.credit_from + cx;
    const TowerLevel lv = law.level[l];
    const uint32_t sets = cr_packet(law, l) ? 2 : 1;
    const uint64_t items = (uint64_t)N * W + N;
    for (uint64_t e = (uint64_t)blockIdx.x * blockDim.x + threadIdx.x; e < items; e += (uint64_t)gridDim.x * blockDim.x) {
        const bool bias = e >= (uint64_t)N * W;
        const uint32_t k = bias ? (uint32_t)(e - (uint64_t)N * W) : (uint32_t)(e / W), j = bias ? 0 : (uint32_t)(e % W);
        wide pre = 0, pim = 0, gate = 0, gbias = 0;
        for (uint32_t s = 0; s < law.streams; s++) {
            for (uint32_t set = 0; set < sets; set++) {
                const int64_t *cov = fr.cr_cov + ((((uint64_t)s * CL + cx) * 2 + set) * N + k) * 2;
                const wide ar = cov[0], ai = cov[1];
                const int64_t *blk = fr.cr_open + cr_block(law, s, cx, set);
                if (bias) {
                    const int64_t *q = blk + 2ull * N * W + 4ull * N + 2 * k;
                    gbias += rel(ar * (wide)q[0] + ai * (wide)q[1], COVECTOR_BITS);
                } else {
                    const int64_t *p = blk + ((uint64_t)k * W + j) * 2;
                    pre += rel(ar * (wide)p[0] + ai * (wide)p[1], STATE_BITS - FACE_BITS);
                    pim += rel(ai * (wide)p[0] - ar * (wide)p[1], STATE_BITS - FACE_BITS);
                    const int64_t *g = blk + 2ull * N * W + 6ull * N + ((uint64_t)k * W + j) * 2;
                    gate += rel(ar * (wide)g[0] + ai * (wide)g[1], STATE_BITS - FACE_BITS);
                }
            }
        }
        if (bias) {
            fr.gradient[lv.gate_bias + k] += gbias;
        } else {
            fr.gradient[lv.push_re + (uint64_t)k * W + j] += pre;
            fr.gradient[lv.push_im + (uint64_t)k * W + j] += pim;
            fr.gradient[lv.gate + (uint64_t)k * W + j] += gate;
        }
    }
}

// The moves' covectors summed over the streams.
extern "C" __global__ void tower_moves(TowerLaw law, TowerFrame fr) {
    const uint32_t l = blockIdx.x, N = law.modes, L = law.levels;
    const TowerLevel lv = law.level[l];
    for (uint32_t k = threadIdx.x; k < N; k += blockDim.x) {
        wide re = 0, im = 0;
        for (uint32_t s = 0; s < law.streams; s++) {
            const wide *g = fr.moves_g + (((uint64_t)s * L + l) * N + k) * 2;
            re += g[0];
            im += g[1];
        }
        fr.gradient[lv.move_re + k] = law.term ? fr.gradient[lv.move_re + k] + re : re;
        fr.gradient[lv.move_im + k] = law.term ? fr.gradient[lv.move_im + k] + im : im;
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
        const TowerLevel lv = law.level[l];
        fr.gradient[(second ? lv.pair_bias : lv.contact_bias) + i] = acc;
    }
}

// The paired contacts' split read (`Tower::split_read_of`), one block a dormant pair `e` of one
// level `l` (`grid.x` the pair, `grid.y` the level): over every stream's cells, in chunks of the
// block (one thread a cell), each cell's `y = v·r̂`, `φ = y²`, `δv = δv_e + δv_(e+H)`, its score
// term `s = δv φ` and its turned weight `δv y` (each released by 16, as the host releases them);
// the score and its squares summed over the block, and the turned sum `Σ (δv y) r̂` over `B/W`
// groups of each chunk's cells (integer sums: any order). A score term at or past 2^SCORE_BITS is
// refused, as the host refuses it: below it, the squares of fewer than 2^31 cells stay below 2^127.
extern "C" __global__ void __launch_bounds__(TOWER_THREADS) tower_split_read(TowerLaw law, TowerFrame fr) {
    const uint32_t e = blockIdx.x, l = blockIdx.y, tid = threadIdx.x, B = blockDim.x;
    const uint32_t W = law.width, F = law.contacts, H = F / 2, L = law.levels;
    const uint32_t G = B / W > 0 ? B / W : 1;
    const uint64_t Q = (uint64_t)law.streams * law.cells;
    extern __shared__ __align__(16) unsigned char smem[];
    unsigned char *at = smem;
    wide *part = (wide *)carve(at, sizeof(wide) * G * W);
    uwide *redw = (uwide *)carve(at, sizeof(uwide) * 32);
    wide *turn = (wide *)carve(at, sizeof(wide) * B);
    int32_t *v = (int32_t *)carve(at, 4ull * W);
    __shared__ uint32_t st;
    if (tid == 0) {
        st = 0;
    }
    const int32_t *dir = fr.split_dir + ((uint64_t)l * H + e) * W;
    for (uint32_t j = tid; j < W; j += B) {
        v[j] = dir[j];
    }
    for (uint32_t idx = tid; idx < G * W; idx += B) {
        part[idx] = 0;
    }
    __syncthreads();
    const wide bound = (wide)1 << SCORE_BITS;
    wide score = 0;
    uwide squares = 0;
    for (uint64_t c0 = 0; c0 < Q; c0 += B) {
        const uint64_t q = c0 + tid;
        wide qv = 0;
        if (q < Q) {
            const uint64_t ql = q * L + l;
            const int32_t *r = fr.read + ql * W;
            wide dotv = 0;
            for (uint32_t j = 0; j < W; j++) {
                dotv += (wide)v[j] * (wide)r[j];
            }
            const wide y = rel(dotv, FACE_BITS);
            const wide phi = rel(y * y, FACE_BITS);
            const wide dv = (wide)fr.split_dv[ql * F + e] + (wide)fr.split_dv[ql * F + e + H];
            const wide s = rel(dv * phi, FACE_BITS);
            if (s >= bound || s <= -bound) {
                atomicOr(&st, TOWER_REFUSED_CARRIER);
            } else {
                score += s;
                squares += (uwide)(s * s);
            }
            qv = rel(dv * y, FACE_BITS);
        }
        turn[tid] = qv;
        __syncthreads();
        const uint32_t chunk = (uint32_t)(Q - c0 < B ? Q - c0 : B);
        for (uint32_t idx = tid; idx < G * W; idx += B) {
            const uint32_t g = idx / W, j = idx % W;
            const uint32_t from = (uint32_t)((uint64_t)chunk * g / G), to = (uint32_t)((uint64_t)chunk * (g + 1) / G);
            wide sum = 0;
            for (uint32_t c = from; c < to; c++) {
                sum += turn[c] * (wide)fr.read[((c0 + c) * L + l) * W + j];
            }
            part[idx] += sum;
        }
        __syncthreads();
    }
    const wide total = (wide)block_sum((uwide)score, redw);
    const wide sq = (wide)block_sum(squares, redw);
    wide *out = fr.split_out + ((uint64_t)l * H + e) * (2 + W);
    for (uint32_t j = tid; j < W; j += B) {
        wide sum = 0;
        for (uint32_t g = 0; g < G; g++) {
            sum += part[g * W + j];
        }
        out[2 + j] = sum;
    }
    if (tid == 0) {
        out[0] = total;
        out[1] = sq;
        if (st != 0) {
            atomicOr(fr.status, st);
        }
    }
}

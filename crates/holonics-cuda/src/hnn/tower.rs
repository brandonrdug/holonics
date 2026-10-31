//! **The gated tower's training pass on the card** (#404, #76): the section's forward and reverse
//! of `holonics::hnn::tower` ([`holonics::hnn::tower::realization`]) realized resident, returning
//! the host's bits.
//!
//! [definition; agent-inferred, October 25] **What runs where.** [`TowerCard`] is a
//! [`PassRealization`]: each section uploads the material (and its transposed matrix families,
//! `tower_transpose`), the gated moves' founded faces, the streams' classes, targets and opening
//! states; the card reads every stream forward (`tower_forward`), returns the streams' covector by
//! the reverse scan and sums it over the streams and cells (`tower_reverse_*`, `tower_outer`,
//! `tower_encoding`, `tower_moves`), and the host reads back the faces at their targets, the
//! continuing states and the summed covector. The moments, the step, the certificate and the
//! deposit stay with the learner (`TowerLearner::section_realized`), whose rereads come back
//! through the card's forward. Integer sums are associative, so the card's covector summed over
//! streams and cells in its own order is the host's stream-by-stream sum, bit for bit.
//!
//! [definition] **The declaration the card carries**: a gated tower, turned or not (each cell's
//! founded unit turned by the arriving turn, composed from the ladder's dyadic turns, and the turn's
//! covector returned through its family and summed against the level's input), pumped or not (a
//! turned mode's move the parametron's, `α_t h + β_t conj(h)`, its pump's opening, depth, axis and
//! `β_t` kept at each cell for the reverse, and the depth's and axis's covectors returned through
//! their families and summed against the level's input; never beside a news clock), with or
//! without a rotor (each arriving class steps and turns a level's rings before the move,
//! `h' = T P^σ h` from the rotor's resident keys, and the modes' scan carries each step's covector
//! back through the monomial's adjoint, the modes of a block exchanging it; never beside the ring
//! face or a news clock), its contacts rectifying, the pair contact or its foil (the second drive
//! `b = W_b r̂ + b_b` read beside the first and kept at each cell for the reverse, the product
//! `v = a ⊙ b`, or the foil's `a b_b + b_a (b − b_b)`, released to the face; the reverse returns
//! each drive's covector through its partner, the foil's through the other drive's bias, and sums
//! the foil's biases on their own, `tower_pair_biases`), with or without strands (each stream's
//! residues and orientation heard from the arriving class's word, one thread a ring, through the
//! strands' resident table, their faces read off the rings' resident faces at their level's
//! contacts beside `r̂`, and their materials' covectors `δa ⊗ s`, `δb ⊗ s` summed by the outer
//! sums; the faces carry none), with or without the clocked levels' passage credit under a news
//! clock (`LevelCredit`: resident between sections in [`ResidentCredit`], each credited level's
//! moments taking its moves' sub-steps in the forward, its material moments summed in closed form by
//! `tower_credit`, and at the opening the carried modes' and packet's covectors met in the modes'
//! scan and `tower_credit_meet`), any number of levels (each level's words
//! resident on the card, which the law's parameter words address), streams of one section length, with
//! or without the pair face (its values resident on the card beside the material, read at each
//! cell's pair of the class before and the class arriving) and with or without the ring face (its
//! ranks carried by every stream beside its modes, each riding its level's mode or its founded pair
//! move at the cell's pair, its pools generated from `b` and `E₀` where the material is read, and
//! its face read through the pair contact with the top face), and with or without a news clock
//! (`NewsClock`, never beside the ring face: each stream carries its open face and phase beside its
//! modes, the forward reads every level's ticks from the arriving class's code under the open face
//! and each level's modes take their step once a tick with the arrival held, and the modes' scan
//! carries the covector back through each tick; participation beside it admits a level's sites at
//! its ticks alone, holds its current between them and closes each level's section at its own
//! count, within a call or across calls; under the clock, a level at a cell where it is still
//! computes only its contacts, its push and gate skipped and, without participation, its read held
//! from its last tick, the faces unchanged; and with the packets, `Tower::join_packets`, each
//! clocked level carries its open packet through the fine level's moves, hears its read at a tick
//! as the input of its push, gate and turn, and returns the read's covector to the fine level's read
//! and scan, `tower_reverse_packet`; and with the heading, `Tower::join_heading`, each clocked level
//! reads its heading from its modes before the arrival for its closure and after it for the face,
//! which reads it through the descent, carries the open trace of its span and closes it at a tick,
//! the section's closure is read at the forward's end (read, not learned), and the face's
//! covector returns through the descent to the heading after each cell and the read covector of
//! the cell's own state, `tower_reverse_ahead` and `tower_reverse_heading`). Any other is refused before a
//! launch ([`TowerCard::admits`]), never run on a partial law.
//!
//! # The realizations (hardware law)
//!
//! | Kernel | Block | Thread | A thread loops over |
//! |---|---|---|---|
//! | `tower_transpose` | a grid striding one matrix family (`grid.y` the family) | one material entry | — |
//! | `tower_forward` | one stream (the cells in order: each state moves from the one before) | one output of each stage of a cell: the pair face's lift, a strands' ring (its three residues heard byte by byte, then their faces), a push or gate logit, a mode's move, a ring rank's advance and face, a read, a contact, a return part, a class's face (with its pair read and the ring's pair read); 256 threads | the stage's outputs (`o ≡ t`), within each its row's weights (a contact both its drives under the pair law; the return's contacts in `256/W` groups; a ring rank its factors) |
//! | `tower_reverse_top`, `tower_reverse_contacts`, `tower_reverse_dx` | one cell of one stream | one output of each stage (the ring's readout covector, its face's and each rank's read covector among them); 256 threads | the stage's outputs, within each its column's weights |
//! | `tower_reverse_ahead` | one cell of one stream | one coordinate of `Dᵀ δx` at each clocked level, then one of its ratio's adjoint | the top's covector against a column of the descent |
//! | `tower_reverse_packet` | one cell of one stream, at a level that hears a packet | one coordinate of the packet read's covector, then one of the packet's | the read's coordinates, then a mode's column of the fine level's read |
//! | `tower_reverse_heading` | one stream of one clocked level | one coordinate of the read covector | the stream's cells in order |
//! | `tower_reverse_modes` | one stream of one level (under a rotor, exactly one thread a mode, the block exchanging each step's covector through shared memory) | one mode | the stream's cells in reverse order (the scan) |
//! | `tower_reverse_ring` | one stream | one ring rank's scan step, then one face coordinate, then one factor entry | the stream's cells in reverse order, every rank's scan carried together; a coordinate the ranks in their order |
//! | `tower_outer_x32`, `tower_outer_x64` | a tile of 16 rows × 64 columns of one family's covector (the pair face's readout and lift, the ring's readout and the strands' materials among them) | four outputs of one column | every stream, its cells in chunks of 32 staged in shared memory |
//! | `tower_ring_factors` | a grid striding the ring's factors | one factor entry | the streams |
//! | `tower_encoding` | one class | one face coordinate | every cell, summing where its class arrived |
//! | `tower_moves` | one level | one mode | the streams |
//! | `tower_credit` | one stream of one credited level (`grid.y`) | one mode for the turns after each cell and the rows, then one entry of the material moments | the stream's cells in reverse order, then its cells |
//! | `tower_credit_meet` | a grid striding a credited level's push, gate and gate-bias entries (`grid.y` the level) | one entry | the streams and the level's two sets |
//! | `tower_pair_biases` (the foil's) | a grid striding each level's two bias covectors | one bias entry | every cell |
//! | `tower_split_read` (the paired contacts' split read) | one dormant pair of one level (`grid.y` the level) | one cell of a chunk of the block's width, then one output of the turned sum in `256/W` groups | every stream's cells, a chunk at a time |
use core::ffi::c_void;
use std::time::Instant;

use holonics::hnn::tower::participation::LevelSites;
use holonics::hnn::tower::realization::{PassRead, PassRealization, ResidentLaw, Slot};
use holonics::hnn::tower::split::{PairRead, PairedContacts, SplitRead};
use holonics::hnn::tower::{ContactLaw, LevelCredit, Tower, TowerError, TowerFace, TowerState};

use crate::cuda::{Dim3, Module};
use crate::hnn::card::{Card, CardBuffer};
use crate::hnn::DeviceError;

/// The PTX image of `kernels/tower.cu`, compiled by `build.rs`.
const IMAGE: &[u8] = include_bytes!(concat!(env!("OUT_DIR"), "/tower.ptx"));

/// The kernels' block (`TOWER_THREADS`).
const THREADS: u32 = 256;
/// The turned modes' ladder `e^(iπ/2^i)`, `i = 0..=16` (`TOWER_LADDER`).
const LADDER: usize = 17;
/// The outer sums' tile (`OUTER_ROWS`, `OUTER_COLS`).
const OUTER_ROWS: u32 = 16;
const OUTER_COLS: u32 = 64;

type Result<T> = std::result::Result<T, TowerError>;

fn device(error: DeviceError) -> TowerError {
    TowerError::Realization(format!("the card: {error}"))
}

/// One level's words (`TowerLevel`).
#[repr(C)]
#[derive(Clone, Copy, Default, Debug)]
struct LevelWords {
    move_re: u64,
    move_im: u64,
    push_re: u64,
    push_im: u64,
    read_re: u64,
    read_im: u64,
    contact: u64,
    contact_bias: u64,
    ret: u64,
    ret_bias: u64,
    gate: u64,
    gate_bias: u64,
    turn: u64,
    turn_bias: u64,
    pump: u64,
    pump_bias: u64,
    pump_axis: u64,
    pump_axis_bias: u64,
    pair: u64,
    pair_bias: u64,
    reach: [u64; 11],
    /// Participation's families and the first nine's reaches (zero without it).
    pa: [u64; 10],
    pa_reach: [u64; 9],
    /// The passage's `W₁ˣ` and its reach (zero without it).
    passage: u64,
    passage_reach: u64,
    /// A clocked level's section `B r^(l−F)` on `2^(−20)` bits (unread below the clock's first
    /// clocked level and without a clock; [`NewsClock`]).
    section: u64,
    /// The heading's read `C^→` (re, im), its descent `D` and their reaches (zero without it and
    /// below the clock's first clocked level; [`Tower::join_heading`]).
    heading_re: u64,
    heading_im: u64,
    descent: u64,
    /// The heading's descent into the stream `D↓` (zero without the motive; [`Tower::join_motive`]),
    /// its reach the fourth.
    fine_descent: u64,
    heading_reach: [u64; 4],
}

/// The law's words (`TowerLaw`).
#[repr(C)]
#[derive(Clone, Copy, Default, Debug)]
struct LawWords {
    alphabet: u32,
    width: u32,
    modes: u32,
    contacts: u32,
    levels: u32,
    cells: u32,
    streams: u32,
    face_digits: u32,
    move_digits: u32,
    families: u32,
    forms: u32,
    /// The contact law: 0 rectifying, 1 the pair contact, 2 its foil.
    contact: u32,
    encoding: u64,
    readout: u64,
    readout_bias: u64,
    readout_reach: u64,
    ln2_square: i64,
    pair_readout: u64,
    pair_lift: u64,
    pair_reach: [u64; 2],
    ring_level: u32,
    ring_mode: u32,
    ring_ranks: u32,
    ring_harmonics: u32,
    ring_readout: u64,
    ring_factors: u64,
    ring_reach: u64,
    half_turn: i64,
    turned: u32,
    turn_spread: u32,
    ladder: [[i64; 2]; LADDER],
    /// The pumped modes (`pumped = 0` when not), the rotor's moving modes a level (`moving = 0`
    /// without a rotor) and `ln 2` on `2^(−30)`.
    pumped: u32,
    moving: u32,
    ln2: i64,
    /// The card address of each level's words (`[L]`, the frame's `levels`), so the law's
    /// parameter words do not grow with the tower's levels.
    level: u64,
    /// The news clock (`news = 0` without one): its first clocked level (the levels below it tick at
    /// every arrival; each clocked level's section is in its words) and the clock's period
    /// ([`NewsClock`]).
    news: u32,
    news_first: u32,
    period: u64,
    /// The strands (`strand_rings = 0` without them): their level, their rings, the places of
    /// `W_sa` and `W_sb` and their reaches ([`holonics::hnn::tower::realization::ResidentStrands`]).
    strand_level: u32,
    strand_rings: u32,
    strand_contact: u64,
    strand_pair: u64,
    strand_reach: [u64; 2],
    /// Participation (`participation = 0` without it): its heads, its section, the pairing's
    /// scale and a held move's met dissipation ([`holonics::hnn::tower::participation`]).
    participation: u32,
    pa_heads: u32,
    pa_section: u32,
    pa_beta: u32,
    pa_held_log: i64,
    /// The mutual contact (`mutual = 0` without it) and its face's shift `b`: the readout's place
    /// holds its geometry `J` (`W × W`) ([`Tower::join_mutual_contact`]).
    mutual: u32,
    mutual_shift: u32,
    /// The passage (`passage = 0` without it): the contacts of every level from the news clock's
    /// first clocked level read the passing current through `W₁ˣ` ([`Tower::join_passage`]).
    passage: u32,
    /// The packets (`packets = 0` without them; else the clocked levels `L − F` that carry one):
    /// a clocked level's push, gate and turn read its packet's ratio at its ticks
    /// ([`Tower::join_packets`]).
    packets: u32,
    /// One when the reverse keeps each contact's covector for the paired contacts' split read
    /// (`tower_split_read`, [`holonics::hnn::tower::split`]), else zero; and the words' padding.
    split: u32,
    split_pad: u32,
    /// The heading (`heading = 0` without it; else the clocked levels `L − F` that carry one) and
    /// the closure's shift `s` ([`Tower::join_heading`]).
    heading: u32,
    heading_shift: u32,
    /// The clocked levels' credit (`credit = 0` without it; else the credited levels `L − F`) and
    /// whether each credited level below the top carries its packet's moments
    /// ([`holonics::hnn::tower::LevelCredit`]).
    credit: u32,
    credit_packet: u32,
    /// Whether this forward reads the heading's closure (the opening read, or a reread under the
    /// declared reading) and whether it advances the credit (the read a carry keeps).
    closure: u32,
    credit_advance: u32,
    /// The first credited level ([`Tower::rest_with_credit_from`]).
    credit_from: u32,
    /// The motive (`motive = 0` without it, [`Tower::join_motive`]) and the term of its series this
    /// reverse reads (0 the face's comparison; a later term's sums are added to the earlier
    /// terms'), and the words' padding.
    motive: u32,
    term: u32,
    term_pad: u32,
}

/// The section's buffers as the kernels address them (`TowerFrame`).
#[repr(C)]
#[derive(Clone, Copy, Default)]
struct FrameWords {
    theta: u64,
    theta_t: u64,
    families: u64,
    gates: u64,
    roots: u64,
    classes: u64,
    targets: u64,
    opening: u64,
    ends: u64,
    faces: u64,
    swell: u64,
    status: u64,
    input: u64,
    push: u64,
    state: u64,
    face: u64,
    read: u64,
    scale: u64,
    drive: u64,
    conduct: u64,
    moves: u64,
    top: u64,
    masses: u64,
    totals: u64,
    r_input: u64,
    r_face_re: u64,
    r_face_im: u64,
    r_read: u64,
    r_conduct: u64,
    r_top: u64,
    dz: u64,
    dx: u64,
    dy: u64,
    da: u64,
    dread: u64,
    readcov: u64,
    gre: u64,
    gim: u64,
    dq: u64,
    r_dz: u64,
    r_dy: u64,
    r_da: u64,
    r_dread: u64,
    r_gre: u64,
    r_gim: u64,
    r_dq: u64,
    moves_g: u64,
    gradient: u64,
    pair_values: u64,
    previous: u64,
    pair: u64,
    r_pair: u64,
    r_dx: u64,
    ring_opening: u64,
    ring_shifts: u64,
    ring_restarts: u64,
    ring_index: u64,
    ring_table: u64,
    ring_open: u64,
    hands_open: u64,
    ring_ends: u64,
    hands_ends: u64,
    ring_after: u64,
    ring_factor: u64,
    ring_move: u64,
    ring_hand: u64,
    ring_rho: u64,
    ring_scale: u64,
    top_hat: u64,
    top_scale: u64,
    ring_pair: u64,
    r_ring_pair: u64,
    ring_cov: u64,
    ring_dmove: u64,
    ring_g: u64,
    units: u64,
    ds: u64,
    r_ds: u64,
    news_open: u64,
    news_ends: u64,
    ticks: u64,
    pumps: u64,
    dk: u64,
    dp: u64,
    r_dk: u64,
    r_dp: u64,
    rotor: u64,
    second: u64,
    db: u64,
    r_db: u64,
    da_bias: u64,
    db_bias: u64,
    strands: u64,
    strand_open: u64,
    strand_ends: u64,
    strand_faces: u64,
    r_strand: u64,
    pa_heads: u64,
    pa_probe: u64,
    pa_key: u64,
    pa_value: u64,
    pa_frame: u64,
    pa_diss: u64,
    pa_current: u64,
    pa_read: u64,
    pa_scale: u64,
    pa_run: u64,
    pa_met: u64,
    pa_z: u64,
    pa_e: u64,
    pa_dra: u64,
    pa_gy: u64,
    pa_gq: u64,
    pa_gk: u64,
    pa_gw: u64,
    pa_gchart: u64,
    pa_gfric: u64,
    pa_gmet: u64,
    pa_tturn: u64,
    pa_tlog: u64,
    r_pa_read: u64,
    r_pa_yre: u64,
    r_pa_yim: u64,
    r_pa_dra: u64,
    r_pa_g: u64,
    pa_open: u64,
    pa_open_key: u64,
    pa_open_value: u64,
    pa_open_diss: u64,
    pa_hold: u64,
    pa_sect: u64,
    pa_member: u64,
    pa_mark: u64,
    contact_y: u64,
    contact_gy: u64,
    r_contact_gy: u64,
    pk_open: u64,
    pk_ends: u64,
    pk_state: u64,
    pk_read: u64,
    pk_scale: u64,
    pk_face: u64,
    pk_dx: u64,
    pk_dread: u64,
    pk_cov: u64,
    r_pk_read: u64,
    r_pk_face_re: u64,
    r_pk_face_im: u64,
    r_pk_dread: u64,
    split_dv: u64,
    split_dir: u64,
    split_out: u64,
    tr_open: u64,
    tr_ends: u64,
    hd_read: u64,
    tr_read: u64,
    hd_list: u64,
    hd_count: u64,
    hd_close: u64,
    hd_g: u64,
    ah_read: u64,
    ah_scale: u64,
    ah_face: u64,
    ah_dread: u64,
    ah_top: u64,
    r_ah_read: u64,
    r_ah_face_re: u64,
    r_ah_face_im: u64,
    r_ah_dread: u64,
    r_ah_top: u64,
    cr_open: u64,
    cr_next: u64,
    cr_turn: u64,
    cr_push: u64,
    cr_gate: u64,
    cr_pgate: u64,
    cr_x: u64,
    cr_rest: u64,
    cr_cov: u64,
    cr_tick: u64,
    mo_read: u64,
    mo_scale: u64,
    mo_face: u64,
    mo_dr0: u64,
    mo_open: u64,
    mo_flag: u64,
    r_mo_read: u64,
    r_mo_face_re: u64,
    r_mo_face_im: u64,
    r_mo_dr0: u64,
}

/// One family's outer sum (`TowerOuter`).
#[repr(C)]
#[derive(Clone, Copy, Debug)]
struct OuterWords {
    y: u64,
    y_stride: u64,
    x: u64,
    x_stride: u64,
    y_reach: u64,
    x_reach: u64,
    reach_stride: u64,
    rows: u32,
    cols: u32,
    streams: u32,
    cells: u32,
    negate: i32,
    bias: u32,
    out: u64,
    bias_out: u64,
    status: u64,
    groups: u32,
    /// One when the family's sum is added to its covector's place (a packet's read on its fine
    /// level's read), zero when it writes it.
    accumulate: u32,
    partial: u64,
}

/// The shape a frame's buffers are sized for.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Shape {
    alphabet: usize,
    width: usize,
    modes: usize,
    contacts: usize,
    levels: usize,
    len: usize,
    streams: usize,
    cells: usize,
    /// The pair face's forms (zero without one).
    forms: usize,
    /// The ring face's ranks, the harmonics its readout reads, and its founded pair moves (each
    /// zero without one).
    ranks: usize,
    harmonics: usize,
    ring_moves: usize,
    /// One when the modes are turned, else zero.
    turned: usize,
    /// One when the levels tick on a news clock, else zero.
    news: usize,
    /// One when the modes are pumped, else zero.
    pumped: usize,
    /// The rotor's moving modes a level (zero without a rotor).
    moving: usize,
    /// One when the contacts carry a second drive (the pair contact or its foil), else zero.
    paired: usize,
    /// One under the pair contact's foil, whose biases' covectors are summed on their own.
    foil: usize,
    /// The strands' rings and their resident table's words (each zero without strands).
    strand_rings: usize,
    strand_table: usize,
    /// Participation's heads and the section its sites span (each zero without it), and one when
    /// a stream carries its section open into the call (its sites' store is then resident).
    heads: usize,
    section: usize,
    carried: usize,
    /// One under the mutual contact, else zero.
    mutual: usize,
    /// The levels whose contacts hear the passing current (zero without the passage): each transposes
    /// `W₁ˣ` beside its other families.
    passage: usize,
    /// The clocked levels that hear a packet (zero without the packets).
    packets: usize,
    /// One under the pair contact, whose reverse can form the paired contacts' split read, else
    /// zero.
    split: usize,
    /// The clocked levels that carry a heading (zero without it).
    heading: usize,
    /// The credited levels (zero when the streams carry no credit), and those among them whose
    /// moves carry a packet.
    credit: usize,
    credit_packets: usize,
    /// One when the fine levels move under the heading ([`Tower::join_motive`]), else zero.
    motive: usize,
}

impl Shape {
    /// The ring's face with its harmonics `2RH`, and the pair read `x̂ ⊗ ρ`, `(W + 1)·2RH`.
    fn ring_reads(&self) -> (usize, usize) {
        let k2 = 2 * self.ranks * self.harmonics;
        (k2, (self.width + 1) * k2)
    }

    /// One ring rank's factors in the material, `6N + 2W + 3`.
    fn rank_material(&self) -> usize {
        6 * self.modes + 2 * self.width + 3
    }
}

/// The section's resident buffers (`TowerFrame`'s owners).
struct Frame<'c> {
    shape: Shape,
    theta: CardBuffer<'c, i32>,
    theta_t: CardBuffer<'c, i32>,
    families: CardBuffer<'c, u64>,
    gates: CardBuffer<'c, i64>,
    roots: CardBuffer<'c, u64>,
    classes: CardBuffer<'c, u32>,
    targets: CardBuffer<'c, i32>,
    opening: CardBuffer<'c, i64>,
    ends: CardBuffer<'c, i64>,
    faces: CardBuffer<'c, u64>,
    /// Each level's words (`TowerLevel`, `[L]`), which the law's words address.
    levels: CardBuffer<'c, LevelWords>,
    swell: CardBuffer<'c, u64>,
    status: CardBuffer<'c, u32>,
    input: CardBuffer<'c, i32>,
    push: CardBuffer<'c, i64>,
    state: CardBuffer<'c, i64>,
    face: CardBuffer<'c, i64>,
    read: CardBuffer<'c, i32>,
    scale: CardBuffer<'c, i64>,
    drive: CardBuffer<'c, i32>,
    conduct: CardBuffer<'c, i32>,
    moves: CardBuffer<'c, i64>,
    top: CardBuffer<'c, i32>,
    masses: CardBuffer<'c, u64>,
    totals: CardBuffer<'c, u64>,
    reaches: CardBuffer<'c, u64>,
    dz: CardBuffer<'c, i64>,
    dx: CardBuffer<'c, i64>,
    dy: CardBuffer<'c, i64>,
    da: CardBuffer<'c, i64>,
    dread: CardBuffer<'c, i64>,
    readcov: CardBuffer<'c, i64>,
    gre: CardBuffer<'c, i64>,
    gim: CardBuffer<'c, i64>,
    dq: CardBuffer<'c, i64>,
    moves_g: CardBuffer<'c, i128>,
    gradient: CardBuffer<'c, i128>,
    /// The outer sums' group sums (`tower_outer_reduce`), sized for the widest family's groups.
    partial: CardBuffer<'c, i128>,
    /// The pair face's values `c(prev, cur)`, each stream's class before its first cell, and the
    /// face read at each cell (each empty without a pair face).
    pair_values: CardBuffer<'c, i32>,
    previous: CardBuffer<'c, u32>,
    pair: CardBuffer<'c, i32>,
    /// The ring face (`TowerFrame`'s ring words; each empty without one).
    ring_opening: CardBuffer<'c, i32>,
    ring_shifts: CardBuffer<'c, u32>,
    ring_restarts: CardBuffer<'c, i32>,
    ring_index: CardBuffer<'c, u32>,
    ring_table: CardBuffer<'c, i64>,
    ring_open: CardBuffer<'c, i128>,
    hands_open: CardBuffer<'c, u32>,
    ring_ends: CardBuffer<'c, i128>,
    hands_ends: CardBuffer<'c, u32>,
    ring_after: CardBuffer<'c, i128>,
    ring_factor: CardBuffer<'c, i128>,
    ring_move: CardBuffer<'c, i64>,
    ring_hand: CardBuffer<'c, u32>,
    ring_rho: CardBuffer<'c, i32>,
    ring_scale: CardBuffer<'c, i64>,
    top_hat: CardBuffer<'c, i32>,
    top_scale: CardBuffer<'c, i64>,
    ring_pair: CardBuffer<'c, i32>,
    ring_cov: CardBuffer<'c, i64>,
    ring_dmove: CardBuffer<'c, i128>,
    ring_g: CardBuffer<'c, i128>,
    /// The turned modes' unit at each cell, `u e^(iπ s_t)`, and the turn's covector `δs` (each
    /// empty when unturned).
    units: CardBuffer<'c, i64>,
    ds: CardBuffer<'c, i64>,
    /// The news clock's open face and phase for each stream before its first cell and after its
    /// last (whether it has one, the total's two words, the phase, then the masses), and each
    /// cell's ticks a level (each empty without a clock).
    news_open: CardBuffer<'c, u64>,
    news_ends: CardBuffer<'c, u64>,
    ticks: CardBuffer<'c, u32>,
    /// The pumped modes' pump at each cell (opening, depth, axis, `β`) and the depth's and axis's
    /// covectors `δκ`, `δp` (each empty when unpumped).
    pumps: CardBuffer<'c, i64>,
    dk: CardBuffer<'c, i64>,
    dp: CardBuffer<'c, i64>,
    /// The rotor's keys a level, class and moving mode (`ResidentRotor`: the source mode, the mode
    /// whose covector returns here, the turn's face; empty without a rotor).
    rotor: CardBuffer<'c, i64>,
    /// The pair contact's second drive `b` at each cell and its covector `δb` (empty under
    /// rectifying contacts), and the foil's bias covectors `δb_a`, `δb_b` (empty but under it).
    second: CardBuffer<'c, i32>,
    db: CardBuffer<'c, i64>,
    da_bias: CardBuffer<'c, i64>,
    db_bias: CardBuffer<'c, i64>,
    /// The strands' resident table, each stream's residues and orientation before its first cell
    /// and after its last, and the faces their level reads at each cell (each empty without them).
    strands: CardBuffer<'c, i32>,
    strand_open: CardBuffer<'c, u32>,
    strand_ends: CardBuffer<'c, u32>,
    strand_faces: CardBuffer<'c, i32>,
    /// Participation's buffers (`TowerFrame`'s participation words; each empty without it).
    pa_heads: CardBuffer<'c, u32>,
    pa_probe: CardBuffer<'c, i64>,
    pa_key: CardBuffer<'c, i64>,
    pa_value: CardBuffer<'c, i64>,
    pa_frame: CardBuffer<'c, i64>,
    pa_diss: CardBuffer<'c, i64>,
    pa_current: CardBuffer<'c, i64>,
    pa_read: CardBuffer<'c, i32>,
    pa_scale: CardBuffer<'c, i64>,
    pa_run: CardBuffer<'c, i64>,
    pa_met: CardBuffer<'c, i64>,
    pa_z: CardBuffer<'c, i64>,
    pa_e: CardBuffer<'c, u64>,
    pa_dra: CardBuffer<'c, i64>,
    pa_gy: CardBuffer<'c, i64>,
    pa_gq: CardBuffer<'c, i128>,
    pa_gk: CardBuffer<'c, i128>,
    pa_gw: CardBuffer<'c, i128>,
    pa_gchart: CardBuffer<'c, i64>,
    pa_gfric: CardBuffer<'c, i128>,
    /// The transport: each cell's covector of its heads' mean met dissipation (`[S][T][H]`), and
    /// each cell's later sums, the covectors of its unit move's turn and of its `log₂ ρ`
    /// (`[S][T][N]` each, on `2^(−48)`), which the modes' scan reads.
    pa_gmet: CardBuffer<'c, i128>,
    pa_tturn: CardBuffer<'c, i128>,
    pa_tlog: CardBuffer<'c, i128>,
    /// The sites each stream carries open into the call at each level (`[S][L]`), at their places
    /// in the section.
    pa_open: CardBuffer<'c, u32>,
    pa_open_key: CardBuffer<'c, i64>,
    pa_open_value: CardBuffer<'c, i64>,
    pa_open_diss: CardBuffer<'c, i64>,
    /// Each level's held current (`[S][L][2N]`), uploaded at the opening and carried through the
    /// call; each level's open section at the call's end, its carried sites still read and the
    /// sites admitted since (`[S][L][2]`), and those sites' cells (`[S][L][section]`); and the
    /// reverse's mark of each cell at the level it returns (`[S][T]`).
    pa_hold: CardBuffer<'c, i64>,
    pa_sect: CardBuffer<'c, u32>,
    pa_member: CardBuffer<'c, u32>,
    pa_mark: CardBuffer<'c, u32>,
    /// The mutual contact's produced face `y = J x` and its covector `G_y` at each cell (each
    /// empty without it).
    contact_y: CardBuffer<'c, i64>,
    contact_gy: CardBuffer<'c, i64>,
    /// The packets (each empty without them; `PK = L − F`, the levels that hear one): each
    /// stream's open packets from the first clocked level up (`[S][PK][N][2]`) and its closing
    /// ones; each cell's packet as its level finds it (`[S][T][PK][N][2]`), its ratio read and
    /// scale at a tick (`[S][T][PK][W]`, `[S][T][PK]`), its face (re block, im block,
    /// `[S][T][PK][2N]`); the reverse's covector of the ratio read, its adjoint (`[S][T][PK][W]`
    /// each) and the packet's covector at a tick (`[S][T][PK][2N]`).
    pk_open: CardBuffer<'c, i64>,
    pk_ends: CardBuffer<'c, i64>,
    pk_state: CardBuffer<'c, i64>,
    pk_read: CardBuffer<'c, i32>,
    pk_scale: CardBuffer<'c, i64>,
    pk_face: CardBuffer<'c, i64>,
    pk_dx: CardBuffer<'c, i64>,
    pk_dread: CardBuffer<'c, i64>,
    pk_cov: CardBuffer<'c, i64>,
    /// The split read (each empty without the pair contact): each contact's covector `δv`
    /// (`[S][T][L][F]`), each pair's direction (`[L][F/2][W]`, zero where the pair is founded) and
    /// each pair's read, its score, squares and turned sum (`[L][F/2][2 + W]`).
    split_dv: CardBuffer<'c, i64>,
    split_dir: CardBuffer<'c, i32>,
    split_out: CardBuffer<'c, i128>,
    /// The heading (each empty without it; `HD = L − F`, the levels that carry one): each
    /// stream's open trace before its first cell and after its last (`[S][HD][W]`); each cell's
    /// heading read before its arrival, which the closure reads (`[S][T][HD][W]`); each trace's
    /// ratio read at a tick (`[S][T][HD][W]`); each stream's ticks a level in the section, their
    /// count and each tick's closure (`[S][HD][T]`, `[S][HD]`, `[S][HD][T][4]`: `e_jj`, the
    /// total's two words, `z_max`); and the closure's scratch (`[S][T]`).
    tr_open: CardBuffer<'c, i64>,
    tr_ends: CardBuffer<'c, i64>,
    hd_read: CardBuffer<'c, i32>,
    tr_read: CardBuffer<'c, i32>,
    hd_list: CardBuffer<'c, u32>,
    hd_count: CardBuffer<'c, u32>,
    hd_close: CardBuffer<'c, u64>,
    hd_g: CardBuffer<'c, i64>,
    /// The heading after each cell, which the face reads through the descent (each empty without
    /// the heading): its ratio read and scale (`[S][T][HD][W]`, `[S][T][HD]`) and the face it read
    /// (`[S][T][HD][2N]`); the reverse's covector of its raw read (`[S][T][HD][W]`) and the top's
    /// covector it was read against (`[S][T][W]`).
    ah_read: CardBuffer<'c, i32>,
    ah_scale: CardBuffer<'c, i64>,
    ah_face: CardBuffer<'c, i64>,
    ah_dread: CardBuffer<'c, i64>,
    ah_top: CardBuffer<'c, i64>,
    /// The clocked levels' credit's scratch (each empty without it; `CL` the credited levels): each
    /// cell's turn, push, gate and packet-gate coefficients (`[S][T][CL][N][2]` each), the input the
    /// push and gate read (`[S][T][CL][W]`), whether the carried packet rested (`[S][T][CL]`), and the
    /// reverse's opening covectors (`[S][CL][2][N][2]`).
    cr_turn: CardBuffer<'c, i64>,
    cr_push: CardBuffer<'c, i64>,
    cr_gate: CardBuffer<'c, i64>,
    cr_pgate: CardBuffer<'c, i64>,
    cr_x: CardBuffer<'c, i32>,
    cr_rest: CardBuffer<'c, u32>,
    cr_cov: CardBuffer<'c, i64>,
    /// Each cell's ticks at each credited level for the read that advances the credit
    /// (`[S][T][CL]`, `tower_credit_moments`).
    cr_tick: CardBuffer<'c, u32>,
    /// The motive (each empty without it, [`Tower::join_motive`]): each clocked level's heading
    /// before each cell, its ratio and scale; the carried modes' face at the opening; a later term's
    /// covector of the first cell's heading's raw read and of the carried modes it reaches; and
    /// whether a term's source is not zero.
    mo_read: CardBuffer<'c, i32>,
    mo_scale: CardBuffer<'c, i64>,
    mo_face: CardBuffer<'c, i64>,
    mo_dr0: CardBuffer<'c, i64>,
    mo_open: CardBuffer<'c, i64>,
    mo_flag: CardBuffer<'c, u32>,
    /// The reaches' slices of `reaches`, in `FrameWords`' order: input, face re, face im, read,
    /// conduct (each `Q·L`), top (`Q`), dz (`Q`), dy, da, dread, gre, gim, dq (each `Q·L`), then
    /// the pair face read, the bottom covector `δx⁰` and the ring's pair read (each `Q`), then the
    /// turn's covector `δs`, then the pump's depth and axis covectors `δκ`, `δp`, then the second
    /// drive's covector `δb`, then the strands' faces at their level (each `Q·L`), then
    /// participation's ratio read, current (re, im) and `∂r̂ᵃ` (each `Q·L`) and its six chart
    /// covectors (`6·Q·L`), then the mutual contact's `G_y` (`Q`), then the packets' ratio read,
    /// face (re, im) and the read's adjoint (each `Q·L`), then the heading's after each cell: the
    /// ratio, the face (re, im) and the read's adjoint (each `Q·HD`, `[HD][S][T]`) and the top's
    /// covector (`Q`).
    reach_offsets: [usize; 40],
}

/// [agent-inferred, October 31] **The streams' credit resident on the card** (record
/// `2026-10-30_THE_COARSE_LEVEL_HEADS_FOR_THE_TRACE_OF_WHAT_COMES_NEXT…`, §22): each stream's credit at
/// the next opening (`open`, its words `Tower::credit_words`) and the credit each kept read advanced it
/// to (`next`, one a slot), outside the frame, so a frame sized for another read keeps it. The host's
/// states hold a mark of it (`LevelCredit::resident_mark`), which [`TowerCard::fetch_credit`] returns.
struct ResidentCredit<'c> {
    streams: usize,
    /// The first credited level and one stream's words.
    from: usize,
    extent: usize,
    generation: u64,
    open: CardBuffer<'c, i64>,
    /// The advance of the read a carry keeps (one: an opening read advances only when its carry
    /// asks, after any reread, `TowerCard::carry`).
    next: CardBuffer<'c, i64>,
}

/// [definition] **The card's realization of the section's pass** (module header).
pub struct TowerCard<'c> {
    card: &'c Card,
    module: Module,
    frame: Option<Frame<'c>>,
    /// The law of the material the frame holds from the last opening read, and its levels' words
    /// (resident in the frame's `levels`, read here by the outer sums' places).
    opened: Option<(LawWords, Vec<LevelWords>)>,
    /// Whether the frame's material is still the opening read's (a reread uploads its candidate).
    opened_current: bool,
    /// Whether the frame holds an opening read's ticks under a news clock, which a reread on them
    /// ([`Slot::OpeningTicks`]) reads; a frame sized again holds none.
    ticks_kept: bool,
    ends: [Option<Vec<TowerState>>; 2],
    /// The streams' credit, when the learner's streams carry one.
    credit: Option<ResidentCredit<'c>>,
    /// The generation the next resident credit takes (a mark of an older one is refused).
    generations: u64,
    /// [agent-inferred, October 31] The read whose credit advance waits for its carry (its slot and
    /// its law's words): `tower_credit` sums the material moments only for the read a carry keeps,
    /// and an opening read advances none unless a carry asks for it (record §23).
    credit_pending: Option<(usize, LawWords)>,
    /// The opening read's classes and targets, which a carry of the opening reads again to advance
    /// its credit; and whether the next opening read advances it.
    opened_reads: Option<(Vec<Vec<usize>>, Vec<Vec<Option<usize>>>)>,
    force_advance: bool,
    /// Whether a reread reads the heading's closure ([`PassRealization::reread_closures`]).
    reread_closures: bool,
    times: TowerCardTimes,
    /// The reverses and terms [`PassRealization::series_read`] last read.
    series_seen: (u64, u64),
    /// When set, each launch is waited on and timed by its entry (a measurement aid: it
    /// serializes the card's stream).
    profile: Option<std::cell::RefCell<std::collections::BTreeMap<&'static str, (u64, u128)>>>,
}

/// The card's own receipt: calls and their wall time, transfers included.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct TowerCardTimes {
    pub forwards: u64,
    pub forward_ns: u128,
    pub reverses: u64,
    pub reverse_ns: u128,
    /// The motive's series ([`Tower::join_motive`]): the terms the reverses read in all (one a
    /// reverse without it).
    pub terms: u64,
}

/// `tower_credit`'s shared bytes (record §28): the whole section's turns, and the staged chunk's
/// rows (six words a cell of a warp's mode) and inputs (`CREDIT_CELLS` cells).
fn credit_shared(words: &LawWords) -> u32 {
    const CREDIT_CELLS: u32 = 32;
    32 * words.modes + 48 * CREDIT_CELLS * (THREADS / 32) + 4 * CREDIT_CELLS * words.width
}

fn slot_index(slot: Slot) -> usize {
    match slot {
        Slot::Opened => 0,
        Slot::Reread | Slot::OpeningTicks => 1,
    }
}

/// `octets` rounded to the kernels' 16-octet carve.
fn carve(octets: usize) -> usize {
    octets.div_ceil(16) * 16
}

impl<'c> TowerCard<'c> {
    /// Load the tower's image on the card.
    pub fn open(card: &'c Card) -> std::result::Result<Self, DeviceError> {
        card.current()?;
        let module = Module::load_ptx(IMAGE)?;
        Ok(Self { card, module, frame: None, opened: None, opened_current: false, ticks_kept: false, ends: [None, None], credit: None, generations: 0, credit_pending: None, opened_reads: None, force_advance: false, reread_closures: false, times: TowerCardTimes::default(), series_seen: (0, 0), profile: None })
    }

    /// Time every launch by its entry from here on (each launch waited on before and after).
    pub fn profile(&mut self) {
        self.profile = Some(Default::default());
    }

    /// Each entry's launches and their summed wall time, when profiled.
    pub fn profiled(&self) -> Vec<(&'static str, u64, u128)> {
        self.profile.as_ref().map_or_else(Vec::new, |p| p.borrow().iter().map(|(&e, &(n, ns))| (e, n, ns)).collect())
    }

    pub fn times(&self) -> TowerCardTimes {
        self.times
    }

    /// The declaration the card carries (module header), or the reason it is refused.
    pub fn admits(law: &ResidentLaw) -> Result<()> {
        let d = &law.declaration;
        let refuse = |why: &'static str| Err(TowerError::Refused(why));
        if !d.gated {
            return refuse("the card carries the gated tower");
        }
        if law.heading.is_some_and(|shift| !law.packets || law.mutual.is_some() || law.participation.is_some() || law.rotor.is_some() || law.ring.is_some() || law.strands.is_some() || shift > 32) {
            return refuse("the card closes a heading at the packets' ticks, never beside a mutual contact, participation, a rotor, a ring face or strands");
        }
        if law.motive && (law.heading.is_none() || d.contact == ContactLaw::Pair) {
            return refuse("the card moves the fine levels under a heading, never beside the pair contact's split read");
        }
        if law.mutual.is_some() && (law.rotor.is_some() || law.news.is_some() || law.pair.is_some() || law.ring.is_some() || law.strands.is_some() || law.participation.is_some()) {
            return refuse("the card carries a mutual contact alone at the comparison, never beside a rotor, a news clock, a pair or ring face, strands or participation");
        }
        if law.participation.as_ref().is_some_and(|p| law.rotor.is_some() || law.ring.is_some() || p.heads.len() > u32::MAX as usize) {
            return refuse("the card carries participation on gated modes, never beside a rotor or a ring face");
        }
        if d.pumped && (!d.turned || law.news.is_some()) {
            return refuse("the card pumps a turned mode, never beside a news clock");
        }
        if d.turned && (law.ladder.len() != LADDER || law.half_turn <= 0) {
            return refuse("the card turns a mode through the ladder's seventeen dyadic turns and the half turn");
        }
        if let Some(ring) = &law.ring {
            let r = ring.ranks;
            if ring.level >= d.levels || ring.mode >= d.modes || r == 0 || ring.harmonics == 0 || ring.shifts.len() != r || ring.moves.len() != r || ring.restarts.len() != r || ring.opening.len() != d.alphabet * d.width {
                return refuse("the card reads a ring face of one or more ranks on a level and mode of the tower, each rank with its shifts, moves and restart");
            }
            if ring.shifts.iter().any(|&([ra, rb, rg], push, read)| [ra, rb, rg, push, read].iter().any(|&b| b >= 127)) {
                return refuse("the card releases a ring's values by fewer than 127 bits");
            }
            if ring.moves.iter().flatten().any(|&(prev, cur, _)| prev > d.alphabet || cur >= d.alphabet) || ring.restarts.iter().flatten().any(|&c| c >= d.alphabet) {
                return refuse("the card reads a ring's pair moves and restarts over the alphabet");
            }
            let reads = (d.width + 1).checked_mul(2 * r).and_then(|v| v.checked_mul(ring.harmonics));
            let factors = r.checked_mul(6 * d.modes + 2 * d.width + 3);
            let moves: usize = ring.moves.iter().map(Vec::len).sum();
            if reads.is_none_or(|v| v > u32::MAX as usize / 8) || factors.is_none_or(|v| v > u32::MAX as usize / 8) || moves > u32::MAX as usize / 8 {
                return refuse("the card's ring extents fit its 32-bit words");
            }
        }
        if let Some(pair) = &law.pair {
            if pair.forms == 0 || pair.forms > u32::MAX as usize / 8 || pair.values.len() != (d.alphabet + 1) * d.alphabet * pair.forms {
                return refuse("the card reads a pair face of one value a form at every pair");
            }
        }
        if let Some(strands) = &law.strands {
            if strands.level >= d.levels || strands.rings == 0 || strands.rings > u32::MAX as usize / 8 || strands.table.len() < 8 + 3 * strands.rings {
                return refuse("the card hears strands of one or more rings on a level of the tower, through their resident table");
            }
        }
        if let Some(rotor) = &law.rotor {
            if rotor.moving > d.modes || d.modes > THREADS as usize || rotor.keys.len() != d.levels * d.alphabet * rotor.moving * 4 {
                return refuse("the card steps a rotor's moving modes with a key for each level, class and moving mode, its modes' scan one thread a mode in one block");
            }
        }
        if law.packets && law.news.is_none_or(|c| c.first() == 0 || c.first() >= d.levels) {
            return refuse("the card hears packets under a news clock that holds a level above its first");
        }
        if d.levels == 0 || d.levels > u32::MAX as usize {
            return refuse("the card carries one or more levels, counted in a 32-bit word");
        }

        if let Some(clock) = &law.news {
            if law.ring.is_some() {
                return refuse("the card carries no ring beside a news clock");
            }
            clock.period(d.levels)?;
            for l in clock.first()..d.levels {
                clock.section(l)?;
            }
        }
        if law.face_roots.iter().chain(&law.move_roots).any(|&r| r >= 1u128 << 63) {
            return refuse("the exponential's roots lie below 2^63");
        }
        let words = [d.alphabet, d.width, d.modes, d.contacts];
        if words.iter().any(|&w| w == 0 || w > u32::MAX as usize / 8) {
            return refuse("the card's extents fit its 32-bit words");
        }
        Ok(())
    }

    /// The law's words and each level's words (the frame's `levels`, which `LawWords::level`
    /// addresses once they are resident).
    fn law_words(law: &ResidentLaw, streams: usize, cells: usize) -> (LawWords, Vec<LevelWords>) {
        let d = &law.declaration;
        let mut words = LawWords {
            alphabet: d.alphabet as u32,
            width: d.width as u32,
            modes: d.modes as u32,
            contacts: d.contacts as u32,
            levels: d.levels as u32,
            cells: cells as u32,
            streams: streams as u32,
            face_digits: law.face_roots.len() as u32,
            move_digits: law.move_roots.len() as u32,
            families: (Self::families(law).len() / 3) as u32,
            contact: match d.contact {
                ContactLaw::Rectifying => 0,
                ContactLaw::Pair => 1,
                ContactLaw::PairLinear => 2,
            },
            encoding: law.encoding as u64,
            readout: law.readout as u64,
            readout_bias: law.readout_bias as u64,
            readout_reach: law.readout_reach,
            ln2_square: law.ln2_square as i64,
            ..LawWords::default()
        };
        if let Some(rotor) = &law.rotor {
            words.moving = rotor.moving as u32;
        }
        if d.pumped {
            words.pumped = 1;
            words.ln2 = law.ln2 as i64;
        }
        if d.turned {
            words.turned = 1;
            words.half_turn = law.half_turn;
            words.turn_spread = usize::BITS - d.width.saturating_sub(1).leading_zeros();
            for (slot, &(re, im)) in words.ladder.iter_mut().zip(&law.ladder) {
                *slot = [re, im];
            }
        }
        if let Some(pair) = &law.pair {
            words.forms = pair.forms as u32;
            words.pair_readout = pair.readout as u64;
            words.pair_lift = pair.lift as u64;
            words.pair_reach = pair.reaches;
        }
        if let Some(ring) = &law.ring {
            words.ring_level = ring.level as u32;
            words.ring_mode = ring.mode as u32;
            words.ring_ranks = ring.ranks as u32;
            words.ring_harmonics = ring.harmonics as u32;
            words.ring_readout = ring.readout as u64;
            words.ring_factors = ring.factors as u64;
            words.ring_reach = ring.reach;
        }
        if let Some(strands) = &law.strands {
            words.strand_level = strands.level as u32;
            words.strand_rings = strands.rings as u32;
            words.strand_contact = strands.contact as u64;
            words.strand_pair = strands.pair as u64;
            words.strand_reach = strands.reaches;
        }
        if let Some(clock) = &law.news {
            words.news = 1;
            words.news_first = clock.first;
            words.period = clock.period(d.levels).expect("admitted");
        }
        if let Some(p) = &law.participation {
            words.participation = 1;
            words.pa_heads = p.heads.len() as u32;
            words.pa_section = p.section as u32;
            words.pa_beta = p.beta_shift;
            words.pa_held_log = law.held_log;
            words.ln2 = law.ln2 as i64;
        }
        words.passage = u32::from(law.passage);
        words.packets = if law.packets { law.news.map_or(0, |c| (d.levels - c.first()) as u32) } else { 0 };
        if let (Some(shift), Some(clock)) = (law.heading, &law.news) {
            words.heading = (d.levels - clock.first()) as u32;
            words.heading_shift = shift;
            words.motive = u32::from(law.motive);
        }
        if let Some(b) = law.mutual {
            words.mutual = 1;
            words.mutual_shift = b;
        }
        let levels = law
            .levels
            .iter()
            .enumerate()
            .map(|(l, lv)| LevelWords {
                move_re: lv.move_re as u64,
                move_im: lv.move_im as u64,
                push_re: lv.push_re as u64,
                push_im: lv.push_im as u64,
                read_re: lv.read_re as u64,
                read_im: lv.read_im as u64,
                contact: lv.contact as u64,
                contact_bias: lv.contact_bias as u64,
                ret: lv.ret as u64,
                ret_bias: lv.ret_bias as u64,
                gate: lv.gate as u64,
                gate_bias: lv.gate_bias as u64,
                turn: lv.turn as u64,
                turn_bias: lv.turn_bias as u64,
                pump: lv.pump as u64,
                pump_bias: lv.pump_bias as u64,
                pump_axis: lv.pump_axis as u64,
                pump_axis_bias: lv.pump_axis_bias as u64,
                pair: lv.pair as u64,
                pair_bias: lv.pair_bias as u64,
                reach: lv.reaches,
                pa: lv.participation.map(|v| v as u64),
                pa_reach: lv.participation_reaches,
                passage: lv.passage as u64,
                passage_reach: lv.passage_reach,
                section: law.news.filter(|c| l >= c.first()).map_or(0, |c| c.section(l).expect("admitted")),
                heading_re: lv.heading_re as u64,
                heading_im: lv.heading_im as u64,
                descent: lv.descent as u64,
                fine_descent: lv.fine_descent as u64,
                heading_reach: lv.heading_reaches,
            })
            .collect();
        (words, levels)
    }

    /// The matrix families `(offset, rows, cols)` the forward reads transposed.
    fn families(law: &ResidentLaw) -> Vec<u64> {
        let d = &law.declaration;
        let (a, w, n, f) = (d.alphabet as u64, d.width as u64, d.modes as u64, d.contacts as u64);
        let mut out = vec![law.readout as u64, if law.mutual.is_some() { w } else { a }, w];
        let heard = if law.passage { law.news.map_or(law.levels.len(), |c| c.first()) } else { law.levels.len() };
        for (l, lv) in law.levels.iter().enumerate() {
            for (offset, rows, cols) in [(lv.push_re, n, w), (lv.push_im, n, w), (lv.gate, n, w), (lv.read_re, w, n), (lv.read_im, w, n), (lv.contact, f, w), (lv.ret, w, f)] {
                out.extend([offset as u64, rows, cols]);
            }
            if d.turned {
                out.extend([lv.turn as u64, n, w]);
            }
            if d.pumped {
                out.extend([lv.pump as u64, n, w, lv.pump_axis as u64, n, w]);
            }
            if d.contact != ContactLaw::Rectifying {
                out.extend([lv.pair as u64, f, w]);
            }
            if law.participation.is_some() {
                let p = &lv.participation;
                for (offset, rows, cols) in [(p[0], n, w), (p[1], n, w), (p[2], n, w), (p[3], n, w), (p[4], n, w), (p[5], n, w), (p[6], w, n), (p[7], w, n), (p[8], f, w)] {
                    out.extend([offset as u64, rows, cols]);
                }
            }
            if l >= heard {
                out.extend([lv.passage as u64, f, w]);
            }
            if law.heading.is_some() && law.news.is_some_and(|c| l >= c.first()) {
                out.extend([lv.heading_re as u64, w, n, lv.heading_im as u64, w, n]);
            }
        }
        if let Some(strands) = &law.strands {
            let c = 6 * strands.rings as u64;
            out.extend([strands.contact as u64, f, c]);
            if d.contact != ContactLaw::Rectifying {
                out.extend([strands.pair as u64, f, c]);
            }
        }
        out
    }

    fn frame(&mut self, shape: Shape) -> std::result::Result<(), DeviceError> {
        if self.frame.as_ref().is_some_and(|f| f.shape == shape) {
            return Ok(());
        }
        self.frame = None;
        self.ticks_kept = false;
        // A frame sized again holds no read's credit advance.
        self.credit_pending = None;
        let card = self.card;
        let Shape { alphabet: a, width: w, modes: n, contacts: f, levels: l, len, streams: s, cells: t, forms: k, ranks: r, ring_moves: m, turned, news, pumped, moving, paired, foil, strand_rings: sr, strand_table, .. } = shape;
        let stranded = usize::from(sr > 0);
        let (k2, kp) = shape.ring_reads();
        let ringed = usize::from(r > 0);
        let q = s * t;
        let ql = q * l;
        let (heads, sec, pa, carried) = (shape.heads, shape.section, usize::from(shape.heads > 0), shape.carried);
        let mutual = shape.mutual;
        let (pk, pkd) = (shape.packets, usize::from(shape.packets > 0));
        let (hd, hdd) = (shape.heading, usize::from(shape.heading > 0));
        let mo = shape.motive;
        let mut reach_offsets = [0usize; 40];
        let extents = [ql, ql, ql, ql, ql, q, q, ql, ql, ql, ql, ql, ql, q, q, q, ql * turned, ql * pumped, ql * pumped, ql * paired, ql * stranded, ql * pa, ql * pa, ql * pa, ql * pa, 6 * ql * pa, q * mutual, ql * pkd, ql * pkd, ql * pkd, ql * pkd, q * hd, q * hd, q * hd, q * hd, q * hdd, q * hd * mo, s * hd * mo, s * hd * mo, s * hd * mo];
        let mut at = 0;
        for (slot, extent) in reach_offsets.iter_mut().zip(extents) {
            *slot = at;
            at += extent;
        }
        self.frame = Some(Frame {
            shape,
            theta: card.alloc(len)?,
            theta_t: card.alloc(len)?,
            families: card.alloc(3 * (1 + (7 + turned + 2 * pumped + paired + 9 * pa) * l + shape.passage + 2 * hd + stranded * (1 + paired)))?,
            gates: card.alloc(l * n * 4)?,
            roots: card.alloc(64)?,
            classes: card.alloc(s * (t + 1))?,
            targets: card.alloc(q)?,
            opening: card.alloc(s * l * n * 2)?,
            ends: card.alloc(s * l * n * 2)?,
            faces: card.alloc(q * 3)?,
            levels: card.alloc(l)?,
            swell: card.alloc(l * 4)?,
            status: card.alloc(s)?,
            input: card.alloc(ql * w)?,
            push: card.alloc(ql * 2 * n)?,
            state: card.alloc(ql * 2 * n)?,
            face: card.alloc(ql * 2 * n)?,
            read: card.alloc(ql * w)?,
            scale: card.alloc(ql)?,
            drive: card.alloc(ql * f)?,
            conduct: card.alloc(ql * f)?,
            moves: card.alloc(ql * n * 6)?,
            top: card.alloc(q * w)?,
            masses: card.alloc(q * a)?,
            totals: card.alloc(q * 2)?,
            reaches: card.alloc(at)?,
            dz: card.alloc(q * a)?,
            dx: card.alloc(q * w)?,
            dy: card.alloc(ql * w)?,
            da: card.alloc(ql * f)?,
            dread: card.alloc(ql * w)?,
            readcov: card.alloc(ql * 2 * n)?,
            gre: card.alloc(ql * n)?,
            gim: card.alloc(ql * n)?,
            dq: card.alloc(ql * n)?,
            moves_g: card.alloc(s * l * n * 2)?,
            gradient: card.alloc(len)?,
            partial: card.alloc(Self::partial_extent(&shape, card.census().multiprocessors))?,
            pair_values: card.alloc((a + 1) * a * k)?,
            previous: card.alloc(s)?,
            pair: card.alloc(q * k)?,
            ring_opening: card.alloc(a * w * ringed)?,
            ring_shifts: card.alloc(5 * r)?,
            ring_restarts: card.alloc(r)?,
            ring_index: card.alloc((r + 1) * ringed)?,
            ring_table: card.alloc(6 * m)?,
            ring_open: card.alloc(s * r * 2)?,
            hands_open: card.alloc(s * r)?,
            ring_ends: card.alloc(s * r * 2)?,
            hands_ends: card.alloc(s * r)?,
            ring_after: card.alloc(q * r * 2)?,
            ring_factor: card.alloc(q * r * 5)?,
            ring_move: card.alloc(q * r * 4)?,
            ring_hand: card.alloc(q * r)?,
            ring_rho: card.alloc(q * k2)?,
            ring_scale: card.alloc(q * r)?,
            top_hat: card.alloc(q * w * ringed)?,
            top_scale: card.alloc(q * ringed)?,
            ring_pair: card.alloc(q * kp)?,
            ring_cov: card.alloc(q * 2 * r)?,
            ring_dmove: card.alloc(q * 4 * ringed)?,
            ring_g: card.alloc(s * r * shape.rank_material())?,
            units: card.alloc(ql * n * 2 * turned)?,
            ds: card.alloc(ql * n * turned)?,
            news_open: card.alloc(s * (a + 4) * news)?,
            news_ends: card.alloc(s * (a + 4) * news)?,
            ticks: card.alloc(ql * news)?,
            pumps: card.alloc(ql * n * 6 * pumped)?,
            dk: card.alloc(ql * n * pumped)?,
            dp: card.alloc(ql * n * pumped)?,
            rotor: card.alloc(l * a * moving * 4)?,
            second: card.alloc(ql * f * paired)?,
            db: card.alloc(ql * f * paired)?,
            da_bias: card.alloc(ql * f * foil)?,
            db_bias: card.alloc(ql * f * foil)?,
            strands: card.alloc(strand_table)?,
            strand_open: card.alloc(s * (3 * sr + 1) * stranded)?,
            strand_ends: card.alloc(s * (3 * sr + 1) * stranded)?,
            strand_faces: card.alloc(q * 6 * sr)?,
            pa_heads: card.alloc((heads + 1) * pa)?,
            pa_probe: card.alloc(ql * n * 2 * pa)?,
            pa_key: card.alloc(ql * n * 2 * pa)?,
            pa_value: card.alloc(ql * n * 2 * pa)?,
            pa_frame: card.alloc(ql * n * 2 * pa)?,
            pa_diss: card.alloc(ql * heads)?,
            pa_current: card.alloc(ql * 2 * n * pa)?,
            pa_read: card.alloc(ql * w * pa)?,
            pa_scale: card.alloc(ql * pa)?,
            pa_run: card.alloc(s * l * n * 2 * pa)?,
            pa_met: card.alloc(s * l * n * pa)?,
            pa_z: card.alloc(s * heads * t.max(sec) * pa)?,
            pa_e: card.alloc(s * heads * t.max(sec) * pa)?,
            pa_dra: card.alloc(ql * w * pa)?,
            pa_gy: card.alloc(ql * 2 * n * pa)?,
            pa_gq: card.alloc(q * n * 2 * pa)?,
            pa_gk: card.alloc(q * n * 2 * pa)?,
            pa_gw: card.alloc(q * n * 2 * pa)?,
            pa_gchart: card.alloc(ql * 6 * n * pa)?,
            pa_gfric: card.alloc(s * l * heads)?,
            pa_gmet: card.alloc(q * heads)?,
            pa_tturn: card.alloc(q * n * pa)?,
            pa_tlog: card.alloc(q * n * pa)?,
            pa_open: card.alloc(s * l * pa)?,
            pa_open_key: card.alloc(s * sec * l * n * 2 * carried)?,
            pa_open_value: card.alloc(s * sec * l * n * 2 * carried)?,
            pa_open_diss: card.alloc(s * sec * l * heads * carried)?,
            pa_hold: card.alloc(s * l * 2 * n * pa)?,
            pa_sect: card.alloc(s * l * 2 * pa)?,
            pa_member: card.alloc(s * l * sec * pa)?,
            pa_mark: card.alloc(q * pa)?,
            contact_y: card.alloc(q * w * mutual)?,
            contact_gy: card.alloc(q * w * mutual)?,
            pk_open: card.alloc(s * pk * n * 2)?,
            pk_ends: card.alloc(s * pk * n * 2)?,
            pk_state: card.alloc(q * pk * n * 2)?,
            pk_read: card.alloc(q * pk * w)?,
            pk_scale: card.alloc(q * pk)?,
            pk_face: card.alloc(q * pk * 2 * n)?,
            pk_dx: card.alloc(q * pk * w)?,
            pk_dread: card.alloc(q * pk * w)?,
            pk_cov: card.alloc(q * pk * 2 * n)?,
            // The split read's buffers are sized at the first split read (`TowerCard::reverse_split`):
            // a pair contact's tower that never reads one holds none.
            split_dv: card.alloc(0)?,
            split_dir: card.alloc(0)?,
            split_out: card.alloc(0)?,
            tr_open: card.alloc(s * hd * w)?,
            tr_ends: card.alloc(s * hd * w)?,
            hd_read: card.alloc(q * hd * w)?,
            tr_read: card.alloc(q * hd * w)?,
            hd_list: card.alloc(s * hd * t)?,
            hd_count: card.alloc(s * hd)?,
            hd_close: card.alloc(s * hd * t * 4)?,
            hd_g: card.alloc(q * hdd)?,
            ah_read: card.alloc(q * hd * w)?,
            ah_scale: card.alloc(q * hd)?,
            ah_face: card.alloc(q * hd * 2 * n)?,
            ah_dread: card.alloc(q * hd * w)?,
            ah_top: card.alloc(q * w * hdd)?,
            cr_turn: card.alloc(q * shape.credit * n * 2)?,
            cr_push: card.alloc(q * shape.credit * n * 2)?,
            cr_gate: card.alloc(q * shape.credit * n * 2)?,
            cr_pgate: card.alloc(q * shape.credit_packets * n * 2)?,
            cr_x: card.alloc(q * shape.credit * w)?,
            cr_rest: card.alloc(q * shape.credit)?,
            cr_cov: card.alloc(s * shape.credit * 2 * n * 2)?,
            cr_tick: card.alloc(q * shape.credit)?,
            mo_read: card.alloc(q * hd * w * mo)?,
            mo_scale: card.alloc(q * hd * mo)?,
            mo_face: card.alloc(s * hd * 2 * n * mo)?,
            mo_dr0: card.alloc(s * hd * w * mo)?,
            mo_open: card.alloc(s * hd * n * 2 * mo)?,
            mo_flag: card.alloc(mo)?,
            reach_offsets,
        });
        Ok(())
    }

    fn frame_words(frame: &Frame<'_>) -> FrameWords {
        let r = |i: usize| frame.reaches.device_ptr() + 8 * frame.reach_offsets[i] as u64;
        FrameWords {
            theta: frame.theta.device_ptr(),
            theta_t: frame.theta_t.device_ptr(),
            families: frame.families.device_ptr(),
            gates: frame.gates.device_ptr(),
            roots: frame.roots.device_ptr(),
            classes: frame.classes.device_ptr(),
            targets: frame.targets.device_ptr(),
            opening: frame.opening.device_ptr(),
            ends: frame.ends.device_ptr(),
            faces: frame.faces.device_ptr(),
            swell: frame.swell.device_ptr(),
            status: frame.status.device_ptr(),
            input: frame.input.device_ptr(),
            push: frame.push.device_ptr(),
            state: frame.state.device_ptr(),
            face: frame.face.device_ptr(),
            read: frame.read.device_ptr(),
            scale: frame.scale.device_ptr(),
            drive: frame.drive.device_ptr(),
            conduct: frame.conduct.device_ptr(),
            moves: frame.moves.device_ptr(),
            top: frame.top.device_ptr(),
            masses: frame.masses.device_ptr(),
            totals: frame.totals.device_ptr(),
            r_input: r(0),
            r_face_re: r(1),
            r_face_im: r(2),
            r_read: r(3),
            r_conduct: r(4),
            r_top: r(5),
            dz: frame.dz.device_ptr(),
            dx: frame.dx.device_ptr(),
            dy: frame.dy.device_ptr(),
            da: frame.da.device_ptr(),
            dread: frame.dread.device_ptr(),
            readcov: frame.readcov.device_ptr(),
            gre: frame.gre.device_ptr(),
            gim: frame.gim.device_ptr(),
            dq: frame.dq.device_ptr(),
            r_dz: r(6),
            r_dy: r(7),
            r_da: r(8),
            r_dread: r(9),
            r_gre: r(10),
            r_gim: r(11),
            r_dq: r(12),
            moves_g: frame.moves_g.device_ptr(),
            gradient: frame.gradient.device_ptr(),
            pair_values: frame.pair_values.device_ptr(),
            previous: frame.previous.device_ptr(),
            pair: frame.pair.device_ptr(),
            r_pair: r(13),
            r_dx: r(14),
            ring_opening: frame.ring_opening.device_ptr(),
            ring_shifts: frame.ring_shifts.device_ptr(),
            ring_restarts: frame.ring_restarts.device_ptr(),
            ring_index: frame.ring_index.device_ptr(),
            ring_table: frame.ring_table.device_ptr(),
            ring_open: frame.ring_open.device_ptr(),
            hands_open: frame.hands_open.device_ptr(),
            ring_ends: frame.ring_ends.device_ptr(),
            hands_ends: frame.hands_ends.device_ptr(),
            ring_after: frame.ring_after.device_ptr(),
            ring_factor: frame.ring_factor.device_ptr(),
            ring_move: frame.ring_move.device_ptr(),
            ring_hand: frame.ring_hand.device_ptr(),
            ring_rho: frame.ring_rho.device_ptr(),
            ring_scale: frame.ring_scale.device_ptr(),
            top_hat: frame.top_hat.device_ptr(),
            top_scale: frame.top_scale.device_ptr(),
            ring_pair: frame.ring_pair.device_ptr(),
            r_ring_pair: r(15),
            ring_cov: frame.ring_cov.device_ptr(),
            ring_dmove: frame.ring_dmove.device_ptr(),
            ring_g: frame.ring_g.device_ptr(),
            units: frame.units.device_ptr(),
            ds: frame.ds.device_ptr(),
            r_ds: r(16),
            news_open: frame.news_open.device_ptr(),
            news_ends: frame.news_ends.device_ptr(),
            ticks: frame.ticks.device_ptr(),
            pumps: frame.pumps.device_ptr(),
            dk: frame.dk.device_ptr(),
            dp: frame.dp.device_ptr(),
            r_dk: r(17),
            r_dp: r(18),
            rotor: frame.rotor.device_ptr(),
            second: frame.second.device_ptr(),
            db: frame.db.device_ptr(),
            r_db: r(19),
            da_bias: frame.da_bias.device_ptr(),
            db_bias: frame.db_bias.device_ptr(),
            strands: frame.strands.device_ptr(),
            strand_open: frame.strand_open.device_ptr(),
            strand_ends: frame.strand_ends.device_ptr(),
            strand_faces: frame.strand_faces.device_ptr(),
            r_strand: r(20),
            pa_heads: frame.pa_heads.device_ptr(),
            pa_probe: frame.pa_probe.device_ptr(),
            pa_key: frame.pa_key.device_ptr(),
            pa_value: frame.pa_value.device_ptr(),
            pa_frame: frame.pa_frame.device_ptr(),
            pa_diss: frame.pa_diss.device_ptr(),
            pa_current: frame.pa_current.device_ptr(),
            pa_read: frame.pa_read.device_ptr(),
            pa_scale: frame.pa_scale.device_ptr(),
            pa_run: frame.pa_run.device_ptr(),
            pa_met: frame.pa_met.device_ptr(),
            pa_z: frame.pa_z.device_ptr(),
            pa_e: frame.pa_e.device_ptr(),
            pa_dra: frame.pa_dra.device_ptr(),
            pa_gy: frame.pa_gy.device_ptr(),
            pa_gq: frame.pa_gq.device_ptr(),
            pa_gk: frame.pa_gk.device_ptr(),
            pa_gw: frame.pa_gw.device_ptr(),
            pa_gchart: frame.pa_gchart.device_ptr(),
            pa_gfric: frame.pa_gfric.device_ptr(),
            pa_gmet: frame.pa_gmet.device_ptr(),
            pa_tturn: frame.pa_tturn.device_ptr(),
            pa_tlog: frame.pa_tlog.device_ptr(),
            r_pa_read: r(21),
            r_pa_yre: r(22),
            r_pa_yim: r(23),
            r_pa_dra: r(24),
            r_pa_g: r(25),
            pa_open: frame.pa_open.device_ptr(),
            pa_open_key: frame.pa_open_key.device_ptr(),
            pa_open_value: frame.pa_open_value.device_ptr(),
            pa_open_diss: frame.pa_open_diss.device_ptr(),
            pa_hold: frame.pa_hold.device_ptr(),
            pa_sect: frame.pa_sect.device_ptr(),
            pa_member: frame.pa_member.device_ptr(),
            pa_mark: frame.pa_mark.device_ptr(),
            contact_y: frame.contact_y.device_ptr(),
            contact_gy: frame.contact_gy.device_ptr(),
            r_contact_gy: r(26),
            pk_open: frame.pk_open.device_ptr(),
            pk_ends: frame.pk_ends.device_ptr(),
            pk_state: frame.pk_state.device_ptr(),
            pk_read: frame.pk_read.device_ptr(),
            pk_scale: frame.pk_scale.device_ptr(),
            pk_face: frame.pk_face.device_ptr(),
            pk_dx: frame.pk_dx.device_ptr(),
            pk_dread: frame.pk_dread.device_ptr(),
            pk_cov: frame.pk_cov.device_ptr(),
            r_pk_read: r(27),
            r_pk_face_re: r(28),
            r_pk_face_im: r(29),
            r_pk_dread: r(30),
            split_dv: frame.split_dv.device_ptr(),
            split_dir: frame.split_dir.device_ptr(),
            split_out: frame.split_out.device_ptr(),
            tr_open: frame.tr_open.device_ptr(),
            tr_ends: frame.tr_ends.device_ptr(),
            hd_read: frame.hd_read.device_ptr(),
            tr_read: frame.tr_read.device_ptr(),
            hd_list: frame.hd_list.device_ptr(),
            hd_count: frame.hd_count.device_ptr(),
            hd_close: frame.hd_close.device_ptr(),
            hd_g: frame.hd_g.device_ptr(),
            ah_read: frame.ah_read.device_ptr(),
            ah_scale: frame.ah_scale.device_ptr(),
            ah_face: frame.ah_face.device_ptr(),
            ah_dread: frame.ah_dread.device_ptr(),
            ah_top: frame.ah_top.device_ptr(),
            r_ah_read: r(31),
            r_ah_face_re: r(32),
            r_ah_face_im: r(33),
            r_ah_dread: r(34),
            r_ah_top: r(35),
            cr_open: 0,
            cr_next: 0,
            cr_turn: frame.cr_turn.device_ptr(),
            cr_push: frame.cr_push.device_ptr(),
            cr_gate: frame.cr_gate.device_ptr(),
            cr_pgate: frame.cr_pgate.device_ptr(),
            cr_x: frame.cr_x.device_ptr(),
            cr_rest: frame.cr_rest.device_ptr(),
            cr_cov: frame.cr_cov.device_ptr(),
            cr_tick: frame.cr_tick.device_ptr(),
            mo_read: frame.mo_read.device_ptr(),
            mo_scale: frame.mo_scale.device_ptr(),
            mo_face: frame.mo_face.device_ptr(),
            mo_dr0: frame.mo_dr0.device_ptr(),
            mo_open: frame.mo_open.device_ptr(),
            mo_flag: frame.mo_flag.device_ptr(),
            r_mo_read: r(36),
            r_mo_face_re: r(37),
            r_mo_face_im: r(38),
            r_mo_dr0: r(39),
        }
    }

    /// Launch an entry of the tower's image on the card's stream.
    fn launch(&self, entry: &'static str, grid: Dim3, block: u32, shared: u32, params: &mut [*mut c_void]) -> std::result::Result<(), DeviceError> {
        let census = self.card.census();
        if shared > census.shared_per_block || grid.x > census.max_grid.x || block > census.max_threads_per_block {
            return Err(DeviceError::Launch { entry, clause: "the census carries the block, its grid and its shared surface" });
        }
        self.card.current()?;
        let started = match &self.profile {
            Some(_) => {
                self.card.synchronize()?;
                Some(Instant::now())
            }
            None => None,
        };
        self.module.function(entry)?.launch_on_shared(self.card.stream(), grid, Dim3 { x: block, y: 1, z: 1 }, shared, params)?;
        if let (Some(profile), Some(started)) = (&self.profile, started) {
            self.card.synchronize()?;
            let mut map = profile.borrow_mut();
            let slot = map.entry(entry).or_insert((0, 0));
            slot.0 += 1;
            slot.1 += started.elapsed().as_nanos();
        }
        Ok(())
    }

    fn law_launch(&self, entry: &'static str, grid: Dim3, block: u32, shared: u32, law: &LawWords, frame: &FrameWords, extra: Option<u32>) -> std::result::Result<(), DeviceError> {
        let mut law = *law;
        let mut frame = *frame;
        let mut extra = extra.unwrap_or(0);
        let mut params: Vec<*mut c_void> = vec![(&mut law as *mut LawWords).cast(), (&mut frame as *mut FrameWords).cast()];
        params.push((&mut extra as *mut u32).cast());
        self.launch(entry, grid, block, shared, &mut params[..if entry_takes_extra(entry) { 3 } else { 2 }])
    }

    /// The streams' refusals, read off the card.
    fn status(&self) -> Result<()> {
        let frame = self.frame.as_ref().ok_or(TowerError::Refused("a card pass needs its frame"))?;
        let status = self.card.fetch(&frame.status).map_err(device)?;
        for (s, &bits) in status.iter().enumerate() {
            if bits != 0 {
                let names = [(1, "a sum outgrew its 128-bit carrier"), (2, "a released value outgrew its 64-bit carrier"), (4, "a released value outgrew its 32-bit carrier"), (8, "a gated move reached the unit circle"), (16, "a class outside the declared alphabet"), (32, "a news phase or an arrival's ticks outgrew its carrier, or an open face was empty")];
                let named: Vec<&str> = names.iter().filter(|(b, _)| bits & b != 0).map(|(_, n)| *n).collect();
                return Err(TowerError::Realization(format!("the card refused stream {s}: {}", named.join("; "))));
            }
        }
        Ok(())
    }

    fn forward_shared(shape: &Shape) -> usize {
        let (a, w, n, f, l, k, r) = (shape.alphabet, shape.width, shape.modes, shape.contacts, shape.levels, shape.forms, shape.ranks);
        let (k2, kp) = shape.ring_reads();
        let ringed = usize::from(r > 0);
        let g = (THREADS as usize / w).max(1);
        let p = usize::from(shape.heads > 0);
        // The packets, a still level's held read (under a news clock without participation), the
        // heading's open traces and tick counts, and the heading each clocked level holds between
        // its ticks (its ratio, lift, maxima and hold, record §19).
        let (pk, pkd) = (shape.packets, usize::from(shape.packets > 0));
        let hold = usize::from(shape.news > 0 && shape.heads == 0);
        [16 * g * w, 16 * 32, 8 * l * 2 * n, 8 * (3 + shape.turned + 2 * shape.pumped) * n, 8 * 2 * n, 8 * 2 * w, 8 * w, 8 * a, 8 * a, 8 * 32, 4 * w, 4 * w, 4 * w, 4 * f, 4 * f, 4 * k, 16 * 2 * r, 4 * r, 8 * 2 * n * ringed, 4 * k2, 4 * w * ringed, 4 * kp, 8 * 2 * shape.moving, 4 * 3 * shape.strand_rings, 4 * 6 * shape.strand_rings, 8 * 2 * n * p, 8 * n * p, 8 * 6 * n * p, 8 * 2 * n * p, 8 * 2 * n * p, 8 * 2 * n * p, 8 * w * p, 4 * w * p, 8 * shape.heads * p, 8 * w * shape.mutual, 4 * l, 4 * l, 4 * l, 8 * 4 * l, 8 * pk * 2 * n, 4 * w * pkd, 4 * l * w * hold, 8 * 4 * l * hold, 4 * l * hold, 8 * shape.heading * w, 4 * shape.heading, 4 * shape.heading * w, 8 * shape.heading * w, 8 * 4 * shape.heading, 4 * shape.heading, 8 * shape.heading * w * shape.motive].iter().map(|&o| carve(o)).sum()
    }

    fn top_shared(shape: &Shape) -> usize {
        let w = shape.width;
        let (k2, kp) = shape.ring_reads();
        let ringed = usize::from(shape.ranks > 0);
        let g = (THREADS as usize / w).max(1);
        [16 * g * w, 8 * shape.alphabet, 8 * 32, 16 * 32 * ringed, 8 * w, 8 * kp, 8 * k2, 8 * w * ringed, 8 * w * shape.mutual].iter().map(|&o| carve(o)).sum()
    }

    fn ring_shared(shape: &Shape) -> usize {
        let r = shape.ranks;
        [16 * 2 * r, 16 * 5 * r, 16 * 4 * r, 8 * 2 * shape.modes, 4 * r].iter().map(|&o| carve(o)).sum()
    }

    fn split_shared(shape: &Shape) -> usize {
        let w = shape.width;
        let g = (THREADS as usize / w).max(1);
        [16 * g * w, 16 * 32, 16 * THREADS as usize, 4 * w].iter().map(|&o| carve(o)).sum()
    }

    fn contacts_shared(shape: &Shape) -> usize {
        let (w, f) = (shape.width, shape.contacts);
        let g = (THREADS as usize / w).max(1);
        let p = usize::from(shape.heads > 0);
        [16 * g * w, 16 * 32, 8 * w, 8 * f, 8 * f * shape.paired, 8 * w, 8 * w, 8 * 32, 8 * w * p, 8 * w * p].iter().map(|&o| carve(o)).sum()
    }

    fn dx_shared(shape: &Shape) -> usize {
        let families = 3 + shape.turned + 2 * shape.pumped + 6 * usize::from(shape.heads > 0);
        [8 * families * shape.modes, 8 * families * shape.width, 8 * 32].iter().map(|&o| carve(o)).sum()
    }

    fn participation_shared(shape: &Shape) -> usize {
        [8 * 2 * shape.modes, 16 * 32, 8 * 32].iter().map(|&o| carve(o)).sum()
    }

    fn ahead_shared(shape: &Shape) -> usize {
        [16 * 32, 8 * 32, 8 * shape.width, 8 * shape.width].iter().map(|&o| carve(o)).sum()
    }

    fn packet_shared(shape: &Shape) -> usize {
        [16 * 32, 8 * 32, 8 * shape.width].iter().map(|&o| carve(o)).sum()
    }

    /// The forward of every stream (`tower_forward`), keeping its temporaries when opened.
    /// [agent-inferred, October 31] The streams' credit at a read's opening made resident: marks of
    /// the present resident credit (each its own stream's), or values, uploaded as a new one.
    fn admit_credit(&mut self, tower: &Tower, opening: &[TowerState], from: usize) -> Result<()> {
        let marks: Vec<Option<(u64, usize)>> = opening.iter().map(|o| o.credit.as_deref().and_then(LevelCredit::residence)).collect();
        if marks.iter().all(Option::is_some) {
            let fits = self.credit.as_ref().is_some_and(|c| c.streams == opening.len() && marks.iter().enumerate().all(|(s, m)| *m == Some((c.generation, s))));
            return if fits { Ok(()) } else { Err(TowerError::Refused("a resident credit's marks of another generation or stream")) };
        }
        if marks.iter().any(Option::is_some) {
            return Err(TowerError::Refused("the streams' credit is resident or uploaded, never both"));
        }
        let extent = tower.credit_extent(from);
        if opening.iter().any(|o| o.credit.as_deref().and_then(|c| tower.credit_from_of(c)) != Some(from)) {
            return Err(TowerError::Refused("every stream's credit begins at the same level"));
        }
        // Credits at rest are zeroed where they live (record §28); any other is carried as words.
        let rested = opening.iter().all(|o| o.credit.as_deref().is_some_and(LevelCredit::at_rest));
        let mut words = Vec::new();
        if !rested {
            words.reserve(extent * opening.len());
            for o in opening {
                words.extend(tower.credit_words(o)?.ok_or(TowerError::Refused("every stream carries a credit"))?);
            }
        }
        let streams = opening.len();
        if !self.credit.as_ref().is_some_and(|c| c.streams == streams && c.extent == extent) {
            self.credit = None;
            let card = self.card;
            self.credit = Some(ResidentCredit { streams, from, extent, generation: 0, open: card.alloc(streams * extent).map_err(device)?, next: card.alloc(streams * extent).map_err(device)? });
        }
        let generation = self.generations;
        self.generations += 1;
        let credit = self.credit.as_mut().expect("allocated above");
        credit.from = from;
        if rested {
            self.card.zero_octets(&credit.open, 0, streams * extent * std::mem::size_of::<i64>()).map_err(device)?;
        } else {
            self.card.write(&credit.open, 0, &words).map_err(device)?;
        }
        credit.generation = generation;
        self.credit_pending = None;
        Ok(())
    }

    /// [agent-inferred, October 31] **The streams' resident credit returned to the host**: each
    /// state holding a mark of the present credit takes its moments back (a receipt or a parity
    /// reads them; a learner's sections never need to).
    pub fn fetch_credit(&mut self, tower: &Tower, states: &mut [TowerState]) -> Result<()> {
        let credit = self.credit.as_ref().ok_or(TowerError::Refused("no credit is resident on the card"))?;
        let marked = states.len() == credit.streams && states.iter().enumerate().all(|(s, o)| o.credit.as_deref().and_then(LevelCredit::residence) == Some((credit.generation, s)));
        if !marked {
            return Err(TowerError::Refused("a fetch reads the streams marked with the present resident credit"));
        }
        let words = self.card.fetch(&credit.open).map_err(device)?;
        for (s, state) in states.iter_mut().enumerate() {
            state.credit = Some(tower.credit_from_words(credit.from, &words[s * credit.extent..(s + 1) * credit.extent])?);
        }
        Ok(())
    }

    fn read_forward(&mut self, tower: &Tower, opening: &[TowerState], classes: &[&[usize]], targets: &[Vec<Option<usize>>], slot: Slot) -> Result<PassRead> {
        let law = tower.resident_law()?;
        Self::admits(&law)?;
        tower.admit_read(classes, targets)?;
        let d = law.declaration;
        let streams = classes.len();
        let cells = classes.first().map_or(0, |c| c.len().saturating_sub(1));
        if streams == 0 || cells == 0 || classes.iter().any(|c| c.len() != cells + 1) || targets.len() != streams || targets.iter().any(|t| t.len() != cells) {
            return Err(TowerError::Refused("the card reads streams of one section length"));
        }
        let ranks = law.ring.as_ref().map_or(0, |r| r.ranks);
        // Each strand's residue lies below its ring's modulus (strand-major, ring `j mod R`), as
        // every residue heard from rest does.
        let strand_rings = law.strands.as_ref().map_or(0, |st| st.rings);
        let below = |o: &TowerState| match &law.strands {
            None => o.strands.is_empty() && !o.reversed,
            Some(st) => o.strands.len() == 3 * st.rings && o.strands.iter().enumerate().all(|(j, &r)| i64::from(r) < i64::from(st.table[8 + 3 * (j % st.rings)])),
        };
        if opening.len() != streams
            || opening.iter().any(|o| o.ring.len() != ranks || o.hands.len() != ranks || !below(o) || o.modes.len() != d.levels || o.modes.iter().any(|m| m.len() != d.modes) || o.previous > d.alphabet)
        {
            return Err(TowerError::Refused("the card opens on states of the declared bank, each ring rank with its value and hand, and each strand's residue below its ring's modulus"));
        }
        // The streams' credit ([`ResidentCredit`]): none, or every stream's, at the levels a news
        // clock holds (`LevelCredit`); held resident since the last carry, or its values uploaded.
        let credited = opening.iter().filter(|o| o.credit.is_some()).count();
        // The first credited level: the resident credit's for its marks, else every stream's own.
        let credit_from = match opening.first().and_then(|o| o.credit.as_deref()) {
            None => d.levels,
            Some(c) if LevelCredit::residence(c).is_some() => self.credit.as_ref().map_or(d.levels, |r| r.from),
            Some(c) => tower.credit_from_of(c).ok_or(TowerError::Refused("a stream's credit of another tower's levels"))?,
        };
        let credit_levels = match (credited, &law.news) {
            (0, _) => 0,
            (c, Some(clock)) if c == streams && clock.first() < d.levels && law.participation.is_none() && credit_from < d.levels => d.levels - credit_from,
            (c, _) if c == streams => return Err(TowerError::Refused("the card carries the credit under a news clock that holds a level, beside no participation")),
            _ => return Err(TowerError::Refused("every stream carries a credit or none does")),
        };
        // Each stream's open packets: one a level from the clock's first clocked level up, of the
        // bank's modes, none below it; none without the packets ([`Tower::join_packets`]).
        let packet_from = if law.packets { law.news.map(|c| c.first()) } else { None };
        let packeted = |o: &TowerState| match packet_from {
            None => o.packets.is_empty(),
            Some(first) => o.packets.len() == d.levels && o.packets.iter().enumerate().all(|(l, a)| a.len() == if l >= first { d.modes } else { 0 }),
        };
        if !opening.iter().all(packeted) {
            return Err(TowerError::Refused("the card opens each stream's packets on the levels that hear one, of the bank's modes"));
        }
        // Each stream's open traces: one a level from the clock's first clocked level up, of the
        // face's width, none below it; none without the heading ([`Tower::join_heading`]).
        let heading_from = law.heading.and(law.news.map(|c| c.first()));
        let traced = |o: &TowerState| match heading_from {
            None => o.traces.is_empty(),
            Some(first) => o.traces.len() == d.levels && o.traces.iter().enumerate().all(|(l, tr)| tr.len() == if l >= first { d.width } else { 0 }),
        };
        if !opening.iter().all(traced) {
            return Err(TowerError::Refused("the card opens each stream's traces on the levels that carry a heading, of the face's width"));
        }
        let hd = heading_from.map_or(0, |first| d.levels - first);
        // The news clock's open face and phase, each mass within the face's total and a 64-bit
        // word (the forward's own faces are), the phase below the clock's period.
        let news_open: Vec<u64> = match &law.news {
            None => {
                if opening.iter().any(|o| o.open.is_some() || o.news != 0) {
                    return Err(TowerError::Refused("an open face or news phase without a news clock"));
                }
                Vec::new()
            }
            Some(clock) => {
                let period = clock.period(d.levels)?;
                let mut words = Vec::with_capacity(streams * (d.alphabet + 4));
                for o in opening {
                    if o.news >= period {
                        return Err(TowerError::Refused("a news phase past its clock's period"));
                    }
                    match &o.open {
                        None => {
                            words.extend([0, 0, 0, o.news]);
                            words.extend(std::iter::repeat_n(0, d.alphabet));
                        }
                        Some(face) => {
                            if face.masses.len() != d.alphabet || face.total == 0 || face.masses.iter().any(|&m| m > face.total || m > u64::MAX as u128) {
                                return Err(TowerError::Refused("the card opens on a face of the alphabet, each mass a 64-bit word within its total"));
                            }
                            words.extend([1, face.total as u64, (face.total >> 64) as u64, o.news]);
                            words.extend(face.masses.iter().map(|&m| m as u64));
                        }
                    }
                }
                words
            }
        };
        let forms = law.pair.as_ref().map_or(0, |p| p.forms);
        let (harmonics, ring_moves) = law.ring.as_ref().map_or((0, 0), |r| (r.harmonics, r.moves.iter().map(Vec::len).sum()));
        // The sites each stream carries open into the call at each level (a section runs on across
        // calls, and closes within one at its level's own count), each site of the bank's modes and
        // heads, with the frames, met dissipation and held current of the bank's modes.
        let carried: Vec<Vec<usize>> = opening.iter().map(|o| o.sites.iter().map(LevelSites::len).collect()).collect();
        if let Some(p) = &law.participation {
            let whole = |o: &TowerState| {
                (o.sites.is_empty() || o.sites.len() == d.levels)
                    && o.sites.iter().all(|sites| {
                        sites.len() < p.section
                            && sites.frame.len() == d.modes
                            && sites.met.len() == d.modes
                            && sites.current.len() == d.modes
                            && sites.keys.iter().chain(&sites.values).all(|site| site.len() == d.modes)
                            && sites.dissipation.iter().all(|site| site.len() == p.heads.len())
                    })
            };
            if !opening.iter().all(whole) {
                return Err(TowerError::Refused("the card carries each level's open section of the bank's modes and heads, short of its close"));
            }
        }
        let shape = Shape { alphabet: d.alphabet, width: d.width, modes: d.modes, contacts: d.contacts, levels: d.levels, len: law.len, streams, cells, forms, ranks, harmonics, ring_moves, turned: usize::from(d.turned), news: usize::from(law.news.is_some()), pumped: usize::from(d.pumped), moving: law.rotor.as_ref().map_or(0, |r| r.moving), paired: usize::from(d.contact != ContactLaw::Rectifying), foil: usize::from(d.contact == ContactLaw::PairLinear), strand_rings, strand_table: law.strands.as_ref().map_or(0, |st| st.table.len()), heads: law.participation.as_ref().map_or(0, |p| p.heads.len()), section: law.participation.as_ref().map_or(0, |p| p.section), carried: usize::from(carried.iter().flatten().any(|&n0| n0 > 0)), mutual: usize::from(law.mutual.is_some()), passage: if law.passage { law.news.map_or(0, |c| d.levels - c.first()) } else { 0 }, packets: if law.packets { law.news.map_or(0, |c| d.levels - c.first()) } else { 0 }, split: usize::from(d.contact == ContactLaw::Pair), heading: hd, motive: usize::from(law.motive && hd > 0), credit: credit_levels, credit_packets: if credit_levels > 0 && law.packets { (credit_from..d.levels).filter(|&l| law.news.is_some_and(|c| l + 1 >= c.first()) && l + 1 < d.levels).count() } else { 0 } };
        self.frame(shape).map_err(device)?;
        if slot == Slot::OpeningTicks && (law.news.is_none() || !self.ticks_kept) {
            return Err(TowerError::Refused("a reread on the opening's ticks reads a news clock's opening read, its frame still resident"));
        }
        let (mut words, levels) = Self::law_words(&law, streams, cells);
        let keep = slot == Slot::Opened;
        // The closure is read on the opening read, and on a reread only under the declared reading.
        let read_closure = hd > 0 && (keep || self.reread_closures);
        words.closure = u32::from(read_closure);
        // The credit advances in the reads a carry may keep: a reread, or an opening read a carry
        // asked for (`TowerCard::carry`); its material moments wait for the carry.
        let advance = credit_levels > 0 && (!keep || self.force_advance);
        if credit_levels == 0 {
            self.credit_pending = None;
        }
        if credit_levels > 0 {
            self.admit_credit(tower, opening, credit_from)?;
            words.credit = credit_levels as u32;
            words.credit_packet = u32::from(law.packets);
            words.credit_advance = u32::from(advance);
            words.credit_from = credit_from as u32;
            if keep && !self.force_advance {
                self.opened_reads = Some((classes.iter().map(|c| c.to_vec()).collect(), targets.to_vec()));
            }
        }
        // The forward's read: the opening (its temporaries kept), a reread, or a reread on the
        // opening's ticks.
        let read = match slot {
            Slot::Opened => 1u32,
            Slot::Reread => 0,
            Slot::OpeningTicks => 2,
        };
        {
            let frame = self.frame.as_ref().expect("the frame was just sized");
            let card = self.card;
            card.write(&frame.levels, 0, &levels).map_err(device)?;
            words.level = frame.levels.device_ptr();
            card.write(&frame.theta, 0, &tower.theta).map_err(device)?;
            card.write(&frame.families, 0, &Self::families(&law)).map_err(device)?;
            let mut gates = Vec::with_capacity(d.levels * d.modes * 4);
            for lv in &law.levels {
                for k in 0..d.modes {
                    gates.extend([lv.units[k].0, lv.units[k].1, lv.moduli[k], lv.logs[k]]);
                }
            }
            card.write(&frame.gates, 0, &gates).map_err(device)?;
            let roots: Vec<u64> = law.face_roots.iter().chain(&law.move_roots).map(|&r| r as u64).collect();
            card.write(&frame.roots, 0, &roots).map_err(device)?;
            let words_of_classes: Vec<u32> = classes.iter().flat_map(|c| c.iter().map(|&u| u.min(u32::MAX as usize) as u32)).collect();
            card.write(&frame.classes, 0, &words_of_classes).map_err(device)?;
            let target_words: Vec<i32> = targets.iter().flatten().map(|t| t.map_or(-1, |t| t.min(i32::MAX as usize) as i32)).collect();
            card.write(&frame.targets, 0, &target_words).map_err(device)?;
            let states: Vec<i64> = opening.iter().flat_map(|o| o.modes.iter().flatten().flat_map(|&(re, im)| [re, im])).collect();
            card.write(&frame.opening, 0, &states).map_err(device)?;
            if let Some(pair) = &law.pair {
                card.write(&frame.pair_values, 0, &pair.values).map_err(device)?;
            }
            if let Some(rotor) = law.rotor.as_ref().filter(|r| r.moving > 0) {
                card.write(&frame.rotor, 0, &rotor.keys).map_err(device)?;
            }
            if let Some(strands) = &law.strands {
                card.write(&frame.strands, 0, &strands.table).map_err(device)?;
                let open: Vec<u32> = opening.iter().flat_map(|o| o.strands.iter().copied().chain([u32::from(o.reversed)])).collect();
                card.write(&frame.strand_open, 0, &open).map_err(device)?;
            }
            if law.pair.is_some() || law.ring.is_some() {
                let previous: Vec<u32> = opening.iter().map(|o| o.previous as u32).collect();
                card.write(&frame.previous, 0, &previous).map_err(device)?;
            }
            if let Some(ring) = &law.ring {
                card.write(&frame.ring_opening, 0, &ring.opening).map_err(device)?;
                let shifts: Vec<u32> = ring.shifts.iter().flat_map(|&([ra, rb, rg], push, read)| [ra, rb, rg, push, read]).collect();
                card.write(&frame.ring_shifts, 0, &shifts).map_err(device)?;
                let restarts: Vec<i32> = ring.restarts.iter().map(|c| c.map_or(-1, |c| c as i32)).collect();
                card.write(&frame.ring_restarts, 0, &restarts).map_err(device)?;
                let index: Vec<u32> = std::iter::once(0).chain(ring.moves.iter().scan(0u32, |at, t| {
                    *at += t.len() as u32;
                    Some(*at)
                })).collect();
                card.write(&frame.ring_index, 0, &index).map_err(device)?;
                if ring_moves > 0 {
                    let table: Vec<i64> = ring.moves.iter().flatten().flat_map(|&(prev, cur, m)| [prev as i64, cur as i64, m[0], m[1], m[2], m[3]]).collect();
                    card.write(&frame.ring_table, 0, &table).map_err(device)?;
                }
                let rings: Vec<i128> = opening.iter().flat_map(|o| o.ring.iter().flat_map(|&(re, im)| [re, im])).collect();
                card.write(&frame.ring_open, 0, &rings).map_err(device)?;
                let hands: Vec<u32> = opening.iter().flat_map(|o| o.hands.iter().map(|&h| u32::from(h))).collect();
                card.write(&frame.hands_open, 0, &hands).map_err(device)?;
            }
            if !news_open.is_empty() {
                card.write(&frame.news_open, 0, &news_open).map_err(device)?;
            }
            if packet_from.is_some() {
                let open: Vec<i64> = opening.iter().flat_map(|o| o.packets.iter().flatten().flat_map(|&(re, im)| [re, im])).collect();
                card.write(&frame.pk_open, 0, &open).map_err(device)?;
            }
            if hd > 0 {
                let open: Vec<i64> = opening.iter().flat_map(|o| o.traces.iter().flatten().copied()).collect();
                card.write(&frame.tr_open, 0, &open).map_err(device)?;
            }
            if let Some(p) = &law.participation {
                let starts: Vec<u32> = std::iter::once(0).chain(p.heads.iter().scan(0u32, |at, &h| {
                    *at += h as u32;
                    Some(*at)
                })).collect();
                card.write(&frame.pa_heads, 0, &starts).map_err(device)?;
                // Each stream's open sites at each level at their places ([S][section][L], a level's
                // places past its own count unread), its running frames and met dissipation, which
                // the forward resumes from (a section at rest opens from rest), and its held currents
                // (re block, im block).
                let (n, l_, h) = (d.modes, d.levels, p.heads.len());
                let counts: Vec<u32> = carried.iter().flat_map(|c| (0..l_).map(|l| c.get(l).map_or(0, |&n0| n0 as u32))).collect();
                card.write(&frame.pa_open, 0, &counts).map_err(device)?;
                let mut held = vec![0i64; streams * l_ * 2 * n];
                for (s, o) in opening.iter().enumerate().filter(|(_, o)| !o.sites.is_empty()) {
                    let n0 = o.sites.iter().map(LevelSites::len).max().unwrap_or(0);
                    if n0 > 0 {
                        let (mut keys, mut values, mut diss) = (vec![0i64; n0 * l_ * n * 2], vec![0i64; n0 * l_ * n * 2], vec![0i64; n0 * l_ * h]);
                        for (l, sites) in o.sites.iter().enumerate() {
                            for j in 0..sites.len() {
                                let at = j * l_ + l;
                                keys[at * n * 2..(at + 1) * n * 2].copy_from_slice(&sites.keys[j].iter().flat_map(|&(re, im)| [re, im]).collect::<Vec<_>>());
                                values[at * n * 2..(at + 1) * n * 2].copy_from_slice(&sites.values[j].iter().flat_map(|&(re, im)| [re, im]).collect::<Vec<_>>());
                                diss[at * h..(at + 1) * h].copy_from_slice(&sites.dissipation[j]);
                            }
                        }
                        card.write(&frame.pa_open_key, s * p.section * l_ * n * 2, &keys).map_err(device)?;
                        card.write(&frame.pa_open_value, s * p.section * l_ * n * 2, &values).map_err(device)?;
                        card.write(&frame.pa_open_diss, s * p.section * l_ * h, &diss).map_err(device)?;
                    }
                    let run: Vec<i64> = o.sites.iter().flat_map(|sites| sites.frame.iter().flat_map(|&(re, im)| [re, im])).collect();
                    let met: Vec<i64> = o.sites.iter().flat_map(|sites| sites.met.iter().copied()).collect();
                    card.write(&frame.pa_run, s * l_ * n * 2, &run).map_err(device)?;
                    card.write(&frame.pa_met, s * l_ * n, &met).map_err(device)?;
                    for (l, sites) in o.sites.iter().enumerate() {
                        let at = (s * l_ + l) * 2 * n;
                        for (k, &(re, im)) in sites.current.iter().enumerate() {
                            held[at + k] = re;
                            held[at + n + k] = im;
                        }
                    }
                }
                card.write(&frame.pa_hold, 0, &held).map_err(device)?;
            }
            card.zero_octets(&frame.status, 0, 4 * streams).map_err(device)?;
            if keep {
                card.zero_octets(&frame.swell, 0, 8 * 4 * d.levels).map_err(device)?;
            }
            let mut fw = Self::frame_words(frame);
            if let Some(credit) = self.credit.as_ref().filter(|_| advance) {
                fw.cr_open = credit.open.device_ptr();
                fw.cr_next = credit.next.device_ptr();
            }
            let blocks = (law.len as u32).div_ceil(THREADS).clamp(1, 1024);
            self.law_launch("tower_transpose", Dim3 { x: blocks, y: words.families, z: 1 }, THREADS, 0, &words, &fw, None).map_err(device)?;
            self.law_launch("tower_forward", Dim3::x(streams as u32), THREADS, Self::forward_shared(&shape) as u32, &words, &fw, Some(read)).map_err(device)?;
            // The credit's material moments wait for the carry of this read (`tower_credit`).
            if advance {
                self.credit_pending = Some((slot_index(slot), words));
            }
        }
        self.status()?;
        let frame = self.frame.as_ref().expect("the frame was just sized");
        let faces = self.card.fetch(&frame.faces).map_err(device)?;
        let ends = self.card.fetch(&frame.ends).map_err(device)?;
        let (ring_ends, hands_ends) = if ranks > 0 { (self.card.fetch(&frame.ring_ends).map_err(device)?, self.card.fetch(&frame.hands_ends).map_err(device)?) } else { (Vec::new(), Vec::new()) };
        let swell = if keep { self.card.fetch(&frame.swell).map_err(device)? } else { Vec::new() };
        let news_ends = if law.news.is_some() { self.card.fetch(&frame.news_ends).map_err(device)? } else { Vec::new() };
        let strand_ends = if strand_rings > 0 { self.card.fetch(&frame.strand_ends).map_err(device)? } else { Vec::new() };
        let packet_ends = if packet_from.is_some() { self.card.fetch(&frame.pk_ends).map_err(device)? } else { Vec::new() };
        let trace_ends = if hd > 0 { self.card.fetch(&frame.tr_ends).map_err(device)? } else { Vec::new() };
        let (counts, closed) = if read_closure { (self.card.fetch(&frame.hd_count).map_err(device)?, self.card.fetch(&frame.hd_close).map_err(device)?) } else { (Vec::new(), Vec::new()) };
        // Each level's section at the read's end, as the host's state carries it: its carried sites
        // still read and the sites admitted since (a section that closed rests), with its running
        // frames, met dissipation and, under a news clock, its held current.
        let sections = match &law.participation {
            Some(p) => {
                let sect = self.card.fetch(&frame.pa_sect).map_err(device)?;
                let open = sect.iter().any(|&c| c > 0);
                let fetch = |b: &CardBuffer<'_, i64>| if open { self.card.fetch(b) } else { Ok(Vec::new()) };
                Some((
                    sect,
                    if open { self.card.fetch(&frame.pa_member).map_err(device)? } else { Vec::new() },
                    fetch(&frame.pa_key).map_err(device)?,
                    fetch(&frame.pa_value).map_err(device)?,
                    fetch(&frame.pa_diss).map_err(device)?,
                    fetch(&frame.pa_run).map_err(device)?,
                    fetch(&frame.pa_met).map_err(device)?,
                    if law.news.is_some() { self.card.fetch(&frame.pa_hold).map_err(device)? } else { Vec::new() },
                    p.heads.len(),
                    p.section,
                ))
            }
            None => None,
        };
        let faces: Vec<Vec<Option<(u128, u128)>>> = targets
            .iter()
            .enumerate()
            .map(|(s, t)| {
                t.iter()
                    .enumerate()
                    .map(|(i, t)| {
                        let at = 3 * (s * cells + i);
                        t.map(|_| (faces[at] as u128, faces[at + 1] as u128 | (faces[at + 2] as u128) << 64))
                    })
                    .collect()
            })
            .collect();
        let per = d.levels * d.modes * 2;
        let ends: Vec<TowerState> = opening
            .iter()
            .zip(classes)
            .enumerate()
            .map(|(s, (open, c))| {
                let mut state = open.clone();
                for (l, level) in state.modes.iter_mut().enumerate() {
                    for (k, mode) in level.iter_mut().enumerate() {
                        let at = s * per + (l * d.modes + k) * 2;
                        *mode = (ends[at], ends[at + 1]);
                    }
                }
                state.previous = c[cells - 1];
                // Participation's sites at each level: released when its section closes, the
                // opening's carried on with the sites admitted since while it is open; the held
                // current carried under a news clock.
                if let Some((sect, member, keys, values, diss, run, met, hold, heads, section)) = sections.as_ref() {
                    let (n, l_) = (d.modes, d.levels);
                    let phasor = |v: &[i64], at: usize| (v[2 * at], v[2 * at + 1]);
                    let opened = std::mem::take(&mut state.sites);
                    state.sites = (0..l_)
                        .map(|l| {
                            let (lead, members) = (sect[(s * l_ + l) * 2] as usize, sect[(s * l_ + l) * 2 + 1] as usize);
                            let mut sites = LevelSites::rest(n);
                            if !hold.is_empty() {
                                sites.current = (0..n).map(|k| (hold[(s * l_ + l) * 2 * n + k], hold[(s * l_ + l) * 2 * n + n + k])).collect();
                            }
                            if lead + members == 0 {
                                return sites;
                            }
                            if let Some(carried) = opened.get(l) {
                                sites.keys.extend_from_slice(&carried.keys[..lead]);
                                sites.values.extend_from_slice(&carried.values[..lead]);
                                sites.dissipation.extend_from_slice(&carried.dissipation[..lead]);
                            }
                            sites.frame = (0..n).map(|k| phasor(run, (s * l_ + l) * n + k)).collect();
                            sites.met = (0..n).map(|k| met[(s * l_ + l) * n + k]).collect();
                            for &t in &member[(s * l_ + l) * section..(s * l_ + l) * section + members] {
                                let q = (s * cells + t as usize) * l_ + l;
                                sites.keys.push((0..n).map(|k| phasor(keys, q * n + k)).collect());
                                sites.values.push((0..n).map(|k| phasor(values, q * n + k)).collect());
                                sites.dissipation.push(diss[q * heads..(q + 1) * heads].to_vec());
                            }
                            sites
                        })
                        .collect();
                }
                if ranks > 0 {
                    state.ring = (0..ranks).map(|r| (ring_ends[(s * ranks + r) * 2], ring_ends[(s * ranks + r) * 2 + 1])).collect();
                    state.hands = (0..ranks).map(|r| hands_ends[s * ranks + r] != 0).collect();
                }
                if strand_rings > 0 {
                    let end = &strand_ends[s * (3 * strand_rings + 1)..(s + 1) * (3 * strand_rings + 1)];
                    state.strands = end[..3 * strand_rings].to_vec();
                    state.reversed = end[3 * strand_rings] != 0;
                }
                if !news_ends.is_empty() {
                    let end = &news_ends[s * (d.alphabet + 4)..(s + 1) * (d.alphabet + 4)];
                    state.open = (end[0] != 0).then(|| TowerFace { masses: end[4..].iter().map(|&m| u128::from(m)).collect(), total: end[1] as u128 | (end[2] as u128) << 64 });
                    state.news = end[3];
                }
                if let Some(first) = packet_from {
                    let per = (d.levels - first) * d.modes * 2;
                    let end = &packet_ends[s * per..(s + 1) * per];
                    for (l, a) in state.packets.iter_mut().enumerate().skip(first) {
                        for (k, mode) in a.iter_mut().enumerate() {
                            let at = ((l - first) * d.modes + k) * 2;
                            *mode = (end[at], end[at + 1]);
                        }
                    }
                }
                if let Some(first) = heading_from {
                    for (l, tr) in state.traces.iter_mut().enumerate().skip(first) {
                        let at = (s * hd + l - first) * d.width;
                        tr.copy_from_slice(&trace_ends[at..at + d.width]);
                    }
                }
                state
            })
            .collect();
        // Each stream's closure faces a clocked level, `(e_jj, Σ_i e_ji)` tick by tick, as the
        // host's `Tower::closure_faces` reads them (empty below the first clocked level).
        let closures: Vec<Vec<Vec<(u128, u128)>>> = match heading_from.filter(|_| read_closure) {
            None => Vec::new(),
            Some(first) => (0..streams)
                .map(|s| {
                    (0..d.levels)
                        .map(|l| {
                            if l < first {
                                return Vec::new();
                            }
                            let i = s * hd + l - first;
                            (0..counts[i] as usize)
                                .map(|j| {
                                    let row = &closed[(i * cells + j) * 4..(i * cells + j) * 4 + 4];
                                    (row[0] as u128, row[1] as u128 | (row[2] as u128) << 64)
                                })
                                .collect()
                        })
                        .collect()
                })
                .collect(),
        };
        self.ends[slot_index(slot)] = Some(ends);
        if keep {
            self.opened = Some((words, levels));
            self.opened_current = true;
            self.ticks_kept = law.news.is_some();
        } else {
            self.opened_current = false;
        }
        let swell = swell.chunks_exact(4).map(|c| [c[0], c[1], c[2], c[3]]).collect();
        Ok(PassRead { faces, swell, closures })
    }

    /// The streams' covector summed (`tower_reverse_*`, `tower_outer_*`, `tower_encoding`,
    /// `tower_moves`), from the opening read's temporaries; with `split`, the reverse also keeps
    /// each contact's covector and `tower_split_read` forms the paired contacts' read against the
    /// directions already uploaded.
    fn read_reverse(&mut self, split: bool) -> Result<Vec<i128>> {
        let (mut words, levels) = self.opened.clone().filter(|_| self.opened_current).ok_or(TowerError::Refused("a card reverse reads the section's opening forward, its material still resident"))?;
        words.split = u32::from(split);
        let frame = self.frame.as_ref().ok_or(TowerError::Refused("a card pass needs its frame"))?;
        let shape = frame.shape;
        let mut fw = Self::frame_words(frame);
        if words.credit > 0 {
            let credit = self.credit.as_ref().ok_or(TowerError::Refused("a credited reverse reads the resident credit"))?;
            fw.cr_open = credit.open.device_ptr();
        }
        let (s, t, l) = (shape.streams, shape.cells, shape.levels);
        let q = (s * t) as u32;
        let card = self.card;
        card.zero_octets(&frame.status, 0, 4 * s).map_err(device)?;
        card.zero_octets(&frame.gradient, 0, 16 * shape.len).map_err(device)?;
        if shape.heads > 0 {
            card.zero_octets(&frame.pa_gfric, 0, 16 * s * l * shape.heads).map_err(device)?;
        }
        // The motive's series (`Tower::reverse_series`, record §29): the first term reads the face's
        // comparison; each later term's only source is the stream's covector of the heading before
        // each cell (`tower_motive_return`), its sums added to the earlier terms'.
        let motive = shape.motive > 0;
        if motive {
            card.zero_octets(&frame.mo_open, 0, 8 * s * shape.heading * shape.modes * 2).map_err(device)?;
        }
        let descents: Vec<u64> = levels.iter().skip(words.news_first as usize).filter(|_| shape.heading > 0).map(|lv| fw.gradient + 16 * lv.descent).collect();
        let mut term = 0u32;
        loop {
        words.term = term;
        if term == 0 {
        self.law_launch("tower_reverse_top", Dim3::x(q), THREADS, Self::top_shared(&shape) as u32, &words, &fw, None).map_err(device)?;
        // The face's read of the heading after each cell takes the top's covector before any
        // level's reverse moves it (`tower_reverse_ahead`).
        if shape.heading > 0 {
            self.law_launch("tower_reverse_ahead", Dim3::x(q), THREADS, Self::ahead_shared(&shape) as u32, &words, &fw, None).map_err(device)?;
        }
        } else {
            card.zero_octets(&frame.dx, 0, 8 * (s * t) * shape.width).map_err(device)?;
        }
        let mode_threads = (shape.modes as u32).next_multiple_of(32).min(THREADS);
        // Under a rotor the modes' scan exchanges each step's covector between the modes of a ring
        // (`Rotor::back`), so each mode holds one thread of the block and the block holds no other.
        let (scan_threads, scan_shared) = if shape.moving > 0 { (shape.modes as u32, 32 * shape.modes as u32) } else { (mode_threads, 0) };
        for level in (0..l).rev() {
            self.law_launch("tower_reverse_contacts", Dim3::x(q), THREADS, Self::contacts_shared(&shape) as u32, &words, &fw, Some(level as u32)).map_err(device)?;
            // A level that carries a heading returns the face's covector of the heading after each
            // cell to the read covector the contacts wrote, before the level's scan reads it
            // (`tower_reverse_heading`).
            if shape.heading > 0 && level as u32 >= words.news_first {
                self.law_launch("tower_reverse_heading", Dim3::x(s as u32), THREADS, 0, &words, &fw, Some(level as u32)).map_err(device)?;
            }
            // Participation's return reads the current's covector the contacts wrote and writes the
            // chart covectors the level's `tower_reverse_dx` returns to the input, and the transport's
            // sums the modes' scan adds to each cell's turn and gate.
            if shape.heads > 0 {
                self.law_launch("tower_reverse_participation", Dim3::x(s as u32), THREADS, Self::participation_shared(&shape) as u32, &words, &fw, Some(level as u32)).map_err(device)?;
            }
            // The ring's reverse reads the level's read covector and returns its own to it and to
            // the mode's move, before the modes' scan.
            if shape.ranks > 0 && level == words.ring_level as usize {
                self.law_launch("tower_reverse_ring", Dim3::x(s as u32), THREADS, Self::ring_shared(&shape) as u32, &words, &fw, None).map_err(device)?;
            }
            self.law_launch("tower_reverse_modes", Dim3::x(s as u32), scan_threads, scan_shared, &words, &fw, Some(level as u32)).map_err(device)?;
            self.law_launch("tower_reverse_dx", Dim3::x(q), THREADS, Self::dx_shared(&shape) as u32, &words, &fw, Some(level as u32)).map_err(device)?;
            // A level that hears a packet returns its read's covector to the fine level's scan,
            // which runs next (`tower_reverse_packet`).
            if shape.packets > 0 && level as u32 >= words.news_first {
                self.law_launch("tower_reverse_packet", Dim3::x(q), THREADS, Self::packet_shared(&shape) as u32, &words, &fw, Some(level as u32)).map_err(device)?;
            }
        }
        // The split read, every dormant pair of every level, from the contacts' covectors the levels
        // kept.
        if split {
            let grid = Dim3 { x: (shape.contacts / 2) as u32, y: l as u32, z: 1 };
            self.law_launch("tower_split_read", grid, THREADS, Self::split_shared(&shape) as u32, &words, &fw, None).map_err(device)?;
        }
        // A later term reads no face: the readout's and the face's descent's sums are the first
        // term's alone, and every other family's sum is added.
        for (i, (outer, wide)) in self.outer_families(&words, &levels, &fw).into_iter().enumerate() {
            if term > 0 && (i == 0 || descents.contains(&outer.out)) {
                continue;
            }
            let outer = if term > 0 { OuterWords { accumulate: 1, ..outer } } else { outer };
            self.launch_outer(&outer, wide).map_err(device)?;
        }
        // The opening's credit meets the material moments, added to the outer sums' covector
        // (`tower_credit_meet`; the moves' meeting is the modes' scan's).
        if words.credit > 0 {
            let items = (shape.modes * shape.width + shape.modes) as u32;
            self.law_launch("tower_credit_meet", Dim3 { x: items.div_ceil(THREADS), y: words.credit, z: 1 }, THREADS, 0, &words, &fw, None).map_err(device)?;
        }
        // The foil's biases each take a covector of their own, summed over every cell.
        if shape.foil > 0 {
            let entries = (2 * l * shape.contacts) as u32;
            self.law_launch("tower_pair_biases", Dim3::x(entries.div_ceil(THREADS)), THREADS, 0, &words, &fw, None).map_err(device)?;
        }
        if shape.ranks > 0 {
            let entries = (shape.ranks * shape.rank_material()) as u32;
            self.law_launch("tower_ring_factors", Dim3::x(entries.div_ceil(THREADS).min(1024)), THREADS, 0, &words, &fw, None).map_err(device)?;
        }
        let class_threads = (shape.width as u32).next_multiple_of(32).min(THREADS);
        self.law_launch("tower_encoding", Dim3::x(shape.alphabet as u32), class_threads, 0, &words, &fw, None).map_err(device)?;
        self.law_launch("tower_moves", Dim3::x(l as u32), mode_threads, 0, &words, &fw, None).map_err(device)?;
        if shape.heads > 0 {
            let head_threads = (shape.heads as u32).next_multiple_of(32).min(THREADS);
            self.law_launch("tower_pa_friction", Dim3::x(l as u32), head_threads, 0, &words, &fw, None).map_err(device)?;
        }
        if !motive {
            break;
        }
        // The term's input covector reaches D↓ against each heading before its cell, and returns the
        // next term's source; the source at the first cell's heading reaches C^→ against the carried
        // modes' face here.
        card.zero_octets(&frame.mo_flag, 0, 4).map_err(device)?;
        self.law_launch("tower_motive_return", Dim3::x(q), THREADS, Self::ahead_shared(&shape) as u32 + 8 * shape.width as u32, &words, &fw, None).map_err(device)?;
        for (outer, wide) in self.motive_families(&words, &levels, &fw) {
            self.launch_outer(&outer, wide).map_err(device)?;
        }
        term += 1;
        if self.card.fetch(&frame.mo_flag).map_err(device)?.first().copied().unwrap_or(0) == 0 {
            break;
        }
        }
        self.times.terms += u64::from(term.max(1));
        self.status()?;
        let frame = self.frame.as_ref().expect("checked above");
        self.card.fetch(&frame.gradient).map_err(device)
    }

    /// The motive's sums of one term ([`Tower::join_motive`], `tower_motive_return`): at each
    /// clocked level, D↓ takes the term's input covector against the heading before each cell,
    /// `Σ δx⁰ ĥᵀ`, and C^→ the next term's source at the first cell against the carried modes'
    /// face (re, and im negated), each added to its place.
    fn motive_families(&self, law: &LawWords, levels: &[LevelWords], fw: &FrameWords) -> Vec<(OuterWords, bool)> {
        let (w, n, s, t, hd) = (law.width as u64, law.modes as u64, law.streams, law.cells, law.heading as u64);
        let q = s as u64 * t as u64;
        let mut out = Vec::new();
        for (i, lv) in levels.iter().skip(law.news_first as usize).enumerate() {
            let i = i as u64;
            let words = |y: u64, y_stride: u64, x: u64, x_stride: u64, y_reach: u64, x_reach: u64, rows: u64, cols: u64, negate: bool, out: u64, cells: u32| OuterWords {
                y,
                y_stride,
                x,
                x_stride,
                y_reach,
                x_reach,
                reach_stride: 1,
                rows: rows as u32,
                cols: cols as u32,
                streams: s,
                cells,
                negate: negate as i32,
                bias: 0,
                out,
                bias_out: 0,
                status: fw.status,
                groups: 1,
                accumulate: 1,
                partial: 0,
            };
            out.push((words(fw.dx, w, fw.mo_read + 4 * i * w, hd * w, fw.r_dx, fw.r_mo_read + 8 * i * q, w, w, false, fw.gradient + 16 * lv.fine_descent, t), false));
            out.push((words(fw.mo_dr0 + 8 * i * w, hd * w, fw.mo_face + 8 * i * 2 * n, hd * 2 * n, fw.r_mo_dr0 + 8 * i * s as u64, fw.r_mo_face_re + 8 * i * s as u64, w, n, false, fw.gradient + 16 * lv.heading_re, 1), true));
            out.push((words(fw.mo_dr0 + 8 * i * w, hd * w, fw.mo_face + 8 * i * 2 * n + 8 * n, hd * 2 * n, fw.r_mo_dr0 + 8 * i * s as u64, fw.r_mo_face_im + 8 * i * s as u64, w, n, true, fw.gradient + 16 * lv.heading_im, 1), true));
        }
        out
    }

    /// Every family's outer sum: `(words, whether x is 64-bit)`.
    fn outer_families(&self, law: &LawWords, levels: &[LevelWords], fw: &FrameWords) -> Vec<(OuterWords, bool)> {
        let (a, w, n, f, l) = (law.alphabet as u64, law.width as u64, law.modes as u64, law.contacts as u64, law.levels as u64);
        let (s, t) = (law.streams, law.cells);
        let gradient = |offset: u64| fw.gradient + 16 * offset;
        let at64 = |base: u64, offset: u64| base + 8 * offset;
        let at32 = |base: u64, offset: u64| base + 4 * offset;
        let family = |y: u64, y_stride: u64, x: u64, x_stride: u64, y_reach: u64, x_reach: u64, reach_stride: u64, rows: u64, cols: u64, negate: bool, out: u64, bias_out: Option<u64>| OuterWords {
            y,
            y_stride,
            x,
            x_stride,
            y_reach,
            x_reach,
            reach_stride,
            rows: rows as u32,
            cols: cols as u32,
            streams: s,
            cells: t,
            negate: negate as i32,
            bias: bias_out.is_some() as u32,
            out,
            bias_out: bias_out.unwrap_or(0),
            status: fw.status,
            groups: 1,
            accumulate: 0,
            partial: 0,
        };
        let added = |(words, wide): (OuterWords, bool)| (OuterWords { accumulate: 1, ..words }, wide);
        // The readout takes `Σ δz xᵀ` and its bias `Σ δz`; under a mutual contact its place holds
        // `J`, which takes `Σ G_y xᵀ`, and the classes' constants are summed beside the encoding's
        // covector (`tower_encoding`).
        let mut out = vec![if law.mutual != 0 {
            (family(fw.contact_gy, w, fw.top, w, fw.r_contact_gy, fw.r_top, 1, w, w, false, gradient(law.readout), None), false)
        } else {
            (family(fw.dz, a, fw.top, w, fw.r_dz, fw.r_top, 1, a, w, false, gradient(law.readout), Some(gradient(law.readout_bias))), false)
        }];
        for level in 0..l as usize {
            let lv = &levels[level];
            let lu = level as u64;
            out.push((family(at64(fw.dy, lu * w), l * w, at32(fw.conduct, lu * f), l * f, at64(fw.r_dy, lu), at64(fw.r_conduct, lu), l, w, f, false, gradient(lv.ret), Some(gradient(lv.ret_bias))), false));
            // Each drive's material takes its covector against the read; its bias the same covector,
            // but under the foil, whose biases are summed on their own (`tower_pair_biases`).
            let bias = |offset: u64| (law.contact != 2).then(|| gradient(offset));
            out.push((family(at64(fw.da, lu * f), l * f, at32(fw.read, lu * w), l * w, at64(fw.r_da, lu), at64(fw.r_read, lu), l, f, w, false, gradient(lv.contact), bias(lv.contact_bias)), false));
            if law.contact != 0 {
                out.push((family(at64(fw.db, lu * f), l * f, at32(fw.read, lu * w), l * w, at64(fw.r_db, lu), at64(fw.r_read, lu), l, f, w, false, gradient(lv.pair), bias(lv.pair_bias)), false));
            }
            out.push((family(at64(fw.dread, lu * w), l * w, at64(fw.face, lu * 2 * n), l * 2 * n, at64(fw.r_dread, lu), at64(fw.r_face_re, lu), l, w, n, false, gradient(lv.read_re), None), true));
            out.push((family(at64(fw.dread, lu * w), l * w, at64(fw.face, lu * 2 * n + n), l * 2 * n, at64(fw.r_dread, lu), at64(fw.r_face_im, lu), l, w, n, true, gradient(lv.read_im), None), true));
            // A level that hears a packet: its push, gate and turn read the packet's read (zero where
            // the level is still, as are their covectors), and the read's covector against the
            // packet's face is added onto the fine level's read, whose own family was pushed above.
            // The packets' buffers hold the levels that hear one (`[S][T][PK]…`, from the clock's
            // first clocked level), their reaches every level (`[S][T][L]`).
            let hears = law.packets != 0 && level as u32 >= law.news_first;
            let pk = law.packets as u64;
            let (input, input_stride, r_input) = if hears {
                (at32(fw.pk_read, (lu - law.news_first as u64) * w), pk * w, at64(fw.r_pk_read, lu))
            } else {
                (at32(fw.input, lu * w), l * w, at64(fw.r_input, lu))
            };
            if hears {
                let (fine, p) = (&levels[level - 1], lu - law.news_first as u64);
                out.push(added((family(at64(fw.pk_dread, p * w), pk * w, at64(fw.pk_face, p * 2 * n), pk * 2 * n, at64(fw.r_pk_dread, lu), at64(fw.r_pk_face_re, lu), l, w, n, false, gradient(fine.read_re), None), true)));
                out.push(added((family(at64(fw.pk_dread, p * w), pk * w, at64(fw.pk_face, p * 2 * n + n), pk * 2 * n, at64(fw.r_pk_dread, lu), at64(fw.r_pk_face_im, lu), l, w, n, true, gradient(fine.read_im), None), true)));
            }
            out.push((family(at64(fw.gre, lu * n), l * n, input, input_stride, at64(fw.r_gre, lu), r_input, l, n, w, false, gradient(lv.push_re), None), false));
            out.push((family(at64(fw.gim, lu * n), l * n, input, input_stride, at64(fw.r_gim, lu), r_input, l, n, w, false, gradient(lv.push_im), None), false));
            out.push((family(at64(fw.dq, lu * n), l * n, input, input_stride, at64(fw.r_dq, lu), r_input, l, n, w, false, gradient(lv.gate), Some(gradient(lv.gate_bias))), false));
            if law.turned != 0 {
                out.push((family(at64(fw.ds, lu * n), l * n, input, input_stride, at64(fw.r_ds, lu), r_input, l, n, w, false, gradient(lv.turn), Some(gradient(lv.turn_bias))), false));
            }
            if law.pumped != 0 {
                out.push((family(at64(fw.dk, lu * n), l * n, at32(fw.input, lu * w), l * w, at64(fw.r_dk, lu), at64(fw.r_input, lu), l, n, w, false, gradient(lv.pump), Some(gradient(lv.pump_bias))), false));
                out.push((family(at64(fw.dp, lu * n), l * n, at32(fw.input, lu * w), l * w, at64(fw.r_dp, lu), at64(fw.r_input, lu), l, n, w, false, gradient(lv.pump_axis), Some(gradient(lv.pump_axis_bias))), false));
            }
            // Participation: each chart takes its turned covector against the level's input, W₁ᵃ the
            // drives' covector against the ratio read, and the current's read ∂r̂ᵃ against y.
            if law.participation != 0 {
                let ql = s as u64 * t as u64 * l;
                for f_ in 0..6u64 {
                    out.push((family(at64(fw.pa_gchart, (lu * 6 + f_) * n), l * 6 * n, at32(fw.input, lu * w), l * w, at64(fw.r_pa_g, f_ * ql + lu), at64(fw.r_input, lu), l, n, w, false, gradient(lv.pa[f_ as usize]), None), false));
                }
                out.push((family(at64(fw.da, lu * f), l * f, at32(fw.pa_read, lu * w), l * w, at64(fw.r_da, lu), at64(fw.r_pa_read, lu), l, f, w, false, gradient(lv.pa[8]), None), false));
                out.push((family(at64(fw.pa_dra, lu * w), l * w, at64(fw.pa_current, lu * 2 * n), l * 2 * n, at64(fw.r_pa_dra, lu), at64(fw.r_pa_yre, lu), l, w, n, false, gradient(lv.pa[6]), None), true));
                out.push((family(at64(fw.pa_dra, lu * w), l * w, at64(fw.pa_current, lu * 2 * n + n), l * 2 * n, at64(fw.r_pa_dra, lu), at64(fw.r_pa_yim, lu), l, w, n, true, gradient(lv.pa[7]), None), true));
            }
            // The passage: `W₁ˣ` takes the drives' covector against the level's input, on the levels
            // the clock holds.
            if law.passage != 0 && level as u32 >= law.news_first {
                out.push((family(at64(fw.da, lu * f), l * f, at32(fw.input, lu * w), l * w, at64(fw.r_da, lu), at64(fw.r_input, lu), l, f, w, false, gradient(lv.passage), None), false));
            }
            // The heading (its buffers `[S][T][HD]…` and reaches `[HD][S][T]`, from the clock's
            // first clocked level): the descent takes the top's covector against the heading after
            // the cell that the face read, `Σ δx ĥ⁺ᵀ`, and the heading's read the covector of its
            // raw read against the face it read after each cell (the closure is read, not learned).
            if law.heading != 0 && level as u32 >= law.news_first {
                let (hd, i, q) = (law.heading as u64, lu - law.news_first as u64, s as u64 * t as u64);
                out.push((family(fw.ah_top, w, at32(fw.ah_read, i * w), hd * w, fw.r_ah_top, at64(fw.r_ah_read, i * q), 1, w, w, false, gradient(lv.descent), None), false));
                out.push((family(at64(fw.ah_dread, i * w), hd * w, at64(fw.ah_face, i * 2 * n), hd * 2 * n, at64(fw.r_ah_dread, i * q), at64(fw.r_ah_face_re, i * q), 1, w, n, false, gradient(lv.heading_re), None), true));
                out.push((family(at64(fw.ah_dread, i * w), hd * w, at64(fw.ah_face, i * 2 * n + n), hd * 2 * n, at64(fw.r_ah_dread, i * q), at64(fw.r_ah_face_im, i * q), 1, w, n, true, gradient(lv.heading_im), None), true));
            }
        }
        // The strands' materials take their level's drives' covectors against the faces,
        // `Σ δa sᵀ` and `Σ δb sᵀ`; the faces carry none.
        if law.strand_rings > 0 {
            let (su, c) = (law.strand_level as u64, 6 * law.strand_rings as u64);
            out.push((family(at64(fw.da, su * f), l * f, fw.strand_faces, c, at64(fw.r_da, su), at64(fw.r_strand, su), l, f, c, false, gradient(law.strand_contact), None), false));
            if law.contact != 0 {
                out.push((family(at64(fw.db, su * f), l * f, fw.strand_faces, c, at64(fw.r_db, su), at64(fw.r_strand, su), l, f, c, false, gradient(law.strand_pair), None), false));
            }
        }
        // The pair face's readout takes the face's covector against the pair read, `Σ δz c(p)ᵀ`,
        // and its lift the bottom covector, `Σ δx⁰ c(p)ᵀ`.
        let k = law.forms as u64;
        if k > 0 {
            out.push((family(fw.dz, a, fw.pair, k, fw.r_dz, fw.r_pair, 1, a, k, false, gradient(law.pair_readout), None), false));
            out.push((family(fw.dx, w, fw.pair, k, fw.r_dx, fw.r_pair, 1, w, k, false, gradient(law.pair_lift), None), false));
        }
        // The ring's readout takes the face's covector against its pair read with the top face,
        // `Σ δz (x̂ ⊗ ρ)ᵀ`.
        if law.ring_ranks > 0 {
            let kp = (w + 1) * 2 * law.ring_ranks as u64 * law.ring_harmonics as u64;
            out.push((family(fw.dz, a, fw.ring_pair, kp, fw.r_dz, fw.r_ring_pair, 1, a, kp, false, gradient(law.ring_readout), None), false));
        }
        out
    }

    /// The groups a family's streams are split over: enough blocks to hold every multiprocessor
    /// four deep (`4·SM` over the family's tiles), at most one group a stream.
    /// A family with no outputs (the pair face's on a tower without one) is one empty tile.
    fn groups(rows: u32, width: u32, streams: u32, multiprocessors: u32) -> u32 {
        let tiles = (width.div_ceil(OUTER_COLS) * rows.div_ceil(OUTER_ROWS)).max(1);
        (4 * multiprocessors).div_ceil(tiles).clamp(1, streams.max(1))
    }

    /// The group sums' extent: the widest family's outputs times its groups, over every family's
    /// rows and columns as [`TowerCard::outer_families`] launches them (a bias is one column more).
    /// A family's groups depend on its own shape, so a family with no bias is listed beside the one
    /// with: the pushes' and participation's charts `(n, w)` and `W₁ᵃ`'s `(f, w)`.
    fn partial_extent(shape: &Shape, multiprocessors: u32) -> usize {
        let (a, w, n, f, k) = (shape.alphabet as u32, shape.width as u32, shape.modes as u32, shape.contacts as u32, shape.forms as u32);
        let kp = shape.ring_reads().1 as u32;
        let c = 6 * shape.strand_rings as u32;
        [(a, w + 1), (w, f + 1), (f, w + 1), (f, w), (w, n), (n, w), (n, w + 1), (a, k), (w, k), (a, kp), (f, c), (w, w)]
            .iter()
            .map(|&(rows, width)| (rows * width) as usize * Self::groups(rows, width, shape.streams as u32, multiprocessors) as usize)
            .max()
            .unwrap_or(0)
    }

    fn launch_outer(&self, words: &OuterWords, wide_x: bool) -> std::result::Result<(), DeviceError> {
        let mut words = *words;
        let frame = self.frame.as_ref().ok_or(DeviceError::Launch { entry: "tower_outer", clause: "a frame" })?;
        let width = words.cols + words.bias;
        words.groups = Self::groups(words.rows, width, words.streams, self.card.census().multiprocessors);
        words.partial = frame.partial.device_ptr();
        if (words.rows * width) as usize * words.groups as usize > frame.partial.len() {
            return Err(DeviceError::Launch { entry: "tower_outer", clause: "the group sums fit their buffer" });
        }
        let grid = Dim3 { x: width.div_ceil(OUTER_COLS), y: words.rows.div_ceil(OUTER_ROWS), z: words.groups };
        let mut params: [*mut c_void; 1] = [(&mut words as *mut OuterWords).cast()];
        self.launch(if wide_x { "tower_outer_x64" } else { "tower_outer_x32" }, grid, THREADS, 0, &mut params)?;
        if words.groups > 1 {
            let blocks = (words.rows * width).div_ceil(THREADS).min(1024);
            let mut params: [*mut c_void; 1] = [(&mut words as *mut OuterWords).cast()];
            self.launch("tower_outer_reduce", Dim3::x(blocks), THREADS, 0, &mut params)?;
        }
        Ok(())
    }

    /// The realization as it runs at the frame's shape (the hardware law's report).
    fn report(&self) -> String {
        let census = self.card.census();
        match self.frame.as_ref().map(|f| f.shape) {
            None => format!("card {}: no section read yet", census.name),
            Some(shape) => {
                let q = shape.streams * shape.cells;
                let split = if shape.split > 0 { format!("; the split read, when formed, {} blocks (one a dormant pair of a level) x {THREADS} threads, every stream's cells a chunk of {THREADS} at a time", shape.levels * shape.contacts / 2) } else { String::new() };
                let participation = if shape.heads > 0 {
                    format!("; participation's {} heads one warp a head, the warps taking the heads in turn, in the forward's block and in its own reverse of {} blocks (one a stream, its cells in order)", shape.heads, shape.streams)
                } else {
                    String::new()
                };
                format!(
                    "card {} ({} multiprocessors): forward {} blocks (one a stream, its {} cells in order) x {THREADS} threads; reverse {q} blocks (one a cell) x {THREADS} threads, the modes' scan {} blocks x {} threads (one a mode); outer sums in tiles of {OUTER_ROWS}x{OUTER_COLS} outputs, 4 a thread{participation}{split}",
                    census.name,
                    census.multiprocessors,
                    shape.streams,
                    shape.cells,
                    shape.streams,
                    (shape.modes as u32).next_multiple_of(32).min(THREADS)
                )
            }
        }
    }
}

fn entry_takes_extra(entry: &str) -> bool {
    matches!(entry, "tower_forward" | "tower_reverse_contacts" | "tower_reverse_modes" | "tower_reverse_dx" | "tower_reverse_participation" | "tower_reverse_packet" | "tower_reverse_heading")
}

impl PassRealization for TowerCard<'_> {
    fn realization(&self) -> String {
        self.report()
    }

    fn admit(&self, tower: &Tower) -> Result<()> {
        Self::admits(&tower.resident_law()?)
    }

    fn series_read(&mut self) -> Option<(u64, u64)> {
        let read = (self.times.reverses - self.series_seen.0, self.times.terms - self.series_seen.1);
        self.series_seen = (self.times.reverses, self.times.terms);
        self.frame.as_ref().is_some_and(|f| f.shape.motive > 0).then_some(read)
    }

    fn forward(&mut self, tower: &Tower, opening: &[TowerState], classes: &[&[usize]], targets: &[Vec<Option<usize>>], slot: Slot) -> Result<PassRead> {
        let started = Instant::now();
        // Only a completed read is counted, so the timing reports passes the card carried.
        let read = self.read_forward(tower, opening, classes, targets, slot)?;
        self.times.forwards += 1;
        self.times.forward_ns += started.elapsed().as_nanos();
        Ok(read)
    }

    fn reverse(&mut self, _tower: &Tower, _opening: &[TowerState], _classes: &[&[usize]], _compared: Option<&[&[Option<usize>]]>) -> Result<Vec<i128>> {
        // The comparison is the opening read's targets, uploaded with it.
        let started = Instant::now();
        let g = self.read_reverse(false)?;
        self.times.reverses += 1;
        self.times.reverse_ns += started.elapsed().as_nanos();
        Ok(g)
    }

    fn reverse_split(&mut self, tower: &Tower, _opening: &[TowerState], _classes: &[&[usize]], _compared: Option<&[&[Option<usize>]]>, paired: &PairedContacts) -> Result<(Vec<i128>, SplitRead)> {
        paired.admits(tower)?;
        let started = Instant::now();
        let card = self.card;
        let frame = self.frame.as_mut().ok_or(TowerError::Refused("a card pass needs its frame"))?;
        let shape = frame.shape;
        if shape.split == 0 || shape.contacts != tower.declaration.contacts || shape.levels != paired.levels.len() {
            return Err(TowerError::Refused("a split read of the tower the opening read carried"));
        }
        let (w, h) = (shape.width, shape.contacts / 2);
        if frame.split_dv.is_empty() {
            let (ql, l, f) = (shape.streams * shape.cells * shape.levels, shape.levels, shape.contacts);
            frame.split_dv = card.alloc(ql * f).map_err(device)?;
            frame.split_dir = card.alloc(l * h * w).map_err(device)?;
            frame.split_out = card.alloc(l * h * (2 + w)).map_err(device)?;
        }
        let frame = self.frame.as_ref().expect("checked above");
        // Each pair's direction, zero where it is founded (its read is not read back).
        let directions: Vec<i32> = paired.levels.iter().flat_map(|pairs| pairs.iter().flat_map(|v| v.as_ref().map_or_else(|| vec![0; w], Clone::clone))).collect();
        self.card.write(&frame.split_dir, 0, &directions).map_err(device)?;
        let g = self.read_reverse(true)?;
        let frame = self.frame.as_ref().expect("checked above");
        let out = self.card.fetch(&frame.split_out).map_err(device)?;
        let levels = paired
            .levels
            .iter()
            .enumerate()
            .map(|(l, pairs)| {
                pairs
                    .iter()
                    .enumerate()
                    .map(|(e, direction)| match direction {
                        None => PairRead::default(),
                        Some(_) => {
                            let at = (l * h + e) * (2 + w);
                            PairRead { score: out[at], squares: out[at + 1], turned: out[at + 2..at + 2 + w].to_vec() }
                        }
                    })
                    .collect()
            })
            .collect();
        self.times.reverses += 1;
        self.times.reverse_ns += started.elapsed().as_nanos();
        Ok((g, SplitRead { levels }))
    }

    fn reread_closures(&mut self, on: bool) {
        self.reread_closures = on;
    }

    fn forms_split(&self) -> bool {
        true
    }

    fn last_faces(&mut self) -> Result<Vec<TowerFace>> {
        // The opening read keeps every cell's masses on the card; only the last cell's cross back.
        if !self.opened_current {
            return Err(TowerError::Refused("a face is read from the opening forward, still resident"));
        }
        let frame = self.frame.as_ref().ok_or(TowerError::Refused("a card pass needs its frame"))?;
        let shape = frame.shape;
        (0..shape.streams)
            .map(|s| {
                let q = s * shape.cells + shape.cells - 1;
                let masses = self.card.fetch_range(&frame.masses, q * shape.alphabet, shape.alphabet).map_err(device)?;
                let total = self.card.fetch_range(&frame.totals, 2 * q, 2).map_err(device)?;
                Ok(TowerFace { masses: masses.into_iter().map(u128::from).collect(), total: total[0] as u128 | (total[1] as u128) << 64 })
            })
            .collect()
    }

    fn carry(&mut self, tower: &Tower, states: &mut [TowerState], opening: &[TowerState], slot: Slot) -> Result<()> {
        let i = slot_index(slot);
        let credited = self.ends[i].as_ref().is_some_and(|ends| ends.iter().any(|e| e.credit.is_some()));
        // The carried read's credit advance: a reread's waits here; an opening read advanced none,
        // so it is read again advancing it (the same faces and ends, bit for bit).
        if credited && self.credit_pending.as_ref().map(|p| p.0) != Some(i) {
            if i != 0 {
                return Err(TowerError::Refused("a credited carry of a reread that a later read replaced"));
            }
            let (classes, targets) = self.opened_reads.clone().ok_or(TowerError::Refused("a credited carry of an opening read keeps its classes"))?;
            let parts: Vec<&[usize]> = classes.iter().map(Vec::as_slice).collect();
            self.force_advance = true;
            let read = self.read_forward(tower, opening, &parts, &targets, Slot::Opened);
            self.force_advance = false;
            read?;
        }
        if credited {
            let (_, words) = self.credit_pending.take().ok_or(TowerError::Refused("a credited carry reads its read's advance"))?;
            let frame = self.frame.as_ref().ok_or(TowerError::Refused("a credited carry needs its frame"))?;
            let mut fw = Self::frame_words(frame);
            let credit = self.credit.as_ref().ok_or(TowerError::Refused("a credited carry reads the resident credit"))?;
            fw.cr_open = credit.open.device_ptr();
            fw.cr_next = credit.next.device_ptr();
            // The per-mode moments over the read's cells, one thread a mode, then the material
            // moments' closed form (record §27).
            let mode_threads = words.modes.next_multiple_of(32).min(THREADS);
            self.law_launch("tower_credit_moments", Dim3 { x: words.streams, y: words.credit, z: 1 }, mode_threads, 0, &words, &fw, None).map_err(device)?;
            self.law_launch("tower_credit", Dim3 { x: words.streams, y: words.credit, z: 1 }, THREADS, credit_shared(&words), &words, &fw, None).map_err(device)?;
            self.status()?;
        }
        let ends = self.ends[i].take().ok_or(TowerError::Refused("a carry reads a kept forward"))?;
        if ends.len() != states.len() {
            return Err(TowerError::Refused("a carry continues every stream"));
        }
        for (state, end) in states.iter_mut().zip(ends) {
            *state = end;
        }
        // The carried credit is the kept read's advance: it becomes the opening's, and the streams
        // hold its mark.
        if credited {
            let generation = self.generations;
            let credit = self.credit.as_mut().ok_or(TowerError::Refused("a credited carry reads the resident credit"))?;
            std::mem::swap(&mut credit.open, &mut credit.next);
            credit.generation = generation;
            self.generations += 1;
            for (s, state) in states.iter_mut().enumerate() {
                state.credit = Some(LevelCredit::resident_mark(generation, s));
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A tower without a pair face sizes its group sums from the families it has: the pair face's
    /// two families have no outputs, take one empty tile and no group sums (they once divided by
    /// zero and refused every pairless frame before its first section).
    #[test]
    fn a_family_with_no_outputs_takes_no_group_sums() {
        let plain = Shape { alphabet: 11, width: 8, modes: 8, contacts: 16, levels: 2, len: 0, streams: 3, cells: 9, forms: 0, ranks: 0, harmonics: 0, ring_moves: 0, turned: 0, news: 0, pumped: 0, moving: 0, paired: 0, foil: 0, strand_rings: 0, strand_table: 0, heads: 0, section: 0, carried: 0, mutual: 0, passage: 0, packets: 0, split: 0, heading: 0, credit: 0, credit_packets: 0, motive: 0 };
        // One empty tile, four deep over 80 multiprocessors, at most one group a stream: its group
        // sums' extent is `11 · 0 · 3 = 0`.
        assert_eq!(TowerCard::groups(11, 0, 3, 80), 3);
        let paired = Shape { forms: 3, ..plain };
        assert!(TowerCard::partial_extent(&plain, 80) > 0);
        assert!(TowerCard::partial_extent(&paired, 80) >= TowerCard::partial_extent(&plain, 80));
    }
}

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
//! the foil's biases on their own, `tower_pair_biases`), no passage credit, at most four levels,
//! streams of one section length, with
//! or without the pair face (its values resident on the card beside the material, read at each
//! cell's pair of the class before and the class arriving) and with or without the ring face (its
//! ranks carried by every stream beside its modes, each riding its level's mode or its founded pair
//! move at the cell's pair, its pools generated from `b` and `E₀` where the material is read, and
//! its face read through the pair contact with the top face), and with or without a news clock
//! (`NewsClock`, never beside the ring face: each stream carries its open face and phase beside its
//! modes, the forward reads every level's ticks from the arriving class's code under the open face
//! and each level's modes take their step once a tick with the arrival held, and the modes' scan
//! carries the covector back through each tick). Any other is refused before a launch ([`TowerCard::admits`]), never run on a partial
//! law.
//!
//! # The realizations (hardware law)
//!
//! | Kernel | Block | Thread | A thread loops over |
//! |---|---|---|---|
//! | `tower_transpose` | a grid striding one matrix family (`grid.y` the family) | one material entry | — |
//! | `tower_forward` | one stream (the cells in order: each state moves from the one before) | one output of each stage of a cell: the pair face's lift, a push or gate logit, a mode's move, a ring rank's advance and face, a read, a contact, a return part, a class's face (with its pair read and the ring's pair read); 256 threads | the stage's outputs (`o ≡ t`), within each its row's weights (a contact both its drives under the pair law; the return's contacts in `256/W` groups; a ring rank its factors) |
//! | `tower_reverse_top`, `tower_reverse_contacts`, `tower_reverse_dx` | one cell of one stream | one output of each stage (the ring's readout covector, its face's and each rank's read covector among them); 256 threads | the stage's outputs, within each its column's weights |
//! | `tower_reverse_modes` | one stream of one level (under a rotor, exactly one thread a mode, the block exchanging each step's covector through shared memory) | one mode | the stream's cells in reverse order (the scan) |
//! | `tower_reverse_ring` | one stream | one ring rank's scan step, then one face coordinate, then one factor entry | the stream's cells in reverse order, every rank's scan carried together; a coordinate the ranks in their order |
//! | `tower_outer_x32`, `tower_outer_x64` | a tile of 16 rows × 64 columns of one family's covector (the pair face's readout and lift and the ring's readout among them) | four outputs of one column | every stream, its cells in chunks of 32 staged in shared memory |
//! | `tower_ring_factors` | a grid striding the ring's factors | one factor entry | the streams |
//! | `tower_encoding` | one class | one face coordinate | every cell, summing where its class arrived |
//! | `tower_moves` | one level | one mode | the streams |
//! | `tower_pair_biases` (the foil's) | a grid striding each level's two bias covectors | one bias entry | every cell |
use core::ffi::c_void;
use std::time::Instant;

use holonics::hnn::tower::realization::{PassRead, PassRealization, ResidentLaw, Slot};
use holonics::hnn::tower::{ContactLaw, Tower, TowerError, TowerFace, TowerState};

use crate::cuda::{Dim3, Module};
use crate::hnn::card::{Card, CardBuffer};
use crate::hnn::DeviceError;

/// The PTX image of `kernels/tower.cu`, compiled by `build.rs`.
const IMAGE: &[u8] = include_bytes!(concat!(env!("OUT_DIR"), "/tower.ptx"));

/// The kernels' block (`TOWER_THREADS`).
const THREADS: u32 = 256;
/// The levels the law's words carry (`TOWER_MAX_LEVELS`).
const MAX_LEVELS: usize = 4;
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
    level: [LevelWords; MAX_LEVELS],
    /// The news clock (`news = 0` without one): each level's section on `2^(−20)` bits (level 0's
    /// unread) and the clock's period ([`NewsClock`]).
    news: u32,
    pad1: u32,
    sections: [u64; MAX_LEVELS],
    period: u64,
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
    pad: u32,
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
    /// The reaches' slices of `reaches`, in `FrameWords`' order: input, face re, face im, read,
    /// conduct (each `Q·L`), top (`Q`), dz (`Q`), dy, da, dread, gre, gim, dq (each `Q·L`), then
    /// the pair face read, the bottom covector `δx⁰` and the ring's pair read (each `Q`), then the
    /// turn's covector `δs`, then the pump's depth and axis covectors `δκ`, `δp`, then the second
    /// drive's covector `δb` (each `Q·L`).
    reach_offsets: [usize; 20],
}

/// [definition] **The card's realization of the section's pass** (module header).
pub struct TowerCard<'c> {
    card: &'c Card,
    module: Module,
    frame: Option<Frame<'c>>,
    /// The law of the material the frame holds from the last opening read.
    opened: Option<LawWords>,
    /// Whether the frame's material is still the opening read's (a reread uploads its candidate).
    opened_current: bool,
    ends: [Option<Vec<TowerState>>; 2],
    times: TowerCardTimes,
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
}

fn slot_index(slot: Slot) -> usize {
    match slot {
        Slot::Opened => 0,
        Slot::Reread => 1,
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
        Ok(Self { card, module, frame: None, opened: None, opened_current: false, ends: [None, None], times: TowerCardTimes::default(), profile: None })
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
        if law.strands {
            return refuse("the card carries no strands: its forward reads no strand contact and its reverse has no strand gradient");
        }
        if let Some(rotor) = &law.rotor {
            if rotor.moving > d.modes || d.modes > THREADS as usize || rotor.keys.len() != d.levels * d.alphabet * rotor.moving * 4 {
                return refuse("the card steps a rotor's moving modes with a key for each level, class and moving mode, its modes' scan one thread a mode in one block");
            }
        }
        if d.levels == 0 || d.levels > MAX_LEVELS {
            return refuse("the card carries one to four levels");
        }
        if let Some(clock) = &law.news {
            if law.ring.is_some() {
                return refuse("the card carries no ring beside a news clock");
            }
            clock.period(d.levels)?;
            for l in 1..d.levels {
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

    fn law_words(law: &ResidentLaw, streams: usize, cells: usize) -> LawWords {
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
            families: (1 + (7 + usize::from(d.turned) + 2 * usize::from(d.pumped) + usize::from(d.contact != ContactLaw::Rectifying)) * d.levels) as u32,
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
        if let Some(clock) = &law.news {
            words.news = 1;
            words.period = clock.period(d.levels).expect("admitted");
            for l in 1..d.levels {
                words.sections[l] = clock.section(l).expect("admitted");
            }
        }
        for (slot, lv) in words.level.iter_mut().zip(&law.levels) {
            *slot = LevelWords {
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
            };
        }
        words
    }

    /// The matrix families `(offset, rows, cols)` the forward reads transposed.
    fn families(law: &ResidentLaw) -> Vec<u64> {
        let d = &law.declaration;
        let (a, w, n, f) = (d.alphabet as u64, d.width as u64, d.modes as u64, d.contacts as u64);
        let mut out = vec![law.readout as u64, a, w];
        for lv in &law.levels {
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
        }
        out
    }

    fn frame(&mut self, shape: Shape) -> std::result::Result<(), DeviceError> {
        if self.frame.as_ref().is_some_and(|f| f.shape == shape) {
            return Ok(());
        }
        self.frame = None;
        let card = self.card;
        let Shape { alphabet: a, width: w, modes: n, contacts: f, levels: l, len, streams: s, cells: t, forms: k, ranks: r, ring_moves: m, turned, news, pumped, moving, paired, foil, .. } = shape;
        let (k2, kp) = shape.ring_reads();
        let ringed = usize::from(r > 0);
        let q = s * t;
        let ql = q * l;
        let mut reach_offsets = [0usize; 20];
        let extents = [ql, ql, ql, ql, ql, q, q, ql, ql, ql, ql, ql, ql, q, q, q, ql * turned, ql * pumped, ql * pumped, ql * paired];
        let mut at = 0;
        for (slot, extent) in reach_offsets.iter_mut().zip(extents) {
            *slot = at;
            at += extent;
        }
        self.frame = Some(Frame {
            shape,
            theta: card.alloc(len)?,
            theta_t: card.alloc(len)?,
            families: card.alloc(3 * (1 + (7 + turned + 2 * pumped + paired) * l))?,
            gates: card.alloc(l * n * 4)?,
            roots: card.alloc(64)?,
            classes: card.alloc(s * (t + 1))?,
            targets: card.alloc(q)?,
            opening: card.alloc(s * l * n * 2)?,
            ends: card.alloc(s * l * n * 2)?,
            faces: card.alloc(q * 3)?,
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
        [16 * g * w, 16 * 32, 8 * l * 2 * n, 8 * (3 + shape.turned + 2 * shape.pumped) * n, 8 * 2 * n, 8 * 2 * w, 8 * w, 8 * a, 8 * a, 8 * 32, 4 * w, 4 * w, 4 * w, 4 * f, 4 * f, 4 * k, 16 * 2 * r, 4 * r, 8 * 2 * n * ringed, 4 * k2, 4 * w * ringed, 4 * kp, 8 * 2 * shape.moving].iter().map(|&o| carve(o)).sum()
    }

    fn top_shared(shape: &Shape) -> usize {
        let w = shape.width;
        let (k2, kp) = shape.ring_reads();
        let ringed = usize::from(shape.ranks > 0);
        let g = (THREADS as usize / w).max(1);
        [16 * g * w, 8 * shape.alphabet, 8 * 32, 16 * 32 * ringed, 8 * w, 8 * kp, 8 * k2, 8 * w * ringed].iter().map(|&o| carve(o)).sum()
    }

    fn ring_shared(shape: &Shape) -> usize {
        let r = shape.ranks;
        [16 * 2 * r, 16 * 5 * r, 16 * 4 * r, 8 * 2 * shape.modes, 4 * r].iter().map(|&o| carve(o)).sum()
    }

    fn contacts_shared(shape: &Shape) -> usize {
        let (w, f) = (shape.width, shape.contacts);
        let g = (THREADS as usize / w).max(1);
        [16 * g * w, 16 * 32, 8 * w, 8 * f, 8 * f * shape.paired, 8 * w, 8 * w, 8 * 32].iter().map(|&o| carve(o)).sum()
    }

    fn dx_shared(shape: &Shape) -> usize {
        let families = 3 + shape.turned + 2 * shape.pumped;
        [8 * families * shape.modes, 8 * families * shape.width, 8 * 32].iter().map(|&o| carve(o)).sum()
    }

    /// The forward of every stream (`tower_forward`), keeping its temporaries when opened.
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
        if opening.len() != streams
            || opening.iter().any(|o| o.credit.is_some() || o.ring.len() != ranks || o.hands.len() != ranks || !o.strands.is_empty() || o.reversed || o.modes.len() != d.levels || o.modes.iter().any(|m| m.len() != d.modes) || o.previous > d.alphabet)
        {
            return Err(TowerError::Refused("the card opens on uncredited states of the declared bank, each ring rank with its value and hand, and no strand residue"));
        }
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
        let shape = Shape { alphabet: d.alphabet, width: d.width, modes: d.modes, contacts: d.contacts, levels: d.levels, len: law.len, streams, cells, forms, ranks, harmonics, ring_moves, turned: usize::from(d.turned), news: usize::from(law.news.is_some()), pumped: usize::from(d.pumped), moving: law.rotor.as_ref().map_or(0, |r| r.moving), paired: usize::from(d.contact != ContactLaw::Rectifying), foil: usize::from(d.contact == ContactLaw::PairLinear) };
        self.frame(shape).map_err(device)?;
        let words = Self::law_words(&law, streams, cells);
        let keep = slot == Slot::Opened;
        {
            let frame = self.frame.as_ref().expect("the frame was just sized");
            let card = self.card;
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
            card.zero_octets(&frame.status, 0, 4 * streams).map_err(device)?;
            if keep {
                card.zero_octets(&frame.swell, 0, 8 * 4 * d.levels).map_err(device)?;
            }
            let fw = Self::frame_words(frame);
            let blocks = (law.len as u32).div_ceil(THREADS).clamp(1, 1024);
            self.law_launch("tower_transpose", Dim3 { x: blocks, y: words.families, z: 1 }, THREADS, 0, &words, &fw, None).map_err(device)?;
            self.law_launch("tower_forward", Dim3::x(streams as u32), THREADS, Self::forward_shared(&shape) as u32, &words, &fw, Some(keep as u32)).map_err(device)?;
        }
        self.status()?;
        let frame = self.frame.as_ref().expect("the frame was just sized");
        let faces = self.card.fetch(&frame.faces).map_err(device)?;
        let ends = self.card.fetch(&frame.ends).map_err(device)?;
        let (ring_ends, hands_ends) = if ranks > 0 { (self.card.fetch(&frame.ring_ends).map_err(device)?, self.card.fetch(&frame.hands_ends).map_err(device)?) } else { (Vec::new(), Vec::new()) };
        let swell = if keep { self.card.fetch(&frame.swell).map_err(device)? } else { Vec::new() };
        let news_ends = if law.news.is_some() { self.card.fetch(&frame.news_ends).map_err(device)? } else { Vec::new() };
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
                if ranks > 0 {
                    state.ring = (0..ranks).map(|r| (ring_ends[(s * ranks + r) * 2], ring_ends[(s * ranks + r) * 2 + 1])).collect();
                    state.hands = (0..ranks).map(|r| hands_ends[s * ranks + r] != 0).collect();
                }
                if !news_ends.is_empty() {
                    let end = &news_ends[s * (d.alphabet + 4)..(s + 1) * (d.alphabet + 4)];
                    state.open = (end[0] != 0).then(|| TowerFace { masses: end[4..].iter().map(|&m| u128::from(m)).collect(), total: end[1] as u128 | (end[2] as u128) << 64 });
                    state.news = end[3];
                }
                state
            })
            .collect();
        self.ends[slot_index(slot)] = Some(ends);
        if keep {
            self.opened = Some(words);
            self.opened_current = true;
        } else {
            self.opened_current = false;
        }
        let swell = swell.chunks_exact(4).map(|c| [c[0], c[1], c[2], c[3]]).collect();
        Ok(PassRead { faces, swell })
    }

    /// The streams' covector summed (`tower_reverse_*`, `tower_outer_*`, `tower_encoding`,
    /// `tower_moves`), from the opening read's temporaries.
    fn read_reverse(&mut self) -> Result<Vec<i128>> {
        let words = self.opened.filter(|_| self.opened_current).ok_or(TowerError::Refused("a card reverse reads the section's opening forward, its material still resident"))?;
        let frame = self.frame.as_ref().ok_or(TowerError::Refused("a card pass needs its frame"))?;
        let shape = frame.shape;
        let fw = Self::frame_words(frame);
        let (s, t, l) = (shape.streams, shape.cells, shape.levels);
        let q = (s * t) as u32;
        let card = self.card;
        card.zero_octets(&frame.status, 0, 4 * s).map_err(device)?;
        card.zero_octets(&frame.gradient, 0, 16 * shape.len).map_err(device)?;
        self.law_launch("tower_reverse_top", Dim3::x(q), THREADS, Self::top_shared(&shape) as u32, &words, &fw, None).map_err(device)?;
        let mode_threads = (shape.modes as u32).next_multiple_of(32).min(THREADS);
        // Under a rotor the modes' scan exchanges each step's covector between the modes of a ring
        // (`Rotor::back`), so each mode holds one thread of the block and the block holds no other.
        let (scan_threads, scan_shared) = if shape.moving > 0 { (shape.modes as u32, 32 * shape.modes as u32) } else { (mode_threads, 0) };
        for level in (0..l).rev() {
            self.law_launch("tower_reverse_contacts", Dim3::x(q), THREADS, Self::contacts_shared(&shape) as u32, &words, &fw, Some(level as u32)).map_err(device)?;
            // The ring's reverse reads the level's read covector and returns its own to it and to
            // the mode's move, before the modes' scan.
            if shape.ranks > 0 && level == words.ring_level as usize {
                self.law_launch("tower_reverse_ring", Dim3::x(s as u32), THREADS, Self::ring_shared(&shape) as u32, &words, &fw, None).map_err(device)?;
            }
            self.law_launch("tower_reverse_modes", Dim3::x(s as u32), scan_threads, scan_shared, &words, &fw, Some(level as u32)).map_err(device)?;
            self.law_launch("tower_reverse_dx", Dim3::x(q), THREADS, Self::dx_shared(&shape) as u32, &words, &fw, Some(level as u32)).map_err(device)?;
        }
        for outer in self.outer_families(&words, &fw) {
            self.launch_outer(&outer.0, outer.1).map_err(device)?;
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
        self.status()?;
        let frame = self.frame.as_ref().expect("checked above");
        self.card.fetch(&frame.gradient).map_err(device)
    }

    /// Every family's outer sum: `(words, whether x is 64-bit)`.
    fn outer_families(&self, law: &LawWords, fw: &FrameWords) -> Vec<(OuterWords, bool)> {
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
            pad: 0,
            partial: 0,
        };
        let mut out = vec![(family(fw.dz, a, fw.top, w, fw.r_dz, fw.r_top, 1, a, w, false, gradient(law.readout), Some(gradient(law.readout_bias))), false)];
        for level in 0..l as usize {
            let lv = &law.level[level];
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
            out.push((family(at64(fw.gre, lu * n), l * n, at32(fw.input, lu * w), l * w, at64(fw.r_gre, lu), at64(fw.r_input, lu), l, n, w, false, gradient(lv.push_re), None), false));
            out.push((family(at64(fw.gim, lu * n), l * n, at32(fw.input, lu * w), l * w, at64(fw.r_gim, lu), at64(fw.r_input, lu), l, n, w, false, gradient(lv.push_im), None), false));
            out.push((family(at64(fw.dq, lu * n), l * n, at32(fw.input, lu * w), l * w, at64(fw.r_dq, lu), at64(fw.r_input, lu), l, n, w, false, gradient(lv.gate), Some(gradient(lv.gate_bias))), false));
            if law.turned != 0 {
                out.push((family(at64(fw.ds, lu * n), l * n, at32(fw.input, lu * w), l * w, at64(fw.r_ds, lu), at64(fw.r_input, lu), l, n, w, false, gradient(lv.turn), Some(gradient(lv.turn_bias))), false));
            }
            if law.pumped != 0 {
                out.push((family(at64(fw.dk, lu * n), l * n, at32(fw.input, lu * w), l * w, at64(fw.r_dk, lu), at64(fw.r_input, lu), l, n, w, false, gradient(lv.pump), Some(gradient(lv.pump_bias))), false));
                out.push((family(at64(fw.dp, lu * n), l * n, at32(fw.input, lu * w), l * w, at64(fw.r_dp, lu), at64(fw.r_input, lu), l, n, w, false, gradient(lv.pump_axis), Some(gradient(lv.pump_axis_bias))), false));
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

    /// The group sums' extent: the widest family's outputs times its groups.
    fn partial_extent(shape: &Shape, multiprocessors: u32) -> usize {
        let (a, w, n, f, k) = (shape.alphabet as u32, shape.width as u32, shape.modes as u32, shape.contacts as u32, shape.forms as u32);
        let kp = shape.ring_reads().1 as u32;
        [(a, w + 1), (w, f + 1), (f, w + 1), (w, n), (n, w + 1), (a, k), (w, k), (a, kp)]
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
                format!(
                    "card {} ({} multiprocessors): forward {} blocks (one a stream, its {} cells in order) x {THREADS} threads; reverse {q} blocks (one a cell) x {THREADS} threads, the modes' scan {} blocks x {} threads (one a mode); outer sums in tiles of {OUTER_ROWS}x{OUTER_COLS} outputs, 4 a thread",
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
    matches!(entry, "tower_forward" | "tower_reverse_contacts" | "tower_reverse_modes" | "tower_reverse_dx")
}

impl PassRealization for TowerCard<'_> {
    fn realization(&self) -> String {
        self.report()
    }

    fn admit(&self, tower: &Tower) -> Result<()> {
        Self::admits(&tower.resident_law()?)
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
        let g = self.read_reverse()?;
        self.times.reverses += 1;
        self.times.reverse_ns += started.elapsed().as_nanos();
        Ok(g)
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

    fn carry(&mut self, _tower: &Tower, states: &mut [TowerState], _opening: &[TowerState], slot: Slot) -> Result<()> {
        let ends = self.ends[slot_index(slot)].take().ok_or(TowerError::Refused("a carry reads a kept forward"))?;
        if ends.len() != states.len() {
            return Err(TowerError::Refused("a carry continues every stream"));
        }
        for (state, end) in states.iter_mut().zip(ends) {
            *state = end;
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
        let plain = Shape { alphabet: 11, width: 8, modes: 8, contacts: 16, levels: 2, len: 0, streams: 3, cells: 9, forms: 0, ranks: 0, harmonics: 0, ring_moves: 0, turned: 0, news: 0, pumped: 0, moving: 0, paired: 0, foil: 0 };
        // One empty tile, four deep over 80 multiprocessors, at most one group a stream: its group
        // sums' extent is `11 · 0 · 3 = 0`.
        assert_eq!(TowerCard::groups(11, 0, 3, 80), 3);
        let paired = Shape { forms: 3, ..plain };
        assert!(TowerCard::partial_extent(&plain, 80) > 0);
        assert!(TowerCard::partial_extent(&paired, 80) >= TowerCard::partial_extent(&plain, 80));
    }
}

//! **The field's card realization** (`holonics::hnn::tower::field`, #404, #407; records
//! `2026-11-01_THE_PROBLEM_IS_ONE_FIELD_EVERY_SITE_READS_EVERY_OTHER_AND_THE_ANSWER_IS_REFINED_NOT_SPOKEN`,
//! §7, and `2026-11-01_THE_FIELD_DISPERSES_A_SITE_MEETS_ITS_RESONANCE_CLASS_AT_ITS_FALLOFF_AND_THE_ANSWER_LOCKS_UNDER_THE_PUMP`,
//! §6).
//!
//! [definition; agent-inferred, November 1] `CardField` implements [`FieldRealization`]: a section's
//! regions read forward through the `K` ticks of the one constitution and returned exactly, and the
//! certificate's rereads, bit for bit the host's [`holonics::hnn::tower::field::HostField`]
//! (`kernels/field.cu`). The work is laid out as the field is: a site is its global index in a
//! batch of regions, each region keeping its own length (no region is padded to another's), a
//! contact row is a head and a receiving site (one warp a row, its lanes over the site's support:
//! its near field and its resonance class, listed on the card each tick by a stable counting sort),
//! and a region's weights `e_ij` are its own block of the weight store, written and read only on the
//! support. The material, the regions' classes, resolutions and carried mixtures cross to the card;
//! the faces (or the logits) of the unresolved sites and the covector cross back. Every tick's
//! carriers stay on the card through the reverse.
//!
//! [agent-inferred, November 1] **Memory: the weights are kept at their dense address, the regions
//! batched by the card's measured memory.** A region of `S` sites reserves `H·S²` weights on `u64` a
//! kept tick, the address `[i][j]` a column's return reads `e_ij` at without an index; only the
//! support's entries are written and read, so the time follows the pairs met, and the reservation
//! is the most a region's classes can ask (every site of one class). The reverse reads them twice
//! (the values' and the contact's returns), so they are kept rather than recomputed; the contact's
//! return `δs_ij` is held for one head at a time (`S²` on 128 bits). A section's
//! regions are read in batches whose every allocation (the weights, the contact's return and each
//! site's carriers) fits the batch budget, the card's free memory at the open less a margin for the
//! driver, never past the 12 GB the runs keep to.
//! Batches sum their covectors on the card (integer sums: any batching gives the same bits).

use core::ffi::c_void;
use std::time::Instant;

use holonics::hnn::tower::field::{band_bits, landmarks_of, BlankClocks, CarryGates, Field, FieldDeclaration, FieldRead, FieldRealization, HeldRows, NearOffsets, RealizationCounters, RowCurrent, Region, Scale, TickRead, NEAR, SHARE_BITS, STATE_BITS};
use holonics::hnn::tower::field::{level_cut, level_section, PACE_BITS};
use holonics::hnn::tower::{TowerError, TowerFace, MATERIAL_BITS};

use crate::cuda::{Dim3, Module};
use crate::hnn::card::{Card, CardBuffer};
use crate::hnn::DeviceError;

const IMAGE: &[u8] = include_bytes!(concat!(env!("OUT_DIR"), "/field.ptx"));
const THREADS: u32 = 256;
/// The dynamic shared memory a tiled affine map may take in a block, the default 48 KiB.
const AFFINE_SHARED: usize = 48 * 1024;


/// [agent-inferred, November 12; the triad record §4] The return of two blocks' tiling (`affine_two_tiled` in `kernels/field.cu`): a block passes
/// `256/rows` sites, holding `W` at the stride `cols + 1`, `W₂` at the stride `cols₂ + 1` and the bias in 32-bit words, each site's joint carrier bound
/// on 128 bits, then a pass's site rows of both blocks on 64 bits, where they fit a block's shared memory (the main line's `D = 64`, `f = 128`,
/// `J = 16`: 46,912 of 49,152 octets).
fn affine_two_tiling(rows: usize, cols: usize, cols2: usize) -> Option<(usize, usize)> {
    let per = (THREADS as usize).checked_div(rows).filter(|&p| p > 0)?;
    let shared = ((rows * (cols + 1) + rows * (cols2 + 1) + rows) * 4).div_ceil(16) * 16 + per * 16 + per * (cols + cols2) * 8;
    (shared <= AFFINE_SHARED).then_some((per, shared))
}
/// The widest span the contact's lanes carry (a lane an entry of the span).
const CONTACT_SPAN: u32 = 32;
/// The series row's carrier, in limbs of 64 bits: at least five (a term's product with a wide value), at
/// most twenty (`field_contact_l5` … `field_contact_l20`, 1,280 bits).
const MIN_LIMBS: usize = 5;
const MAX_LIMBS: usize = 20;
/// The most modes a head's rows carry on the card (`MAXN` in `kernels/field.cu`).
const MAX_MODES: usize = 16;
/// Warps a contact or a reverse block carries (`CONTACT_ROWS`, `REV_ROWS` in `kernels/field.cu`).
const CONTACT_ROWS: u64 = 4;
const REV_ROWS: u64 = 4;
/// The threads a moment scan's block carries (a power of two, `kernels/field_moment.cuh`).
const MOMENT_BLOCK: u32 = 256;
/// The most crowds a receiver hears, one lane each (`MAX_CROWD_SLOTS` in `kernels/field.cu`).
const MAX_CROWD_SLOTS: usize = 32;
/// The sites a thread of an encoding's covector segment takes (the segments' tile).
const OUTER_TILE: u64 = 64;
/// [realization; P61 item 4e] The sites an outer sum's block walks (`OUTER_WALK` in `kernels/field.cu`).
const OUTER_WALK: u64 = 512;
/// [realization; P61 item 4f] The outer passes' slots for their largest words, zeroed again each time they are spent.
const OUTER_SLOTS: usize = 4096;
/// The device octets the runs keep to (the board's, the desktop included).
const BOARD_CEILING: u64 = 12 << 30;
/// Octets kept free beside a batch's counted allocations for the driver, the material and the
/// allocator's grain.
const MARGIN: u64 = 1 << 30;

type Result<T> = std::result::Result<T, TowerError>;

fn device(error: DeviceError) -> TowerError {
    TowerError::Realization(format!("the card: {error}"))
}

/// The batch's words (`FieldWords` in `kernels/field.cu`, field for field).
#[repr(C)]
#[derive(Clone, Copy, Default)]
struct Words {
    d: u32,
    h: u32,
    n: u32,
    still: u32,
    f: u32,
    a: u32,
    frames: u32,
    lanes: u32,
    beta: i32,
    ctrits: u32,
    nclasses: u32,
    dsbits: u32,
    m: u32,
    m2: u32,
    span: u32,
    digits: u32,
    t: u32,
    r: u32,
    slots: u32,
    band: u32,
    pairs: u64,
    ln2_lo: u64,
    ln2_hi: u64,
    theta: u64,
    enc: u64,
    enc_before: u64,
    enc_after: u64,
    q: u64,
    q_bias: u64,
    v: u64,
    v_bias: u64,
    out: u64,
    out_bias: u64,
    wa: u64,
    a_bias: u64,
    wb: u64,
    b_bias: u64,
    w: u64,
    w_bias: u64,
    read: u64,
    read_bias: u64,
    rq: u64,
    rv: u64,
    rout: u64,
    ra: u64,
    rb: u64,
    rw: u64,
    rread: u64,
    phasor: u64,
    ring_off: u64,
    ring_n: u64,
    decay: u64,
    dreach: u64,
    roots: u64,
    site_region: u64,
    site_pos: u64,
    region_off: u64,
    region_eoff: u64,
    classes: u64,
    unresolved: u64,
    definite: u64,
    // [E] Each site's row computed where its region's room is cut to its windows (`Region::window`); none where no region of
    // the batch is cut.
    computed: u64,
    // Each site whose blank face a clock reads: silent, and at or before its region's silent stretch's first place (every
    // silent site under the per-blank clock). The blank clock's face kernels read these sites alone.
    blank_read: u64,
    mix_off: u64,
    mix_class: u64,
    mix_share: u64,
    status: u64,
    met: u64,
    x: u64,
    qkv: u64,
    qf: u64,
    vf: u64,
    cls: u64,
    class_off: u64,
    members: u64,
    pn: u64,
    pcls: u64,
    poff: u64,
    pmem: u64,
    e: u64,
    e_prev: u64,
    y: u64,
    pa: u64,
    pb: u64,
    pc: u64,
    bits: u64,
    face: u64,
    amin: u64,
    sw: u64,
    sv: u64,
    sc: u64,
    ce: u64,
    cv: u64,
    cw: u64,
    moment: u64,
    echo_has: u64,
    echo_b: u64,
    echo_logits: u64,
    trips: u64,
    qf32: u64,
    decay_t: u64,
    dpb: u64,
    dlist: u64,
    dstart: u64,
    olist: u64,
    ostart: u64,
    temper_at: u64,
    fine_roots: u64,
    gcov: u64,
    sb: u64,
    pr: u64,
    pq: u64,
    pq32: u64,
    pscale: u64,
    dp: u64,
    probe: u64,
    probe_bias: u64,
    rprobe: u64,
    // The turned heads' own clocks (§16, `FieldWords`' tail, field for field).
    paced: u32,
    pace_at: u64,
    pi_lo: u64,
    pi_hi: u64,
    kappa: u64,
    tau: u64,
    sigma: u64,
    plain: u64,
    pframe: u64,
    gtau: u64,
    gsig: u64,
    cds: u64,
    dsshare: u64,
    // [§16.44] A tick's blanks' rates, and the face they were read from (zero where the tick reads the pass's clocks).
    blank_rate: u64,
    blank_masses: u64,
    blank_totals: u64,
    // [measurement] Every silent place runs its own rate past the last arrival too (the host's `Field::per_blank_clock`).
    per_blank: u64,
    // The depth rings' count (`FieldDeclaration::depth`).
    depth: u64,
    // [the unified-theory reading of November 6, 10:31] Past the last arrival a silent place runs at the bare rate (the host's
    // `Field::bare_stretch`).
    bare_stretch: u64,
    // [definition; theory, November 11 17:25 and November 12 (G98)] The carry circles (`FieldDeclaration::carry`): their count `C`, their charts' and
    // biases' offsets in the material (`FieldLayout::carry`, `carry_bias`) and the charts' reach, and (set per tick) the charts' reads `q`, `ℓ` `[t][2C]`,
    // the gate `γ` `[t][2C]`, the scan's operand `[t][2C]` and the drive coupled through the leak `[t][2C]`.
    carry: u64,
    wg: u64,
    wgb: u64,
    rg: u64,
    pg: u64,
    pgam: u64,
    pqm: u64,
    pkb: u64,
    // [theory, November 11 04:14, step S] The skin's site addresses `[p][l][t]` three words each (`FieldWords::saddr`), the clock's own beside `sigma`.
    saddr: u64,
    // [definition; theory, November 12; the triad record (`2026-11-12_THE_LAW_ACROSS_A_PLACE_IS_HELD_BY_A_PUMPED_CONTACT…`) §3 and §4] The triads
    // (`FieldDeclaration::triads`): their count `J`, the chart's and its biases' offsets in the material (`FieldLayout::triad`, `triad_bias`) and the
    // chart's reach, the return's offset (`FieldLayout::w_triad`) and reach, and (set per tick) the chart's read `abg` `[t][6J]` and the products `p`
    // and `c^T` `[t][2J]`. Zero where `J = 0`, where no kernel reads them.
    triads: u64,
    wt: u64,
    wtb: u64,
    rt: u64,
    wtr: u64,
    rwt: u64,
    pabg: u64,
    ptp: u64,
    pct: u64,
    // [theory, November 12, P50 step 1] The clock's skins (`FieldWords::skin`, `cskin`): a paced head's skin of each support pair `[p][pair][l]` and
    // of each crowd edge `[p][t][slot][l]`, 32 bits each, formed once a clock by `field_skin_fill`. Zero where the batch keeps none.
    skin: u64,
    cskin: u64,
    // [theory, November 12, P51] The skins' support stride: each region's prefix of `S_r K_r` (`FieldWords::region_soff`) and their sum `E2`.
    region_soff: u64,
    skin_entries: u64,
    // [theory, November 12, P50 step 2] A clock's near phases and skins (`FieldWords::mphase`, `mskin`), the moment modes' map and their count.
    mphase: u64,
    mskin: u64,
    mcmap: u64,
    tm: u64,
    // [definition; agent-inferred, November 14, the ring record §4] The field that reads twice (`FieldWords::mark_at`, `mark_share`): the strengths'
    // offset in the material, and on the second read each silent site's shares of the face the first read gave it `[t][A]` (zero elsewhere and on a
    // first read).
    mark_at: u64,
    mark_share: u64,
}

/// The moment kernels' words (`MomentWords` in `kernels/field_moment.cuh`, field for field): the batch's
/// regions and the one ring slot a launch reads.
#[repr(C)]
#[derive(Clone, Copy, Default)]
struct MomentWords {
    r: u32,
    t: u32,
    region_off: u64,
    site_region: u64,
    site_pos: u64,
    ring: u64,
    n: u64,
    ring_len: u64,
    decay: u64,
    dreach: u64,
    ok: u64,
    status: u64,
}

/// A kernel argument: the address of a value the launch copies.
/// The moment's chart into the face (§16.22, [`holonics::hnn::tower::field::FieldLayout::moment_face`]): its offset in
/// the material, its bias's, and its reach `max |C|` (the affine's carrier bound).
fn moment_face(field: &Field) -> (u64, u64, u64) {
    let (l, d) = (field.layout(), field.declaration);
    let len = d.width * 2 * d.complex();
    let reach = field.theta[l.moment_face..l.moment_face + len].iter().map(|v| v.unsigned_abs() as u64).max().unwrap_or(0);
    (l.moment_face as u64, l.moment_face_bias as u64, reach)
}

fn arg<T>(v: &mut T) -> *mut c_void {
    (v as *mut T).cast()
}

/// [definition; agent-inferred, November 1] **The crowds a receiver of a region of `sites` hears**
/// (the dispersing field's §14.10, the host's `crowd_ranges`): two an octave `level ≥ 2` with
/// `2^level < sites`, one on each side.
pub fn crowd_slots(sites: usize) -> usize {
    (2..usize::BITS).take_while(|&level| (1usize << level) < sites).count() * 2
}

/// [definition; agent-inferred, November 1] **The limbs a launch's rows need** (§14.11, §15.2: width is
/// dynamic, never arbitrary): a row's carrier is as wide as the exponents its rows hold, `62` bits of face,
/// `WEIGHT_BITS` of weight, `⌈log₂ reach⌉` of a crowd's count, the spread of whole bits `a − a₀` the widest
/// row of the launch holds, the bits of the terms a row sums, `64 + ⌈log₂ reach⌉` of a value summed over the
/// reach and the sign: [`Field::row_bits`] (its gain read from the largest temperature's octave the material
/// holds, [`Field::row_gain`], §15.10, §16.12) with its spread bound (`4n 2^c + 1 + ⌊log₂ reach⌋ + 2`) replaced by
/// the spread read. A spread
/// past that bound is refused (the bound is where a row ends), and so is a carrier past the twenty limbs the
/// card keeps.
pub fn row_limbs(field: &Field, spread: u64) -> Result<usize> {
    let d = &field.declaration;
    let bound = field.row_gain()? + (usize::BITS - 1 - d.reach.leading_zeros()) as u64 + 2;
    if spread > bound {
        return Err(TowerError::Refused("a contact row holds exponents past the declaration's bound (`row_bits`)"));
    }
    let need = field.row_bits()? as u64 - bound + spread;
    let limbs = (need.div_ceil(64) as usize).max(MIN_LIMBS);
    if limbs > MAX_LIMBS {
        return Err(TowerError::Refused("a contact row needs a carrier past the card's twenty limbs (1,280 bits)"));
    }
    Ok(limbs)
}

/// The card's time on the field: forwards (reads), returns, their wall time and the site pairs met.
#[derive(Clone, Copy, Debug, Default)]
pub struct FieldTimes {
    pub reads: u64,
    pub read_ns: u128,
    pub returns: u64,
    pub return_ns: u128,
    /// The site pairs the contact met, `Σ |S_i^h|` over every row, head and tick of every read
    /// (counted on the card).
    pub pairs: u128,
    pub batches: u64,
    /// The largest batch's counted allocations (weights, contact return and per-site carriers), in
    /// octets.
    pub peak_store: u64,
    /// The landmark reads ([`FieldRealization::read_landmarks`]) and their wall time, apart from the
    /// reads and pairs above.
    pub landmarks: u64,
    pub landmark_ns: u128,
    /// [measurement; theory, November 12, P50 step 1 and P51] The clock's skins ([`skin_octets`]): the largest batch's store, the octets a reserved
    /// support entry and a site (zero where no head is paced), the support entries `E2` and the dense pairs summed over the batches, and the largest
    /// batch's `E2` beside its dense pairs.
    pub skin_store: u64,
    pub skin_entry_octets: u64,
    pub skin_site_octets: u64,
    pub skin_entries: u128,
    pub skin_dense_pairs: u128,
    pub skin_peak_entries: u64,
    pub skin_peak_pairs: u64,
    /// [measurement; theory, November 12, P50 step 2] A clock's near phases and skins: octets a site.
    pub clock_site_octets: u64,
    /// The batches' cut: four fifths of the batch budget less the exponential's face, the last run's.
    pub batch_cut: u64,
}

/// [theory, November 12, P50 step 1 and P51] The clock's skin store of a region of `sites` sites, `definite` of them definite
/// ([`CardField::skin_fill`]): 32 bits a paced head, support entry and mode over the row's support stride `K = NEAR_SLOTS + definite` (atlas
/// `tower.field-support-stride`: every row's support fits it), and a paced head, site, crowd slot and mode. Returns (the region's octets, octets a
/// reserved entry, octets a site's crowd edges, octets a site's near phases and skins).
pub fn skin_octets(d: &FieldDeclaration, sites: usize, definite: usize) -> (u64, u64, u64, u64) {
    let per = 4 * d.paced_heads() as u64 * d.modes as u64;
    let (entry, site) = (per, per * crowd_slots(d.reach) as u64);
    let stride = (2 * (NEAR - 1) + definite) as u64;
    // [theory, November 12, P50 step 2] A clock's near phases (two words) and skins (one), a moment mode and near offset of each site.
    let moment = if d.paced_heads() > 0 { 12 * (d.moment_modes() * CLOCK_NEAR) as u64 } else { 0 };
    (entry * sites as u64 * stride + (site + moment) * sites as u64, entry, site, moment)
}

/// [measurement; theory, November 12, P54 item 1] The ruler build's arrays whose words' bits it reads, by clock (`field_yard_bits_*`).
/// [measurement; theory, November 13, P56 item 1] After them, the share `e` by head and by the receiver's kind (definite, open), heads 0 to 3.
pub const BITS_NAMES: [&str; 30] = [
    "e_score", "e_share", "sb", "ds", "dpb", "skin_l0", "skin_l1", "skin_l2", "skin_l3", "skin_l4", "skin_l5", "skin_l6", "skin_l7", "vf", "qf", "pq", "qf32", "pq32", "ce", "sc", "sw", "sv",
    "e_share_h0_definite", "e_share_h0_open", "e_share_h1_definite", "e_share_h1_open", "e_share_h2_definite", "e_share_h2_open", "e_share_h3_definite", "e_share_h3_open",
];
pub const BITS_TICKS: usize = 4;
pub const BITS_BINS: usize = 129;

/// The near offsets a moment mode reads about a site, `2(NEAR − 1)` (the clock's store, `near_slot`).
const CLOCK_NEAR: usize = 2 * (NEAR - 1);

/// A region's definite sites (the stage's `definite`: known and carrying no face, or locked).
fn definite_sites(region: &Region) -> usize {
    (0..region.classes.len()).filter(|&t| (!region.unresolved[t] && region.faces.get(t).and_then(Option::as_ref).is_none()) || region.locked.get(t).copied().unwrap_or(false)).count()
}

/// One tick's carriers on the card.
/// A field's uploaded run buffers ([`CardField::upload`]), held while its words are read.
struct Upload<'c> {
    _pack: Pooled<'c, u8>,
    _face: Option<Pooled<'c, u64>>,
    met: Pooled<'c, u64>,
}

/// The fine sites a batch's words stage.
fn tb_fine_sites(words: &Words) -> usize {
    words.t as usize
}

/// Point the words at a tick's temporaries.
/// [definition; §16.44] A tick's own clocks on the card (the host's `TickClock`): its rates, clocks, variations, plainness
/// and frames, the moments read on them, and the blanks' rates with the face they were read from.
struct CardClock<'c> {
    kappa: Pooled<'c, i64>,
    tau: Pooled<'c, i64>,
    sigma: Pooled<'c, i64>,
    saddr: Pooled<'c, i64>,
    plain: Pooled<'c, u8>,
    pframe: Pooled<'c, i64>,
    moment: Pooled<'c, i64>,
    rates: Pooled<'c, i64>,
    masses: Pooled<'c, u64>,
    totals: Pooled<'c, i128>,
    /// The blanks' reads the return runs through: the chart and its scales, and the lift.
    fread: Pooled<'c, i32>,
    fscale: Pooled<'c, i128>,
    lift: Pooled<'c, i64>,
}

/// The words a tick reads its clocks through (§16.44): its own, or the pass's `base` (`kappa`, `tau`, `sigma`, `plain`,
/// `pframe`, `moment`), with no blank rates.
fn set_clock(w: &mut Words, clock: Option<&CardClock>, base: [u64; 7]) {
    match clock {
        Some(c) => {
            (w.kappa, w.tau, w.sigma, w.plain, w.pframe, w.moment) = (c.kappa.device_ptr(), c.tau.device_ptr(), c.sigma.device_ptr(), c.plain.device_ptr(), c.pframe.device_ptr(), c.moment.device_ptr());
            w.saddr = c.saddr.device_ptr();
            (w.blank_rate, w.blank_masses, w.blank_totals) = (c.rates.device_ptr(), c.masses.device_ptr(), c.totals.device_ptr());
        }
        None => {
            [w.kappa, w.tau, w.sigma, w.plain, w.pframe, w.moment, w.saddr] = base;
            (w.blank_rate, w.blank_masses, w.blank_totals) = (0, 0, 0);
        }
    }
}

fn set_tick(w: &mut Words, tick: &Tick, returning: bool) {
    w.qkv = tick.qkv.device_ptr();
    w.qf = tick.qf.device_ptr();
    w.qf32 = tick.qf32.device_ptr();
    w.pq = tick.pq.device_ptr();
    w.pq32 = tick.pq32.device_ptr();
    w.pscale = tick.pscale.device_ptr();
    w.vf = tick.vf.device_ptr();
    w.cls = tick.cls.device_ptr();
    w.class_off = tick.class_off.device_ptr();
    w.members = tick.members.device_ptr();
    w.pn = tick.pn.device_ptr();
    w.pcls = tick.pcls.device_ptr();
    w.poff = tick.poff.device_ptr();
    w.pmem = tick.pmem.device_ptr();
    w.e = tick.e.device_ptr();
    w.sb = if returning { tick.sb.device_ptr() } else { 0 };
    w.amin = tick.amin.device_ptr();
    w.sw = tick.sw.device_ptr();
    w.sv = tick.sv.device_ptr();
    w.sc = tick.sc.device_ptr();
    w.ce = tick.ce.device_ptr();
    w.y = tick.y.device_ptr();
    w.pa = tick.pa.device_ptr();
    w.pg = tick.pg.device_ptr();
    w.pgam = tick.pgam.device_ptr();
    w.pqm = tick.pqm.device_ptr();
    w.pkb = tick.pkb.device_ptr();
    w.pb = tick.pb.device_ptr();
    w.pc = tick.pc.device_ptr();
    set_triads(w, tick);
    w.bits = tick.bits.device_ptr();
}

/// [theory, November 12; the triad record §4] Point the words at a tick's triads' carriers (`abg`, `p`, `c^T`), none where the field has no triads.
fn set_triads(w: &mut Words, tick: &Tick) {
    (w.pabg, w.ptp, w.pct) = (held_at(&tick.pabg), held_at(&tick.ptp), held_at(&tick.pct));
}

/// A held buffer's address, zero where none is held.
fn held_at(b: &Option<Pooled<'_, i64>>) -> u64 {
    b.as_ref().map_or(0, |b| b.device_ptr())
}

/// A level above for a run ([`CardField::tower_run`]): the level's field's words and buffers, the glue's material (read by the
/// level's words pointed at it), each level's covector, and the cut's section and half turn.
struct TowerRun<'c> {
    cwords: Words,
    glue_at: u64,
    _cup: Upload<'c>,
    _glue: Pooled<'c, i32>,
    cg: Option<Pooled<'c, i128>>,
    gg: Option<Pooled<'c, i128>>,
    harmonics: usize,
    split: usize,
    section: i64,
    pi: i128,
    offsets: (usize, usize, usize, usize, usize),
    reach_a: u64,
    reach_b: u64,
}

/// A level's epochs for one batch ([`CardField::tower_batch`]): the epochs staged as the level's regions, each fine place's epoch, its
/// harmonics, the epochs' fine offsets, and the per-pass buffers.
struct TowerBatch<'c> {
    st: Staged<'c>,
    ticks: Vec<Tick<'c>>,
    _trips: Pooled<'c, i128>,
    _moment: Pooled<'c, i64>,
    pr: Pooled<'c, i64>,
    _clocks: Vec<Pooled<'c, i64>>,
    _plain: Pooled<'c, u8>,
    split_read: Pooled<'c, i32>,
    split_scale: Pooled<'c, i128>,
    restricted: Pooled<'c, i64>,
    read1: Pooled<'c, i32>,
    scale1: Pooled<'c, i128>,
    pad: Pooled<'c, i64>,
    epoch: Pooled<'c, u32>,
    harmonics: Pooled<'c, i64>,
    off: Pooled<'c, u32>,
    /// The level's skin addresses, its clock's skins and near phases (the stores the fine batch keeps for its own clock).
    _saddr: Pooled<'c, i64>,
    _stores: Vec<Pooled<'c, u32>>,
}

/// A level's reverse buffers ([`CardField::back_buffers`]).
struct Back<'c> {
    dx: Pooled<'c, i64>,
    dr: Pooled<'c, i64>,
    dc: Pooled<'c, i64>,
    da: Pooled<'c, i64>,
    db: Pooled<'c, i64>,
    /// [theory, November 11 17:25] The carry circles' covector `[t][2C]` (one slot without them): the scan's reverse writes `δγ`, and the gate's
    /// reverse writes `δq`, `δℓ` over it in place, the circles' charts' row order.
    dg: Pooled<'c, i64>,
    /// [theory, November 12; the triad record §4] The triads' covectors (none without them): the products' `δc^T = W_Tᵀ δx` `[t][2J]`, and the legs'
    /// `δα`, `δβ`, `δγ` `[t][6J]` in the chart's row order.
    dct: Option<Pooled<'c, i64>>,
    dabg: Option<Pooled<'c, i64>>,
    ra: Pooled<'c, i64>,
    rb: Pooled<'c, i64>,
    dmid: Pooled<'c, i64>,
    dy: Pooled<'c, i64>,
    dyh: Pooled<'c, i64>,
    dq: Pooled<'c, i64>,
    dv: Pooled<'c, i64>,
    dp: Pooled<'c, i64>,
    ds: Pooled<'c, i64>,
    dpb: Pooled<'c, i128>,
    cv: Pooled<'c, i128>,
    cw: Pooled<'c, i128>,
    dm: Pooled<'c, i128>,
    gtau: Pooled<'c, i128>,
    gsig: Pooled<'c, i128>,
    cds: Pooled<'c, i64>,
    pr_back: Pooled<'c, i64>,
}

/// A batch's staged tables ([`CardField::stage`]).
struct Staged<'c> {
    site_region: Vec<u32>,
    site_pos: Vec<u32>,
    region_off: Vec<u32>,
    classes: Vec<u32>,
    unresolved: Vec<u8>,
    definite: Vec<u8>,
    echo_has: Vec<u8>,
    mix_off: Vec<u32>,
    mix_class: Vec<u32>,
    mix_share: Vec<u32>,
    site_weight: Vec<(u64, u64)>,
    pairs: usize,
    /// [theory, November 12, P51] The skins' support entries `E2 = Σ_r S_r K_r`.
    skin_entries: usize,
    sites: usize,
    _tables: Pooled<'c, u8>,
    status: Pooled<'c, u32>,
    x: Pooled<'c, i64>,
}

/// [realization; theory, November 13, P60 item 2] **The standing moments' operands, kept for the cavity's**: every moment mode's strands and their
/// exact prefixes, the forward's admission flags and the modes' words (`moments` with `keep`), which the cavity moments read at their standing
/// phases and the cavity's clock covector reads again.
struct MomentKeep<'c> {
    before: Pooled<'c, i64>,
    after: Pooled<'c, i64>,
    up: Pooled<'c, i128>,
    down: Pooled<'c, i128>,
    _ok: Pooled<'c, u8>,
    ws: Pooled<'c, u64>,
    cmap: Pooled<'c, u32>,
}

/// [realization; theory, November 13, P60 item 2] **The opening's comparison's forward on the card** (the host's `Field::cavity_forward` and
/// `Field::opening_read` at every compared place), kept for its return and its codes: the compared places (`mask`, the words' open-site mask while
/// the opening is read), the cavity moments `[t][2M]` and their two sides `[u][t]`, the cavity openings, their charts, lifts and faces.
struct Opening<'c> {
    mask: Pooled<'c, u8>,
    keep: Option<MomentKeep<'c>>,
    cmoment: Pooled<'c, i64>,
    sb: Pooled<'c, i64>,
    sa: Pooled<'c, i64>,
    read: Pooled<'c, i32>,
    scale: Pooled<'c, i128>,
    lift: Pooled<'c, i64>,
    masses: Pooled<'c, u64>,
    totals: Pooled<'c, i128>,
}

/// [realization; agent-inferred, November 14, the ring record §4] **What a batch's reads stand on** ([`CardField::batch_base`]): everything a
/// read does before its opening `x⁰`, none of which the opening's state reaches. The host's `Field::pass_with` reads the region's clocks
/// (`paces`) and moments (`moments_of`) from the region and the constitution alone, the opening's comparison from the cavity openings, which open
/// no site on a mark (`cavity_forward` passes none), and the level's news from that comparison (`level_news`); only `open` takes the marks. So a
/// field that reads twice ([`FieldDeclaration::mark`]) stages its regions, forms the base clock and its moments, reads the opening's comparison,
/// fetches the news and cuts its level once a batch, and both reads stand on them: the first read's opening is the built one, the second's carries
/// the marks, and from the opening on each read is its own. The opening's comparison is kept here until the read that compares it (the last)
/// returns through it. The clock's stores (the skins, the near phases) are each clock's: a read after the first forms the base clock's again
/// before its first tick (`reads`).
struct BatchBase<'c> {
    st: Staged<'c>,
    /// The base clock (§16): its rates, clocks, variations, skin addresses, plainness and frames, and the site moments on it (§15.1).
    kappa: Pooled<'c, i64>,
    tau: Pooled<'c, i64>,
    sigma: Pooled<'c, i64>,
    saddr: Pooled<'c, i64>,
    plain: Pooled<'c, u8>,
    pframe: Pooled<'c, i64>,
    moment: Pooled<'c, i64>,
    /// The clock's skins and its near phases and skins, one store each for the batch, formed again at each clock.
    _skins: Option<(Pooled<'c, u32>, Pooled<'c, u32>)>,
    _clock_store: Option<(Pooled<'c, u32>, Pooled<'c, u32>)>,
    opening: Option<Opening<'c>>,
    tb: Option<TowerBatch<'c>>,
    /// The reads taken on this base so far.
    reads: usize,
}

impl BatchBase<'_> {
    /// The words of the base clock, in [`set_clock`]'s order.
    fn clock(&self) -> [u64; 7] {
        [self.kappa.device_ptr(), self.tau.device_ptr(), self.sigma.device_ptr(), self.plain.device_ptr(), self.pframe.device_ptr(), self.moment.device_ptr(), self.saddr.device_ptr()]
    }
}

struct Tick<'c> {
    read: Pooled<'c, i32>,
    scale: Pooled<'c, i128>,
    /// The word and the value, `[t][2·2M]`.
    qkv: Pooled<'c, i64>,
    qf: Pooled<'c, i64>,
    /// The unit words on 32 bits `[h][t][span]` (`field_unit` writes them beside `qf`).
    qf32: Pooled<'c, i32>,
    /// Every receiver's probe framed and at unit power by head (`[h][t][span]`, and on 32 bits) with its powers
    /// `[h][t]` (§16.19).
    pq: Pooled<'c, i64>,
    pq32: Pooled<'c, i32>,
    pscale: Pooled<'c, i128>,
    vf: Pooled<'c, i64>,
    /// The framed word's powers `[h][t]`, the ratios `field_unit` reads it as.
    qscale: Pooled<'c, i128>,
    /// The resonance classes `[h][t]`, each region's class offsets `[h][r][2·3^b + 1]` and members
    /// `[h][t]` (`field_classes`).
    cls: Pooled<'c, u32>,
    class_off: Pooled<'c, u32>,
    members: Pooled<'c, u32>,
    /// Each receiver's probed classes: their number `[h][t]`, the classes `[h][t][2^b − 1]`, and the
    /// receivers that probe each class, offsets `[h][r][3^b + 1]` and members `[h][t][2^b − 1]`.
    pn: Pooled<'c, u32>,
    pcls: Pooled<'c, u32>,
    poff: Pooled<'c, u32>,
    pmem: Pooled<'c, u32>,
    e: Pooled<'c, u64>,
    /// The pairs' locks at unit gain `S` (the temperatures' covector, §15.10), kept on a return.
    sb: Pooled<'c, i64>,
    /// The row's least whole bit `[h][t]` (`field_exposure`), each head's prefix sums of the definite
    /// sites' unit words and values `[h][row][span]` and their counts `[h][row]`, and each receiver's
    /// crowd shares `[h][t][slots]` (`row = site + region`, a region's `S + 1` rows).
    amin: Pooled<'c, i64>,
    sw: Pooled<'c, i128>,
    sv: Pooled<'c, i128>,
    sc: Pooled<'c, u64>,
    ce: Pooled<'c, u64>,
    y: Pooled<'c, i64>,
    read2: Pooled<'c, i32>,
    scale2: Pooled<'c, i128>,
    pa: Pooled<'c, i64>,
    /// [theory, November 11 17:25 and November 12 (G98)] The carry circles' charts' reads `q`, `ℓ` `[t][2C]`, their gate `γ` `[t][2C]`, the scan's operand
    /// `[t][2C]` and the coupled drive `κ b` `[t][2C]` (one slot each without them).
    pg: Pooled<'c, i64>,
    pgam: Pooled<'c, i64>,
    pqm: Pooled<'c, i64>,
    pkb: Pooled<'c, i64>,
    pb: Pooled<'c, i64>,
    pc: Pooled<'c, i64>,
    /// [theory, November 12; the triad record §3 and §4] The triads' chart read `abg` `[t][6J]`, their products `p` `[t][2J]` and `c^T` `[t][2J]`, kept
    /// for the reverse; none where the field has no triads, so a field without them takes nothing more.
    pabg: Option<Pooled<'c, i64>>,
    ptp: Option<Pooled<'c, i64>>,
    pct: Option<Pooled<'c, i64>>,
    /// The tick's carrier width: the binary length of its largest unit word.
    bits: Pooled<'c, u32>,
}

/// What a profiled call's time is charged to.
#[derive(Clone, Copy)]
enum Kind {
    Copy,
    Alloc,
}

/// [definition; agent-inferred, November 1] **The card's buffers are kept and reused, not freed with each
/// batch** (measured November 1, 153 calls of a lap's opening: a batch's ~60 allocations and frees took 42 %
/// of the card's wall time, `cuMemAlloc` and `cuMemFree` each tens of microseconds and a free draining the
/// stream). A buffer a batch is done with returns to its size class; the next batch takes one of its class
/// (a class is a multiple of an eighth of the power of two above, so a buffer is at most a quarter too long).
/// What the kept buffers cannot supply (a class up to twice the request's) is allocated; when the live buffers, the kept
/// ones and the new one pass the batch budget, a plain take is first served by the least kept buffer of its type at least
/// its class (P58 item 1, at [`CardField::take`]), and otherwise the largest kept ones are freed first, one at a time. The contents of a taken buffer are undefined, zeroed where
/// the call says so; the work of the stream is ordered, so a buffer a queued kernel still reads is never
/// overwritten before it has.
trait Poolable: Copy + Sized + 'static {
    fn list<'a, 'c>(pools: &'a mut Pools<'c>) -> &'a mut Vec<(usize, CardBuffer<'c, Self>)>;
}

#[derive(Default)]
struct Pools<'c> {
    u8s: Vec<(usize, CardBuffer<'c, u8>)>,
    u32s: Vec<(usize, CardBuffer<'c, u32>)>,
    i32s: Vec<(usize, CardBuffer<'c, i32>)>,
    u64s: Vec<(usize, CardBuffer<'c, u64>)>,
    i64s: Vec<(usize, CardBuffer<'c, i64>)>,
    i128s: Vec<(usize, CardBuffer<'c, i128>)>,
    /// The octets of the buffers taken and not yet returned, and of those kept.
    live: u64,
    retained: u64,
    /// [measurement; G143] The live octets by the line of the take that holds them.
    live_by_line: std::collections::BTreeMap<u32, u64>,
}

macro_rules! poolable {
    ($t:ty, $f:ident) => {
        impl Poolable for $t {
            fn list<'a, 'c>(pools: &'a mut Pools<'c>) -> &'a mut Vec<(usize, CardBuffer<'c, Self>)> {
                &mut pools.$f
            }
        }
    };
}
poolable!(u8, u8s);
poolable!(u32, u32s);
poolable!(i32, i32s);
poolable!(u64, u64s);
poolable!(i64, i64s);
poolable!(i128, i128s);

impl Pools<'_> {
    /// Free the kept buffer of the most octets, of any element type.
    fn free_largest(&mut self) -> u64 {
        fn largest<T>(list: &[(usize, CardBuffer<'_, T>)]) -> Option<(usize, u64)> {
            list.iter().enumerate().map(|(i, (c, _))| (i, (*c * core::mem::size_of::<T>()) as u64)).max_by_key(|&(_, o)| o)
        }
        let candidates = [largest(&self.u8s), largest(&self.u32s), largest(&self.i32s), largest(&self.u64s), largest(&self.i64s), largest(&self.i128s)];
        let Some((which, (i, octets))) = candidates.iter().enumerate().filter_map(|(w, c)| c.map(|c| (w, c))).max_by_key(|&(_, (_, o))| o) else {
            self.retained = 0;
            return 0;
        };
        match which {
            0 => drop(self.u8s.swap_remove(i)),
            1 => drop(self.u32s.swap_remove(i)),
            2 => drop(self.i32s.swap_remove(i)),
            3 => drop(self.u64s.swap_remove(i)),
            4 => drop(self.i64s.swap_remove(i)),
            _ => drop(self.i128s.swap_remove(i)),
        }
        self.retained = self.retained.saturating_sub(octets);
        octets
    }

}

/// The elements of the size class holding `len`: a multiple of an eighth of the power of two above it
/// (and of four, the memset's word).
fn size_class(len: usize) -> usize {
    let len = len.max(4);
    let top = len.next_power_of_two();
    let step = (top / 8).max(4);
    len.div_ceil(step) * step
}

/// Host arrays packed into one buffer for one transfer, each at a 16-octet boundary (a transfer of its own
/// costs tens of microseconds and drains the stream; a batch's fourteen were a tenth of its host time).
#[derive(Default)]
struct Packed {
    bytes: Vec<u8>,
}

impl Packed {
    /// The octet offset of `values`, appended (plain integers only).
    fn put<T: Copy>(&mut self, values: &[T]) -> u64 {
        while self.bytes.len() % 16 != 0 {
            self.bytes.push(0);
        }
        let at = self.bytes.len();
        // SAFETY: the arrays packed are slices of integers, read as the octets that hold them.
        self.bytes.extend_from_slice(unsafe { std::slice::from_raw_parts(values.as_ptr().cast::<u8>(), core::mem::size_of_val(values)) });
        at as u64
    }
}

/// A buffer taken from the card's pool; it returns there when dropped. It stands for a `CardBuffer`
/// (dereferences to it) whose length is its class, at least what was asked.
struct Pooled<'c, T: Poolable> {
    buf: Option<(usize, CardBuffer<'c, T>)>,
    pools: std::rc::Rc<std::cell::RefCell<Pools<'c>>>,
    /// [measurement; G143] The line of the take that holds it (the live set by take site, a reading).
    line: u32,
}

impl<'c, T: Poolable> std::ops::Deref for Pooled<'c, T> {
    type Target = CardBuffer<'c, T>;
    fn deref(&self) -> &Self::Target {
        &self.buf.as_ref().expect("a pooled buffer holds its card buffer until it is dropped").1
    }
}

impl<T: Poolable> Drop for Pooled<'_, T> {
    fn drop(&mut self) {
        if let Some((cap, buf)) = self.buf.take() {
            let octets = (cap * core::mem::size_of::<T>()) as u64;
            let mut pools = self.pools.borrow_mut();
            pools.live = pools.live.saturating_sub(octets);
            pools.retained += octets;
            if let Some(v) = pools.live_by_line.get_mut(&self.line) {
                *v = v.saturating_sub(octets);
            }
            T::list(&mut pools).push((cap, buf));

        }
    }
}

/// [measurement; P57 item 1] One launch as a trace reads it (`FieldProfile::trace`).
#[derive(Clone, Debug, Default)]
pub struct LaunchRecord {
    pub run: u64,
    pub phase: &'static str,
    pub entry: &'static str,
    pub grid: [u32; 3],
    pub block: u32,
    pub shared: u32,
    pub ns: u128,
    pub head: Option<u32>,
}

/// [measurement; P57 item 1] An entry's lowering on the mounted card: registers a thread, static shared and local octets, the
/// largest block, and the blocks a multiprocessor keeps resident at the launch's block and dynamic shared octets.
#[derive(Clone, Copy, Debug, Default)]
pub struct EntryAttributes {
    pub registers: u32,
    pub static_shared: u32,
    pub local: usize,
    pub max_threads: u32,
    pub blocks_a_multiprocessor: u32,
}

/// [measurement; theory, November 13, P61 item 3] A site's map's launch kind: the entry, its rows and cols, whether it reads only the open
/// sites, and whether it adds into its output (`add` for a forward map, `accumulate` for a transposed one).
pub type MapKind = (&'static str, u32, u32, bool, bool);

/// [measurement; P61 item 3] A kind's operands read by the bits ruler: the largest weight (`wmax`) and each operand's largest word in bits;
/// its sites and those whose row stands under `2^31`, by operand; its tiles of [`MAP_TILE`] sites and those whose sums stand in 64 bits under
/// the limb test ([`tile_proves`]), and in 96 bits (a third carry word, a reading only); its launches whose every tile proves.
#[derive(Clone, Debug, Default)]
pub struct MapBits {
    pub launches: u64,
    pub w_bits: u32,
    pub bits: [u32; 2],
    pub sites: u64,
    pub under31: [u64; 2],
    pub tiles: u64,
    pub proved64: u64,
    pub proved96: u64,
    pub launches_all64: u64,
    pub launches_all96: u64,
}

/// [measurement; P61 item 3] The sites a tile of the tiled form holds (a block's 64 sites at a 64 by 64 map).
pub const MAP_TILE: usize = 64;

/// [definition; P61 item 4c, `agent-inferred`] **A tile's sums stand in `bits` bits** where its magnitudes prove it: `k` terms a sum, each a
/// product of two operands of largest magnitudes `a` and `b` (a weight on 32 bits, a word on 32 or 64). An operand under `2^31` is one signed
/// limb; one over it enters as two 32-bit limbs (the low one unsigned, under `2^32`, the high one signed, at most `(m >> 32) + 1`), and each
/// limb's sum stands alone. One operand on two limbs: `k · 2^32 · b` and `k · ((a >> 32) + 1) · b` under `2^(bits − 1)`; both on two limbs: the
/// low limbs' product reaches `2^64`, so only the wide form stands under 64 bits. Both under `2^31`: `k · a · b` under `2^(bits − 1)`.
pub fn tile_proves(k: u128, a: u128, b: u128, bits: u32) -> bool {
    let top = 1u128 << (bits - 1);
    let small = |m: u128| m < (1u128 << 31);
    let under = |x: Option<u128>| x.is_some_and(|v| v < top);
    let prod = |x: u128, y: u128, z: u128| x.checked_mul(y).and_then(|v| v.checked_mul(z));
    match (small(a), small(b)) {
        (true, true) => under(prod(k, a, b)),
        (false, true) => under(prod(k, 1u128 << 32, b)) && under(prod(k, (a >> 32) + 1, b)),
        (true, false) => under(prod(k, a, 1u128 << 32)) && under(prod(k, a, (b >> 32) + 1)),
        (false, false) => bits > 64 && under(prod(k, 1u128 << 32, 1u128 << 32)) && under(prod(k, (a >> 32) + 1, (b >> 32) + 1)) && under(prod(k, (a >> 32) + 1, 1u128 << 32)),
    }
}

/// [measurement; P57 item 1] The launches a trace keeps: a section's are about 510, so four sections and the run's opening.
pub const TRACE_LAUNCHES: usize = 2600;

/// [agent-inferred, November 1] A declared reading (`CardField::profile`): every launch timed alone,
/// the card synchronized before and after it, by entry; every transfer and allocation timed after the
/// card's stream has drained, so a run's wall time splits into kernels, copies, allocations and the
/// host's own work. It moves nothing the field computes.
#[derive(Clone, Debug, Default)]
pub struct FieldProfile {
    pub kernels: std::collections::BTreeMap<&'static str, (u64, u128)>,
    /// [measurement; theory, November 11] Each entry's blocks × block-threads summed over its launches (a reading of the launches' grids; the mean grid is this over the launches).
    pub threads: std::collections::BTreeMap<&'static str, u128>,
    pub copies: (u64, u128),
    pub allocations: (u64, u128),
    /// [measurement; theory, November 12, P50 step 0] The launches made a head at a time (the contact's return: its rows, its
    /// columns, the skin's return, the spread), by entry and head: launches and ns.
    pub by_head: std::collections::BTreeMap<(&'static str, u32), (u64, u128)>,
    /// The site pairs the forward contact met a head, `Σ_i |S_i^h|` over every row and tick of the runs counted in `FieldTimes::pairs`.
    pub pairs_by_head: Vec<u128>,
    /// Each head's kind as the declaration reads it: `still`, `paced` (a turned ring set that is no depth ring, whose skin reads its
    /// own clock) or `depth`.
    pub head_kinds: Vec<&'static str>,
    /// [measurement; theory, November 13, P56 item 4] Each copy and take by its call site's line in this file (`copy` or `take`): count and ns.
    pub by_site: std::collections::BTreeMap<(&'static str, u32), (u64, u128)>,
    /// [measurement; theory, November 13, P56 item 4] A zeroed take's zeroing by its call site's line: count, ns (timed alone, the stream drained
    /// before and after) and octets zeroed.
    pub zeroed: std::collections::BTreeMap<u32, (u64, u128, u128)>,
    /// [measurement; theory, November 13, P61 item 3] A site's maps by launch kind (entry, rows, cols, only_unresolved, add or accumulate):
    /// launches, ns and products (sites times rows times cols as launched).
    pub maps: std::collections::BTreeMap<MapKind, (u64, u128, u128)>,
    /// [measurement; P61 item 3] Under `FIELD_TRACE`, each kind's operands' magnitudes and its tiles' proofs ([`MapBits`]).
    pub map_bits: std::collections::BTreeMap<MapKind, MapBits>,
    /// [measurement; theory, November 13, P57 item 1] Under `FIELD_TRACE` (with the profile): every launch in order, up to
    /// [`TRACE_LAUNCHES`], with the run it belongs to, the last phase marked, its grid, block, dynamic shared octets, its timed ns
    /// and its head; and each entry's attributes as the driver lowered it, at each block and dynamic shared it was launched with.
    pub trace_on: bool,
    pub trace: Vec<LaunchRecord>,
    /// Each traced run's batches' region lengths in sites.
    pub trace_regions: Vec<(u64, Vec<usize>)>,
    pub attributes: std::collections::BTreeMap<(&'static str, u32, u32), EntryAttributes>,
    /// [measurement; theory, November 13, P58 item 1] The pool by a take's call site's line and its size class in octets: hits, misses (an
    /// allocation), the kept buffers a miss freed and their octets.
    /// [realization; P58 item 1] and the plain takes served by a larger kept buffer in place of an allocation.
    pub pool: std::collections::BTreeMap<(u32, u64), [u64; 5]>,
    /// [measurement; theory, November 13, G142] At each take that allocated, by its line and class: the takes, and the live, kept and over-budget
    /// octets summed at that take (live and kept before it; over budget the octets by which live, kept and the new buffer passed the batch's
    /// budget). Each kept buffer the budget freed, by its octets. The largest live set the batch's takes reached, and the budget.
    pub pool_pressure: std::collections::BTreeMap<(u32, u64), [u128; 4]>,
    pub pool_freed: std::collections::BTreeMap<u64, u64>,
    pub pool_peak: (u64, u64),
    /// [measurement; G143] The phase (the last mark) of the live set's peak and the live octets by take line there; and each phase's largest live set.
    pub peak_phase: &'static str,
    pub peak_by_line: Vec<(u32, u64)>,
    pub phase_peak: std::collections::BTreeMap<&'static str, u64>,
    /// [measurement; theory, November 13, P56 item 4] Every timed launch, copy, take and zeroing summed (ns): what a phase's wall holds of the card's.
    pub timed_ns: u128,
}

/// [measurement; theory, November 12, P50 step 0b] The card's yardsticks ([`CardField::yardsticks`]): each reading as (rate a
/// second, count, seconds).
#[derive(Clone, Debug)]
pub struct Yardsticks {
    pub multiprocessors: u32,
    pub product_blocks: u32,
    pub stream_blocks: u32,
    /// Narrow products, one thread a cell (site, output) of a 64 by 64 map.
    pub cell: (f64, u64, f64),
    /// Narrow products, one thread a tile of four outputs by four sites.
    pub tile: (f64, u64, f64),
    pub store_octets: u64,
    pub read: (f64, u64, f64),
    pub write: (f64, u64, f64),
    pub gather_rows: u32,
    pub gather_entries: u32,
    /// Eight words (32 octets) a gather at a random entry of a random row.
    pub gather: (f64, u64, f64),
}

/// **The field on the card**: its image, the card it runs on and the octets a batch may take.
pub struct CardField<'c> {
    card: &'c Card,
    module: Module,
    budget: u64,
    times: FieldTimes,
    profile: Option<std::cell::RefCell<FieldProfile>>,
    /// The head a launch is made for, where the launches go a head at a time (a profile's reading by head).
    head: std::cell::Cell<Option<u32>>,
    /// [measurement; P61 item 3] The last launch's timed ns, under the profile.
    last_ns: std::cell::Cell<u128>,
    /// [realization; P61 item 4f] The outer passes' slots for their largest words and the next slot ([`CardField::outer_slot`]).
    outer_maxima: std::cell::RefCell<Option<(Pooled<'c, u64>, usize)>>,
    /// [theory, November 12, P50 step 1] The test build's negative control: the clock's fill withheld, its store left at `SKIN_UNFILLED`.
    #[cfg(test)]
    unfilled: std::cell::Cell<bool>,
    /// [measurement; theory, November 12, P54 item 1] The ruler build's histograms of the words' bits (`BITS_NAMES` by clock by bit length).
    #[cfg(feature = "ruler-bits")]
    bits: std::cell::RefCell<Option<CardBuffer<'c, u64>>>,
    pools: std::rc::Rc<std::cell::RefCell<Pools<'c>>>,
    /// A held read's rows by where their mass lies (a reading for the receipts): the regions' answer starts
    /// while it is read, and the cells `[tick · heads + head][rows, question, soft_near, other, current, question_far, far_effective, far_rows]` summed.
    held_questions: std::cell::RefCell<Option<Vec<usize>>>,
    /// [measurement, §16.20] While a covector's shares are read, `[h][near, far]` summed over the batches.
    covector_shares: std::cell::RefCell<Option<Vec<i128>>>,
    /// [measurement, §16.21] While the held rows' currents are read: the regions' answer starts, the rows read region by
    /// region, and the batch's current covectors a tick `[h][t][2n]` where read with a return.
    row_questions: std::cell::RefCell<Option<Vec<usize>>>,
    row_out: std::cell::RefCell<Vec<Vec<RowCurrent>>>,
    row_cov: std::cell::RefCell<Option<Vec<Vec<i64>>>>,
    held_cells: std::cell::RefCell<Vec<i128>>,
    /// [measurement, November 4] While the ticks are read: each region's tick reads, region by region.
    tick_reads: std::cell::RefCell<Option<Vec<Vec<TickRead>>>>,
    /// [measurement; theory, November 11 18:33, part P2] While the carry circles' gates are read: each circle's `|γ|` sum, then its `ℓ ≥ 0` count,
    /// then the reads (`2C + 1` words, [`CarryGates`]), summed over the batches from each tick's forward.
    carry_gates: std::cell::RefCell<Option<Vec<u128>>>,
    /// [measurement, §16.42] While a near field is read: the named sites of the batch's one region, and each one's near field
    /// by offset at every kept tick and head.
    near_sites: std::cell::RefCell<Option<Vec<usize>>>,
    near_out: std::cell::RefCell<Vec<NearOffsets>>,
    /// [measurement, §16.44] While the blanks' clocks are read: the named sites of the batch's one region, and each one's
    /// clocks by tick.
    clock_sites: std::cell::RefCell<Option<Vec<usize>>>,
    clock_out: std::cell::RefCell<Vec<BlankClocks>>,
    /// The host's wall time between marks, by name (`FIELD_PHASES`), no stream synchronized.
    phases: Option<std::cell::RefCell<(Instant, std::collections::BTreeMap<&'static str, (u64, u128)>)>>,
    /// [measurement; theory, November 13, P56 item 4] Each phase's timed card ns (launches, copies, takes, zeroings) when also profiled, and the
    /// profile's running total at the last mark.
    phase_card: std::cell::RefCell<(u128, std::collections::BTreeMap<&'static str, u128>)>,
    /// [realization; theory, November 13, P58 item 3] While the training path reads its faces at their classes
    /// ([`FieldRealization::read_and_return_at_class`]): set, and each region's open sites' `(m_c, T)` gathered on the card.
    narrow: std::cell::Cell<bool>,
    narrow_out: std::cell::RefCell<Vec<Vec<Option<(u128, u128)>>>>,
    /// [measurement; theory, November 13, P57 item 2 (G132)] While the charts are read by stage
    /// ([`FieldRealization::read_tick_charts`]): each region's open sites' chart rows at each tick's opening and after the last tick.
    tick_charts: std::cell::RefCell<Option<Vec<Vec<Vec<i32>>>>>,
    /// [measurement; P57 item 1] The last phase marked, which a trace's launches are read under.
    last_mark: std::cell::Cell<&'static str>,
    /// [realization; theory, November 13, P60 items 1d and 2] While the training path reads the opening's codes
    /// ([`FieldRealization::read_and_return_opening`]): set, and each region's opening code at every compared place.
    opening_wanted: std::cell::Cell<bool>,
    opening_out: std::cell::RefCell<Vec<Vec<Option<i64>>>>,
}

impl<'c> CardField<'c> {
    /// Load the field's image; a batch's stores take the card's free memory at its open less the
    /// margin, kept under the 12 GB the runs keep the board to.
    pub fn open(card: &'c Card) -> std::result::Result<Self, DeviceError> {
        card.current()?;
        let module = Module::load_ptx(IMAGE)?;
        let memory = card.census().memory;
        let (free, total) = (memory.free_bytes as u64, memory.total_bytes as u64);
        let used = total.saturating_sub(free);
        let budget = free.min(BOARD_CEILING.saturating_sub(used)).saturating_sub(MARGIN);
        Ok(Self { card, module, budget, times: FieldTimes::default(), profile: None, head: Default::default(), last_ns: Default::default(), outer_maxima: Default::default(), #[cfg(test)] unfilled: Default::default(), #[cfg(feature = "ruler-bits")] bits: Default::default(), pools: Default::default(), held_questions: Default::default(), covector_shares: Default::default(), row_questions: Default::default(), row_out: Default::default(), row_cov: Default::default(), held_cells: Default::default(), tick_reads: Default::default(), carry_gates: Default::default(), near_sites: Default::default(), near_out: Default::default(), clock_sites: Default::default(), clock_out: Default::default(), phases: None, phase_card: Default::default(), narrow: Default::default(), narrow_out: Default::default(), last_mark: std::cell::Cell::new("open"), tick_charts: Default::default(), opening_wanted: Default::default(), opening_out: Default::default() })
    }

    /// The octets a batch's weight and contact stores may take.
    pub fn budget(&self) -> u64 {
        self.budget
    }

    pub fn times(&self) -> FieldTimes {
        self.times
    }

    /// A buffer of at least `len` elements, contents undefined (`Pooled`).
    #[track_caller]
    fn take<T: Poolable>(&self, len: usize) -> std::result::Result<Pooled<'c, T>, DeviceError> {
        self.take_with(len, true, std::panic::Location::caller().line())
    }

    /// [`take`](Self::take), `wide` where a kept buffer longer than twice the class may serve it.
    fn take_with<T: Poolable>(&self, len: usize, wide: bool, line: u32) -> std::result::Result<Pooled<'c, T>, DeviceError> {
        let cap = size_class(len.max(1));
        let size = core::mem::size_of::<T>();
        let mut pools = self.pools.borrow_mut();
        // [agent-inferred, November 5] A kept buffer of the class or the next ones up to twice it serves the request (the
        // least such), and the budget is kept by freeing the largest kept buffers one at a time, not every kept buffer at
        // once: the profile read 33,780 allocations taking 12.2 s of a 94 s training read, a batch's buffers of varied
        // classes missing an exact class and a trim freeing every kept buffer the next batch then allocated again.
        let hit = {
            let list = T::list(&mut pools);
            list.iter().enumerate().filter(|(_, (c, _))| *c >= cap && *c <= 2 * cap).min_by_key(|(_, (c, _))| *c).map(|(i, _)| i).map(|i| list.swap_remove(i))
        };
        let (mut frees, mut freed) = (0u64, 0u64);
        // [realization; theory, November 13, P58 item 1] **A kept buffer longer than the class serves a plain take that the
        // budget would otherwise pay for with a free.** The counted read of 100 sections (sections 2,001 to 2,100 of the store
        // trainer's run 2) found the face covector's block (`dz`, 160 MiB) and the clock's skins (`sk`, 448 MiB), both `i128`,
        // taken in turn within each batch and never live together: 5 of `dz`'s 300 takes and 98 of `sk`'s 400 hit, and each
        // miss freed the other's kept buffer (294 frees of 465 MB on average at `dz`, 278 of 172 MB at `sk`), because the live
        // set, the other's kept buffer and the new one passed the budget, and the other's buffer was more than twice `dz`'s
        // class. Freeing what the last section did not take first, or holding a section's set, would not answer it: both are
        // taken in every section, and the budget cannot hold both kept beside the live set. Taking the kept buffer as it is
        // moves its octets from kept to live, so live plus kept stays as it was, under the budget. A zeroed take keeps the
        // twice-class bound, so its zeroing stays its class's.
        let mut widened = false;
        let missed;
        let entry = match hit {
            Some(entry) => {
                missed = false;
                pools.retained = pools.retained.saturating_sub((entry.0 * size) as u64);
                entry
            }
            None => {
                let octets = (cap * size) as u64;
                let longer = if wide && pools.live + pools.retained + octets > self.budget {
                    let list = T::list(&mut pools);
                    list.iter().enumerate().filter(|(_, (c, _))| *c >= cap).min_by_key(|(_, (c, _))| *c).map(|(i, _)| i).map(|i| list.swap_remove(i))
                } else {
                    None
                };
                match longer {
                    Some(entry) => {
                        (missed, widened) = (false, true);
                        pools.retained = pools.retained.saturating_sub((entry.0 * size) as u64);
                        entry
                    }
                    None => {
                        missed = true;
                        if let Some(profile) = &self.profile {
                            let mut p = profile.borrow_mut();
                            let over = (pools.live + pools.retained + octets).saturating_sub(self.budget);
                            let slot = p.pool_pressure.entry((line, octets)).or_insert([0; 4]);
                            (slot[0], slot[1], slot[2], slot[3]) = (slot[0] + 1, slot[1] + u128::from(pools.live), slot[2] + u128::from(pools.retained), slot[3] + u128::from(over));
                        }
                        while pools.live + pools.retained + octets > self.budget && pools.retained > 0 {
                            let before = pools.retained;
                            let class = pools.free_largest();
                            if let Some(profile) = &self.profile {
                                *profile.borrow_mut().pool_freed.entry(class).or_insert(0) += 1;
                            }
                            (frees, freed) = (frees + 1, freed + before.saturating_sub(pools.retained));
                        }
                        (cap, self.card.alloc::<T>(cap)?)
                    }
                }
            }
        };
        if let Some(profile) = &self.profile {
            let mut p = profile.borrow_mut();
            let slot = p.pool.entry((line, (cap * size) as u64)).or_insert([0; 5]);
            slot[if widened { 4 } else { usize::from(missed) }] += 1;
            (slot[2], slot[3]) = (slot[2] + frees, slot[3] + freed);
        }
        pools.live += (entry.0 * size) as u64;
        *pools.live_by_line.entry(line).or_insert(0) += (entry.0 * size) as u64;
        if let Some(profile) = &self.profile {
            let mut p = profile.borrow_mut();
            // [measurement; G143] At each new peak of the live set: the phase it stood in (the last mark) and the live octets by take site.
            if pools.live > p.pool_peak.0 {
                p.peak_phase = self.last_mark.get();
                p.peak_by_line = pools.live_by_line.iter().filter(|(_, v)| **v > 0).map(|(l, v)| (*l, *v)).collect();
            }
            p.pool_peak = (p.pool_peak.0.max(pools.live), self.budget);
            let slot = p.phase_peak.entry(self.last_mark.get()).or_insert(0);
            *slot = (*slot).max(pools.live);
        }
        Ok(Pooled { buf: Some(entry), pools: self.pools.clone(), line })
    }

    /// [`take`](Self::take) with every element zero.
    #[track_caller]
    fn take_zeroed<T: Poolable>(&self, len: usize) -> std::result::Result<Pooled<'c, T>, DeviceError> {
        let line = std::panic::Location::caller().line();
        let buffer = self.take_with::<T>(len, false, line)?;
        let octets = buffer.len() * core::mem::size_of::<T>();
        // [measurement; theory, November 13, P56 item 4] When profiled, the zeroing timed alone by its call site.
        let started = self.profile.as_ref().map(|_| {
            let _ = self.card.synchronize();
            Instant::now()
        });
        self.card.zero_octets(&*buffer, 0, octets)?;
        if let (Some(profile), Some(started)) = (&self.profile, started) {
            let _ = self.card.synchronize();
            let ns = started.elapsed().as_nanos();
            let mut p = profile.borrow_mut();
            let z = p.zeroed.entry(line).or_insert((0, 0, 0));
            (z.0, z.1, z.2) = (z.0 + 1, z.1 + ns, z.2 + octets as u128);
        }
        Ok(buffer)
    }

    /// [`take`](Self::take) holding `values` (a synchronous transfer: complete when this returns).
    fn take_up<T: Poolable>(&self, values: &[T]) -> std::result::Result<Pooled<'c, T>, DeviceError> {
        let buffer = self.take::<T>(values.len())?;
        self.card.write(&*buffer, 0, values)?;
        Ok(buffer)
    }

    /// Time every launch, transfer and allocation from here on ([`FieldProfile`]).
    pub fn profile(&mut self) {
        self.profile = Some(std::cell::RefCell::new(FieldProfile { trace_on: std::env::var_os("FIELD_TRACE").is_some(), ..Default::default() }));
    }

    /// Time the host between the marks of a batch (`mark`), without synchronizing: where the wall time of a
    /// pass goes between the host's work and its waits on the card.
    pub fn trace_phases(&mut self) {
        self.phases = Some(std::cell::RefCell::new((Instant::now(), Default::default())));
    }

    /// The phases read so far, when traced: name, marks and wall ns.
    pub fn phased(&self) -> Option<Vec<(&'static str, u64, u128)>> {
        self.phases.as_ref().map(|p| p.borrow().1.iter().map(|(k, v)| (*k, v.0, v.1)).collect())
    }

    fn mark(&self, name: &'static str) {
        self.last_mark.set(name);
        if let Some(p) = &self.phases {
            let mut p = p.borrow_mut();
            let ns = p.0.elapsed().as_nanos();
            p.0 = Instant::now();
            let slot = p.1.entry(name).or_insert((0, 0));
            slot.0 += 1;
            slot.1 += ns;
            if let Some(profile) = &self.profile {
                let total = profile.borrow().timed_ns;
                let mut c = self.phase_card.borrow_mut();
                let delta = total.saturating_sub(c.0);
                c.0 = total;
                *c.1.entry(name).or_insert(0) += delta;
            }
        }
    }

    /// [measurement; theory, November 13, P56 item 4] Each phase's timed card ns, when traced and profiled.
    pub fn phase_card(&self) -> Vec<(&'static str, u128)> {
        self.phase_card.borrow().1.iter().map(|(k, v)| (*k, *v)).collect()
    }

    /// The profile read so far, when profiled.
    pub fn profiled(&self) -> Option<FieldProfile> {
        self.profile.as_ref().map(|p| p.borrow().clone())
    }

    /// [measurement; theory, November 12, P50 step 0b] **The card's yardsticks** (`kernels/field.cu`, `field_yard_*`): narrow
    /// products a second from a site's map held in shared memory (one thread a cell, and one thread a tile of four outputs by
    /// four sites), and octets a second on a store of 2^28 words of 32 bits read in order, written in order, and gathered eight
    /// words at a random entry of a random row of `entries` entries. Each reading is timed alone, after a calibrating launch,
    /// to at least `seconds` of the card's time. No law and no state: the field's buffers are not touched.
    pub fn yardsticks(&self, entries: u32, seconds: f64) -> std::result::Result<Yardsticks, DeviceError> {
        let card = self.card;
        card.current()?;
        let sms = card.census().multiprocessors.max(1);
        let timed = |entry: &'static str, grid: u32, params: &mut [*mut c_void], launches: u32| -> std::result::Result<f64, DeviceError> {
            let function = self.module.function(entry)?;
            card.synchronize()?;
            let started = Instant::now();
            for _ in 0..launches {
                function.launch_on_shared(card.stream(), Dim3::x(grid), Dim3 { x: 256, y: 1, z: 1 }, 0, params)?;
            }
            card.synchronize()?;
            Ok(started.elapsed().as_secs_f64())
        };
        // A calibrating run at `trial`, then the count that takes `seconds` at its rate (at least the trial's).
        let scaled = |trial: u32, took: f64| -> u32 { ((f64::from(trial) * seconds / took.max(1e-9)).ceil() as u64).clamp(u64::from(trial), u64::from(u32::MAX)) as u32 };
        let n = 64u64;
        let table: Vec<u32> = (0..n * n).map(|c| (c as u32).wrapping_mul(0x9E37_79B9) ^ 0x7F4A_7C15).collect();
        let (table, input) = (card.upload(&table)?, card.upload(&table.iter().rev().copied().collect::<Vec<u32>>())?);
        let blocks = sms * 64;
        let out = card.alloc::<u64>(blocks as usize * 256)?;
        let (mut tp, mut ip, mut op) = (table.device_ptr(), input.device_ptr(), out.device_ptr());
        let mut products = |entry: &'static str, per_pass: u64| -> std::result::Result<(f64, u64, f64), DeviceError> {
            let mut passes = 64u32;
            let took = timed(entry, blocks, &mut [arg(&mut tp), arg(&mut ip), arg(&mut op), arg(&mut passes)], 1)?;
            let mut passes = scaled(passes, took);
            let took = timed(entry, blocks, &mut [arg(&mut tp), arg(&mut ip), arg(&mut op), arg(&mut passes)], 1)?;
            let count = u64::from(blocks) * per_pass * u64::from(passes);
            Ok((count as f64 / took, count, took))
        };
        let cell = products("field_yard_products_cell", 256 * n)?;
        let tile = products("field_yard_products_tile", 256 * n * 16)?;
        // The store: 2^28 words, every word written before it is read.
        let words = 1usize << 28;
        let store = card.alloc::<u32>(words)?;
        let (mut sp, mut quads, mut seed) = (store.device_ptr(), (words / 4) as u64, 0x5EED_u32);
        let stride_blocks = sms * 32;
        let sums = card.alloc::<u64>(stride_blocks as usize * 256)?;
        let mut sum_p = sums.device_ptr();
        let octets = (words * 4) as u64;
        let streamed = |entry: &'static str, params: &mut [*mut c_void]| -> std::result::Result<(f64, u64, f64), DeviceError> {
            let took = timed(entry, stride_blocks, params, 4)?;
            let launches = scaled(4, took);
            let took = timed(entry, stride_blocks, params, launches)?;
            let moved = octets * u64::from(launches);
            Ok((moved as f64 / took, moved, took))
        };
        let write = streamed("field_yard_write", &mut [arg(&mut sp), arg(&mut quads), arg(&mut seed)])?;
        let read = streamed("field_yard_read", &mut [arg(&mut sp), arg(&mut quads), arg(&mut sum_p)])?;
        let entries = entries.max(1);
        let mut rows = (words as u64 / (u64::from(entries) * 8)) as u32;
        let mut entries_a = entries;
        let mut gathers = 64u32;
        let took = timed("field_yard_gather", stride_blocks, &mut [arg(&mut sp), arg(&mut rows), arg(&mut entries_a), arg(&mut gathers), arg(&mut seed), arg(&mut sum_p)], 1)?;
        let mut gathers = scaled(gathers, took);
        let took = timed("field_yard_gather", stride_blocks, &mut [arg(&mut sp), arg(&mut rows), arg(&mut entries_a), arg(&mut gathers), arg(&mut seed), arg(&mut sum_p)], 1)?;
        let moved = u64::from(stride_blocks) * 256 * u64::from(gathers) * 32;
        let gather = (moved as f64 / took, moved, took);
        Ok(Yardsticks { multiprocessors: sms, product_blocks: blocks, stream_blocks: stride_blocks, cell, tile, store_octets: octets, read, write, gather_rows: rows, gather_entries: entries, gather })
    }

    /// A transfer or an allocation, timed after the stream drains when profiled.
    #[track_caller]
    fn timed<T>(&self, kind: Kind, f: impl FnOnce() -> T) -> T {
        let Some(profile) = &self.profile else { return f() };
        let line = std::panic::Location::caller().line();
        let _ = self.card.synchronize();
        let started = Instant::now();
        let out = f();
        let ns = started.elapsed().as_nanos();
        let mut p = profile.borrow_mut();
        let (slot, name) = match kind {
            Kind::Copy => (&mut p.copies, "copy"),
            Kind::Alloc => (&mut p.allocations, "take"),
        };
        slot.0 += 1;
        slot.1 += ns;
        let site = p.by_site.entry((name, line)).or_insert((0, 0));
        site.0 += 1;
        site.1 += ns;
        p.timed_ns += ns;
        out
    }

    fn launch(&self, entry: &'static str, grid: u32, block: u32, params: &mut [*mut c_void]) -> Result<()> {
        self.launch_shared(entry, grid, block, 0, params)
    }

    /// A launch with `shared` octets of the block's dynamic shared memory.
    fn launch_shared(&self, entry: &'static str, grid: u32, block: u32, shared: u32, params: &mut [*mut c_void]) -> Result<()> {
        self.launch_grid(entry, Dim3::x(grid.max(1)), block, shared, params)
    }

    /// A launch over a grid of `grid` blocks of `block` threads and `shared` octets of dynamic shared memory.
    fn launch_grid(&self, entry: &'static str, grid: Dim3, block: u32, shared: u32, params: &mut [*mut c_void]) -> Result<()> {
        self.card.current().map_err(device)?;
        let function = self.module.function(entry).map_err(|e| device(e.into()))?;
        let started = match &self.profile {
            Some(_) => {
                self.card.synchronize().map_err(device)?;
                Some(Instant::now())
            }
            None => None,
        };
        function.launch_on_shared(self.card.stream(), grid, Dim3 { x: block, y: 1, z: 1 }, shared, params).map_err(|e| device(e.into()))?;
        if let (Some(profile), Some(started)) = (&self.profile, started) {
            self.card.synchronize().map_err(device)?;
            let mut p = profile.borrow_mut();
            let slot = p.kernels.entry(entry).or_insert((0, 0));
            slot.0 += 1;
            slot.1 += started.elapsed().as_nanos();
            p.timed_ns += started.elapsed().as_nanos();
            self.last_ns.set(started.elapsed().as_nanos());
            *p.threads.entry(entry).or_insert(0) += u128::from(grid.x) * u128::from(grid.y) * u128::from(grid.z) * u128::from(block);
            if let Some(h) = self.head.get() {
                let slot = p.by_head.entry((entry, h)).or_insert((0, 0));
                slot.0 += 1;
                slot.1 += started.elapsed().as_nanos();
            }
            if p.trace_on && p.trace.len() < TRACE_LAUNCHES {
                let ns = started.elapsed().as_nanos();
                p.trace.push(LaunchRecord { run: self.times.returns + self.times.reads, phase: self.last_mark.get(), entry, grid: [grid.x, grid.y, grid.z], block, shared, ns, head: self.head.get() });
                if !p.attributes.contains_key(&(entry, block, shared)) {
                    let a = EntryAttributes {
                        registers: function.num_regs().map_err(|e| device(e.into()))?,
                        static_shared: function.static_shared_bytes().map_err(|e| device(e.into()))?,
                        local: function.local_size_bytes().map_err(|e| device(e.into()))?,
                        max_threads: function.max_threads_per_block().map_err(|e| device(e.into()))?,
                        blocks_a_multiprocessor: function.active_blocks_per_multiprocessor(block, shared).map_err(|e| device(e.into()))?,
                    };
                    p.attributes.insert((entry, block, shared), a);
                }
            }
        }
        Ok(())
    }

    /// A grid striding `cells` with one thread a cell.
    fn cells(cells: u64) -> u32 {
        cells.div_ceil(THREADS as u64).clamp(1, 65_535) as u32
    }

    /// A grid striding `rows` with one warp a row.
    fn warps(rows: u64) -> u32 {
        rows.div_ceil((THREADS / 32) as u64).clamp(1, 1 << 20) as u32
    }

    /// A grid of blocks of `per_block` warps, one warp a row.
    fn rows_grid(rows: u64, per_block: u64) -> u32 {
        rows.div_ceil(per_block).clamp(1, 1 << 20) as u32
    }


    /// A field's material, rings, skins and exponential uploaded once a run, and the words that read them; a tower's packets'
    /// field reads the fine field's resident exponential (`shared_face`). Returns the words, the buffers they point into and
    /// the octets of the resident face this upload holds.
    fn upload(&self, field: &Field, shared_face: Option<u64>) -> Result<(Words, Upload<'c>, u64)> {
        let d = field.declaration;
        let l = field.layout();
        let mut ring_off = Vec::new();
        let mut ring_n = Vec::new();
        let mut phasor = Vec::new();
        for (n, ring) in field.rings() {
            ring_off.push((phasor.len() / 2) as u64);
            ring_n.push(*n as u64);
            for &(re, im) in ring {
                phasor.extend([re, im]);
            }
        }
        // A field with no turned slot still uploads one word, so every buffer has an address.
        if phasor.is_empty() {
            phasor.extend([0, 0]);
            ring_off.push(0);
            ring_n.push(1);
        }
        // The skin decays, `[slot][d]` with stride the reach (one word where no slot is turned).
        let mut decay: Vec<i64> = field.decays().iter().flatten().copied().collect();
        if decay.is_empty() {
            decay.push(0);
        }

        // The skins `[h][d][n]` on 32 bits for the exposure's vector loads (eight modes a head; a still head's is the
        // exact 1).
        let mut decay_t: Vec<u32> = Vec::new();
        if d.modes == 8 {
            let (frames, still_sets, reach) = (d.frames, d.still, d.reach);
            let per_set = frames - still_sets;
            for h in 0..d.heads {
                let set = h % frames;
                let not_turned = set < still_sets;
                for gap in 0..reach {
                    for l in 0..8usize {
                        let v = if not_turned { 1 } else { decay[(l * per_set + set - still_sets) * reach + gap] };
                        decay_t.push(u32::try_from(v).map_err(|_| TowerError::Refused("a skin decay outside 32 bits"))?);
                    }
                }
            }
        }
        if decay_t.is_empty() {
            decay_t.push(0);
        }
        let roots: Vec<u64> = field.exponential().roots().iter().map(|&r| u64::try_from(r).map_err(|_| TowerError::Refused("the exponential's roots lie below 2^63"))).collect::<Result<_>>()?;
        // The material, the skin, the rings and the exponential's roots go up in one transfer.
        let mut pack = Packed::default();
        let (theta_at, decay_at, phasor_at, ring_off_at, ring_n_at, roots_at) = (pack.put(&field.theta), pack.put(&decay), pack.put(&phasor), pack.put(&ring_off), pack.put(&ring_n), pack.put(&roots));
        let decay_t_at = pack.put(&decay_t);
        // The temperatures' fine roots, past the resident face's sixteen (§16.12).
        let fine: Vec<u64> = field.fine_exponential().roots()[roots.len()..].iter().map(|&r| u64::try_from(r).map_err(|_| TowerError::Refused("the exponential's roots lie below 2^63"))).collect::<Result<_>>()?;
        let fine_at = pack.put(&fine);
        let run_pack = self.timed(Kind::Copy, || self.take_up(&pack.bytes)).map_err(device)?;
        let run_base = run_pack.device_ptr();
        if d.contacts % 2 != 0 {
            return Err(TowerError::Refused("a field's contacts are complex pairs (an even count)"));
        }
        if 2 * d.modes as u32 > CONTACT_SPAN {
            return Err(TowerError::Refused("the card's contact carries a span of at most 32 entries (16 modes a head)"));
        }
        // The crowds' slots a receiver keeps (two an octave `2^level < reach`, from the octave of four).
        if d.modes > MAX_MODES {
            return Err(TowerError::Refused("the card's rows carry at most 16 modes a head"));
        }
        // [theory, November 13, the junction record §7] The tick's return is built on the host, its card realization owed: a field with it is refused
        // here, so no card pass reads it as the built tick.
        if d.junction {
            return Err(TowerError::Refused("the junction's return has no card realization yet (the host's is the reference)"));
        }
        // [measurement; G161] The read's mirror at uniform strength is a host reading only.
        if field.mirror_strength.is_some() {
            return Err(TowerError::Refused("the read's mirror at uniform strength is a host reading, with no card realization"));
        }
        // [measurement; G176] The release's mark at a strength is a host ruler only.
        if field.mark.is_some() {
            return Err(TowerError::Refused("the release's mark at a strength is a host ruler, with no card realization"));
        }
        let slots = crowd_slots(d.reach);
        if slots > MAX_CROWD_SLOTS {
            return Err(TowerError::Refused("the declaration's reach holds more crowds than a warp keeps (32)"));
        }
        // The exponential's resident face: `2^digits` words, held beside the batches and counted
        // against the same budget.
        let face_octets = Some(roots.len()).filter(|&digits| digits < 61).map(|digits| 8u64 << digits).filter(|&o| o < self.budget).ok_or(TowerError::Refused("the exponential's resident face passes the card's batch budget"))?;
        let face_octets = if shared_face.is_some() { 0 } else { face_octets };
        let face = match shared_face {
            Some(_) => None,
            None => Some(self.timed(Kind::Alloc, || self.take::<u64>(1usize << roots.len())).map_err(device)?),
        };
        // The pairs met, one word a head (a reading: their sum is the run's count, each the head's own).
        let met = self.timed(Kind::Alloc, || self.take_zeroed::<u64>(d.heads)).map_err(device)?;
        let reach = |start: usize, len: usize| field.theta[start..start + len].iter().map(|v| v.unsigned_abs() as u64).max().unwrap_or(0);
        let (dw, m, n, f, a, heads) = (d.width, d.complex(), d.modes, d.contacts, d.alphabet, d.heads);
        let m2 = 2 * m;
        let ln2 = field.ln2();
        let mut words = Words {
            d: dw as u32,
            h: heads as u32,
            n: n as u32,
            still: d.still as u32,
            f: f as u32,
            a: a as u32,
            frames: d.frames as u32,
            lanes: d.lanes as u32,
            beta: d.score_shift(),
            ctrits: d.class_trits() as u32,
            nclasses: d.classes() as u32,
            dsbits: d.contact_return_bits(),
            m: m as u32,
            m2: m2 as u32,
            span: (2 * n) as u32,
            digits: roots.len() as u32,
            slots: slots as u32,
            band: band_bits(d.class_trits()),
            ln2_lo: ln2 as u64,
            ln2_hi: (ln2 >> 64) as u64,
            theta: run_base + theta_at,
            enc: l.enc as u64,
            enc_before: l.before as u64,
            enc_after: l.after as u64,
            q: l.q as u64,
            q_bias: l.q_bias as u64,
            v: l.v as u64,
            v_bias: l.v_bias as u64,
            out: l.out as u64,
            out_bias: l.out_bias as u64,
            wa: l.a as u64,
            a_bias: l.a_bias as u64,
            wb: l.b as u64,
            b_bias: l.b_bias as u64,
            w: l.w as u64,
            w_bias: l.w_bias as u64,
            read: l.read as u64,
            read_bias: l.read_bias as u64,
            rq: reach(l.q, m2 * dw),
            rv: reach(l.v, m2 * dw),
            rout: reach(l.out, dw * m2),
            ra: reach(l.a, f * dw),
            rg: reach(l.carry, 2 * d.carry * dw),
            wg: l.carry as u64,
            wgb: l.carry_bias as u64,
            carry: d.carry as u64,
            // [theory, November 12; the triad record §4] The triads' chart (`6J` rows of `D`) and return (`D` rows of `2J`), their reaches over the
            // families as the host's `Reaches` reads them (zero long, and so zero, where `J = 0`).
            triads: d.triads as u64,
            wt: l.triad as u64,
            wtb: l.triad_bias as u64,
            rt: reach(l.triad, 6 * d.triads * dw),
            wtr: l.w_triad as u64,
            rwt: reach(l.w_triad, dw * 2 * d.triads),
            rb: reach(l.b, f * dw),
            rw: reach(l.w, dw * f),
            rread: reach(l.read, dw * dw),
            phasor: run_base + phasor_at,
            ring_off: run_base + ring_off_at,
            ring_n: run_base + ring_n_at,
            decay: run_base + decay_at,
            decay_t: run_base + decay_t_at,
            dreach: d.reach as u64,
            roots: run_base + roots_at,
            met: met.device_ptr(),
            temper_at: l.temper as u64,
            fine_roots: run_base + fine_at,
            probe: l.probe as u64,
            probe_bias: l.probe_bias as u64,
            rprobe: reach(l.probe, m2 * dw),
            paced: d.paced_heads() as u32,
            pace_at: l.pace as u64,
            pi_lo: field.half_turn() as u64,
            pi_hi: (field.half_turn() >> 64) as u64,
            per_blank: u64::from(field.per_blank_clock),
            depth: d.depth as u64,
            bare_stretch: u64::from(field.bare_stretch),
            // [the ring record §4] The strengths `α_b`, read from the uploaded material at the second read (`run` sets the shares there).
            mark_at: l.mark as u64,
            ..Words::default()
        };
        // The exponential's resident face, read once by its own loop on the card (a tower's packets read the fine field's).
        match (&face, shared_face) {
            (Some(face), _) => {
                let mut face_ptr = face.device_ptr();
                self.launch("field_exponential", Self::cells(1u64 << roots.len()), THREADS, &mut [arg(&mut words), arg(&mut face_ptr)])?;
                words.face = face_ptr;
            }
            (None, Some(shared)) => words.face = shared,
            (None, None) => unreachable!("a face is made where none is shared"),
        }
        Ok((words, Upload { _pack: run_pack, _face: face, met }, face_octets))
    }

    /// Each region's faces (and their logits when `logits`) and, when `returning`, the covector
    /// over the regions; with `keep`, the still heads' last-tick weight rows of those sites of the one
    /// region read ([`FieldRealization::read_landmarks`]).
    #[allow(clippy::type_complexity)]
    fn run(&mut self, field: &Field, regions: &[Region], returning: bool, logits: bool, keep: Option<&[usize]>) -> Result<(Vec<Vec<Option<TowerFace>>>, Vec<Vec<Option<Vec<i64>>>>, Vec<i128>, Rows, Vec<Vec<u64>>)> {
        let d = field.declaration;
        for region in regions {
            if region.classes.len() != region.unresolved.len() || region.classes.len() < 2 {
                return Err(TowerError::Refused("a region needs one class and one resolution a site, and two sites to meet"));
            }
            if region.classes.len() > d.reach {
                return Err(TowerError::Refused("a region past the field's reach, where its frames would repeat"));
            }
            if region.classes.iter().any(|&c| c >= d.alphabet) {
                return Err(TowerError::Refused("a region's class outside the field's alphabet"));
            }
            if !region.faces.is_empty() && region.faces.len() != region.classes.len() {
                return Err(TowerError::Refused("a region's carried faces that are not one a site"));
            }
            if region.faces.iter().flatten().any(|face| face.is_empty() || face.iter().any(|&(c, w)| c as usize >= d.alphabet || w > 1 << STATE_BITS)) {
                return Err(TowerError::Refused("a carried face that is empty, or whose class is outside the alphabet or share past one"));
            }
            if !region.locked.is_empty() && (region.locked.len() != region.classes.len() || (0..region.classes.len()).any(|t| region.locked[t] && region.faces.get(t).and_then(Option::as_ref).is_none())) {
                return Err(TowerError::Refused("a region's locks that are not one a site, or a lock on a site that carries no face"));
            }
            if !region.echo.is_empty() && region.echo.len() != region.classes.len() {
                return Err(TowerError::Refused("a region's echoes that are not one a site"));
            }
            if region.echo.iter().flatten().any(|e| e.logits.len() != d.alphabet) {
                return Err(TowerError::Refused("an echo whose logits are not one a class"));
            }
        }
        self.mark("outside_the_card");
        let card = self.card;
        let started = Instant::now();
        let l = field.layout();
        let (mut words, upload, face_octets) = self.upload(field, None)?;
        // [measurement; theory, November 13, P56 item 4] The material's upload (it reads the state the section before left).
        self.mark("material_upload");
        // A tower's packets' level, uploaded beside the fine field once a run.
        let mut tower = match field.scale.as_deref() {
            Some(s) => Some(self.tower_run(field, s, words.face, returning)?),
            None => None,
        };
        let met = &upload.met;
        let heads = d.heads;
        let g = if returning { Some(self.timed(Kind::Alloc, || self.take_zeroed::<i128>(l.len)).map_err(device)?) } else { None };
        words.gcov = g.as_ref().map_or(0, |g| g.device_ptr());
        // The batches: whole regions in order, each batch's every allocation within the budget.
        // A landmark read stores one tick's weights beside a read's carriers; a logits read keeps every tick
        // and its shares (the echo's round trips, §15.3).
        // [G145] A level's epochs are at most its places, so its field is sized at the places, beside the fine chart at the split, the
        // epochs' harmonic blocks (restricted and returned) and each place's harmonics and epoch.
        let towered = field.scale.as_deref().map(|s| (s.coarse.declaration, s.harmonics));
        let octets = |sites: usize| {
            read_octets(&d, returning, logits, sites)
                + if keep.is_some() { 8 * (heads * sites * sites) as u64 } else { 0 }
                + towered.map_or(0, |(cd, h)| read_octets(&cd, returning, false, sites) + 20 * (sites * d.width) as u64 + 16 * (sites * h * d.width) as u64 + 8 * (sites * h) as u64 + 8 * sites as u64)
        };
        let lengths: Vec<usize> = regions.iter().map(|r| r.classes.len()).collect();
        if let Some(profile) = &self.profile {
            let mut p = profile.borrow_mut();
            if p.trace_on && p.trace.len() < TRACE_LAUNCHES {
                p.trace_regions.push((self.times.returns + self.times.reads, lengths.clone()));
            }
        }
        // [theory, November 12, P51] The clock's skins at the support stride: each region's own need, its definite sites read (the fine level only;
        // the tower's packets keep no store).
        let definite: Vec<usize> = regions.iter().map(definite_sites).collect();
        let skins: Vec<u64> = lengths.iter().zip(&definite).map(|(&n, &dd)| skin_octets(&d, n, dd).0).collect();
        let needs: Vec<u64> = lengths.iter().zip(&skins).map(|(&n, &sk)| octets(n) + sk).collect();
        // A pooled buffer is at most a quarter longer than asked (its size class), so the batches are cut at four
        // fifths of the budget.
        let cut = (self.budget - face_octets) / 5 * 4;
        self.times.batch_cut = cut;
        let batches = batches_of(&lengths, &needs, cut)?;
        if keep.is_some() && (regions.len() != 1 || returning) {
            return Err(TowerError::Refused("the weight rows are read from one region's forward"));
        }
        let mut faces: Vec<Vec<Option<TowerFace>>> = Vec::with_capacity(regions.len());
        let mut read_logits: Vec<Vec<Option<Vec<i64>>>> = Vec::new();
        let mut echoes: Vec<Vec<u64>> = Vec::new();
        let mut rows = Rows::new();
        for batch in batches {
            if batch.is_empty() {
                continue;
            }
            let peak = needs[batch.clone()].iter().sum::<u64>();
            self.times.peak_store = self.times.peak_store.max(peak);
            let store = skins[batch.clone()].iter().sum::<u64>();
            let entries = batch.clone().map(|r| (lengths[r] * (2 * (NEAR - 1) + definite[r])) as u64).sum::<u64>();
            let dense = lengths[batch.clone()].iter().map(|&n| (n * n) as u64).sum::<u64>();
            let t = &mut self.times;
            (t.skin_entry_octets, t.skin_site_octets, t.clock_site_octets) = (skin_octets(&d, 0, 0).1, skin_octets(&d, 0, 0).2, skin_octets(&d, 0, 0).3);
            t.skin_store = t.skin_store.max(store);
            (t.skin_entries, t.skin_dense_pairs) = (t.skin_entries + u128::from(entries), t.skin_dense_pairs + u128::from(dense));
            if entries > t.skin_peak_entries {
                (t.skin_peak_entries, t.skin_peak_pairs) = (entries, dense);
            }
            self.times.batches += 1;
            self.mark("run_setup");
            // [definition; agent-inferred, November 14, the ring record §4] **The field that reads twice** (the host's `Field::pass`): the batch's
            // first read is the built read, no readings and no return, and leaves each silent site's shares of its face on the card
            // (`field_mark_shares`); the second read opens each silent site on its mark and is the batch's read, its faces, readings and return
            // the field's. A region's marks are its own first read's, so the two reads run batch by batch. [realization; agent-inferred, November 14]
            // Both stand on one base (`batch_base`): what comes before the opening is formed once a batch.
            let mut base = self.batch_base(field, &regions[batch.clone()], &mut words, tower.as_mut(), returning)?;
            let (f, z, r, e) = if d.mark {
                let mut shares = None;
                self.batch(field, &regions[batch.clone()], batch.start, &mut words, &mut base, None, false, None, tower.as_mut(), Some(&mut shares))?;
                let shares = shares.ok_or(TowerError::Refused("a field's first read that left no shares for its marks"))?;
                self.mark("mark_first_read");
                words.mark_share = shares.device_ptr();
                let read = self.batch(field, &regions[batch.clone()], batch.start, &mut words, &mut base, g.as_deref(), logits, keep, tower.as_mut(), None);
                words.mark_share = 0;
                drop(shares);
                read?
            } else {
                self.batch(field, &regions[batch.clone()], batch.start, &mut words, &mut base, g.as_deref(), logits, keep, tower.as_mut(), None)?
            };
            drop(base);
            self.mark("batch_drop_and_collect");
            faces.extend(f);
            read_logits.extend(z);
            rows.extend(r);
            echoes.extend(e);
        }
        let mut g = match g {
            Some(g) => self.timed(Kind::Copy, || card.fetch_range(&g, 0, l.len)).map_err(device)?,
            None => Vec::new(),
        };
        // [measurement; theory, November 13, P56 item 4] The covector's fetch.
        self.mark("covector_fetch");
        // A tower's covector over its whole material: the fine field's, the packets' field's and the glue's.
        if let (Some(tr), Some(s), true) = (tower.as_ref(), field.scale.as_deref(), returning) {
            if let (Some(cg), Some(gg)) = (tr.cg.as_ref(), tr.gg.as_ref()) {
                g.extend(self.timed(Kind::Copy, || card.fetch_range(cg, 0, s.coarse.theta.len())).map_err(device)?);
                g.extend(self.timed(Kind::Copy, || card.fetch_range(gg, 0, s.glue.len())).map_err(device)?);
            }
        }
        let met_by_head = self.timed(Kind::Copy, || card.fetch_range(met, 0, heads)).map_err(device)?;
        let met = met_by_head.iter().map(|&m| u128::from(m)).sum::<u128>();
        if keep.is_some() {
            // A landmark read is a reading of a release's last state, counted apart.
            self.times.landmarks += 1;
            self.times.landmark_ns += started.elapsed().as_nanos();
            return Ok((faces, read_logits, g, rows, echoes));
        }
        self.times.pairs += met;
        if let Some(profile) = &self.profile {
            let mut p = profile.borrow_mut();
            if p.pairs_by_head.len() < heads {
                p.pairs_by_head.resize(heads, 0);
            }
            for (h, &m) in met_by_head.iter().enumerate() {
                p.pairs_by_head[h] += u128::from(m);
            }
        }
        if returning {
            self.times.returns += 1;
            self.times.return_ns += started.elapsed().as_nanos();
        } else {
            self.times.reads += 1;
            self.times.read_ns += started.elapsed().as_nanos();
        }
        // [measurement; theory, November 13, P56 item 4] The run's end: the next run's `outside_the_card` is the host's time between runs.
        self.mark("run_end");
        Ok((faces, read_logits, g, rows, echoes))
    }

    fn tick(&self, sites: usize, pairs: usize, regions: usize, field: &Field, stored: bool, returning: bool, dense: bool) -> Result<Tick<'c>> {
        let d = field.declaration;
        let rows = sites + regions;
        let slots = crowd_slots(d.reach);
        let (dw, m2, f, heads, span, lanes) = (d.width, 2 * d.complex(), d.contacts, d.heads, 2 * d.modes, d.lanes);
        let classes = d.classes();
        // A receiver's probed classes: its probe's own and the `2^b − 1` across its seams (§16.19).
        let probe_stride = 1usize << d.class_trits();
        let card = self.card;
        let alloc64 = |len: usize| self.timed(Kind::Alloc, || self.take::<i64>(len.max(1))).map_err(device);
        let alloc32 = |len: usize| self.timed(Kind::Alloc, || self.take::<u32>(len.max(1))).map_err(device);
        // [theory, November 12; the triad record §4] A triads' carrier `[t][rows J]`, none where the field has no triads.
        let triads = d.triads;
        let triad = |rows: usize| if triads > 0 { alloc64(sites * rows * triads).map(Some) } else { Ok(None) };
        Ok(Tick {
            read: self.timed(Kind::Alloc, || self.take::<i32>((sites * dw).max(1))).map_err(device)?,
            scale: self.timed(Kind::Alloc, || self.take::<i128>((sites * lanes).max(1))).map_err(device)?,
            qkv: alloc64(sites * 2 * m2)?,
            qf: alloc64(heads * sites * span)?,
            qf32: self.take::<i32>(heads * sites * span).map_err(device)?,
            pq: alloc64(heads * sites * span)?,
            pq32: self.take::<i32>(heads * sites * span).map_err(device)?,
            pscale: self.take::<i128>((heads * sites).max(1)).map_err(device)?,
            vf: alloc64(heads * sites * span)?,
            qscale: self.timed(Kind::Alloc, || self.take::<i128>((heads * sites).max(1))).map_err(device)?,
            cls: alloc32(heads * sites)?,
            class_off: alloc32(heads * regions * (2 * classes + 1))?,
            members: alloc32(heads * sites)?,
            pn: alloc32(heads * sites)?,
            pcls: alloc32(heads * sites * probe_stride)?,
            poff: alloc32(heads * regions * (classes + 1))?,
            pmem: alloc32(heads * sites * probe_stride)?,
            // The shares are zeroed where the echo reads another tick's (a pair absent from a row reads zero).
            // The pairs' scores, then their shares, a word a pair; zeroed where the echo reads another tick's (a
            // pair absent from a row reads zero), else only the support's entries are ever written and read.
            sb: self.take::<i64>(if returning { (heads * pairs).max(1) } else { 1 }).map_err(device)?,
            // [theory, November 13, P56 step 6] Taken without its zeroing where no dense reader runs (`dense`, at the call): every other word read is
            // written first in the same tick. The exposure (`field_exposure`) writes the score at every support entry `[i][j]` of every computed row of
            // every head; the contact (`contact_body`) reads it there and writes the share there; the rows, the skin's return and the rulers read only
            // those entries of computed rows, and the columns read them at the pairs whose covector `ds` they read beside, which is an unzeroed take
            // the rows write only at support entries. No reader meets an entry outside a computed row's support.
            e: if stored && dense { self.timed(Kind::Alloc, || self.take_zeroed::<u64>((heads * pairs).max(1))).map_err(device)? } else { self.timed(Kind::Alloc, || self.take::<u64>((heads * pairs).max(1))).map_err(device)? },
            amin: alloc64(heads * sites)?,
            sw: self.timed(Kind::Alloc, || self.take::<i128>((heads * rows * span).max(1))).map_err(device)?,
            sv: self.timed(Kind::Alloc, || self.take::<i128>((heads * rows * span).max(1))).map_err(device)?,
            sc: self.timed(Kind::Alloc, || self.take::<u64>((heads * rows).max(1))).map_err(device)?,
            ce: self.timed(Kind::Alloc, || self.take::<u64>(if stored { (heads * sites * slots).max(1) } else { 1 })).map_err(device)?,
            y: alloc64(sites * m2)?,
            read2: self.timed(Kind::Alloc, || self.take::<i32>((sites * dw).max(1))).map_err(device)?,
            scale2: self.timed(Kind::Alloc, || self.take::<i128>((sites * lanes).max(1))).map_err(device)?,
            pa: alloc64(sites * f)?,
            pg: alloc64(if field.declaration.carry > 0 { sites * 2 * field.declaration.carry } else { 1 })?,
            pgam: alloc64(if field.declaration.carry > 0 { sites * 2 * field.declaration.carry } else { 1 })?,
            pqm: alloc64(if field.declaration.carry > 0 { sites * 2 * field.declaration.carry } else { 1 })?,
            pkb: alloc64(if field.declaration.carry > 0 { sites * 2 * field.declaration.carry } else { 1 })?,
            pb: alloc64(sites * f)?,
            pc: alloc64(sites * f)?,
            pabg: triad(6)?,
            ptp: triad(2)?,
            pct: triad(2)?,
            bits: self.timed(Kind::Alloc, || self.take_zeroed::<u32>(4)).map_err(device)?,
        })
    }

    /// A batch's site and region tables uploaded in one transfer, its status word and its faces' buffer, and the words
    /// that read them (the host's tables kept beside them for the reverse and the readings).
    fn stage(&self, regions: &[Region], a: usize, dw: usize, declaration: &FieldDeclaration, words: &mut Words) -> Result<Staged<'c>> {
        let ticks = declaration.ticks;
        // The batch's sites, region by region, and the carried mixtures as one list a site.
        let mut site_region = Vec::new();
        let mut site_pos = Vec::new();
        let mut region_off = vec![0u32];
        let mut region_eoff = Vec::new();
        // [theory, November 12, P51] The skins' support stride: each region's prefix of `S_r K_r`, and their sum.
        let (mut region_soff, mut skin_entries) = (Vec::<u64>::new(), 0usize);
        let mut classes = Vec::new();
        let mut unresolved = Vec::new();
        // A definite site (§14.1): known (resolved, carrying no mixture) or locked (a foil).
        let mut definite = Vec::new();
        // Each site's echo (§15.3): its `B`, and its logits a class (zero where none).
        let (mut echo_has, mut echo_b, mut echo_logits) = (Vec::new(), Vec::new(), Vec::new());
        let (mut mix_off, mut mix_class, mut mix_share) = (vec![0u32], Vec::new(), Vec::new());
        let mut pairs = 0usize;
        let any_echo = regions.iter().any(|r| r.echo.iter().any(Option::is_some));
        // [E] The cut rooms' windows, each site's row computed or not (every site of an uncut region); kept whole where the field has carry
        // circles (the host's `FieldDeclaration::room_window`, the one owner of the cut's admission).
        let windows: Vec<Option<Vec<bool>>> = regions.iter().map(|r| declaration.room_window(r)).collect();
        let (per_blank, bare) = (words.per_blank != 0, words.bare_stretch != 0);
        let blank_read: Vec<u8> = regions
            .iter()
            .flat_map(|r| {
                let silent = |t: usize| r.unresolved[t] && r.faces.get(t).and_then(Option::as_ref).is_none();
                let s = r.classes.len();
                let stretch = if per_blank { s } else { (0..s).rev().find(|&t| !silent(t)).map_or(0, |last| last + 1) };
                // Under the bare stretch no place past the last arrival reads a face, its first among them.
                let read_to = if bare && !per_blank { stretch } else { stretch + 1 };
                (0..s).map(move |t| u8::from(silent(t) && t < read_to))
            })
            .collect();
        let computed: Vec<u8> = if windows.iter().any(Option::is_some) { regions.iter().zip(&windows).flat_map(|(r, w)| (0..r.classes.len()).map(move |t| u8::from(w.as_ref().is_none_or(|w| w[t])))).collect() } else { Vec::new() };
        // Each region's definite sites and its open ones, by place (§15.9: an open receiver hears every definite
        // site, and a definite source is heard by every open one).
        let (mut dlist, mut dstart, mut olist, mut ostart) = (Vec::<u32>::new(), Vec::<u32>::new(), Vec::<u32>::new(), Vec::<u32>::new());
        // Each site's region's weight in the joint code (§16.23, `Region::weight`), for the reverse.
        let mut site_weight: Vec<(u64, u64)> = Vec::new();
        for (r, region) in regions.iter().enumerate() {
            let s = region.classes.len();
            let weight = region.weight();
            site_weight.extend(std::iter::repeat_n(weight, s));
            region_eoff.push(pairs as u64);
            pairs += s * s;
            region_soff.push(skin_entries as u64);
            dstart.push(dlist.len() as u32);
            ostart.push(olist.len() as u32);
            for t in 0..s {
                site_region.push(r as u32);
                site_pos.push(t as u32);
                classes.push(region.classes[t] as u32);
                unresolved.push(u8::from(region.unresolved[t]));
                let carried = region.faces.get(t).and_then(Option::as_ref).is_some();
                let is_definite = (!region.unresolved[t] && !carried) || region.locked.get(t).copied().unwrap_or(false);
                definite.push(u8::from(is_definite));
                if is_definite {
                    dlist.push(t as u32);
                } else if windows[r].as_ref().is_none_or(|w| w[t]) {
                    // [E] A definite source is heard by every open receiver its region computes (the host's `Field::tick`
                    // skips the rest), so the receivers its return walks are those alone.
                    olist.push(t as u32);
                }
                match region.echo.get(t).and_then(Option::as_ref) {
                    Some(e) => {
                        echo_has.push(1u8);
                        echo_b.push(e.b);
                        echo_logits.extend_from_slice(&e.logits);
                    }
                    None => {
                        echo_has.push(0u8);
                        echo_b.push(0u64);
                        // (the logits are read only where a site carries an echo, so a batch with none keeps none)
                        if any_echo {
                            echo_logits.extend(std::iter::repeat_n(0i64, a));
                        }
                    }
                }
                for &(c, w) in region.faces.get(t).and_then(Option::as_ref).into_iter().flatten() {
                    mix_class.push(c);
                    mix_share.push(w);
                }
                mix_off.push(mix_class.len() as u32);
            }
            region_off.push(site_region.len() as u32);
            // [theory, November 12, P51] The region's support stride `K_r = NEAR_SLOTS + D_r` a row (the clock's skins).
            skin_entries += s * (2 * (NEAR - 1) + dlist.len() - *dstart.last().expect("the region's definite list opened") as usize);
        }
        region_soff.push(skin_entries as u64);
        let sites = site_region.len();
        dstart.push(dlist.len() as u32);
        ostart.push(olist.len() as u32);
        if dlist.is_empty() {
            dlist.push(0);
        }
        if olist.is_empty() {
            olist.push(0);
        }
        if echo_logits.is_empty() {
            echo_logits.push(0i64);
        }
        // A batch with no carried site still uploads one word, so every buffer has an address.
        let (mix_class_up, mix_share_up) = if mix_class.is_empty() { (vec![0u32], vec![0u32]) } else { (mix_class.clone(), mix_share.clone()) };
        // The batch's site and region tables go up in one transfer.
        // [measurement; theory, November 13, P56 item 4] The batch's lists and tables, built from its regions and the declaration alone.
        self.mark("stage_lists");
        let mut pack = Packed::default();
        let site_region_at = pack.put(&site_region);
        let site_pos_at = pack.put(&site_pos);
        let region_off_at = pack.put(&region_off);
        let region_eoff_at = pack.put(&region_eoff);
        let classes_at = pack.put(&classes);
        let unresolved_at = pack.put(&unresolved);
        let definite_at = pack.put(&definite);
        let computed_at = (!computed.is_empty()).then(|| pack.put(&computed));
        let blank_read_at = pack.put(&blank_read);
        let echo_has_at = pack.put(&echo_has);
        let echo_b_at = pack.put(&echo_b);
        let echo_logits_at = pack.put(&echo_logits);
        let mix_off_at = pack.put(&mix_off);
        let mix_class_at = pack.put(&mix_class_up);
        let mix_share_at = pack.put(&mix_share_up);
        let (dlist_at, dstart_at, olist_at, ostart_at) = (pack.put(&dlist), pack.put(&dstart), pack.put(&olist), pack.put(&ostart));
        let region_soff_at = pack.put(&region_soff);
        // [theory, November 12, P50 step 2] The moment modes' map (the moment kernels' `cmap`, `moment_modes`), for the clock's fill.
        let d = declaration;
        let mcmap: Vec<u32> = (0..d.heads).filter(|&h| d.carries_moment(h)).flat_map(|h| (0..d.modes).map(move |li| (h * d.modes + li) as u32 | if d.is_depth(h) { 1 << 31 } else { 0 })).collect();
        let mcmap_at = pack.put(if mcmap.is_empty() { &[0u32][..] } else { &mcmap[..] });
        let tables = self.timed(Kind::Copy, || self.take_up(&pack.bytes)).map_err(device)?;
        self.mark("stage_pack_upload");
        let base = tables.device_ptr();
        let status = self.timed(Kind::Alloc, || self.take_zeroed::<u32>(1)).map_err(device)?;
        let x = self.timed(Kind::Alloc, || self.take::<i64>(sites * dw)).map_err(device)?;
        words.t = sites as u32;
        words.r = regions.len() as u32;
        words.pairs = pairs as u64;
        words.site_region = base + site_region_at;
        words.site_pos = base + site_pos_at;
        words.region_off = base + region_off_at;
        words.region_eoff = base + region_eoff_at;
        words.classes = base + classes_at;
        words.unresolved = base + unresolved_at;
        words.definite = base + definite_at;
        words.computed = computed_at.map_or(0, |at| base + at);
        words.blank_read = base + blank_read_at;
        words.echo_has = base + echo_has_at;
        words.echo_b = base + echo_b_at;
        words.echo_logits = base + echo_logits_at;
        words.mix_off = base + mix_off_at;
        words.mix_class = base + mix_class_at;
        words.mix_share = base + mix_share_at;
        words.region_soff = base + region_soff_at;
        (words.mcmap, words.tm) = (base + mcmap_at, mcmap.len() as u64);
        words.skin_entries = skin_entries as u64;
        words.dlist = base + dlist_at;
        words.dstart = base + dstart_at;
        words.olist = base + olist_at;
        words.ostart = base + ostart_at;
        words.status = status.device_ptr();
        words.x = x.device_ptr();
        Ok(Staged { site_region, site_pos, region_off, classes, unresolved, definite, echo_has, mix_off, mix_class, mix_share, site_weight, pairs, skin_entries, sites, _tables: tables, status, x })
    }

    /// One tick of the constitution on the card over the staged sites of `words` (the host's `Field::tick`), its temporaries in
    /// `ticks[k]` (or the one shared tick where none is kept).
    #[allow(clippy::too_many_arguments)]
    fn tick_forward(&self, field: &Field, words: &mut Words, ticks: &[Tick<'c>], k: usize, kept: bool, stored: bool, keep_last: bool, logits: bool, returning: bool, pr: u64, sites: usize, pairs: usize, regions: usize) -> Result<()> {
        let card = self.card;
        let d = field.declaration;
        let (dw, m2, f, n, heads) = (d.width, 2 * d.complex(), d.contacts, d.modes, d.heads);
        let span = 2 * n;
        let buckets = 4 * 3 * d.classes() as u32;
        let tick = &ticks[if kept { k } else { 0 }];
        set_tick(words, tick, returning);
        self.chart(words, words.x, &tick.read, &tick.scale, false)?;
        for (part, weight, bias, wmax) in [(0usize, words.q, words.q_bias, words.rq), (1, words.v, words.v_bias, words.rv)] {
            let out = tick.qkv.device_ptr() + (part * m2 * 8) as u64;
            self.affine("field_affine_x32", words, weight, bias, wmax, m2, dw, tick.read.device_ptr(), dw, out, 2 * m2, 0, false)?;
        }
        // A value is linear in its site's moment (§15.1).
        self.launch("field_moment_add", Self::cells((sites * m2) as u64), THREADS, &mut [arg(words)])?;
        card.zero_octets(&tick.bits, 0, 16).map_err(device)?;
        // Every receiver's probe (§16.19), before the classes: a receiver's probed classes are its probe's.
        self.affine("field_affine_x32", words, words.probe, words.probe_bias, words.rprobe, m2, dw, tick.read.device_ptr(), dw, pr, m2, 0, false)?;
        // Its probe reads its moment, as its value does (§16.20).
        let mut prp = pr;
        self.launch("field_moment_add_probe", Self::cells((sites * m2) as u64), THREADS, &mut [arg(words), arg(&mut prp)])?;
        self.launch_shared("field_classes", (heads * regions).clamp(1, 1 << 20) as u32, 32, buckets, &mut [arg(words)])?;
        self.launch("field_frame", Self::cells((heads * sites * n) as u64), THREADS, &mut [arg(words)])?;
        let mut qs = tick.qscale.device_ptr();
        self.launch("field_unit", Self::warps((heads * sites) as u64), THREADS, &mut [arg(words), arg(&mut qs)])?;
        self.launch("field_frame_probe", Self::cells((heads * sites * n) as u64), THREADS, &mut [arg(words)])?;
        let mut ps = tick.pscale.device_ptr();
        self.launch("field_unit_probe", Self::warps((heads * sites) as u64), THREADS, &mut [arg(words), arg(&mut ps)])?;
        // The definite sites' prefix sums (§14.10), read by the contact's crowds.
        self.launch("field_sums", Self::cells((heads * regions * (2 * span + 1)) as u64), THREADS, &mut [arg(words)])?;
        // The clock's skins, formed once for the exposure and the contact (the return forms them again for this tick's clock).
        self.skin_fill(field, words, sites)?;
        #[cfg(feature = "ruler-bits")]
        {
            let rows1 = sites + regions;
            for (arr, kind, count, at) in [(words.vf, 0, heads * sites * span, 13), (words.qf, 0, heads * sites * span, 14), (words.pq, 0, heads * sites * span, 15), (words.qf32, 1, heads * sites * span, 16), (words.pq32, 1, heads * sites * span, 17), (words.sc, 3, heads * rows1, 19), (words.sw, 2, heads * rows1 * span, 20), (words.sv, 2, heads * rows1 * span, 21)] {
                self.bits_words(arr, kind, count, at, k)?;
            }
            if words.skin != 0 {
                for h in (0..heads).filter(|&h| d.carries_moment(h) && !d.is_depth(h)) {
                    for l in 0..n {
                        self.bits_pairs(words, h, 4, l as u32, words.skin, 5 + l, k, sites)?;
                    }
                }
            }
        }
        let mut store = u32::from(stored);
        if keep_last && k + 1 == d.ticks {
            // The last tick's rows are read whole: the entries outside its support read zero.
            card.zero_octets(&tick.e, 0, 8 * heads * pairs).map_err(device)?;
        }
        // [definition; agent-inferred, November 1] **The series row's carrier is as wide as the exponents
        // its rows hold** (§14.11, §15.2: width is dynamic, never arbitrary): the exposure reads each row's
        // least whole bit and the widest spread any row of the launch holds, and the contact is launched
        // with the limbs that spread needs, never past the declaration's bound (`row_bits`), where a row
        // is refused.
        let rows_per_block = CONTACT_ROWS;
        self.mark("tick_launch_pre");
        self.launch("field_exposure", Self::rows_grid((heads * sites) as u64, rows_per_block), (rows_per_block * 32) as u32, &mut [arg(words)])?;
        #[cfg(feature = "ruler-bits")]
        for h in 0..heads {
            // The score is a signed word (`scored`), read as one; the share after the contact is a 63-bit fraction, read unsigned.
            self.bits_pairs(words, h, 1, 0, words.e, 0, k, sites)?;
            if words.sb != 0 {
                self.bits_pairs(words, h, 1, 0, words.sb, 2, k, sites)?;
            }
        }
        let spread = self.timed(Kind::Copy, || card.fetch(&tick.bits)).map_err(device)?[1] as u64;
        if std::env::var_os("FIELD_SPREAD").is_some() {
            let need = field.row_bits().ok().zip(field.row_gain().ok()).map(|(bits, gain)| bits as i64 - (gain as i64 + (usize::BITS - 1 - d.reach.leading_zeros()) as i64 + 2) + spread as i64);
            eprintln!("FIELD_SPREAD tick={k} sites={sites} spread={spread} need_bits={} bound_limbs={}", need.map_or("-".to_string(), |n| n.to_string()), row_limbs(field, spread).map_or(0, |l| l));
        }
        self.mark("tick_exposure_wait");
        let limbs = row_limbs(field, spread)?;
        let contact: &'static str = ["field_contact_l5", "field_contact_l6", "field_contact_l7", "field_contact_l8", "field_contact_l9", "field_contact_l10", "field_contact_l11", "field_contact_l12", "field_contact_l13", "field_contact_l14", "field_contact_l15", "field_contact_l16", "field_contact_l17", "field_contact_l18", "field_contact_l19", "field_contact_l20"][limbs - MIN_LIMBS];
        self.launch(contact, Self::rows_grid((heads * sites) as u64, rows_per_block), (rows_per_block * 32) as u32, &mut [arg(words), arg(&mut store)])?;
        #[cfg(feature = "ruler-bits")]
        if store != 0 {
            for h in 0..heads {
                self.bits_pairs(words, h, 0, 0, words.e, 1, k, sites)?;
                self.bits_pairs(words, h, 5, 0, words.ce, 18, k, sites)?;
                if h < 4 {
                    self.bits_pairs(words, h, 6, (BITS_TICKS * BITS_BINS) as u32, words.e, 22 + 2 * h, k, sites)?;
                }
            }
        }
        // The echo's round trips of this tick against the last (§15.3).
        if logits && k > 0 {
            words.e_prev = ticks[k - 1].e.device_ptr();
            self.launch("field_echo_trips", Self::rows_grid((heads * sites) as u64, rows_per_block), (rows_per_block * 32) as u32, &mut [arg(words)])?;
        }
        self.affine("field_affine_x64", words, words.out, words.out_bias, words.rout, dw, m2, tick.y.device_ptr(), m2, 0, dw, words.x, false)?;
        self.chart(words, words.x, &tick.read2, &tick.scale2, false)?;
        self.affine("field_affine_x32", words, words.wa, words.a_bias, words.ra, f, dw, tick.read2.device_ptr(), dw, tick.pa.device_ptr(), f, 0, false)?;
        self.affine("field_affine_x32", words, words.wb, words.b_bias, words.rb, f, dw, tick.read2.device_ptr(), dw, tick.pb.device_ptr(), f, 0, false)?;
        // The plain contacts, the first `f/2 − C`: one thread a site and contact.
        let (plain, circles) = (d.carry_first(), d.carry);
        if plain > 0 {
            self.launch("field_pair", Self::cells((sites * plain) as u64), THREADS, &mut [arg(words)])?;
        }
        if circles > 0 {
            // [theory, November 11 17:25 and November 12 (G98)] The carry circles: their charts' reads `q`, `ℓ` (one affine with its bias), the gate's
            // two divisions and the drive's coupling through the leak off the chain on the pair's grid (one thread a site and circle, as
            // tower.field-scan-gate-once-a-site moved the root out), then the chain, one thread a (region, circle) in strand order.
            self.affine("field_affine_x32", words, words.wg, words.wgb, words.rg, 2 * circles, dw, tick.read2.device_ptr(), dw, tick.pg.device_ptr(), 2 * circles, 0, false)?;
            self.launch("field_pair_gamma", Self::cells((sites * circles) as u64), THREADS, &mut [arg(words)])?;
            self.launch("field_pair_scan", Self::cells((words.r as usize * circles) as u64), THREADS, &mut [arg(words)])?;
        }
        let triads = d.triads;
        if triads > 0 {
            // [definition; theory, November 12; the triad record §3 and §4] The triads, after the carry scan and before the return: their chart's read
            // `abg` (one affine with its bias over the pair chart, at the grains `a` and `b` are read at), then the products `p` and `c^T` a site and
            // triad on the pair's grid (zero at a region's two ends); then the return's two blocks, `W c` and `W_T c^T`, summed whole in one wide sum
            // with the bias before its one release and added into `x`, the joint carrier bound read over both blocks.
            self.affine("field_affine_x32", words, words.wt, words.wtb, words.rt, 6 * triads, dw, tick.read2.device_ptr(), dw, words.pabg, 6 * triads, 0, false)?;
            self.launch("field_triad", Self::cells((sites * triads) as u64), THREADS, &mut [arg(words)])?;
            self.affine_two(words, (words.w, words.w_bias, words.rw, dw, f, tick.pc.device_ptr(), f), (words.wtr, words.rwt, 2 * triads, words.pct, 2 * triads), words.x)?;
        } else {
            self.affine("field_affine_x64", words, words.w, words.w_bias, words.rw, dw, f, tick.pc.device_ptr(), f, 0, dw, words.x, false)?;
        }
        self.mark("tick_launch_post");
        Ok(())
    }

    /// [definition; agent-inferred, November 3] **A tower's packets' level on the card** (the host's `field::scale`): the
    /// packets' field uploaded beside the fine one (reading its resident exponential), the glue uploaded, and each level's
    /// covector where the run returns one.
    fn tower_run(&self, field: &Field, s: &Scale, face: u64, returning: bool) -> Result<TowerRun<'c>> {
        let (mut cwords, cup, _) = self.upload(&s.coarse, Some(face))?;
        let glue = self.timed(Kind::Copy, || self.take_up(&s.glue)).map_err(device)?;
        let offsets = s.glue_offsets(field.declaration.width);
        let (a, ab, b, bb, len) = offsets;
        let reach = |from: usize, to: usize| s.glue[from..to].iter().map(|v| v.unsigned_abs() as u64).max().unwrap_or(0);
        let cg = if returning { Some(self.timed(Kind::Alloc, || self.take_zeroed::<i128>(s.coarse.theta.len())).map_err(device)?) } else { None };
        let gg = if returning { Some(self.timed(Kind::Alloc, || self.take_zeroed::<i128>(len)).map_err(device)?) } else { None };
        cwords.gcov = cg.as_ref().map_or(0, |g| g.device_ptr());
        let _ = (ab, bb);
        Ok(TowerRun { cwords, glue_at: glue.device_ptr(), _cup: cup, _glue: glue, cg, gg, harmonics: s.harmonics, split: s.split, section: level_section(field.declaration.alphabet), pi: field.half_turn(), offsets, reach_a: reach(a, offsets.1), reach_b: reach(b, offsets.3) })
    }

    /// A batch's epochs staged as the level's field's regions (an epoch definite where its every place is, keyed where any is: unresolved
    /// and carrying class 0 where keyed and not definite), each region cut from its places' `news` by the host's `level_cut`; each fine
    /// place's epoch and harmonics, the epochs' fine offsets, the level's clocks uploaded as the cut gives them and its per-pass buffers.
    /// [realization; agent-inferred, November 14, the ring record §4] The level's ticks are each read's own ([`CardField::level_ticks`]): the
    /// news is the opening's comparison's face, which no mark enters (the host's `Field::level_news` reads `cavity_forward`), so a field that reads
    /// twice cuts its level once a batch and both reads stand on the cut.
    fn tower_batch(&self, field: &Field, tr: &mut TowerRun<'c>, fine: &Staged<'c>, regions: usize, news: &[i64]) -> Result<TowerBatch<'c>> {
        let s = field.scale.as_deref().ok_or(TowerError::Refused("a level's batch of a field without a level"))?;
        let coarse = &s.coarse;
        let cd = coarse.declaration;
        let h = tr.harmonics;
        let carried = vec![(0u32, 1u32 << 16)];
        let mut owned: Vec<(Vec<usize>, Vec<bool>, Vec<Option<Vec<(u32, u32)>>>)> = Vec::with_capacity(regions);
        let (mut epoch_of, mut harm, mut off, mut taus) = (Vec::with_capacity(fine.sites), Vec::with_capacity(fine.sites * h), Vec::new(), Vec::with_capacity(regions));
        for r in 0..regions {
            let (first, end) = (fine.region_off[r] as usize, fine.region_off[r + 1] as usize);
            let cut = level_cut(&news[first..end], tr.section, h, tr.pi)?;
            let base = off.len() as u32;
            let epochs = cut.anchors.len();
            let (mut unres, mut faces) = (Vec::with_capacity(epochs), Vec::with_capacity(epochs));
            for j in 0..epochs {
                let span = first + cut.anchors[j]..first + cut.anchors.get(j + 1).copied().unwrap_or(end - first);
                off.push(span.start as u32);
                let definite = span.clone().all(|t| fine.definite[t] != 0);
                let keyed = span.clone().any(|t| fine.unresolved[t] == 0 || fine.mix_off[t + 1] != fine.mix_off[t]);
                unres.push(!definite);
                faces.push((keyed && !definite).then(|| carried.clone()));
            }
            epoch_of.extend(cut.epoch.iter().map(|&j| base + j as u32));
            harm.extend_from_slice(&cut.harmonics);
            taus.push(cut.tau);
            owned.push((vec![0usize; epochs], unres, faces));
        }
        off.push(fine.sites as u32);
        let pregions: Vec<Region> = owned.iter().map(|(c, u, f)| Region { classes: c, unresolved: u, faces: if f.iter().any(Option::is_some) { f } else { &[] }, locked: &[], echo: &[], domain: None, port: None }).collect();
        let st = self.stage(&pregions, cd.alphabet, cd.width, &cd, &mut tr.cwords)?;
        let (sites, m2, n) = (st.sites, 2 * cd.complex(), cd.modes);
        let trips = self.timed(Kind::Alloc, || self.take_zeroed::<i128>(sites.max(1))).map_err(device)?;
        tr.cwords.trips = trips.device_ptr();
        // The level carries no moments: its values and probes read zero there.
        let moment = self.timed(Kind::Alloc, || self.take_zeroed::<i64>((sites * m2).max(1))).map_err(device)?;
        tr.cwords.moment = moment.device_ptr();
        let pr = self.timed(Kind::Alloc, || self.take::<i64>((sites * m2).max(1))).map_err(device)?;
        tr.cwords.pr = pr.device_ptr();
        // The level's clock (the host's `level_paces`): every turned head on the news between the epochs' anchors, uploaded as the cut
        // gives it; the frames and the skins' addresses then follow by the fine field's own laws on the level's strand.
        let paced = cd.paced_heads();
        let one = 1i64 << PACE_BITS;
        let (mut kappa, mut tau, mut plain) = (Vec::with_capacity(paced * sites), Vec::with_capacity(paced * sites), Vec::with_capacity(paced * regions));
        for _ in 0..paced {
            for t in &taus {
                tau.extend_from_slice(t);
                kappa.extend((0..t.len()).map(|j| if j == 0 { one } else { t[j] - t[j - 1] }));
            }
            plain.extend(taus.iter().map(|t| u8::from((1..t.len()).all(|j| t[j] - t[j - 1] == one))));
        }
        let up64 = |v: &[i64]| self.timed(Kind::Copy, || self.take_up(if v.is_empty() { &[0i64][..] } else { v })).map_err(device);
        let alloc64 = |len: usize| self.timed(Kind::Alloc, || self.take::<i64>(len.max(1))).map_err(device);
        let clocks = vec![up64(&kappa)?, up64(&tau)?, up64(&tau)?, self.timed(Kind::Alloc, || self.take::<i64>((2 * paced * sites * n).max(1))).map_err(device)?];
        let plain = self.timed(Kind::Copy, || self.take_up(if plain.is_empty() { &[0u8][..] } else { &plain[..] })).map_err(device)?;
        tr.cwords.kappa = clocks[0].device_ptr();
        tr.cwords.tau = clocks[1].device_ptr();
        tr.cwords.sigma = clocks[2].device_ptr();
        tr.cwords.pframe = clocks[3].device_ptr();
        tr.cwords.plain = plain.device_ptr();
        // The level's own stores of its clock, as the fine batch keeps them for its own (`skin_fill` fills the pairs' and the crowds' skins at
        // each tick, `clock_fill` the near phases and skins and the crowd edges' far skins once the clock is set).
        let saddr = alloc64(3 * paced * n * sites)?;
        tr.cwords.saddr = saddr.device_ptr();
        let alloc32 = |len: usize| self.timed(Kind::Alloc, || self.take::<u32>(len.max(1))).map_err(device);
        let mut stores = Vec::new();
        if paced > 0 {
            stores.push(alloc32(paced * st.skin_entries * n)?);
            stores.push(alloc32(paced * sites * tr.cwords.slots as usize * n)?);
            (tr.cwords.skin, tr.cwords.cskin) = (stores[0].device_ptr(), stores[1].device_ptr());
        } else {
            (tr.cwords.skin, tr.cwords.cskin) = (0, 0);
        }
        let tm = cd.moment_modes();
        if paced > 0 && tm > 0 {
            let near = tm * sites * CLOCK_NEAR;
            stores.push(alloc32(2 * near)?);
            stores.push(alloc32(near)?);
            (tr.cwords.mphase, tr.cwords.mskin) = (stores[2].device_ptr(), stores[3].device_ptr());
        } else {
            (tr.cwords.mphase, tr.cwords.mskin) = (0, 0);
        }
        if paced > 0 {
            self.launch("field_skin_addresses", Self::cells((paced * n * sites) as u64), THREADS, &mut [arg(&mut tr.cwords)])?;
            self.launch("field_pframes", Self::cells((paced * sites * n) as u64), THREADS, &mut [arg(&mut tr.cwords)])?;
            self.clock_fill(coarse, &tr.cwords, sites)?;
        }
        let d0 = field.declaration.width;
        let split_read = self.timed(Kind::Alloc, || self.take::<i32>((fine.sites * d0).max(1))).map_err(device)?;
        let split_scale = self.timed(Kind::Alloc, || self.take::<i128>((fine.sites * field.declaration.lanes).max(1))).map_err(device)?;
        let restricted = alloc64(sites * h * d0)?;
        let read1 = self.timed(Kind::Alloc, || self.take::<i32>((sites * cd.width).max(1))).map_err(device)?;
        let scale1 = self.timed(Kind::Alloc, || self.take::<i128>((sites * cd.lanes).max(1))).map_err(device)?;
        let pad = alloc64(sites * h * d0)?;
        let epoch = self.timed(Kind::Copy, || self.take_up(if epoch_of.is_empty() { &[0u32][..] } else { &epoch_of[..] })).map_err(device)?;
        let harmonics = up64(&harm)?;
        let off = self.timed(Kind::Copy, || self.take_up(&off)).map_err(device)?;
        Ok(TowerBatch { st, ticks: Vec::new(), _trips: trips, _moment: moment, pr, _clocks: clocks, _plain: plain, split_read, split_scale, restricted, read1, scale1, pad, epoch, harmonics, off, _saddr: saddr, _stores: stores })
    }

    /// A read's own ticks on a batch's level ([`CardField::tower_batch`]): every tick kept where the read keeps the fine field's, and the shares
    /// stored where it stores them, taken as [`CardField::tick`] takes the fine field's.
    fn level_ticks(&self, field: &Field, tb: &TowerBatch<'c>, regions: usize, stored: bool, returning: bool, kept: bool) -> Result<Vec<Tick<'c>>> {
        let s = field.scale.as_deref().ok_or(TowerError::Refused("a level's ticks of a field without a level"))?;
        (0..if kept { s.coarse.declaration.ticks } else { 1 }).map(|_| self.tick(tb.st.sites, tb.st.pairs, regions, &s.coarse, stored, returning, true)).collect()
    }

    /// The level's forward at the split (the host's `scale_forward`): the fine faces read, each epoch's harmonics of its places' reads
    /// restricted through `A`, the level's ticks, and the prolongation, each place reading its epoch's harmonic blocks at its own phase,
    /// added back into the fine faces.
    #[allow(clippy::too_many_arguments)]
    fn tower_forward(&self, field: &Field, words: &mut Words, tr: &mut TowerRun<'c>, tb: &TowerBatch<'c>, regions: usize, stored: bool, returning: bool, kept: bool) -> Result<()> {
        let s = field.scale.as_deref().ok_or(TowerError::Refused("a level's forward of a field without a level"))?;
        let (d0, d1, h) = (field.declaration.width, s.coarse.declaration.width, tr.harmonics);
        let (a, ab, b, bb, _) = tr.offsets;
        let epochs = tb.st.sites;
        self.chart(words, words.x, &tb.split_read, &tb.split_scale, false)?;
        let (mut src, mut hp, mut op, mut e64, mut h32, mut w32, mut dst) = (tb.split_read.device_ptr(), tb.harmonics.device_ptr(), tb.off.device_ptr(), epochs as u64, h as u32, d0 as u32, tb.restricted.device_ptr());
        self.launch("field_level_chart32", Self::cells((epochs * h * d0) as u64), THREADS, &mut [arg(words), arg(&mut src), arg(&mut hp), arg(&mut op), arg(&mut e64), arg(&mut h32), arg(&mut w32), arg(&mut dst)])?;
        let mut gwords = tr.cwords;
        gwords.theta = tr.glue_at;
        self.affine("field_affine_x64", &mut gwords, a as u64, ab as u64, tr.reach_a, d1, h * d0, tb.restricted.device_ptr(), h * d0, tr.cwords.x, d1, 0, false)?;
        for k in 0..s.coarse.declaration.ticks {
            self.tick_forward(&s.coarse, &mut tr.cwords, &tb.ticks, k, kept, stored, false, false, returning, tb.pr.device_ptr(), epochs, tb.st.pairs, regions)?;
        }
        let x1 = tr.cwords.x;
        self.chart(&mut tr.cwords, x1, &tb.read1, &tb.scale1, false)?;
        let mut gwords = tr.cwords;
        gwords.theta = tr.glue_at;
        self.affine("field_affine_x32", &mut gwords, b as u64, bb as u64, tr.reach_b, h * d0, d1, tb.read1.device_ptr(), d1, tb.pad.device_ptr(), h * d0, 0, false)?;
        let (mut vp, mut hp, mut ep, mut h32, mut w32, mut dst, mut add) = (tb.pad.device_ptr(), tb.harmonics.device_ptr(), tb.epoch.device_ptr(), h as u32, d0 as u32, words.x, 1u32);
        self.launch("field_level_unchart", Self::cells((tb_fine_sites(words) * d0) as u64), THREADS, &mut [arg(words), arg(&mut vp), arg(&mut hp), arg(&mut ep), arg(&mut h32), arg(&mut w32), arg(&mut dst), arg(&mut add)])
    }

    /// The level's reverse at the split (the host's `scale_return`): `back.dx`, the covector of the fine faces after the prolongation,
    /// carried through the prolongation, the level's ticks and the restriction into the covector of the fine faces before it; the
    /// level's and the glue's covectors added into their own buffers. The cut is data and takes nothing.
    fn tower_back(&self, field: &Field, words: &mut Words, tr: &mut TowerRun<'c>, tb: &TowerBatch<'c>, back: &Back<'c>, cb: &Back<'c>) -> Result<()> {
        let s = field.scale.as_deref().ok_or(TowerError::Refused("a level's reverse of a field without a level"))?;
        let (d0, d1, h) = (field.declaration.width, s.coarse.declaration.width, tr.harmonics);
        let (a, ab, b, bb, _) = tr.offsets;
        let epochs = tb.st.sites;
        let (cg, gg) = match (tr.cg.as_deref(), tr.gg.as_deref()) {
            (Some(cg), Some(gg)) => (cg, gg),
            _ => return Err(TowerError::Refused("a level's reverse without its levels' covectors")),
        };
        // The prolongation: `δv(j)` each epoch's harmonics of its places' covectors, then `δb_B`, `δB` and `δr̂¹ = Bᵀ δv`.
        let (mut src, mut hp, mut op, mut e64, mut h32, mut w32, mut dst) = (back.dx.device_ptr(), tb.harmonics.device_ptr(), tb.off.device_ptr(), epochs as u64, h as u32, d0 as u32, tb.pad.device_ptr());
        self.launch("field_level_chart64", Self::cells((epochs * h * d0) as u64), THREADS, &mut [arg(words), arg(&mut src), arg(&mut hp), arg(&mut op), arg(&mut e64), arg(&mut h32), arg(&mut w32), arg(&mut dst)])?;
        self.outer(&mut tr.cwords, gg, bb as u64, h * d0, 0, tb.pad.device_ptr(), h * d0, 0, 0, false, false)?;
        self.outer(&mut tr.cwords, gg, b as u64, h * d0, d1, tb.pad.device_ptr(), h * d0, tb.read1.device_ptr(), d1, false, false)?;
        let mut gwords = tr.cwords;
        gwords.theta = tr.glue_at;
        self.transposed(&mut gwords, b as u64, h * d0, d1, tb.pad.device_ptr(), h * d0, cb.dr.device_ptr(), false, false)?;
        self.ratio_adjoint(&mut tr.cwords, tb.read1.device_ptr(), tb.scale1.device_ptr(), cb.dr.device_ptr(), 0, cb.dx.device_ptr(), false)?;
        // The level's ticks, in reverse.
        for (at, tick) in tb.ticks.iter().enumerate().rev() {
            self.tick_back(&s.coarse, &mut tr.cwords, tick, at, cg, cb, cb.dm.device_ptr(), epochs, false)?;
        }
        // The restriction: `δb_A`, `δA` and `δm = Aᵀ δx¹`, each place's part at its own phase through its read's adjoint into `δx`.
        self.outer(&mut tr.cwords, gg, ab as u64, d1, 0, cb.dx.device_ptr(), d1, 0, 0, false, false)?;
        self.outer(&mut tr.cwords, gg, a as u64, d1, h * d0, cb.dx.device_ptr(), d1, tb.restricted.device_ptr(), h * d0, true, false)?;
        let mut gwords = tr.cwords;
        gwords.theta = tr.glue_at;
        self.transposed(&mut gwords, a as u64, d1, h * d0, cb.dx.device_ptr(), d1, tb.pad.device_ptr(), false, false)?;
        let (mut vp, mut hp, mut ep, mut h32, mut w32, mut dst, mut add) = (tb.pad.device_ptr(), tb.harmonics.device_ptr(), tb.epoch.device_ptr(), h as u32, d0 as u32, back.dr.device_ptr(), 0u32);
        self.launch("field_level_unchart", Self::cells((tb_fine_sites(words) * d0) as u64), THREADS, &mut [arg(words), arg(&mut vp), arg(&mut hp), arg(&mut ep), arg(&mut h32), arg(&mut w32), arg(&mut dst), arg(&mut add)])?;
        self.ratio_adjoint(words, tb.split_read.device_ptr(), tb.split_scale.device_ptr(), back.dr.device_ptr(), back.dx.device_ptr(), back.dx.device_ptr(), false)
    }

    /// [realization; agent-inferred, November 14, the ring record §4] **A batch's base** ([`BatchBase`]): the regions staged, the base clock formed
    /// (its paces, skin addresses and frames), the site moments on it, the opening's comparison's forward wherever a read of the batch reads it
    /// (`returning`: the batch's last read returns; a level reads its news in every read), the level's news fetched and its cut staged. The
    /// opening's forward is kept only where the last read compares it (it returns through it before its ticks), and dropped here otherwise.
    fn batch_base(&self, field: &Field, regions: &[Region], words: &mut Words, tower: Option<&mut TowerRun<'c>>, returning: bool) -> Result<BatchBase<'c>> {
        if field.scale.is_some() != tower.is_some() {
            return Err(TowerError::Refused("a tower is read with its packets' level"));
        }
        let card = self.card;
        let d = field.declaration;
        let (dw, n, a) = (d.width, d.modes, d.alphabet);
        let m2 = 2 * d.complex();
        let st = self.stage(regions, a, dw, &d, words)?;
        let sites = st.sites;
        // The site moments (§15.1), once for the pass, added into every tick's values.
        let moment = self.timed(Kind::Alloc, || self.take_zeroed::<i64>((sites * m2).max(1))).map_err(device)?;
        words.moment = moment.device_ptr();
        // The turned heads' clocks (§16): their rates, clocks, variations and plainness `[p][t]`, `[p][r]`, and frames.
        let paced = d.paced_heads();
        let kappa = self.timed(Kind::Alloc, || self.take::<i64>((paced * sites).max(1))).map_err(device)?;
        let tau = self.timed(Kind::Alloc, || self.take::<i64>((paced * sites).max(1))).map_err(device)?;
        let sigma = self.timed(Kind::Alloc, || self.take::<i64>((paced * sites).max(1))).map_err(device)?;
        let saddr = self.timed(Kind::Alloc, || self.take::<i64>((3 * paced * n * sites).max(1))).map_err(device)?;
        let plain = self.timed(Kind::Alloc, || self.take::<u8>((paced * regions.len()).max(1))).map_err(device)?;
        let pframe = self.timed(Kind::Alloc, || self.take::<i64>((2 * paced * sites * n).max(1))).map_err(device)?;
        // [theory, November 12, P50 step 1 and P51] The clock's skins (`skin_fill`): a word a paced head, support entry and mode at the row's support
        // stride (`E2` entries), and a word a paced head, site, crowd slot and mode; one store for the batch, formed again at each clock.
        let skins = if paced > 0 {
            let pair_words = paced * st.skin_entries * n;
            let crowd_words = paced * sites * words.slots as usize * n;
            Some((self.timed(Kind::Alloc, || self.take::<u32>(pair_words.max(1))).map_err(device)?, self.timed(Kind::Alloc, || self.take::<u32>(crowd_words.max(1))).map_err(device)?))
        } else {
            None
        };
        (words.skin, words.cskin) = skins.as_ref().map_or((0, 0), |(a, b)| (a.device_ptr(), b.device_ptr()));
        // [theory, November 12, P50 step 2] A clock's near phases (two words) and skins (one) a moment mode, site and near offset; one store, formed
        // again for each clock where its moments are read (`clock_fill`).
        let tm = d.moment_modes();
        let clock_store = if paced > 0 && tm > 0 {
            let near = tm * sites * CLOCK_NEAR;
            Some((self.timed(Kind::Alloc, || self.take::<u32>(2 * near)).map_err(device)?, self.timed(Kind::Alloc, || self.take::<u32>(near)).map_err(device)?))
        } else {
            None
        };
        (words.mphase, words.mskin) = clock_store.as_ref().map_or((0, 0), |(a, b)| (a.device_ptr(), b.device_ptr()));
        words.kappa = kappa.device_ptr();
        words.tau = tau.device_ptr();
        words.sigma = sigma.device_ptr();
        words.saddr = saddr.device_ptr();
        words.plain = plain.device_ptr();
        words.pframe = pframe.device_ptr();
        // [measurement; theory, November 13, P56 item 4] The batch's clocks' takes.
        self.mark("batch_takes");
        if paced > 0 {
            self.launch("field_paces", Self::cells((paced * regions.len()) as u64), THREADS, &mut [arg(words)])?;
            self.launch("field_skin_addresses", Self::cells((paced * n * sites) as u64), THREADS, &mut [arg(words)])?;
            self.launch("field_pframes", Self::cells((paced * sites * n) as u64), THREADS, &mut [arg(words)])?;
        }
        // [P60 item 2] The opening is compared in a training read where the field has the opening's lift: the standing moments' operands are kept.
        let compared = d.opening && returning;
        // [theory, November 13, the design record §4.9] A level reads the opening's news in every pass, so the opening's forward runs
        // wherever a level stands; its comparison and return only where the pass returns.
        let opened = d.opening && (returning || field.scale.is_some());
        let kept_moments = self.moments(field, words, regions.len(), sites, opened)?;
        let opening = if opened { Some(self.opening_forward(field, words, regions, &st, kept_moments)?) } else { None };
        // [G145] The level's news at every place, from the opening's face (`field_level_news`, the host's `Field::level_news`), read to the
        // host, which cuts each region's epochs (`level_cut`, a kind of work placed on the host; its bits are the host's own function's).
        let news = match (opening.as_ref(), field.scale.is_some()) {
            (Some(op), true) => {
                let out = self.timed(Kind::Alloc, || self.take::<i64>(sites.max(1))).map_err(device)?;
                let (mut mp, mut tp, mut np) = (op.masses.device_ptr(), op.totals.device_ptr(), out.device_ptr());
                self.launch("field_level_news", Self::warps(sites as u64), THREADS, &mut [arg(words), arg(&mut mp), arg(&mut tp), arg(&mut np)])?;
                Some(self.timed(Kind::Copy, || card.fetch_range(&out, 0, sites)).map_err(device)?)
            }
            _ => None,
        };
        // The opening's forward ends here where no read compares it.
        let opening = opening.filter(|_| compared);
        let tb = match tower {
            Some(tr) => Some(self.tower_batch(field, tr, &st, regions.len(), news.as_deref().ok_or(TowerError::Refused("a level without the opening's news"))?)?),
            None => None,
        };
        self.mark("batch_base");
        Ok(BatchBase { st, kappa, tau, sigma, saddr, plain, pframe, moment, _skins: skins, _clock_store: clock_store, opening, tb, reads: 0 })
    }

    /// One read of a batch of regions on its base ([`CardField::batch_base`]): the opening and the forward, each unresolved site's face (and its
    /// logits when `logits`), when `g` is given the reverse added into it, and with `keep` the still heads' last-tick weight rows of those sites
    /// (the batch's one region). With `first` (a field that reads twice, [`FieldDeclaration::mark`]) it is the batch's first read: the forward to
    /// the faces with no reading, and each silent site's shares of its face left on the card in `first`, nothing fetched.
    #[allow(clippy::type_complexity)]
    #[allow(clippy::too_many_arguments)]
    fn batch(&self, field: &Field, regions: &[Region], at_region: usize, words: &mut Words, base: &mut BatchBase<'c>, g: Option<&CardBuffer<'c, i128>>, logits: bool, keep: Option<&[usize]>, mut tower: Option<&mut TowerRun<'c>>, first: Option<&mut Option<Pooled<'c, u32>>>) -> Result<(Vec<Vec<Option<TowerFace>>>, Vec<Vec<Option<Vec<i64>>>>, Rows, Vec<Vec<u64>>)> {
        if field.scale.is_some() != tower.is_some() || field.scale.is_some() != base.tb.is_some() {
            return Err(TowerError::Refused("a tower is read with its packets' level"));
        }
        // [the ring record §4] A first read is the built read alone: no return, no logits, no kept rows, no mark of its own, and none of the
        // readings below (they read the second read, the field's).
        let reading = first.is_none();
        if !reading && (g.is_some() || logits || keep.is_some() || words.mark_share != 0) {
            return Err(TowerError::Refused("a field's first read with a return, a reading or a mark"));
        }
        let card = self.card;
        let d = field.declaration;
        let (dw, m, n, f, a, heads) = (d.width, d.complex(), d.modes, d.contacts, d.alphabet, d.heads);
        let m2 = 2 * m;
        let span = 2 * n;
        let st = &base.st;
        let (sites, pairs) = (st.sites, st.pairs);
        let (site_region, site_pos, region_off, classes, unresolved, definite) = (&st.site_region, &st.site_pos, &st.region_off, &st.classes, &st.unresolved, &st.definite);
        let (echo_has, mix_off, mix_class, mix_share, site_weight) = (&st.echo_has, &st.mix_off, &st.mix_class, &st.mix_share, &st.site_weight);
        let (status, x) = (&st.status, &st.x);
        let returning = g.is_some();
        // The shares are stored for a return's reverse, for the rows `keep` reads, and for a logits read's
        // echo (§15.3: the round trips of consecutive ticks, so every tick is kept).
        let stored = returning || keep.is_some() || logits;
        let kept = returning || logits;
        // [theory, November 13, P56 step 6] The pairs' block `e` is read past its rows' supports only by a logits read (the echo's round trips at the reverse
        // pair, the held rows and the rows' currents over every entry of a row) and by a landmark read (whole rows fetched): only those take it zeroed.
        let dense = logits || keep.is_some();
        // The read before's level ticks end before this read's are taken.
        if let Some(tb) = base.tb.as_mut() {
            tb.ticks = Vec::new();
        }
        let ticks: Vec<Tick> = (0..if kept { d.ticks } else { 1 }).map(|_| self.tick(sites, pairs, regions.len(), field, stored, returning, dense)).collect::<Result<_>>()?;
        // The round trips a site's echo sums (128 bits a site), over the heads and the ticks.
        let trips = self.timed(Kind::Alloc, || self.take_zeroed::<i128>(sites.max(1))).map_err(device)?;
        words.trips = trips.device_ptr();
        // Every receiver's probe chart of the read, once a tick (§16.19), framed and put at unit power by head.
        let pr = self.timed(Kind::Alloc, || self.take::<i64>((sites * m2).max(1))).map_err(device)?;
        words.pr = pr.device_ptr();
        let paced = d.paced_heads();
        // [§16.44] The base clock (the batch's, [`BatchBase`]): the words hold it from here to the first tick's end, and again after the ticks.
        let base_clock = base.clock();
        set_clock(words, None, base_clock);
        let t64 = sites as u64;
        // [measurement; theory, November 13, P56 item 4] The read's ticks' takes.
        self.mark("batch_takes");
        // The class lists' shared words: the buckets `2·3^b`, and a chunk's keys `[32][2^b]` and counts.
        let buckets = 4 * 3 * d.classes() as u32;
        self.launch("field_open", Self::cells(t64 * dw as u64), THREADS, &mut [arg(words)])?;
        // [realization; agent-inferred, November 14] A read after the first forms the base clock's phases and skins again (`clock_fill`, as the base's
        // moments did): the first read's blanks formed their own clocks' in the same stores, and the crowds and the moments read the clock's.
        if base.reads > 0 {
            self.clock_fill(field, words, sites)?;
        }
        base.reads += 1;
        // The moment's chart into the face (§16.22, the host's `Field::open`): `x⁰ += release(C s + b, 24)`.
        let (mface, mface_bias, rmface) = moment_face(field);
        self.affine("field_affine_x64", words, mface, mface_bias, rmface, dw, m2, words.moment, m2, 0, dw, words.x, false)?;
        // [realization; theory, November 13, G144] **The opening's return runs at the end of its own forward, before the ticks.** It reads only its
        // forward's buffers, the constitution, the base clock's frames and clocks (the words hold the base clock here and again at the reverse's start,
        // and its kernels read no filled clock store) and the stage's host arrays; it adds into `g` and into the base clock's two covectors, taken here
        // zeroed and handed to the reverse as its own, every one an integer sum, so the order is the realization's. Its forward's buffers end here,
        // so none stands beside the ticks, the face or the reverse: held across them they added a buffer to each class they share, and the card's pool
        // passed its budget by about a tenth of a gigabyte, freeing and allocating again at three take sites every section (G143's profiled logs).
        // [realization; agent-inferred, November 14] The forward is the base's (formed once a batch); the read that returns takes it, and a field that
        // reads twice holds it across its first read, whose one tick's carriers stand under the second's every tick's.
        let early_clocks = match base.opening.take() {
            Some(op) if !returning => {
                // A read that does not return leaves the forward to the read that does.
                base.opening = Some(op);
                None
            }
            Some(op) => {
                // [P60 item 1d] The opening's code at every compared place, where the training path reads it: each place's mass at its class and its total.
                if self.opening_wanted.get() {
                    let picked = self.timed(Kind::Alloc, || self.take::<u64>(sites.max(1))).map_err(device)?;
                    let mut cw = *words;
                    cw.unresolved = op.mask.device_ptr();
                    let (mut mp, mut pp) = (op.masses.device_ptr(), picked.device_ptr());
                    self.launch("field_face_at_class", Self::cells(sites as u64), THREADS, &mut [arg(&mut cw), arg(&mut mp), arg(&mut pp)])?;
                    let picked = self.timed(Kind::Copy, || card.fetch_range(&picked, 0, sites)).map_err(device)?;
                    let totals = self.timed(Kind::Copy, || card.fetch_range(&op.totals, 0, sites)).map_err(device)?;
                    let mask = self.timed(Kind::Copy, || card.fetch_range(&op.mask, 0, sites)).map_err(device)?;
                    let mut out = self.opening_out.borrow_mut();
                    for r in 0..regions.len() {
                        let span = region_off[r] as usize..region_off[r + 1] as usize;
                        out.push(span.map(|t| (mask[t] != 0).then(|| TowerFace { masses: vec![u128::from(picked[t])], total: totals[t] as u128 }.code(0))).collect());
                    }
                }
                let g = g.ok_or(TowerError::Refused("the opening is compared only where the pass returns"))?;
                let gtau = self.timed(Kind::Alloc, || self.take_zeroed::<i128>((paced * sites).max(1))).map_err(device)?;
                let gsig = self.timed(Kind::Alloc, || self.take_zeroed::<i128>((paced * sites).max(1))).map_err(device)?;
                (words.gtau, words.gsig) = (gtau.device_ptr(), gsig.device_ptr());
                self.opening_back(field, words, &op, g, (classes, unresolved, site_pos, mix_off, mix_class, mix_share), sites)?;
                drop(op);
                Some((gtau, gsig))
            }
            None => None,
        };
        // The level's ticks, the read's own.
        if let Some(tb) = base.tb.as_mut() {
            tb.ticks = self.level_ticks(field, tb, regions.len(), stored, returning, kept)?;
        }
        let tb = base.tb.as_ref();
        self.mark("batch_setup");
        // [§16.44] The blanks run at the bare rate in the first tick, and each later tick at the faces the tick before
        // gave them (the host's `pass`).
        let blanks = paced > 0 && (0..sites).any(|t| unresolved[t] != 0 && st.mix_off[t] == st.mix_off[t + 1]);
        let mut clocks: Vec<Option<CardClock<'c>>> = vec![None];
        // [measurement; part P2] The carry circles' gates, where read: one accumulator a batch, added into after each tick's forward from that tick's
        // own gate and leak reads, fetched once the ticks end.
        let gate_acc = if reading && d.carry > 0 && self.carry_gates.borrow().is_some() { Some(self.timed(Kind::Alloc, || self.take_zeroed::<u64>(2 * d.carry + 1)).map_err(device)?) } else { None };
        for k in 0..d.ticks {
            set_clock(words, clocks[k].as_ref(), base_clock);
            if let (Some(tr), Some(tb)) = (tower.as_deref_mut(), tb) {
                if k == tr.split {
                    self.tower_forward(field, words, tr, tb, regions.len(), stored, returning, kept)?;
                }
            }
            self.tick_forward(field, words, &ticks, k, kept, stored, keep.is_some(), logits, returning, pr.device_ptr(), sites, pairs, regions.len())?;
            if let Some(acc) = gate_acc.as_ref() {
                let tick = &ticks[if kept { k } else { 0 }];
                (words.pg, words.pgam) = (tick.pg.device_ptr(), tick.pgam.device_ptr());
                let mut ap = acc.device_ptr();
                self.launch("field_carry_gates_read", Self::cells((sites * d.carry) as u64), THREADS, &mut [arg(words), arg(&mut ap)])?;
            }
            if k + 1 < d.ticks {
                let next = if blanks { Some(self.blank_clock(field, words, regions.len(), sites)?) } else { None };
                clocks.push(next);
            }
        }
        set_clock(words, None, base_clock);
        if let Some(acc) = gate_acc.as_ref() {
            let read = self.timed(Kind::Copy, || card.fetch(&**acc)).map_err(device)?;
            if let Some(sum) = self.carry_gates.borrow_mut().as_mut() {
                for (s, &v) in sum.iter_mut().zip(&read) {
                    *s += u128::from(v);
                }
            }
        }
        // Each named site's clocks by tick (a reading, §16.44), the batch's one region.
        if let Some(named) = self.clock_sites.borrow().as_ref().filter(|_| reading) {
            let mut out = self.clock_out.borrow_mut();
            for &i in named {
                if regions.len() != 1 || i >= sites {
                    return Err(TowerError::Refused("a clock's site outside its region"));
                }
                let mut read = BlankClocks::default();
                for clock in &clocks {
                    read.ticks.push(match clock {
                        Some(c) if unresolved[i] != 0 && st.mix_off[i] == st.mix_off[i + 1] => {
                            let kappa = self.timed(Kind::Copy, || card.fetch_range(&c.kappa, 0, paced * sites)).map_err(device)?;
                            let masses = self.timed(Kind::Copy, || card.fetch_range(&c.masses, i * a, a)).map_err(device)?;
                            let total = self.timed(Kind::Copy, || card.fetch_range(&c.totals, i, 1)).map_err(device)?;
                            Some(((0..paced).map(|p| kappa[p * sites + i]).collect(), TowerFace { masses: masses.into_iter().map(|m| m as u128).collect(), total: total[0] as u128 }))
                        }
                        _ => None,
                    });
                }
                out.push(read);
            }
        }
        // [measurement; theory, November 13, P57 item 2 (G132)] The charts by stage, where they are read: each tick's chart at its opening,
        // gathered at the open sites (`field_gather_rows32`), and after the last tick the face's (below).
        let open_at: Vec<u32> = (0..sites as u32).filter(|&t| unresolved[t as usize] != 0).collect();
        let mut stage_rows: Option<Vec<Vec<i32>>> = None;
        let gather = |src: u64, at: &CardBuffer<'c, u32>| -> Result<Vec<i32>> {
            let rows = self.timed(Kind::Alloc, || self.take::<i32>((open_at.len() * dw).max(1))).map_err(device)?;
            let (mut sp, mut ap, mut count, mut width, mut dp) = (src, at.device_ptr(), open_at.len() as u64, dw as u32, rows.device_ptr());
            self.launch("field_gather_rows32", Self::cells((open_at.len() * dw) as u64), THREADS, &mut [arg(&mut sp), arg(&mut ap), arg(&mut count), arg(&mut width), arg(&mut dp)])?;
            self.timed(Kind::Copy, || card.fetch_range(&rows, 0, open_at.len() * dw)).map_err(device)
        };
        let open_buf = if reading && self.tick_charts.borrow().is_some() && !open_at.is_empty() { Some(self.timed(Kind::Copy, || self.take_up(&open_at)).map_err(device)?) } else { None };
        if let Some(at) = open_buf.as_ref() {
            let mut stages = Vec::with_capacity(ticks.len() + 1);
            for tick in &ticks {
                stages.push(gather(tick.read.device_ptr(), at)?);
            }
            stage_rows = Some(stages);
        }
        // Each tick's reads, where the ticks are read (a reading of expansion and volume).
        if let Some(out) = self.tick_reads.borrow_mut().as_mut().filter(|_| reading) {
            let mut per: Vec<Vec<TickRead>> = vec![Vec::new(); regions.len()];
            for tick in &ticks {
                let read = self.timed(Kind::Copy, || card.fetch_range(&tick.read, 0, sites * dw)).map_err(device)?;
                let lanes = field.declaration.lanes;
                let scale = self.timed(Kind::Copy, || card.fetch_range(&tick.scale, 0, sites * lanes)).map_err(device)?;
                let read2 = self.timed(Kind::Copy, || card.fetch_range(&tick.read2, 0, sites * dw)).map_err(device)?;
                let scale2 = self.timed(Kind::Copy, || card.fetch_range(&tick.scale2, 0, sites * lanes)).map_err(device)?;
                for (r, slot) in per.iter_mut().enumerate() {
                    let (a0, a1) = (region_off[r] as usize, region_off[r + 1] as usize);
                    slot.push(TickRead {
                        read: read[a0 * dw..a1 * dw].to_vec(),
                        scale: scale[a0 * lanes..a1 * lanes].to_vec(),
                        pair_read: read2[a0 * dw..a1 * dw].to_vec(),
                        pair_scale: scale2[a0 * lanes..a1 * lanes].to_vec(),
                    });
                }
            }
            out.extend(per);
        }
        // Each named site's near field by offset (a reading, §16.42): every kept tick's shares of each head, the batch's one
        // region.
        if let Some(named) = self.near_sites.borrow().as_ref().filter(|_| reading) {
            let mut out = self.near_out.borrow_mut();
            for &i in named {
                if regions.len() != 1 || i >= sites {
                    return Err(TowerError::Refused("a near-field site outside its region"));
                }
                let mut near = NearOffsets::default();
                for tick in &ticks {
                    for h in 0..heads {
                        let row = self.timed(Kind::Copy, || card.fetch_range(&tick.e, h * pairs + i * sites, sites)).map_err(device)?;
                        let (mut before, mut after) = ([0u64; NEAR - 1], [0u64; NEAR - 1]);
                        for (d, (b, a)) in before.iter_mut().zip(after.iter_mut()).enumerate() {
                            if let Some(&e) = i.checked_sub(d + 1).and_then(|j| row.get(j)) {
                                *b = e;
                            }
                            if let Some(&e) = row.get(i + d + 1) {
                                *a = e;
                            }
                        }
                        near.before.push(before);
                        near.after.push(after);
                    }
                }
                out.push(near);
            }
        }
        // A held read's rows by where their mass lies (a reading for the receipts): each kept tick's shares.
        if let Some(questions) = self.held_questions.borrow().as_ref().filter(|_| reading) {
            let starts: Vec<u32> = (0..regions.len()).map(|r| questions[at_region + r] as u32).collect();
            let starts_c = self.timed(Kind::Copy, || self.take_up(&starts)).map_err(device)?;
            let acc = self.timed(Kind::Alloc, || self.take_zeroed::<i128>(d.ticks * heads * 9)).map_err(device)?;
            for (k, tick) in ticks.iter().enumerate() {
                set_tick(words, tick, returning);
                set_clock(words, clocks.get(k).and_then(Option::as_ref).filter(|_| kept), base_clock);
                let (mut sp, mut tk, mut ap) = (starts_c.device_ptr(), k as u32, acc.device_ptr());
                self.launch("field_held_rows", Self::warps((heads * sites) as u64), THREADS, &mut [arg(words), arg(&mut sp), arg(&mut tk), arg(&mut ap)])?;
            }
            let cells = self.timed(Kind::Copy, || self.card.fetch_range(&*acc, 0, d.ticks * heads * 9)).map_err(device)?;
            let mut total = self.held_cells.borrow_mut();
            if total.is_empty() {
                total.resize(cells.len(), 0);
            }
            for (t, c) in total.iter_mut().zip(cells) {
                *t += c;
            }
        }
        // The held rows' currents by where they come from (a reading, §16.21): each kept tick's shares.
        if let Some(questions) = self.row_questions.borrow().as_ref().filter(|_| reading) {
            let span = 2 * n;
            let starts: Vec<u32> = (0..regions.len()).map(|r| questions[at_region + r] as u32).collect();
            let starts_c = self.timed(Kind::Copy, || self.take_up(&starts)).map_err(device)?;
            for (k, tick) in ticks.iter().enumerate() {
                set_tick(words, tick, returning);
                set_clock(words, clocks.get(k).and_then(Option::as_ref).filter(|_| kept), base_clock);
                let far = self.timed(Kind::Alloc, || self.take_zeroed::<i128>(heads * sites * span)).map_err(device)?;
                let near = self.timed(Kind::Alloc, || self.take_zeroed::<i128>(heads * sites * span)).map_err(device)?;
                let rest = self.timed(Kind::Alloc, || self.take_zeroed::<i128>(heads * sites * span)).map_err(device)?;
                let top = self.timed(Kind::Alloc, || self.take_zeroed::<u64>(heads * sites)).map_err(device)?;
                let (mut sp, mut fp, mut np, mut rp, mut tp) = (starts_c.device_ptr(), far.device_ptr(), near.device_ptr(), rest.device_ptr(), top.device_ptr());
                self.launch("field_row_currents", Self::warps((heads * sites) as u64), THREADS, &mut [arg(words), arg(&mut sp), arg(&mut fp), arg(&mut np), arg(&mut rp), arg(&mut tp)])?;
                let (fv, nv) = (self.card.fetch_range(&*far, 0, heads * sites * span).map_err(device)?, self.card.fetch_range(&*near, 0, heads * sites * span).map_err(device)?);
                let rv = self.card.fetch_range(&*rest, 0, heads * sites * span).map_err(device)?;
                let tv = self.card.fetch_range(&*top, 0, heads * sites).map_err(device)?;
                let mut out = self.row_out.borrow_mut();
                for (r, region) in regions.iter().enumerate() {
                    let first = region_off[r] as usize;
                    for h in 0..heads {
                        for t in (0..region.classes.len()).filter(|&t| region.unresolved[t]) {
                            let at = (h * sites + first + t) * span;
                            out[at_region + r].push(RowCurrent { tick: k as u32, head: h as u32, site: t as u32, far: fv[at..at + span].to_vec(), near: nv[at..at + span].to_vec(), rest: rv[at..at + span].to_vec(), top: tv[h * sites + first + t], covector: Vec::new() });
                        }
                    }
                }
            }
        }
        set_clock(words, None, base_clock);
        // The faces at the unresolved sites.
        let fread = self.timed(Kind::Alloc, || self.take::<i32>(sites * dw)).map_err(device)?;
        // [realization; theory, November 13, P58 item 2] The face's scale and totals, and the lift below, are taken without zeroing: each word
        // read is written first, at the open sites (`unresolved`) alone. `field_chart` writes every lane's scale of an open site, and its one reader,
        // `field_ratio_adjoint` (the reverse's, on the same sites), reads the scale only there. `field_face` writes an open site's total, and its
        // readers read it only there: `field_face_covector`, the host's faces at the batch's end and a port's places (`unresolved[t] != 0`).
        let fscale = self.timed(Kind::Alloc, || self.take::<i128>(sites * field.declaration.lanes)).map_err(device)?;
        let z = self.timed(Kind::Alloc, || self.take::<i64>(sites * a)).map_err(device)?;
        let masses = self.timed(Kind::Alloc, || self.take::<u64>(sites * a)).map_err(device)?;
        let totals = self.timed(Kind::Alloc, || self.take::<i128>(sites)).map_err(device)?;
        self.chart(words, words.x, &fread, &fscale, true)?;
        // [P57 item 2] The chart after the last tick, the stage the faces read, gathered at the open sites beside each tick's.
        if let (Some(stages), Some(at)) = (stage_rows.as_mut(), open_buf.as_ref()) {
            stages.push(gather(fread.device_ptr(), at)?);
        }
        // The face read through the encoding (§16.26, the host's `Field::tied`): the lift `y = R r̂ + b_R`, then
        // `z(a) = rel(⟨E(a), y⟩, 16) + c_a`. [P58 item 2] The lift unzeroed: `affine` writes an open site's every output, and its readers,
        // `field_tied_face` and the reverse's `field_tied_back_e`, read it at open sites alone.
        let lift = self.timed(Kind::Alloc, || self.take::<i64>(sites * dw)).map_err(device)?;
        let lift_bias = field.layout().lift_bias as u64;
        self.affine("field_affine_x32", words, words.read, lift_bias, words.rread, dw, dw, fread.device_ptr(), dw, lift.device_ptr(), dw, 0, true)?;
        {
            let (mut enc, mut cb, mut yp, mut zp) = (words.enc, words.read_bias, lift.device_ptr(), z.device_ptr());
            self.launch("field_tied_face", Self::cells(t64 * a as u64), THREADS, &mut [arg(words), arg(&mut enc), arg(&mut cb), arg(&mut yp), arg(&mut zp)])?;
        }
        // The cavity field (§15.3): a carried site's read less its own echo.
        if echo_has.iter().any(|&h| h != 0) {
            let mut zp = z.device_ptr();
            self.launch("field_echo_apply", Self::cells((sites * a) as u64), THREADS, &mut [arg(words), arg(&mut zp)])?;
        }
        let (mut zp, mut mp, mut tp) = (z.device_ptr(), masses.device_ptr(), totals.device_ptr());
        self.launch("field_face", Self::warps(t64), THREADS, &mut [arg(words), arg(&mut zp), arg(&mut mp), arg(&mut tp)])?;
        self.mark("face_launch");
        // [the ring record §4] A first read ends at its faces: each silent site's shares of its face (the host's `shares`) stay on the card for the
        // second read's marks, and nothing is fetched.
        if let Some(out) = first {
            let shares = self.timed(Kind::Alloc, || self.take::<u32>((sites * a).max(1))).map_err(device)?;
            let mut sp = shares.device_ptr();
            self.launch("field_mark_shares", Self::cells((sites * a) as u64), THREADS, &mut [arg(words), arg(&mut mp), arg(&mut tp), arg(&mut sp)])?;
            self.status(&status)?;
            *out = Some(shares);
            return Ok((Vec::new(), Vec::new(), Rows::new(), Vec::new()));
        }
        if let Some(g) = g {
            // The covector's magnitude near and far, where read (§16.20).
            let shares = match self.covector_shares.borrow().is_some() {
                true => Some(self.timed(Kind::Alloc, || self.take_zeroed::<i128>(2 * heads)).map_err(device)?),
                false => None,
            };
            words.dsshare = shares.as_ref().map_or(0, |b| b.device_ptr());
            // The held rows' current covectors, where read (§16.21).
            if self.row_questions.borrow().is_some() {
                *self.row_cov.borrow_mut() = Some(vec![Vec::new(); ticks.len()]);
            }
            // The ports' covectors (§16.24, the host's `port_reading`): their places' faces fetched, each port's coupling read on
            // the host from the same masses and totals, its rows written over the face covector at its places.
            let mut ported: (Vec<u32>, Vec<i64>) = (Vec::new(), Vec::new());
            if regions.iter().any(|r| r.port.is_some()) {
                let ms = self.timed(Kind::Copy, || card.fetch_range(&masses, 0, sites * a)).map_err(device)?;
                let ts = self.timed(Kind::Copy, || card.fetch_range(&totals, 0, sites)).map_err(device)?;
                for (r, region) in regions.iter().enumerate() {
                    let Some(port) = region.port else { continue };
                    let first = region_off[r] as usize;
                    let wide: Vec<Vec<u128>> = (first + port.start..region_off[r + 1] as usize).map(|t| ms[t * a..(t + 1) * a].iter().map(|&v| v as u128).collect()).collect();
                    // [§16.47] A resolved place of a port at its boundary carries no face (the host's `port_faces`).
                    // [§16.47] A place past the port's stop is read and not compared: it carries no face to the reading, and its
                    // covector is zero, written as a zero row (an unported open place would take its own place's).
                    let stop = first + port.stop.unwrap_or(region_off[r + 1] as usize - first).min(region_off[r + 1] as usize - first);
                    // [§16.47] A place the port does not hear is read and not compared, as one past the stop.
                    let heard = |t: usize| t < stop && port.heard.is_none_or(|h| h[t - first]);
                    let at: Vec<(&[u128], u128)> = wide.iter().zip(first + port.start..).map(|(m, t)| if unresolved[t] != 0 && heard(t) { (m.as_slice(), ts[t] as u128) } else { (&[][..], 0) }).collect();
                    let (rows, _) = holonics::hnn::tower::field::port_reading(&at, &port)?;
                    for (k, row) in rows.into_iter().enumerate() {
                        let t = first + port.start + k;
                        if !row.is_empty() {
                            ported.0.push(t as u32);
                            ported.1.extend(row);
                        } else if !heard(t) && unresolved[t] != 0 {
                            ported.0.push(t as u32);
                            ported.1.extend(std::iter::repeat_n(0i64, a));
                        }
                    }
                }
            }
            self.reverse(field, words, &ticks, (&clocks, base_clock), g, &fread, &fscale, &lift, &masses, &totals, &classes, &unresolved, &site_pos, &mix_off, &mix_class, &mix_share, &site_weight, &ported, sites, pairs, tower.as_deref_mut().zip(tb), early_clocks)?;
            if let Some(cov) = self.row_cov.borrow_mut().take() {
                let span = 2 * n;
                let mut out = self.row_out.borrow_mut();
                for (r, _) in regions.iter().enumerate() {
                    let first = region_off[r] as usize;
                    for row in out[at_region + r].iter_mut() {
                        let at = (row.head as usize * sites + first + row.site as usize) * span;
                        row.covector = cov[row.tick as usize][at..at + span].to_vec();
                    }
                }
            }
            if let Some(buffer) = shares {
                let cells = self.timed(Kind::Copy, || self.card.fetch_range(&*buffer, 0, 2 * heads)).map_err(device)?;
                if let Some(total) = self.covector_shares.borrow_mut().as_mut() {
                    for (t, c) in total.iter_mut().zip(cells) {
                        *t += c;
                    }
                }
            }
            words.dsshare = 0;
        }
        self.mark("reverse_launch");
        self.status(&status)?;
        self.mark("status_wait");
        // [realization; theory, November 13, P58 item 3] The training path's faces (`narrow`, no port, no logits, no kept rows): each open site's
        // mass at its class and its total, `(m_c, T)`, the words the learner's comparison reads of a face, gathered on the card and fetched alone
        // (8 and 16 octets a site, where the whole faces are 8 octets a site and class). The same pairs as the whole faces give.
        if self.narrow.get() && keep.is_none() && !logits && regions.iter().all(|r| r.port.is_none()) {
            if (0..sites).any(|t| unresolved[t] != 0 && classes[t] as usize >= a) {
                return Err(TowerError::Refused("an open site whose class is outside the alphabet"));
            }
            let picked = self.timed(Kind::Alloc, || self.take::<u64>(sites.max(1))).map_err(device)?;
            let (mut mp, mut pp) = (masses.device_ptr(), picked.device_ptr());
            self.launch("field_face_at_class", Self::cells(sites as u64), THREADS, &mut [arg(words), arg(&mut mp), arg(&mut pp)])?;
            let picked = self.timed(Kind::Copy, || card.fetch_range(&picked, 0, sites)).map_err(device)?;
            let totals = self.timed(Kind::Copy, || card.fetch_range(&totals, 0, sites)).map_err(device)?;
            let mut out = self.narrow_out.borrow_mut();
            for r in 0..regions.len() {
                let span = region_off[r] as usize..region_off[r + 1] as usize;
                out.push(span.map(|t| (unresolved[t] != 0).then(|| (u128::from(picked[t]), totals[t] as u128))).collect());
            }
            return Ok((Vec::new(), Vec::new(), Rows::new(), Vec::new()));
        }
        let masses = self.timed(Kind::Copy, || card.fetch_range(&masses, 0, sites * a)).map_err(device)?;
        let totals = self.timed(Kind::Copy, || card.fetch_range(&totals, 0, sites)).map_err(device)?;
        let zs = if logits { self.timed(Kind::Copy, || card.fetch_range(&z, 0, sites * a)).map_err(device)? } else { Vec::new() };
        // The kept rows: each named site's row of each still head at the last tick, with its shares.
        let mut rows = Rows::new();
        if let Some(keep) = keep {
            let tick = &ticks[ticks.len() - 1];
            for &i in keep {
                if i >= sites {
                    return Err(TowerError::Refused("a landmark site outside its region"));
                }
                let mut heads_rows = Vec::new();
                for h in (0..heads).filter(|h| h % d.frames < d.still) {
                    let row = self.timed(Kind::Copy, || card.fetch_range(&tick.e, h * pairs + i * sites, sites)).map_err(device)?;
                    // A row's shares make its whole, `2^63` (§14.11): the host holds the same mass.
                    heads_rows.push((row.into_iter().enumerate().filter(|&(_, e)| e != 0).map(|(j, e)| (j as u32, e)).collect(), 1u64 << SHARE_BITS));
                }
                rows.push(heads_rows);
            }
        }
        // The echoes (§15.3): the round trips' mean over the heads and the consecutive ticks, to the nearest
        // numerator (the host's `pass`).
        let mut out_echo = Vec::new();
        if logits {
            let trips = self.timed(Kind::Copy, || card.fetch_range(&trips, 0, sites)).map_err(device)?;
            let read = ((d.ticks.saturating_sub(1) * d.heads).max(1)) as u128;
            for r in 0..regions.len() {
                out_echo.push((region_off[r] as usize..region_off[r + 1] as usize).map(|t| ((trips[t] as u128 + read / 2) / read) as u64).collect());
            }
        }
        let (mut out, mut out_z) = (Vec::with_capacity(regions.len()), Vec::new());
        for r in 0..regions.len() {
            let span = region_off[r] as usize..region_off[r + 1] as usize;
            out.push(span.clone().map(|t| (unresolved[t] != 0).then(|| TowerFace { masses: masses[t * a..(t + 1) * a].iter().map(|&v| v as u128).collect(), total: totals[t] as u128 })).collect());
            if logits {
                out_z.push(span.map(|t| (unresolved[t] != 0).then(|| zs[t * a..(t + 1) * a].to_vec())).collect());
            }
        }
        // [P57 item 2] The charts by stage, each region's open rows in site order.
        if let Some(out) = self.tick_charts.borrow_mut().as_mut() {
            let stages = stage_rows.unwrap_or_default();
            let mut row = 0usize;
            for r in 0..regions.len() {
                let open = (region_off[r] as usize..region_off[r + 1] as usize).filter(|&t| unresolved[t] != 0).count();
                out.push(stages.iter().map(|s| s[row * dw..(row + open) * dw].to_vec()).collect());
                row += open;
            }
        }
        Ok((out, out_z, rows, out_echo))
    }

    /// [realization; theory, November 13, P60 item 2] **The opening's comparison's forward** (the host's `Field::cavity_forward` and
    /// `Field::opening_read`): the cavity moments from the standing moments' kept operands (`field_cavity_moment_all`), the cavity openings
    /// (`field_cavity_open`, then the moment's chart on the cavity moment), and at every compared place the lane chart, the opening's lift `R⁰ r̂ + b⁰`,
    /// the face through the encoding and its masses, by the field's own entries with the words' open-site mask set to the compared places. Every
    /// word a later kernel reads is written first: the cavity moment is zeroed (its still modes stay zero), the chart, the lift and the face are read
    /// at the compared places alone. Launches a batch: one, two and the moment's chart's, then the chart, the lift, `tied` and the face.
    fn opening_forward(&self, field: &Field, words: &mut Words, regions: &[Region], st: &Staged<'c>, keep: Option<MomentKeep<'c>>) -> Result<Opening<'c>> {
        let d = field.declaration;
        let (dw, m2, a, sites, tm, lanes) = (d.width, 2 * d.complex(), d.alphabet, st.sites, d.moment_modes(), d.lanes);
        let l = field.layout();
        let mut mask = vec![0u8; sites.max(1)];
        for (r, region) in regions.iter().enumerate() {
            let first = st.region_off[r] as usize;
            let end = region.port.map_or(region.classes.len(), |p| p.start);
            mask[first..first + end].fill(1);
        }
        let mask = self.timed(Kind::Copy, || self.take_up(&mask)).map_err(device)?;
        let cmoment = self.timed(Kind::Alloc, || self.take_zeroed::<i64>((sites * m2).max(1))).map_err(device)?;
        let alloc64 = |len: usize| self.timed(Kind::Alloc, || self.take::<i64>(len.max(1))).map_err(device);
        let (sb, sa) = (alloc64(tm * 2 * sites)?, alloc64(tm * 2 * sites)?);
        if let Some(k) = keep.as_ref() {
            let (mut wsp, mut cmp, mut fw) = (k.ws.device_ptr(), k.cmap.device_ptr(), *words);
            let (mut bp, mut ap, mut upp, mut dnp) = (k.before.device_ptr(), k.after.device_ptr(), k.up.device_ptr(), k.down.device_ptr());
            let (mut sbp, mut sap, mut cp) = (sb.device_ptr(), sa.device_ptr(), cmoment.device_ptr());
            let (mut stride, mut pre_stride) = ((2 * sites) as u64, (2 * (sites + regions.len())) as u64);
            self.launch_grid("field_cavity_moment_all", Dim3 { x: Self::cells(sites as u64), y: tm as u32, z: 1 }, THREADS, 0, &mut [arg(&mut wsp), arg(&mut cmp), arg(&mut fw), arg(&mut bp), arg(&mut ap), arg(&mut upp), arg(&mut dnp), arg(&mut sbp), arg(&mut sap), arg(&mut cp), arg(&mut stride), arg(&mut pre_stride)])?;
        }
        let cx = alloc64(sites * dw)?;
        let mut cxp = cx.device_ptr();
        self.launch("field_cavity_open", Self::cells((sites * dw) as u64), THREADS, &mut [arg(words), arg(&mut cxp)])?;
        let (mface, mface_bias, rmface) = moment_face(field);
        self.affine("field_affine_x64", words, mface, mface_bias, rmface, dw, m2, cmoment.device_ptr(), m2, 0, dw, cx.device_ptr(), false)?;
        let mut cw = *words;
        cw.unresolved = mask.device_ptr();
        let read = self.timed(Kind::Alloc, || self.take::<i32>((sites * dw).max(1))).map_err(device)?;
        let scale = self.timed(Kind::Alloc, || self.take::<i128>((sites * lanes).max(1))).map_err(device)?;
        self.chart(&mut cw, cx.device_ptr(), &read, &scale, true)?;
        let reach = field.theta[l.opening..l.opening + dw * dw].iter().map(|v| v.unsigned_abs() as u64).max().unwrap_or(0);
        let lift = alloc64(sites * dw)?;
        self.affine("field_affine_x32", &mut cw, l.opening as u64, l.opening_bias as u64, reach, dw, dw, read.device_ptr(), dw, lift.device_ptr(), dw, 0, true)?;
        let z = alloc64(sites * a)?;
        {
            let (mut enc, mut cb, mut yp, mut zp) = (cw.enc, cw.read_bias, lift.device_ptr(), z.device_ptr());
            self.launch("field_tied_face", Self::cells((sites * a) as u64), THREADS, &mut [arg(&mut cw), arg(&mut enc), arg(&mut cb), arg(&mut yp), arg(&mut zp)])?;
        }
        let masses = self.timed(Kind::Alloc, || self.take::<u64>((sites * a).max(1))).map_err(device)?;
        let totals = self.timed(Kind::Alloc, || self.take::<i128>(sites.max(1))).map_err(device)?;
        let (mut zp, mut mp, mut tp) = (z.device_ptr(), masses.device_ptr(), totals.device_ptr());
        self.launch("field_face", Self::warps(sites as u64), THREADS, &mut [arg(&mut cw), arg(&mut zp), arg(&mut mp), arg(&mut tp)])?;
        self.mark("opening_forward");
        Ok(Opening { mask, keep, cmoment, sb, sa, read, scale, lift, masses, totals })
    }

    /// [realization; theory, November 13, P60 item 2] **The opening's comparison's return** (the host's `Field::opening_compare_return`): at every
    /// compared place the face covector at unit gain, through the class biases, the encoding (`tied`), the opening's lift and bias, the chart and its
    /// lanes, by the field's own entries under the compared places' mask; the cavity opening's covector into the unresolved row and the neighbours'
    /// strand rows (`field_encoding`), the moment's chart and bias, and the cavity moments' covector through their return and their clocks
    /// (`field_cavity_terms_all` and `field_cavity_scan_all`, `field_cavity_return_paced_all`, `field_cavity_pace_back_all`), added into `g` and into the pass's clock covectors
    /// the words name.
    #[allow(clippy::type_complexity)]
    fn opening_back(&self, field: &Field, words: &mut Words, op: &Opening<'c>, g: &CardBuffer<'c, i128>, (classes, unresolved, site_pos, mix_off, mix_class, mix_share): (&[u32], &[u8], &[u32], &[u32], &[u32], &[u32]), sites: usize) -> Result<()> {
        let d = field.declaration;
        let (dw, m2, a, tm) = (d.width, 2 * d.complex(), d.alphabet, d.moment_modes());
        let l = field.layout();
        let regions = words.r as usize;
        let mut cw = *words;
        cw.unresolved = op.mask.device_ptr();
        let alloc64 = |len: usize| self.timed(Kind::Alloc, || self.take::<i64>(len.max(1))).map_err(device);
        let zeroed64 = |len: usize| self.timed(Kind::Alloc, || self.take_zeroed::<i64>(len.max(1))).map_err(device);
        // The face's covector at unit gain (no domain weighs it), written at every cell (zero past the compared places).
        let dz = alloc64(sites * a)?;
        let (mut mp, mut tp, mut dzp) = (op.masses.device_ptr(), op.totals.device_ptr(), dz.device_ptr());
        self.launch("field_face_covector", Self::cells((sites * a) as u64), THREADS, &mut [arg(&mut cw), arg(&mut mp), arg(&mut tp), arg(&mut dzp)])?;
        self.outer(&mut cw, g, words.read_bias, a, 0, dz.device_ptr(), a, 0, 0, false, true)?;
        let dy = alloc64(sites * dw)?;
        {
            let (mut gp, mut enc, mut dzp, mut yp, mut dyp) = (g.device_ptr(), cw.enc, dz.device_ptr(), op.lift.device_ptr(), dy.device_ptr());
            let tiles = (sites as u64).div_ceil(64);
            self.launch("field_tied_back_e", Self::cells(a as u64 * dw as u64 * tiles), THREADS, &mut [arg(&mut cw), arg(&mut gp), arg(&mut enc), arg(&mut dzp), arg(&mut yp)])?;
            let mut enc = cw.enc;
            self.launch("field_tied_back_y", Self::cells((sites * dw) as u64), THREADS, &mut [arg(&mut cw), arg(&mut enc), arg(&mut dzp), arg(&mut dyp)])?;
        }
        self.outer(&mut cw, g, l.opening_bias as u64, dw, 0, dy.device_ptr(), dw, 0, 0, false, true)?;
        self.outer(&mut cw, g, l.opening as u64, dw, dw, dy.device_ptr(), dw, op.read.device_ptr(), dw, false, true)?;
        let dr = alloc64(sites * dw)?;
        self.transposed(&mut cw, l.opening as u64, dw, dw, dy.device_ptr(), dw, dr.device_ptr(), false, true)?;
        let dx = zeroed64(sites * dw)?;
        self.ratio_adjoint(&mut cw, op.read.device_ptr(), op.scale.device_ptr(), dr.device_ptr(), 0, dx.device_ptr(), true)?;
        // The cavity opening's rows: the unresolved row for every compared place, its neighbours' rows of theirs (a carried neighbour's mixture by
        // its shares), the entries partitioned by row once for each encoding, as the reverse's opening.
        let mask = self.timed(Kind::Copy, || self.card.fetch_range(&op.mask, 0, sites)).map_err(device)?;
        let terms = |s: usize, t: u32| -> Vec<(usize, u32, u32)> {
            let (from, to) = (mix_off[s] as usize, mix_off[s + 1] as usize);
            if from == to {
                return vec![(if unresolved[s] != 0 { a } else { classes[s] as usize }, t, 1 << STATE_BITS)];
            }
            (from..to).map(|k| (mix_class[k] as usize, t, mix_share[k])).collect()
        };
        let compared = |t: usize| mask[t] != 0;
        let own: Vec<(usize, u32, u32)> = (0..sites).filter(|&t| compared(t)).map(|t| (a, t as u32, 1 << STATE_BITS)).collect();
        let before: Vec<(usize, u32, u32)> = (0..sites).filter(|&t| compared(t) && site_pos[t] > 0).flat_map(|t| terms(t - 1, t as u32)).collect();
        let after: Vec<(usize, u32, u32)> = (0..sites).filter(|&t| compared(t) && t + 1 < sites && site_pos[t + 1] > 0).flat_map(|t| terms(t + 1, t as u32)).collect();
        for (base, rows) in [(words.enc, own), (words.enc_before, before), (words.enc_after, after)] {
            let (rows_sites, rows_shares, segments) = encoding_partition(&rows, a + 1);
            let count = (segments.len() / 3) as u32;
            if count == 0 {
                continue;
            }
            let rows_sites_c = self.timed(Kind::Copy, || self.take_up(&rows_sites)).map_err(device)?;
            let rows_shares_c = self.timed(Kind::Copy, || self.take_up(&rows_shares)).map_err(device)?;
            let segments_c = self.timed(Kind::Copy, || self.take_up(&segments)).map_err(device)?;
            let (mut gp, mut dxp, mut rsp, mut rwp, mut sgp, mut count, mut base) = (g.device_ptr(), dx.device_ptr(), rows_sites_c.device_ptr(), rows_shares_c.device_ptr(), segments_c.device_ptr(), count, base);
            self.launch("field_encoding", Self::cells(count as u64 * dw as u64), THREADS, &mut [arg(words), arg(&mut gp), arg(&mut dxp), arg(&mut rsp), arg(&mut rwp), arg(&mut sgp), arg(&mut count), arg(&mut base)])?;
        }
        // The moment's chart on the cavity moment: `δC += Σ_t δx_t s_tᵀ`, `δb += Σ_t δx_t`, `δs_t = Cᵀ δx_t` (zero past the compared places).
        let (mface, mface_bias, _) = moment_face(field);
        self.outer(&mut cw, g, mface_bias, dw, 0, dx.device_ptr(), dw, 0, 0, false, true)?;
        self.outer(&mut cw, g, mface, dw, m2, dx.device_ptr(), dw, op.cmoment.device_ptr(), m2, true, true)?;
        let dq = zeroed64(sites * m2)?;
        self.transposed(&mut cw, mface, dw, m2, dx.device_ptr(), dw, dq.device_ptr(), false, true)?;
        let Some(k) = op.keep.as_ref().filter(|_| tm > 0) else {
            return Ok(());
        };
        let dm = self.timed(Kind::Alloc, || self.take_zeroed::<i128>((sites * m2).max(1))).map_err(device)?;
        let (mut cp, mut dmp) = (dq.device_ptr(), dm.device_ptr());
        self.launch("field_moment_accumulate", Self::cells((sites * m2) as u64), THREADS, &mut [arg(words), arg(&mut cp), arg(&mut dmp)])?;
        // The cavity moments' return: each moment mode's covector, admitted by the return's certificate, its released prefix and the cavity's far
        // prefixes, the return at every site into the strands' rows, then the clocks' covector.
        let (strand, prefix) = ((2 * sites) as u64, (2 * (sites + regions)) as u64);
        let ds = alloc64(tm * 2 * sites)?;
        let q = self.timed(Kind::Alloc, || self.take::<i128>((tm * 2 * (sites + regions)).max(1))).map_err(device)?;
        let (d_before, d_after) = (self.timed(Kind::Alloc, || self.take::<i128>((tm * 2 * sites).max(1))).map_err(device)?, self.timed(Kind::Alloc, || self.take::<i128>((tm * 2 * sites).max(1))).map_err(device)?);
        let ok = self.timed(Kind::Alloc, || self.take_up(&vec![0u8; (tm * regions).max(1)])).map_err(device)?;
        let (ws, cmap) = self.moment_modes(field, words, regions, sites, &ok)?;
        let (mut wsp, mut cmp, mut dmp) = (ws.device_ptr(), cmap.device_ptr(), dm.device_ptr());
        let (mut dsp, mut qp, mut dbp, mut dap, mut gp, mut none) = (ds.device_ptr(), q.device_ptr(), d_before.device_ptr(), d_after.device_ptr(), g.device_ptr(), 0u64);
        let (mut w2, mut base_b, mut base_a, mut tm32) = (*words, l.moment_before as u64, l.moment_after as u64, tm as u32);
        let (mut one32, mut stride, mut pre_stride) = (1u32, strand, prefix);
        let grid = |x: usize| Dim3 { x: x.max(1) as u32, y: tm as u32, z: 1 };
        self.launch("field_moment_ds_all", Self::cells((sites * tm) as u64), THREADS, &mut [arg(&mut w2), arg(&mut dmp), arg(&mut cmp), arg(&mut tm32), arg(&mut dsp)])?;
        let mut fw = *words;
        self.launch_grid("field_moment_admit_paced_all", grid(regions), MOMENT_BLOCK, 3 * MOMENT_BLOCK * 16, &mut [arg(&mut wsp), arg(&mut cmp), arg(&mut fw), arg(&mut dsp), arg(&mut none), arg(&mut stride), arg(&mut one32)])?;
        self.launch_grid("field_moment_prefix_paced_all", grid(regions), MOMENT_BLOCK, MOMENT_BLOCK * 32, &mut [arg(&mut wsp), arg(&mut cmp), arg(&mut fw), arg(&mut dsp), arg(&mut qp), arg(&mut stride), arg(&mut pre_stride), arg(&mut one32)])?;
        let levels = (2u32..).take_while(|&lv| (1usize << lv) < d.reach).count() as u32;
        let sk_stride = (2 * levels as usize * 2 * (sites + regions)) as u64;
        // [realization; G143] The far prefixes are taken a moment mode at a time: one mode's prefixes (`sk_stride` words) serve every mode in turn,
        // each mode's terms, scan and return launched on its own words (`MomentWords` of 88 octets, its covector, prefix and return at its
        // offsets), so the return's scratch holds one mode's 1/tm of the prefixes every mode would hold at once. The same words and sums.
        let sk = self.timed(Kind::Alloc, || self.take::<i128>((sk_stride as usize).max(1))).map_err(device)?;
        let (mut skp, mut sk_stride_a, mut levels_a, mut one) = (sk.device_ptr(), sk_stride, levels, 1u32);
        for u in 0..tm as u64 {
            let (mut wsu, mut cmu, mut dsu, mut qu, mut dbu, mut dau) = (wsp + 88 * u, cmp + 4 * u, dsp + 8 * stride * u, qp + 16 * pre_stride * u, dbp + 16 * stride * u, dap + 16 * stride * u);
            if levels > 0 {
                // [realization; G141] The far prefixes' terms a thread each, then their scan a warp a row and region.
                self.launch("field_cavity_terms_all", Self::cells((2 * levels as usize * sites) as u64), THREADS, &mut [arg(&mut wsu), arg(&mut cmu), arg(&mut fw), arg(&mut dsu), arg(&mut skp), arg(&mut stride), arg(&mut sk_stride_a), arg(&mut levels_a), arg(&mut one)])?;
                self.launch("field_cavity_scan_all", Self::warps((2 * levels as usize * regions) as u64), THREADS, &mut [arg(&mut wsu), arg(&mut cmu), arg(&mut fw), arg(&mut skp), arg(&mut sk_stride_a), arg(&mut levels_a), arg(&mut one)])?;
            }
            self.launch_grid("field_cavity_return_paced_all", Dim3 { x: Self::cells(sites as u64), y: 1, z: 1 }, THREADS, 0, &mut [arg(&mut wsu), arg(&mut cmu), arg(&mut fw), arg(&mut dsu), arg(&mut qu), arg(&mut skp), arg(&mut dbu), arg(&mut dau), arg(&mut stride), arg(&mut pre_stride), arg(&mut sk_stride_a)])?;
        }
        self.launch("field_moment_strand_return_all", Self::cells((sites * tm) as u64), THREADS, &mut [arg(&mut w2), arg(&mut base_b), arg(&mut base_a), arg(&mut tm32), arg(&mut dbp), arg(&mut dap), arg(&mut gp)])?;
        let (mut bp, mut ap, mut upp, mut dnp) = (k.before.device_ptr(), k.after.device_ptr(), k.up.device_ptr(), k.down.device_ptr());
        let (mut sbp, mut sap) = (op.sb.device_ptr(), op.sa.device_ptr());
        self.launch_grid("field_cavity_pace_back_all", Dim3 { x: Self::cells(sites as u64), y: tm as u32, z: 1 }, THREADS, 0, &mut [arg(&mut wsp), arg(&mut cmp), arg(&mut fw), arg(&mut bp), arg(&mut ap), arg(&mut sbp), arg(&mut sap), arg(&mut dsp), arg(&mut dbp), arg(&mut dap), arg(&mut upp), arg(&mut dnp), arg(&mut stride), arg(&mut pre_stride)])?;
        let _ = &mut none;
        self.mark("opening_back");
        Ok(())
    }

    /// [definition; agent-inferred, November 1] **The site moments of a batch** (§15.1; the host's
    /// `Field::moments_of`, [`holonics::hnn::tower::field::moment`]), every moment mode (a turned head that
    /// is turned, each of its modes) in the same launches: the strands' encodings of each mode's ring
    /// slot gathered at every site (`field_moment_strands_all`), admitted by the l1 certificate, scanned to
    /// the prefix sums and read at every site (`kernels/field_moment.cuh` through its `_all` entries, a mode
    /// to a grid row), and placed at the unframed value's modes.
    fn moments(&self, field: &Field, words: &Words, regions: usize, sites: usize, keep: bool) -> Result<Option<MomentKeep<'c>>> {
        let d = field.declaration;
        let tm = d.moment_modes();
        if tm == 0 {
            return Ok(None);
        }
        let (n, l, card) = (d.modes, field.layout(), self.card);
        let (strand, prefix) = ((2 * sites) as u64, (2 * (sites + regions)) as u64);
        let alloc64 = |len: usize| self.timed(Kind::Alloc, || self.take::<i64>(len.max(1))).map_err(device);
        let (before, after, s) = (alloc64(tm * 2 * sites)?, alloc64(tm * 2 * sites)?, alloc64(tm * 2 * sites)?);
        let (up, down) = (self.timed(Kind::Alloc, || self.take::<i128>((tm * 2 * (sites + regions)).max(1))).map_err(device)?, self.timed(Kind::Alloc, || self.take::<i128>((tm * 2 * (sites + regions)).max(1))).map_err(device)?);
        let ok = self.timed(Kind::Alloc, || self.take_up(&vec![0u8; (tm * regions).max(1)])).map_err(device)?;
        let (ws, cmap) = self.moment_modes(field, words, regions, sites, &ok)?;
        let (mut wsp, mut cmp) = (ws.device_ptr(), cmap.device_ptr());
        let (mut bp, mut ap, mut sp, mut upp, mut dnp, mut none) = (before.device_ptr(), after.device_ptr(), s.device_ptr(), up.device_ptr(), down.device_ptr(), 0u64);
        let (mut w2, mut base_b, mut base_a, mut tm32) = (*words, l.moment_before as u64, l.moment_after as u64, tm as u32);
        let (mut zero32, mut stride, mut pre_stride) = (0u32, strand, prefix);
        // The clock's phases and skins, once, for its moments (the return forms them again for its own).
        self.clock_fill(field, words, sites)?;
        let grid = |x: usize| Dim3 { x: x.max(1) as u32, y: tm as u32, z: 1 };
        let _ = n;
        self.launch("field_moment_strands_all", Self::cells((sites * tm) as u64), THREADS, &mut [arg(&mut w2), arg(&mut base_b), arg(&mut base_a), arg(&mut tm32), arg(&mut bp), arg(&mut ap)])?;
        // The paced kernels read a mode's region by the paced law where its pace is not plain, by the slot's own
        // elsewhere (the same bits there, §16).
        let mut fw = *words;
        self.launch_grid("field_moment_admit_paced_all", grid(regions), MOMENT_BLOCK, 3 * MOMENT_BLOCK * 16, &mut [arg(&mut wsp), arg(&mut cmp), arg(&mut fw), arg(&mut bp), arg(&mut ap), arg(&mut stride), arg(&mut zero32)])?;
        self.launch_grid("field_moment_prefix_paced_all", grid(regions), MOMENT_BLOCK, MOMENT_BLOCK * 32, &mut [arg(&mut wsp), arg(&mut cmp), arg(&mut fw), arg(&mut bp), arg(&mut upp), arg(&mut stride), arg(&mut pre_stride), arg(&mut zero32)])?;
        self.launch_grid("field_moment_prefix_paced_all", grid(regions), MOMENT_BLOCK, MOMENT_BLOCK * 32, &mut [arg(&mut wsp), arg(&mut cmp), arg(&mut fw), arg(&mut ap), arg(&mut dnp), arg(&mut stride), arg(&mut pre_stride), arg(&mut zero32)])?;
        self.launch_grid("field_moment_paced_all", Dim3 { x: Self::cells(sites as u64), y: tm as u32, z: 1 }, THREADS, 0, &mut [arg(&mut wsp), arg(&mut cmp), arg(&mut fw), arg(&mut bp), arg(&mut ap), arg(&mut upp), arg(&mut dnp), arg(&mut sp), arg(&mut stride), arg(&mut pre_stride)])?;
        self.launch("field_moment_scatter_all", Self::cells((sites * tm) as u64), THREADS, &mut [arg(&mut w2), arg(&mut sp), arg(&mut cmp), arg(&mut tm32)])?;
        let _ = &mut none;
        // [P60 item 2] The strands, prefixes, admissions and modes' words kept where the opening is compared.
        Ok(keep.then_some(MomentKeep { before, after, up, down, _ok: ok, ws, cmap }))
    }

    /// The moment kernels' words for every moment mode, in the order of the moment index (`MomentWords` in
    /// `kernels/field_moment.cuh`, an array of them), each mode's ring slot's resident phasors and skin and
    /// its admission flags `ok[u][r]`; and the map from a moment mode to the unframed value's mode `h n + l`.
    fn moment_modes(&self, field: &Field, words: &Words, regions: usize, sites: usize, ok: &CardBuffer<'c, u8>) -> Result<(Pooled<'c, u64>, Pooled<'c, u32>)> {
        let d = field.declaration;
        let (mut packed, mut cmap) = (Vec::new(), Vec::new());
        for h in (0..d.heads).filter(|&h| d.carries_moment(h)) {
            for li in 0..d.modes {
                let slot = li * (d.frames - d.still) + h % d.frames - d.still;
                let offset: usize = field.rings()[..slot].iter().map(|(_, ring)| ring.len()).sum();
                let (period, ring) = &field.rings()[slot];
                let u = d.moment_index(h) + li;
                // `MomentWords`: `R, T` (two words of 32 bits), then the pointers and counts, 8 octets each.
                packed.extend([
                    regions as u64 | (sites as u64) << 32,
                    words.region_off,
                    words.site_region,
                    words.site_pos,
                    words.phasor + 16 * offset as u64,
                    *period as u64,
                    ring.len() as u64,
                    words.decay + 8 * (slot * d.reach) as u64,
                    d.reach as u64,
                    ok.device_ptr() + (u * regions) as u64,
                    words.status,
                ]);
                // A depth ring's mode carries no moment (its map's top bit, read by the moment kernels).
                cmap.push((h * d.modes + li) as u32 | if d.is_depth(h) { 1 << 31 } else { 0 });
            }
        }
        let card = self.card;
        Ok((self.timed(Kind::Copy, || self.take_up(&packed)).map_err(device)?, self.timed(Kind::Copy, || self.take_up(&cmap)).map_err(device)?))
    }

    /// [definition; §16.44] **A blank's clock returns through its face** (the host's `Field::blank_return`): from each
    /// silent site's rates' covector `δκ` the face's logits' covector (held `2^30` finer), the encoding's bias and rows, the
    /// lift's covector (held `2^16` finer), the lift's bias and the read matrix, the chart's return and the lane adjoint, and
    /// the state's covector `dx` takes it.
    #[allow(clippy::too_many_arguments)]
    fn blank_back(&self, field: &Field, words: &mut Words, clock: &CardClock<'c>, dkappa: &CardBuffer<'c, i128>, g: &CardBuffer<'c, i128>, dx: &CardBuffer<'c, i64>, sites: usize) -> Result<()> {
        let d = field.declaration;
        let (dw, a) = (d.width, d.alphabet);
        let l = field.layout();
        let dz = self.timed(Kind::Alloc, || self.take::<i128>((sites * a).max(1))).map_err(device)?;
        // The faces were read at the sites a clock reads alone (`blank_clock`), and return there alone.
        let unresolved = words.unresolved;
        words.unresolved = words.blank_read;
        let (mut dkp, mut dzp) = (dkappa.device_ptr(), dz.device_ptr());
        self.launch("field_blank_dz", Self::cells((sites * a) as u64), THREADS, &mut [arg(words), arg(&mut dkp), arg(&mut dzp)])?;
        let tiles = (sites as u64).div_ceil(64);
        {
            let (mut gp, mut enc, mut bias, mut dzp, mut yp) = (g.device_ptr(), words.enc, words.read_bias, dz.device_ptr(), clock.lift.device_ptr());
            self.launch("field_blank_bias_enc", Self::cells(a as u64 * (dw as u64 + 1) * tiles), THREADS, &mut [arg(words), arg(&mut gp), arg(&mut enc), arg(&mut bias), arg(&mut dzp), arg(&mut yp)])?;
        }
        let dy = self.timed(Kind::Alloc, || self.take::<i64>((sites * dw).max(1))).map_err(device)?;
        {
            let (mut enc, mut dzp, mut dyp) = (words.enc, dz.device_ptr(), dy.device_ptr());
            self.launch("field_blank_dy", Self::cells((sites * dw) as u64), THREADS, &mut [arg(words), arg(&mut enc), arg(&mut dzp), arg(&mut dyp)])?;
        }
        {
            let (mut gp, mut read, mut bias, mut dyp, mut rp) = (g.device_ptr(), words.read, l.lift_bias as u64, dy.device_ptr(), clock.fread.device_ptr());
            self.launch("field_blank_lift_read", Self::cells(dw as u64 * (dw as u64 + 1) * tiles), THREADS, &mut [arg(words), arg(&mut gp), arg(&mut read), arg(&mut bias), arg(&mut dyp), arg(&mut rp)])?;
        }
        // [realization; theory, November 13, P58 item 2] `dr` and `back` unzeroed. `field_transposed` (no accumulation) writes every column of a
        // site the clock read (`blank_read`, set above), and `dr`'s one reader, `field_ratio_adjoint` on the same sites, reads its covector only
        // there. `field_ratio_adjoint` with no base writes every word of `back`, zero at a site it skips and every lane's coordinates elsewhere,
        // before `field_blank_dx` reads it.
        let dr = self.timed(Kind::Alloc, || self.take::<i64>((sites * dw).max(1))).map_err(device)?;
        self.transposed(words, words.read, dw, dw, dy.device_ptr(), dw, dr.device_ptr(), false, true)?;
        let back = self.timed(Kind::Alloc, || self.take::<i64>((sites * dw).max(1))).map_err(device)?;
        self.ratio_adjoint(words, clock.fread.device_ptr(), clock.fscale.device_ptr(), dr.device_ptr(), 0, back.device_ptr(), true)?;
        let (mut bp, mut dxp) = (back.device_ptr(), dx.device_ptr());
        let done = self.launch("field_blank_dx", Self::cells((sites * dw) as u64), THREADS, &mut [arg(words), arg(&mut bp), arg(&mut dxp)]);
        words.unresolved = unresolved;
        done
    }

    /// [definition; §16.44] **The clocks a tick's blanks run at** (the host's `pass`): the face each unresolved site's state
    /// reads now (the chart, the lift, the encoding, at temperature one), each silent site's rate from its shares
    /// (`field_blank_rates`), and the clocks, frames and moments read again on those rates, into a tick's own buffers; the
    /// words are left pointing at them.
    fn blank_clock(&self, field: &Field, words: &mut Words, regions: usize, sites: usize) -> Result<CardClock<'c>> {
        let d = field.declaration;
        let (dw, a, n, m2, paced) = (d.width, d.alphabet, d.modes, 2 * d.complex(), d.paced_heads());
        // [realization; theory, November 13, P58 item 2] The blank's read, scale, lift and totals are taken without zeroing where no clock is read
        // at named sites: the face kernels write each at the sites the clock reads (`blank_read`) and every reader reads them only there:
        // `field_affine` and `field_ratio_adjoint` (blank_back) on the same sites, `field_blank_bias_enc` and `field_blank_lift_read` only where
        // the blank's face covector `dz` and its lift's `dy` are nonzero (written zero off those sites, by `field_blank_dz` and `field_blank_dy`),
        // `field_blank_rates` and `field_blank_dz` on the same sites, and `field_pace_c_back` where `blank_read[t]`. The clocks' reading at named
        // sites (`clock_sites`) fetches a silent site's face that the clock may not have read, so it keeps them zeroed.
        let zeroed = self.clock_sites.borrow().is_some();
        let fread = if zeroed { self.timed(Kind::Alloc, || self.take_zeroed::<i32>(sites * dw)) } else { self.timed(Kind::Alloc, || self.take::<i32>(sites * dw)) }.map_err(device)?;
        let fscale = if zeroed { self.timed(Kind::Alloc, || self.take_zeroed::<i128>(sites * d.lanes)) } else { self.timed(Kind::Alloc, || self.take::<i128>(sites * d.lanes)) }.map_err(device)?;
        // [the unified-theory reading of November 6, 08:16] The faces are read only at the sites a clock reads (`blank_read`): the
        // face kernels read the open sites, so they are given those sites as the open ones, and the region's own are restored
        // before the clocks.
        let unresolved = words.unresolved;
        words.unresolved = words.blank_read;
        self.chart(words, words.x, &fread, &fscale, true)?;
        let lift = if zeroed { self.timed(Kind::Alloc, || self.take_zeroed::<i64>(sites * dw)) } else { self.timed(Kind::Alloc, || self.take::<i64>(sites * dw)) }.map_err(device)?;
        let lift_bias = field.layout().lift_bias as u64;
        self.affine("field_affine_x32", words, words.read, lift_bias, words.rread, dw, dw, fread.device_ptr(), dw, lift.device_ptr(), dw, 0, true)?;
        let z = self.timed(Kind::Alloc, || self.take::<i64>(sites * a)).map_err(device)?;
        {
            let (mut enc, mut cb, mut yp, mut zp) = (words.enc, words.read_bias, lift.device_ptr(), z.device_ptr());
            self.launch("field_tied_face", Self::cells((sites * a) as u64), THREADS, &mut [arg(words), arg(&mut enc), arg(&mut cb), arg(&mut yp), arg(&mut zp)])?;
        }
        let masses = self.timed(Kind::Alloc, || self.take::<u64>(sites * a)).map_err(device)?;
        let totals = if zeroed { self.timed(Kind::Alloc, || self.take_zeroed::<i128>(sites)) } else { self.timed(Kind::Alloc, || self.take::<i128>(sites)) }.map_err(device)?;
        {
            let (mut zp, mut mp, mut tp) = (z.device_ptr(), masses.device_ptr(), totals.device_ptr());
            self.launch("field_face", Self::warps(sites as u64), THREADS, &mut [arg(words), arg(&mut zp), arg(&mut mp), arg(&mut tp)])?;
        }
        let alloc64 = |len: usize| self.timed(Kind::Alloc, || self.take::<i64>(len.max(1))).map_err(device);
        let rates = alloc64(paced * sites)?;
        let clock = CardClock {
            kappa: alloc64(paced * sites)?,
            tau: alloc64(paced * sites)?,
            sigma: alloc64(paced * sites)?,
            saddr: alloc64(3 * paced * n * sites)?,
            plain: self.timed(Kind::Alloc, || self.take::<u8>((paced * regions).max(1))).map_err(device)?,
            pframe: alloc64(2 * paced * sites * n)?,
            moment: self.timed(Kind::Alloc, || self.take_zeroed::<i64>((sites * m2).max(1))).map_err(device)?,
            rates,
            masses,
            totals,
            fread,
            fscale,
            lift,
        };
        (words.blank_masses, words.blank_totals) = (clock.masses.device_ptr(), clock.totals.device_ptr());
        let mut rp = clock.rates.device_ptr();
        self.launch("field_blank_rates", Self::cells((paced * sites) as u64), THREADS, &mut [arg(words), arg(&mut rp)])?;
        words.unresolved = unresolved;
        set_clock(words, Some(&clock), [0; 7]);
        self.launch("field_paces", Self::cells((paced * regions) as u64), THREADS, &mut [arg(words)])?;
        self.launch("field_skin_addresses", Self::cells((paced * n * sites) as u64), THREADS, &mut [arg(words)])?;
        self.launch("field_pframes", Self::cells((paced * sites * n) as u64), THREADS, &mut [arg(words)])?;
        self.moments(field, words, regions, sites, false)?;
        Ok(clock)
    }

    fn chart(&self, words: &mut Words, x: u64, read: &CardBuffer<'c, i32>, scale: &CardBuffer<'c, i128>, only_unresolved: bool) -> Result<()> {
        let (mut x, mut rp, mut sp, mut u) = (x, read.device_ptr(), scale.device_ptr(), u32::from(only_unresolved));
        self.launch("field_chart", Self::warps(words.t as u64), THREADS, &mut [arg(words), arg(&mut x), arg(&mut rp), arg(&mut sp), arg(&mut u)])
    }

    #[allow(clippy::too_many_arguments)]
    fn affine(&self, entry: &'static str, words: &mut Words, weight: u64, bias: u64, wmax: u64, rows: usize, cols: usize, x: u64, x_stride: usize, out: u64, out_stride: usize, add: u64, only_unresolved: bool) -> Result<()> {
        let (mut weight, mut bias, mut wmax, mut rows32, mut cols32) = (weight, bias, wmax, rows as u32, cols as u32);
        let (mut x, mut xs, mut out, mut os, mut add, mut u) = (x, x_stride as u64, out, out_stride as u64, add, u32::from(only_unresolved));
        // [realization; P61 item 4] Every forward map in the tile form (`map_tile` in `kernels/field.cu`): a block a tile of 64 outputs by 64
        // sites, whatever the map's shape; the cell map and its tiling are retired with it.
        let x64 = entry.ends_with("x64");
        let launched = if x64 { "field_affine_tiled_x64" } else { "field_affine_tiled_x32" };
        let grid = (rows as u64).div_ceil(64).saturating_mul((words.t as u64).div_ceil(64)).clamp(1, 65_535) as u32;
        self.launch(launched, grid, THREADS, &mut [arg(words), arg(&mut weight), arg(&mut bias), arg(&mut wmax), arg(&mut rows32), arg(&mut cols32), arg(&mut x), arg(&mut xs), arg(&mut out), arg(&mut os), arg(&mut add), arg(&mut u)])?;
        self.map_record((launched, rows32, cols32, u != 0, add != 0), words, Some(cols), Some(wmax), None, &[(x, x64, xs as usize, cols)])
    }

    /// [definition; theory, November 12; the triad record §3 and §4] **The return of two blocks** (`field_affine_two_x64`; tiled,
    /// `field_affine_two_tiled_x64`, where both blocks' weights, the bias and a pass's site rows fit a block's shared memory, the same integers either
    /// way): `add[t][o] += release(Σ_i W[o][i] x_t[i] + Σ_j W₂[o][j] x₂_t[j] + bias[o] 2^24, 24)`, both blocks summed whole in one wide sum with the bias
    /// before the one release, the carrier bound read over both blocks together (the sum of each block's bound as [`Self::affine`] reads it) and refused
    /// at `2^126`. The first block is `(weight, bias, wmax, rows, cols, x, x_stride)` (the pair's return `W` over `c`), the second `(weight₂, wmax₂,
    /// cols₂, x₂, x₂_stride)` (the triads' `W_T` over `c^T`, no bias of its own), both on 64-bit faces.
    #[allow(clippy::type_complexity)]
    fn affine_two(&self, words: &mut Words, (weight, bias, wmax, rows, cols, x, x_stride): (u64, u64, u64, usize, usize, u64, usize), (weight2, wmax2, cols2, x2, x2_stride): (u64, u64, usize, u64, usize), add: u64) -> Result<()> {
        let (mut weight, mut bias, mut wmax, mut rows32, mut cols32, mut x, mut xs) = (weight, bias, wmax, rows as u32, cols as u32, x, x_stride as u64);
        let (mut weight2, mut wmax2, mut cols2_32, mut x2, mut x2s) = (weight2, wmax2, cols2 as u32, x2, x2_stride as u64);
        let (mut out, mut os, mut add) = (0u64, rows as u64, add);
        let tiling = affine_two_tiling(rows, cols, cols2);
        if std::env::var_os("FIELD_AFFINE_TRACE").is_some() {
            eprintln!("FIELD_AFFINE_TRACE entry=field_affine_two_x64 rows={rows} cols={cols} cols2={cols2} tiling={tiling:?}");
        }
        if let Some((per, shared)) = tiling {
            let grid = (words.t as u64).div_ceil(per as u64).clamp(1, 65_535) as u32;
            return self.launch_shared("field_affine_two_tiled_x64", grid, THREADS, shared as u32, &mut [arg(words), arg(&mut weight), arg(&mut bias), arg(&mut wmax), arg(&mut rows32), arg(&mut cols32), arg(&mut x), arg(&mut xs), arg(&mut weight2), arg(&mut wmax2), arg(&mut cols2_32), arg(&mut x2), arg(&mut x2s), arg(&mut out), arg(&mut os), arg(&mut add)]);
        }
        let cells = words.t as u64 * rows as u64;
        self.launch("field_affine_two_x64", Self::cells(cells), THREADS, &mut [arg(words), arg(&mut weight), arg(&mut bias), arg(&mut wmax), arg(&mut rows32), arg(&mut cols32), arg(&mut x), arg(&mut xs), arg(&mut weight2), arg(&mut wmax2), arg(&mut cols2_32), arg(&mut x2), arg(&mut x2s), arg(&mut out), arg(&mut os), arg(&mut add)])
    }

    #[allow(clippy::too_many_arguments)]
    fn transposed(&self, words: &mut Words, weight: u64, rows: usize, cols: usize, y: u64, y_stride: usize, out: u64, accumulate: bool, only_unresolved: bool) -> Result<()> {
        let (mut weight, mut rows32, mut cols32, mut y, mut ys, mut out, mut acc, mut u) = (weight, rows as u32, cols as u32, y, y_stride as u64, out, u32::from(accumulate), u32::from(only_unresolved));
        let grid = (cols as u64).div_ceil(64).saturating_mul((words.t as u64).div_ceil(64)).clamp(1, 65_535) as u32;
        self.launch("field_transposed", grid, THREADS, &mut [arg(words), arg(&mut weight), arg(&mut rows32), arg(&mut cols32), arg(&mut y), arg(&mut ys), arg(&mut out), arg(&mut acc), arg(&mut u)])?;
        self.map_record(("field_transposed", rows32, cols32, u != 0, acc != 0), words, Some(rows), None, Some((weight, rows * cols)), &[(y, true, ys as usize, rows)])
    }

    /// A family's covector `g[at..] += Σ_t y_t ⊗ x_t` (or the bias's `Σ_t y_t` when `x` is zero), with
    /// the host's per-region refusal of its carrier when `x` is given.
    #[allow(clippy::too_many_arguments)]
    fn outer(&self, words: &mut Words, g: &CardBuffer<'c, i128>, at: u64, rows: usize, cols: usize, y: u64, y_stride: usize, x: u64, x_stride: usize, x64: bool, only_unresolved: bool) -> Result<()> {
        let (mut gp, mut at, mut rows32, mut cols32, mut y, mut ys, mut x, mut xs, mut u) = (g.device_ptr(), at, rows as u32, cols as u32, y, y_stride as u64, x, x_stride as u64, u32::from(only_unresolved));
        // [realization; P61 items 4e and 4f] The outer sum in the tile form, then (where `x` is given) the host's per-region refusal, which
        // first reads the outer pass's largest words from a slot of its own (`outer_slot`) and reads a region again only where they leave
        // its bound open. Without a slot the bound reads every region as before.
        let mut maxima = if x != 0 { self.outer_slot()? } else { 0 };
        let entry = if x64 { "field_outer_x64" } else { "field_outer_x32" };
        let grid = if x != 0 {
            (rows as u64).div_ceil(64).saturating_mul((cols as u64).div_ceil(64)).saturating_mul((words.t as u64).div_ceil(OUTER_WALK)).clamp(1, 65_535) as u32
        } else {
            (rows as u64).div_ceil(THREADS as u64).saturating_mul((words.t as u64).div_ceil(OUTER_WALK)).clamp(1, 65_535) as u32
        };
        self.launch(entry, grid, THREADS, &mut [arg(words), arg(&mut gp), arg(&mut at), arg(&mut rows32), arg(&mut cols32), arg(&mut y), arg(&mut ys), arg(&mut x), arg(&mut xs), arg(&mut u), arg(&mut maxima)])?;
        let ops: Vec<(u64, bool, usize, usize)> = if x != 0 { vec![(y, true, ys as usize, rows), (x, x64, xs as usize, cols)] } else { vec![(y, true, ys as usize, rows)] };
        self.map_record((entry, rows32, if x != 0 { cols32 } else { 0 }, u != 0, false), words, None, None, None, &ops)?;
        if x != 0 {
            let bound = if x64 { "field_outer_bound_x64" } else { "field_outer_bound_x32" };
            self.launch(bound, words.r, THREADS, &mut [arg(words), arg(&mut rows32), arg(&mut cols32), arg(&mut y), arg(&mut ys), arg(&mut x), arg(&mut xs), arg(&mut u), arg(&mut maxima)])?;
            self.map_record((bound, rows32, cols32, u != 0, false), words, None, None, None, &[])?;
        }
        Ok(())
    }

    /// [measurement; theory, November 13, P61 item 3] **A site's map's launch read by kind**, under the profile: its launches, ns (the launch just
    /// made) and products (`words.t · rows · cols`). Under `FIELD_TRACE` its operands are read by the bits ruler (`field_yard_rows_max`, each site's
    /// largest word a row), and its tiles of [`MAP_TILE`] sites judged by [`tile_proves`]: `k` terms a sum, the weight's largest `wmax` (read from
    /// the material where not given) against the one operand (a forward or transposed map), or the covector against the input (an outer sum, `k`
    /// the tile's sites). A reading: nothing the field computes moves.
    #[allow(clippy::too_many_arguments)]
    fn map_record(&self, kind: MapKind, words: &Words, k: Option<usize>, wmax: Option<u64>, weight: Option<(u64, usize)>, operands: &[(u64, bool, usize, usize)]) -> Result<()> {
        let Some(profile) = &self.profile else { return Ok(()) };
        let products = u128::from(words.t) * u128::from(kind.1) * u128::from(kind.2.max(1));
        let trace = {
            let mut p = profile.borrow_mut();
            let slot = p.maps.entry(kind).or_insert((0, 0, 0));
            (slot.0, slot.1, slot.2) = (slot.0 + 1, slot.1 + self.last_ns.get(), slot.2 + products);
            p.trace_on
        };
        if !trace || words.t == 0 {
            return Ok(());
        }
        let card = self.card;
        let sites = words.t as usize;
        let rows_max = |ptr: u64, x64: bool, n: usize, stride: usize, width: usize| -> Result<Vec<u64>> {
            let out = self.timed(Kind::Alloc, || self.take::<u64>(n)).map_err(device)?;
            let (mut a, mut kind64, mut nn, mut st, mut wd, mut o) = (ptr, if x64 { 64u32 } else { 32u32 }, n as u64, stride as u64, width as u32, out.device_ptr());
            self.launch("field_yard_rows_max", Self::cells(n as u64), THREADS, &mut [arg(&mut a), arg(&mut kind64), arg(&mut nn), arg(&mut st), arg(&mut wd), arg(&mut o)])?;
            Ok(self.timed(Kind::Copy, || card.fetch_range(&out, 0, n)).map_err(device)?)
        };
        let wmax = match (wmax, weight) {
            (Some(w), _) => u128::from(w),
            (None, Some((offset, len))) => u128::from(rows_max(words.theta + 4 * offset, false, 1, len, len)?[0]),
            (None, None) => 1,
        };
        let maxima: Vec<Vec<u64>> = operands.iter().map(|&(ptr, x64, stride, width)| rows_max(ptr, x64, sites, stride, width)).collect::<Result<_>>()?;
        let bits = |m: u64| 64 - m.leading_zeros();
        let mut p = profile.borrow_mut();
        let b = p.map_bits.entry(kind).or_default();
        b.launches += 1;
        b.w_bits = b.w_bits.max(bits(wmax as u64));
        b.sites += sites as u64;
        for (j, m) in maxima.iter().enumerate().take(2) {
            b.bits[j] = b.bits[j].max(m.iter().copied().map(bits).max().unwrap_or(0));
            b.under31[j] += m.iter().filter(|&&v| v < 1 << 31).count() as u64;
        }
        let (mut all64, mut all96) = (true, true);
        for start in (0..sites).step_by(MAP_TILE) {
            let end = (start + MAP_TILE).min(sites);
            let tile = |j: usize| -> u128 { maxima.get(j).map_or(1, |m| u128::from(m[start..end].iter().copied().max().unwrap_or(0))) };
            let (kk, a, c) = match k {
                Some(terms) => (terms as u128, tile(0), wmax),
                None => ((end - start) as u128, tile(0), tile(1)),
            };
            let (p64, p96) = (tile_proves(kk, a, c, 64), tile_proves(kk, a, c, 96));
            b.tiles += 1;
            b.proved64 += u64::from(p64);
            b.proved96 += u64::from(p96);
            all64 &= p64;
            all96 &= p96;
        }
        b.launches_all64 += u64::from(all64);
        b.launches_all96 += u64::from(all96);
        Ok(())
    }

    /// [realization; P61 item 4f] **An outer pass's slot for its two largest words**: two 64-bit words of a card buffer of `OUTER_SLOTS` slots,
    /// zeroed when it is first taken and again (in the stream's order, after every launch that read the slots before) each time its slots are
    /// spent, so every pass reads a slot zeroed for it alone. The device address of the slot.
    fn outer_slot(&self) -> Result<u64> {
        let mut held = self.outer_maxima.borrow_mut();
        if held.is_none() {
            let buffer = self.timed(Kind::Alloc, || self.take_zeroed::<u64>(2 * OUTER_SLOTS)).map_err(device)?;
            *held = Some((buffer, 0));
        }
        let (buffer, next) = held.as_mut().expect("the slots were just taken");
        if *next == OUTER_SLOTS {
            self.card.stream().memset_u32_async(buffer.device_ptr(), 0, 4 * OUTER_SLOTS).map_err(|e| device(e.into()))?;
            *next = 0;
        }
        let at = buffer.device_ptr() + 16 * *next as u64;
        *next += 1;
        Ok(at)
    }

    fn ratio_adjoint(&self, words: &mut Words, read: u64, scale: u64, cov: u64, base: u64, dst: u64, only_unresolved: bool) -> Result<()> {
        let (mut read, mut scale, mut cov, mut base, mut dst, mut u) = (read, scale, cov, base, dst, u32::from(only_unresolved));
        self.launch("field_ratio_adjoint", Self::warps(words.t as u64), THREADS, &mut [arg(words), arg(&mut read), arg(&mut scale), arg(&mut cov), arg(&mut base), arg(&mut dst), arg(&mut u)])
    }

    /// One tick's reverse on the card (the host's `Field::tick_return`): `b.dx`, the covector of the tick's output faces,
    /// carried back to the covector of its input faces, the level's material covector added into `g`.
    #[allow(clippy::too_many_arguments)]
    #[allow(clippy::too_many_arguments)]
    fn tick_back(&self, field: &Field, words: &mut Words, tick: &Tick<'c>, at: usize, g: &CardBuffer<'c, i128>, b: &Back<'c>, dm: u64, sites: usize, readings: bool) -> Result<()> {
        let card = self.card;
        let d = field.declaration;
        let (dw, m, n, f, heads) = (d.width, d.complex(), d.modes, d.contacts, d.heads);
        let (m2, span) = (2 * m, 2 * n);
        let regions = words.r as usize;
        let rows = sites + regions;
        let paced = d.paced_heads();
        let Back { dx, dr, dc, da, db, dg, dct, dabg, ra, rb, dmid, dy, dyh, dq, dv, dp, ds, cv, cw, pr_back, .. } = b;
        words.qf = tick.qf.device_ptr();
        words.qf32 = tick.qf32.device_ptr();
        words.pq = tick.pq.device_ptr();
        words.pq32 = tick.pq32.device_ptr();
        words.pscale = tick.pscale.device_ptr();
        words.vf = tick.vf.device_ptr();
        words.cls = tick.cls.device_ptr();
        words.class_off = tick.class_off.device_ptr();
        words.members = tick.members.device_ptr();
        words.pn = tick.pn.device_ptr();
        words.pcls = tick.pcls.device_ptr();
        words.poff = tick.poff.device_ptr();
        words.pmem = tick.pmem.device_ptr();
        words.e = tick.e.device_ptr();
        words.sb = tick.sb.device_ptr();
        words.qkv = tick.qkv.device_ptr();
        words.amin = tick.amin.device_ptr();
        words.sw = tick.sw.device_ptr();
        words.sv = tick.sv.device_ptr();
        words.sc = tick.sc.device_ptr();
        words.ce = tick.ce.device_ptr();
        words.pa = tick.pa.device_ptr();
        words.pg = tick.pg.device_ptr();
        words.pgam = tick.pgam.device_ptr();
        words.pqm = tick.pqm.device_ptr();
        words.pkb = tick.pkb.device_ptr();
        words.pb = tick.pb.device_ptr();
        words.pc = tick.pc.device_ptr();
        set_triads(words, tick);
        // The pair contact: x_out = x_mid + W_c c + b_c.
        self.outer(words, g, words.w_bias, dw, 0, dx.device_ptr(), dw, 0, 0, false, false)?;
        self.outer(words, g, words.w, dw, f, dx.device_ptr(), dw, tick.pc.device_ptr(), f, true, false)?;
        self.transposed(words, words.w, dw, f, dx.device_ptr(), dw, dc.device_ptr(), false, false)?;
        // [definition; theory, November 12; the triad record §4] The triads' reverse, by the product rule through the producing operands: `W_T`'s
        // covector `Σ_t δx_t c^T_tᵀ`, the products' covector `δc^T = W_Tᵀ δx` a site, then the legs' covectors `δα`, `δβ`, `δγ` (`field_triad_back`), each
        // slot written by the one place that read it. Their chart's outer sums and transposed read follow the plain contacts' and the circles' below.
        let triads = d.triads;
        let (dctp, dabgp) = (held_at(dct), held_at(dabg));
        if triads > 0 {
            self.outer(words, g, words.wtr, dw, 2 * triads, dx.device_ptr(), dw, words.pct, 2 * triads, true, false)?;
            self.transposed(words, words.wtr, dw, 2 * triads, dx.device_ptr(), dw, dctp, false, false)?;
            let (mut dctp, mut dabgp) = (dctp, dabgp);
            self.launch("field_triad_back", Self::cells((sites * triads) as u64), THREADS, &mut [arg(words), arg(&mut dctp), arg(&mut dabgp)])?;
        }
        let (mut dcp, mut dap, mut dbp) = (dc.device_ptr(), da.device_ptr(), db.device_ptr());
        let (plain, circles) = (d.carry_first(), d.carry);
        if plain > 0 {
            self.launch("field_pair_back", Self::cells((sites * plain) as u64), THREADS, &mut [arg(words), arg(&mut dcp), arg(&mut dap), arg(&mut dbp)])?;
        }
        if circles > 0 {
            // [theory, November 11 17:25 and November 12 (G98)] The circles' reverse: the same (region, circle) jobs in the opposite strand order, with the
            // forward's `γ`, coupled drive and `Q` operand, writing `δγ` and `u` a site and circle; then `δq`, `δℓ` and the drive's `δb = κ u` off the chain
            // on the pair's grid, the divisions out of the chain.
            let mut dgp = dg.device_ptr();
            self.launch("field_pair_scan_back", Self::cells((words.r as usize * circles) as u64), THREADS, &mut [arg(words), arg(&mut dcp), arg(&mut dap), arg(&mut dbp), arg(&mut dgp)])?;
            let (mut dgp, mut dbp) = (dg.device_ptr(), db.device_ptr());
            self.launch("field_pair_gate_back", Self::cells((sites * circles) as u64), THREADS, &mut [arg(words), arg(&mut dgp), arg(&mut dbp)])?;
        }
        self.outer(words, g, words.wa, f, dw, da.device_ptr(), f, tick.read2.device_ptr(), dw, false, false)?;
        self.outer(words, g, words.wb, f, dw, db.device_ptr(), f, tick.read2.device_ptr(), dw, false, false)?;
        self.outer(words, g, words.a_bias, f, 0, da.device_ptr(), f, 0, 0, false, false)?;
        self.outer(words, g, words.b_bias, f, 0, db.device_ptr(), f, 0, 0, false, false)?;
        if circles > 0 {
            self.outer(words, g, words.wg, 2 * circles, dw, dg.device_ptr(), 2 * circles, tick.read2.device_ptr(), dw, false, false)?;
            self.outer(words, g, words.wgb, 2 * circles, 0, dg.device_ptr(), 2 * circles, 0, 0, false, false)?;
        }
        if triads > 0 {
            // The triads' chart: `Σ_t δabg(t) r̂(t)ᵀ` into `A`, `B` and `G`, and `Σ_t δabg(t)` into their biases.
            self.outer(words, g, words.wt, 6 * triads, dw, dabgp, 6 * triads, tick.read2.device_ptr(), dw, false, false)?;
            self.outer(words, g, words.wtb, 6 * triads, 0, dabgp, 6 * triads, 0, 0, false, false)?;
        }
        self.transposed(words, words.wa, f, dw, da.device_ptr(), f, ra.device_ptr(), false, false)?;
        self.transposed(words, words.wb, f, dw, db.device_ptr(), f, rb.device_ptr(), false, false)?;
        if circles > 0 {
            self.transposed(words, words.wg, 2 * circles, dw, dg.device_ptr(), 2 * circles, rb.device_ptr(), true, false)?;
        }
        if triads > 0 {
            // The triads' chart reads the pair chart as `a`, `b` and the circles' do, so its transposed product joins the read's covector.
            self.transposed(words, words.wt, 6 * triads, dw, dabgp, 6 * triads, rb.device_ptr(), true, false)?;
        }
        let (mut rap, mut rbp, mut cells) = (ra.device_ptr(), rb.device_ptr(), (sites * dw) as u64);
        self.launch("field_add", Self::cells(cells), THREADS, &mut [arg(words), arg(&mut rap), arg(&mut rbp), arg(&mut cells)])?;
        self.ratio_adjoint(words, tick.read2.device_ptr(), tick.scale2.device_ptr(), rb.device_ptr(), dx.device_ptr(), dmid.device_ptr(), false)?;
        // The current: x_mid = x_in + O y + b_o.
        self.outer(words, g, words.out_bias, dw, 0, dmid.device_ptr(), dw, 0, 0, false, false)?;
        self.outer(words, g, words.out, dw, m2, dmid.device_ptr(), dw, tick.y.device_ptr(), m2, true, false)?;
        self.transposed(words, words.out, dw, m2, dmid.device_ptr(), dw, dy.device_ptr(), false, false)?;
        // The weights and the contact over each site's support, head by head: the rows' return
        // first, then the columns', which adds the word's second role into the same slots.
        let (mut dyp, mut dyhp) = (dy.device_ptr(), dyh.device_ptr());
        self.launch("field_current_back", Self::cells((heads * sites * n) as u64), THREADS, &mut [arg(words), arg(&mut dyp), arg(&mut dyhp)])?;
        // The current's covector of this tick, where the held rows' currents are read (§16.21).
        if let Some(cov) = self.row_cov.borrow_mut().as_mut().filter(|_| readings) {
            cov[at] = self.timed(Kind::Copy, || self.card.fetch_range(&dyh, 0, heads * sites * span)).map_err(device)?;
        }
        if paced > 0 {
            let (mut dyp, mut yp) = (dy.device_ptr(), tick.y.device_ptr());
            self.launch("field_pace_current_back", Self::cells((paced * sites) as u64), THREADS, &mut [arg(words), arg(&mut dyp), arg(&mut yp)])?;
        }
        card.zero_octets(&dp, 0, 8 * sites * m2).map_err(device)?;
        // The tick's clock's phases and skins and its pairs' skins, formed again for its return (the forward's stores hold a later tick's): the crowd
        // edges and the moments' return read the clock's.
        self.clock_fill(field, words, sites)?;
        self.skin_fill(field, words, sites)?;
        if let Some(profile) = &self.profile {
            let mut p = profile.borrow_mut();
            if p.head_kinds.len() < heads {
                p.head_kinds = (0..heads).map(|h| if !d.carries_moment(h) { "still" } else if d.is_depth(h) { "depth" } else { "paced" }).collect();
            }
        }
        for h in 0..heads {
            self.head.set(Some(h as u32));
            // The crowds' difference arrays start empty a head (§14.10).
            card.zero_octets(&cv, 0, 16 * rows * span).map_err(device)?;
            card.zero_octets(&cw, 0, 16 * rows * span).map_err(device)?;
            let (mut hh, mut dyhp, mut dsp, mut dqp) = (h as u32, dyh.device_ptr(), ds.device_ptr(), dq.device_ptr());
            // [measurement; theory, November 12, P53 item 1 (G120)] The ruler build alone: the rows' memory without their arithmetic, immediately
            // before the entry, its stores and atomics into scratch arrays of the layouts the entry writes, so the state's bytes are the law's.
            #[cfg(feature = "ruler-rows-reads")]
            {
                let pairs = words.pairs as usize;
                let scratch64 = |len: usize| self.timed(Kind::Alloc, || self.take::<i64>(len.max(1))).map_err(device);
                let scratch128 = |len: usize| self.timed(Kind::Alloc, || self.take::<i128>(len.max(1))).map_err(device);
                let (ds_s, dq_s, dp_s) = (scratch64(pairs)?, scratch64(sites * m2)?, scratch64(sites * m2)?);
                let (dpb_s, cds_s) = (scratch128(pairs)?, scratch64(heads * sites * words.slots as usize)?);
                let (cw_s, cv_s, gcov_s) = (scratch128(rows * span)?, scratch128(rows * span)?, scratch128(field.layout().len)?);
                let (mut dsp_s, mut dqp_s, mut dpp_s, mut dpbp_s) = (ds_s.device_ptr(), dq_s.device_ptr(), dp_s.device_ptr(), dpb_s.device_ptr());
                let (mut cdsp_s, mut cwp_s, mut cvp_s, mut gcp_s) = (cds_s.device_ptr(), cw_s.device_ptr(), cv_s.device_ptr(), gcov_s.device_ptr());
                self.launch(
                    "field_yard_rows",
                    Self::rows_grid(sites as u64, REV_ROWS),
                    (REV_ROWS * 32) as u32,
                    &mut [arg(words), arg(&mut hh), arg(&mut dyhp), arg(&mut dsp_s), arg(&mut dqp_s), arg(&mut dpp_s), arg(&mut dpbp_s), arg(&mut cdsp_s), arg(&mut cwp_s), arg(&mut cvp_s), arg(&mut gcp_s)],
                )?;
            }
            self.launch("field_contact_rows", Self::rows_grid(sites as u64, REV_ROWS), (REV_ROWS * 32) as u32, &mut [arg(words), arg(&mut hh), arg(&mut dyhp), arg(&mut dsp), arg(&mut dqp)])?;
            #[cfg(feature = "ruler-bits")]
            {
                self.bits_pairs(words, h, 2, 0, ds.device_ptr(), 3, at, sites)?;
                self.bits_pairs(words, h, 3, 0, words.dpb, 4, at, sites)?;
            }
            if d.carries_moment(h) && !d.is_depth(h) {
                // The head's skins return to its variation (§16), from the pairs' and crowds' covectors just formed.
                let (mut hh, mut dyhp, mut dsp) = (h as u32, dyh.device_ptr(), ds.device_ptr());
                self.launch("field_pace_skin_back", Self::rows_grid(sites as u64, CONTACT_ROWS), (CONTACT_ROWS * 32) as u32, &mut [arg(words), arg(&mut hh), arg(&mut dyhp), arg(&mut dsp)])?;
            }
            let (mut hh, mut dyhp, mut dsp, mut dqp, mut dvp) = (h as u32, dyh.device_ptr(), ds.device_ptr(), dq.device_ptr(), dv.device_ptr());
            self.launch("field_contact_columns", Self::rows_grid(sites as u64, CONTACT_ROWS), (CONTACT_ROWS * 32) as u32, &mut [arg(words), arg(&mut hh), arg(&mut dyhp), arg(&mut dsp), arg(&mut dqp), arg(&mut dvp)])?;
            let (mut hh, mut dqp, mut dvp) = (h as u32, dq.device_ptr(), dv.device_ptr());
            self.launch("field_spread", (regions as u32).clamp(1, 65_535), THREADS, &mut [arg(words), arg(&mut hh), arg(&mut dqp), arg(&mut dvp)])?;
        }
        self.head.set(None);
        let (mut qs, mut dqp) = (tick.qscale.device_ptr(), dq.device_ptr());
        self.launch("field_unit_back", Self::warps((heads * sites) as u64), THREADS, &mut [arg(words), arg(&mut qs), arg(&mut dqp)])?;
        // The probe's return through its own power, alike (§16.19).
        let (mut ps, mut dpp) = (tick.pscale.device_ptr(), dp.device_ptr());
        self.launch("field_unit_back_probe", Self::warps((heads * sites) as u64), THREADS, &mut [arg(words), arg(&mut ps), arg(&mut dpp)])?;
        for chart in [&dq, &dv, &dp] {
            let mut cp = chart.device_ptr();
            self.launch("field_unframe", Self::cells((sites * m) as u64), THREADS, &mut [arg(words), arg(&mut cp)])?;
        }
        if paced > 0 {
            // The frames' return to the clocks (§16): the unframed word and value of the tick, its probe read again.
            self.affine("field_affine_x32", words, words.probe, words.probe_bias, words.rprobe, m2, dw, tick.read.device_ptr(), dw, pr_back.device_ptr(), m2, 0, false)?;
            let mut prb = pr_back.device_ptr();
            self.launch("field_moment_add_probe", Self::cells((sites * m2) as u64), THREADS, &mut [arg(words), arg(&mut prb)])?;
            let (mut dqp, mut dvp, mut dpp, mut qkvp, mut prp) = (dq.device_ptr(), dv.device_ptr(), dp.device_ptr(), tick.qkv.device_ptr(), pr_back.device_ptr());
            self.launch("field_pace_frame_back", Self::cells((paced * sites) as u64), THREADS, &mut [arg(words), arg(&mut dqp), arg(&mut dvp), arg(&mut dpp), arg(&mut qkvp), arg(&mut prp)])?;
        }
        // The values' and the probes' covectors, summed over the ticks, for the moments (§15.1, §16.20).
        for chart in [&dv, &dp] {
            let (mut cp, mut dmp) = (chart.device_ptr(), dm);
            self.launch("field_moment_accumulate", Self::cells((sites * m2) as u64), THREADS, &mut [arg(words), arg(&mut cp), arg(&mut dmp)])?;
        }
        card.zero_octets(&dr, 0, 8 * sites * dw).map_err(device)?;
        for (weight, bias, chart) in [(words.q, words.q_bias, &dq), (words.v, words.v_bias, &dv), (words.probe, words.probe_bias, &dp)] {
            self.outer(words, g, weight, m2, dw, chart.device_ptr(), m2, tick.read.device_ptr(), dw, false, false)?;
            self.outer(words, g, bias, m2, 0, chart.device_ptr(), m2, 0, 0, false, false)?;
            self.transposed(words, weight, m2, dw, chart.device_ptr(), m2, dr.device_ptr(), true, false)?;
        }
        self.ratio_adjoint(words, tick.read.device_ptr(), tick.scale.device_ptr(), dr.device_ptr(), dmid.device_ptr(), dx.device_ptr(), false)?;
        Ok(())
    }

    /// The reverse's per-site and per-pair buffers of one level, the words pointed at those the kernels read.
    fn back_buffers(&self, field: &Field, words: &mut Words, sites: usize, pairs: usize, early_clocks: Option<(Pooled<'c, i128>, Pooled<'c, i128>)>) -> Result<Back<'c>> {
        let d = field.declaration;
        let (dw, m, n, f, heads) = (d.width, d.complex(), d.modes, d.contacts, d.heads);
        let (m2, span) = (2 * m, 2 * n);
        let alloc64 = |len: usize| self.timed(Kind::Alloc, || self.take::<i64>(len.max(1))).map_err(device);
        let dx = alloc64(sites * dw)?;
        let dr = alloc64(sites * dw)?;
        let dc = alloc64(sites * f)?;
        let da = alloc64(sites * f)?;
        let db = alloc64(sites * f)?;
        let dg = alloc64(if d.carry > 0 { sites * 2 * d.carry } else { 1 })?;
        // [theory, November 12; the triad record §4] The triads' covectors, `δc^T` `[t][2J]` and `δabg` `[t][6J]`, none without triads.
        let triad = |rows: usize| if d.triads > 0 { alloc64(sites * rows * d.triads).map(Some) } else { Ok(None) };
        let (dct, dabg) = (triad(2)?, triad(6)?);
        let ra = alloc64(sites * dw)?;
        let rb = alloc64(sites * dw)?;
        let dmid = alloc64(sites * dw)?;
        let dy = alloc64(sites * m2)?;
        let dyh = alloc64(heads * sites * span)?;
        let dq = alloc64(sites * m2)?;
        let dv = alloc64(sites * m2)?;
        // The probe role, its own chart's covector (§16.19).
        let dp = alloc64(sites * m2)?;
        words.dp = dp.device_ptr();
        // The contact's covector a pair, `|δs| < 2^dsbits` with `dsbits ≤ 63` (refused past it).
        let ds = self.timed(Kind::Alloc, || self.take::<i64>(pairs.max(1))).map_err(device)?;
        // The pair covectors `⟨δỹ_i, D ṽ_j⟩` the rows compute once for both passes, on 128 bits.
        let dpb = self.timed(Kind::Alloc, || self.take::<i128>(pairs.max(1))).map_err(device)?;
        words.dpb = dpb.device_ptr();
        // The crowds' difference arrays over the places `[site + region][span]`, for the values and for
        // the word (§14.10).
        let regions = words.r as usize;
        let rows = sites + regions;
        let cv = self.timed(Kind::Alloc, || self.take_zeroed::<i128>((rows * span).max(1))).map_err(device)?;
        let cw = self.timed(Kind::Alloc, || self.take_zeroed::<i128>((rows * span).max(1))).map_err(device)?;
        words.cv = cv.device_ptr();
        words.cw = cw.device_ptr();
        // The values' covector at the moment modes, summed over the ticks (§15.1).
        let dm = self.timed(Kind::Alloc, || self.take_zeroed::<i128>((sites * m2).max(1))).map_err(device)?;
        // The clocks' covectors `[p][t]` (§16), the crowds' contact covectors the skins' return reads, and the probe
        // chart's unframed read a tick (the frames' return turns it).
        let paced = d.paced_heads();
        // [realization; G144] Where the opening was compared, the base clock's two covectors were taken zeroed at the end of its forward and hold its
        // return; they are the pass's own.
        let (gtau, gsig) = match early_clocks {
            Some(clocks) => clocks,
            None => (self.timed(Kind::Alloc, || self.take_zeroed::<i128>((paced * sites).max(1))).map_err(device)?, self.timed(Kind::Alloc, || self.take_zeroed::<i128>((paced * sites).max(1))).map_err(device)?),
        };
        let cds = self.timed(Kind::Alloc, || self.take_zeroed::<i64>((heads * sites * words.slots as usize).max(1))).map_err(device)?;
        let pr_back = alloc64(sites * m2)?;
        words.gtau = gtau.device_ptr();
        words.gsig = gsig.device_ptr();
        words.cds = cds.device_ptr();
        Ok(Back { dx, dr, dc, da, db, dg, dct, dabg, ra, rb, dmid, dy, dyh, dq, dv, dp, ds, dpb, cv, cw, dm, gtau, gsig, cds, pr_back })
    }

    #[allow(clippy::too_many_arguments)]
    fn reverse(&self, field: &Field, words: &mut Words, ticks: &[Tick<'c>], (clocks, base_clock): (&[Option<CardClock<'c>>], [u64; 7]), g: &CardBuffer<'c, i128>, fread: &CardBuffer<'c, i32>, fscale: &CardBuffer<'c, i128>, lift: &CardBuffer<'c, i64>, masses: &CardBuffer<'c, u64>, totals: &CardBuffer<'c, i128>, classes: &[u32], unresolved: &[u8], site_pos: &[u32], mix_off: &[u32], mix_class: &[u32], mix_share: &[u32], site_weight: &[(u64, u64)], ported: &(Vec<u32>, Vec<i64>), sites: usize, pairs: usize, mut tower: Option<(&mut TowerRun<'c>, &TowerBatch<'c>)>, early_clocks: Option<(Pooled<'c, i128>, Pooled<'c, i128>)>) -> Result<()> {
        let card = self.card;
        let d = field.declaration;
        let (dw, m, n, f, a, heads) = (d.width, d.complex(), d.modes, d.contacts, d.alphabet, d.heads);
        let (m2, span) = (2 * m, 2 * n);
        let alloc64 = |len: usize| self.timed(Kind::Alloc, || self.take::<i64>(len.max(1))).map_err(device);
        let dz = alloc64(sites * a)?;
        let back = self.back_buffers(field, words, sites, pairs, early_clocks)?;
        let Back { dx, dr, dc, da, db, ra, rb, dmid, dy, dyh, dq, dv, dp, ds, cv, cw, dm, gtau, gsig, cds, pr_back, .. } = &back;
        let regions = words.r as usize;
        let rows = sites + regions;
        let paced = d.paced_heads();
        // The face.
        let (mut mp, mut tp, mut dzp) = (masses.device_ptr(), totals.device_ptr(), dz.device_ptr());
        self.launch("field_face_covector", Self::cells((sites * a) as u64), THREADS, &mut [arg(words), arg(&mut mp), arg(&mut tp), arg(&mut dzp)])?;
        // The covector weighed as each region's state in the joint code (§16.23, the host's `returned_with`).
        if site_weight.iter().any(|&(m, k)| m != k) {
            let (wm, wk): (Vec<u64>, Vec<u64>) = site_weight.iter().copied().unzip();
            let wm_c = self.timed(Kind::Copy, || self.take_up(&wm)).map_err(device)?;
            let wk_c = self.timed(Kind::Copy, || self.take_up(&wk)).map_err(device)?;
            let (mut wmp, mut wkp) = (wm_c.device_ptr(), wk_c.device_ptr());
            self.launch("field_face_weigh", Self::cells((sites * a) as u64), THREADS, &mut [arg(words), arg(&mut wmp), arg(&mut wkp), arg(&mut dzp)])?;
        }
        // A port's places take their coupling's covector (§16.24), read on the host.
        if !ported.0.is_empty() {
            let at_c = self.timed(Kind::Copy, || self.take_up(&ported.0)).map_err(device)?;
            let rows_c = self.timed(Kind::Copy, || self.take_up(&ported.1)).map_err(device)?;
            let (mut atp, mut rp, mut count) = (at_c.device_ptr(), rows_c.device_ptr(), ported.0.len() as u64);
            self.launch("field_face_set", Self::cells(count * a as u64), THREADS, &mut [arg(words), arg(&mut atp), arg(&mut rp), arg(&mut count), arg(&mut dzp)])?;
        }
        self.outer(words, g, words.read_bias, a, 0, dz.device_ptr(), a, 0, 0, false, true)?;
        // Through the encoding (§16.26, the host's `returned_with`): `δE(a)_i += Σ_t rel(δz_a y_i, 16)`, `δy = rel(Σ_a δz_a E(a), 16)`,
        // then the lift's own return.
        let dyl = alloc64(sites * dw)?;
        {
            let (mut gp, mut enc, mut dzp, mut yp, mut dyp) = (g.device_ptr(), words.enc, dz.device_ptr(), lift.device_ptr(), dyl.device_ptr());
            let tiles = (sites as u64).div_ceil(64);
            self.launch("field_tied_back_e", Self::cells(a as u64 * dw as u64 * tiles), THREADS, &mut [arg(words), arg(&mut gp), arg(&mut enc), arg(&mut dzp), arg(&mut yp)])?;
            let mut enc = words.enc;
            self.launch("field_tied_back_y", Self::cells((sites * dw) as u64), THREADS, &mut [arg(words), arg(&mut enc), arg(&mut dzp), arg(&mut dyp)])?;
        }
        let lift_bias = field.layout().lift_bias as u64;
        self.outer(words, g, lift_bias, dw, 0, dyl.device_ptr(), dw, 0, 0, false, true)?;
        self.outer(words, g, words.read, dw, dw, dyl.device_ptr(), dw, fread.device_ptr(), dw, false, true)?;
        self.transposed(words, words.read, dw, dw, dyl.device_ptr(), dw, dr.device_ptr(), false, true)?;
        self.ratio_adjoint(words, fread.device_ptr(), fscale.device_ptr(), dr.device_ptr(), 0, dx.device_ptr(), true)?;
        // A tower's packets' reverse buffers, beside the fine field's.
        let cback = match (tower.as_mut(), field.scale.as_deref()) {
            (Some((tr, tb)), Some(s)) => Some(self.back_buffers(&s.coarse, &mut tr.cwords, tb.st.sites, tb.st.pairs, None)?),
            _ => None,
        };
        // [§16.44] One set of the clocks' and moments' covectors a clock: the pass's (the first tick and the opening), and
        // each tick's own where its blanks ran at the faces the tick before gave them.
        let own: Vec<Option<[Pooled<'c, i128>; 3]>> = clocks
            .iter()
            .map(|c| {
                c.as_ref()
                    .map(|_| -> Result<[Pooled<'c, i128>; 3]> {
                        let zeroed = |len: usize| self.timed(Kind::Alloc, || self.take_zeroed::<i128>(len.max(1))).map_err(device);
                        Ok([zeroed(sites * m2)?, zeroed(paced * sites)?, zeroed(paced * sites)?])
                    })
                    .transpose()
            })
            .collect::<Result<_>>()?;
        let covectors = |at: usize| -> [u64; 3] { own.get(at).and_then(Option::as_ref).map_or([dm.device_ptr(), gtau.device_ptr(), gsig.device_ptr()], |b| [b[0].device_ptr(), b[1].device_ptr(), b[2].device_ptr()]) };
        for (at, tick) in ticks.iter().enumerate().rev() {
            set_clock(words, clocks.get(at).and_then(Option::as_ref), base_clock);
            let [dmp, gtp, gsp] = covectors(at);
            (words.gtau, words.gsig) = (gtp, gsp);
            self.tick_back(field, words, tick, at, g, &back, dmp, sites, true)?;
            if let (Some((tr, tb)), Some(cb)) = (tower.as_mut(), cback.as_ref()) {
                if at == tr.split {
                    self.tower_back(field, words, tr, tb, &back, cb)?;
                }
            }
            // [§16.44] A tick's own clock was read off the state this tick began from: its moments and rates return now,
            // and each blank's clock returns through its face into that state's covector (the host's `clock_return`).
            if let Some(clock) = clocks.get(at).and_then(Option::as_ref) {
                self.moments_return_at(field, words, g, dmp, regions, sites)?;
                if paced > 0 {
                    // [realization; theory, November 13, P58 item 2] Unzeroed: `field_pace_kappa_back` writes every `(paced head, site)` word, each
                    // region's sites from its last to its first, before `field_pace_c_back` and `field_blank_dz` read them.
                    let dkappa = self.timed(Kind::Alloc, || self.take::<i128>((paced * sites).max(1))).map_err(device)?;
                    let (mut dkp, mut gp) = (dkappa.device_ptr(), g.device_ptr());
                    self.launch("field_pace_kappa_back", Self::cells((paced * regions) as u64), THREADS, &mut [arg(words), arg(&mut dkp)])?;
                    self.launch("field_pace_c_back", Self::cells((paced * sites) as u64), THREADS, &mut [arg(words), arg(&mut dkp), arg(&mut gp)])?;
                    self.blank_back(field, words, clock, &dkappa, g, dx, sites)?;
                }
            }
        }
        set_clock(words, None, base_clock);
        (words.gtau, words.gsig) = (gtau.device_ptr(), gsig.device_ptr());
        // The moment's chart into the face (§16.22, the host's `returned_with`): `δC += Σ_t δx⁰_t s_tᵀ`, `δb += Σ_t δx⁰_t`,
        // and the moments' covector `δs_t += Cᵀ δx⁰_t` (formed in `dq`, free past the ticks) joined to the values' and probes'.
        let (mface, mface_bias, _) = moment_face(field);
        self.outer(words, g, mface_bias, dw, 0, dx.device_ptr(), dw, 0, 0, false, false)?;
        self.outer(words, g, mface, dw, m2, dx.device_ptr(), dw, words.moment, m2, true, false)?;
        self.transposed(words, mface, dw, m2, dx.device_ptr(), dw, dq.device_ptr(), false, false)?;
        let (mut cp, mut dmp) = (dq.device_ptr(), dm.device_ptr());
        self.launch("field_moment_accumulate", Self::cells((sites * m2) as u64), THREADS, &mut [arg(words), arg(&mut cp), arg(&mut dmp)])?;
        // The moments' return (§15.1): each moment mode's value covector, summed over the ticks that read one clock,
        // through the strands to the families on that clock (the host's `moments_return`); then the clocks return to
        // their paces (§16, §16.16): `δκ` by suffix sums, then `δc[u] += Σ_(u_t = u) δκ_t` on the class sheet, a blank's by
        // the shares of the face its clock read (§16.44); the opening takes nothing.
        {
            let [dmp, gtp, gsp] = [dm.device_ptr(), gtau.device_ptr(), gsig.device_ptr()];
            set_clock(words, None, base_clock);
            (words.gtau, words.gsig) = (gtp, gsp);
            self.moments_return_at(field, words, g, dmp, regions, sites)?;
            if paced > 0 {
                // [P58 item 2] Unzeroed, as each tick's: `field_pace_kappa_back` writes every word before `field_pace_c_back` reads it.
                let dkappa = self.timed(Kind::Alloc, || self.take::<i128>((paced * sites).max(1))).map_err(device)?;
                let (mut dkp, mut gp) = (dkappa.device_ptr(), g.device_ptr());
                self.launch("field_pace_kappa_back", Self::cells((paced * regions) as u64), THREADS, &mut [arg(words), arg(&mut dkp)])?;
                self.launch("field_pace_c_back", Self::cells((paced * sites) as u64), THREADS, &mut [arg(words), arg(&mut dkp), arg(&mut gp)])?;
            }
        }
        set_clock(words, None, base_clock);
        (words.gtau, words.gsig) = (gtau.device_ptr(), gsig.device_ptr());
        // The opening: each site's row of the encoding and its strand neighbours' rows of theirs (a
        // carried site's mixture by its shares), the entries partitioned by row once for each encoding
        // (a neighbour only within the site's region: the next site is the region's own when its place
        // is not the first). A plain row is a share of `2^16`.
        let terms = |s: usize, t: u32| -> Vec<(usize, u32, u32)> {
            let (from, to) = (mix_off[s] as usize, mix_off[s + 1] as usize);
            if from == to {
                return vec![(if unresolved[s] != 0 { a } else { classes[s] as usize }, t, 1 << STATE_BITS)];
            }
            (from..to).map(|k| (mix_class[k] as usize, t, mix_share[k])).collect()
        };
        let own: Vec<(usize, u32, u32)> = (0..sites).flat_map(|t| terms(t, t as u32)).collect();
        let before: Vec<(usize, u32, u32)> = (0..sites).filter(|&t| site_pos[t] > 0).flat_map(|t| terms(t - 1, t as u32)).collect();
        let after: Vec<(usize, u32, u32)> = (0..sites).filter(|&t| t + 1 < sites && site_pos[t + 1] > 0).flat_map(|t| terms(t + 1, t as u32)).collect();
        for (base, rows) in [(words.enc, own), (words.enc_before, before), (words.enc_after, after)] {
            let (rows_sites, rows_shares, segments) = encoding_partition(&rows, a + 1);
            let count = (segments.len() / 3) as u32;
            if count == 0 {
                continue;
            }
            let rows_sites_c = self.timed(Kind::Copy, || self.take_up(&rows_sites)).map_err(device)?;
            let rows_shares_c = self.timed(Kind::Copy, || self.take_up(&rows_shares)).map_err(device)?;
            let segments_c = self.timed(Kind::Copy, || self.take_up(&segments)).map_err(device)?;
            let (mut gp, mut dxp, mut rsp, mut rwp, mut sgp, mut count, mut base) = (g.device_ptr(), dx.device_ptr(), rows_sites_c.device_ptr(), rows_shares_c.device_ptr(), segments_c.device_ptr(), count, base);
            self.launch("field_encoding", Self::cells(count as u64 * dw as u64), THREADS, &mut [arg(words), arg(&mut gp), arg(&mut dxp), arg(&mut rsp), arg(&mut rwp), arg(&mut sgp), arg(&mut count), arg(&mut base)])?;
        }
        // [definition; agent-inferred, November 14, the ring record §4] **The mark's return** (the host's `Field::opening_return` at a marked site):
        // on a field's second read each silent site's rows above gave its open row `dx`; its mark adds `−release(α_b dx, 24)` there, each class's
        // `release(w_c release(α_b dx, 24), 16)` and the strength's `Σ_i dx_i Δ_i`, in every encoding its row enters (`field_mark_back`, then
        // `field_mark_rows` over the kept `release(α_b dx, 24)`).
        if words.mark_share != 0 {
            let marked: Vec<u32> = (0..sites).filter(|&s| unresolved[s] != 0 && mix_off[s] == mix_off[s + 1]).map(|s| s as u32).collect();
            if !marked.is_empty() {
                let count = marked.len();
                let marked_c = self.timed(Kind::Copy, || self.take_up(&marked)).map_err(device)?;
                // Unzeroed: `field_mark_back` writes every word `[b][k][i]` before `field_mark_rows` reads it.
                let adx = alloc64(3 * count * dw)?;
                let (mut gp, mut dxp, mut mp, mut cnt, mut ap) = (g.device_ptr(), dx.device_ptr(), marked_c.device_ptr(), count as u32, adx.device_ptr());
                self.launch("field_mark_back", Self::cells((count * dw) as u64), THREADS, &mut [arg(words), arg(&mut gp), arg(&mut dxp), arg(&mut mp), arg(&mut cnt), arg(&mut ap)])?;
                self.launch("field_mark_rows", Self::cells((3 * (a + 1) * dw * count.div_ceil(64)) as u64), THREADS, &mut [arg(words), arg(&mut gp), arg(&mut mp), arg(&mut cnt), arg(&mut ap)])?;
            }
        }
        Ok(())
    }

    /// [definition; agent-inferred, November 1] **The moments' return** (the host's `Field::moments_return`,
    /// the released law of §15.1): every moment mode's covector `dm` at its value (fit to 64 bits), admitted by
    /// the return's certificate, the prefix of the covector turned and released once a term, the return at
    /// every site, and the strands' encodings' rows (or a carried site's classes by their shares) added into
    /// `g`; all modes in the same launches.
    fn moments_return(&self, field: &Field, words: &Words, g: &CardBuffer<'c, i128>, dm: &CardBuffer<'c, i128>, regions: usize, sites: usize) -> Result<()> {
        self.moments_return_at(field, words, g, dm.device_ptr(), regions, sites)
    }

    /// [`CardField::moments_return`] of the moments' covector at `dm` (§16.44: one a clock).
    fn moments_return_at(&self, field: &Field, words: &Words, g: &CardBuffer<'c, i128>, dm: u64, regions: usize, sites: usize) -> Result<()> {
        let d = field.declaration;
        let tm = d.moment_modes();
        if tm == 0 {
            return Ok(());
        }
        let (l, card) = (field.layout(), self.card);
        let (strand, prefix) = ((2 * sites) as u64, (2 * (sites + regions)) as u64);
        let ds = self.timed(Kind::Alloc, || self.take::<i64>((tm * 2 * sites).max(1))).map_err(device)?;
        let q = self.timed(Kind::Alloc, || self.take::<i128>((tm * 2 * (sites + regions)).max(1))).map_err(device)?;
        let (d_before, d_after) = (self.timed(Kind::Alloc, || self.take::<i128>((tm * 2 * sites).max(1))).map_err(device)?, self.timed(Kind::Alloc, || self.take::<i128>((tm * 2 * sites).max(1))).map_err(device)?);
        let ok = self.timed(Kind::Alloc, || self.take_up(&vec![0u8; (tm * regions).max(1)])).map_err(device)?;
        let (ws, cmap) = self.moment_modes(field, words, regions, sites, &ok)?;
        let (mut wsp, mut cmp, mut dmp) = (ws.device_ptr(), cmap.device_ptr(), dm);
        let (mut dsp, mut qp, mut dbp, mut dap, mut gp, mut none) = (ds.device_ptr(), q.device_ptr(), d_before.device_ptr(), d_after.device_ptr(), g.device_ptr(), 0u64);
        let (mut w2, mut base_b, mut base_a, mut tm32) = (*words, l.moment_before as u64, l.moment_after as u64, tm as u32);
        let (mut one32, mut stride, mut pre_stride) = (1u32, strand, prefix);
        let grid = |x: usize| Dim3 { x: x.max(1) as u32, y: tm as u32, z: 1 };
        self.launch("field_moment_ds_all", Self::cells((sites * tm) as u64), THREADS, &mut [arg(&mut w2), arg(&mut dmp), arg(&mut cmp), arg(&mut tm32), arg(&mut dsp)])?;
        // The paced law where a mode's pace is not plain (§16): the admission with the faces' bound, the released
        // prefix of the turned covector, each receiver's far octave at its own skin (the skinned prefixes), the return.
        let mut fw = *words;
        self.launch_grid("field_moment_admit_paced_all", grid(regions), MOMENT_BLOCK, 3 * MOMENT_BLOCK * 16, &mut [arg(&mut wsp), arg(&mut cmp), arg(&mut fw), arg(&mut dsp), arg(&mut none), arg(&mut stride), arg(&mut one32)])?;
        self.launch_grid("field_moment_prefix_paced_all", grid(regions), MOMENT_BLOCK, MOMENT_BLOCK * 32, &mut [arg(&mut wsp), arg(&mut cmp), arg(&mut fw), arg(&mut dsp), arg(&mut qp), arg(&mut stride), arg(&mut pre_stride), arg(&mut one32)])?;
        let levels = (2u32..).take_while(|&lv| (1usize << lv) < d.reach).count() as u32;
        let sk_stride = (2 * levels as usize * 2 * (sites + regions)) as u64;
        let sk = self.timed(Kind::Alloc, || self.take::<i128>((tm * sk_stride as usize).max(1))).map_err(device)?;
        let (mut skp, mut sk_stride_a, mut levels_a) = (sk.device_ptr(), sk_stride, levels);
        if levels > 0 {
            self.launch("field_moment_skinned_all", Self::cells((tm * regions * 2 * levels as usize) as u64), THREADS, &mut [arg(&mut wsp), arg(&mut cmp), arg(&mut fw), arg(&mut dsp), arg(&mut skp), arg(&mut stride), arg(&mut sk_stride_a), arg(&mut levels_a), arg(&mut tm32)])?;
        }
        self.launch_grid("field_moment_return_paced_all", Dim3 { x: Self::cells(sites as u64), y: tm as u32, z: 1 }, THREADS, 0, &mut [arg(&mut wsp), arg(&mut cmp), arg(&mut fw), arg(&mut dsp), arg(&mut qp), arg(&mut skp), arg(&mut dbp), arg(&mut dap), arg(&mut stride), arg(&mut pre_stride), arg(&mut sk_stride_a)])?;
        self.launch("field_moment_strand_return_all", Self::cells((sites * tm) as u64), THREADS, &mut [arg(&mut w2), arg(&mut base_b), arg(&mut base_a), arg(&mut tm32), arg(&mut dbp), arg(&mut dap), arg(&mut gp)])?;
        // The moments' clock covector (§16, `moment::pace_return`): the strands and their paced prefixes read again.
        let (before, after) = (self.timed(Kind::Alloc, || self.take::<i64>((tm * 2 * sites).max(1))).map_err(device)?, self.timed(Kind::Alloc, || self.take::<i64>((tm * 2 * sites).max(1))).map_err(device)?);
        let (up, down) = (self.timed(Kind::Alloc, || self.take::<i128>((tm * 2 * (sites + regions)).max(1))).map_err(device)?, self.timed(Kind::Alloc, || self.take::<i128>((tm * 2 * (sites + regions)).max(1))).map_err(device)?);
        let (mut bp, mut ap, mut upp, mut dnp, mut zero32) = (before.device_ptr(), after.device_ptr(), up.device_ptr(), down.device_ptr(), 0u32);
        self.launch("field_moment_strands_all", Self::cells((sites * tm) as u64), THREADS, &mut [arg(&mut w2), arg(&mut base_b), arg(&mut base_a), arg(&mut tm32), arg(&mut bp), arg(&mut ap)])?;
        self.launch_grid("field_moment_prefix_paced_all", grid(regions), MOMENT_BLOCK, MOMENT_BLOCK * 32, &mut [arg(&mut wsp), arg(&mut cmp), arg(&mut fw), arg(&mut bp), arg(&mut upp), arg(&mut stride), arg(&mut pre_stride), arg(&mut zero32)])?;
        self.launch_grid("field_moment_prefix_paced_all", grid(regions), MOMENT_BLOCK, MOMENT_BLOCK * 32, &mut [arg(&mut wsp), arg(&mut cmp), arg(&mut fw), arg(&mut ap), arg(&mut dnp), arg(&mut stride), arg(&mut pre_stride), arg(&mut zero32)])?;
        self.launch_grid("field_moment_pace_back_all", Dim3 { x: Self::cells(sites as u64), y: tm as u32, z: 1 }, THREADS, 0, &mut [arg(&mut wsp), arg(&mut cmp), arg(&mut fw), arg(&mut bp), arg(&mut ap), arg(&mut dsp), arg(&mut dbp), arg(&mut dap), arg(&mut upp), arg(&mut dnp), arg(&mut stride), arg(&mut pre_stride)])?;
        Ok(())
    }

    /// [definition; theory, November 12, P50 step 1 (G116 a)] **The clock's skins, formed once** (`field_skin_fill`): after the clock is set, every
    /// support pair's and crowd edge's skin of the paced heads where their pace is not plain, read by the lock, the numerators, the rows, the columns
    /// and the skin's return. The test build first writes `SKIN_UNFILLED` over the store, so a reader of a word no fill formed is refused
    /// (`REFUSED_UNFILLED`); a level with no store (no paced head, the packets' plain clocks) forms none.
    fn skin_fill(&self, field: &Field, words: &mut Words, sites: usize) -> Result<()> {
        let d = field.declaration;
        let paced = d.paced_heads();
        if paced == 0 || words.skin == 0 {
            return Ok(());
        }
        if cfg!(debug_assertions) {
            let n = d.modes;
            let pair_words = paced * words.skin_entries as usize * n;
            let stream = self.card.stream();
            stream.memset_u32_async(words.skin, u32::MAX, pair_words.max(1)).map_err(|e| device(e.into()))?;
        }
        #[cfg(test)]
        if self.unfilled.get() {
            return Ok(());
        }
        let mut pc = paced as u32;
        self.launch("field_skin_fill", Self::rows_grid((paced * sites) as u64, CONTACT_ROWS), (CONTACT_ROWS * 32) as u32, &mut [arg(words), arg(&mut pc)])
    }

    /// [definition; theory, November 12, P50 step 2 (G116 b)] **The clock's phases and skins, formed once** (`field_clock_fill`): after a clock is set,
    /// every moment mode's near phases and skins at every site of a paced head, and its far skins into the crowd edges' store, read by the moments, the
    /// skinned prefixes, the moments' return and the clocks' covector, and by the contact's crowds. The test build first writes `PHASE_UNFILLED` and
    /// `SKIN_UNFILLED` over the stores, so a reader of a word no fill formed is refused (`REFUSED_UNFILLED`).
    fn clock_fill(&self, field: &Field, words: &Words, sites: usize) -> Result<()> {
        let d = field.declaration;
        let tm = words.tm as usize;
        if tm == 0 || words.mphase == 0 || words.cskin == 0 {
            return Ok(());
        }
        if cfg!(debug_assertions) {
            let stream = self.card.stream();
            let near = tm * sites * CLOCK_NEAR;
            stream.memset_u32_async(words.mphase, 0x8000_0000, 2 * near).map_err(|e| device(e.into()))?;
            stream.memset_u32_async(words.mskin, u32::MAX, near).map_err(|e| device(e.into()))?;
            stream.memset_u32_async(words.cskin, u32::MAX, (d.paced_heads() * sites * words.slots as usize * d.modes).max(1)).map_err(|e| device(e.into()))?;
        }
        #[cfg(test)]
        if self.unfilled.get() {
            return Ok(());
        }
        let mut fw = *words;
        self.launch_grid("field_clock_fill", Dim3 { x: Self::cells(sites as u64), y: tm as u32, z: 1 }, THREADS, 0, &mut [arg(&mut fw)])
    }

    /// [measurement; theory, November 12, P50 step 3] The turn's series against the wide one on the card (`field_series_check`): for each argument
    /// `b`, the narrow series' face and `exp_series_dev(0, b)`'s, `[narrow re, narrow im, wide re, wide im]`.
    pub fn series_check(&self, bs: &[i64]) -> Result<Vec<i64>> {
        let card = self.card;
        let up = self.timed(Kind::Copy, || self.take_up(bs)).map_err(device)?;
        let out = self.timed(Kind::Alloc, || self.take::<i64>((4 * bs.len()).max(1))).map_err(device)?;
        let (mut bp, mut count, mut op) = (up.device_ptr(), bs.len() as u64, out.device_ptr());
        self.launch("field_series_check", Self::cells(bs.len() as u64), THREADS, &mut [arg(&mut bp), arg(&mut count), arg(&mut op)])?;
        card.fetch_range(&out, 0, 4 * bs.len()).map_err(device)
    }

    /// [measurement; theory, November 12, P54 item 1] The ruler build's histogram slot of one array at one clock.
    #[cfg(feature = "ruler-bits")]
    fn bits_slot(&self, array: usize, tick: usize) -> Result<u64> {
        let mut b = self.bits.borrow_mut();
        if b.is_none() {
            *b = Some(self.card.zeroed::<u64>(BITS_NAMES.len() * BITS_TICKS * BITS_BINS).map_err(device)?);
        }
        Ok(b.as_ref().map_or(0, |b| b.device_ptr()) + (((array * BITS_TICKS + tick.min(BITS_TICKS - 1)) * BITS_BINS) * 8) as u64)
    }

    #[cfg(feature = "ruler-bits")]
    #[allow(clippy::too_many_arguments)]
    fn bits_pairs(&self, words: &mut Words, h: usize, kind: u32, mode: u32, arr: u64, array: usize, tick: usize, sites: usize) -> Result<()> {
        let mut slot = self.bits_slot(array, tick)?;
        let (mut hh, mut kd, mut md, mut ap) = (h as u32, kind, mode, arr);
        self.launch("field_yard_bits_pairs", Self::rows_grid(sites as u64, CONTACT_ROWS), (CONTACT_ROWS * 32) as u32, &mut [arg(words), arg(&mut hh), arg(&mut kd), arg(&mut md), arg(&mut ap), arg(&mut slot)])
    }

    #[cfg(feature = "ruler-bits")]
    fn bits_words(&self, arr: u64, kind: u32, count: usize, array: usize, tick: usize) -> Result<()> {
        let mut slot = self.bits_slot(array, tick)?;
        let (mut ap, mut kd, mut n) = (arr, kind, count as u64);
        self.launch("field_yard_bits_words", Self::cells(count as u64), THREADS, &mut [arg(&mut ap), arg(&mut kd), arg(&mut n), arg(&mut slot)])
    }

    /// [measurement; theory, November 12, P54 item 1] The ruler build's histograms: `[array][tick][bits]`, the arrays in `BITS_NAMES`' order.
    #[cfg(feature = "ruler-bits")]
    pub fn bits_histograms(&self) -> Option<Vec<u64>> {
        self.bits.borrow().as_ref().and_then(|b| self.card.fetch(b).ok())
    }

    /// The batch's refusals, read off the card.
    fn status(&self, status: &CardBuffer<'c, u32>) -> Result<()> {
        let bits = self.timed(Kind::Copy, || self.card.fetch(status)).map_err(device)?[0];
        if bits == 0 {
            return Ok(());
        }
        let names = [(1, "a sum outgrew its 128-bit carrier"), (2, "a released value outgrew its 64-bit carrier"), (4, "a released value outgrew its 32-bit carrier"), (8, "a current's covector outgrew its 128-bit carrier"), (16, "a moment's strand outruns its resident ring or skin"), (32, "a contact's key return outgrew its carrier"), (64, "a temperature past its carrier (2^(−23) to 2^7)"), (128, "a skin read from the clock's store where its fill formed none")];
        let named: Vec<&str> = names.iter().filter(|(b, _)| bits & b != 0).map(|(_, n)| *n).collect();
        Err(TowerError::Realization(format!("the card refused the field: {}", named.join("; "))))
    }
}

/// [agent-inferred, November 1] **Everything a region of `sites` sites allocates in a batch**
/// ([`CardField::batch`], `tick`, `reverse`): each kept tick's carriers (the chart's read and scale,
/// the word and the value and their framed copies, the word's powers, the classes and members, the
/// masses, the current, the pair contact's read, scale and drives), its class offsets and its weights
/// `H·S²` (their dense reservation), the opening's carried mixtures at most one share a class, the
/// face's carriers, and on a return the reverse's per-site covectors and the contact's return `δs`
/// (`S²` on 128 bits). Measured November 1: sized by the weights and the contact's return alone, a
/// batched release's per-site carriers took the board to 13,372 MiB; sized by its carriers too, the
/// same release peaked at 11,256 MiB.
pub fn region_octets(d: &FieldDeclaration, returning: bool, sites: usize, definite: usize) -> u64 {
    read_octets(d, returning, false, sites) + skin_octets(d, sites, definite).0
}

/// [`region_octets`] for a read of `logits` too: a logits read keeps every tick and its shares (the echo's
/// round trips of consecutive ticks, §15.3), as a return does.
pub fn read_octets(d: &FieldDeclaration, returning: bool, echo: bool, sites: usize) -> u64 {
    let (dw, m2, f, a, h, span) = (d.width as u64, 2 * d.complex() as u64, d.contacts as u64, d.alphabet as u64, d.heads as u64, 2 * d.modes as u64);
    let kept = returning || echo;
    let ticks_kept = if kept { d.ticks as u64 } else { 1 };
    // Per site a kept tick adds the row's least bit, its class and its place in the lists, its prefix sums'
    // row (words and values on 128 bits, a count) and its crowd shares (`crowd_slots` words a head).
    let slots = crowd_slots(d.reach) as u64;
    // A receiver's probes: their number, their classes, and its place among the probers of each (`2^b − 1`).
    let probe_site = 4 * h * (1 + 2 * (1u64 << d.class_trits()));
    // The chart's and the pair contact's scales are one a lane (§16.40).
    let lanes = d.lanes as u64;
    // [theory, November 11 17:25] The carry circles' charts' reads, gate and scan operand, `[t][2C]` each.
    let carry_site = 48 * d.carry as u64;
    // [theory, November 12; the triad record §4] The triads' chart read `[t][6J]` and their products `p` and `c^T` `[t][2J]` each, kept a tick.
    let triad_site = 8 * 10 * d.triads as u64;
    let tick_site = triad_site + carry_site + 4 * dw + 16 * lanes + 8 * 2 * m2 + 2 * 8 * h * span + 16 * h + 8 * h + 4 * h + 4 * h + 8 * m2 + 4 * dw + 16 * lanes + 3 * 8 * f + (2 * 16 * span + 8) * h + 8 * h * slots + probe_site + 4 * h * span + 8 * h * span + 4 * h * span + 16 * h;
    let tick_fixed = tick_fixed_octets(d);
    // The face: its read, scale, logits, masses and total, and (§16.26) the lift and its covector.
    let face_site = 8 * dw + 4 * dw + 16 * lanes + 8 * a + 8 * a + 16 + 16 + 2 * 8 * dw;
    // A site's carried mixture, definite bit, echo (a flag, `B` and logits) and the round trips.
    let mixture_site = 5 + 2 * 4 * a + 9 + 8 * a + 16;
    // The moments: the pass's values `[t][2M]`, and a mode's strands, moments, prefix sums and admission
    // (112 octets a site), batched over the modes.
    let tm = d.moment_modes() as u64;
    // [theory, November 11 04:14, step S] The skin's site addresses: three words a (paced head, mode, site) for the pass's clock and each kept tick's own.
    let address_site = 24 * d.paced_heads() as u64 * d.modes as u64 * (ticks_kept + 1);
    let moment_site = if tm > 0 { 8 * m2 + 112 * tm } else { 0 };
    let moment_site = moment_site + address_site;
    // The reverse adds its covectors (the triads' `δc^T` `[t][2J]` and `δabg` `[t][6J]` among them), the values' sum over the ticks and the
    // moments' return, and the crowds' two difference arrays.
    let reverse_site = if returning { 8 * 8 * d.triads as u64 + 16 * d.carry as u64 + 8 * m2 + 8 * a + 5 * 8 * dw + 3 * 8 * f + 8 * m2 + 8 * h * span + 2 * 8 * m2 + 16 * m2 + 2 * 16 * span + 112 * tm } else { 0 };
    // [the ring record §4] A field that reads twice holds its first read's shares `[t][A]` through the second read, and its return the marked
    // sites' list and `release(α_b dx, 24)` in each of the three encodings (`[3][t][D]` at most).
    let mark_site = if d.mark { 4 * a + if returning { 4 + 3 * 8 * dw } else { 0 } } else { 0 };
    let (s, pairs) = (sites as u64, (sites * sites) as u64);
    // The shares are kept for a return and an echo; the reverse holds one head's covector a pair on 64 bits.
    let weights = h * 8 * pairs * if returning { 2 } else { 1 };
    ticks_kept * (weights + s * tick_site + tick_fixed) + s * (face_site + mixture_site + moment_site + reverse_site + mark_site + 8 * m2) + if returning { 24 * pairs } else { 0 }
}

/// A kept tick's octets a region beside its sites': the carrier's width (one word), the class
/// offsets `H (2·3^b + 1)` words (each class's definite members and the rest) and the prefix sums'
/// extra row (a region's `S + 1` rows, §14.10), which the reverse's difference arrays share.
fn tick_fixed_octets(d: &FieldDeclaration) -> u64 {
    4 + 4 * d.heads as u64 * (2 * d.classes() as u64 + 1) + 4 * d.heads as u64 * (d.classes() as u64 + 1) + (2 * 16 * 2 * d.modes as u64 + 8) * d.heads as u64 + 2 * 16 * 2 * d.modes as u64
}

/// An encoding's entries sorted by the row they opened on (`rows` holds each entry's row, site and
/// share, `rows_n` the encoding's rows), and each row's entries cut into segments of at most
/// `OUTER_TILE` (each its row, first and end in the sorted entries): one thread a segment and a column.
fn encoding_partition(rows: &[(usize, u32, u32)], rows_n: usize) -> (Vec<u32>, Vec<u32>, Vec<u32>) {
    let mut rows_off = vec![0u32; rows_n + 1];
    for &(row, _, _) in rows {
        rows_off[row + 1] += 1;
    }
    for row in 0..rows_n {
        rows_off[row + 1] += rows_off[row];
    }
    let mut filled = rows_off.clone();
    let mut rows_sites = vec![0u32; rows.len()];
    let mut rows_shares = vec![0u32; rows.len()];
    for &(row, t, w) in rows {
        rows_sites[filled[row] as usize] = t;
        rows_shares[filled[row] as usize] = w;
        filled[row] += 1;
    }
    let mut segments: Vec<u32> = Vec::new();
    for row in 0..rows_n {
        let (from, to) = (rows_off[row], rows_off[row + 1]);
        let mut at = from;
        while at < to {
            let end = to.min(at + OUTER_TILE as u32);
            segments.extend([row as u32, at, end]);
            at = end;
        }
    }
    (rows_sites, rows_shares, segments)
}

/// The batches of whole regions, in order, each batch's allocations within `budget`; a region whose
/// allocations alone pass the budget is refused.
pub fn batches(lengths: &[usize], octets: &dyn Fn(usize) -> u64, budget: u64) -> Result<Vec<std::ops::Range<usize>>> {
    batches_of(lengths, &lengths.iter().map(|&n| octets(n)).collect::<Vec<_>>(), budget)
}

/// [`batches`] from each region's own need (`needs[i]` for region `i` of `lengths[i]` sites).
pub fn batches_of(lengths: &[usize], needs: &[u64], budget: u64) -> Result<Vec<std::ops::Range<usize>>> {
    let mut out = Vec::new();
    let (mut from, mut taken) = (0usize, 0u64);
    for (i, &n) in lengths.iter().enumerate() {
        let need = needs[i];
        if need > budget {
            return Err(TowerError::Realization(format!("a region of {n} sites needs {need} octets, past the card's batch budget of {budget}")));
        }
        if taken + need > budget {
            out.push(from..i);
            from = i;
            taken = 0;
        }
        taken += need;
    }
    if from < lengths.len() {
        out.push(from..lengths.len());
    }
    Ok(out)
}

impl FieldRealization for CardField<'_> {
    fn read_and_return(&mut self, field: &Field, regions: &[Region]) -> Result<(Vec<Vec<Option<TowerFace>>>, Vec<i128>)> {
        let (faces, _, g, _, _) = self.run(field, regions, true, false, None)?;
        Ok((faces, g))
    }

    /// [realization; theory, November 13, P58 item 3] The faces' masses at their classes and their totals gathered on the card (`narrow`, read
    /// at the batch's end), the whole faces where a region has a port (its coupling reads every class of its places).
    fn read_and_return_at_class(&mut self, field: &Field, regions: &[Region]) -> Result<(Vec<Vec<Option<(u128, u128)>>>, Vec<i128>)> {
        if regions.iter().any(|r| r.port.is_some()) {
            let (faces, g) = self.read_and_return(field, regions)?;
            return Ok((holonics::hnn::tower::field::faces_at_class(&faces, regions), g));
        }
        self.narrow_out.borrow_mut().clear();
        self.narrow.set(true);
        let run = self.run(field, regions, true, false, None);
        self.narrow.set(false);
        let (_, _, g, _, _) = run?;
        let pairs = std::mem::take(&mut *self.narrow_out.borrow_mut());
        if pairs.len() != regions.len() {
            return Err(TowerError::Refused("a narrow read that did not return one row of faces a region"));
        }
        Ok((pairs, g))
    }

    /// [realization; theory, November 13, P60 items 1d and 2] The training path with the opening compared in the card's own forward: its codes at
    /// every compared place gathered beside the faces' words and the covector of the same read and return.
    fn read_and_return_opening(&mut self, field: &Field, regions: &[Region]) -> Result<(Vec<Vec<Option<(u128, u128)>>>, Vec<i128>, Vec<Vec<Option<i64>>>)> {
        self.opening_out.borrow_mut().clear();
        self.opening_wanted.set(field.declaration.opening);
        let read = self.read_and_return_at_class(field, regions);
        self.opening_wanted.set(false);
        let (at_class, g) = read?;
        let codes = std::mem::take(&mut *self.opening_out.borrow_mut());
        if field.declaration.opening && codes.len() != regions.len() {
            return Err(TowerError::Refused("an opening's read that did not return one row of codes a region"));
        }
        Ok((at_class, g, codes))
    }

    fn read_faces(&mut self, field: &Field, regions: &[Region]) -> Result<Vec<Vec<Option<TowerFace>>>> {
        Ok(self.run(field, regions, false, false, None)?.0)
    }

    /// [measurement; theory, November 13, P57 item 2 (G132)] The faces and the open sites' charts by stage, from one forward that keeps every tick.
    fn read_tick_charts(&mut self, field: &Field, regions: &[Region]) -> Result<(Vec<Vec<Option<TowerFace>>>, Vec<Vec<Vec<i32>>>)> {
        *self.tick_charts.borrow_mut() = Some(Vec::new());
        let read = self.run(field, regions, false, true, None);
        let charts = self.tick_charts.borrow_mut().take().unwrap_or_default();
        let faces = read?.0;
        if charts.len() != regions.len() {
            return Err(TowerError::Refused("a read of the charts by stage that did not return one a region"));
        }
        Ok((faces, charts))
    }

    /// [measurement; part P2] The faces and the carry circles' gates from the same pass: every tick's gate and leak reads are summed on the card
    /// over the open sites (`field_carry_gates_read`), so no face and no other read changes.
    fn read_faces_gated(&mut self, field: &Field, regions: &[Region]) -> Result<(Vec<Vec<Option<TowerFace>>>, CarryGates)> {
        let c = field.declaration.carry;
        *self.carry_gates.borrow_mut() = (c > 0).then(|| vec![0u128; 2 * c + 1]);
        let read = self.run(field, regions, false, false, None);
        let sum = self.carry_gates.borrow_mut().take();
        let faces = read?.0;
        let mut gates = CarryGates::new(c);
        if let Some(sum) = sum {
            gates.modulus = sum[..c].to_vec();
            gates.friction = sum[c..2 * c].iter().map(|&v| v as u64).collect();
            gates.reads = sum[2 * c] as u64;
        }
        Ok((faces, gates))
    }

    fn read_logits(&mut self, field: &Field, regions: &[Region]) -> Result<Vec<FieldRead>> {
        let (_, logits, _, _, echo) = self.run(field, regions, false, true, None)?;
        Ok(logits.into_iter().zip(echo).map(|(logits, echo)| FieldRead { logits, echo }).collect())
    }

    fn read_landmarks(&mut self, field: &Field, region: &Region, question: usize, sites: &[usize], count: usize) -> Result<Vec<Vec<(usize, u64)>>> {
        if question > region.classes.len() {
            return Err(TowerError::Refused("a landmark site outside its region"));
        }
        let rows = self.run(field, std::slice::from_ref(region), false, false, Some(sites))?.3;
        Ok(landmarks_of(&rows, question, count))
    }

    fn met_pairs(&self) -> Option<u128> {
        Some(self.times.pairs)
    }

    fn counters(&self) -> Option<RealizationCounters> {
        let t = self.times;
        Some(RealizationCounters { reads: t.reads, returns: t.returns, pairs: t.pairs, batches: t.batches, peak_store: t.peak_store })
    }

    fn read_row_currents(&mut self, field: &Field, regions: &[Region], questions: &[usize], returning: bool) -> Result<Vec<Vec<RowCurrent>>> {
        if regions.len() != questions.len() {
            return Err(TowerError::Refused("a held read's answer starts that are not one a region"));
        }
        *self.row_questions.borrow_mut() = Some(questions.to_vec());
        *self.row_out.borrow_mut() = vec![Vec::new(); regions.len()];
        let read = self.run(field, regions, returning, true, None);
        *self.row_questions.borrow_mut() = None;
        *self.row_cov.borrow_mut() = None;
        read?;
        Ok(std::mem::take(&mut *self.row_out.borrow_mut()))
    }

    fn read_covector_shares(&mut self, field: &Field, regions: &[Region]) -> Result<Vec<[u128; 2]>> {
        *self.covector_shares.borrow_mut() = Some(vec![0i128; 2 * field.declaration.heads]);
        let read = self.run(field, regions, true, false, None);
        let total = self.covector_shares.borrow_mut().take().unwrap_or_default();
        read?;
        Ok(total.chunks_exact(2).map(|c| [c[0] as u128, c[1] as u128]).collect())
    }

    fn read_ticks(&mut self, field: &Field, regions: &[Region]) -> Result<Vec<Vec<TickRead>>> {
        // Every tick is kept where a logits read keeps them; its reads are fetched after the forward.
        *self.tick_reads.borrow_mut() = Some(Vec::new());
        let read = self.run(field, regions, false, true, None);
        let out = self.tick_reads.borrow_mut().take().unwrap_or_default();
        read?;
        Ok(out)
    }

    fn read_blank_clocks(&mut self, field: &Field, region: &Region, sites: &[usize]) -> Result<Vec<BlankClocks>> {
        *self.clock_sites.borrow_mut() = Some(sites.to_vec());
        self.clock_out.borrow_mut().clear();
        let read = self.run(field, std::slice::from_ref(region), false, true, None);
        *self.clock_sites.borrow_mut() = None;
        read?;
        Ok(std::mem::take(&mut *self.clock_out.borrow_mut()))
    }

    fn read_near_offsets(&mut self, field: &Field, region: &Region, sites: &[usize]) -> Result<Vec<NearOffsets>> {
        // Every tick is kept where a logits read keeps them, and the named rows are fetched after the forward.
        *self.near_sites.borrow_mut() = Some(sites.to_vec());
        self.near_out.borrow_mut().clear();
        let read = self.run(field, std::slice::from_ref(region), false, true, None);
        *self.near_sites.borrow_mut() = None;
        let logits = read?.1;
        let mut out = std::mem::take(&mut *self.near_out.borrow_mut());
        for (near, &i) in out.iter_mut().zip(sites) {
            near.logits = logits.first().and_then(|r| r.get(i).cloned()).flatten();
        }
        Ok(out)
    }

    fn read_row_shares(&mut self, field: &Field, regions: &[Region], questions: &[usize]) -> Result<Vec<HeldRows>> {
        if regions.len() != questions.len() {
            return Err(TowerError::Refused("a held read's answer starts that are not one a region"));
        }
        // The shares of every tick are kept (a logits read keeps them), and read once each by `field_held_rows`.
        *self.held_questions.borrow_mut() = Some(questions.to_vec());
        self.held_cells.borrow_mut().clear();
        let read = self.run(field, regions, false, true, None);
        *self.held_questions.borrow_mut() = None;
        read?;
        let cells = std::mem::take(&mut *self.held_cells.borrow_mut());
        let (heads, ticks) = (field.declaration.heads, field.declaration.ticks);
        let cells = if cells.is_empty() { vec![0i128; ticks * heads * 9] } else { cells };
        Ok(cells
            .chunks_exact(9)
            .map(|c| HeldRows { rows: c[0] as u64, question: c[1] as u128, soft_near: c[2] as u128, other: c[3] as u128, question_current: c[4], question_far: c[5] as u128, far_effective: c[6] as u128, far_rows: c[7] as u64, near_definite: c[8] as u128 })
            .collect())
    }

}

/// Each kept site's still heads' rows: the met sources with their weights, and the row's mass.
type Rows = Vec<Vec<(Vec<(u32, u64)>, u64)>>;

#[cfg(test)]
mod tests {
    use super::*;

    fn declaration(width: usize, heads: usize, contacts: usize) -> FieldDeclaration {
        FieldDeclaration { alphabet: 122, width, heads, modes: 8, still: 2, contacts, ticks: 2, frames: 4, reach: 2221, lanes: 1, depth: 0, carry: 0, triads: 0, opening: false, junction: false, mark: false }
    }

    /// [measurement; theory, November 10 20:34] **The card's footprint by growth route** (host arithmetic, no card read): from the
    /// main line's declaration (width 64 in two lanes, 64 contacts, four heads of eight modes, four ticks, reach 3,771, 100 classes), each
    /// growth route at two and four times (`contacts`: f; `lane`: lanes, the width a lane's coordinates more each; `width`:
    /// [`FieldDeclaration::grown`], the width, the contacts and the lanes by the factor): the material's length, whether every affine map
    /// of the declaration still tiles a block (`affine_tiling`: the contacts' rows and the width's rows are a block's threads at most),
    /// and the octets of the longest region (a return at the reach's 3,771 sites) and of one thousand. Printed as `ROUTE` lines; ignored
    /// by default, run with `--ignored --nocapture`.

    #[test]
    #[ignore]
    fn the_card_footprint_by_growth_route() {
        let base = FieldDeclaration { alphabet: 100, width: 64, heads: 4, modes: 8, still: 2, contacts: 64, ticks: 4, frames: 4, reach: 3771, lanes: 2, depth: 0, carry: 0, triads: 0, opening: false, junction: false, mark: false };
        let describe = |name: &str, d: FieldDeclaration| {
            let draws = 4 * d.founding_draws();
            let field = holonics::hnn::tower::field::Field::found(d, &vec![7u8; draws]).expect("founded");
            let (m2, dw, f) = (2 * d.complex(), d.width, d.contacts);
            // [P61] Every map takes the tile form, whatever its shape.
            let tiled: Vec<String> = [(m2, dw), (dw, m2), (f, dw), (dw, f), (dw, dw)].iter().map(|&(r, c)| format!("{r}x{c}:tile")).collect();
            println!("ROUTE {name} width={dw} lanes={} contacts={f} material={} tiles[{}] region_3771_octets={} region_1000_octets={} site_octets={}", d.lanes, field.material_len(), tiled.join(" "), region_octets(&d, true, 3771, 3771), region_octets(&d, true, 1000, 1000), (region_octets(&d, true, 1001, 1001) - region_octets(&d, true, 1000, 1000)));
        };
        describe("base", base);
        for k in [2usize, 4] {
            describe(&format!("contacts x{k}"), FieldDeclaration { contacts: base.contacts * k, ..base });
            let mut laned = base;
            for _ in 0..(k - 1) * base.lanes {
                laned = laned.laned().expect("laned");
            }
            describe(&format!("lane x{k}"), laned);
            describe(&format!("width x{k}"), base.grown(k).expect("grown"));
        }
    }

    /// Every region is in one batch, in order, each batch within the budget; a region past the budget
    /// alone is refused.
    #[test]
    fn batches_cover_the_regions_in_order_within_the_budget() {
        let d = declaration(32, 4, 32);
        let lengths = [1412, 300, 2221, 64, 900, 1229, 1229, 77];
        for returning in [false, true] {
            let octets = |n: usize| region_octets(&d, returning, n, n);
            let budget = octets(2221) + octets(900);
            let plan = batches(&lengths, &octets, budget).unwrap();
            assert_eq!(plan.first().unwrap().start, 0);
            assert_eq!(plan.last().unwrap().end, lengths.len());
            for w in plan.windows(2) {
                assert_eq!(w[0].end, w[1].start);
            }
            for b in &plan {
                assert!(!b.is_empty() && lengths[b.clone()].iter().map(|&n| octets(n)).sum::<u64>() <= budget);
            }
            assert!(batches(&lengths, &octets, octets(2221) - 1).is_err());
        }
        assert!(batches(&[], &|n| n as u64, 1).unwrap().is_empty());
    }

    /// The carrier follows the spread read and is the declaration's `row_bits` at its bound: a row of the
    /// widest spread the declaration allows needs exactly `row_bits`, one past it is refused.
    #[test]
    fn the_carrier_follows_the_spread_and_ends_at_the_declarations_bound() {
        let d = declaration(32, 4, 32);
        let keys: Vec<u8> = (0..1u64 << 18).flat_map(|i| (i.wrapping_add(1).wrapping_mul(0x9E37_79B9_7F4A_7C15) ^ (i << 17)).to_be_bytes()).collect();
        let field = Field::found(d, &keys).unwrap();
        // The gain is read from the largest temperature the material holds (§15.10).
        let l = field.layout();
        let bound = field.row_gain().unwrap() + (usize::BITS - 1 - d.reach.leading_zeros()) as u64 + 2;
        assert_eq!(row_limbs(&field, bound).ok(), Some((field.row_bits().unwrap() as usize).div_ceil(64).max(MIN_LIMBS)).filter(|&l| l <= MAX_LIMBS));
        assert!(row_limbs(&field, bound + 1).is_err());
        // A narrow row needs five limbs at least, and the carrier never narrows as the spread widens.
        let mut last = 0;
        for spread in (0..=bound).step_by(7) {
            if let Ok(limbs) = row_limbs(&field, spread) {
                assert!(limbs >= last.max(MIN_LIMBS));
                last = limbs;
            }
        }
        assert_eq!(row_limbs(&field, 0).unwrap(), MIN_LIMBS);
    }

    /// A region's allocations count its weights, its contact's return on a return, and every site's
    /// carriers beside them: a release batch of 128 regions at the reach carries some 3 GB of them at
    /// the grown declaration, which the weights alone never counted.
    #[test]
    fn a_size_class_holds_its_length_within_a_quarter_in_whole_memset_words() {
        for len in (1..5000usize).chain([1 << 20, (1 << 20) + 1, 3_000_001]) {
            let class = size_class(len);
            assert!(class >= len && class % 4 == 0, "{len} {class}");
            // (below 17 elements the memset's four-word step is the whole class)
            assert!(len < 17 || class * 4 <= len * 5, "{len} {class}");
            assert_eq!(size_class(class), class, "{len}");
        }
    }

    #[test]
    fn a_regions_octets_count_its_carriers_beside_its_weights() {
        for d in [declaration(32, 4, 32), declaration(64, 8, 64)] {
            let n = 1504u64;
            // The scores and shares (a word a pair) are kept a tick for a return, with the reverse's covector a
            // pair on 64 bits, and one tick's otherwise; each kept tick adds its carrier widths and class offsets. The clock's skins
            // (P50 step 1, P51) are one store a batch, 32 bits a paced head, support entry and mode, `K = NEAR_SLOTS + definite` entries a row:
            // with every site definite, `n²` entries grow by pair and the near slots and the crowd edges by site.
            let skins = 4 * d.paced_heads() as u64 * d.modes as u64 * n * n;
            let weights = |returning: bool| skins + if returning { d.ticks as u64 * d.heads as u64 * 16 * n * n + 24 * n * n } else { d.heads as u64 * 8 * n * n };
            let fixed = |returning: bool| tick_fixed_octets(&d) * if returning { d.ticks as u64 } else { 1 };
            for returning in [false, true] {
                let all = region_octets(&d, returning, n as usize, n as usize);
                assert!(all > weights(returning) + fixed(returning));
                // The carriers grow by site, the weights by pair.
                let carriers = all - weights(returning) - fixed(returning);
                assert_eq!(region_octets(&d, returning, 2 * n as usize, 2 * n as usize) - 4 * weights(returning) - fixed(returning), 2 * carriers);
            }
        }
        let grown = declaration(64, 8, 64);
        let carriers = 128 * 1504 * (region_octets(&grown, false, 1, 1) - tick_fixed_octets(&grown));
        assert!(carriers > 1 << 30, "{carriers}");
    }

    /// [theory, November 12; the triad record §4] **The triads' maps tile on the main line's declaration** (host arithmetic, no card read): at
    /// `D = 64`, `f = 128` and `J = 16`, the triads' chart (`6J × D` over the pair chart's 32-bit read) tiles as every chart does, and the return of two
    /// blocks (`D × f` over `c` beside `D × 2J` over `c^T`, 64-bit faces) tiles a block of four sites in 46,912 of the 49,152 shared octets, the weights
    /// at their odd strides (`f + 1`, `2J + 1`), the bias, the joint bounds on 128 bits and a pass's rows; a return past a block's shared memory is
    /// refused the tiles and read by the cell map, the same integers.
    #[test]
    fn the_triads_maps_tile_on_the_main_lines_declaration() {
        let (dw, f, triads) = (64usize, 128usize, 16usize);
        assert_eq!(affine_two_tiling(dw, f, 2 * triads), Some((4, 46_912)));
        let need = ((dw * (f + 1) + dw * (2 * triads + 1) + dw) * 4).div_ceil(16) * 16 + 4 * 16 + 4 * (f + 2 * triads) * 8;
        assert_eq!(need, 46_912);
        assert!(affine_two_tiling(dw, 4 * f, 2 * triads).is_none(), "a return past the shared memory reads by cells");
        assert!(affine_two_tiling(512, f, 2 * triads).is_none(), "more rows than a block's threads");
    }

    /// [theory, November 12; the triad record §4] **A region's octets count the triads' carriers, and none at `J = 0`**: a kept tick holds `abg`
    /// `[t][6J]`, `p` and `c^T` `[t][2J]` (80 J octets a site) and a return adds `δc^T` and `δabg` (64 J a site); at `J = 0` the count is the
    /// declaration's as before, term for term.
    #[test]
    fn a_regions_octets_count_the_triads_carriers() {
        let base = FieldDeclaration { carry: 32, ..declaration(64, 4, 128) };
        let triads = 16u64;
        let d = FieldDeclaration { triads: triads as usize, ..base };
        for n in [2usize, 1504, 3771] {
            let s = n as u64;
            assert_eq!(region_octets(&d, false, n, n) - region_octets(&base, false, n, n), s * 80 * triads);
            assert_eq!(region_octets(&d, true, n, n) - region_octets(&base, true, n, n), s * (base.ticks as u64 * 80 * triads + 64 * triads));
            assert_eq!(read_octets(&d, false, true, n) - read_octets(&base, false, true, n), s * base.ticks as u64 * 80 * triads);
        }
    }

    /// [measurement; theory, November 12; the triad record §4] **The triads on the card read the host's bits** (needs the card): a field of
    /// `declaration(32, 4, 32)` grown by two carry circles and sixteen triads ([`holonics::hnn::tower::field::FieldLearner::with_triads`]), its
    /// readout, current and pair returns, `W_T` and the triads' chart biases moved off zero from a keyed stream's tail (so the faces have a
    /// covector and every triad term, forward and reverse, is read), read and returned on regions of 2, 3, 5, 64 and 257 sites through the host and
    /// through the card: every face and every covector entry equal, and the covector nonzero on `W_T`, the triads' chart and their biases. The
    /// ends are read with them: a region of two sites has no place with both strand mates, one of three a single one, and one of five reads each
    /// leg's covector at one place only.
    #[test]
    #[ignore = "needs the CUDA card; run alone with --include-ignored --test-threads=1"]
    fn the_triads_on_the_card_read_the_hosts_bits() {
        use holonics::hnn::tower::field::FieldLearner;
        let keys: Vec<u8> = (0..1u64 << 18).flat_map(|i| (i.wrapping_add(1).wrapping_mul(0x9E37_79B9_7F4A_7C15) ^ (i << 17)).to_be_bytes()).collect();
        let founded = Field::found(declaration(32, 4, 32), &keys).unwrap();
        let triads = 16usize;
        let mut field = FieldLearner::new(founded, 12).with_carry(2, &keys).unwrap().with_triads(triads, &keys).unwrap().field;
        let d = field.declaration;
        let (l, dw, f, m2) = (field.layout().clone(), d.width, d.contacts, 2 * d.complex());
        assert_eq!((d.triads, d.carry), (triads, 2));
        // Each moved entry with its shift: the material's families on `2^(−24)`, the triads' biases on the face's grain, eight bits coarser.
        let moved: Vec<(usize, u32)> = (l.read..l.read + dw * dw)
            .map(|i| (i, 14))
            .chain((l.out..l.out + dw * m2).map(|i| (i, 14)))
            .chain((l.w..l.w + dw * f).map(|i| (i, 14)))
            .chain((l.w_triad..l.w_triad + dw * 2 * triads).map(|i| (i, 12)))
            .chain((l.triad_bias..l.triad_bias + 6 * triads).map(|i| (i, 20)))
            .collect();
        let tail = keys.len() - 4 * moved.len() - 8;
        for (k, &(i, shift)) in moved.iter().enumerate() {
            let word = &keys[tail + 4 * k..tail + 4 * k + 4];
            field.theta[i] = i32::from_be_bytes([word[0], word[1], word[2], word[3]]) >> shift;
        }
        let lengths = [2usize, 3, 5, 64, 257];
        let classes: Vec<Vec<usize>> = lengths.iter().map(|&n| (0..n).map(|t| (t * 37 + 11) % 120).collect()).collect();
        let open: Vec<Vec<bool>> = lengths.iter().map(|&n| (0..n).map(|t| t % 3 == 1 || t + 1 == n).collect()).collect();
        let regions: Vec<Region> = classes.iter().zip(&open).map(|(c, u)| Region { classes: c, unresolved: u, faces: &[], locked: &[], echo: &[], domain: None, port: None }).collect();
        let (host_faces, host_g) = field.read_and_return(&regions).unwrap();
        let card = Card::open(0).expect("a CUDA card with the field's kernels built");
        let mut card_field = CardField::open(&card).unwrap();
        let (card_faces, card_g) = card_field.read_and_return(&field, &regions).unwrap();
        assert_eq!(host_faces, card_faces);
        assert_eq!(host_g.len(), card_g.len());
        let unequal: Vec<usize> = (0..host_g.len()).filter(|&i| host_g[i] != card_g[i]).collect();
        assert!(unequal.is_empty(), "{} covector entries differ, the first at {:?} (triad at {}, triad_bias at {}, w_triad at {})", unequal.len(), unequal.first(), l.triad, l.triad_bias, l.w_triad);
        // [P58 item 3] The faces at their classes gathered on the card are the whole faces' at their classes, beside the same covector.
        let (at_class, narrow_g) = card_field.read_and_return_at_class(&field, &regions).unwrap();
        assert_eq!(at_class, holonics::hnn::tower::field::faces_at_class(&host_faces, &regions));
        assert!(narrow_g == card_g, "the narrow read's covector differs from the whole read's");
        // [P57 item 2] The open sites' charts by stage on the card are the host's, beside the same faces.
        let (charts_faces, card_charts) = card_field.read_tick_charts(&field, &regions).unwrap();
        let (host_charts_faces, host_charts) = holonics::hnn::tower::field::HostField.read_tick_charts(&field, &regions).unwrap();
        assert_eq!(charts_faces, host_charts_faces);
        assert_eq!(card_charts.len(), regions.len());
        assert!(card_charts == host_charts, "the charts by stage differ between the card and the host");
        assert_eq!(card_charts[4].len(), field.declaration.ticks + 1);
        for (name, start, len) in [("w_triad", l.w_triad, dw * 2 * triads), ("triad", l.triad, 6 * triads * dw), ("triad_bias", l.triad_bias, 6 * triads)] {
            assert!(host_g[start..start + len].iter().any(|&v| v != 0), "the triads' {name} takes no covector");
        }
    }

    /// [realization; theory, November 13, P61 item 5] **A site's maps in the tile form read the definitions' integers** (needs the card): the
    /// forward map, the transposed map and the outer sum with its bound, at every shape the store line's declaration launches (P61's reading:
    /// forward 64 × 64 and 128 × 64 on 32-bit inputs, 64 × 64 and 64 × 128 on 64-bit ones; transposed 64 × 64, 64 × 128 and 128 × 64; outer
    /// 64 × 64 and 128 × 64 on 32-bit inputs, 64 × 64 and 64 × 128 on 64-bit ones, and the bias's sums of 64, 128 and 244), against the
    /// definitions summed here on 128 bits: every output word, every entry of `g` (a ring sum on 128 bits) and the status bits equal. The
    /// fixtures force the wide form (words past `2^31` in some tiles), a site the forward map refuses (`wmax · xmax · (cols + 1) ≥ 2^126`), a
    /// region the outer bound refuses, a mask of open sites, `add` and `accumulate`, site counts that are no multiple of a tile, and the bias's
    /// sum with no `x`.
    #[test]
    #[ignore = "needs the CUDA card; run alone with --include-ignored --test-threads=1"]
    fn a_sites_maps_in_the_tile_form_read_the_definitions_integers() {
        let card = Card::open(0).expect("a CUDA card with the field's kernels built");
        let cf = CardField::open(&card).unwrap();
        let mut state = 0x9E37_79B9_7F4A_7C15u64;
        let mut next = move || {
            state = state.wrapping_add(0x9E37_79B9_7F4A_7C15);
            let mut z = state;
            z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
            z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
            z ^ (z >> 31)
        };
        // A word of `bits` bits, signed.
        let mut word = |bits: u32| -> i64 { let v = (next() >> (64 - bits)) as i64; if next() & 1 == 1 { -v } else { v } };
        let rel = |x: i128, bits: u32| -> i128 { let half = 1i128 << (bits - 1); if x >= 0 { (x + half) >> bits } else { -((-x + half) >> bits) } };
        let (refused_carrier, refused_word64) = (1u32, 2u32);
        let fit = |v: i128, st: &mut u32| -> i64 { if v > i64::MAX as i128 || v < i64::MIN as i128 { *st |= refused_word64; 0 } else { v as i64 } };
        let mut checked = 0usize;
        // Sites: no multiple of a tile, and more than a walk of the outer sum.
        for &sites in &[37usize, 200, 1093] {
            let regions: Vec<u32> = { let mut r = vec![0u32]; let mut at = 0u32; while (at as usize) < sites { at = (at + 97 + (word(9).unsigned_abs() % 300) as u32).min(sites as u32); r.push(at); } r };
            for &only in &[false, true] {
                let unresolved: Vec<u8> = (0..sites).map(|t| u8::from(!only || t % 3 != 1)).collect();
                let mut base = Words { t: sites as u32, r: (regions.len() - 1) as u32, ..Default::default() };
                let unresolved_buf = card.upload(&unresolved).unwrap();
                let region_buf = card.upload(&regions).unwrap();
                base.unresolved = unresolved_buf.device_ptr();
                base.region_off = region_buf.device_ptr();
                // The forward map.
                for &(rows, cols, x64, add, wide_tile, refuse) in &[(64usize, 64usize, false, false, false, false), (128, 64, false, false, false, false), (64, 64, true, true, true, false), (64, 128, true, true, false, true), (64, 64, true, false, false, false)] {
                    let w: Vec<i32> = (0..rows * cols).map(|_| word(28) as i32).collect();
                    let b: Vec<i32> = (0..rows).map(|_| word(20) as i32).collect();
                    let theta: Vec<i32> = w.iter().chain(&b).copied().collect();
                    let wmax_true = w.iter().map(|v| v.unsigned_abs() as u64).max().unwrap();
                    let x: Vec<i64> = (0..sites * cols).map(|c| { let t = c / cols; if x64 && wide_tile && t % 64 < 3 { word(40) } else if x64 && refuse && t == sites / 2 { if c % cols == 0 { 1i64 << 61 } else { word(40) } } else { word(22) } }).collect();
                    // A refused site: the host's carrier bound read with a weight bound past the true one (`2^58 · 2^61 · 129` reaches `2^126`
                    // and stands under `2^128`).
                    let wmax = if refuse { 1u64 << 58 } else { wmax_true };
                    let prior: Vec<i64> = (0..sites * rows).map(|_| word(40)).collect();
                    let theta_buf = card.upload(&theta).unwrap();
                    let status_buf = card.zeroed::<u32>(1).unwrap();
                    let out_buf = card.upload(&prior).unwrap();
                    let x_buf = if x64 { card.upload(&x).unwrap() } else { card.upload(&x.iter().map(|&v| v as i32 as i64).collect::<Vec<_>>()).unwrap() };
                    let x32: Vec<i32> = x.iter().map(|&v| v as i32).collect();
                    let x32_buf = card.upload(&x32).unwrap();
                    let mut words = Words { theta: theta_buf.device_ptr(), status: status_buf.device_ptr(), ..base };
                    let xp = if x64 { x_buf.device_ptr() } else { x32_buf.device_ptr() };
                    let entry = if x64 { "field_affine_x64" } else { "field_affine_x32" };
                    let (outp, addp) = if add { (0, out_buf.device_ptr()) } else { (out_buf.device_ptr(), 0) };
                    cf.affine(entry, &mut words, 0, (rows * cols) as u64, wmax, rows, cols, xp, cols, outp, rows, addp, only).unwrap();
                    let got = card.fetch(&out_buf).unwrap();
                    let st = card.fetch(&status_buf).unwrap()[0];
                    let (mut want, mut wst) = (prior.clone(), 0u32);
                    for t in 0..sites {
                        if only && unresolved[t] == 0 {
                            continue;
                        }
                        let xt: Vec<i128> = (0..cols).map(|i| if x64 { x[t * cols + i] as i128 } else { x32[t * cols + i] as i128 }).collect();
                        let xmax = xt.iter().map(|v| v.unsigned_abs()).max().unwrap();
                        if (wmax as u128) * xmax * (cols as u128 + 1) >= 1u128 << 126 {
                            wst |= refused_carrier;
                            continue;
                        }
                        for o in 0..rows {
                            let sum: i128 = (0..cols).map(|i| w[o * cols + i] as i128 * xt[i]).sum::<i128>() + ((b[o] as i128) << 24);
                            let v = fit(rel(sum, 24), &mut wst);
                            want[t * rows + o] = if add { fit(prior[t * rows + o] as i128 + v as i128, &mut wst) } else { v };
                        }
                    }
                    assert_eq!(st, wst, "forward {rows}x{cols} x64={x64} sites={sites} only={only}: the status bits");
                    assert!(got == want, "forward {rows}x{cols} x64={x64} add={add} sites={sites} only={only}: {} words differ", got.iter().zip(&want).filter(|(a, b)| a != b).count());
                    checked += 1;
                }
                // The transposed map.
                for &(rows, cols, acc, wide_tile) in &[(64usize, 64usize, false, true), (64, 64, true, false), (64, 128, false, false), (128, 64, true, true)] {
                    let w: Vec<i32> = (0..rows * cols).map(|_| word(28) as i32).collect();
                    let y: Vec<i64> = (0..sites * rows).map(|c| if wide_tile && (c / rows) % 64 == 5 { word(44) } else { word(31) }).collect();
                    let prior: Vec<i64> = (0..sites * cols).map(|_| word(40)).collect();
                    let theta_buf = card.upload(&w).unwrap();
                    let status_buf = card.zeroed::<u32>(1).unwrap();
                    let out_buf = card.upload(&prior).unwrap();
                    let y_buf = card.upload(&y).unwrap();
                    let mut words = Words { theta: theta_buf.device_ptr(), status: status_buf.device_ptr(), ..base };
                    cf.transposed(&mut words, 0, rows, cols, y_buf.device_ptr(), rows, out_buf.device_ptr(), acc, only).unwrap();
                    let got = card.fetch(&out_buf).unwrap();
                    let st = card.fetch(&status_buf).unwrap()[0];
                    let (mut want, mut wst) = (prior.clone(), 0u32);
                    for t in 0..sites {
                        if only && unresolved[t] == 0 {
                            continue;
                        }
                        for i in 0..cols {
                            let sum: i128 = (0..rows).map(|o| w[o * cols + i] as i128 * y[t * rows + o] as i128).sum();
                            let v = fit(rel(sum, 24), &mut wst);
                            want[t * cols + i] = if acc { fit(prior[t * cols + i] as i128 + v as i128, &mut wst) } else { v };
                        }
                    }
                    assert_eq!(st, wst, "transposed {rows}x{cols} sites={sites} only={only}: the status bits");
                    assert!(got == want, "transposed {rows}x{cols} acc={acc} sites={sites} only={only}: {} words differ", got.iter().zip(&want).filter(|(a, b)| a != b).count());
                    checked += 1;
                }
                // The outer sum and its bound, and the bias's sums.
                for &(rows, cols, x64, case) in &[(64usize, 64usize, false, 0u8), (128, 64, false, 1), (64, 64, true, 1), (64, 128, true, 2), (64, 0, false, 0), (128, 0, false, 1), (244, 0, false, 0)] {
                    // case 0 narrow; 1 a wide walk (words past 2^31 in one walk); 2 a region refused by the bound.
                    let y: Vec<i64> = (0..sites * rows).map(|c| { let t = c / rows; if case == 1 && t % 512 < 4 { word(40) } else if case == 2 && t < 8 { word(63) } else { word(31) } }).collect();
                    let xw = cols.max(1);
                    let x: Vec<i64> = (0..sites * xw).map(|c| { let t = c / xw; if case == 2 && t < 8 { word(63) } else { word(22) } }).collect();
                    let x32: Vec<i32> = x.iter().map(|&v| v as i32).collect();
                    let entries = rows * cols.max(1);
                    let at = 3usize;
                    let prior: Vec<i128> = (0..entries + 2 * at).map(|_| (word(60) as i128) << 20).collect();
                    let status_buf = card.zeroed::<u32>(1).unwrap();
                    let g_buf = card.upload(&prior).unwrap();
                    let y_buf = card.upload(&y).unwrap();
                    let x_buf = card.upload(&x).unwrap();
                    let x32_buf = card.upload(&x32).unwrap();
                    let mut words = Words { status: status_buf.device_ptr(), ..base };
                    let xp = if cols == 0 { 0 } else if x64 { x_buf.device_ptr() } else { x32_buf.device_ptr() };
                    cf.outer(&mut words, &g_buf, at as u64, rows, cols, y_buf.device_ptr(), rows, xp, xw, x64, only).unwrap();
                    let got = card.fetch(&g_buf).unwrap();
                    let st = card.fetch(&status_buf).unwrap()[0];
                    let (mut want, mut wst) = (prior.clone(), 0u32);
                    let live = |t: usize| !(only && unresolved[t] == 0);
                    let xv = |t: usize, i: usize| -> i128 { if x64 { x[t * xw + i] as i128 } else { x32[t * xw + i] as i128 } };
                    for o in 0..rows {
                        for i in 0..cols.max(1) {
                            let mut sum = 0i128;
                            for t in (0..sites).filter(|&t| live(t)) {
                                sum = sum.wrapping_add((y[t * rows + o] as i128).wrapping_mul(if cols == 0 { 1 } else { xv(t, i) }));
                            }
                            want[at + o * cols.max(1) + i] = want[at + o * cols.max(1) + i].wrapping_add(sum);
                        }
                    }
                    if cols > 0 {
                        for r in 0..regions.len() - 1 {
                            let mut bound = 0u128;
                            let mut over = false;
                            for t in (regions[r] as usize..regions[r + 1] as usize).filter(|&t| live(t)) {
                                let ym = (0..rows).map(|o| (y[t * rows + o] as i128).unsigned_abs()).max().unwrap();
                                let xm = (0..cols).map(|i| xv(t, i).unsigned_abs()).max().unwrap();
                                match bound.checked_add(ym * xm) {
                                    Some(b) if b < 1u128 << 126 => bound = b,
                                    _ => over = true,
                                }
                            }
                            if over {
                                wst |= refused_carrier;
                            }
                        }
                    }
                    assert_eq!(st, wst, "outer {rows}x{cols} x64={x64} case={case} sites={sites} only={only}: the status bits");
                    assert!(got == want, "outer {rows}x{cols} x64={x64} case={case} sites={sites} only={only}: {} entries differ", got.iter().zip(&want).filter(|(a, b)| a != b).count());
                    checked += 1;
                }
            }
        }
        println!("SITE_MAPS_PARITY cases={checked}");
        assert_eq!(checked, 3 * 2 * (5 + 4 + 7));
    }

    /// [measurement; theory, November 13, P60 item 2] **The opening's comparison on the card reads the host's bits** (needs the card): a field of
    /// two carry circles with the opening's lift, its readout, current, pair return and the lift moved off zero from a keyed stream's tail and its
    /// paces moved off zero (so the paced heads' clocks are not plain and the cavity clocks differ from the standing ones), read and returned on
    /// regions of 2, 3, 5, 64 and 257 sites (written and open places, the far crowds reached) through the host and through the card: every face,
    /// every covector entry and every place's opening code equal, the covector reaching the lift, its bias, the unresolved row and the paces; and
    /// one learner's section on both, its receipt (the opening's codes with it) and its state equal.
    #[test]
    #[ignore = "needs the CUDA card; run alone with --include-ignored --test-threads=1"]
    fn the_opening_comparison_on_the_card_reads_the_hosts_bits() {
        use holonics::hnn::tower::field::{FieldLearner, HostField};
        let keys: Vec<u8> = (0..1u64 << 18).flat_map(|i| (i.wrapping_add(1).wrapping_mul(0x9E37_79B9_7F4A_7C15) ^ (i << 17)).to_be_bytes()).collect();
        let founded = Field::found(declaration(32, 4, 32), &keys).unwrap();
        let mut learner = FieldLearner::new(founded, 12).with_carry(2, &keys).unwrap().with_opening().unwrap();
        let d = learner.field.declaration;
        assert!(d.opening);
        let (l, dw, f, m2) = (learner.field.layout().clone(), d.width, d.contacts, 2 * d.complex());
        let moved: Vec<usize> = (l.read..l.read + dw * dw).chain(l.out..l.out + dw * m2).chain(l.w..l.w + dw * f).chain(l.opening..l.opening + dw * dw).collect();
        let tail = keys.len() - 4 * moved.len() - 8;
        for (k, &i) in moved.iter().enumerate() {
            let word = &keys[tail + 4 * k..tail + 4 * k + 4];
            learner.field.theta[i] = i32::from_be_bytes([word[0], word[1], word[2], word[3]]) >> 14;
        }
        let paces = d.paced_heads() * (d.alphabet + 1);
        let before = tail - 4 * paces;
        for k in 0..paces {
            let word = &keys[before + 4 * k..before + 4 * k + 4];
            learner.field.theta[l.pace + k] = i32::from_be_bytes([word[0], word[1], word[2], word[3]]) >> 12;
        }
        let field = learner.field.clone();
        let lengths = [2usize, 3, 5, 64, 257];
        let classes: Vec<Vec<usize>> = lengths.iter().map(|&n| (0..n).map(|t| (t * 37 + 11) % 120).collect()).collect();
        let open: Vec<Vec<bool>> = lengths.iter().map(|&n| (0..n).map(|t| t % 3 == 1 || t + 1 == n).collect()).collect();
        let regions: Vec<Region> = classes.iter().zip(&open).map(|(c, u)| Region { classes: c, unresolved: u, faces: &[], locked: &[], echo: &[], domain: None, port: None }).collect();
        let (host_faces, host_g) = field.read_and_return(&regions).unwrap();
        let card = Card::open(0).expect("a CUDA card with the field's kernels built");
        let mut card_field = CardField::open(&card).unwrap();
        let (card_faces, card_g) = card_field.read_and_return(&field, &regions).unwrap();
        assert_eq!(host_faces, card_faces);
        let unequal: Vec<usize> = (0..host_g.len()).filter(|&i| host_g[i] != card_g[i]).collect();
        let family = |i: usize| field.families_all().iter().position(|&(s, n, _)| (s..s + n).contains(&i));
        assert!(unequal.is_empty(), "{} covector entries differ, the first at {:?} (its family {:?}; opening at {}, opening_bias at {}, pace at {})", unequal.len(), unequal.first(), unequal.first().map(|&i| family(i)), l.opening, l.opening_bias, l.pace);
        let (host_at, host_ng, host_codes) = HostField.read_and_return_opening(&field, &regions).unwrap();
        let (card_at, card_ng, card_codes) = card_field.read_and_return_opening(&field, &regions).unwrap();
        assert_eq!(host_at, card_at);
        assert!(host_ng == card_ng && card_ng == card_g, "the opening's training read's covector differs");
        assert_eq!(host_codes, card_codes);
        assert_eq!(card_codes.iter().map(Vec::len).collect::<Vec<_>>(), lengths.to_vec());
        assert!(card_codes.iter().flatten().all(Option::is_some), "every place compared");
        for (name, start, len) in [("opening", l.opening, dw * dw), ("opening_bias", l.opening_bias, dw), ("unresolved row", l.enc + d.alphabet * dw, dw), ("pace", l.pace, paces)] {
            assert!(host_g[start..start + len].iter().any(|&v| v != 0), "the opening's comparison returns nothing to {name}");
        }
        // One section on the host and on the card: the receipt with the opening's codes, and the state after the deposit.
        let (mut host_learner, mut card_learner) = (learner.clone(), learner.clone());
        let host_receipt = host_learner.section_realized(&regions, &mut HostField).unwrap();
        let card_receipt = card_learner.section_realized(&regions, &mut card_field).unwrap();
        assert_eq!(host_receipt, card_receipt);
        assert_eq!(card_receipt.opening.len(), regions.len());
        assert!(host_learner.to_text() == card_learner.to_text(), "the learner's state after a section differs between the host and the card");
    }

    /// [definition; theory, November 13, the design record §4.9; G145] **The level above on the card reads the host's bits**: a learner with
    /// carry circles and the opening's block, its read, out, contact, opening and pace blocks drawn, grown by a level (six harmonics after half
    /// its ticks), the level's prolongation drawn so every path of the level carries; the faces and the whole covector of a training read, and
    /// the faces of a read that does not return (the level reads the opening's news there too), equal on host and card.
    #[test]
    #[ignore = "needs the CUDA card; run alone with --include-ignored --test-threads=1"]
    fn the_level_on_the_card_reads_the_hosts_bits() {
        use holonics::hnn::tower::field::{level_declaration, level_split, FieldLearner, FieldRealization, HostField, LEVEL_HARMONICS};
        let keys: Vec<u8> = (0..1u64 << 18).flat_map(|i| (i.wrapping_add(1).wrapping_mul(0x9E37_79B9_7F4A_7C15) ^ (i << 17)).to_be_bytes()).collect();
        let founded = Field::found(declaration(32, 4, 32), &keys).unwrap();
        let mut learner = FieldLearner::new(founded, 12).with_carry(2, &keys).unwrap().with_opening().unwrap();
        let d = learner.field.declaration;
        let (l, dw, f, m2) = (learner.field.layout().clone(), d.width, d.contacts, 2 * d.complex());
        let moved: Vec<usize> = (l.read..l.read + dw * dw).chain(l.out..l.out + dw * m2).chain(l.w..l.w + dw * f).chain(l.opening..l.opening + dw * dw).collect();
        let tail = keys.len() - 4 * moved.len() - 8;
        for (k, &i) in moved.iter().enumerate() {
            let word = &keys[tail + 4 * k..tail + 4 * k + 4];
            learner.field.theta[i] = i32::from_be_bytes([word[0], word[1], word[2], word[3]]) >> 14;
        }
        let paces = d.paced_heads() * (d.alphabet + 1);
        let before = tail - 4 * paces;
        for k in 0..paces {
            let word = &keys[before + 4 * k..before + 4 * k + 4];
            learner.field.theta[l.pace + k] = i32::from_be_bytes([word[0], word[1], word[2], word[3]]) >> 12;
        }
        let mut leveled = learner.scaled_up(LEVEL_HARMONICS, level_split(&d), level_declaration(&d), &keys).unwrap();
        let s = leveled.field.scale.as_deref_mut().unwrap();
        let (_, _, b, _, len) = s.glue_offsets(dw);
        let back = before - 4 * (len - b) - 8;
        for (k, v) in s.glue[b..].iter_mut().enumerate() {
            let word = &keys[back + 4 * k..back + 4 * k + 4];
            *v = i32::from_be_bytes([word[0], word[1], word[2], word[3]]) >> 12;
        }
        let field = leveled.field.clone();
        let lengths = [2usize, 3, 5, 64, 257];
        let classes: Vec<Vec<usize>> = lengths.iter().map(|&n| (0..n).map(|t| (t * 37 + 11) % 120).collect()).collect();
        let open: Vec<Vec<bool>> = lengths.iter().map(|&n| (0..n).map(|t| t % 3 == 1 || t + 1 == n).collect()).collect();
        let regions: Vec<Region> = classes.iter().zip(&open).map(|(c, u)| Region { classes: c, unresolved: u, faces: &[], locked: &[], echo: &[], domain: None, port: None }).collect();
        let cuts: Vec<usize> = regions.iter().map(|r| holonics::hnn::tower::field::level_anchors(&field.level_news(r).unwrap(), holonics::hnn::tower::field::level_section(d.alphabet)).len()).collect();
        assert!(cuts.iter().zip(&lengths).any(|(&e, &n)| e > 1 && e < n), "the fixture's news cuts some region into epochs: {cuts:?} of {lengths:?}");
        let (host_faces, host_g) = field.read_and_return(&regions).unwrap();
        let card = Card::open(0).expect("a CUDA card with the field's kernels built");
        let mut card_field = CardField::open(&card).unwrap();
        let (card_faces, card_g) = card_field.read_and_return(&field, &regions).unwrap();
        assert_eq!(host_faces, card_faces);
        let unequal: Vec<usize> = (0..host_g.len()).filter(|&i| host_g[i] != card_g[i]).collect();
        let family = |i: usize| field.families_all().iter().position(|&(s, n, _)| (s..s + n).contains(&i));
        assert!(unequal.is_empty(), "{} covector entries differ, the first at {:?} (its family {:?}; the fine material ends at {})", unequal.len(), unequal.first(), unequal.first().map(|&i| family(i)), field.theta.len());
        assert!(host_g[field.theta.len()..].iter().any(|&v| v != 0), "the level's covector reaches its material");
        let host_read = HostField.read_faces(&field, &regions).unwrap();
        let card_read = card_field.read_faces(&field, &regions).unwrap();
        assert_eq!(host_read, card_read, "a read that does not return");
    }

    /// The lettered learner's case ([`a_lettered_learners_section_on_the_card_reads_the_hosts_bits`]): the learner, its layout and width, the
    /// fresh letters' count, and the stretches' classes, open sites and domains.
    fn lettered_case() -> (holonics::hnn::tower::field::FieldLearner, holonics::hnn::tower::field::FieldLayout, usize, usize, Vec<Vec<usize>>, Vec<Vec<bool>>, Vec<Option<usize>>) {
        use holonics::hnn::tower::field::FieldLearner;
        let keys: Vec<u8> = (0..1u64 << 18).flat_map(|i| (i.wrapping_add(1).wrapping_mul(0x9E37_79B9_7F4A_7C15) ^ (i << 17)).to_be_bytes()).collect();
        let founded = Field::found(FieldDeclaration { alphabet: 100, ..declaration(32, 4, 32) }, &keys).unwrap();
        let fresh = 5usize;
        let mut learner = FieldLearner::new(founded, 12).with_carry(2, &keys).unwrap().lettered(fresh).unwrap();
        let d = learner.field.declaration;
        assert_eq!((d.alphabet, d.carry), (100 + fresh, 2));
        let (l, dw, f, m2) = (learner.field.layout().clone(), d.width, d.contacts, 2 * d.complex());
        let moved: Vec<usize> = (l.read..l.read + dw * dw).chain(l.out..l.out + dw * m2).chain(l.w..l.w + dw * f).collect();
        let tail = keys.len() - 4 * moved.len() - 8;
        for (k, &i) in moved.iter().enumerate() {
            let word = &keys[tail + 4 * k..tail + 4 * k + 4];
            learner.field.theta[i] = i32::from_be_bytes([word[0], word[1], word[2], word[3]]) >> 14;
        }
        // [theory, November 12, P50 step 1] The paces moved off zero from the words before the tail (a rate a class on `2^(−24)`, within `±2^(−5)`), so
        // the paced heads' clocks are not plain: their skins are formed by the clock's fill and read from its store.
        let paces = d.paced_heads() * (d.alphabet + 1);
        let before = tail - 4 * paces;
        for k in 0..paces {
            let word = &keys[before + 4 * k..before + 4 * k + 4];
            learner.field.theta[l.pace + k] = i32::from_be_bytes([word[0], word[1], word[2], word[3]]) >> 12;
        }
        let void = 99usize;
        // Stretches: (context, run, a true end), each one state.
        let stretches = [(7usize, 33usize, true), (12, 61, false), (4, 9, true), (30, 90, false), (5, 17, true)];
        let mut classes: Vec<Vec<usize>> = Vec::new();
        let mut open: Vec<Vec<bool>> = Vec::new();
        let mut domains: Vec<Option<usize>> = Vec::new();
        for (s, &(q, a, ends)) in stretches.iter().enumerate() {
            let n = q + a + if ends { NEAR } else { 0 };
            classes.push((0..n).map(|t| if t >= q + a { void } else if (t * 7 + s) % 11 == 0 { 100 + (t + s) % fresh } else { (t * 37 + 11 * s) % 99 }).collect());
            let (u, dom) = match s % 3 {
                // A mask state over the whole stretch, and one past its context.
                0 => ((0..n).map(|t| t % 3 == 1).collect::<Vec<_>>(), Some(((4 * n * (0..n).filter(|t| t % 3 == 1).count()) as u128).isqrt() as usize)),
                1 => ((0..n).map(|t| t >= q && t % 2 == 0).collect::<Vec<_>>(), Some(((4 * (n - q) * (q..n).filter(|t| t % 2 == 0).count()) as u128).isqrt() as usize)),
                // The writer's state: the context known, the run's first places resolved, the end's voids given.
                _ => ((0..n).map(|t| t >= q + a / 4 && t < q + a).collect::<Vec<_>>(), None),
            };
            open.push(u);
            domains.push(dom);
        }
        assert!(classes.iter().flatten().any(|&c| c >= 100) && classes.iter().flatten().any(|&c| c == 99));
        (learner, l, dw, fresh, classes, open, domains)
    }

    /// [measurement; theory, November 12 (the record of the opening's room, §4 items 2 and 4)] **A lettered learner's section on the card
    /// reads the host's bits** (needs the card): a learner of 100 classes with two carry circles grown by five fresh letters
    /// ([`holonics::hnn::tower::field::FieldLearner::lettered`]), its readout, current and pair returns moved off zero from a keyed stream's tail, takes
    /// one section of stretches as the store's trainer forms them (mask states over a whole stretch and past its context with their weighed
    /// domains, and writer's states with the first of their run resolved, a true end's near tail of voids, plain regions with no port) whose
    /// classes hold the void and fresh letters, through the host and through the card: the receipt, the material and the moments after the
    /// deposit equal, and the read and return of the same regions on the learner's field equal face for face and entry for entry, with a
    /// covector reaching the fresh letters' encoding rows.
    #[test]
    #[ignore = "needs the CUDA card; run alone with --include-ignored --test-threads=1"]
    fn a_lettered_learners_section_on_the_card_reads_the_hosts_bits() {
        use holonics::hnn::tower::field::HostField;
        let (learner, l, dw, fresh, classes, open, domains) = lettered_case();
        let regions: Vec<Region> = classes.iter().zip(&open).zip(&domains).map(|((c, u), &dom)| Region { classes: c, unresolved: u, faces: &[], locked: &[], echo: &[], domain: dom, port: None }).collect();
        let card = Card::open(0).expect("a CUDA card with the field's kernels built");
        let mut card_field = CardField::open(&card).unwrap();
        let (host_faces, host_g) = learner.field.read_and_return(&regions).unwrap();
        let (card_faces, card_g) = card_field.read_and_return(&learner.field, &regions).unwrap();
        assert_eq!(host_faces, card_faces);
        let unequal: Vec<usize> = (0..host_g.len()).filter(|&i| host_g[i] != card_g[i]).collect();
        assert!(unequal.is_empty() && host_g.len() == card_g.len(), "{} covector entries differ, the first at {:?}", unequal.len(), unequal.first());
        assert!(host_g[l.enc + 100 * dw..l.enc + (100 + fresh) * dw].iter().any(|&v| v != 0), "a covector reaches the fresh letters' encoding rows");
        let (mut on_host, mut on_card) = (learner.clone(), learner.clone());
        let host_receipt = on_host.section_realized(&regions, &mut HostField).unwrap();
        let card_receipt = on_card.section_realized(&regions, &mut card_field).unwrap();
        assert_eq!(host_receipt, card_receipt);
        assert!(host_receipt.deposited);
        assert_eq!(on_host.to_text(), on_card.to_text(), "the material and the moments after the deposit");
    }

    /// [theory, November 12, P50 step 3] **The turn's series on its narrow words is the wide series** (needs the card): on a sweep of the turn's
    /// arguments with its edges (zero, the least step, the faces just under a whole clock at the half turn, the largest admitted `⌊π 2^30⌉`, and every
    /// 2^13-th argument between), `turn_series_dev` and `exp_series_dev(0, b)` give the same integers on the card.
    #[test]
    #[ignore = "needs the CUDA card; run alone with --include-ignored --test-threads=1"]
    fn the_turns_series_on_narrow_words_is_the_wide_series() {
        let top = 3_373_259_426i64;
        let mut bs: Vec<i64> = vec![0, 1, -1, 2, -2, top, -top, top - 1, -(top - 1), top - 2, -(top - 2), 1 << 31, -(1 << 31), (1 << 30) - 1, 1 << 30];
        bs.extend((-top..=top).step_by(1 << 13));
        let card = Card::open(0).expect("a CUDA card with the field's kernels built");
        let card_field = CardField::open(&card).unwrap();
        let out = card_field.series_check(&bs).unwrap();
        let differ: Vec<i64> = bs.iter().enumerate().filter(|(c, _)| out[4 * c] != out[4 * c + 2] || out[4 * c + 1] != out[4 * c + 3]).map(|(_, &b)| b).collect();
        assert!(differ.is_empty(), "{} of {} arguments differ, the first {:?}", differ.len(), bs.len(), differ.first());
        let (b0, bt) = (0usize, 5usize);
        assert_eq!((out[4 * b0], out[4 * b0 + 1]), (1 << 30, 0), "the zero argument's face is one");
        assert!((out[4 * bt] + (1 << 30)).abs() < 1 << 10 && out[4 * bt + 1].abs() < 1 << 10, "the largest argument turns to the half turn within the series' rounding");
        // The bound the clock's store holds a phase's parts by (P50 step 2): under `2^30 + 2^10` at every argument.
        let peak = out.iter().map(|v| v.unsigned_abs()).max().unwrap_or(0);
        assert!(peak < (1 << 30) + (1 << 10), "a face's part {peak} past 2^30 + 2^10");
        println!("SERIES_CHECK arguments={} equal={} peak_part={peak} half_turn=({}, {})", bs.len(), bs.len() - differ.len(), out[4 * bt], out[4 * bt + 1]);
    }

    /// [theory, November 12, P50 step 1] **A skin no fill formed is refused**: the lettered learner's read and return with the clock's fill withheld
    /// (the test build writes `SKIN_UNFILLED` over the store before each fill) is refused by the card. So its readers read the clock's store, and a word
    /// no fill formed never enters a sum.
    #[test]
    #[ignore = "needs the CUDA card; run alone with --include-ignored --test-threads=1"]
    fn a_skin_no_fill_formed_is_refused() {
        let (learner, _, _, _, classes, open, domains) = lettered_case();
        let regions: Vec<Region> = classes.iter().zip(&open).zip(&domains).map(|((c, u), &dom)| Region { classes: c, unresolved: u, faces: &[], locked: &[], echo: &[], domain: dom, port: None }).collect();
        let card = Card::open(0).expect("a CUDA card with the field's kernels built");
        let mut card_field = CardField::open(&card).unwrap();
        card_field.unfilled.set(true);
        let refused = card_field.read_and_return(&learner.field, &regions).map(|_| ()).expect_err("a read of a store no fill formed is refused");
        assert!(refused.to_string().contains("a skin read from the clock's store where its fill formed none"), "{refused}");
    }

    /// The strengths the mark is read at off its founding: a quarter, an eighth and three sixteenths on the material's grain (`enc`, `before`,
    /// `after`), the host's covector test's.
    const MARK_STRENGTHS: [i32; 3] = [1 << 22, 1 << 21, 3 << 20];

    /// [the ring record §4] The learners a field that reads twice is grown onto on the card, before the growth: plain (its read, out and contact
    /// blocks drawn off zero from a keyed stream's tail), with two carry circles, with the circles and the opening's lift (the lift and the paces
    /// drawn too, so the paced heads' clocks are not plain), and that learner grown by a level (its prolongation drawn).
    fn mark_cases() -> Vec<(&'static str, holonics::hnn::tower::field::FieldLearner)> {
        use holonics::hnn::tower::field::{level_declaration, level_split, FieldLearner, LEVEL_HARMONICS};
        let keys: Vec<u8> = (0..1u64 << 18).flat_map(|i| (i.wrapping_add(1).wrapping_mul(0x9E37_79B9_7F4A_7C15) ^ (i << 17)).to_be_bytes()).collect();
        let founded = Field::found(declaration(32, 4, 32), &keys).unwrap();
        let drawn = |mut learner: FieldLearner, paces: bool| -> (FieldLearner, usize) {
            let d = learner.field.declaration;
            let (l, dw, f, m2) = (learner.field.layout().clone(), d.width, d.contacts, 2 * d.complex());
            let lift = if d.opening { dw * dw } else { 0 };
            let moved: Vec<usize> = (l.read..l.read + dw * dw).chain(l.out..l.out + dw * m2).chain(l.w..l.w + dw * f).chain(l.opening..l.opening + lift).collect();
            let tail = keys.len() - 4 * moved.len() - 8;
            for (k, &i) in moved.iter().enumerate() {
                let word = &keys[tail + 4 * k..tail + 4 * k + 4];
                learner.field.theta[i] = i32::from_be_bytes([word[0], word[1], word[2], word[3]]) >> 14;
            }
            let rates = if paces { d.paced_heads() * (d.alphabet + 1) } else { 0 };
            let before = tail - 4 * rates;
            for k in 0..rates {
                let word = &keys[before + 4 * k..before + 4 * k + 4];
                learner.field.theta[l.pace + k] = i32::from_be_bytes([word[0], word[1], word[2], word[3]]) >> 12;
            }
            (learner, before)
        };
        let (plain, _) = drawn(FieldLearner::new(founded.clone(), 12), false);
        let (carry, _) = drawn(FieldLearner::new(founded.clone(), 12).with_carry(2, &keys).unwrap(), false);
        let (opened, before) = drawn(FieldLearner::new(founded, 12).with_carry(2, &keys).unwrap().with_opening().unwrap(), true);
        let d = opened.field.declaration;
        let mut tower = opened.scaled_up(LEVEL_HARMONICS, level_split(&d), level_declaration(&d), &keys).unwrap();
        let s = tower.field.scale.as_deref_mut().unwrap();
        let (_, _, b, _, len) = s.glue_offsets(d.width);
        let back = before - 4 * (len - b) - 8;
        for (k, v) in s.glue[b..].iter_mut().enumerate() {
            let word = &keys[back + 4 * k..back + 4 * k + 4];
            *v = i32::from_be_bytes([word[0], word[1], word[2], word[3]]) >> 12;
        }
        vec![("plain", plain), ("carry", carry), ("opened", opened), ("tower", tower)]
    }

    /// [the ring record §4] The regions the mark is read on: 2, 3, 5, 64 and 257 sites (the ends with none, one and two strand mates, the far
    /// crowds reached), written and open places, and in the two longest a carried face at some open places (unresolved and not silent, so no mark
    /// there, each neighbour of a marked one), the 257 weighed by a domain.
    #[allow(clippy::type_complexity)]
    fn mark_regions() -> (Vec<Vec<usize>>, Vec<Vec<bool>>, Vec<Vec<Option<holonics::hnn::tower::field::Shares>>>, Vec<Option<usize>>) {
        let lengths = [2usize, 3, 5, 64, 257];
        let classes: Vec<Vec<usize>> = lengths.iter().map(|&n| (0..n).map(|t| (t * 37 + 11) % 120).collect()).collect();
        let open: Vec<Vec<bool>> = lengths.iter().map(|&n| (0..n).map(|t| t % 3 == 1 || t + 1 == n || (n > 5 && t % 7 == 2)).collect()).collect();
        let carried: Vec<Vec<Option<holonics::hnn::tower::field::Shares>>> = lengths
            .iter()
            .zip(&open)
            .map(|(&n, u)| if n < 64 { Vec::new() } else { (0..n).map(|t| (u[t] && t % 9 == 4).then(|| vec![((t * 13 % 120) as u32, 40_000u32), ((t * 29 % 120 + 1) as u32, 25_536u32)])).collect() })
            .collect();
        let domains = lengths.iter().zip(&open).map(|(&n, u)| (n == 257).then(|| 2 * u.iter().filter(|&&o| o).count())).collect();
        (classes, open, carried, domains)
    }

    /// [definition; agent-inferred, November 14, the ring record §4] **The field that reads twice on the card reads the host's bits** (needs the
    /// card): grown onto each of [`mark_cases`] ([`holonics::hnn::tower::field::FieldLearner::with_mark`]) with its strengths at their founding
    /// and at [`MARK_STRENGTHS`], read and returned on [`mark_regions`] through the host and through the card: every face, every covector entry
    /// (the strengths' among them, nonzero), the faces of a read that does not return, the training path's words with the opening's codes, the
    /// charts by stage and the logits with their echoes equal; at the founding every face is the field's before the growth on the card too, and
    /// off it some face moves.
    #[test]
    #[ignore = "needs the CUDA card; run alone with --include-ignored --test-threads=1"]
    fn the_field_that_reads_twice_on_the_card_reads_the_hosts_bits() {
        use holonics::hnn::tower::field::{FieldRealization, HostField, MARK_BASES};
        let (classes, open, carried, domains) = mark_regions();
        let regions: Vec<Region> = (0..classes.len()).map(|r| Region { classes: &classes[r], unresolved: &open[r], faces: &carried[r], locked: &[], echo: &[], domain: domains[r], port: None }).collect();
        let card = Card::open(0).expect("a CUDA card with the field's kernels built");
        let mut card_field = CardField::open(&card).unwrap();
        for (name, learner) in mark_cases() {
            let before = card_field.read_and_return(&learner.field, &regions).unwrap();
            let marked = learner.with_mark().unwrap();
            let l = marked.field.layout().clone();
            for strengths in [[0i32; MARK_BASES], MARK_STRENGTHS] {
                let mut field = marked.field.clone();
                field.theta[l.mark..l.mark + MARK_BASES].copy_from_slice(&strengths);
                let (host_faces, host_g) = field.read_and_return(&regions).unwrap();
                let (card_faces, card_g) = card_field.read_and_return(&field, &regions).unwrap();
                assert_eq!(host_faces, card_faces, "{name} at {strengths:?}: the faces");
                let unequal: Vec<usize> = (0..host_g.len()).filter(|&i| host_g.get(i) != card_g.get(i)).collect();
                let family = |i: usize| field.families_all().iter().position(|&(s, n, _)| (s..s + n).contains(&i));
                assert!(unequal.is_empty() && host_g.len() == card_g.len(), "{name} at {strengths:?}: {} covector entries differ, the first at {:?} (its family {:?}; the strengths at {})", unequal.len(), unequal.first(), unequal.first().map(|&i| family(i)), l.mark);
                assert!(host_g[l.mark..l.mark + MARK_BASES].iter().all(|&v| v != 0), "{name} at {strengths:?}: every strength takes a covector");
                if strengths == [0; MARK_BASES] {
                    assert_eq!(card_faces, before.0, "{name}: founded at zero, every face is the field's before the growth");
                } else {
                    assert_ne!(card_faces, before.0, "{name}: off the founding some face moves");
                }
                assert_eq!(HostField.read_faces(&field, &regions).unwrap(), card_field.read_faces(&field, &regions).unwrap(), "{name} at {strengths:?}: a read that does not return");
                let (host_at, host_ng, host_codes) = HostField.read_and_return_opening(&field, &regions).unwrap();
                let (card_at, card_ng, card_codes) = card_field.read_and_return_opening(&field, &regions).unwrap();
                assert_eq!(host_at, card_at, "{name} at {strengths:?}: the training path's words");
                assert!(host_ng == card_ng && card_ng == card_g, "{name} at {strengths:?}: the training path's covector");
                assert_eq!(host_codes, card_codes, "{name} at {strengths:?}: the opening's codes");
                let (host_cf, host_charts) = HostField.read_tick_charts(&field, &regions).unwrap();
                let (card_cf, card_charts) = card_field.read_tick_charts(&field, &regions).unwrap();
                assert!(host_cf == card_cf && host_charts == card_charts, "{name} at {strengths:?}: the charts by stage");
                assert_eq!(HostField.read_logits(&field, &regions).unwrap(), card_field.read_logits(&field, &regions).unwrap(), "{name} at {strengths:?}: the logits and echoes");
                let open_sites: usize = regions.iter().map(|r| r.unresolved.iter().filter(|&&u| u).count()).sum();
                println!("MARK_PARITY field={name} strengths={strengths:?} open_sites={open_sites} covector_entries={} strengths_covector={:?} faces_equal=1 covector_equal=1", card_g.len(), &card_g[l.mark..l.mark + MARK_BASES]);
            }
        }
    }

    /// [definition; agent-inferred, November 14, the ring record §4] **A marked learner's sections on the card read the host's bits** (needs the
    /// card): each of [`mark_cases`] and the lettered learner grown to read twice, its strengths at [`MARK_STRENGTHS`], takes two sections on
    /// [`mark_regions`] (the lettered one on its own stretches) through the host ([`holonics::hnn::tower::field::HostField`]) and through the card:
    /// the receipts and the learner's whole state (the material, the strengths among it, and the moments) equal after each.
    #[test]
    #[ignore = "needs the CUDA card; run alone with --include-ignored --test-threads=1"]
    fn a_marked_learners_sections_on_the_card_read_the_hosts_bits() {
        use holonics::hnn::tower::field::{HostField, MARK_BASES};
        let (classes, open, carried, domains) = mark_regions();
        let regions: Vec<Region> = (0..classes.len()).map(|r| Region { classes: &classes[r], unresolved: &open[r], faces: &carried[r], locked: &[], echo: &[], domain: domains[r], port: None }).collect();
        let (lettered, _, _, _, lclasses, lopen, ldomains) = lettered_case();
        let lregions: Vec<Region> = lclasses.iter().zip(&lopen).zip(&ldomains).map(|((c, u), &dom)| Region { classes: c, unresolved: u, faces: &[], locked: &[], echo: &[], domain: dom, port: None }).collect();
        let card = Card::open(0).expect("a CUDA card with the field's kernels built");
        let mut card_field = CardField::open(&card).unwrap();
        let mut cases = mark_cases();
        cases.push(("lettered", lettered));
        for (name, learner) in cases {
            let mut marked = learner.with_mark().unwrap();
            let l = marked.field.layout().clone();
            marked.field.theta[l.mark..l.mark + MARK_BASES].copy_from_slice(&MARK_STRENGTHS);
            let on = if name == "lettered" { &lregions } else { &regions };
            let (mut on_host, mut on_card) = (marked.clone(), marked);
            for section in 0..2 {
                let host_receipt = on_host.section_realized(on, &mut HostField).unwrap();
                let card_receipt = on_card.section_realized(on, &mut card_field).unwrap();
                assert_eq!(host_receipt, card_receipt, "{name}: section {section}'s receipt");
                assert!(host_receipt.deposited, "{name}: section {section} deposits");
                assert!(on_host.to_text() == on_card.to_text(), "{name}: the learner's state after section {section} differs between the host and the card");
                println!("MARK_SECTION field={name} section={section} code_before={} strengths={:?} state_equal=1", card_receipt.code_before, &on_card.field.theta[l.mark..l.mark + MARK_BASES]);
            }
        }
    }

    /// [measurement; the ring record §4] **The two reads' time on the card against one read** (needs the card): the opened learner's field before
    /// the growth and grown to read twice at [`MARK_STRENGTHS`], each read and returned (a training read) and read without a return on one batch of 32 regions of 257
    /// sites (the open places of [`mark_regions`]'s longest), timed inside one hold as control, marked, control, marked, control after a warm read
    /// of each; the control's spread is the read's resolution.
    #[test]
    #[ignore = "needs the CUDA card; run alone with --include-ignored --test-threads=1"]
    fn the_field_that_reads_twice_times_its_two_reads_on_the_card() {
        use holonics::hnn::tower::field::MARK_BASES;
        let (classes, open, _, _) = mark_regions();
        let regions: Vec<Region> = (0..32).map(|_| Region { classes: &classes[4], unresolved: &open[4], faces: &[], locked: &[], echo: &[], domain: None, port: None }).collect();
        let (_, learner) = mark_cases().into_iter().find(|(n, _)| *n == "opened").unwrap();
        let plain = learner.field.clone();
        let mut marked = learner.with_mark().unwrap().field;
        let l = marked.layout().clone();
        marked.theta[l.mark..l.mark + MARK_BASES].copy_from_slice(&MARK_STRENGTHS);
        let card = Card::open(0).expect("a CUDA card with the field's kernels built");
        let mut card_field = CardField::open(&card).unwrap();
        let sites = regions.len() * classes[4].len();
        let open_sites = regions.len() * open[4].iter().filter(|&&u| u).count();
        // A training read (read and return) and a read that does not return, each in its own interleaved hold.
        for returning in [true, false] {
            let mut timed = |field: &Field| -> u128 {
                let started = Instant::now();
                if returning {
                    card_field.read_and_return(field, &regions).unwrap();
                } else {
                    card_field.read_faces(field, &regions).unwrap();
                }
                started.elapsed().as_micros()
            };
            timed(&plain);
            timed(&marked);
            let reads: Vec<(&str, u128)> = [("control", &plain), ("marked", &marked), ("control", &plain), ("marked", &marked), ("control", &plain)].into_iter().map(|(n, f)| (n, timed(f))).collect();
            println!("MARK_TIMES returning={} sites={sites} open_sites={open_sites} reads_us={}", u8::from(returning), reads.iter().map(|(n, us)| format!("{n}:{us}")).collect::<Vec<_>>().join(","));
        }
    }
}

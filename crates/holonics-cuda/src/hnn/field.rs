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

use holonics::hnn::tower::field::{landmarks_of, Field, FieldDeclaration, FieldRealization, Region, SHARE_BITS, STATE_BITS};
use holonics::hnn::tower::{TowerError, TowerFace};

use crate::cuda::{Dim3, Module};
use crate::hnn::card::{Card, CardBuffer};
use crate::hnn::DeviceError;

const IMAGE: &[u8] = include_bytes!(concat!(env!("OUT_DIR"), "/field.ptx"));
const THREADS: u32 = 256;
/// The widest span the contact's lanes carry (a lane an entry of the span).
const CONTACT_SPAN: u32 = 32;
/// The series row's carrier, in limbs of 64 bits: at least five (a term's product with a wide value),
/// at most eight (`field_contact_l5` … `field_contact_l8`).
const MIN_LIMBS: usize = 5;
const MAX_LIMBS: usize = 8;
/// The most crowds a receiver hears, one lane each (`MAX_CROWD_SLOTS` in `kernels/field.cu`).
const MAX_CROWD_SLOTS: usize = 32;
/// The sites a thread of a covector sum takes (`OUTER_TILE` in `kernels/field.cu`).
const OUTER_TILE: u64 = 64;
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
    limbs: u32,
    slots: u32,
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
    e: u64,
    y: u64,
    pa: u64,
    pb: u64,
    pc: u64,
    bits: u64,
    face: u64,
    hold: u64,
    holdm: u64,
    sw: u64,
    sv: u64,
    sc: u64,
    ce: u64,
    lifts: u64,
    cv: u64,
    cw: u64,
}

/// A kernel argument: the address of a value the launch copies.
fn arg<T>(v: &mut T) -> *mut c_void {
    (v as *mut T).cast()
}

/// [definition; agent-inferred, November 1] **The crowds a receiver of a region of `sites` hears**
/// (the dispersing field's §14.10, the host's `crowd_ranges`): two an octave `level ≥ 2` with
/// `2^level < sites`, one on each side.
pub fn crowd_slots(sites: usize) -> usize {
    (2..usize::BITS).take_while(|&level| (1usize << level) < sites).count() * 2
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
}

/// One tick's carriers on the card.
struct Tick<'c> {
    read: CardBuffer<'c, i32>,
    scale: CardBuffer<'c, i128>,
    /// The word and the value, `[t][2·2M]`.
    qkv: CardBuffer<'c, i64>,
    qf: CardBuffer<'c, i64>,
    vf: CardBuffer<'c, i64>,
    /// The framed word's powers `[h][t]`, the ratios `field_unit` reads it as.
    qscale: CardBuffer<'c, i128>,
    /// The resonance classes `[h][t]`, each region's class offsets `[h][r][2^b + 1]` and members
    /// `[h][t]` (`field_classes`).
    cls: CardBuffer<'c, u32>,
    class_off: CardBuffer<'c, u32>,
    members: CardBuffer<'c, u32>,
    e: CardBuffer<'c, u64>,
    /// The holds `[h][t]` on `2^(−40)` and the mode that sets each (`hold` in `kernels/field.cu`), each
    /// head's prefix sums of the definite sites' unit words and values `[h][row][span]` and their counts
    /// `[h][row]`, and each receiver's crowd shares `[h][t][slots]` (`row = site + region`, a region's
    /// `S + 1` rows).
    hold: CardBuffer<'c, u64>,
    holdm: CardBuffer<'c, u32>,
    sw: CardBuffer<'c, i128>,
    sv: CardBuffer<'c, i128>,
    sc: CardBuffer<'c, u64>,
    ce: CardBuffer<'c, u64>,
    y: CardBuffer<'c, i64>,
    read2: CardBuffer<'c, i32>,
    scale2: CardBuffer<'c, i128>,
    pa: CardBuffer<'c, i64>,
    pb: CardBuffer<'c, i64>,
    pc: CardBuffer<'c, i64>,
    /// The tick's carrier width: the binary length of its largest unit word.
    bits: CardBuffer<'c, u32>,
}

/// What a profiled call's time is charged to.
#[derive(Clone, Copy)]
enum Kind {
    Copy,
    Alloc,
}

/// [agent-inferred, November 1] A declared reading (`CardField::profile`): every launch timed alone,
/// the card synchronized before and after it, by entry; every transfer and allocation timed after the
/// card's stream has drained, so a run's wall time splits into kernels, copies, allocations and the
/// host's own work. It moves nothing the field computes.
#[derive(Clone, Debug, Default)]
pub struct FieldProfile {
    pub kernels: std::collections::BTreeMap<&'static str, (u64, u128)>,
    pub copies: (u64, u128),
    pub allocations: (u64, u128),
}

/// **The field on the card**: its image, the card it runs on and the octets a batch may take.
pub struct CardField<'c> {
    card: &'c Card,
    module: Module,
    budget: u64,
    times: FieldTimes,
    profile: Option<std::cell::RefCell<FieldProfile>>,
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
        Ok(Self { card, module, budget, times: FieldTimes::default(), profile: None })
    }

    /// The octets a batch's weight and contact stores may take.
    pub fn budget(&self) -> u64 {
        self.budget
    }

    pub fn times(&self) -> FieldTimes {
        self.times
    }

    /// Time every launch, transfer and allocation from here on ([`FieldProfile`]).
    pub fn profile(&mut self) {
        self.profile = Some(Default::default());
    }

    /// The profile read so far, when profiled.
    pub fn profiled(&self) -> Option<FieldProfile> {
        self.profile.as_ref().map(|p| p.borrow().clone())
    }

    /// A transfer or an allocation, timed after the stream drains when profiled.
    fn timed<T>(&self, kind: Kind, f: impl FnOnce() -> T) -> T {
        let Some(profile) = &self.profile else { return f() };
        let _ = self.card.synchronize();
        let started = Instant::now();
        let out = f();
        let ns = started.elapsed().as_nanos();
        let mut p = profile.borrow_mut();
        let slot = match kind {
            Kind::Copy => &mut p.copies,
            Kind::Alloc => &mut p.allocations,
        };
        slot.0 += 1;
        slot.1 += ns;
        out
    }

    fn launch(&self, entry: &'static str, grid: u32, block: u32, params: &mut [*mut c_void]) -> Result<()> {
        self.launch_shared(entry, grid, block, 0, params)
    }

    /// A launch with `shared` octets of the block's dynamic shared memory.
    fn launch_shared(&self, entry: &'static str, grid: u32, block: u32, shared: u32, params: &mut [*mut c_void]) -> Result<()> {
        self.card.current().map_err(device)?;
        let function = self.module.function(entry).map_err(|e| device(e.into()))?;
        let started = match &self.profile {
            Some(_) => {
                self.card.synchronize().map_err(device)?;
                Some(Instant::now())
            }
            None => None,
        };
        function.launch_on_shared(self.card.stream(), Dim3::x(grid.max(1)), Dim3 { x: block, y: 1, z: 1 }, shared, params).map_err(|e| device(e.into()))?;
        if let (Some(profile), Some(started)) = (&self.profile, started) {
            self.card.synchronize().map_err(device)?;
            let mut p = profile.borrow_mut();
            let slot = p.kernels.entry(entry).or_insert((0, 0));
            slot.0 += 1;
            slot.1 += started.elapsed().as_nanos();
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


    /// Each region's faces (and their logits when `logits`) and, when `returning`, the covector
    /// over the regions; with `keep`, the still heads' last-tick weight rows of those sites of the one
    /// region read ([`FieldRealization::read_landmarks`]).
    #[allow(clippy::type_complexity)]
    fn run(&mut self, field: &Field, regions: &[Region], returning: bool, logits: bool, keep: Option<&[usize]>) -> Result<(Vec<Vec<Option<TowerFace>>>, Vec<Vec<Option<Vec<i64>>>>, Vec<i128>, Rows)> {
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
        }
        let card = self.card;
        let started = Instant::now();
        let l = field.layout();
        let theta = self.timed(Kind::Copy, || card.upload(&field.theta)).map_err(device)?;
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
        let decay_card = self.timed(Kind::Copy, || card.upload(&decay)).map_err(device)?;
        let roots: Vec<u64> = field.exponential().roots().iter().map(|&r| u64::try_from(r).map_err(|_| TowerError::Refused("the exponential's roots lie below 2^63"))).collect::<Result<_>>()?;
        let phasor = self.timed(Kind::Copy, || card.upload(&phasor)).map_err(device)?;
        let ring_off = self.timed(Kind::Copy, || card.upload(&ring_off)).map_err(device)?;
        let ring_n = self.timed(Kind::Copy, || card.upload(&ring_n)).map_err(device)?;
        let roots_card = self.timed(Kind::Copy, || card.upload(&roots)).map_err(device)?;
        if 2 * d.modes as u32 > CONTACT_SPAN {
            return Err(TowerError::Refused("the card's contact carries a span of at most 32 entries (16 modes a head)"));
        }
        // The series row's carrier in limbs of 64 bits, read from the declaration's own bounds
        // (`FieldDeclaration::row_bits`, §14.11), and the crowds' slots a receiver keeps (two an
        // octave `2^level < reach`, from the octave of four).
        let limbs = (d.row_bits() as usize).div_ceil(64).max(MIN_LIMBS);
        if limbs > MAX_LIMBS {
            return Err(TowerError::Refused("the declaration's series row is past the card's widest carrier (512 bits)"));
        }
        let slots = crowd_slots(d.reach);
        if slots > MAX_CROWD_SLOTS {
            return Err(TowerError::Refused("the declaration's reach holds more crowds than a warp keeps (32)"));
        }
        // The exponential's resident face: `2^digits` words, held beside the batches and counted
        // against the same budget.
        let face_octets = Some(roots.len()).filter(|&digits| digits < 61).map(|digits| 8u64 << digits).filter(|&o| o < self.budget).ok_or(TowerError::Refused("the exponential's resident face passes the card's batch budget"))?;
        let face = self.timed(Kind::Alloc, || card.alloc::<u64>(1usize << roots.len())).map_err(device)?;
        let met = self.timed(Kind::Alloc, || card.zeroed::<u64>(1)).map_err(device)?;
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
            beta: d.score_shift(),
            ctrits: d.class_trits() as u32,
            nclasses: d.classes() as u32,
            dsbits: d.contact_return_bits(),
            m: m as u32,
            m2: m2 as u32,
            span: (2 * n) as u32,
            digits: roots.len() as u32,
            limbs: limbs as u32,
            slots: slots as u32,
            ln2_lo: ln2 as u64,
            ln2_hi: (ln2 >> 64) as u64,
            theta: theta.device_ptr(),
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
            rb: reach(l.b, f * dw),
            rw: reach(l.w, dw * f),
            rread: reach(l.read, a * dw),
            phasor: phasor.device_ptr(),
            ring_off: ring_off.device_ptr(),
            ring_n: ring_n.device_ptr(),
            decay: decay_card.device_ptr(),
            dreach: d.reach as u64,
            roots: roots_card.device_ptr(),
            met: met.device_ptr(),
            ..Words::default()
        };
        // The exponential's resident face, read once by its own loop on the card.
        let mut face_ptr = face.device_ptr();
        self.launch("field_exponential", Self::cells(1u64 << roots.len()), THREADS, &mut [arg(&mut words), arg(&mut face_ptr)])?;
        words.face = face_ptr;
        let g = if returning { Some(self.timed(Kind::Alloc, || card.zeroed::<i128>(l.len)).map_err(device)?) } else { None };
        // The batches: whole regions in order, each batch's every allocation within the budget.
        // A landmark read stores one tick's weights beside a read's carriers.
        let octets = |sites: usize| region_octets(&d, returning, sites) + if keep.is_some() { 8 * (heads * sites * sites) as u64 } else { 0 };
        let lengths: Vec<usize> = regions.iter().map(|r| r.classes.len()).collect();
        let batches = batches(&lengths, &octets, self.budget - face_octets)?;
        if keep.is_some() && (regions.len() != 1 || returning) {
            return Err(TowerError::Refused("the weight rows are read from one region's forward"));
        }
        let mut faces: Vec<Vec<Option<TowerFace>>> = Vec::with_capacity(regions.len());
        let mut read_logits: Vec<Vec<Option<Vec<i64>>>> = Vec::new();
        let mut rows = Rows::new();
        for batch in batches {
            if batch.is_empty() {
                continue;
            }
            let peak = lengths[batch.clone()].iter().map(|&n| octets(n)).sum::<u64>();
            self.times.peak_store = self.times.peak_store.max(peak);
            self.times.batches += 1;
            let (f, z, r) = self.batch(field, &regions[batch], &mut words, g.as_ref(), logits, keep)?;
            faces.extend(f);
            read_logits.extend(z);
            rows.extend(r);
        }
        let g = match g {
            Some(g) => self.timed(Kind::Copy, || card.fetch(&g)).map_err(device)?,
            None => Vec::new(),
        };
        let met = self.timed(Kind::Copy, || card.fetch(&met)).map_err(device)?[0] as u128;
        if keep.is_some() {
            // A landmark read is a reading of a release's last state, counted apart.
            self.times.landmarks += 1;
            self.times.landmark_ns += started.elapsed().as_nanos();
            return Ok((faces, read_logits, g, rows));
        }
        self.times.pairs += met;
        if returning {
            self.times.returns += 1;
            self.times.return_ns += started.elapsed().as_nanos();
        } else {
            self.times.reads += 1;
            self.times.read_ns += started.elapsed().as_nanos();
        }
        Ok((faces, read_logits, g, rows))
    }

    fn tick(&self, sites: usize, pairs: usize, regions: usize, field: &Field, stored: bool) -> Result<Tick<'c>> {
        let d = field.declaration;
        let rows = sites + regions;
        let slots = crowd_slots(d.reach);
        let (dw, m2, f, heads, span) = (d.width, 2 * d.complex(), d.contacts, d.heads, 2 * d.modes);
        let classes = d.classes();
        let card = self.card;
        let alloc64 = |len: usize| self.timed(Kind::Alloc, || card.alloc::<i64>(len.max(1))).map_err(device);
        let alloc32 = |len: usize| self.timed(Kind::Alloc, || card.alloc::<u32>(len.max(1))).map_err(device);
        Ok(Tick {
            read: self.timed(Kind::Alloc, || card.alloc::<i32>((sites * dw).max(1))).map_err(device)?,
            scale: self.timed(Kind::Alloc, || card.alloc::<i128>(sites.max(1))).map_err(device)?,
            qkv: alloc64(sites * 2 * m2)?,
            qf: alloc64(heads * sites * span)?,
            vf: alloc64(heads * sites * span)?,
            qscale: self.timed(Kind::Alloc, || card.alloc::<i128>((heads * sites).max(1))).map_err(device)?,
            cls: alloc32(heads * sites)?,
            class_off: alloc32(heads * regions * (2 * classes + 1))?,
            members: alloc32(heads * sites)?,
            // The weights are kept only for a return's reverse or the rows a landmark reads.
            e: self.timed(Kind::Alloc, || card.alloc::<u64>(if stored { (heads * pairs).max(1) } else { 1 })).map_err(device)?,
            hold: self.timed(Kind::Alloc, || card.alloc::<u64>((heads * sites).max(1))).map_err(device)?,
            holdm: alloc32(heads * sites)?,
            sw: self.timed(Kind::Alloc, || card.alloc::<i128>((heads * rows * span).max(1))).map_err(device)?,
            sv: self.timed(Kind::Alloc, || card.alloc::<i128>((heads * rows * span).max(1))).map_err(device)?,
            sc: self.timed(Kind::Alloc, || card.alloc::<u64>((heads * rows).max(1))).map_err(device)?,
            ce: self.timed(Kind::Alloc, || card.alloc::<u64>(if stored { (heads * sites * slots).max(1) } else { 1 })).map_err(device)?,
            y: alloc64(sites * m2)?,
            read2: self.timed(Kind::Alloc, || card.alloc::<i32>((sites * dw).max(1))).map_err(device)?,
            scale2: self.timed(Kind::Alloc, || card.alloc::<i128>(sites.max(1))).map_err(device)?,
            pa: alloc64(sites * f)?,
            pb: alloc64(sites * f)?,
            pc: alloc64(sites * f)?,
            bits: self.timed(Kind::Alloc, || card.zeroed::<u32>(1)).map_err(device)?,
        })
    }

    /// One batch of regions: the forward, each unresolved site's face (and its logits when
    /// `logits`), when `g` is given the reverse added into it, and with `keep` the still heads'
    /// last-tick weight rows of those sites (the batch's one region).
    #[allow(clippy::type_complexity)]
    fn batch(&self, field: &Field, regions: &[Region], words: &mut Words, g: Option<&CardBuffer<'c, i128>>, logits: bool, keep: Option<&[usize]>) -> Result<(Vec<Vec<Option<TowerFace>>>, Vec<Vec<Option<Vec<i64>>>>, Rows)> {
        let card = self.card;
        let d = field.declaration;
        let (dw, m, n, f, a, heads) = (d.width, d.complex(), d.modes, d.contacts, d.alphabet, d.heads);
        let m2 = 2 * m;
        let span = 2 * n;
        // The batch's sites, region by region, and the carried mixtures as one list a site.
        let mut site_region = Vec::new();
        let mut site_pos = Vec::new();
        let mut region_off = vec![0u32];
        let mut region_eoff = Vec::new();
        let mut classes = Vec::new();
        let mut unresolved = Vec::new();
        // A definite site (§14.1): known (resolved, carrying no mixture) or locked (a foil).
        let mut definite = Vec::new();
        let (mut mix_off, mut mix_class, mut mix_share) = (vec![0u32], Vec::new(), Vec::new());
        let mut pairs = 0usize;
        for (r, region) in regions.iter().enumerate() {
            let s = region.classes.len();
            region_eoff.push(pairs as u64);
            pairs += s * s;
            for t in 0..s {
                site_region.push(r as u32);
                site_pos.push(t as u32);
                classes.push(region.classes[t] as u32);
                unresolved.push(u8::from(region.unresolved[t]));
                let carried = region.faces.get(t).and_then(Option::as_ref).is_some();
                definite.push(u8::from((!region.unresolved[t] && !carried) || region.locked.get(t).copied().unwrap_or(false)));
                for &(c, w) in region.faces.get(t).and_then(Option::as_ref).into_iter().flatten() {
                    mix_class.push(c);
                    mix_share.push(w);
                }
                mix_off.push(mix_class.len() as u32);
            }
            region_off.push(site_region.len() as u32);
        }
        let sites = site_region.len();
        // A batch with no carried site still uploads one word, so every buffer has an address.
        let (mix_class_up, mix_share_up) = if mix_class.is_empty() { (vec![0u32], vec![0u32]) } else { (mix_class.clone(), mix_share.clone()) };
        let site_region_c = self.timed(Kind::Copy, || card.upload(&site_region)).map_err(device)?;
        let site_pos_c = self.timed(Kind::Copy, || card.upload(&site_pos)).map_err(device)?;
        let region_off_c = self.timed(Kind::Copy, || card.upload(&region_off)).map_err(device)?;
        let region_eoff_c = self.timed(Kind::Copy, || card.upload(&region_eoff)).map_err(device)?;
        let classes_c = self.timed(Kind::Copy, || card.upload(&classes)).map_err(device)?;
        let unresolved_c = self.timed(Kind::Copy, || card.upload(&unresolved)).map_err(device)?;
        let definite_c = self.timed(Kind::Copy, || card.upload(&definite)).map_err(device)?;
        let mix_off_c = self.timed(Kind::Copy, || card.upload(&mix_off)).map_err(device)?;
        let mix_class_c = self.timed(Kind::Copy, || card.upload(&mix_class_up)).map_err(device)?;
        let mix_share_c = self.timed(Kind::Copy, || card.upload(&mix_share_up)).map_err(device)?;
        let status = self.timed(Kind::Alloc, || card.zeroed::<u32>(1)).map_err(device)?;
        let x = self.timed(Kind::Alloc, || card.alloc::<i64>(sites * dw)).map_err(device)?;
        words.t = sites as u32;
        words.r = regions.len() as u32;
        words.pairs = pairs as u64;
        words.site_region = site_region_c.device_ptr();
        words.site_pos = site_pos_c.device_ptr();
        words.region_off = region_off_c.device_ptr();
        words.region_eoff = region_eoff_c.device_ptr();
        words.classes = classes_c.device_ptr();
        words.unresolved = unresolved_c.device_ptr();
        words.definite = definite_c.device_ptr();
        words.mix_off = mix_off_c.device_ptr();
        words.mix_class = mix_class_c.device_ptr();
        words.mix_share = mix_share_c.device_ptr();
        words.status = status.device_ptr();
        words.x = x.device_ptr();
        let returning = g.is_some();
        // The weights are stored for a return's reverse, or for the rows `keep` reads.
        let stored = returning || keep.is_some();
        let ticks: Vec<Tick> = (0..if returning { d.ticks } else { 1 }).map(|_| self.tick(sites, pairs, regions.len(), field, stored)).collect::<Result<_>>()?;
        let set = |w: &mut Words, tick: &Tick| {
            w.qkv = tick.qkv.device_ptr();
            w.qf = tick.qf.device_ptr();
            w.vf = tick.vf.device_ptr();
            w.cls = tick.cls.device_ptr();
            w.class_off = tick.class_off.device_ptr();
            w.members = tick.members.device_ptr();
            w.e = tick.e.device_ptr();
            w.hold = tick.hold.device_ptr();
            w.holdm = tick.holdm.device_ptr();
            w.sw = tick.sw.device_ptr();
            w.sv = tick.sv.device_ptr();
            w.sc = tick.sc.device_ptr();
            w.ce = tick.ce.device_ptr();
            w.y = tick.y.device_ptr();
            w.pa = tick.pa.device_ptr();
            w.pb = tick.pb.device_ptr();
            w.pc = tick.pc.device_ptr();
            w.bits = tick.bits.device_ptr();
        };
        let t64 = sites as u64;
        let buckets = 8 * d.classes() as u32;
        self.launch("field_open", Self::cells(t64 * dw as u64), THREADS, &mut [arg(words)])?;
        for k in 0..d.ticks {
            let tick = &ticks[if returning { k } else { 0 }];
            set(words, tick);
            self.chart(words, words.x, &tick.read, &tick.scale, false)?;
            for (part, weight, bias, wmax) in [(0usize, words.q, words.q_bias, words.rq), (1, words.v, words.v_bias, words.rv)] {
                let out = tick.qkv.device_ptr() + (part * m2 * 8) as u64;
                self.affine("field_affine_x32", words, weight, bias, wmax, m2, dw, tick.read.device_ptr(), dw, out, 2 * m2, 0, false)?;
            }
            card.zero_octets(&tick.bits, 0, 4).map_err(device)?;
            self.launch_shared("field_classes", (heads * regions.len()).clamp(1, 1 << 20) as u32, 32, buckets, &mut [arg(words)])?;
            self.launch("field_frame", Self::cells((heads * sites * n) as u64), THREADS, &mut [arg(words)])?;
            let mut qs = tick.qscale.device_ptr();
            self.launch("field_unit", Self::warps((heads * sites) as u64), THREADS, &mut [arg(words), arg(&mut qs)])?;
            // The definite sites' prefix sums (§14.10), read by the contact's crowds.
            self.launch("field_sums", Self::cells((heads * regions.len() * (2 * span + 1)) as u64), THREADS, &mut [arg(words)])?;
            let mut store = u32::from(stored);
            if keep.is_some() && k + 1 == d.ticks {
                // The last tick's rows are read whole: the entries outside its support read zero.
                card.zero_octets(&tick.e, 0, 8 * heads * pairs).map_err(device)?;
            }
            let contact = match words.limbs {
                5 => "field_contact_l5",
                6 => "field_contact_l6",
                7 => "field_contact_l7",
                _ => "field_contact_l8",
            };
            self.launch(contact, Self::warps((heads * sites) as u64), THREADS, &mut [arg(words), arg(&mut store)])?;
            self.affine("field_affine_x64", words, words.out, words.out_bias, words.rout, dw, m2, tick.y.device_ptr(), m2, 0, dw, words.x, false)?;
            self.chart(words, words.x, &tick.read2, &tick.scale2, false)?;
            self.affine("field_affine_x32", words, words.wa, words.a_bias, words.ra, f, dw, tick.read2.device_ptr(), dw, tick.pa.device_ptr(), f, 0, false)?;
            self.affine("field_affine_x32", words, words.wb, words.b_bias, words.rb, f, dw, tick.read2.device_ptr(), dw, tick.pb.device_ptr(), f, 0, false)?;
            self.launch("field_pair", Self::cells((sites * f) as u64), THREADS, &mut [arg(words)])?;
            self.affine("field_affine_x64", words, words.w, words.w_bias, words.rw, dw, f, tick.pc.device_ptr(), f, 0, dw, words.x, false)?;
        }
        // The faces at the unresolved sites.
        let fread = self.timed(Kind::Alloc, || card.alloc::<i32>(sites * dw)).map_err(device)?;
        let fscale = self.timed(Kind::Alloc, || card.zeroed::<i128>(sites)).map_err(device)?;
        let z = self.timed(Kind::Alloc, || card.alloc::<i64>(sites * a)).map_err(device)?;
        let masses = self.timed(Kind::Alloc, || card.alloc::<u64>(sites * a)).map_err(device)?;
        let totals = self.timed(Kind::Alloc, || card.zeroed::<i128>(sites)).map_err(device)?;
        self.chart(words, words.x, &fread, &fscale, true)?;
        self.affine("field_affine_x32", words, words.read, words.read_bias, words.rread, a, dw, fread.device_ptr(), dw, z.device_ptr(), a, 0, true)?;
        let (mut zp, mut mp, mut tp) = (z.device_ptr(), masses.device_ptr(), totals.device_ptr());
        self.launch("field_face", Self::warps(t64), THREADS, &mut [arg(words), arg(&mut zp), arg(&mut mp), arg(&mut tp)])?;
        if let Some(g) = g {
            self.reverse(field, words, &ticks, g, &fread, &fscale, &masses, &totals, &classes, &unresolved, &site_pos, &mix_off, &mix_class, &mix_share, sites, pairs)?;
        }
        self.status(&status)?;
        let masses = self.timed(Kind::Copy, || card.fetch(&masses)).map_err(device)?;
        let totals = self.timed(Kind::Copy, || card.fetch(&totals)).map_err(device)?;
        let zs = if logits { self.timed(Kind::Copy, || card.fetch(&z)).map_err(device)? } else { Vec::new() };
        // The kept rows: each named site's row of each still head at the last tick, with its mass.
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
        let (mut out, mut out_z) = (Vec::with_capacity(regions.len()), Vec::new());
        for r in 0..regions.len() {
            let span = region_off[r] as usize..region_off[r + 1] as usize;
            out.push(span.clone().map(|t| (unresolved[t] != 0).then(|| TowerFace { masses: masses[t * a..(t + 1) * a].iter().map(|&v| v as u128).collect(), total: totals[t] as u128 })).collect());
            if logits {
                out_z.push(span.map(|t| (unresolved[t] != 0).then(|| zs[t * a..(t + 1) * a].to_vec())).collect());
            }
        }
        Ok((out, out_z, rows))
    }

    fn chart(&self, words: &mut Words, x: u64, read: &CardBuffer<'c, i32>, scale: &CardBuffer<'c, i128>, only_unresolved: bool) -> Result<()> {
        let (mut x, mut rp, mut sp, mut u) = (x, read.device_ptr(), scale.device_ptr(), u32::from(only_unresolved));
        self.launch("field_chart", Self::warps(words.t as u64), THREADS, &mut [arg(words), arg(&mut x), arg(&mut rp), arg(&mut sp), arg(&mut u)])
    }

    #[allow(clippy::too_many_arguments)]
    fn affine(&self, entry: &'static str, words: &mut Words, weight: u64, bias: u64, wmax: u64, rows: usize, cols: usize, x: u64, x_stride: usize, out: u64, out_stride: usize, add: u64, only_unresolved: bool) -> Result<()> {
        let (mut weight, mut bias, mut wmax, mut rows32, mut cols32) = (weight, bias, wmax, rows as u32, cols as u32);
        let (mut x, mut xs, mut out, mut os, mut add, mut u) = (x, x_stride as u64, out, out_stride as u64, add, u32::from(only_unresolved));
        let cells = words.t as u64 * rows as u64;
        self.launch(entry, Self::cells(cells), THREADS, &mut [arg(words), arg(&mut weight), arg(&mut bias), arg(&mut wmax), arg(&mut rows32), arg(&mut cols32), arg(&mut x), arg(&mut xs), arg(&mut out), arg(&mut os), arg(&mut add), arg(&mut u)])
    }

    #[allow(clippy::too_many_arguments)]
    fn transposed(&self, words: &mut Words, weight: u64, rows: usize, cols: usize, y: u64, y_stride: usize, out: u64, accumulate: bool, only_unresolved: bool) -> Result<()> {
        let (mut weight, mut rows32, mut cols32, mut y, mut ys, mut out, mut acc, mut u) = (weight, rows as u32, cols as u32, y, y_stride as u64, out, u32::from(accumulate), u32::from(only_unresolved));
        self.launch("field_transposed", Self::cells(words.t as u64 * cols as u64), THREADS, &mut [arg(words), arg(&mut weight), arg(&mut rows32), arg(&mut cols32), arg(&mut y), arg(&mut ys), arg(&mut out), arg(&mut acc), arg(&mut u)])
    }

    /// A family's covector `g[at..] += Σ_t y_t ⊗ x_t` (or the bias's `Σ_t y_t` when `x` is zero), with
    /// the host's per-region refusal of its carrier when `x` is given.
    #[allow(clippy::too_many_arguments)]
    fn outer(&self, words: &mut Words, g: &CardBuffer<'c, i128>, at: u64, rows: usize, cols: usize, y: u64, y_stride: usize, x: u64, x_stride: usize, x64: bool, only_unresolved: bool) -> Result<()> {
        let (mut gp, mut at, mut rows32, mut cols32, mut y, mut ys, mut x, mut xs, mut u) = (g.device_ptr(), at, rows as u32, cols as u32, y, y_stride as u64, x, x_stride as u64, u32::from(only_unresolved));
        if x != 0 {
            let entry = if x64 { "field_outer_bound_x64" } else { "field_outer_bound_x32" };
            self.launch(entry, words.r, THREADS, &mut [arg(words), arg(&mut rows32), arg(&mut cols32), arg(&mut y), arg(&mut ys), arg(&mut x), arg(&mut xs), arg(&mut u)])?;
        }
        let entries = rows as u64 * if x != 0 { cols as u64 } else { 1 };
        let entry = if x64 { "field_outer_x64" } else { "field_outer_x32" };
        self.launch(entry, Self::cells(entries * (words.t as u64).div_ceil(OUTER_TILE)), THREADS, &mut [arg(words), arg(&mut gp), arg(&mut at), arg(&mut rows32), arg(&mut cols32), arg(&mut y), arg(&mut ys), arg(&mut x), arg(&mut xs), arg(&mut u)])
    }

    fn ratio_adjoint(&self, words: &mut Words, read: u64, scale: u64, cov: u64, base: u64, dst: u64, only_unresolved: bool) -> Result<()> {
        let (mut read, mut scale, mut cov, mut base, mut dst, mut u) = (read, scale, cov, base, dst, u32::from(only_unresolved));
        self.launch("field_ratio_adjoint", Self::warps(words.t as u64), THREADS, &mut [arg(words), arg(&mut read), arg(&mut scale), arg(&mut cov), arg(&mut base), arg(&mut dst), arg(&mut u)])
    }

    #[allow(clippy::too_many_arguments)]
    fn reverse(&self, field: &Field, words: &mut Words, ticks: &[Tick<'c>], g: &CardBuffer<'c, i128>, fread: &CardBuffer<'c, i32>, fscale: &CardBuffer<'c, i128>, masses: &CardBuffer<'c, u64>, totals: &CardBuffer<'c, i128>, classes: &[u32], unresolved: &[u8], site_pos: &[u32], mix_off: &[u32], mix_class: &[u32], mix_share: &[u32], sites: usize, pairs: usize) -> Result<()> {
        let card = self.card;
        let d = field.declaration;
        let (dw, m, n, f, a, heads) = (d.width, d.complex(), d.modes, d.contacts, d.alphabet, d.heads);
        let (m2, span) = (2 * m, 2 * n);
        let alloc64 = |len: usize| self.timed(Kind::Alloc, || card.alloc::<i64>(len.max(1))).map_err(device);
        let dz = alloc64(sites * a)?;
        let dx = alloc64(sites * dw)?;
        let dr = alloc64(sites * dw)?;
        let dc = alloc64(sites * f)?;
        let da = alloc64(sites * f)?;
        let db = alloc64(sites * f)?;
        let ra = alloc64(sites * dw)?;
        let rb = alloc64(sites * dw)?;
        let dmid = alloc64(sites * dw)?;
        let dy = alloc64(sites * m2)?;
        let dyh = alloc64(heads * sites * span)?;
        let dq = alloc64(sites * m2)?;
        let dv = alloc64(sites * m2)?;
        let ds = self.timed(Kind::Alloc, || card.alloc::<i128>(pairs.max(1))).map_err(device)?;
        // The holds' covectors `[h][t]` (§14.2) and the crowds' difference arrays over the places
        // `[site + region][span]`, for the values and for the word (§14.10).
        let regions = words.r as usize;
        let rows = sites + regions;
        let lifts = self.timed(Kind::Alloc, || card.zeroed::<i128>((heads * sites).max(1))).map_err(device)?;
        let cv = self.timed(Kind::Alloc, || card.zeroed::<i128>((rows * span).max(1))).map_err(device)?;
        let cw = self.timed(Kind::Alloc, || card.zeroed::<i128>((rows * span).max(1))).map_err(device)?;
        words.lifts = lifts.device_ptr();
        words.cv = cv.device_ptr();
        words.cw = cw.device_ptr();
        // The face.
        let (mut mp, mut tp, mut dzp) = (masses.device_ptr(), totals.device_ptr(), dz.device_ptr());
        self.launch("field_face_covector", Self::cells((sites * a) as u64), THREADS, &mut [arg(words), arg(&mut mp), arg(&mut tp), arg(&mut dzp)])?;
        self.outer(words, g, words.read_bias, a, 0, dz.device_ptr(), a, 0, 0, false, true)?;
        self.outer(words, g, words.read, a, dw, dz.device_ptr(), a, fread.device_ptr(), dw, false, true)?;
        self.transposed(words, words.read, a, dw, dz.device_ptr(), a, dr.device_ptr(), false, true)?;
        self.ratio_adjoint(words, fread.device_ptr(), fscale.device_ptr(), dr.device_ptr(), 0, dx.device_ptr(), true)?;
        for (at, tick) in ticks.iter().enumerate().rev() {
            words.qf = tick.qf.device_ptr();
            words.vf = tick.vf.device_ptr();
            words.cls = tick.cls.device_ptr();
            words.class_off = tick.class_off.device_ptr();
            words.members = tick.members.device_ptr();
            words.e = tick.e.device_ptr();
            words.qkv = tick.qkv.device_ptr();
            words.hold = tick.hold.device_ptr();
            words.holdm = tick.holdm.device_ptr();
            words.sw = tick.sw.device_ptr();
            words.sv = tick.sv.device_ptr();
            words.sc = tick.sc.device_ptr();
            words.ce = tick.ce.device_ptr();
            words.pa = tick.pa.device_ptr();
            words.pb = tick.pb.device_ptr();
            words.pc = tick.pc.device_ptr();
            // The pair contact: x_out = x_mid + W_c c + b_c.
            self.outer(words, g, words.w_bias, dw, 0, dx.device_ptr(), dw, 0, 0, false, false)?;
            self.outer(words, g, words.w, dw, f, dx.device_ptr(), dw, tick.pc.device_ptr(), f, true, false)?;
            self.transposed(words, words.w, dw, f, dx.device_ptr(), dw, dc.device_ptr(), false, false)?;
            let (mut dcp, mut dap, mut dbp) = (dc.device_ptr(), da.device_ptr(), db.device_ptr());
            self.launch("field_pair_back", Self::cells((sites * f) as u64), THREADS, &mut [arg(words), arg(&mut dcp), arg(&mut dap), arg(&mut dbp)])?;
            self.outer(words, g, words.wa, f, dw, da.device_ptr(), f, tick.read2.device_ptr(), dw, false, false)?;
            self.outer(words, g, words.wb, f, dw, db.device_ptr(), f, tick.read2.device_ptr(), dw, false, false)?;
            self.outer(words, g, words.a_bias, f, 0, da.device_ptr(), f, 0, 0, false, false)?;
            self.outer(words, g, words.b_bias, f, 0, db.device_ptr(), f, 0, 0, false, false)?;
            self.transposed(words, words.wa, f, dw, da.device_ptr(), f, ra.device_ptr(), false, false)?;
            self.transposed(words, words.wb, f, dw, db.device_ptr(), f, rb.device_ptr(), false, false)?;
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
            card.zero_octets(&lifts, 0, 16 * heads * sites).map_err(device)?;
            for h in 0..heads {
                // The crowds' difference arrays start empty a head (§14.10).
                card.zero_octets(&cv, 0, 16 * rows * span).map_err(device)?;
                card.zero_octets(&cw, 0, 16 * rows * span).map_err(device)?;
                let (mut hh, mut closes, mut dyhp, mut dsp, mut dqp) = (h as u32, if field.declaration.closes(at, h) { field.declaration.copies() as u32 } else { 0 }, dyh.device_ptr(), ds.device_ptr(), dq.device_ptr());
                self.launch("field_contact_rows", Self::warps(sites as u64), THREADS, &mut [arg(words), arg(&mut hh), arg(&mut closes), arg(&mut dyhp), arg(&mut dsp), arg(&mut dqp)])?;
                let (mut hh, mut dyhp, mut dsp, mut dqp, mut dvp) = (h as u32, dyh.device_ptr(), ds.device_ptr(), dq.device_ptr(), dv.device_ptr());
                self.launch("field_contact_columns", Self::warps(sites as u64), THREADS, &mut [arg(words), arg(&mut hh), arg(&mut dyhp), arg(&mut dsp), arg(&mut dqp), arg(&mut dvp)])?;
                let (mut hh, mut dqp, mut dvp) = (h as u32, dq.device_ptr(), dv.device_ptr());
                self.launch("field_spread", Self::cells((regions * span) as u64), THREADS, &mut [arg(words), arg(&mut hh), arg(&mut dqp), arg(&mut dvp)])?;
            }
            let (mut qs, mut dqp) = (tick.qscale.device_ptr(), dq.device_ptr());
            self.launch("field_unit_back", Self::warps((heads * sites) as u64), THREADS, &mut [arg(words), arg(&mut qs), arg(&mut dqp)])?;
            for chart in [&dq, &dv] {
                let mut cp = chart.device_ptr();
                self.launch("field_unframe", Self::cells((sites * m) as u64), THREADS, &mut [arg(words), arg(&mut cp)])?;
            }
            // The holds return to the unframed word's mode that sets them (§14.2).
            let mut dqp = dq.device_ptr();
            self.launch("field_hold_back", Self::cells((heads * sites) as u64), THREADS, &mut [arg(words), arg(&mut dqp)])?;
            card.zero_octets(&dr, 0, 8 * sites * dw).map_err(device)?;
            for (weight, bias, chart) in [(words.q, words.q_bias, &dq), (words.v, words.v_bias, &dv)] {
                self.outer(words, g, weight, m2, dw, chart.device_ptr(), m2, tick.read.device_ptr(), dw, false, false)?;
                self.outer(words, g, bias, m2, 0, chart.device_ptr(), m2, 0, 0, false, false)?;
                self.transposed(words, weight, m2, dw, chart.device_ptr(), m2, dr.device_ptr(), true, false)?;
            }
            self.ratio_adjoint(words, tick.read.device_ptr(), tick.scale.device_ptr(), dr.device_ptr(), dmid.device_ptr(), dx.device_ptr(), false)?;
        }
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
            let rows_sites_c = self.timed(Kind::Copy, || card.upload(&rows_sites)).map_err(device)?;
            let rows_shares_c = self.timed(Kind::Copy, || card.upload(&rows_shares)).map_err(device)?;
            let segments_c = self.timed(Kind::Copy, || card.upload(&segments)).map_err(device)?;
            let (mut gp, mut dxp, mut rsp, mut rwp, mut sgp, mut count, mut base) = (g.device_ptr(), dx.device_ptr(), rows_sites_c.device_ptr(), rows_shares_c.device_ptr(), segments_c.device_ptr(), count, base);
            self.launch("field_encoding", Self::cells(count as u64 * dw as u64), THREADS, &mut [arg(words), arg(&mut gp), arg(&mut dxp), arg(&mut rsp), arg(&mut rwp), arg(&mut sgp), arg(&mut count), arg(&mut base)])?;
        }
        Ok(())
    }

    /// The batch's refusals, read off the card.
    fn status(&self, status: &CardBuffer<'c, u32>) -> Result<()> {
        let bits = self.timed(Kind::Copy, || self.card.fetch(status)).map_err(device)?[0];
        if bits == 0 {
            return Ok(());
        }
        let names = [(1, "a sum outgrew its 128-bit carrier"), (2, "a released value outgrew its 64-bit carrier"), (4, "a released value outgrew its 32-bit carrier"), (8, "a current's covector outgrew its 128-bit carrier")];
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
pub fn region_octets(d: &FieldDeclaration, returning: bool, sites: usize) -> u64 {
    let (dw, m2, f, a, h, span) = (d.width as u64, 2 * d.complex() as u64, d.contacts as u64, d.alphabet as u64, d.heads as u64, 2 * d.modes as u64);
    let ticks_kept = if returning { d.ticks as u64 } else { 1 };
    // Per site a kept tick adds its hold (a word and its mode), its prefix sums' row (words and values
    // on 128 bits, a count) and its crowd shares (`crowd_slots` words a head).
    let slots = crowd_slots(d.reach) as u64;
    let tick_site = 4 * dw + 16 + 8 * 2 * m2 + 2 * 8 * h * span + 16 * h + 2 * 4 * h + (8 + 4) * h + 8 * m2 + 4 * dw + 16 + 3 * 8 * f + (2 * 16 * span + 8) * h + 8 * h * slots;
    let tick_fixed = tick_fixed_octets(d);
    let face_site = 8 * dw + 4 * dw + 16 + 8 * a + 8 * a + 16 + 16;
    let mixture_site = 5 + 2 * 4 * a;
    // The reverse adds its covectors, the hold covectors `[h][t]` and the crowds' two difference arrays.
    let reverse_site = if returning { 8 * a + 5 * 8 * dw + 3 * 8 * f + 8 * m2 + 8 * h * span + 2 * 8 * m2 + 16 * h + 2 * 16 * span } else { 0 };
    let (s, pairs) = (sites as u64, (sites * sites) as u64);
    // The weights are kept only for a return.
    let weights = if returning { h * 8 * pairs } else { 0 };
    ticks_kept * (weights + s * tick_site + tick_fixed) + s * (face_site + mixture_site + reverse_site) + if returning { 16 * pairs } else { 0 }
}

/// A kept tick's octets a region beside its sites': the carrier's width (one word), the class
/// offsets `H (2·3^b + 1)` words (each class's definite members and the rest) and the prefix sums'
/// extra row (a region's `S + 1` rows, §14.10), which the reverse's difference arrays share.
fn tick_fixed_octets(d: &FieldDeclaration) -> u64 {
    4 + 4 * d.heads as u64 * (2 * d.classes() as u64 + 1) + (2 * 16 * 2 * d.modes as u64 + 8) * d.heads as u64 + 2 * 16 * 2 * d.modes as u64
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
    let mut out = Vec::new();
    let (mut from, mut taken) = (0usize, 0u64);
    for (i, &n) in lengths.iter().enumerate() {
        let need = octets(n);
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
        let (faces, _, g, _) = self.run(field, regions, true, false, None)?;
        Ok((faces, g))
    }

    fn read_faces(&mut self, field: &Field, regions: &[Region]) -> Result<Vec<Vec<Option<TowerFace>>>> {
        Ok(self.run(field, regions, false, false, None)?.0)
    }

    fn read_logits(&mut self, field: &Field, regions: &[Region]) -> Result<Vec<Vec<Option<Vec<i64>>>>> {
        Ok(self.run(field, regions, false, true, None)?.1)
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
}

/// Each kept site's still heads' rows: the met sources with their weights, and the row's mass.
type Rows = Vec<Vec<(Vec<(u32, u64)>, u64)>>;

#[cfg(test)]
mod tests {
    use super::*;

    fn declaration(width: usize, heads: usize, contacts: usize) -> FieldDeclaration {
        FieldDeclaration { alphabet: 122, width, heads, modes: 8, still: 2, contacts, ticks: 2, frames: 4, reach: 2221 }
    }

    /// Every region is in one batch, in order, each batch within the budget; a region past the budget
    /// alone is refused.
    #[test]
    fn batches_cover_the_regions_in_order_within_the_budget() {
        let d = declaration(32, 4, 32);
        let lengths = [1412, 300, 2221, 64, 900, 1229, 1229, 77];
        for returning in [false, true] {
            let octets = |n: usize| region_octets(&d, returning, n);
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

    /// A region's allocations count its weights, its contact's return on a return, and every site's
    /// carriers beside them: a release batch of 128 regions at the reach carries some 3 GB of them at
    /// the grown declaration, which the weights alone never counted.
    #[test]
    fn a_regions_octets_count_its_carriers_beside_its_weights() {
        for d in [declaration(32, 4, 32), declaration(64, 8, 64)] {
            let n = 1504u64;
            // The weights are kept only for a return; each kept tick adds its carrier widths and class
            // offsets.
            let weights = |returning: bool| if returning { d.ticks as u64 * d.heads as u64 * 8 * n * n + 16 * n * n } else { 0 };
            let fixed = |returning: bool| tick_fixed_octets(&d) * if returning { d.ticks as u64 } else { 1 };
            for returning in [false, true] {
                let all = region_octets(&d, returning, n as usize);
                assert!(all > weights(returning) + fixed(returning));
                // The carriers grow by site, the weights by pair.
                let carriers = all - weights(returning) - fixed(returning);
                assert_eq!(region_octets(&d, returning, 2 * n as usize) - 4 * weights(returning) - fixed(returning), 2 * carriers);
            }
        }
        let grown = declaration(64, 8, 64);
        let carriers = 128 * 1504 * (region_octets(&grown, false, 1) - tick_fixed_octets(&grown));
        assert!(carriers > 1 << 30, "{carriers}");
    }
}

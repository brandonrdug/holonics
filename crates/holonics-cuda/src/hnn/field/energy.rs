//! **The energy field's forward on the card** (`holonics::hnn::tower::field::energy`, the unified-theory readings of
//! November 6, 22:52 and November 7, 00:02; `kernels/field_energy.cuh`): the opening, `K` ticks of certified descent of one
//! stored energy under the supports held from the opening, and each open site's face as the total derivative of the energy
//! at the last state, `−dG/de` with `G = Φ(x^K(e); e)`, bit for bit the host's `Field::energy_pass`
//! ([`holonics::hnn::tower::field::Field::energy_logits`]).
//!
//! [definition; agent-inferred, November 6] **The work is laid out as the field's forward is.** The opening and the moments
//! are the field's own launches; the energy's sites are the host's `Field::energy_sites` (an open site carries the locked
//! uniform mixture), staged as any region's. A state's energy read is a cell ([`EnergyCell`]): the chart, the key and probe
//! words (the probe reading its moment), framed and at unit power, the definite words' prefix sums, the exposure's scores, and
//! each receiver's lock partition (`field_energy_rows_l*`: its mass the contact's series, its `log₂ Z` read from the
//! mass's leading bits as the host's `log2_big` reads them, its shares), the strand pair's and the letters' energy, each summed
//! per region as integers. The force is the locks' shares as their scores' covector through the reverse's own key and
//! probe brackets (`field_energy_rows_back`, `field_contact_columns`, `field_spread`), the unit powers' and the frames'
//! returns and the charts' transposes, with the pair's (`field_pair_back` of the contraction) and the letters' (held). The
//! regions of a batch tick in lockstep: each tick's force, then rounds of candidate steps, each region at its own halvings,
//! its energy read back and its fall certified as the host's `energy_relax` certifies it (`FIRST_HALVINGS`, `MOST_HALVINGS`,
//! one unit of `2^(−32)` a logarithm and two of slack); a region whose fall is certified takes its candidate's state, one
//! whose step moves nothing or whose halvings run out rests.
//!
//! [agent-inferred, November 6] **Each tick's cell is kept on the card** ([`EnergyPass::cells`]): the opening's and each
//! tick's last state's (a candidate whose every region stood is kept as it is; otherwise the tick's states are read again,
//! the same bits), with each tick's force and each region's halvings. [definition; the unified-theory reading of November 7,
//! 00:02] **The face's reverse reads them** ([`CardField::energy_reverse`], the host's `energy_reverse`): from `λ^K = −J F^K`
//! back over the kept ticks, each region at the halvings it stood at (none where it rested: its covector passes the tick),
//! the force's tangent along `w = s ⊙ λ'` (`−Hess Φ · w`, [`CardField::energy_tangent`]: the words' tangents, the locks'
//! scores', shares' and brackets' tangents beside their forces, the unit power's return differentiated, the pair's), the
//! tick's letters' covectors, and the opening's; the face adds them to the partial face at the last state. The learner's
//! return (the material's covector through the ticks) is not built: an energy field is read on the card, not trained.

use super::*;
use holonics::hnn::tower::field::{EnergyRead, EnergySquare, Shares, SquareCorners, FIRST_HALVINGS, MOST_HALVINGS};
use holonics::hnn::tower::FACE_BITS;

/// A region's energy sums on the card (`ENERGY_SUMS` in `kernels/field_energy.cuh`): the locks', the letters' and the
/// pair's, the logarithms read, the site pairs met, whether a step moved it, and `Φ` on `2^(−32)` bits.
const ENERGY_SUMS: usize = 8;
const ENERGY_LOGS: usize = 3;
const ENERGY_PAIRS: usize = 4;
const ENERGY_MOVED: usize = 5;
const ENERGY_PHI: usize = 6;

/// A state's energy read on the card (the host's `EnergyCell`): the state, its chart, the key and probe words (unframed,
/// then framed at unit power with their powers, the value half of the words at zero), the definite words' prefix sums,
/// the rows' least whole bits, the shares (the pairs' at the region block's dense address, the crowds' a slot), the pair
/// drives, the lifts, each row's `log₂ Z` on `2^(−32)` and each region's sums.
pub(super) struct EnergyCell<'c> {
    x: Pooled<'c, i64>,
    read: Pooled<'c, i32>,
    scale: Pooled<'c, i128>,
    qkv: Pooled<'c, i64>,
    pr: Pooled<'c, i64>,
    qf: Pooled<'c, i64>,
    qf32: Pooled<'c, i32>,
    vf: Pooled<'c, i64>,
    qscale: Pooled<'c, i128>,
    pq: Pooled<'c, i64>,
    pq32: Pooled<'c, i32>,
    pscale: Pooled<'c, i128>,
    sw: Pooled<'c, i128>,
    sv: Pooled<'c, i128>,
    sc: Pooled<'c, u64>,
    amin: Pooled<'c, i64>,
    e: Pooled<'c, u64>,
    ce: Pooled<'c, u64>,
    pa: Pooled<'c, i64>,
    pb: Pooled<'c, i64>,
    lift: Pooled<'c, i64>,
    rowlog: Pooled<'c, i128>,
    bits: Pooled<'c, u32>,
    sums: Pooled<'c, i128>,
}

/// What a batch's energy holds from its opening through its ticks (the host's `Held`): the resonance classes and their
/// lists, each site's letter rows and class bias, the moment's term in the face, the letters' force, the pair's
/// contraction at every site, and a zero covector of the current (the columns' value part reads it).
struct EnergyHeld<'c> {
    /// The resonance classes and their lists the rows read (`cls`, `class_off`, `members`, `pn`, `pcls`, `poff`, `pmem`): the
    /// batch's own ([`EnergyLists`]) or a base's.
    lists: [u64; 7],
    own: Pooled<'c, i64>,
    before: Pooled<'c, i64>,
    after: Pooled<'c, i64>,
    bias: Pooled<'c, i64>,
    mterm: Pooled<'c, i64>,
    lf: Pooled<'c, i64>,
    dc: Pooled<'c, i64>,
    dyh0: Pooled<'c, i64>,
}

/// [definition; the unified-theory reading of November 7, 00:02] **A batch's supports as a base holds them** (the host's
/// `Held::classes` and `Held::definite`): the resonance classes and their lists read at the opening (`[h][t]`, per region
/// `[h][r][..]`), each site's definite flag, and the regions' lengths, so a batch of other letters on the same layout is read
/// under them (`energy_relax`'s `base`).
pub(super) struct EnergyLists<'c> {
    cls: Pooled<'c, u32>,
    class_off: Pooled<'c, u32>,
    members: Pooled<'c, u32>,
    pn: Pooled<'c, u32>,
    pcls: Pooled<'c, u32>,
    poff: Pooled<'c, u32>,
    pmem: Pooled<'c, u32>,
    definite: Vec<u8>,
    lengths: Vec<usize>,
}

impl EnergyLists<'_> {
    fn pointers(&self) -> [u64; 7] {
        [self.cls.device_ptr(), self.class_off.device_ptr(), self.members.device_ptr(), self.pn.device_ptr(), self.pcls.device_ptr(), self.poff.device_ptr(), self.pmem.device_ptr()]
    }
}

/// [definition; the unified-theory reading of November 7, 00:02] **How a batch is read** (the host's `energy_relax` and
/// `energy_faces` arguments): its descent certified, or replayed at given halvings a region (`replay`, uncertified: a base's
/// descent read again on other letters); its supports its own or a base's (`base`); and whether its faces are read (the
/// reverse through the ticks), or only its energy (a square's `G`).
#[derive(Clone, Copy)]
struct EnergyPlan<'p, 'c> {
    replay: Option<&'p [Vec<Option<u32>>]>,
    base: Option<&'p EnergyLists<'c>>,
    faces: bool,
    /// Whether the energy's material covector `∂G/∂θ` is read a region (`Field::energy_material`; no faces).
    material: bool,
}

impl<'p, 'c> EnergyPlan<'p, 'c> {
    /// The forward as `energy_pass` reads it: certified, under the batch's own supports, with its faces.
    fn forward() -> Self {
        EnergyPlan { replay: None, base: None, faces: true, material: false }
    }
}

/// The force's buffers: the key and probe charts' covectors, the values' (read and discarded), one head's score covectors
/// at the dense address, the crowds' difference arrays, the pair drives' covectors and the force on the chart reads.
struct EnergyForce<'c> {
    dq: Pooled<'c, i64>,
    dp: Pooled<'c, i64>,
    dv: Pooled<'c, i64>,
    ds: Pooled<'c, i64>,
    cv: Pooled<'c, i128>,
    cw: Pooled<'c, i128>,
    da: Pooled<'c, i64>,
    db: Pooled<'c, i64>,
    force: Pooled<'c, i64>,
}

/// The force's tangent's buffers ([`CardField::energy_tangent`]): the words' tangents (unframed `[t][2M]`, framed and through
/// the unit power `[h][t][2n]`), their definite prefix sums, one head's score covectors and their tangents at the dense address,
/// the crowds' difference arrays, the words' forces and their tangents (`[t][2M]`), the unit power's return differentiated,
/// the pair drives' tangents and their forces, and the force's tangent on the chart reads.
struct EnergyTangent<'c> {
    wq: Pooled<'c, i64>,
    wp: Pooled<'c, i64>,
    fq: Pooled<'c, i64>,
    fp: Pooled<'c, i64>,
    uq: Pooled<'c, i64>,
    up: Pooled<'c, i64>,
    tsw: Pooled<'c, i128>,
    tsv: Pooled<'c, i128>,
    tsc: Pooled<'c, u64>,
    ds: Pooled<'c, i64>,
    tds: Pooled<'c, i128>,
    cw: Pooled<'c, i128>,
    tcw: Pooled<'c, i128>,
    fdq: Pooled<'c, i64>,
    fdp: Pooled<'c, i64>,
    tq: Pooled<'c, i64>,
    tp: Pooled<'c, i64>,
    cq: Pooled<'c, i64>,
    cp: Pooled<'c, i64>,
    ta: Pooled<'c, i64>,
    tb: Pooled<'c, i64>,
    da: Pooled<'c, i64>,
    db: Pooled<'c, i64>,
    t: Pooled<'c, i64>,
}

/// The reverse's buffers ([`CardField::energy_reverse`]): the state's covector `λ`, the scaled covector `w = s ⊙ λ`, its lift
/// `R w` and moment chart `Cᵀ w`, the lanes' adjoint of the tangent, and the letters' covectors (the host's
/// `LetterCovectors`: own, before and after rows `[t][D]`, the moment's `[t][2M]`, on `2^(−24)`).
struct EnergyReverse<'c> {
    lambda: Pooled<'c, i64>,
    wv: Pooled<'c, i64>,
    lift: Pooled<'c, i64>,
    chart: Pooled<'c, i64>,
    jt: Pooled<'c, i64>,
    own: Pooled<'c, i64>,
    before: Pooled<'c, i64>,
    after: Pooled<'c, i64>,
    moment: Pooled<'c, i64>,
}

/// [definition; agent-inferred, November 7] The material covector's accumulators ([`CardField::energy_material_run`]): each
/// region's `∂G/∂θ` and a stood tick's sum before its halvings' release, theta-long a region, on `2^(−40)`.
struct EnergyMaterial<'c> {
    g: Pooled<'c, i128>,
    tick: Pooled<'c, i128>,
    len: usize,
}

/// [agent-inferred, November 6] **A batch's energy forward as the card holds it**: every tick's cell (the opening's first,
/// then each tick's last state's), each region's halvings by tick, and the read's receipt. What a reverse through the ticks
/// will read.
pub(super) struct EnergyPass<'c> {
    #[allow(dead_code, reason = "held for a learner's reverse through the ticks (the face's own reverse has read them)")]
    pub(super) cells: Vec<EnergyCell<'c>>,
    pub(super) reads: Vec<EnergyRead>,
    /// The tick's last states read again ([`FieldTimes::energy_rereads`]).
    pub(super) rereads: u64,
    /// The batch's own supports (none where it read a base's), which a batch of other letters may hold.
    pub(super) lists: Option<EnergyLists<'c>>,
    /// Each region's material covector `∂G/∂θ` on `2^(−40)` where the plan reads it.
    pub(super) material: Vec<Vec<i128>>,
}

/// A region's energy read back: `Φ`, the logarithms read, the site pairs met, and whether the step before it moved it.
#[derive(Clone, Copy, Debug)]
struct Read {
    phi: i128,
    logs: u64,
    pairs: u64,
    moved: bool,
}

/// [agent-inferred, November 6] **Everything a region of `sites` sites allocates in an energy batch**: its kept cells (the
/// opening's, one a tick and a candidate in flight), each with its shares `H·S²` at their dense address and its per-site
/// carriers; what the batch holds (the classes and their lists, the letters, the moment's term and the letters' force, the
/// clocks and the moments); the force's buffers (one head's score covectors `S²`); and the face's.
pub fn energy_octets(d: &FieldDeclaration, sites: usize) -> u64 {
    energy_octets_widened(d, sites, None)
}

/// [`energy_octets`] under the width law at share `widen` (theory, November 7 23:34): the class lists sized by the law's bounds,
/// `3^b + 2(n − b)⌊S/(cap + 1)⌋` leaves and a probe stride of `2^n`.
pub fn energy_octets_widened(d: &FieldDeclaration, sites: usize, widen: Option<usize>) -> u64 {
    let (dw, m2, f, a, h, span) = (d.width as u64, 2 * d.complex() as u64, d.contacts as u64, d.alphabet as u64, d.heads as u64, 2 * d.modes as u64);
    let (s, pairs, lanes, slots, tm) = (sites as u64, (sites * sites) as u64, d.lanes as u64, crowd_slots(d.reach) as u64, d.moment_modes() as u64);
    let (probe_stride, classes) = match widen {
        Some(cap) => (1u64 << d.modes, (3usize.pow(d.class_trits() as u32) + 2 * d.modes.saturating_sub(d.class_trits()) * (sites / (cap + 1))) as u64),
        None => (1u64 << d.class_trits(), d.classes() as u64),
    };
    let cell_site = 8 * dw + 4 * dw + 16 * lanes + 8 * 2 * m2 + 8 * m2 + h * span * (8 + 4 + 8 + 8 + 4) + 2 * 16 * h + 2 * 16 * h * span + 8 * h + 8 * h + 8 * h * slots + 2 * 8 * f + 8 * dw + 16 * h;
    let cell_fixed = (2 * 16 * h * span + 8 * h) + 64 + 16 * ENERGY_SUMS as u64;
    let cells = d.ticks as u64 + 2;
    let held_site = 4 * h * (3 + 2 * probe_stride) + 6 * 8 * dw + 8 + 8 * f + 8 * h * span + 8 * m2 + 3 * 8 * 2 * h + 2 * 8 * h * d.modes as u64 + 112 * tm;
    let force_site = 3 * 8 * m2 + 2 * 16 * span + 2 * 8 * f + 8 * dw;
    let face_site = 16 * m2 + 2 * 8 * a + 16 + tm * (8 * 2 + 16 * 2 * 3 + 16 * 2 * 2 * 16) + 8 * dw + 8 * 2 * m2;
    // The reverse: each tick's force, the tangent's words and sums, its forces and the pair's, the covectors; one head's score
    // covectors and their tangents a pair.
    let reverse_site = d.ticks as u64 * 8 * dw + 2 * 8 * m2 + 4 * 8 * h * span + 2 * 16 * h * span + 8 * h + 2 * 16 * span + 6 * 8 * m2 + 4 * 8 * f + 8 * dw + 8 * 8 * dw + 2 * 8 * m2;
    cells * (h * 8 * pairs + s * cell_site + cell_fixed) + (8 + 8 + 16) * pairs + s * (held_site + force_site + face_site + reverse_site) + 4 * h * (3 * classes + 2)
}

/// The threads of a block of the skinless heads' score tangents (four warps, `field_energy_still_dz_k*`).
const STILL_THREADS: u32 = 128;

/// [definition; agent-inferred, November 7] **Whether a skinless head's score tangents run on the tensor cores**, and the tiles
/// of 16 its span takes (`kernels/field_energy.cuh`, the skinless heads' pair products): where the declaration has a skinless
/// head (a still or depth ring set) and its span fits two tiles. `FIELD_SCALAR_PAIRS` keeps the scalar products (a reading: the
/// same bits, the scalar time beside the tensor cores').
fn still_tiles(field: &Field) -> Option<u32> {
    let d = field.declaration;
    if !(0..d.heads).any(|h| skinless_head(field, h)) || std::env::var_os("FIELD_SCALAR_PAIRS").is_some() {
        return None;
    }
    match 2 * d.modes {
        1..=16 => Some(1),
        17..=32 => Some(2),
        _ => None,
    }
}

/// Whether head `h` of the declaration is skinless (`skinless` in `kernels/field.cu`: a still ring set's head, or a depth
/// ring's, a turned set among the last `depth`).
fn skinless_head(field: &Field, h: usize) -> bool {
    let d = field.declaration;
    let set = h % d.frames;
    set < d.still || set + d.depth >= d.frames
}

impl<'c> CardField<'c> {
    /// [definition; the unified-theory reading of November 6, 22:52] **An energy field's faces and logits on the card**
    /// (the host's `Field::energy_pass` region by region: each face the energy's total derivative), with each region's energy
    /// read ([`EnergyRead`]): the regions' energy sites staged, batched by the card's memory, each batch's forward and the
    /// face's reverse ([`CardField::energy_batch`]).
    #[allow(clippy::type_complexity)]
    pub(super) fn energy_run(&mut self, field: &Field, regions: &[Region]) -> Result<(Vec<Vec<Option<TowerFace>>>, Vec<Vec<Option<Vec<i64>>>>, Vec<EnergyRead>)> {
        let d = field.declaration;
        if !d.energy {
            return Err(TowerError::Refused("an energy read of a field whose faces are not one energy's forces"));
        }
        // The host's refusals of the energy's first build: no tower of scales (a non-plain clock is refused per batch).
        if field.scale.is_some() {
            return Err(TowerError::Refused("an energy field read with a tower of scales (its energy is not built)"));
        }
        admit_regions(&d, regions)?;
        // An open site stays a source carrying the locked mixture (the host's `Field::energy_sites`).
        let sited: Vec<(Vec<Option<Shares>>, Vec<bool>)> = regions.iter().map(|r| field.energy_sites(r)).collect();
        let staged: Vec<Region> = regions.iter().zip(&sited).map(|(r, (faces, locked))| Region { faces, locked, ..*r }).collect();
        admit_regions(&d, &staged)?;
        self.mark("outside_the_card");
        let card = self.card;
        let started = Instant::now();
        let (mut words, upload, face_octets) = self.upload(field, None)?;
        let lengths: Vec<usize> = staged.iter().map(|r| r.classes.len()).collect();
        let octets = |sites: usize| energy_octets_widened(&d, sites, field.widen);
        // A pooled buffer is at most a quarter longer than asked (its size class), so the batches are cut at four fifths of
        // the budget.
        let batches = batches(&lengths, &octets, (self.budget - face_octets) / 5 * 4)?;
        let (mut faces, mut logits, mut reads) = (Vec::with_capacity(regions.len()), Vec::with_capacity(regions.len()), Vec::with_capacity(regions.len()));
        for batch in batches {
            if batch.is_empty() {
                continue;
            }
            let peak = lengths[batch.clone()].iter().map(|&n| octets(n)).sum::<u64>();
            self.times.peak_store = self.times.peak_store.max(peak);
            self.times.batches += 1;
            let (f, z, pass) = self.energy_batch(field, &staged[batch], &mut words, EnergyPlan::forward())?;
            faces.extend(f);
            logits.extend(z);
            reads.extend(pass.reads);
            self.times.energy_rereads += pass.rereads;
        }
        let met = self.timed(Kind::Copy, || card.fetch(&upload.met)).map_err(device)?[0] as u128;
        self.times.pairs += met;
        self.times.reads += 1;
        self.times.read_ns += started.elapsed().as_nanos();
        Ok((faces, logits, reads))
    }

    /// A cell's buffers ([`EnergyCell`]).
    fn energy_cell_alloc(&self, field: &Field, sites: usize, pairs: usize, regions: usize) -> Result<EnergyCell<'c>> {
        let d = field.declaration;
        let (dw, m2, f, heads, span, lanes) = (d.width, 2 * d.complex(), d.contacts, d.heads, 2 * d.modes, d.lanes);
        let rows = sites + regions;
        let slots = crowd_slots(d.reach);
        let i64s = |len: usize| self.timed(Kind::Alloc, || self.take::<i64>(len.max(1))).map_err(device);
        let i128s = |len: usize| self.timed(Kind::Alloc, || self.take::<i128>(len.max(1))).map_err(device);
        Ok(EnergyCell {
            x: i64s(sites * dw)?,
            read: self.timed(Kind::Alloc, || self.take::<i32>((sites * dw).max(1))).map_err(device)?,
            scale: i128s(sites * lanes)?,
            // The value half of the words stays zero: an energy field reads no value.
            qkv: self.timed(Kind::Alloc, || self.take_zeroed::<i64>((sites * 2 * m2).max(1))).map_err(device)?,
            pr: i64s(sites * m2)?,
            qf: i64s(heads * sites * span)?,
            qf32: self.timed(Kind::Alloc, || self.take::<i32>((heads * sites * span).max(1))).map_err(device)?,
            vf: i64s(heads * sites * span)?,
            qscale: i128s(heads * sites)?,
            pq: i64s(heads * sites * span)?,
            pq32: self.timed(Kind::Alloc, || self.take::<i32>((heads * sites * span).max(1))).map_err(device)?,
            pscale: i128s(heads * sites)?,
            sw: i128s(heads * rows * span)?,
            sv: i128s(heads * rows * span)?,
            sc: self.timed(Kind::Alloc, || self.take::<u64>((heads * rows).max(1))).map_err(device)?,
            amin: i64s(heads * sites)?,
            e: self.timed(Kind::Alloc, || self.take::<u64>((heads * pairs).max(1))).map_err(device)?,
            ce: self.timed(Kind::Alloc, || self.take::<u64>((heads * sites * slots).max(1))).map_err(device)?,
            pa: i64s(sites * f)?,
            pb: i64s(sites * f)?,
            lift: i64s(sites * dw)?,
            rowlog: i128s(heads * sites)?,
            bits: self.timed(Kind::Alloc, || self.take_zeroed::<u32>(4)).map_err(device)?,
            sums: self.timed(Kind::Alloc, || self.take_zeroed::<i128>(regions * ENERGY_SUMS)).map_err(device)?,
        })
    }

    /// Point the words at a cell's carriers and the held lists.
    fn energy_point(words: &mut Words, c: &EnergyCell<'c>, held: &EnergyHeld<'c>) {
        words.x = c.x.device_ptr();
        words.qkv = c.qkv.device_ptr();
        words.pr = c.pr.device_ptr();
        words.qf = c.qf.device_ptr();
        words.qf32 = c.qf32.device_ptr();
        words.vf = c.vf.device_ptr();
        words.pq = c.pq.device_ptr();
        words.pq32 = c.pq32.device_ptr();
        words.pscale = c.pscale.device_ptr();
        words.sw = c.sw.device_ptr();
        words.sv = c.sv.device_ptr();
        words.sc = c.sc.device_ptr();
        words.amin = c.amin.device_ptr();
        words.e = c.e.device_ptr();
        words.ce = c.ce.device_ptr();
        words.pa = c.pa.device_ptr();
        words.pb = c.pb.device_ptr();
        words.bits = c.bits.device_ptr();
        words.sb = 0;
        [words.cls, words.class_off, words.members, words.pn, words.pcls, words.poff, words.pmem] = held.lists;
    }

    /// [definition; agent-inferred, November 6] **A state's energy read** (the host's `energy_cell`) at the cell's state
    /// `c.x`, its region sums zeroed by the caller (a step's moved flags are raised there first). At the opening (`classes`)
    /// the resonance classes are read from its chart and held (the host's `energy_classes`).
    #[allow(clippy::too_many_arguments)]
    fn energy_cell(&self, field: &Field, words: &mut Words, c: &EnergyCell<'c>, held: &EnergyHeld<'c>, classes: bool, sites: usize, regions: usize) -> Result<()> {
        let card = self.card;
        let d = field.declaration;
        let (dw, m2, f, n, heads) = (d.width, 2 * d.complex(), d.contacts, d.modes, d.heads);
        let span = 2 * n;
        let l = field.layout();
        Self::energy_point(words, c, held);
        self.chart(words, c.x.device_ptr(), &c.read, &c.scale, false)?;
        // The key word a head, and every receiver's probe reading its moment (the host's `energy_words`).
        self.affine("field_affine_x32", words, words.q, words.q_bias, words.rq, m2, dw, c.read.device_ptr(), dw, c.qkv.device_ptr(), 2 * m2, 0, false)?;
        self.affine("field_affine_x32", words, words.probe, words.probe_bias, words.rprobe, m2, dw, c.read.device_ptr(), dw, c.pr.device_ptr(), m2, 0, false)?;
        let mut prp = c.pr.device_ptr();
        self.launch("field_moment_add_probe", Self::cells((sites * m2) as u64), THREADS, &mut [arg(words), arg(&mut prp)])?;
        if classes {
            let buckets = 4 * 3 * d.classes() as u32;
            self.launch_shared("field_classes", (heads * regions).clamp(1, 1 << 20) as u32, 32, buckets, &mut [arg(words)])?;
        }
        card.zero_octets(&c.bits, 0, 16).map_err(device)?;
        // The frame and the unit power, by head.
        self.launch("field_frame", Self::cells((heads * sites * n) as u64), THREADS, &mut [arg(words)])?;
        let mut qs = c.qscale.device_ptr();
        self.launch("field_unit", Self::warps((heads * sites) as u64), THREADS, &mut [arg(words), arg(&mut qs)])?;
        self.launch("field_frame_probe", Self::cells((heads * sites * n) as u64), THREADS, &mut [arg(words)])?;
        let mut ps = c.pscale.device_ptr();
        self.launch("field_unit_probe", Self::warps((heads * sites) as u64), THREADS, &mut [arg(words), arg(&mut ps)])?;
        // The definite words' prefix sums, read by the crowds.
        self.launch("field_sums", Self::cells((heads * regions * (2 * span + 1)) as u64), THREADS, &mut [arg(words)])?;
        // The scores, then the partitions in the carrier their rows' exponents need.
        self.launch("field_exposure", Self::rows_grid((heads * sites) as u64, CONTACT_ROWS), (CONTACT_ROWS * 32) as u32, &mut [arg(words)])?;
        let spread = self.timed(Kind::Copy, || card.fetch(&c.bits)).map_err(device)?[1] as u64;
        let limbs = row_limbs(field, spread)?;
        let rows_entry: &'static str = [
            "field_energy_rows_l5",
            "field_energy_rows_l6",
            "field_energy_rows_l7",
            "field_energy_rows_l8",
            "field_energy_rows_l9",
            "field_energy_rows_l10",
            "field_energy_rows_l11",
            "field_energy_rows_l12",
            "field_energy_rows_l13",
            "field_energy_rows_l14",
            "field_energy_rows_l15",
            "field_energy_rows_l16",
            "field_energy_rows_l17",
            "field_energy_rows_l18",
            "field_energy_rows_l19",
            "field_energy_rows_l20",
        ][limbs - MIN_LIMBS];
        let (mut lp, mut sp) = (c.rowlog.device_ptr(), c.sums.device_ptr());
        self.launch(rows_entry, Self::rows_grid((heads * sites) as u64, CONTACT_ROWS), (CONTACT_ROWS * 32) as u32, &mut [arg(words), arg(&mut lp), arg(&mut sp)])?;
        // The strand pair's energy through its contraction.
        self.affine("field_affine_x32", words, words.wa, words.a_bias, words.ra, f, dw, c.read.device_ptr(), dw, c.pa.device_ptr(), f, 0, false)?;
        self.affine("field_affine_x32", words, words.wb, words.b_bias, words.rb, f, dw, c.read.device_ptr(), dw, c.pb.device_ptr(), f, 0, false)?;
        let (mut pc, mut sp) = (l.pair_c as u64, c.sums.device_ptr());
        let region_grid = (regions as u32).clamp(1, 65_535);
        self.launch("field_energy_pair_phi", region_grid, THREADS, &mut [arg(words), arg(&mut pc), arg(&mut sp)])?;
        // The letters' energy: each letter with every site its rows reach, through the lift at every site.
        self.affine("field_affine_x32", words, words.read, l.lift_bias as u64, words.rread, dw, dw, c.read.device_ptr(), dw, c.lift.device_ptr(), dw, 0, false)?;
        {
            let (mut rp, mut yp, mut op, mut bp, mut ap, mut cp, mut mp, mut sp) = (c.read.device_ptr(), c.lift.device_ptr(), held.own.device_ptr(), held.before.device_ptr(), held.after.device_ptr(), held.bias.device_ptr(), held.mterm.device_ptr(), c.sums.device_ptr());
            self.launch("field_energy_letters_phi", region_grid, THREADS, &mut [arg(words), arg(&mut rp), arg(&mut yp), arg(&mut op), arg(&mut bp), arg(&mut ap), arg(&mut cp), arg(&mut mp), arg(&mut sp)])?;
        }
        let mut sp = c.sums.device_ptr();
        self.launch("field_energy_phi", Self::cells(regions as u64), THREADS, &mut [arg(words), arg(&mut sp)])
    }

    /// Each region's energy read back from a cell ([`Read`]).
    fn energy_reads(&self, c: &EnergyCell<'c>, regions: usize) -> Result<Vec<Read>> {
        let sums = self.timed(Kind::Copy, || self.card.fetch_range(&c.sums, 0, regions * ENERGY_SUMS)).map_err(device)?;
        Ok(sums
            .chunks_exact(ENERGY_SUMS)
            .map(|s| Read { phi: s[ENERGY_PHI], logs: s[ENERGY_LOGS] as u64, pairs: s[ENERGY_PAIRS] as u64, moved: s[ENERGY_MOVED] != 0 })
            .collect())
    }

    /// [definition; agent-inferred, November 6] **The energy's force on each site's chart read** (the host's
    /// `energy_force`), `−∂Φ/∂r̂` on `2^(−24)` into `fb.force`, and the probes' share of it `fb.dp` (unframed), whose turned
    /// modes the face's moment part reads.
    #[allow(clippy::too_many_arguments)]
    fn energy_force(&self, field: &Field, words: &mut Words, c: &EnergyCell<'c>, held: &EnergyHeld<'c>, fb: &EnergyForce<'c>, sites: usize, regions: usize) -> Result<()> {
        let card = self.card;
        let d = field.declaration;
        let (dw, m, n, f, heads) = (d.width, d.complex(), d.modes, d.contacts, d.heads);
        let (m2, span) = (2 * m, 2 * n);
        let rows = sites + regions;
        Self::energy_point(words, c, held);
        words.dp = fb.dp.device_ptr();
        words.cv = fb.cv.device_ptr();
        words.cw = fb.cw.device_ptr();
        card.zero_octets(&fb.dp, 0, 8 * sites * m2).map_err(device)?;
        // The locks: each head's shares as their scores' covector, through the probe's and the key's brackets.
        for h in 0..heads {
            self.stamp_head(Some(h));
            card.zero_octets(&fb.cv, 0, 16 * rows * span).map_err(device)?;
            card.zero_octets(&fb.cw, 0, 16 * rows * span).map_err(device)?;
            let (mut hh, mut dsp, mut dqp) = (h as u32, fb.ds.device_ptr(), fb.dq.device_ptr());
            self.launch("field_energy_rows_back", Self::rows_grid(sites as u64, REV_ROWS), (REV_ROWS * 32) as u32, &mut [arg(words), arg(&mut hh), arg(&mut dsp), arg(&mut dqp)])?;
            let (mut hh, mut dyhp, mut dsp, mut dqp, mut dvp) = (h as u32, held.dyh0.device_ptr(), fb.ds.device_ptr(), fb.dq.device_ptr(), fb.dv.device_ptr());
            self.launch("field_contact_columns", Self::rows_grid(sites as u64, CONTACT_ROWS), (CONTACT_ROWS * 32) as u32, &mut [arg(words), arg(&mut hh), arg(&mut dyhp), arg(&mut dsp), arg(&mut dqp), arg(&mut dvp)])?;
            let (mut hh, mut dqp, mut dvp) = (h as u32, fb.dq.device_ptr(), fb.dv.device_ptr());
            self.launch("field_spread", (regions as u32).clamp(1, 65_535), THREADS, &mut [arg(words), arg(&mut hh), arg(&mut dqp), arg(&mut dvp)])?;
        }
        self.stamp_head(None);
        // Through each word's ratio to its own power, then out of the frame.
        let (mut qs, mut dqp) = (c.qscale.device_ptr(), fb.dq.device_ptr());
        self.launch("field_unit_back", Self::warps((heads * sites) as u64), THREADS, &mut [arg(words), arg(&mut qs), arg(&mut dqp)])?;
        let (mut ps, mut dpp) = (c.pscale.device_ptr(), fb.dp.device_ptr());
        self.launch("field_unit_back_probe", Self::warps((heads * sites) as u64), THREADS, &mut [arg(words), arg(&mut ps), arg(&mut dpp)])?;
        for chart in [&fb.dq, &fb.dp] {
            let mut cp = chart.device_ptr();
            self.launch("field_unframe", Self::cells((sites * m) as u64), THREADS, &mut [arg(words), arg(&mut cp)])?;
        }
        self.transposed(words, words.q, m2, dw, fb.dq.device_ptr(), m2, fb.force.device_ptr(), false, false)?;
        self.transposed(words, words.probe, m2, dw, fb.dp.device_ptr(), m2, fb.force.device_ptr(), true, false)?;
        // The pair: the complex product's return of its contraction, through the drives' transposes.
        let (mut dcp, mut dap, mut dbp) = (held.dc.device_ptr(), fb.da.device_ptr(), fb.db.device_ptr());
        self.launch("field_pair_back", Self::cells((sites * f / 2) as u64), THREADS, &mut [arg(words), arg(&mut dcp), arg(&mut dap), arg(&mut dbp)])?;
        self.transposed(words, words.wa, f, dw, fb.da.device_ptr(), f, fb.force.device_ptr(), true, false)?;
        self.transposed(words, words.wb, f, dw, fb.db.device_ptr(), f, fb.force.device_ptr(), true, false)?;
        // The letters' force, held.
        let (mut lfp, mut fp) = (held.lf.device_ptr(), fb.force.device_ptr());
        self.launch("field_energy_force_add", Self::cells((sites * dw) as u64), THREADS, &mut [arg(words), arg(&mut lfp), arg(&mut fp)])
    }

    /// The tangent's buffers ([`EnergyTangent`]).
    fn energy_tangent_alloc(&self, field: &Field, sites: usize, pairs: usize, regions: usize) -> Result<EnergyTangent<'c>> {
        let d = field.declaration;
        let (dw, m2, f, heads, span) = (d.width, 2 * d.complex(), d.contacts, d.heads, 2 * d.modes);
        let rows = sites + regions;
        let i64s = |len: usize| self.timed(Kind::Alloc, || self.take::<i64>(len.max(1))).map_err(device);
        let i128s = |len: usize| self.timed(Kind::Alloc, || self.take::<i128>(len.max(1))).map_err(device);
        Ok(EnergyTangent {
            wq: i64s(sites * m2)?,
            wp: i64s(sites * m2)?,
            fq: i64s(heads * sites * span)?,
            fp: i64s(heads * sites * span)?,
            uq: i64s(heads * sites * span)?,
            up: i64s(heads * sites * span)?,
            tsw: i128s(heads * rows * span)?,
            tsv: i128s(heads * rows * span)?,
            tsc: self.timed(Kind::Alloc, || self.take::<u64>((heads * rows).max(1))).map_err(device)?,
            ds: i64s(pairs)?,
            tds: i128s(pairs)?,
            cw: i128s(rows * span)?,
            tcw: i128s(rows * span)?,
            fdq: i64s(sites * m2)?,
            fdp: i64s(sites * m2)?,
            tq: i64s(sites * m2)?,
            tp: i64s(sites * m2)?,
            cq: i64s(sites * m2)?,
            cp: i64s(sites * m2)?,
            ta: i64s(sites * f)?,
            tb: i64s(sites * f)?,
            da: i64s(sites * f)?,
            db: i64s(sites * f)?,
            t: i64s(sites * dw)?,
        })
    }

    /// [definition; the unified-theory reading of November 7, 00:02] **The force's tangent** `δF = −Hess Φ · v` at cell `c`
    /// along `v` (`[t][D]` on `2^(−24)`, at `v`), into `tb.t`, and the probes' share of it `tb.cp` (unframed, `[t][2M]`): the
    /// host's `energy_tangent` and `lock_words` with a tangent, launch for launch (`kernels/field_energy.cuh`).
    #[allow(clippy::too_many_arguments)]
    fn energy_tangent(&self, field: &Field, words: &mut Words, c: &EnergyCell<'c>, held: &EnergyHeld<'c>, tb: &EnergyTangent<'c>, v: u64, sites: usize, regions: usize) -> Result<()> {
        let card = self.card;
        let d = field.declaration;
        let (dw, m, n, f, heads) = (d.width, d.complex(), d.modes, d.contacts, d.heads);
        let (m2, span) = (2 * m, 2 * n);
        let rows = sites + regions;
        let l = field.layout();
        Self::energy_point(words, c, held);
        // The words' tangents through the charts (no bias: linear in the direction), framed by head.
        self.affine("field_affine_x64", words, words.q, NO_BIAS, words.rq, m2, dw, v, dw, tb.wq.device_ptr(), m2, 0, false)?;
        self.affine("field_affine_x64", words, words.probe, NO_BIAS, words.rprobe, m2, dw, v, dw, tb.wp.device_ptr(), m2, 0, false)?;
        let (pr0, pq0) = (words.pr, words.pq);
        for (word, framed) in [(&tb.wq, &tb.fq), (&tb.wp, &tb.fp)] {
            (words.pr, words.pq) = (word.device_ptr(), framed.device_ptr());
            self.launch("field_frame_probe", Self::cells((heads * sites * n) as u64), THREADS, &mut [arg(words)])?;
        }
        (words.pr, words.pq) = (pr0, pq0);
        // Through the unit power (its Jacobian is its return).
        for (unit, scale, framed, out) in [(&c.qf, &c.qscale, &tb.fq, &tb.uq), (&c.pq, &c.pscale, &tb.fp, &tb.up)] {
            let (mut up_, mut sp, mut fp, mut op) = (unit.device_ptr(), scale.device_ptr(), framed.device_ptr(), out.device_ptr());
            self.launch("field_energy_unit_tangent", Self::warps((heads * sites) as u64), THREADS, &mut [arg(words), arg(&mut up_), arg(&mut sp), arg(&mut fp), arg(&mut op)])?;
        }
        // The key tangents' definite prefix sums, read by the crowds (`field_sums` on the tangent's words).
        let saved = (words.qf, words.vf, words.sw, words.sv, words.sc);
        (words.qf, words.vf, words.sw, words.sv, words.sc) = (tb.uq.device_ptr(), tb.uq.device_ptr(), tb.tsw.device_ptr(), tb.tsv.device_ptr(), tb.tsc.device_ptr());
        self.launch("field_sums", Self::cells((heads * regions * (2 * span + 1)) as u64), THREADS, &mut [arg(words)])?;
        (words.qf, words.vf, words.sw, words.sv, words.sc) = saved;
        // The locks' force on the words and its tangent, head by head.
        words.dp = tb.fdp.device_ptr();
        words.cw = tb.cw.device_ptr();
        let still_dz = still_tiles(field).map(|kt| if kt == 1 { "field_energy_still_dz_k1" } else { "field_energy_still_dz_k2" });
        for h in 0..heads {
            self.stamp_head(Some(h));
            card.zero_octets(&tb.cw, 0, 16 * rows * span).map_err(device)?;
            card.zero_octets(&tb.tcw, 0, 16 * rows * span).map_err(device)?;
            // A skinless head's class blocks' score tangents on the tensor cores, into `tds` for the rows to read.
            let mut blocked = 0u32;
            if let Some(entry) = still_dz.filter(|_| skinless_head(field, h)) {
                let (mut hh, mut uqp, mut upp, mut tdsp) = (h as u32, tb.uq.device_ptr(), tb.up.device_ptr(), tb.tds.device_ptr());
                let blocks = (regions * d.classes()).clamp(1, 1 << 20) as u32;
                self.launch(entry, blocks, STILL_THREADS, &mut [arg(words), arg(&mut hh), arg(&mut uqp), arg(&mut upp), arg(&mut tdsp)])?;
                blocked = 1;
            }
            let (mut hh, mut uqp, mut upp, mut tswp, mut dsp, mut tdsp, mut dqp, mut tqp, mut tpp, mut tcwp) = (h as u32, tb.uq.device_ptr(), tb.up.device_ptr(), tb.tsw.device_ptr(), tb.ds.device_ptr(), tb.tds.device_ptr(), tb.fdq.device_ptr(), tb.tq.device_ptr(), tb.tp.device_ptr(), tb.tcw.device_ptr());
            self.launch("field_energy_tangent_rows", Self::rows_grid(sites as u64, REV_ROWS), (REV_ROWS * 32) as u32, &mut [arg(words), arg(&mut hh), arg(&mut uqp), arg(&mut upp), arg(&mut tswp), arg(&mut dsp), arg(&mut tdsp), arg(&mut dqp), arg(&mut tqp), arg(&mut tpp), arg(&mut tcwp), arg(&mut blocked)])?;
            let (mut hh, mut uqp, mut upp, mut dsp, mut tdsp, mut dqp, mut tqp) = (h as u32, tb.uq.device_ptr(), tb.up.device_ptr(), tb.ds.device_ptr(), tb.tds.device_ptr(), tb.fdq.device_ptr(), tb.tq.device_ptr());
            self.launch("field_energy_tangent_columns", Self::rows_grid(sites as u64, CONTACT_ROWS), (CONTACT_ROWS * 32) as u32, &mut [arg(words), arg(&mut hh), arg(&mut uqp), arg(&mut upp), arg(&mut dsp), arg(&mut tdsp), arg(&mut dqp), arg(&mut tqp)])?;
            for (cw, extra, out) in [(&tb.cw, 0u32, &tb.fdq), (&tb.tcw, 8, &tb.tq)] {
                let (mut hh, mut cwp, mut ex, mut op) = (h as u32, cw.device_ptr(), extra, out.device_ptr());
                self.launch("field_energy_spread", (regions as u32).clamp(1, 65_535), THREADS, &mut [arg(words), arg(&mut hh), arg(&mut cwp), arg(&mut ex), arg(&mut op)])?;
            }
        }
        self.stamp_head(None);
        // The unit power's return differentiated along the words' tangents, then out of the frame.
        for (unit, scale, du, dwt, force, tforce, out) in [(&c.qf, &c.qscale, &tb.uq, &tb.fq, &tb.fdq, &tb.tq, &tb.cq), (&c.pq, &c.pscale, &tb.up, &tb.fp, &tb.fdp, &tb.tp, &tb.cp)] {
            let (mut up_, mut sp, mut dup, mut dwp, mut fp, mut tfp, mut op) = (unit.device_ptr(), scale.device_ptr(), du.device_ptr(), dwt.device_ptr(), force.device_ptr(), tforce.device_ptr(), out.device_ptr());
            self.launch("field_energy_unit_tangent_back", Self::warps((heads * sites) as u64), THREADS, &mut [arg(words), arg(&mut up_), arg(&mut sp), arg(&mut dup), arg(&mut dwp), arg(&mut fp), arg(&mut tfp), arg(&mut op)])?;
        }
        for chart in [&tb.cq, &tb.cp] {
            let mut cp = chart.device_ptr();
            self.launch("field_unframe", Self::cells((sites * m) as u64), THREADS, &mut [arg(words), arg(&mut cp)])?;
        }
        self.transposed(words, words.q, m2, dw, tb.cq.device_ptr(), m2, tb.t.device_ptr(), false, false)?;
        self.transposed(words, words.probe, m2, dw, tb.cp.device_ptr(), m2, tb.t.device_ptr(), true, false)?;
        // The pair: each drive's force linear in the other's tangent drive, through the transposes.
        self.affine("field_affine_x64", words, words.wa, NO_BIAS, words.ra, f, dw, v, dw, tb.ta.device_ptr(), f, 0, false)?;
        self.affine("field_affine_x64", words, words.wb, NO_BIAS, words.rb, f, dw, v, dw, tb.tb.device_ptr(), f, 0, false)?;
        let (mut pc, mut tap, mut tbp, mut dap, mut dbp) = (l.pair_c as u64, tb.ta.device_ptr(), tb.tb.device_ptr(), tb.da.device_ptr(), tb.db.device_ptr());
        self.launch("field_energy_pair_tangent", Self::cells((sites * f / 2) as u64), THREADS, &mut [arg(words), arg(&mut pc), arg(&mut tap), arg(&mut tbp), arg(&mut dap), arg(&mut dbp)])?;
        self.transposed(words, words.wa, f, dw, tb.da.device_ptr(), f, tb.t.device_ptr(), true, false)?;
        self.transposed(words, words.wb, f, dw, tb.db.device_ptr(), f, tb.t.device_ptr(), true, false)
    }

    /// [definition; the unified-theory reading of November 7, 00:02] **The reverse through the ticks and the opening** (the
    /// host's `energy_reverse`), every region of the batch at once: from `λ^K = −J F^K` (the force `fb.force` at the last cell)
    /// back over each kept tick, each region at the halvings it stood at there (none where it did not stand: its covector
    /// passes the tick unchanged), `w = s ⊙ λ'`, the force's tangent along `w`, the tick's letters' covectors and `λ = λ' +
    /// 2^(−h) (r̂⟨λ', F⟩/W + J δF)`; then the opening's. Returns the letters' covectors.
    #[allow(clippy::too_many_arguments)]
    fn energy_reverse(&self, field: &Field, words: &mut Words, cells: &[EnergyCell<'c>], forces: &[Pooled<'c, i64>], halvings: &[Vec<Option<u32>>], held: &EnergyHeld<'c>, fb: &EnergyForce<'c>, sites: usize, pairs: usize, regions: usize, material: Option<&EnergyMaterial<'c>>) -> Result<EnergyReverse<'c>> {
        let d = field.declaration;
        let (dw, m2) = (d.width, 2 * d.complex());
        let (mface, _, _) = moment_face(field);
        let i64s = |len: usize| self.timed(Kind::Alloc, || self.take::<i64>(len.max(1))).map_err(device);
        let zeroed = |len: usize| self.timed(Kind::Alloc, || self.take_zeroed::<i64>(len.max(1))).map_err(device);
        let rb = EnergyReverse { lambda: i64s(sites * dw)?, wv: i64s(sites * dw)?, lift: i64s(sites * dw)?, chart: i64s(sites * m2)?, jt: i64s(sites * dw)?, own: zeroed(sites * dw)?, before: zeroed(sites * dw)?, after: zeroed(sites * dw)?, moment: zeroed(sites * m2)? };
        let last = cells.last().ok_or(TowerError::Refused("an energy forward with no opening"))?;
        // λ^K = −J F^K.
        Self::energy_point(words, last, held);
        self.ratio_adjoint(words, last.read.device_ptr(), last.scale.device_ptr(), fb.force.device_ptr(), 0, rb.lambda.device_ptr(), false)?;
        let (mut lp, mut cells_n) = (rb.lambda.device_ptr(), (sites * dw) as u64);
        self.launch("field_energy_negate", Self::cells(cells_n), THREADS, &mut [arg(words), arg(&mut lp), arg(&mut cells_n)])?;
        let tb = self.energy_tangent_alloc(field, sites, pairs, regions)?;
        for k in (0..forces.len()).rev() {
            let at: Vec<u32> = (0..regions).map(|r| halvings[r].get(k).copied().flatten().unwrap_or(u32::MAX)).collect();
            if at.iter().all(|&h| h == u32::MAX) {
                continue;
            }
            let c = &cells[k];
            let at_c = self.timed(Kind::Copy, || self.take_up(&at)).map_err(device)?;
            // The material reads the forces on the tick's words beside their tangents (the host's `energy_force_parts`).
            if material.is_some() {
                self.energy_force(field, words, c, held, fb, sites, regions)?;
            }
            // `w = s ⊙ λ'`.
            {
                let (mut sp, mut lp, mut hp, mut wp) = (c.scale.device_ptr(), rb.lambda.device_ptr(), at_c.device_ptr(), rb.wv.device_ptr());
                self.launch("field_energy_scaled", Self::cells((sites * dw) as u64), THREADS, &mut [arg(words), arg(&mut sp), arg(&mut lp), arg(&mut hp), arg(&mut wp)])?;
            }
            self.energy_tangent(field, words, c, held, &tb, rb.wv.device_ptr(), sites, regions)?;
            // The tick's letters: `R w`, the neighbours' `w`, and `Cᵀ w + δp'` on the moment.
            self.affine("field_affine_x64", words, words.read, NO_BIAS, words.rread, dw, dw, rb.wv.device_ptr(), dw, rb.lift.device_ptr(), dw, 0, false)?;
            self.transposed(words, mface, dw, m2, rb.wv.device_ptr(), dw, rb.chart.device_ptr(), false, false)?;
            {
                let (mut wp, mut yp, mut cp, mut pp, mut hp) = (rb.wv.device_ptr(), rb.lift.device_ptr(), rb.chart.device_ptr(), tb.cp.device_ptr(), at_c.device_ptr());
                let (mut op, mut bp, mut ap, mut mp) = (rb.own.device_ptr(), rb.before.device_ptr(), rb.after.device_ptr(), rb.moment.device_ptr());
                self.launch("field_energy_reverse_letters", Self::cells((sites * (dw + m2)) as u64), THREADS, &mut [arg(words), arg(&mut wp), arg(&mut yp), arg(&mut cp), arg(&mut pp), arg(&mut hp), arg(&mut op), arg(&mut bp), arg(&mut ap), arg(&mut mp)])?;
            }
            if let Some(mb) = material {
                self.energy_tick_material(field, words, c, held, fb, &tb, &rb, mb, &at_c, sites, regions)?;
            }
            // `λ = λ' + 2^(−h) (r̂⟨λ', F⟩/W + J δF)`.
            self.ratio_adjoint(words, c.read.device_ptr(), c.scale.device_ptr(), tb.t.device_ptr(), 0, rb.jt.device_ptr(), false)?;
            let (mut rp, mut fp, mut jp, mut hp, mut lp) = (c.read.device_ptr(), forces[k].device_ptr(), rb.jt.device_ptr(), at_c.device_ptr(), rb.lambda.device_ptr());
            self.launch("field_energy_lambda", Self::warps(sites as u64), THREADS, &mut [arg(words), arg(&mut rp), arg(&mut fp), arg(&mut jp), arg(&mut hp), arg(&mut lp)])?;
        }
        // The opening: `x⁰_t = E(u_t) + E₋(u_(t−1)) + E₊(u_(t+1)) + C s_t + b`.
        self.transposed(words, mface, dw, m2, rb.lambda.device_ptr(), dw, rb.chart.device_ptr(), false, false)?;
        let (mut lp, mut cp, mut op, mut bp, mut ap, mut mp) = (rb.lambda.device_ptr(), rb.chart.device_ptr(), rb.own.device_ptr(), rb.before.device_ptr(), rb.after.device_ptr(), rb.moment.device_ptr());
        self.launch("field_energy_opening_letters", Self::cells((sites * (dw + m2)) as u64), THREADS, &mut [arg(words), arg(&mut lp), arg(&mut cp), arg(&mut op), arg(&mut bp), arg(&mut ap), arg(&mut mp)])?;
        Ok(rb)
    }

    /// `g[r][base + o cols + i] += Σ_(t∈r) carry(sign y_t[o] x_t[i], shift)` over each region's sites (no `x`: the bias's
    /// `Σ carry(sign y_t[o], shift)`), `entry` the kinds (`_ll`, `_ls`, `_sl`) of `y` and `x`.
    #[allow(clippy::too_many_arguments)]
    fn material_outer(&self, entry: &'static str, words: &mut Words, mb: &EnergyMaterial<'c>, into_tick: bool, base: usize, rows: usize, cols: usize, y: u64, ys: usize, x: u64, xs: usize, shift: i32, sign: i32) -> Result<()> {
        let g = if into_tick { mb.tick.device_ptr() } else { mb.g.device_ptr() };
        let entries = rows as u64 * if x != 0 { cols as u64 } else { 1 };
        let tiles = (words.t as u64).div_ceil(OUTER_TILE);
        let (mut gp, mut len, mut b, mut r32, mut c32, mut yp, mut ysp, mut xp, mut xsp, mut sh, mut sg) = (g, mb.len as u64, base as u64, rows as u32, cols as u32, y, ys as u64, x, xs as u64, shift, sign);
        self.launch(entry, Self::cells(entries * tiles), THREADS, &mut [arg(words), arg(&mut gp), arg(&mut len), arg(&mut b), arg(&mut r32), arg(&mut c32), arg(&mut yp), arg(&mut ysp), arg(&mut xp), arg(&mut xsp), arg(&mut sh), arg(&mut sg)])
    }

    /// `g[r][base + row D + o] += carry(sign wgt src_(t+off)[o], shift)` over each site's letter rows.
    #[allow(clippy::too_many_arguments)]
    fn material_rows(&self, entry: &'static str, words: &mut Words, mb: &EnergyMaterial<'c>, into_tick: bool, base: usize, src: u64, off: i32, shift: i32, sign: i32) -> Result<()> {
        let g = if into_tick { mb.tick.device_ptr() } else { mb.g.device_ptr() };
        let (mut gp, mut len, mut b, mut sp, mut o, mut sh, mut sg) = (g, mb.len as u64, base as u64, src, off, shift, sign);
        self.launch(entry, Self::cells((words.t as u64) * words.d as u64), THREADS, &mut [arg(words), arg(&mut gp), arg(&mut len), arg(&mut b), arg(&mut sp), arg(&mut o), arg(&mut sh), arg(&mut sg)])
    }

    /// [definition; agent-inferred, November 7] **A stood tick's material** (the host's `energy_material`, its second part):
    /// `2^(−h) Σ_t (δF_words ⊗ r̂ + F_words ⊗ w)` on each chart and drive with the tangents' biases, the contraction's
    /// `δ(a · b)`, the letters' rows against `w` and `R w`, and the moment's chart against the moments, gathered a region and
    /// released by its halvings. The words' forces at the tick's cell are `fb`'s, their tangents `tb`'s, `w` and `R w` `rb`'s.
    #[allow(clippy::too_many_arguments)]
    fn energy_tick_material(&self, field: &Field, words: &mut Words, c: &EnergyCell<'c>, held: &EnergyHeld<'c>, fb: &EnergyForce<'c>, tb: &EnergyTangent<'c>, rb: &EnergyReverse<'c>, mb: &EnergyMaterial<'c>, at_c: &Pooled<'c, u32>, sites: usize, regions: usize) -> Result<()> {
        let d = field.declaration;
        let (dw, m2, f) = (d.width, 2 * d.complex(), d.contacts);
        let l = field.layout();
        let (mface, mface_bias, _) = moment_face(field);
        let card = self.card;
        card.zero_octets(&mb.tick, 0, 16 * regions * mb.len).map_err(device)?;
        Self::energy_point(words, c, held);
        let (read, wv) = (c.read.device_ptr(), rb.wv.device_ptr());
        for (w_, bias, fw, tw, rows) in [(l.q, l.q_bias, &fb.dq, &tb.cq, m2), (l.probe, l.probe_bias, &fb.dp, &tb.cp, m2), (l.a, l.a_bias, &fb.da, &tb.da, f), (l.b, l.b_bias, &fb.db, &tb.db, f)] {
            self.material_outer("field_energy_outer_ls", words, mb, true, w_, rows, dw, tw.device_ptr(), rows, read, dw, 0, 1)?;
            self.material_outer("field_energy_outer_ll", words, mb, true, w_, rows, dw, fw.device_ptr(), rows, wv, dw, -8, 1)?;
            self.material_outer("field_energy_outer_ll", words, mb, true, bias, rows, 1, tw.device_ptr(), rows, 0, 0, FACE_BITS as i32, 1)?;
        }
        {
            let (mut gp, mut len, mut pc, mut tap, mut tbp) = (mb.tick.device_ptr(), mb.len as u64, l.pair_c as u64, tb.ta.device_ptr(), tb.tb.device_ptr());
            self.launch("field_energy_pair_material", Self::cells((regions * f / 2) as u64), THREADS, &mut [arg(words), arg(&mut gp), arg(&mut len), arg(&mut pc), arg(&mut tap), arg(&mut tbp)])?;
        }
        self.material_outer("field_energy_outer_ll", words, mb, true, l.read, dw, dw, held.own.device_ptr(), dw, wv, dw, 0, 1)?;
        self.material_rows("field_energy_letter_rows_l", words, mb, true, l.enc, rb.lift.device_ptr(), 0, 0, 1)?;
        self.material_rows("field_energy_letter_rows_l", words, mb, true, l.before, wv, 1, 0, 1)?;
        self.material_rows("field_energy_letter_rows_l", words, mb, true, l.after, wv, -1, 0, 1)?;
        self.material_outer("field_energy_outer_ll", words, mb, true, mface as usize, dw, m2, wv, dw, words.moment, m2, 0, 1)?;
        self.material_outer("field_energy_outer_ll", words, mb, true, mface_bias as usize, dw, 1, wv, dw, 0, 0, FACE_BITS as i32, 1)?;
        let (mut tp, mut gp, mut len, mut hp) = (mb.tick.device_ptr(), mb.g.device_ptr(), mb.len as u64, at_c.device_ptr());
        self.launch("field_energy_tick_release", Self::cells((regions * mb.len) as u64), THREADS, &mut [arg(words), arg(&mut tp), arg(&mut gp), arg(&mut len), arg(&mut hp)])
    }

    /// [definition; agent-inferred, November 7] **The energy's material covector a region** (the host's `Field::energy_material`):
    /// the explicit `∂Φ/∂θ` at the last state (every term minus the force's: each chart's and drive's word force against the
    /// reads with its bias, the contraction against `a · b`, the letters' rows against the lift and the neighbours' reads, the
    /// read matrix and its bias against the letter, the moment's chart against the moments), the stood ticks
    /// ([`CardField::energy_tick_material`] inside the reverse), the opening's `(∂x⁰/∂θ)ᵀ λ⁰`, and the moments' covector `−(Cᵀ r̂ +
    /// δp − m)` (the face's negated) back through the strands; each region's on `2^(−40)`, theta long.
    #[allow(clippy::too_many_arguments, clippy::type_complexity)]
    fn energy_material_of(&self, field: &Field, words: &mut Words, cells: &[EnergyCell<'c>], forces: &[Pooled<'c, i64>], halvings: &[Vec<Option<u32>>], held: &EnergyHeld<'c>, fb: &EnergyForce<'c>, sites: usize, pairs: usize, regions: usize) -> Result<Vec<Vec<i128>>> {
        let card = self.card;
        let d = field.declaration;
        let (dw, m2, f) = (d.width, 2 * d.complex(), d.contacts);
        let l = field.layout();
        let (mface, mface_bias, _) = moment_face(field);
        let len = field.theta.len();
        let zeroed = |n: usize| self.timed(Kind::Alloc, || self.take_zeroed::<i128>(n.max(1))).map_err(device);
        let mb = EnergyMaterial { g: zeroed(regions * len)?, tick: zeroed(regions * len)?, len };
        let last = cells.last().ok_or(TowerError::Refused("an energy forward with no opening"))?;
        // 1. The explicit `∂Φ/∂θ` at the last state.
        self.energy_force(field, words, last, held, fb, sites, regions)?;
        let read = last.read.device_ptr();
        for (w_, bias, fw, rows) in [(l.q, l.q_bias, &fb.dq, m2), (l.probe, l.probe_bias, &fb.dp, m2), (l.a, l.a_bias, &fb.da, f), (l.b, l.b_bias, &fb.db, f)] {
            self.material_outer("field_energy_outer_ls", words, &mb, false, w_, rows, dw, fw.device_ptr(), rows, read, dw, 0, -1)?;
            self.material_outer("field_energy_outer_ll", words, &mb, false, bias, rows, 1, fw.device_ptr(), rows, 0, 0, FACE_BITS as i32, -1)?;
        }
        {
            let (mut gp, mut ln, mut pc, mut none_a, mut none_b) = (mb.g.device_ptr(), len as u64, l.pair_c as u64, 0u64, 0u64);
            self.launch("field_energy_pair_material", Self::cells((regions * f / 2) as u64), THREADS, &mut [arg(words), arg(&mut gp), arg(&mut ln), arg(&mut pc), arg(&mut none_a), arg(&mut none_b)])?;
        }
        self.material_outer("field_energy_outer_ls", words, &mb, false, l.read, dw, dw, held.own.device_ptr(), dw, read, dw, 8, -1)?;
        self.material_outer("field_energy_outer_ll", words, &mb, false, l.lift_bias, dw, 1, held.own.device_ptr(), dw, 0, 0, MATERIAL_BITS as i32, -1)?;
        self.material_rows("field_energy_letter_rows_l", words, &mb, false, l.enc, last.lift.device_ptr(), 0, 8, -1)?;
        self.material_rows("field_energy_letter_rows_s", words, &mb, false, l.before, read, 1, 8, -1)?;
        self.material_rows("field_energy_letter_rows_s", words, &mb, false, l.after, read, -1, 8, -1)?;
        {
            let (mut gp, mut ln) = (mb.g.device_ptr(), len as u64);
            self.launch("field_energy_letter_bias", Self::cells(sites as u64), THREADS, &mut [arg(words), arg(&mut gp), arg(&mut ln)])?;
        }
        self.material_outer("field_energy_outer_sl", words, &mb, false, mface as usize, dw, m2, read, dw, words.moment, m2, 8, -1)?;
        self.material_outer("field_energy_outer_sl", words, &mb, false, mface_bias as usize, dw, 1, read, dw, 0, 0, MATERIAL_BITS as i32, -1)?;
        // The probes' force at the last state, held for the moments' covector (the reverse's ticks read the force again).
        let dp_last = self.timed(Kind::Alloc, || self.take::<i64>((sites * m2).max(1))).map_err(device)?;
        card.copy_within(&fb.dp, 0, &dp_last, 0, sites * m2).map_err(device)?;
        // 2. The ticks, back from `λ^K = −J F^K`, each stood tick's material gathered and released.
        let rb = self.energy_reverse(field, words, cells, forces, halvings, held, fb, sites, pairs, regions, Some(&mb))?;
        Self::energy_point(words, last, held);
        // 3. The opening: `x⁰_t = E(u_t) + E₋(u_(t−1)) + E₊(u_(t+1)) + C s_t + b`.
        let lambda = rb.lambda.device_ptr();
        self.material_rows("field_energy_letter_rows_l", words, &mb, false, l.enc, lambda, 0, 0, 1)?;
        self.material_rows("field_energy_letter_rows_l", words, &mb, false, l.before, lambda, 1, 0, 1)?;
        self.material_rows("field_energy_letter_rows_l", words, &mb, false, l.after, lambda, -1, 0, 1)?;
        self.material_outer("field_energy_outer_ll", words, &mb, false, mface as usize, dw, m2, lambda, dw, words.moment, m2, 0, 1)?;
        self.material_outer("field_energy_outer_ll", words, &mb, false, mface_bias as usize, dw, 1, lambda, dw, 0, 0, FACE_BITS as i32, 1)?;
        // The moments' covector `−(Cᵀ r̂ + δp − m)` back through the strands' moment encodings.
        let tm = d.moment_modes();
        if tm > 0 {
            let dm = zeroed(sites * m2)?;
            let (mut mp, mut rp, mut dpp, mut tmp, mut dmp) = (mface, read, dp_last.device_ptr(), rb.moment.device_ptr(), dm.device_ptr());
            self.launch("field_energy_dm", Self::cells((sites * m2) as u64), THREADS, &mut [arg(words), arg(&mut mp), arg(&mut rp), arg(&mut dpp), arg(&mut tmp), arg(&mut dmp)])?;
            let (mut dmp, mut n) = (dm.device_ptr(), (sites * m2) as u64);
            self.launch("field_energy_negate_wide", Self::cells(n), THREADS, &mut [arg(words), arg(&mut dmp), arg(&mut n)])?;
            let back = self.moment_strands_back(field, words, dm.device_ptr(), regions, sites)?;
            let (mut bb, mut ba, mut tm32, mut dbp, mut dap, mut gp, mut ln) = (l.moment_before as u64, l.moment_after as u64, tm as u32, back.d_before.device_ptr(), back.d_after.device_ptr(), mb.g.device_ptr(), len as u64);
            self.launch("field_energy_strand_material", Self::cells((sites * tm) as u64), THREADS, &mut [arg(words), arg(&mut bb), arg(&mut ba), arg(&mut tm32), arg(&mut dbp), arg(&mut dap), arg(&mut gp), arg(&mut ln)])?;
        }
        let g = self.timed(Kind::Copy, || card.fetch_range(&mb.g, 0, regions * len)).map_err(device)?;
        Ok(g.chunks_exact(len).map(<[i128]>::to_vec).collect())
    }

    /// [definition; the unified-theory reading of November 7, 00:02] **A base's definite flags held** (the host's
    /// `Held::definite` under `base`): where they differ from the batch's own, each region's definite and open lists are read
    /// again from them (the open lists over the batch's own windows, as `stage` reads them) and the words point at them.
    fn energy_hold_definite(&self, words: &mut Words, regions: &[Region], st: &Staged<'c>, definite: &[u8], ticks: usize) -> Result<Option<Pooled<'c, u8>>> {
        if definite == st.definite.as_slice() {
            return Ok(None);
        }
        let (mut dlist, mut dstart, mut olist, mut ostart) = (Vec::<u32>::new(), Vec::<u32>::new(), Vec::<u32>::new(), Vec::<u32>::new());
        for (r, region) in regions.iter().enumerate() {
            let window = region.window(ticks);
            dstart.push(dlist.len() as u32);
            ostart.push(olist.len() as u32);
            let first = st.region_off[r] as usize;
            for t in 0..region.classes.len() {
                if definite[first + t] != 0 {
                    dlist.push(t as u32);
                } else if window.as_ref().is_none_or(|w| w[t]) {
                    olist.push(t as u32);
                }
            }
        }
        dstart.push(dlist.len() as u32);
        ostart.push(olist.len() as u32);
        for list in [&mut dlist, &mut olist] {
            if list.is_empty() {
                list.push(0);
            }
        }
        let mut pack = Packed::default();
        let (def_at, dlist_at, dstart_at, olist_at, ostart_at) = (pack.put(definite), pack.put(&dlist), pack.put(&dstart), pack.put(&olist), pack.put(&ostart));
        let tables = self.timed(Kind::Copy, || self.take_up(&pack.bytes)).map_err(device)?;
        let base = tables.device_ptr();
        (words.definite, words.dlist, words.dstart, words.olist, words.ostart) = (base + def_at, base + dlist_at, base + dstart_at, base + olist_at, base + ostart_at);
        Ok(Some(tables))
    }

    /// [definition; the unified-theory reading of November 6, 22:52] **One batch's energy forward** (the host's
    /// `energy_relax` and `energy_faces`, region by region in lockstep): the opening, the held letters and classes, `K` ticks
    /// of certified descent, the reverse through the ticks and the opening, and each unresolved site's face as the energy's
    /// total derivative on its letter at the last state.
    #[allow(clippy::type_complexity)]
    /// [definition; the unified-theory reading of November 7, 23:34] **The width law's lists on the card**: the opening's key
    /// and probe words read on the card (as `energy_cell` reads them), fetched, each head's and region's leaves built on the
    /// host's lanes (`ClassLists::widened`, the host's `energy_classes`), and uploaded in `field_classes`'s layout under the
    /// width law's bounds: `3^b + 2(n − b)⌊S/(cap + 1)⌋` leaves for the batch's longest region `S`, and a receiver's probes at a
    /// stride of `2^n`. The words carry the bounds (`nclasses`, `pstride`). The round trip prints as `FIELD_WIDEN_LISTS`.
    #[allow(clippy::too_many_arguments)]
    fn energy_widened_lists(&self, field: &Field, words: &mut Words, st: &Staged<'c>, lengths: &[usize], pairs: usize, rn: usize) -> Result<EnergyLists<'c>> {
        let card = self.card;
        let d = field.declaration;
        let cap = field.widen.ok_or(TowerError::Refused("a widened list without the width law"))?;
        let (dw, m, n, heads) = (d.width, d.complex(), d.modes, d.heads);
        let m2 = 2 * m;
        let (b, sites) = (d.class_trits(), st.sites);
        let started = std::time::Instant::now();
        // The opening's words, read on a cell of their own.
        let c = self.energy_cell_alloc(field, sites, pairs, rn)?;
        card.copy_within(&st.x, 0, &c.x, 0, sites * dw).map_err(device)?;
        (words.x, words.qkv, words.pr) = (c.x.device_ptr(), c.qkv.device_ptr(), c.pr.device_ptr());
        self.chart(words, c.x.device_ptr(), &c.read, &c.scale, false)?;
        self.affine("field_affine_x32", words, words.q, words.q_bias, words.rq, m2, dw, c.read.device_ptr(), dw, c.qkv.device_ptr(), 2 * m2, 0, false)?;
        self.affine("field_affine_x32", words, words.probe, words.probe_bias, words.rprobe, m2, dw, c.read.device_ptr(), dw, c.pr.device_ptr(), m2, 0, false)?;
        let mut prp = c.pr.device_ptr();
        self.launch("field_moment_add_probe", Self::cells((sites * m2) as u64), THREADS, &mut [arg(words), arg(&mut prp)])?;
        let qkv = self.timed(Kind::Copy, || card.fetch_range(&c.qkv, 0, sites * 2 * m2)).map_err(device)?;
        let pr = self.timed(Kind::Copy, || card.fetch_range(&c.pr, 0, sites * m2)).map_err(device)?;
        let fetched = started.elapsed();
        let firsts: Vec<usize> = lengths.iter().scan(0usize, |at, &len| { let f = *at; *at += len; Some(f) }).collect();
        let longest = lengths.iter().copied().max().unwrap_or(0);
        let classes = 3usize.pow(b as u32) + 2 * n.saturating_sub(b) * (longest / (cap + 1));
        let pstride = 1usize << n;
        // Each head and region built on the host's lanes.
        use rayon::prelude::*;
        let definite_all: &[u8] = &st.definite;
        let built: Vec<(usize, usize, holonics::hnn::tower::field::ClassLists, usize)> = (0..heads * rn)
            .into_par_iter()
            .map(|u| {
                let (h, r) = (u / rn, u % rn);
                let (first, len) = (firsts[r], lengths[r]);
                let keys: Vec<Vec<(i64, i64)>> = (first..first + len).map(|g| (0..n).map(|li| (qkv[g * 2 * m2 + h * n + li], qkv[g * 2 * m2 + m + h * n + li])).collect()).collect();
                let probes: Vec<Vec<(i64, i64)>> = (first..first + len).map(|g| (0..n).map(|li| (pr[g * m2 + h * n + li], pr[g * m2 + m + h * n + li])).collect()).collect();
                let definite: Vec<bool> = (first..first + len).map(|g| definite_all[g] != 0).collect();
                let (lists, leaves) = holonics::hnn::tower::field::ClassLists::widened(&keys, &probes, definite, b, cap);
                (h, r, lists, leaves)
            })
            .collect();
        let built_at = started.elapsed();
        if let Some(&(_, _, _, leaves)) = built.iter().find(|(.., leaves)| *leaves > classes) {
            return Err(TowerError::Refused(if leaves > classes { "a widened region with more leaves than the width law's bound" } else { "" }));
        }
        // `field_classes`'s layout: `cls`, `pn`, `members` `[h][t]`, `pcls` and `pmem` at the stride, `class_off` `[h][r][2C + 1]`,
        // `poff` `[h][r][C + 1]`.
        let t = sites;
        let mut cls = vec![0u32; heads * t];
        let mut pn = vec![0u32; heads * t];
        let mut members = vec![0u32; heads * t];
        let mut pcls = vec![0u32; heads * t * pstride];
        let mut pmem = vec![0u32; heads * t * pstride];
        let mut class_off = vec![0u32; heads * rn * (2 * classes + 1)];
        let mut poff = vec![0u32; heads * rn * (classes + 1)];
        for (h, r, lists, leaves) in &built {
            let (first, len) = (firsts[*r], lengths[*r]);
            let off = &mut class_off[(h * rn + r) * (2 * classes + 1)..(h * rn + r + 1) * (2 * classes + 1)];
            off[..=2 * leaves].copy_from_slice(&lists.off[..=2 * leaves]);
            let total = lists.off[2 * leaves];
            off[2 * leaves + 1..].iter_mut().for_each(|o| *o = total);
            members[h * t + first..h * t + first + len].copy_from_slice(&lists.members);
            let mut count = vec![0u32; classes + 1];
            for i in 0..len {
                let g = first + i;
                cls[h * t + g] = lists.class[i];
                if lists.definite[i] {
                    let row = std::iter::once(lists.probe_class[i]).chain(lists.probes[i].iter().copied()).collect::<Vec<u32>>();
                    // The kernels hold a row's probed classes in shared memory, at most 128 (`MAX_PROBES` + its own).
                    if row.len() > pstride || row.len() > 128 {
                        return Err(TowerError::Refused("a widened receiver with more probes than a row holds (MAX_PROBES)"));
                    }
                    pn[h * t + g] = row.len() as u32;
                    for (k, &q) in row.iter().enumerate() {
                        pcls[(h * t + g) * pstride + k] = q;
                        count[q as usize] += 1;
                    }
                }
            }
            let po = &mut poff[(h * rn + r) * (classes + 1)..(h * rn + r + 1) * (classes + 1)];
            let mut at = 0u32;
            for q in 0..classes {
                po[q] = at;
                at += count[q];
            }
            po[classes] = at;
            let mut fill: Vec<u32> = po[..classes].to_vec();
            let block = (h * t + first) * pstride;
            for i in 0..len {
                let g = first + i;
                for k in 0..pn[h * t + g] as usize {
                    let q = pcls[(h * t + g) * pstride + k] as usize;
                    pmem[block + fill[q] as usize] = i as u32;
                    fill[q] += 1;
                }
            }
        }
        let up = |v: &[u32]| self.timed(Kind::Copy, || self.take_up(v)).map_err(device);
        let lists = EnergyLists { cls: up(&cls)?, class_off: up(&class_off)?, members: up(&members)?, pn: up(&pn)?, pcls: up(&pcls)?, poff: up(&poff)?, pmem: up(&pmem)?, definite: st.definite.clone(), lengths: lengths.to_vec() };
        (words.nclasses, words.pstride) = (classes as u32, pstride as u32);
        let receivers: Vec<u32> = pn.iter().copied().filter(|&k| k > 0).collect();
        println!(
            "FIELD_WIDEN_LISTS regions={rn} sites={sites} heads={heads} probes_most={} probes_mean_milli={} leaves_most={} bound={classes} fetch_us={} build_us={} upload_us={} threads={}",
            receivers.iter().max().map_or(0, |&k| k - 1),
            receivers.iter().map(|&k| (k - 1) as u64).sum::<u64>() * 1000 / receivers.len().max(1) as u64,
            built.iter().map(|(.., l)| *l).max().unwrap_or(0),
            fetched.as_micros(),
            (built_at - fetched).as_micros(),
            (started.elapsed() - built_at).as_micros(),
            rayon::current_num_threads()
        );
        Ok(lists)
    }

    fn energy_batch(&self, field: &Field, regions: &[Region], words: &mut Words, plan: EnergyPlan<'_, 'c>) -> Result<(Vec<Vec<Option<TowerFace>>>, Vec<Vec<Option<Vec<i64>>>>, EnergyPass<'c>)> {
        let card = self.card;
        let d = field.declaration;
        let (dw, m, n, f, a, heads) = (d.width, d.complex(), d.modes, d.contacts, d.alphabet, d.heads);
        let (m2, span) = (2 * m, 2 * n);
        let l = field.layout();
        let st = self.stage(regions, a, dw, d.ticks, words)?;
        let (sites, pairs, rn) = (st.sites, st.pairs, regions.len());
        let i64s = |len: usize| self.timed(Kind::Alloc, || self.take::<i64>(len.max(1))).map_err(device);
        // The turned heads' clocks; an energy field's are plain (the host's refusal).
        let paced = d.paced_heads();
        let kappa = i64s(paced * sites)?;
        let tau = i64s(paced * sites)?;
        let sigma = i64s(paced * sites)?;
        let plain = self.timed(Kind::Alloc, || self.take::<u8>((paced * rn).max(1))).map_err(device)?;
        let pframe = i64s(2 * paced * sites * n)?;
        (words.kappa, words.tau, words.sigma, words.plain, words.pframe) = (kappa.device_ptr(), tau.device_ptr(), sigma.device_ptr(), plain.device_ptr(), pframe.device_ptr());
        (words.blank_rate, words.blank_masses, words.blank_totals) = (0, 0, 0);
        self.launch("field_open", Self::cells((sites * dw) as u64), THREADS, &mut [arg(words)])?;
        if paced > 0 {
            self.launch("field_paces", Self::cells((paced * rn) as u64), THREADS, &mut [arg(words)])?;
            self.launch("field_pframes", Self::cells((paced * sites * n) as u64), THREADS, &mut [arg(words)])?;
            let flags = self.timed(Kind::Copy, || card.fetch_range(&plain, 0, paced * rn)).map_err(device)?;
            if flags.iter().any(|&p| p == 0) {
                return Err(TowerError::Refused("an energy field read with a clock that is not plain (its letters' force through the frames is not built)"));
            }
        }
        // The moments, once for the pass, and their term in the face, held and added into the opening (the host's `open`).
        let moment = self.timed(Kind::Alloc, || self.take_zeroed::<i64>((sites * m2).max(1))).map_err(device)?;
        words.moment = moment.device_ptr();
        self.moments(field, words, rn, sites)?;
        let (mface, mface_bias, rmface) = moment_face(field);
        let mterm = i64s(sites * dw)?;
        self.affine("field_affine_x64", words, mface, mface_bias, rmface, dw, m2, words.moment, m2, mterm.device_ptr(), dw, 0, false)?;
        self.affine("field_affine_x64", words, mface, mface_bias, rmface, dw, m2, words.moment, m2, 0, dw, words.x, false)?;
        // What the ticks hold: the letters, their force, the pair's contraction, and the class lists (read at the opening).
        let classes = d.classes();
        let probe_stride = 1usize << d.class_trits();
        let u32s = |len: usize| self.timed(Kind::Alloc, || self.take::<u32>(len.max(1))).map_err(device);
        // A base's supports are held where the plan gives one (its layout the batch's), its definite flags with them;
        // otherwise the batch's own, read at its opening.
        let lengths: Vec<usize> = regions.iter().map(|r| r.classes.len()).collect();
        let (lists, _held_definite) = match plan.base {
            Some(base) => {
                if base.lengths != lengths {
                    return Err(TowerError::Refused("a batch read under a base whose regions are not its own layout"));
                }
                (None, self.energy_hold_definite(words, regions, &st, &base.definite, d.ticks)?)
            }
            // [definition; the unified-theory reading of November 7, 23:34] Under the width law the lists are built on the host
            // from the opening's words (`ClassLists::widened`, the host's own lists) and laid out as `field_classes` lays them.
            None if field.widen.is_some() => (Some(self.energy_widened_lists(field, words, &st, &lengths, pairs, rn)?), None),
            None => (
                Some(EnergyLists {
                    cls: u32s(heads * sites)?,
                    class_off: u32s(heads * rn * (2 * classes + 1))?,
                    members: u32s(heads * sites)?,
                    pn: u32s(heads * sites)?,
                    pcls: u32s(heads * sites * probe_stride)?,
                    poff: u32s(heads * rn * (classes + 1))?,
                    pmem: u32s(heads * sites * probe_stride)?,
                    definite: st.definite.clone(),
                    lengths,
                }),
                None,
            ),
        };
        let held = EnergyHeld {
            lists: match (&lists, plan.base) {
                (Some(own), _) => own.pointers(),
                (None, Some(base)) => base.pointers(),
                (None, None) => unreachable!("a batch's supports are its own or a base's"),
            },
            own: i64s(sites * dw)?,
            before: i64s(sites * dw)?,
            after: i64s(sites * dw)?,
            bias: i64s(sites)?,
            mterm,
            lf: i64s(sites * dw)?,
            dc: i64s(sites * f)?,
            dyh0: self.timed(Kind::Alloc, || self.take_zeroed::<i64>((heads * sites * span).max(1))).map_err(device)?,
        };
        {
            let (mut op, mut bp, mut ap, mut cp) = (held.own.device_ptr(), held.before.device_ptr(), held.after.device_ptr(), held.bias.device_ptr());
            self.launch("field_energy_letters", Self::cells((sites * dw) as u64), THREADS, &mut [arg(words), arg(&mut op), arg(&mut bp), arg(&mut ap), arg(&mut cp)])?;
            let (mut op, mut bp, mut ap, mut mp, mut lp) = (held.own.device_ptr(), held.before.device_ptr(), held.after.device_ptr(), held.mterm.device_ptr(), held.lf.device_ptr());
            self.launch("field_energy_letter_force", Self::cells((sites * dw) as u64), THREADS, &mut [arg(words), arg(&mut op), arg(&mut bp), arg(&mut ap), arg(&mut mp), arg(&mut lp)])?;
            let (mut pc, mut dcp) = (l.pair_c as u64, held.dc.device_ptr());
            self.launch("field_energy_pair_c", Self::cells((sites * f) as u64), THREADS, &mut [arg(words), arg(&mut pc), arg(&mut dcp)])?;
        }
        let fb = EnergyForce {
            dq: i64s(sites * m2)?,
            dp: i64s(sites * m2)?,
            dv: i64s(sites * m2)?,
            ds: i64s(pairs)?,
            cv: self.timed(Kind::Alloc, || self.take::<i128>(((sites + rn) * span).max(1))).map_err(device)?,
            cw: self.timed(Kind::Alloc, || self.take::<i128>(((sites + rn) * span).max(1))).map_err(device)?,
            da: i64s(sites * f)?,
            db: i64s(sites * f)?,
            force: i64s(sites * dw)?,
        };
        let state = &st.x;
        self.mark("energy_setup");
        // The opening's read, its classes held.
        let opening = self.energy_cell_alloc(field, sites, pairs, rn)?;
        card.copy_within(state, 0, &opening.x, 0, sites * dw).map_err(device)?;
        // Under the width law the lists were built on the host (`energy_widened_lists`); `field_classes` does not run.
        self.energy_cell(field, words, &opening, &held, plan.base.is_none() && field.widen.is_none(), sites, rn)?;
        let read0 = self.energy_reads(&opening, rn)?;
        let mut cells = vec![opening];
        let mut now: Vec<Read> = read0.clone();
        let mut reads = vec![1u64; rn];
        let mut met: Vec<u64> = read0.iter().map(|r| r.pairs).collect();
        let mut halvings: Vec<Vec<Option<u32>>> = vec![Vec::with_capacity(d.ticks); rn];
        let mut active = vec![true; rn];
        let mut first = vec![FIRST_HALVINGS; rn];
        let mut rereads = 0u64;
        let mut forces: Vec<Pooled<'c, i64>> = Vec::with_capacity(d.ticks);
        // A replay steps each region at the halvings it is given, uncertified (the host's `energy_relax` with `replay`): every
        // read counted, a region done where its halvings end or rest.
        if let Some(replay) = plan.replay {
            if replay.len() != rn {
                return Err(TowerError::Refused("a replay's halvings that are not one a region"));
            }
            let ticks = replay.iter().map(Vec::len).max().unwrap_or(0);
            for k in 0..ticks {
                let at: Vec<u32> = (0..rn)
                    .map(|r| match replay[r].get(k).copied() {
                        Some(Some(h)) if active[r] => h,
                        _ => {
                            active[r] = false;
                            u32::MAX
                        }
                    })
                    .collect();
                if at.iter().all(|&h| h == u32::MAX) {
                    break;
                }
                let current = cells.last().ok_or(TowerError::Refused("an energy forward with no opening"))?;
                self.energy_force(field, words, current, &held, &fb, sites, rn)?;
                let kept_force = i64s(sites * dw)?;
                card.copy_within(&fb.force, 0, &kept_force, 0, sites * dw).map_err(device)?;
                forces.push(kept_force);
                let candidate = self.energy_cell_alloc(field, sites, pairs, rn)?;
                let at_c = self.timed(Kind::Copy, || self.take_up(&at)).map_err(device)?;
                {
                    let (mut xp, mut sp, mut fp, mut hp, mut np, mut ep) = (state.device_ptr(), current.scale.device_ptr(), fb.force.device_ptr(), at_c.device_ptr(), candidate.x.device_ptr(), candidate.sums.device_ptr());
                    self.launch("field_energy_step", Self::cells((sites * dw) as u64), THREADS, &mut [arg(words), arg(&mut xp), arg(&mut sp), arg(&mut fp), arg(&mut hp), arg(&mut np), arg(&mut ep)])?;
                }
                self.energy_cell(field, words, &candidate, &held, false, sites, rn)?;
                let next = self.energy_reads(&candidate, rn)?;
                for r in (0..rn).filter(|&r| at[r] != u32::MAX) {
                    reads[r] += 1;
                    met[r] += next[r].pairs;
                    halvings[r].push(Some(at[r]));
                    now[r] = next[r];
                }
                // Every region stands at the candidate's state (a region done this tick was copied there).
                card.copy_within(&candidate.x, 0, state, 0, sites * dw).map_err(device)?;
                cells.push(candidate);
            }
        }
        for _ in 0..if plan.replay.is_some() { 0 } else { d.ticks } {
            if !active.iter().any(|&on| on) {
                break;
            }
            let current = cells.last().ok_or(TowerError::Refused("an energy forward with no opening"))?;
            self.energy_force(field, words, current, &held, &fb, sites, rn)?;
            // The tick's force, kept for the reverse (the host's `Step::force`).
            let kept_force = i64s(sites * dw)?;
            card.copy_within(&fb.force, 0, &kept_force, 0, sites * dw).map_err(device)?;
            forces.push(kept_force);
            let ticking = active.clone();
            let mut h: Vec<u32> = first.clone();
            let mut searching = active.clone();
            let mut stood: Vec<Option<u32>> = vec![None; rn];
            // Whether the last round's candidate is every region's read at its state (no region rejected there).
            let mut whole = false;
            let mut kept: Option<EnergyCell<'c>> = None;
            let mut any = false;
            while searching.iter().any(|&on| on) {
                let current = cells.last().ok_or(TowerError::Refused("an energy forward with no opening"))?;
                let candidate = self.energy_cell_alloc(field, sites, pairs, rn)?;
                let at: Vec<u32> = (0..rn).map(|r| if searching[r] { h[r] } else { u32::MAX }).collect();
                let at_c = self.timed(Kind::Copy, || self.take_up(&at)).map_err(device)?;
                {
                    let (mut xp, mut sp, mut fp, mut hp, mut np, mut ep) = (state.device_ptr(), current.scale.device_ptr(), fb.force.device_ptr(), at_c.device_ptr(), candidate.x.device_ptr(), candidate.sums.device_ptr());
                    self.launch("field_energy_step", Self::cells((sites * dw) as u64), THREADS, &mut [arg(words), arg(&mut xp), arg(&mut sp), arg(&mut fp), arg(&mut hp), arg(&mut np), arg(&mut ep)])?;
                }
                self.energy_cell(field, words, &candidate, &held, false, sites, rn)?;
                let next = self.energy_reads(&candidate, rn)?;
                let mut accept = vec![0u8; rn];
                whole = true;
                let round = searching.clone();
                for r in (0..rn).filter(|&r| round[r]) {
                    if !next[r].moved {
                        // The step moves nothing: the state rests (no read is counted).
                        searching[r] = false;
                        active[r] = false;
                        continue;
                    }
                    reads[r] += 1;
                    met[r] += next[r].pairs;
                    // The fall is certified past the two reads' summed reading error, one unit of `2^(−32)` a logarithm.
                    let slack = (now[r].logs + next[r].logs) as i128 + 2;
                    if next[r].phi + slack <= now[r].phi {
                        accept[r] = 1;
                        now[r] = next[r];
                        stood[r] = Some(h[r]);
                        first[r] = h[r].saturating_sub(1);
                        searching[r] = false;
                        any = true;
                    } else {
                        whole = false;
                        h[r] += 1;
                        if h[r] > MOST_HALVINGS {
                            searching[r] = false;
                            active[r] = false;
                        }
                    }
                }
                if accept.iter().any(|&on| on != 0) {
                    let accept_c = self.timed(Kind::Copy, || self.take_up(&accept)).map_err(device)?;
                    let (mut np, mut xp, mut ap) = (candidate.x.device_ptr(), state.device_ptr(), accept_c.device_ptr());
                    self.launch("field_energy_accept", Self::cells((sites * dw) as u64), THREADS, &mut [arg(words), arg(&mut np), arg(&mut xp), arg(&mut ap)])?;
                }
                kept = Some(candidate);
            }
            for r in (0..rn).filter(|&r| ticking[r]) {
                halvings[r].push(stood[r]);
            }
            if any {
                // The tick's last states: the last candidate where every region stands at it, else read again (the same bits).
                let next = match kept.filter(|_| whole) {
                    Some(c) => c,
                    None => {
                        rereads += 1;
                        let c = self.energy_cell_alloc(field, sites, pairs, rn)?;
                        card.copy_within(state, 0, &c.x, 0, sites * dw).map_err(device)?;
                        self.energy_cell(field, words, &c, &held, false, sites, rn)?;
                        c
                    }
                };
                cells.push(next);
            }
        }
        self.mark("energy_ticks");
        let reads = (0..rn).map(|r| EnergyRead { opening: read0[r].phi, last: now[r].phi, halvings: halvings[r].clone(), reads: reads[r], pairs: met[r] }).collect();
        // The energy's material covector a region (`Field::energy_material`).
        if plan.material {
            let material = self.energy_material_of(field, words, &cells, &forces, &halvings, &held, &fb, sites, pairs, rn)?;
            self.status(&st.status)?;
            return Ok((Vec::new(), Vec::new(), EnergyPass { cells, reads, rereads, lists, material }));
        }
        // A read of the energy alone (a square's `G`) ends at its last state.
        if !plan.faces {
            self.status(&st.status)?;
            return Ok((Vec::new(), Vec::new(), EnergyPass { cells, reads, rereads, lists, material: Vec::new() }));
        }
        // The faces: each unresolved site's letter force at the last state, with the reverse's letters' covectors through
        // the ticks that stood and the opening (the total derivative, the host's `energy_faces`).
        let last = cells.last().ok_or(TowerError::Refused("an energy forward with no opening"))?;
        self.energy_force(field, words, last, &held, &fb, sites, rn)?;
        let rb = self.energy_reverse(field, words, &cells, &forces, &halvings, &held, &fb, sites, pairs, rn, None)?;
        self.mark("energy_reverse");
        let z = i64s(sites * a)?;
        let masses = self.timed(Kind::Alloc, || self.take::<u64>((sites * a).max(1))).map_err(device)?;
        let totals = self.timed(Kind::Alloc, || self.take_zeroed::<i128>(sites.max(1))).map_err(device)?;
        {
            let (mut enc, mut cb, mut yp, mut zp) = (words.enc, words.read_bias, last.lift.device_ptr(), z.device_ptr());
            self.launch("field_tied_face", Self::cells((sites * a) as u64), THREADS, &mut [arg(words), arg(&mut enc), arg(&mut cb), arg(&mut yp), arg(&mut zp)])?;
        }
        let tm = d.moment_modes();
        let dm = self.timed(Kind::Alloc, || self.take::<i128>((sites * m2).max(1))).map_err(device)?;
        let back = if tm > 0 {
            let (mut mp, mut rp, mut dpp, mut tmp, mut dmp) = (mface, last.read.device_ptr(), fb.dp.device_ptr(), rb.moment.device_ptr(), dm.device_ptr());
            self.launch("field_energy_dm", Self::cells((sites * m2) as u64), THREADS, &mut [arg(words), arg(&mut mp), arg(&mut rp), arg(&mut dpp), arg(&mut tmp), arg(&mut dmp)])?;
            Some(self.moment_strands_back(field, words, dm.device_ptr(), rn, sites)?)
        } else {
            None
        };
        {
            let (mut rp, mut dbp, mut dap) = (last.read.device_ptr(), back.as_ref().map_or(0, |b| b.d_before.device_ptr()), back.as_ref().map_or(0, |b| b.d_after.device_ptr()));
            let (mut tm32, mut mb, mut ma, mut zp) = (tm as u32, l.moment_before as u64, l.moment_after as u64, z.device_ptr());
            let (mut op, mut bp, mut ap, mut ft) = (rb.own.device_ptr(), rb.before.device_ptr(), rb.after.device_ptr(), l.face_temper as u64);
            self.launch("field_energy_face", Self::cells((sites * a) as u64), THREADS, &mut [arg(words), arg(&mut rp), arg(&mut dbp), arg(&mut dap), arg(&mut tm32), arg(&mut mb), arg(&mut ma), arg(&mut op), arg(&mut bp), arg(&mut ap), arg(&mut ft), arg(&mut zp)])?;
        }
        // The cavity field (§15.3): a carried site's read less its own echo.
        if st.echo_has.iter().any(|&on| on != 0) {
            let mut zp = z.device_ptr();
            self.launch("field_echo_apply", Self::cells((sites * a) as u64), THREADS, &mut [arg(words), arg(&mut zp)])?;
        }
        {
            let (mut zp, mut mp, mut tp) = (z.device_ptr(), masses.device_ptr(), totals.device_ptr());
            self.launch("field_face", Self::warps(sites as u64), THREADS, &mut [arg(words), arg(&mut zp), arg(&mut mp), arg(&mut tp)])?;
        }
        self.status(&st.status)?;
        self.mark("energy_faces");
        let ms = self.timed(Kind::Copy, || card.fetch_range(&masses, 0, sites * a)).map_err(device)?;
        let ts = self.timed(Kind::Copy, || card.fetch_range(&totals, 0, sites)).map_err(device)?;
        let zs = self.timed(Kind::Copy, || card.fetch_range(&z, 0, sites * a)).map_err(device)?;
        let (mut faces, mut logits) = (Vec::with_capacity(rn), Vec::with_capacity(rn));
        for r in 0..rn {
            let span = st.region_off[r] as usize..st.region_off[r + 1] as usize;
            faces.push(span.clone().map(|t| (st.unresolved[t] != 0).then(|| TowerFace { masses: ms[t * a..(t + 1) * a].iter().map(|&v| v as u128).collect(), total: ts[t] as u128 })).collect());
            logits.push(span.map(|t| (st.unresolved[t] != 0).then(|| zs[t * a..(t + 1) * a].to_vec())).collect());
        }
        Ok((faces, logits, EnergyPass { cells, reads, rereads, lists, material: Vec::new() }))
    }
}

/// A region's own parts, as a square's passes build them (the host's `energy_square_corners` regions).
struct Owned {
    classes: Vec<usize>,
    unresolved: Vec<bool>,
    faces: Vec<Option<Shares>>,
    locked: Vec<bool>,
}

impl Owned {
    /// A square's corner (the host's `corner`): `at` read open; `other` set to `letter`, or open carrying `mixture` locked.
    fn corner(truth: &[usize], at: usize, other: usize, letter: Option<usize>, mixture: Option<Shares>) -> Self {
        let sites = truth.len();
        let mut o = Owned { classes: truth.to_vec(), unresolved: vec![false; sites], faces: vec![None; sites], locked: vec![false; sites] };
        o.unresolved[at] = true;
        match letter {
            Some(c) => o.classes[other] = c,
            None => {
                o.unresolved[other] = true;
                (o.faces[other], o.locked[other]) = (mixture, true);
            }
        }
        o
    }

    fn region(&self) -> Region<'_> {
        Region { classes: &self.classes, unresolved: &self.unresolved, faces: &self.faces, locked: &self.locked, echo: &[], domain: None, port: None }
    }
}

impl<'c> CardField<'c> {
    /// One batch of owned regions read on a plan: their energy sites staged (the host's `Field::energy_sites`), admitted,
    /// and read ([`CardField::energy_batch`]); each region's logits (empty where the plan reads no faces) and the pass.
    #[allow(clippy::type_complexity)]
    fn energy_owned(&self, field: &Field, owned: &[Owned], words: &mut Words, plan: EnergyPlan<'_, 'c>) -> Result<(Vec<Vec<Option<Vec<i64>>>>, EnergyPass<'c>)> {
        let d = field.declaration;
        let regions: Vec<Region> = owned.iter().map(Owned::region).collect();
        admit_regions(&d, &regions)?;
        let sited: Vec<(Vec<Option<Shares>>, Vec<bool>)> = regions.iter().map(|r| field.energy_sites(r)).collect();
        let staged: Vec<Region> = regions.iter().zip(&sited).map(|(r, (faces, locked))| Region { faces, locked, ..*r }).collect();
        admit_regions(&d, &staged)?;
        let (_, logits, pass) = self.energy_batch(field, &staged, words, plan)?;
        Ok((logits, pass))
    }

    /// [measurement; the unified-theory reading of November 7, 01:37] **One batch of squares at their bases** (the host's
    /// `Field::energy_square_corners`, square for square): the bases read (each truth with its two sites open), their supports
    /// and halvings kept; then on that layout, every region replayed at its base's halvings under its base's supports, `i`'s
    /// corners with `j` at `b`, `j`'s with `i` at `a`, the runner-ups read on the host's law, the corners at the runner-ups, the
    /// four energies `G` (no faces), and the attribution's corners with the mixtures moved by `ε` and by `4ε`; each square read into the
    /// host's own [`EnergySquare`] (`Field::energy_square_reading`). A square with no runner-up reads `None` (its later regions
    /// are read at its own letters, to keep the layout, and discarded).
    fn energy_square_batch(&self, field: &Field, squares: &[(&[usize], (usize, usize))], void: usize, eps: u32, words: &mut Words) -> Result<Vec<Option<EnergySquare>>> {
        let open_at = |(truth, (i, j)): &(&[usize], (usize, usize))| {
            let mut unresolved = vec![false; truth.len()];
            (unresolved[*i], unresolved[*j]) = (true, true);
            Owned { classes: truth.to_vec(), unresolved, faces: Vec::new(), locked: Vec::new() }
        };
        let face_at = |logits: &[Vec<Option<Vec<i64>>>], s: usize, t: usize| -> Result<Vec<i64>> { logits[s][t].clone().ok_or(TowerError::Refused("a square's open place with no face")) };
        let bases: Vec<Owned> = squares.iter().map(open_at).collect();
        let (base_logits, base) = self.energy_owned(field, &bases, words, EnergyPlan::forward())?;
        drop(bases);
        let lists = base.lists.ok_or(TowerError::Refused("a square's base read under another's supports"))?;
        let halvings: Vec<Vec<Option<u32>>> = base.reads.iter().map(|r| r.halvings.clone()).collect();
        drop(base.cells);
        let plan = EnergyPlan { replay: Some(&halvings), base: Some(&lists), faces: true, material: false };
        let n = squares.len();
        let letters: Vec<(usize, usize)> = squares.iter().map(|(truth, (i, j))| (truth[*i], truth[*j])).collect();
        let corners = |kinds: &dyn Fn(usize) -> Owned, plan: EnergyPlan<'_, 'c>, words: &mut Words| -> Result<(Vec<Vec<Option<Vec<i64>>>>, EnergyPass<'c>)> {
            let owned: Vec<Owned> = (0..n).map(kinds).collect();
            self.energy_owned(field, &owned, words, plan)
        };
        // `i` open with `j` at its letter, and `j` with `i` at its own.
        let (zi_b, _) = corners(&|s| Owned::corner(squares[s].0, squares[s].1 .0, squares[s].1 .1, Some(letters[s].1), None), plan, words)?;
        let (zj_a, _) = corners(&|s| Owned::corner(squares[s].0, squares[s].1 .1, squares[s].1 .0, Some(letters[s].0), None), plan, words)?;
        let zi_b: Vec<Vec<i64>> = (0..n).map(|s| face_at(&zi_b, s, squares[s].1 .0)).collect::<Result<_>>()?;
        let zj_a: Vec<Vec<i64>> = (0..n).map(|s| face_at(&zj_a, s, squares[s].1 .1)).collect::<Result<_>>()?;
        let runners: Vec<Option<(usize, usize)>> = (0..n).map(|s| field.energy_square_runners(&zi_b[s], &zj_a[s], letters[s], void)).collect();
        let at: Vec<(usize, usize)> = (0..n).map(|s| runners[s].unwrap_or(letters[s])).collect();
        // The corners at the runner-ups.
        let (zi_b2, _) = corners(&|s| Owned::corner(squares[s].0, squares[s].1 .0, squares[s].1 .1, Some(at[s].1), None), plan, words)?;
        let (zj_a2, _) = corners(&|s| Owned::corner(squares[s].0, squares[s].1 .1, squares[s].1 .0, Some(at[s].0), None), plan, words)?;
        let zi_b2: Vec<Vec<i64>> = (0..n).map(|s| face_at(&zi_b2, s, squares[s].1 .0)).collect::<Result<_>>()?;
        let zj_a2: Vec<Vec<i64>> = (0..n).map(|s| face_at(&zj_a2, s, squares[s].1 .1)).collect::<Result<_>>()?;
        // The energy's own square: `G` at `(a′, b)`, `(a, b′)`, `(a, b)`, `(a′, b′)`, read again at the base, no faces.
        let energies = EnergyPlan { faces: false, ..plan };
        let mut g = vec![[0i128; 4]; n];
        for (k, pick) in [|(a, b): (usize, usize), (a2, b2): (usize, usize)| (a2, b), |(a, b), (a2, b2)| (a, b2), |(a, b), _| (a, b), |_, (a2, b2)| (a2, b2)].iter().enumerate() {
            let (_, pass) = corners(
                &|s| {
                    let (truth, (i, j)) = squares[s];
                    let mut classes = truth.to_vec();
                    (classes[i], classes[j]) = pick(letters[s], at[s]);
                    Owned { classes, unresolved: vec![false; truth.len()], faces: Vec::new(), locked: Vec::new() }
                },
                energies,
                words,
            )?;
            for s in 0..n {
                g[s][k] = pass.reads[s].last;
            }
        }
        // The attribution read at one base: the base's own faces, and each site's with the other's mixture moved by `ε`.
        let (zi_moved, _) = corners(&|s| Owned::corner(squares[s].0, squares[s].1 .0, squares[s].1 .1, None, Some(field.energy_square_mixture(Some((at[s].1, letters[s].1)), eps))), plan, words)?;
        let (zj_moved, _) = corners(&|s| Owned::corner(squares[s].0, squares[s].1 .1, squares[s].1 .0, None, Some(field.energy_square_mixture(Some((at[s].0, letters[s].0)), eps))), plan, words)?;
        // And at four times the step.
        let (zi_wide, _) = corners(&|s| Owned::corner(squares[s].0, squares[s].1 .0, squares[s].1 .1, None, Some(field.energy_square_mixture(Some((at[s].1, letters[s].1)), 4 * eps))), plan, words)?;
        let (zj_wide, _) = corners(&|s| Owned::corner(squares[s].0, squares[s].1 .1, squares[s].1 .0, None, Some(field.energy_square_mixture(Some((at[s].0, letters[s].0)), 4 * eps))), plan, words)?;
        (0..n)
            .map(|s| {
                let Some(runner) = runners[s] else { return Ok(None) };
                let (i, j) = squares[s].1;
                let (zi, zj, zim, zjm) = (face_at(&base_logits, s, i)?, face_at(&base_logits, s, j)?, face_at(&zi_moved, s, i)?, face_at(&zj_moved, s, j)?);
                let (ziw, zjw) = (face_at(&zi_wide, s, i)?, face_at(&zj_wide, s, j)?);
                let read = SquareCorners { zi_b: &zi_b[s], zj_a: &zj_a[s], zi_b2: &zi_b2[s], zj_a2: &zj_a2[s], zi: &zi, zj: &zj, zi_moved: &zim, zj_moved: &zjm, zi_wide: &ziw, zj_wide: &zjw, g: g[s] };
                field.energy_square_reading(letters[s], runner, &read, void).map(Some)
            })
            .collect()
    }
}

impl CardField<'_> {
    /// [definition; agent-inferred, November 7] **An energy field's material covector on the card** (the host's
    /// `Field::energy_material` region by region): each region's `∂G/∂θ` on `2^(−40)` (theta long) and `G` on `2^(−32)` bits,
    /// the regions batched by the card's memory (each region's two theta-long accumulators beside its forward), each batch's
    /// certified descent, its reverse with every stood tick's material, and the opening.
    pub fn energy_material(&mut self, field: &Field, regions: &[Region]) -> Result<Vec<(Vec<i128>, i128)>> {
        let d = field.declaration;
        if !d.energy {
            return Err(TowerError::Refused("an energy material of a field whose faces are not one energy's forces"));
        }
        if field.scale.is_some() {
            return Err(TowerError::Refused("an energy field read with a tower of scales (its energy is not built)"));
        }
        admit_regions(&d, regions)?;
        let sited: Vec<(Vec<Option<Shares>>, Vec<bool>)> = regions.iter().map(|r| field.energy_sites(r)).collect();
        let staged: Vec<Region> = regions.iter().zip(&sited).map(|(r, (faces, locked))| Region { faces, locked, ..*r }).collect();
        admit_regions(&d, &staged)?;
        let card = self.card;
        let started = Instant::now();
        let (mut words, upload, face_octets) = self.upload(field, None)?;
        let lengths: Vec<usize> = staged.iter().map(|r| r.classes.len()).collect();
        let theta = field.theta.len() as u64;
        let octets = |sites: usize| energy_octets_widened(&d, sites, field.widen) + 2 * 16 * theta;
        let batches = batches(&lengths, &octets, (self.budget - face_octets) / 5 * 4)?;
        let mut out = Vec::with_capacity(regions.len());
        let plan = EnergyPlan { replay: None, base: None, faces: false, material: true };
        for batch in batches {
            if batch.is_empty() {
                continue;
            }
            let peak = lengths[batch.clone()].iter().map(|&n| octets(n)).sum::<u64>();
            self.times.peak_store = self.times.peak_store.max(peak);
            self.times.batches += 1;
            let (_, _, pass) = self.energy_batch(field, &staged[batch], &mut words, plan)?;
            self.times.energy_rereads += pass.rereads;
            out.extend(pass.material.into_iter().zip(pass.reads).map(|(g, read)| (g, read.last)));
        }
        let met = self.timed(Kind::Copy, || card.fetch(&upload.met)).map_err(device)?[0] as u128;
        self.times.pairs += met;
        self.times.returns += 1;
        self.times.return_ns += started.elapsed().as_nanos();
        Ok(out)
    }

    /// [measurement; the unified-theory reading of November 7, 01:37] **Squares read at one base on the card** (the host's
    /// `Field::energy_square_corners` for each `(truth, (i, j))`): the squares batched by the card's memory, each batch's
    /// thirteen reads ([`CardField::energy_square_batch`]).
    pub fn energy_squares(&mut self, field: &Field, squares: &[(&[usize], (usize, usize))], void: usize, eps: u32) -> Result<Vec<Option<EnergySquare>>> {
        let d = field.declaration;
        if !d.energy {
            return Err(TowerError::Refused("an energy square of a field whose faces are not one energy's forces"));
        }
        if field.scale.is_some() {
            return Err(TowerError::Refused("an energy field read with a tower of scales (its energy is not built)"));
        }
        if squares.iter().any(|(truth, (i, j))| i == j || *i >= truth.len() || *j >= truth.len()) {
            return Err(TowerError::Refused("a square whose two sites are not two of its truth's"));
        }
        let card = self.card;
        let started = Instant::now();
        let (mut words, upload, face_octets) = self.upload(field, None)?;
        let lengths: Vec<usize> = squares.iter().map(|(truth, _)| truth.len()).collect();
        let octets = |sites: usize| energy_octets_widened(&d, sites, field.widen);
        let batches = batches(&lengths, &octets, (self.budget - face_octets) / 5 * 4)?;
        let mut out = Vec::with_capacity(squares.len());
        for batch in batches {
            if batch.is_empty() {
                continue;
            }
            let peak = lengths[batch.clone()].iter().map(|&n| octets(n)).sum::<u64>();
            self.times.peak_store = self.times.peak_store.max(peak);
            self.times.batches += 1;
            out.extend(self.energy_square_batch(field, &squares[batch], void, eps, &mut words)?);
        }
        let met = self.timed(Kind::Copy, || card.fetch(&upload.met)).map_err(device)?[0] as u128;
        self.times.pairs += met;
        self.times.reads += 1;
        self.times.read_ns += started.elapsed().as_nanos();
        Ok(out)
    }

    /// [measurement] **An energy field's faces, logits and energy reads on the card** ([`EnergyRead`] a region): the card's
    /// forward the host's `Field::energy_logits` is checked against.
    #[allow(clippy::type_complexity)]
    pub fn energy_read(&mut self, field: &Field, regions: &[Region]) -> Result<(Vec<Vec<Option<TowerFace>>>, Vec<Vec<Option<Vec<i64>>>>, Vec<EnergyRead>)> {
        self.energy_run(field, regions)
    }
}

impl CardField<'_> {
    /// [measurement; the unified-theory readings of November 7, 03:22 and 04:20] **Central squares at one base on the card**
    /// (the host's `Field::energy_central_square` for each `(truth, (i, j))`): each step's readings `(z_i(a′) − z_i(a))` with
    /// `j`'s mixture moved by `+ε(b′ − b)` less the same moved by `−ε(b′ − b)`, and `j`'s alike, every corner replayed at the
    /// base's halvings under its supports; the squares batched by the card's memory, each batch's `3 + 4·steps` reads.
    pub fn energy_central_squares(&mut self, field: &Field, squares: &[(&[usize], (usize, usize))], void: usize, steps: &[u32]) -> Result<Vec<Option<Vec<(i128, i128)>>>> {
        let d = field.declaration;
        if !d.energy || field.scale.is_some() {
            return Err(TowerError::Refused("a central square of a field whose faces are not one energy's forces"));
        }
        let base_w = (1u32 << holonics::hnn::tower::field::STATE_BITS) / d.alphabet as u32;
        if steps.iter().any(|&e| e > base_w) {
            return Err(TowerError::Refused("a square's step past a letter's weight in the uniform mixture"));
        }
        if squares.iter().any(|(truth, (i, j))| i == j || *i >= truth.len() || *j >= truth.len()) {
            return Err(TowerError::Refused("a square whose two sites are not two of its truth's"));
        }
        let card = self.card;
        let started = Instant::now();
        let (mut words, upload, face_octets) = self.upload(field, None)?;
        let lengths: Vec<usize> = squares.iter().map(|(truth, _)| truth.len()).collect();
        let octets = |sites: usize| energy_octets_widened(&d, sites, field.widen);
        let batches = batches(&lengths, &octets, (self.budget - face_octets) / 5 * 4)?;
        let mut out = Vec::with_capacity(squares.len());
        for batch in batches {
            if batch.is_empty() {
                continue;
            }
            let peak = lengths[batch.clone()].iter().map(|&n| octets(n)).sum::<u64>();
            self.times.peak_store = self.times.peak_store.max(peak);
            self.times.batches += 1;
            out.extend(self.energy_central_batch(field, &squares[batch], void, steps, &mut words)?);
        }
        let met = self.timed(Kind::Copy, || card.fetch(&upload.met)).map_err(device)?[0] as u128;
        self.times.pairs += met;
        self.times.reads += 1;
        self.times.read_ns += started.elapsed().as_nanos();
        Ok(out)
    }

    #[allow(clippy::type_complexity)]
    fn energy_central_batch(&self, field: &Field, squares: &[(&[usize], (usize, usize))], void: usize, steps: &[u32], words: &mut Words) -> Result<Vec<Option<Vec<(i128, i128)>>>> {
        let bases: Vec<Owned> = squares
            .iter()
            .map(|(truth, (i, j))| {
                let mut unresolved = vec![false; truth.len()];
                (unresolved[*i], unresolved[*j]) = (true, true);
                Owned { classes: truth.to_vec(), unresolved, faces: Vec::new(), locked: Vec::new() }
            })
            .collect();
        let (_, base) = self.energy_owned(field, &bases, words, EnergyPlan::forward())?;
        drop(bases);
        let lists = base.lists.ok_or(TowerError::Refused("a square's base read under another's supports"))?;
        let halvings: Vec<Vec<Option<u32>>> = base.reads.iter().map(|r| r.halvings.clone()).collect();
        drop(base.cells);
        let plan = EnergyPlan { replay: Some(&halvings), base: Some(&lists), faces: true, material: false };
        let n = squares.len();
        let letters: Vec<(usize, usize)> = squares.iter().map(|(truth, (i, j))| (truth[*i], truth[*j])).collect();
        let face_at = |logits: &[Vec<Option<Vec<i64>>>], s: usize, t: usize| -> Result<Vec<i64>> { logits[s][t].clone().ok_or(TowerError::Refused("a square's open place with no face")) };
        // `i`'s face with `j` resolved or carrying a mixture (and `j`'s alike), every square of the batch at once.
        let read = |own: bool, letter: &dyn Fn(usize) -> Option<usize>, mixture: &dyn Fn(usize) -> Option<Shares>, words: &mut Words| -> Result<Vec<Vec<i64>>> {
            let owned: Vec<Owned> = (0..n)
                .map(|s| {
                    let (truth, (i, j)) = squares[s];
                    let (at, other) = if own { (i, j) } else { (j, i) };
                    Owned::corner(truth, at, other, letter(s), mixture(s))
                })
                .collect();
            let (logits, _) = self.energy_owned(field, &owned, words, plan)?;
            (0..n).map(|s| face_at(&logits, s, if own { squares[s].1 .0 } else { squares[s].1 .1 })).collect()
        };
        let zi_b = read(true, &|s| Some(letters[s].1), &|_| None, words)?;
        let zj_a = read(false, &|s| Some(letters[s].0), &|_| None, words)?;
        let runners: Vec<Option<(usize, usize)>> = (0..n).map(|s| field.energy_square_runners(&zi_b[s], &zj_a[s], letters[s], void)).collect();
        let at: Vec<(usize, usize)> = (0..n).map(|s| runners[s].unwrap_or(letters[s])).collect();
        let gap = |z: &[i64], hi: usize, lo: usize| (z[hi] - z[lo]) as i128;
        let mut out: Vec<Vec<(i128, i128)>> = vec![Vec::with_capacity(steps.len()); n];
        for &eps in steps {
            let zi_up = read(true, &|_| None, &|s| Some(field.energy_square_mixture(Some((at[s].1, letters[s].1)), eps)), words)?;
            let zi_down = read(true, &|_| None, &|s| Some(field.energy_square_mixture(Some((letters[s].1, at[s].1)), eps)), words)?;
            let zj_up = read(false, &|_| None, &|s| Some(field.energy_square_mixture(Some((at[s].0, letters[s].0)), eps)), words)?;
            let zj_down = read(false, &|_| None, &|s| Some(field.energy_square_mixture(Some((letters[s].0, at[s].0)), eps)), words)?;
            for s in 0..n {
                let ((a, b), (a2, b2)) = (letters[s], at[s]);
                out[s].push((gap(&zi_up[s], a2, a) - gap(&zi_down[s], a2, a), gap(&zj_up[s], b2, b) - gap(&zj_down[s], b2, b)));
            }
        }
        Ok(runners.iter().zip(out).map(|(r, o)| r.map(|_| o)).collect())
    }

    /// [measurement; the unified-theory reading of November 7, 04:05] **Each resolved region's energy on the card**: `G(e) =
    /// Φ(x^K(e); e)` at its own certified halvings, on `2^(−32)` bits (the host's `Field::energy_g`), no faces read; the
    /// regions batched by the card's memory. Every site of each region is resolved.
    pub fn energies(&mut self, field: &Field, regions: &[&[usize]]) -> Result<Vec<i128>> {
        let d = field.declaration;
        if !d.energy || field.scale.is_some() {
            return Err(TowerError::Refused("an energy read of a field whose faces are not one energy's forces"));
        }
        let card = self.card;
        let started = Instant::now();
        let (mut words, upload, face_octets) = self.upload(field, None)?;
        let lengths: Vec<usize> = regions.iter().map(|r| r.len()).collect();
        let octets = |sites: usize| energy_octets_widened(&d, sites, field.widen);
        let batches = batches(&lengths, &octets, (self.budget - face_octets) / 5 * 4)?;
        let mut out = Vec::with_capacity(regions.len());
        let plan = EnergyPlan { faces: false, ..EnergyPlan::forward() };
        for batch in batches {
            if batch.is_empty() {
                continue;
            }
            let peak = lengths[batch.clone()].iter().map(|&n| octets(n)).sum::<u64>();
            self.times.peak_store = self.times.peak_store.max(peak);
            self.times.batches += 1;
            let owned: Vec<Owned> = regions[batch].iter().map(|c| Owned { classes: c.to_vec(), unresolved: vec![false; c.len()], faces: Vec::new(), locked: Vec::new() }).collect();
            let (_, pass) = self.energy_owned(field, &owned, &mut words, plan)?;
            out.extend(pass.reads.iter().map(|r| r.last));
        }
        let met = self.timed(Kind::Copy, || card.fetch(&upload.met)).map_err(device)?[0] as u128;
        self.times.pairs += met;
        self.times.reads += 1;
        self.times.read_ns += started.elapsed().as_nanos();
        Ok(out)
    }
}

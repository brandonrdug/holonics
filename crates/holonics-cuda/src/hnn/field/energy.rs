//! **The energy field's forward on the card** (`holonics::hnn::tower::field::energy`, the unified-theory reading of
//! November 6, 22:52; `kernels/field_energy.cuh`): the opening, `K` ticks of certified descent of one stored energy under
//! the supports held from the opening, and each open site's face as the energy's force on its letter, bit for bit the host's
//! `Field::energy_pass` ([`holonics::hnn::tower::field::Field::energy_logits`]).
//!
//! [definition; agent-inferred, November 6] **The work is laid out as the field's forward is.** The opening and the moments
//! are the field's own launches; the energy's sites are the host's `Field::energy_sites` (an open site carries the locked
//! uniform mixture), staged as any region's. A state's energy read is a cell ([`EnergyCell`]): the chart, the key and probe
//! words (the probe reading its moment), framed and at unit power, the definite words' prefix sums, the exposure's scores, and
//! each receiver's lock partition (`field_energy_rows_l*`: its mass the contact's exact series, its `log₂ Z` read from the
//! mass's leading bits as the host's `log2_big` reads them, its shares), the strand pair's and the letters' energy, each summed
//! per region as exact integers. The force is the locks' shares as their scores' covector through the reverse's own key and
//! probe brackets (`field_energy_rows_back`, `field_contact_columns`, `field_spread`), the unit powers' and the frames'
//! returns and the charts' transposes, with the pair's (`field_pair_back` of the contraction) and the letters' (held). The
//! regions of a batch tick in lockstep: each tick's force, then rounds of candidate steps, each region at its own halvings,
//! its energy read back and its fall certified as the host's `energy_relax` certifies it (`FIRST_HALVINGS`, `MOST_HALVINGS`,
//! one unit of `2^(−32)` a logarithm and two of slack); a region whose fall is certified takes its candidate's state, one
//! whose step moves nothing or whose halvings run out rests.
//!
//! [agent-inferred, November 6] **Each tick's cell is kept on the card** ([`EnergyPass::cells`]): the opening's and each
//! tick's last state's (a candidate whose every region stood is kept as it is; otherwise the tick's states are read again,
//! the same bits), with each region's halvings, so a reverse through the ticks (the face's total derivative: a
//! Hessian-vector product of `Φ` per tick) reads every tick's charts, unit words, shares and drives where the forward left
//! them. The reverse itself is not built: an energy field is read on the card, not trained.

use super::*;
use holonics::hnn::tower::field::{EnergyRead, Shares, FIRST_HALVINGS, MOST_HALVINGS};

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
    cls: Pooled<'c, u32>,
    class_off: Pooled<'c, u32>,
    members: Pooled<'c, u32>,
    pn: Pooled<'c, u32>,
    pcls: Pooled<'c, u32>,
    poff: Pooled<'c, u32>,
    pmem: Pooled<'c, u32>,
    own: Pooled<'c, i64>,
    before: Pooled<'c, i64>,
    after: Pooled<'c, i64>,
    bias: Pooled<'c, i64>,
    mterm: Pooled<'c, i64>,
    lf: Pooled<'c, i64>,
    dc: Pooled<'c, i64>,
    dyh0: Pooled<'c, i64>,
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

/// [agent-inferred, November 6] **A batch's energy forward as the card holds it**: every tick's cell (the opening's first,
/// then each tick's last state's), each region's halvings by tick, and the read's receipt. What a reverse through the ticks
/// will read.
pub(super) struct EnergyPass<'c> {
    #[allow(dead_code, reason = "held for the reverse through the ticks, which is not built")]
    pub(super) cells: Vec<EnergyCell<'c>>,
    pub(super) reads: Vec<EnergyRead>,
    /// The tick's last states read again ([`FieldTimes::energy_rereads`]).
    pub(super) rereads: u64,
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
    let (dw, m2, f, a, h, span) = (d.width as u64, 2 * d.complex() as u64, d.contacts as u64, d.alphabet as u64, d.heads as u64, 2 * d.modes as u64);
    let (s, pairs, lanes, slots, tm) = (sites as u64, (sites * sites) as u64, d.lanes as u64, crowd_slots(d.reach) as u64, d.moment_modes() as u64);
    let probe_stride = 1u64 << d.class_trits();
    let cell_site = 8 * dw + 4 * dw + 16 * lanes + 8 * 2 * m2 + 8 * m2 + h * span * (8 + 4 + 8 + 8 + 4) + 2 * 16 * h + 2 * 16 * h * span + 8 * h + 8 * h + 8 * h * slots + 2 * 8 * f + 8 * dw + 16 * h;
    let cell_fixed = (2 * 16 * h * span + 8 * h) + 64 + 16 * ENERGY_SUMS as u64;
    let cells = d.ticks as u64 + 2;
    let held_site = 4 * h * (3 + 2 * probe_stride) + 6 * 8 * dw + 8 + 8 * f + 8 * h * span + 8 * m2 + 3 * 8 * 2 * h + 2 * 8 * h * d.modes as u64 + 112 * tm;
    let force_site = 3 * 8 * m2 + 2 * 16 * span + 2 * 8 * f + 8 * dw;
    let face_site = 16 * m2 + 2 * 8 * a + 16 + tm * (8 * 2 + 16 * 2 * 3 + 16 * 2 * 2 * 16) + 8 * dw + 8 * 2 * m2;
    cells * (h * 8 * pairs + s * cell_site + cell_fixed) + 8 * pairs + s * (held_site + force_site + face_site) + 4 * h * (3 * d.classes() as u64 + 2)
}

impl<'c> CardField<'c> {
    /// [definition; the unified-theory reading of November 6, 22:52] **An energy field's faces and logits on the card**
    /// (the host's `Field::energy_pass` region by region), with each region's energy read ([`EnergyRead`]): the regions'
    /// energy sites staged, batched by the card's memory, each batch's forward ([`CardField::energy_batch`]).
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
        let octets = |sites: usize| energy_octets(&d, sites);
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
            let (f, z, pass) = self.energy_batch(field, &staged[batch], &mut words)?;
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
        words.cls = held.cls.device_ptr();
        words.class_off = held.class_off.device_ptr();
        words.members = held.members.device_ptr();
        words.pn = held.pn.device_ptr();
        words.pcls = held.pcls.device_ptr();
        words.poff = held.poff.device_ptr();
        words.pmem = held.pmem.device_ptr();
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
            card.zero_octets(&fb.cv, 0, 16 * rows * span).map_err(device)?;
            card.zero_octets(&fb.cw, 0, 16 * rows * span).map_err(device)?;
            let (mut hh, mut dsp, mut dqp) = (h as u32, fb.ds.device_ptr(), fb.dq.device_ptr());
            self.launch("field_energy_rows_back", Self::rows_grid(sites as u64, REV_ROWS), (REV_ROWS * 32) as u32, &mut [arg(words), arg(&mut hh), arg(&mut dsp), arg(&mut dqp)])?;
            let (mut hh, mut dyhp, mut dsp, mut dqp, mut dvp) = (h as u32, held.dyh0.device_ptr(), fb.ds.device_ptr(), fb.dq.device_ptr(), fb.dv.device_ptr());
            self.launch("field_contact_columns", Self::rows_grid(sites as u64, CONTACT_ROWS), (CONTACT_ROWS * 32) as u32, &mut [arg(words), arg(&mut hh), arg(&mut dyhp), arg(&mut dsp), arg(&mut dqp), arg(&mut dvp)])?;
            let (mut hh, mut dqp, mut dvp) = (h as u32, fb.dq.device_ptr(), fb.dv.device_ptr());
            self.launch("field_spread", (regions as u32).clamp(1, 65_535), THREADS, &mut [arg(words), arg(&mut hh), arg(&mut dqp), arg(&mut dvp)])?;
        }
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

    /// [definition; the unified-theory reading of November 6, 22:52] **One batch's energy forward** (the host's
    /// `energy_relax` and `energy_pass`, region by region in lockstep): the opening, the held letters and classes, `K` ticks
    /// of certified descent, and each unresolved site's face as the energy's force on its letter at the last state.
    #[allow(clippy::type_complexity)]
    fn energy_batch(&self, field: &Field, regions: &[Region], words: &mut Words) -> Result<(Vec<Vec<Option<TowerFace>>>, Vec<Vec<Option<Vec<i64>>>>, EnergyPass<'c>)> {
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
        let held = EnergyHeld {
            cls: u32s(heads * sites)?,
            class_off: u32s(heads * rn * (2 * classes + 1))?,
            members: u32s(heads * sites)?,
            pn: u32s(heads * sites)?,
            pcls: u32s(heads * sites * probe_stride)?,
            poff: u32s(heads * rn * (classes + 1))?,
            pmem: u32s(heads * sites * probe_stride)?,
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
        self.energy_cell(field, words, &opening, &held, true, sites, rn)?;
        let read0 = self.energy_reads(&opening, rn)?;
        let mut cells = vec![opening];
        let mut now: Vec<Read> = read0.clone();
        let mut reads = vec![1u64; rn];
        let mut met: Vec<u64> = read0.iter().map(|r| r.pairs).collect();
        let mut halvings: Vec<Vec<Option<u32>>> = vec![Vec::with_capacity(d.ticks); rn];
        let mut active = vec![true; rn];
        let mut first = vec![FIRST_HALVINGS; rn];
        let mut rereads = 0u64;
        for _ in 0..d.ticks {
            if !active.iter().any(|&on| on) {
                break;
            }
            let current = cells.last().ok_or(TowerError::Refused("an energy forward with no opening"))?;
            self.energy_force(field, words, current, &held, &fb, sites, rn)?;
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
        // The faces: each unresolved site's letter force at the last state.
        let last = cells.last().ok_or(TowerError::Refused("an energy forward with no opening"))?;
        self.energy_force(field, words, last, &held, &fb, sites, rn)?;
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
            let (mut mp, mut rp, mut dpp, mut dmp) = (mface, last.read.device_ptr(), fb.dp.device_ptr(), dm.device_ptr());
            self.launch("field_energy_dm", Self::cells((sites * m2) as u64), THREADS, &mut [arg(words), arg(&mut mp), arg(&mut rp), arg(&mut dpp), arg(&mut dmp)])?;
            Some(self.moment_strands_back(field, words, dm.device_ptr(), rn, sites)?)
        } else {
            None
        };
        {
            let (mut rp, mut dbp, mut dap) = (last.read.device_ptr(), back.as_ref().map_or(0, |b| b.d_before.device_ptr()), back.as_ref().map_or(0, |b| b.d_after.device_ptr()));
            let (mut tm32, mut mb, mut ma, mut zp) = (tm as u32, l.moment_before as u64, l.moment_after as u64, z.device_ptr());
            self.launch("field_energy_face", Self::cells((sites * a) as u64), THREADS, &mut [arg(words), arg(&mut rp), arg(&mut dbp), arg(&mut dap), arg(&mut tm32), arg(&mut mb), arg(&mut ma), arg(&mut zp)])?;
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
        let reads = (0..rn).map(|r| EnergyRead { opening: read0[r].phi, last: now[r].phi, halvings: halvings[r].clone(), reads: reads[r], pairs: met[r] }).collect();
        Ok((faces, logits, EnergyPass { cells, reads, rereads }))
    }
}

impl CardField<'_> {
    /// [measurement] **An energy field's faces, logits and energy reads on the card** ([`EnergyRead`] a region): the card's
    /// forward the host's `Field::energy_logits` is checked against.
    #[allow(clippy::type_complexity)]
    pub fn energy_read(&mut self, field: &Field, regions: &[Region]) -> Result<(Vec<Vec<Option<TowerFace>>>, Vec<Vec<Option<Vec<i64>>>>, Vec<EnergyRead>)> {
        self.energy_run(field, regions)
    }
}

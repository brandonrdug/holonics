//! **The field's card realization** (`holonics::hnn::tower::field`, #404, #407; record
//! `2026-11-01_THE_PROBLEM_IS_ONE_FIELD_EVERY_SITE_READS_EVERY_OTHER_AND_THE_ANSWER_IS_REFINED_NOT_SPOKEN`,
//! §7).
//!
//! [definition; agent-inferred, November 1] `CardField` implements [`FieldRealization`]: a section's
//! regions read forward through the `K` ticks of the one constitution and returned exactly, and the
//! certificate's rereads, bit for bit the host's [`holonics::hnn::tower::field::HostField`]
//! (`kernels/field.cu`). The work is laid out as the field is: a site is its global index in a
//! batch of regions, each region keeping its own length (no region is padded to another's), a
//! contact row is a head and a receiving site (one warp a row, its lanes over the region's sites), and
//! a region's weights `e_ij` are its own block of the weight store. The material, the regions'
//! classes and resolutions cross to the card; the faces of the unresolved sites and the covector
//! cross back. Every tick's carriers stay on the card through the reverse.
//!
//! [agent-inferred, November 1] **Memory: the weights are kept, the regions batched by the card's
//! measured memory.** A region of `S` sites holds `H·S²` weights on `u64` a tick, and the reverse
//! reads them twice (the values' and the contact's returns), so they are kept through the reverse
//! rather than recomputed (a recompute would rerun every row's exponentials in two more passes);
//! the contact's return `δs_ij` is held for one head at a time (`S²` on 128 bits). A section's
//! regions are read in batches whose every allocation (the weights, the contact's return and each
//! site's carriers) fits the batch budget, the card's free memory at the open less a margin for the
//! driver, never past the 12 GB the runs keep to.
//! Batches sum their covectors on the card (integer sums: any batching gives the same bits).

use core::ffi::c_void;
use std::time::Instant;

use holonics::hnn::tower::field::{Field, FieldDeclaration, FieldRealization, Region};
use holonics::hnn::tower::{TowerError, TowerFace};

use crate::cuda::{Dim3, Module};
use crate::hnn::card::{Card, CardBuffer};
use crate::hnn::DeviceError;

const IMAGE: &[u8] = include_bytes!(concat!(env!("OUT_DIR"), "/field.ptx"));
const THREADS: u32 = 256;
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
    beta: u32,
    m: u32,
    m2: u32,
    span: u32,
    digits: u32,
    t: u32,
    r: u32,
    pairs: u64,
    ln2_lo: u64,
    ln2_hi: u64,
    theta: u64,
    enc: u64,
    q: u64,
    q_bias: u64,
    k: u64,
    k_bias: u64,
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
    rk: u64,
    rv: u64,
    rout: u64,
    ra: u64,
    rb: u64,
    rw: u64,
    rread: u64,
    phasor: u64,
    ring_off: u64,
    ring_n: u64,
    roots: u64,
    site_region: u64,
    site_pos: u64,
    region_off: u64,
    region_eoff: u64,
    classes: u64,
    unresolved: u64,
    status: u64,
    x: u64,
    qkv: u64,
    qf: u64,
    kf: u64,
    vf: u64,
    e: u64,
    mass: u64,
    y: u64,
    pa: u64,
    pb: u64,
    pc: u64,
}

/// A kernel argument: the address of a value the launch copies.
fn arg<T>(v: &mut T) -> *mut c_void {
    (v as *mut T).cast()
}

/// The card's time on the field: forwards (reads), returns, their wall time and the site pairs read.
#[derive(Clone, Copy, Debug, Default)]
pub struct FieldTimes {
    pub reads: u64,
    pub read_ns: u128,
    pub returns: u64,
    pub return_ns: u128,
    /// The site pairs `Σ H S²` over every tick of every read.
    pub pairs: u128,
    pub batches: u64,
    /// The largest batch's counted allocations (weights, contact return and per-site carriers), in
    /// octets.
    pub peak_store: u64,
}

/// One tick's carriers on the card.
struct Tick<'c> {
    read: CardBuffer<'c, i32>,
    scale: CardBuffer<'c, i128>,
    qkv: CardBuffer<'c, i64>,
    qf: CardBuffer<'c, i64>,
    kf: CardBuffer<'c, i64>,
    vf: CardBuffer<'c, i64>,
    e: CardBuffer<'c, u64>,
    mass: CardBuffer<'c, u64>,
    y: CardBuffer<'c, i64>,
    read2: CardBuffer<'c, i32>,
    scale2: CardBuffer<'c, i128>,
    pa: CardBuffer<'c, i64>,
    pb: CardBuffer<'c, i64>,
    pc: CardBuffer<'c, i64>,
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
        self.card.current().map_err(device)?;
        let function = self.module.function(entry).map_err(|e| device(e.into()))?;
        let started = match &self.profile {
            Some(_) => {
                self.card.synchronize().map_err(device)?;
                Some(Instant::now())
            }
            None => None,
        };
        function.launch_on_shared(self.card.stream(), Dim3::x(grid.max(1)), Dim3 { x: block, y: 1, z: 1 }, 0, params).map_err(|e| device(e.into()))?;
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

    /// A grid striding `sites` with one block every 32 sites (a lane a site, the block's warps
    /// sharing its sums).
    fn blocks_of_32(sites: u64) -> u32 {
        sites.div_ceil(32).clamp(1, 1 << 20) as u32
    }

    /// Each region's faces and, when `returning`, the covector over the regions.
    fn run(&mut self, field: &Field, regions: &[Region], returning: bool) -> Result<(Vec<Vec<Option<TowerFace>>>, Vec<i128>)> {
        let d = field.declaration;
        for region in regions {
            if region.classes.len() != region.unresolved.len() || region.classes.is_empty() {
                return Err(TowerError::Refused("a region needs one class and one resolution a site"));
            }
            if region.classes.len() > d.reach {
                return Err(TowerError::Refused("a region past the field's reach, where its frames would repeat"));
            }
            if region.classes.iter().any(|&c| c >= d.alphabet) {
                return Err(TowerError::Refused("a region's class outside the field's alphabet"));
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
        let roots: Vec<u64> = field.exponential().roots().iter().map(|&r| u64::try_from(r).map_err(|_| TowerError::Refused("the exponential's roots lie below 2^63"))).collect::<Result<_>>()?;
        let phasor = self.timed(Kind::Copy, || card.upload(&phasor)).map_err(device)?;
        let ring_off = self.timed(Kind::Copy, || card.upload(&ring_off)).map_err(device)?;
        let ring_n = self.timed(Kind::Copy, || card.upload(&ring_n)).map_err(device)?;
        let roots_card = self.timed(Kind::Copy, || card.upload(&roots)).map_err(device)?;
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
            m: m as u32,
            m2: m2 as u32,
            span: (2 * n) as u32,
            digits: roots.len() as u32,
            ln2_lo: ln2 as u64,
            ln2_hi: (ln2 >> 64) as u64,
            theta: theta.device_ptr(),
            enc: l.enc as u64,
            q: l.q as u64,
            q_bias: l.q_bias as u64,
            k: l.k as u64,
            k_bias: l.k_bias as u64,
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
            rk: reach(l.k, m2 * dw),
            rv: reach(l.v, m2 * dw),
            rout: reach(l.out, dw * m2),
            ra: reach(l.a, f * dw),
            rb: reach(l.b, f * dw),
            rw: reach(l.w, dw * f),
            rread: reach(l.read, a * dw),
            phasor: phasor.device_ptr(),
            ring_off: ring_off.device_ptr(),
            ring_n: ring_n.device_ptr(),
            roots: roots_card.device_ptr(),
            ..Words::default()
        };
        let g = if returning { Some(self.timed(Kind::Alloc, || card.zeroed::<i128>(l.len)).map_err(device)?) } else { None };
        // The batches: whole regions in order, each batch's every allocation within the budget.
        let octets = |sites: usize| region_octets(&d, returning, sites);
        let lengths: Vec<usize> = regions.iter().map(|r| r.classes.len()).collect();
        let batches = batches(&lengths, &octets, self.budget)?;
        let mut faces: Vec<Vec<Option<TowerFace>>> = Vec::with_capacity(regions.len());
        for batch in batches {
            if batch.is_empty() {
                continue;
            }
            let peak = lengths[batch.clone()].iter().map(|&n| octets(n)).sum::<u64>();
            self.times.peak_store = self.times.peak_store.max(peak);
            self.times.batches += 1;
            faces.extend(self.batch(field, &regions[batch], &mut words, g.as_ref())?);
        }
        let g = match g {
            Some(g) => self.timed(Kind::Copy, || card.fetch(&g)).map_err(device)?,
            None => Vec::new(),
        };
        let pairs: u128 = regions.iter().map(|r| (heads * r.classes.len() * r.classes.len()) as u128).sum::<u128>() * d.ticks as u128;
        self.times.pairs += pairs;
        if returning {
            self.times.returns += 1;
            self.times.return_ns += started.elapsed().as_nanos();
        } else {
            self.times.reads += 1;
            self.times.read_ns += started.elapsed().as_nanos();
        }
        Ok((faces, g))
    }

    fn tick(&self, sites: usize, pairs: usize, field: &Field) -> Result<Tick<'c>> {
        let d = field.declaration;
        let (dw, m2, f, heads, span) = (d.width, 2 * d.complex(), d.contacts, d.heads, 2 * d.modes);
        let card = self.card;
        let alloc64 = |len: usize| self.timed(Kind::Alloc, || card.alloc::<i64>(len.max(1))).map_err(device);
        Ok(Tick {
            read: self.timed(Kind::Alloc, || card.alloc::<i32>((sites * dw).max(1))).map_err(device)?,
            scale: self.timed(Kind::Alloc, || card.alloc::<i128>(sites.max(1))).map_err(device)?,
            qkv: alloc64(sites * 3 * m2)?,
            qf: alloc64(heads * sites * span)?,
            kf: alloc64(heads * sites * span)?,
            vf: alloc64(heads * sites * span)?,
            e: self.timed(Kind::Alloc, || card.alloc::<u64>((heads * pairs).max(1))).map_err(device)?,
            mass: self.timed(Kind::Alloc, || card.alloc::<u64>((heads * sites).max(1))).map_err(device)?,
            y: alloc64(sites * m2)?,
            read2: self.timed(Kind::Alloc, || card.alloc::<i32>((sites * dw).max(1))).map_err(device)?,
            scale2: self.timed(Kind::Alloc, || card.alloc::<i128>(sites.max(1))).map_err(device)?,
            pa: alloc64(sites * f)?,
            pb: alloc64(sites * f)?,
            pc: alloc64(sites * f)?,
        })
    }

    /// One batch of regions: the forward, each unresolved site's face, and when `g` is given the
    /// reverse added into it.
    fn batch(&self, field: &Field, regions: &[Region], words: &mut Words, g: Option<&CardBuffer<'c, i128>>) -> Result<Vec<Vec<Option<TowerFace>>>> {
        let card = self.card;
        let d = field.declaration;
        let (dw, m, n, f, a, heads) = (d.width, d.complex(), d.modes, d.contacts, d.alphabet, d.heads);
        let m2 = 2 * m;
        // The batch's sites, region by region.
        let mut site_region = Vec::new();
        let mut site_pos = Vec::new();
        let mut region_off = vec![0u32];
        let mut region_eoff = Vec::new();
        let mut classes = Vec::new();
        let mut unresolved = Vec::new();
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
            }
            region_off.push(site_region.len() as u32);
        }
        let sites = site_region.len();
        let site_region_c = self.timed(Kind::Copy, || card.upload(&site_region)).map_err(device)?;
        let site_pos_c = self.timed(Kind::Copy, || card.upload(&site_pos)).map_err(device)?;
        let region_off_c = self.timed(Kind::Copy, || card.upload(&region_off)).map_err(device)?;
        let region_eoff_c = self.timed(Kind::Copy, || card.upload(&region_eoff)).map_err(device)?;
        let classes_c = self.timed(Kind::Copy, || card.upload(&classes)).map_err(device)?;
        let unresolved_c = self.timed(Kind::Copy, || card.upload(&unresolved)).map_err(device)?;
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
        words.status = status.device_ptr();
        words.x = x.device_ptr();
        let returning = g.is_some();
        let ticks: Vec<Tick> = (0..if returning { d.ticks } else { 1 }).map(|_| self.tick(sites, pairs, field)).collect::<Result<_>>()?;
        let set = |w: &mut Words, tick: &Tick| {
            w.qkv = tick.qkv.device_ptr();
            w.qf = tick.qf.device_ptr();
            w.kf = tick.kf.device_ptr();
            w.vf = tick.vf.device_ptr();
            w.e = tick.e.device_ptr();
            w.mass = tick.mass.device_ptr();
            w.y = tick.y.device_ptr();
            w.pa = tick.pa.device_ptr();
            w.pb = tick.pb.device_ptr();
            w.pc = tick.pc.device_ptr();
        };
        let t64 = sites as u64;
        self.launch("field_open", Self::cells(t64 * dw as u64), THREADS, &mut [arg(words)])?;
        for k in 0..d.ticks {
            let tick = &ticks[if returning { k } else { 0 }];
            set(words, tick);
            self.chart(words, words.x, &tick.read, &tick.scale, false)?;
            for (part, weight, bias, wmax) in [(0usize, words.q, words.q_bias, words.rq), (1, words.k, words.k_bias, words.rk), (2, words.v, words.v_bias, words.rv)] {
                let out = tick.qkv.device_ptr() + (part * m2 * 8) as u64;
                self.affine("field_affine_x32", words, weight, bias, wmax, m2, dw, tick.read.device_ptr(), dw, out, 3 * m2, 0, false)?;
            }
            self.launch("field_frame", Self::cells((heads * sites * n) as u64), THREADS, &mut [arg(words)])?;
            self.launch("field_contact", Self::warps((heads * sites) as u64), THREADS, &mut [arg(words)])?;
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
            self.reverse(field, words, &ticks, g, &fread, &fscale, &masses, &totals, &classes, &unresolved, sites, pairs)?;
        }
        self.status(&status)?;
        let masses = self.timed(Kind::Copy, || card.fetch(&masses)).map_err(device)?;
        let totals = self.timed(Kind::Copy, || card.fetch(&totals)).map_err(device)?;
        let mut out = Vec::with_capacity(regions.len());
        for r in 0..regions.len() {
            let mut faces = Vec::with_capacity((region_off[r + 1] - region_off[r]) as usize);
            for t in region_off[r] as usize..region_off[r + 1] as usize {
                faces.push((unresolved[t] != 0).then(|| TowerFace { masses: masses[t * a..(t + 1) * a].iter().map(|&v| v as u128).collect(), total: totals[t] as u128 }));
            }
            out.push(faces);
        }
        Ok(out)
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
    fn reverse(&self, field: &Field, words: &mut Words, ticks: &[Tick<'c>], g: &CardBuffer<'c, i128>, fread: &CardBuffer<'c, i32>, fscale: &CardBuffer<'c, i128>, masses: &CardBuffer<'c, u64>, totals: &CardBuffer<'c, i128>, classes: &[u32], unresolved: &[u8], sites: usize, pairs: usize) -> Result<()> {
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
        let wr = alloc64(heads * sites * span)?;
        let dq = alloc64(sites * m2)?;
        let dk = alloc64(sites * m2)?;
        let dv = alloc64(sites * m2)?;
        let ds = self.timed(Kind::Alloc, || card.alloc::<i128>(pairs.max(1))).map_err(device)?;
        // The face.
        let (mut mp, mut tp, mut dzp) = (masses.device_ptr(), totals.device_ptr(), dz.device_ptr());
        self.launch("field_face_covector", Self::cells((sites * a) as u64), THREADS, &mut [arg(words), arg(&mut mp), arg(&mut tp), arg(&mut dzp)])?;
        self.outer(words, g, words.read_bias, a, 0, dz.device_ptr(), a, 0, 0, false, true)?;
        self.outer(words, g, words.read, a, dw, dz.device_ptr(), a, fread.device_ptr(), dw, false, true)?;
        self.transposed(words, words.read, a, dw, dz.device_ptr(), a, dr.device_ptr(), false, true)?;
        self.ratio_adjoint(words, fread.device_ptr(), fscale.device_ptr(), dr.device_ptr(), 0, dx.device_ptr(), true)?;
        for tick in ticks.iter().rev() {
            words.qf = tick.qf.device_ptr();
            words.kf = tick.kf.device_ptr();
            words.vf = tick.vf.device_ptr();
            words.e = tick.e.device_ptr();
            words.mass = tick.mass.device_ptr();
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
            // The weights and the contact, head by head.
            let (mut dyp, mut dyhp, mut wrp) = (dy.device_ptr(), dyh.device_ptr(), wr.device_ptr());
            self.launch("field_current_back", Self::cells((heads * sites * n) as u64), THREADS, &mut [arg(words), arg(&mut dyp), arg(&mut dyhp), arg(&mut wrp)])?;
            for h in 0..heads {
                let (mut hh, mut dyhp, mut dsp, mut dqp) = (h as u32, dyh.device_ptr(), ds.device_ptr(), dq.device_ptr());
                self.launch("field_contact_rows", Self::warps(sites as u64), THREADS, &mut [arg(words), arg(&mut hh), arg(&mut dyhp), arg(&mut dsp), arg(&mut dqp)])?;
                let (mut hh, mut wrp, mut dsp, mut dkp, mut dvp) = (h as u32, wr.device_ptr(), ds.device_ptr(), dk.device_ptr(), dv.device_ptr());
                self.launch("field_contact_columns", Self::blocks_of_32(sites as u64), THREADS, &mut [arg(words), arg(&mut hh), arg(&mut wrp), arg(&mut dsp), arg(&mut dkp), arg(&mut dvp)])?;
            }
            for chart in [&dq, &dk, &dv] {
                let mut cp = chart.device_ptr();
                self.launch("field_unframe", Self::cells((sites * m) as u64), THREADS, &mut [arg(words), arg(&mut cp)])?;
            }
            card.zero_octets(&dr, 0, 8 * sites * dw).map_err(device)?;
            for (weight, bias, chart) in [(words.q, words.q_bias, &dq), (words.k, words.k_bias, &dk), (words.v, words.v_bias, &dv)] {
                self.outer(words, g, weight, m2, dw, chart.device_ptr(), m2, tick.read.device_ptr(), dw, false, false)?;
                self.outer(words, g, bias, m2, 0, chart.device_ptr(), m2, 0, 0, false, false)?;
                self.transposed(words, weight, m2, dw, chart.device_ptr(), m2, dr.device_ptr(), true, false)?;
            }
            self.ratio_adjoint(words, tick.read.device_ptr(), tick.scale.device_ptr(), dr.device_ptr(), dmid.device_ptr(), dx.device_ptr(), false)?;
        }
        // The opening: each site's row of the encoding, the sites partitioned by row.
        let mut rows_off = vec![0u32; a + 2];
        for (t, &c) in classes.iter().enumerate() {
            let row = if unresolved[t] != 0 { a } else { c as usize };
            rows_off[row + 1] += 1;
        }
        for row in 0..=a {
            rows_off[row + 1] += rows_off[row];
        }
        let mut filled = rows_off.clone();
        let mut rows_sites = vec![0u32; sites];
        for (t, &c) in classes.iter().enumerate() {
            let row = if unresolved[t] != 0 { a } else { c as usize };
            rows_sites[filled[row] as usize] = t as u32;
            filled[row] += 1;
        }
        // Each row's sites cut into segments of at most `OUTER_TILE`, one thread a segment and a
        // column.
        let mut segments: Vec<u32> = Vec::new();
        for row in 0..=a {
            let (from, to) = (rows_off[row], rows_off[row + 1]);
            let mut at = from;
            while at < to {
                let end = to.min(at + OUTER_TILE as u32);
                segments.extend([row as u32, at, end]);
                at = end;
            }
        }
        let count = (segments.len() / 3) as u32;
        if count == 0 {
            return Ok(());
        }
        let rows_sites_c = self.timed(Kind::Copy, || card.upload(&rows_sites)).map_err(device)?;
        let segments_c = self.timed(Kind::Copy, || card.upload(&segments)).map_err(device)?;
        let (mut gp, mut dxp, mut rsp, mut sgp, mut count) = (g.device_ptr(), dx.device_ptr(), rows_sites_c.device_ptr(), segments_c.device_ptr(), count);
        self.launch("field_encoding", Self::cells(count as u64 * dw as u64), THREADS, &mut [arg(words), arg(&mut gp), arg(&mut dxp), arg(&mut rsp), arg(&mut sgp), arg(&mut count)])?;
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
/// the three charts and their framed copies, the masses, the current, the pair contact's read, scale
/// and drives) and its weights `H·S²`, the opening's and the face's carriers, and on a return the
/// reverse's per-site covectors and the contact's return `δs` (`S²` on 128 bits). Measured November 1:
/// sized by the weights and the contact's return alone, a batched release's per-site carriers took the
/// board to 13,372 MiB; sized by this, the same release peaked at 11,256 MiB.
pub fn region_octets(d: &FieldDeclaration, returning: bool, sites: usize) -> u64 {
    let (dw, m2, f, a, h, span) = (d.width as u64, 2 * d.complex() as u64, d.contacts as u64, d.alphabet as u64, d.heads as u64, 2 * d.modes as u64);
    let ticks_kept = if returning { d.ticks as u64 } else { 1 };
    let tick_site = 4 * dw + 16 + 8 * 3 * m2 + 3 * 8 * h * span + 8 * h + 8 * m2 + 4 * dw + 16 + 3 * 8 * f;
    let face_site = 8 * dw + 4 * dw + 16 + 8 * a + 8 * a + 16 + 16;
    let reverse_site = if returning { 8 * a + 5 * 8 * dw + 3 * 8 * f + 8 * m2 + 2 * 8 * h * span + 3 * 8 * m2 } else { 0 };
    let (s, pairs) = (sites as u64, (sites * sites) as u64);
    ticks_kept * (h * 8 * pairs + s * tick_site) + s * (face_site + reverse_site) + if returning { 16 * pairs } else { 0 }
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
        self.run(field, regions, true)
    }

    fn read_faces(&mut self, field: &Field, regions: &[Region]) -> Result<Vec<Vec<Option<TowerFace>>>> {
        Ok(self.run(field, regions, false)?.0)
    }
}

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
            let n = 1500u64;
            let weights = |returning: bool| (if returning { d.ticks as u64 } else { 1 }) * d.heads as u64 * 8 * n * n + if returning { 16 * n * n } else { 0 };
            for returning in [false, true] {
                let all = region_octets(&d, returning, n as usize);
                assert!(all > weights(returning));
                // The carriers grow by site, the weights by pair.
                assert_eq!(region_octets(&d, returning, 2 * n as usize) - 4 * weights(returning), 2 * (all - weights(returning)));
            }
        }
        let grown = declaration(64, 8, 64);
        let carriers = 128 * 1500 * (region_octets(&grown, false, 1) - grown.heads as u64 * 8);
        assert!(carriers > 1 << 30, "{carriers}");
    }
}

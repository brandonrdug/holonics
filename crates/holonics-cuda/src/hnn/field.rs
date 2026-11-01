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
//! regions are read in batches whose weight and contact stores fit the batch budget, the card's free
//! memory at the open less what the run keeps beside it, never past the 12 GB the runs keep to.
//! Batches sum their covectors on the card (integer sums: any batching gives the same bits).

use core::ffi::c_void;
use std::time::Instant;

use holonics::hnn::tower::field::{Field, FieldRealization, Region};
use holonics::hnn::tower::{TowerError, TowerFace};

use crate::cuda::{Dim3, Module};
use crate::hnn::card::{Card, CardBuffer};
use crate::hnn::DeviceError;

const IMAGE: &[u8] = include_bytes!(concat!(env!("OUT_DIR"), "/field.ptx"));
const THREADS: u32 = 256;
/// The device octets the runs keep to (the board's, the desktop included).
const BOARD_CEILING: u64 = 12 << 30;
/// Octets kept free beside a batch for its per-site carriers and the driver.
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
    /// The largest batch's weight and contact stores, in octets.
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

/// **The field on the card**: its image, the card it runs on and the octets a batch may take.
pub struct CardField<'c> {
    card: &'c Card,
    module: Module,
    budget: u64,
    times: FieldTimes,
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
        Ok(Self { card, module, budget, times: FieldTimes::default() })
    }

    /// The octets a batch's weight and contact stores may take.
    pub fn budget(&self) -> u64 {
        self.budget
    }

    pub fn times(&self) -> FieldTimes {
        self.times
    }

    fn launch(&self, entry: &'static str, grid: u32, block: u32, params: &mut [*mut c_void]) -> Result<()> {
        self.card.current().map_err(device)?;
        let function = self.module.function(entry).map_err(|e| device(e.into()))?;
        function.launch_on_shared(self.card.stream(), Dim3::x(grid.max(1)), Dim3 { x: block, y: 1, z: 1 }, 0, params).map_err(|e| device(e.into()))
    }

    /// A grid striding `cells` with one thread a cell.
    fn cells(cells: u64) -> u32 {
        cells.div_ceil(THREADS as u64).clamp(1, 65_535) as u32
    }

    /// A grid striding `rows` with one warp a row.
    fn warps(rows: u64) -> u32 {
        rows.div_ceil((THREADS / 32) as u64).clamp(1, 1 << 20) as u32
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
        let theta = card.upload(&field.theta).map_err(device)?;
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
        let phasor = card.upload(&phasor).map_err(device)?;
        let ring_off = card.upload(&ring_off).map_err(device)?;
        let ring_n = card.upload(&ring_n).map_err(device)?;
        let roots_card = card.upload(&roots).map_err(device)?;
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
        let g = if returning { Some(card.zeroed::<i128>(l.len).map_err(device)?) } else { None };
        // The batches: whole regions in order, each batch's stores within the budget.
        let ticks_kept = if returning { d.ticks } else { 1 };
        let store = |s: usize| -> u64 {
            let pairs = (s * s) as u64;
            (ticks_kept * heads) as u64 * 8 * pairs + if returning { 16 * pairs } else { 0 }
        };
        let mut batches: Vec<std::ops::Range<usize>> = Vec::new();
        let mut from = 0usize;
        let mut taken = 0u64;
        for (i, region) in regions.iter().enumerate() {
            let need = store(region.classes.len());
            if need > self.budget {
                return Err(TowerError::Realization(format!("a region of {} sites needs {need} octets of weights, past the card's batch budget of {}", region.classes.len(), self.budget)));
            }
            if taken + need > self.budget {
                batches.push(from..i);
                from = i;
                taken = 0;
            }
            taken += need;
        }
        batches.push(from..regions.len());
        let mut faces: Vec<Vec<Option<TowerFace>>> = Vec::with_capacity(regions.len());
        for batch in batches {
            if batch.is_empty() {
                continue;
            }
            let peak = regions[batch.clone()].iter().map(|r| store(r.classes.len())).sum::<u64>();
            self.times.peak_store = self.times.peak_store.max(peak);
            self.times.batches += 1;
            faces.extend(self.batch(field, &regions[batch], &mut words, g.as_ref())?);
        }
        let g = match g {
            Some(g) => card.fetch(&g).map_err(device)?,
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
        let alloc64 = |len: usize| card.alloc::<i64>(len.max(1)).map_err(device);
        Ok(Tick {
            read: card.alloc::<i32>((sites * dw).max(1)).map_err(device)?,
            scale: card.alloc::<i128>(sites.max(1)).map_err(device)?,
            qkv: alloc64(sites * 3 * m2)?,
            qf: alloc64(heads * sites * span)?,
            kf: alloc64(heads * sites * span)?,
            vf: alloc64(heads * sites * span)?,
            e: card.alloc::<u64>((heads * pairs).max(1)).map_err(device)?,
            mass: card.alloc::<u64>((heads * sites).max(1)).map_err(device)?,
            y: alloc64(sites * m2)?,
            read2: card.alloc::<i32>((sites * dw).max(1)).map_err(device)?,
            scale2: card.alloc::<i128>(sites.max(1)).map_err(device)?,
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
        let site_region_c = card.upload(&site_region).map_err(device)?;
        let site_pos_c = card.upload(&site_pos).map_err(device)?;
        let region_off_c = card.upload(&region_off).map_err(device)?;
        let region_eoff_c = card.upload(&region_eoff).map_err(device)?;
        let classes_c = card.upload(&classes).map_err(device)?;
        let unresolved_c = card.upload(&unresolved).map_err(device)?;
        let status = card.zeroed::<u32>(1).map_err(device)?;
        let x = card.alloc::<i64>(sites * dw).map_err(device)?;
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
        let fread = card.alloc::<i32>(sites * dw).map_err(device)?;
        let fscale = card.zeroed::<i128>(sites).map_err(device)?;
        let z = card.alloc::<i64>(sites * a).map_err(device)?;
        let masses = card.alloc::<u64>(sites * a).map_err(device)?;
        let totals = card.zeroed::<i128>(sites).map_err(device)?;
        self.chart(words, words.x, &fread, &fscale, true)?;
        self.affine("field_affine_x32", words, words.read, words.read_bias, words.rread, a, dw, fread.device_ptr(), dw, z.device_ptr(), a, 0, true)?;
        let (mut zp, mut mp, mut tp) = (z.device_ptr(), masses.device_ptr(), totals.device_ptr());
        self.launch("field_face", Self::warps(t64), THREADS, &mut [arg(words), arg(&mut zp), arg(&mut mp), arg(&mut tp)])?;
        if let Some(g) = g {
            self.reverse(field, words, &ticks, g, &fread, &fscale, &masses, &totals, &classes, &unresolved, sites, pairs)?;
        }
        self.status(&status)?;
        let masses = card.fetch(&masses).map_err(device)?;
        let totals = card.fetch(&totals).map_err(device)?;
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
        self.launch(entry, Self::cells(entries), THREADS, &mut [arg(words), arg(&mut gp), arg(&mut at), arg(&mut rows32), arg(&mut cols32), arg(&mut y), arg(&mut ys), arg(&mut x), arg(&mut xs), arg(&mut u)])
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
        let alloc64 = |len: usize| card.alloc::<i64>(len.max(1)).map_err(device);
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
        let ds = card.alloc::<i128>(pairs.max(1)).map_err(device)?;
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
                self.launch("field_contact_columns", Self::warps(sites as u64), THREADS, &mut [arg(words), arg(&mut hh), arg(&mut wrp), arg(&mut dsp), arg(&mut dkp), arg(&mut dvp)])?;
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
        let rows_off_c = card.upload(&rows_off).map_err(device)?;
        let rows_sites_c = card.upload(&rows_sites).map_err(device)?;
        let (mut gp, mut dxp, mut rop, mut rsp) = (g.device_ptr(), dx.device_ptr(), rows_off_c.device_ptr(), rows_sites_c.device_ptr());
        self.launch("field_encoding", Self::cells(((a + 1) * dw) as u64), THREADS, &mut [arg(words), arg(&mut gp), arg(&mut dxp), arg(&mut rop), arg(&mut rsp)])?;
        Ok(())
    }

    /// The batch's refusals, read off the card.
    fn status(&self, status: &CardBuffer<'c, u32>) -> Result<()> {
        let bits = self.card.fetch(status).map_err(device)?[0];
        if bits == 0 {
            return Ok(());
        }
        let names = [(1, "a sum outgrew its 128-bit carrier"), (2, "a released value outgrew its 64-bit carrier"), (4, "a released value outgrew its 32-bit carrier"), (8, "a current's covector outgrew its 128-bit carrier")];
        let named: Vec<&str> = names.iter().filter(|(b, _)| bits & b != 0).map(|(_, n)| *n).collect();
        Err(TowerError::Realization(format!("the card refused the field: {}", named.join("; "))))
    }
}

impl FieldRealization for CardField<'_> {
    fn read_and_return(&mut self, field: &Field, regions: &[Region]) -> Result<(Vec<Vec<Option<TowerFace>>>, Vec<i128>)> {
        self.run(field, regions, true)
    }

    fn read_faces(&mut self, field: &Field, regions: &[Region]) -> Result<Vec<Vec<Option<TowerFace>>>> {
        Ok(self.run(field, regions, false)?.0)
    }
}

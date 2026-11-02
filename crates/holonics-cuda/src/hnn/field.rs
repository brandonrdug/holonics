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

use holonics::hnn::tower::field::{band_bits, landmarks_of, Field, FieldDeclaration, FieldRead, FieldRealization, HeldPeak, HeldRows, Region, SHARE_BITS, STATE_BITS};
use holonics::hnn::tower::{TowerError, TowerFace, MATERIAL_BITS};

use crate::cuda::{Dim3, Module};
use crate::hnn::card::{Card, CardBuffer};
use crate::hnn::DeviceError;

const IMAGE: &[u8] = include_bytes!(concat!(env!("OUT_DIR"), "/field.ptx"));
const THREADS: u32 = 256;
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
    slots: u32,
    clocks: u32,
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
    clock: u64,
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
/// reach and the sign: [`Field::row_bits`] (its gain read from the largest temperature the material holds,
/// §15.10) with its spread bound (`4n |T| 2^(−24) + 1 + ⌊log₂ reach⌋ + 2`) replaced by the spread read. A spread
/// past that bound is refused (the bound is where a row ends), and so is a carrier past the twenty limbs the
/// card keeps.
pub fn row_limbs(field: &Field, spread: u64) -> Result<usize> {
    let d = &field.declaration;
    let top = field.theta[field.layout().temper..field.layout().temper + 2 * d.heads].iter().map(|v| v.unsigned_abs() as u128).max().unwrap_or(0);
    let gain = ((4 * d.modes as u128 * top) >> MATERIAL_BITS) as u64 + 1;
    let bound = gain + (usize::BITS - 1 - d.reach.leading_zeros()) as u64 + 2;
    if spread > bound {
        return Err(TowerError::Refused("a contact row holds exponents past the declaration's bound (`row_bits`)"));
    }
    let need = field.row_bits() as u64 - bound + spread;
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
}

/// One tick's carriers on the card.
struct Tick<'c> {
    read: Pooled<'c, i32>,
    scale: Pooled<'c, i128>,
    /// The word and the value, `[t][2·2M]`.
    qkv: Pooled<'c, i64>,
    qf: Pooled<'c, i64>,
    /// The unit words on 32 bits `[h][t][span]` (`field_unit` writes them beside `qf`).
    qf32: Pooled<'c, i32>,
    /// A listener's probe framed and at unit power by head (`[h][t][span]`, and on 32 bits) with its powers
    /// `[h][t]` (§15.12).
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
    pb: Pooled<'c, i64>,
    pc: Pooled<'c, i64>,
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
/// What a class cannot supply is allocated; when the live buffers, the kept ones and the new one pass the
/// batch budget, the kept ones are freed first. The contents of a taken buffer are undefined, zeroed where
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
    /// Free every kept buffer.
    fn trim(&mut self) {
        self.u8s.clear();
        self.u32s.clear();
        self.i32s.clear();
        self.u64s.clear();
        self.i64s.clear();
        self.i128s.clear();
        self.retained = 0;
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
            T::list(&mut pools).push((cap, buf));

        }
    }
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
    pools: std::rc::Rc<std::cell::RefCell<Pools<'c>>>,
    /// Whether a return carries the closure's comparison (§19); off only for [`FieldRealization::read_and_return_open`].
    closure: std::cell::Cell<bool>,
    /// A held read's rows by where their mass lies (a reading for the receipts): the regions' answer starts
    /// while it is read, and the cells `[tick · heads + head][rows, question, soft_near, other, current]` summed.
    held_questions: std::cell::RefCell<Option<Vec<usize>>>,
    held_cells: std::cell::RefCell<Vec<i128>>,
    /// A held read's answer rows by their concentration on the question (a reading for the receipts): the
    /// regions' answer starts and the digit classes while it is read, and the rows read, region by region.
    held_peaks: std::cell::RefCell<Option<(Vec<usize>, Vec<u8>)>>,
    peak_rows: std::cell::RefCell<Vec<HeldPeak>>,
    /// The host's wall time between marks, by name (`FIELD_PHASES`), no stream synchronized.
    phases: Option<std::cell::RefCell<(Instant, std::collections::BTreeMap<&'static str, (u64, u128)>)>>,
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
        Ok(Self { card, module, budget, times: FieldTimes::default(), profile: None, pools: Default::default(), closure: std::cell::Cell::new(true), held_questions: Default::default(), held_cells: Default::default(), held_peaks: Default::default(), peak_rows: Default::default(), phases: None })
    }

    /// The octets a batch's weight and contact stores may take.
    pub fn budget(&self) -> u64 {
        self.budget
    }

    pub fn times(&self) -> FieldTimes {
        self.times
    }

    /// A buffer of at least `len` elements, contents undefined (`Pooled`).
    fn take<T: Poolable>(&self, len: usize) -> std::result::Result<Pooled<'c, T>, DeviceError> {
        let cap = size_class(len.max(1));
        let octets = (cap * core::mem::size_of::<T>()) as u64;
        let mut pools = self.pools.borrow_mut();
        let hit = {
            let list = T::list(&mut pools);
            list.iter().position(|(c, _)| *c == cap).map(|i| list.swap_remove(i))
        };
        let entry = match hit {
            Some(entry) => {
                pools.retained = pools.retained.saturating_sub(octets);
                entry
            }
            None => {
                if pools.live + pools.retained + octets > self.budget {
                    pools.trim();
                }
                (cap, self.card.alloc::<T>(cap)?)
            }
        };
        pools.live += octets;
        Ok(Pooled { buf: Some(entry), pools: self.pools.clone() })
    }

    /// [`take`](Self::take) with every element zero.
    fn take_zeroed<T: Poolable>(&self, len: usize) -> std::result::Result<Pooled<'c, T>, DeviceError> {
        let buffer = self.take::<T>(len)?;
        self.card.zero_octets(&*buffer, 0, buffer.len() * core::mem::size_of::<T>())?;
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
        self.profile = Some(Default::default());
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
        if let Some(p) = &self.phases {
            let mut p = p.borrow_mut();
            let ns = p.0.elapsed().as_nanos();
            p.0 = Instant::now();
            let slot = p.1.entry(name).or_insert((0, 0));
            slot.0 += 1;
            slot.1 += ns;
        }
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
            if (!region.clock.is_empty() && (region.clock.len() != region.classes.len() || region.clock.iter().any(|&c| c as usize >= d.reach))) || (!region.echo.is_empty() && region.echo.len() != region.classes.len()) {
                return Err(TowerError::Refused("a region's clocks or echoes that are not one a site, or a clock past the reach"));
            }
            if region.echo.iter().flatten().any(|e| e.logits.len() != d.alphabet) {
                return Err(TowerError::Refused("an echo whose logits are not one a class"));
            }
        }
        self.mark("outside_the_card");
        let card = self.card;
        let started = Instant::now();
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

        // The skins `[h][d][n]` on 32 bits for the exposure's vector loads (eight modes a head; a still or clock head's
        // is the exact 1).
        let mut decay_t: Vec<u32> = Vec::new();
        if d.modes == 8 {
            let (frames, still_sets, reach) = (d.frames, d.still, d.reach);
            let per_set = frames - still_sets;
            for h in 0..d.heads {
                let set = h % frames;
                let not_turned = set < still_sets || set >= frames - d.clocks;
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
        let slots = crowd_slots(d.reach);
        if slots > MAX_CROWD_SLOTS {
            return Err(TowerError::Refused("the declaration's reach holds more crowds than a warp keeps (32)"));
        }
        // The exponential's resident face: `2^digits` words, held beside the batches and counted
        // against the same budget.
        let face_octets = Some(roots.len()).filter(|&digits| digits < 61).map(|digits| 8u64 << digits).filter(|&o| o < self.budget).ok_or(TowerError::Refused("the exponential's resident face passes the card's batch budget"))?;
        let face = self.timed(Kind::Alloc, || self.take::<u64>(1usize << roots.len())).map_err(device)?;
        let met = self.timed(Kind::Alloc, || self.take_zeroed::<u64>(1)).map_err(device)?;
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
            slots: slots as u32,
            clocks: d.clocks as u32,
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
            rb: reach(l.b, f * dw),
            rw: reach(l.w, dw * f),
            rread: reach(l.read, a * dw),
            phasor: run_base + phasor_at,
            ring_off: run_base + ring_off_at,
            ring_n: run_base + ring_n_at,
            decay: run_base + decay_at,
            decay_t: run_base + decay_t_at,
            dreach: d.reach as u64,
            roots: run_base + roots_at,
            met: met.device_ptr(),
            temper_at: l.temper as u64,
            probe: l.probe as u64,
            probe_bias: l.probe_bias as u64,
            rprobe: reach(l.probe, m2 * dw),
            ..Words::default()
        };
        // The exponential's resident face, read once by its own loop on the card.
        let mut face_ptr = face.device_ptr();
        self.launch("field_exponential", Self::cells(1u64 << roots.len()), THREADS, &mut [arg(&mut words), arg(&mut face_ptr)])?;
        words.face = face_ptr;
        let g = if returning { Some(self.timed(Kind::Alloc, || self.take_zeroed::<i128>(l.len)).map_err(device)?) } else { None };
        words.gcov = g.as_ref().map_or(0, |g| g.device_ptr());
        // The batches: whole regions in order, each batch's every allocation within the budget.
        // A landmark read stores one tick's weights beside a read's carriers; a logits read keeps every tick
        // and its shares (the echo's round trips, §15.3).
        let octets = |sites: usize| read_octets(&d, returning, logits, sites) + if keep.is_some() { 8 * (heads * sites * sites) as u64 } else { 0 };
        let lengths: Vec<usize> = regions.iter().map(|r| r.classes.len()).collect();
        // A pooled buffer is at most a quarter longer than asked (its size class), so the batches are cut at four
        // fifths of the budget.
        let batches = batches(&lengths, &octets, (self.budget - face_octets) / 5 * 4)?;
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
            let peak = lengths[batch.clone()].iter().map(|&n| octets(n)).sum::<u64>();
            self.times.peak_store = self.times.peak_store.max(peak);
            self.times.batches += 1;
            self.mark("run_setup");
            let (f, z, r, e) = self.batch(field, &regions[batch.clone()], batch.start, &mut words, g.as_deref(), logits, keep)?;
            self.mark("batch_drop_and_collect");
            faces.extend(f);
            read_logits.extend(z);
            rows.extend(r);
            echoes.extend(e);
        }
        let g = match g {
            Some(g) => self.timed(Kind::Copy, || card.fetch_range(&g, 0, l.len)).map_err(device)?,
            None => Vec::new(),
        };
        let met = self.timed(Kind::Copy, || card.fetch(&met)).map_err(device)?[0] as u128;
        if keep.is_some() {
            // A landmark read is a reading of a release's last state, counted apart.
            self.times.landmarks += 1;
            self.times.landmark_ns += started.elapsed().as_nanos();
            return Ok((faces, read_logits, g, rows, echoes));
        }
        self.times.pairs += met;
        if returning {
            self.times.returns += 1;
            self.times.return_ns += started.elapsed().as_nanos();
        } else {
            self.times.reads += 1;
            self.times.read_ns += started.elapsed().as_nanos();
        }
        Ok((faces, read_logits, g, rows, echoes))
    }

    fn tick(&self, sites: usize, pairs: usize, regions: usize, field: &Field, stored: bool, returning: bool) -> Result<Tick<'c>> {
        let d = field.declaration;
        let rows = sites + regions;
        let slots = crowd_slots(d.reach);
        let (dw, m2, f, heads, span) = (d.width, 2 * d.complex(), d.contacts, d.heads, 2 * d.modes);
        let classes = d.classes();
        let probe_stride = (1usize << d.class_trits()) - 1;
        let card = self.card;
        let alloc64 = |len: usize| self.timed(Kind::Alloc, || self.take::<i64>(len.max(1))).map_err(device);
        let alloc32 = |len: usize| self.timed(Kind::Alloc, || self.take::<u32>(len.max(1))).map_err(device);
        Ok(Tick {
            read: self.timed(Kind::Alloc, || self.take::<i32>((sites * dw).max(1))).map_err(device)?,
            scale: self.timed(Kind::Alloc, || self.take::<i128>(sites.max(1))).map_err(device)?,
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
            e: if stored { self.timed(Kind::Alloc, || self.take_zeroed::<u64>((heads * pairs).max(1))).map_err(device)? } else { self.timed(Kind::Alloc, || self.take::<u64>((heads * pairs).max(1))).map_err(device)? },
            amin: alloc64(heads * sites)?,
            sw: self.timed(Kind::Alloc, || self.take::<i128>((heads * rows * span).max(1))).map_err(device)?,
            sv: self.timed(Kind::Alloc, || self.take::<i128>((heads * rows * span).max(1))).map_err(device)?,
            sc: self.timed(Kind::Alloc, || self.take::<u64>((heads * rows).max(1))).map_err(device)?,
            ce: self.timed(Kind::Alloc, || self.take::<u64>(if stored { (heads * sites * slots).max(1) } else { 1 })).map_err(device)?,
            y: alloc64(sites * m2)?,
            read2: self.timed(Kind::Alloc, || self.take::<i32>((sites * dw).max(1))).map_err(device)?,
            scale2: self.timed(Kind::Alloc, || self.take::<i128>(sites.max(1))).map_err(device)?,
            pa: alloc64(sites * f)?,
            pb: alloc64(sites * f)?,
            pc: alloc64(sites * f)?,
            bits: self.timed(Kind::Alloc, || self.take_zeroed::<u32>(4)).map_err(device)?,
        })
    }

    /// One batch of regions: the forward, each unresolved site's face (and its logits when
    /// `logits`), when `g` is given the reverse added into it, and with `keep` the still heads'
    /// last-tick weight rows of those sites (the batch's one region).
    #[allow(clippy::type_complexity)]
    fn batch(&self, field: &Field, regions: &[Region], at_region: usize, words: &mut Words, g: Option<&CardBuffer<'c, i128>>, logits: bool, keep: Option<&[usize]>) -> Result<(Vec<Vec<Option<TowerFace>>>, Vec<Vec<Option<Vec<i64>>>>, Rows, Vec<Vec<u64>>)> {
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
        // Each site's clock (§15.4) and echo (§15.3): its `B`, and its logits a class (zero where none).
        let (mut clock, mut echo_has, mut echo_b, mut echo_logits) = (Vec::new(), Vec::new(), Vec::new(), Vec::new());
        let (mut mix_off, mut mix_class, mut mix_share) = (vec![0u32], Vec::new(), Vec::new());
        let mut pairs = 0usize;
        let any_echo = regions.iter().any(|r| r.echo.iter().any(Option::is_some));
        // Each region's definite sites and its open ones, by place (§15.9: an open receiver hears every definite
        // site, and a definite source is heard by every open one).
        let (mut dlist, mut dstart, mut olist, mut ostart) = (Vec::<u32>::new(), Vec::<u32>::new(), Vec::<u32>::new(), Vec::<u32>::new());
        for (r, region) in regions.iter().enumerate() {
            let s = region.classes.len();
            region_eoff.push(pairs as u64);
            pairs += s * s;
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
                } else {
                    olist.push(t as u32);
                }
                clock.push(region.clock.get(t).copied().unwrap_or(0));
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
        }
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
        let mut pack = Packed::default();
        let site_region_at = pack.put(&site_region);
        let site_pos_at = pack.put(&site_pos);
        let region_off_at = pack.put(&region_off);
        let region_eoff_at = pack.put(&region_eoff);
        let classes_at = pack.put(&classes);
        let unresolved_at = pack.put(&unresolved);
        let definite_at = pack.put(&definite);
        let clock_at = pack.put(&clock);
        let echo_has_at = pack.put(&echo_has);
        let echo_b_at = pack.put(&echo_b);
        let echo_logits_at = pack.put(&echo_logits);
        let mix_off_at = pack.put(&mix_off);
        let mix_class_at = pack.put(&mix_class_up);
        let mix_share_at = pack.put(&mix_share_up);
        let (dlist_at, dstart_at, olist_at, ostart_at) = (pack.put(&dlist), pack.put(&dstart), pack.put(&olist), pack.put(&ostart));
        let tables = self.timed(Kind::Copy, || self.take_up(&pack.bytes)).map_err(device)?;
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
        words.clock = base + clock_at;
        words.echo_has = base + echo_has_at;
        words.echo_b = base + echo_b_at;
        words.echo_logits = base + echo_logits_at;
        words.mix_off = base + mix_off_at;
        words.mix_class = base + mix_class_at;
        words.mix_share = base + mix_share_at;
        words.dlist = base + dlist_at;
        words.dstart = base + dstart_at;
        words.olist = base + olist_at;
        words.ostart = base + ostart_at;
        words.status = status.device_ptr();
        words.x = x.device_ptr();
        let returning = g.is_some();
        // The shares are stored for a return's reverse, for the rows `keep` reads, and for a logits read's
        // echo (§15.3: the round trips of consecutive ticks, so every tick is kept).
        let stored = returning || keep.is_some() || logits;
        let kept = returning || logits;
        let ticks: Vec<Tick> = (0..if kept { d.ticks } else { 1 }).map(|_| self.tick(sites, pairs, regions.len(), field, stored, returning)).collect::<Result<_>>()?;
        // The round trips a site's echo sums (128 bits a site), over the heads and the ticks.
        let trips = self.timed(Kind::Alloc, || self.take_zeroed::<i128>(sites.max(1))).map_err(device)?;
        words.trips = trips.device_ptr();
        // The site moments (§15.1), once for the pass, added into every tick's values.
        let moment = self.timed(Kind::Alloc, || self.take_zeroed::<i64>((sites * m2).max(1))).map_err(device)?;
        words.moment = moment.device_ptr();
        // A listener's probe chart of the read, once a tick (§15.12), framed and put at unit power by head.
        let pr = self.timed(Kind::Alloc, || self.take::<i64>((sites * m2).max(1))).map_err(device)?;
        words.pr = pr.device_ptr();
        self.moments(field, words, regions.len(), sites)?;
        let set = |w: &mut Words, tick: &Tick| {
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
            w.pb = tick.pb.device_ptr();
            w.pc = tick.pc.device_ptr();
            w.bits = tick.bits.device_ptr();
        };
        let t64 = sites as u64;
        // The class lists' shared words: the buckets `2·3^b`, and a chunk's keys `[32][2^b]` and counts.
        let buckets = 4 * 3 * d.classes() as u32;
        self.launch("field_open", Self::cells(t64 * dw as u64), THREADS, &mut [arg(words)])?;
        self.mark("batch_setup");
        for k in 0..d.ticks {
            let tick = &ticks[if kept { k } else { 0 }];
            set(words, tick);
            self.chart(words, words.x, &tick.read, &tick.scale, false)?;
            for (part, weight, bias, wmax) in [(0usize, words.q, words.q_bias, words.rq), (1, words.v, words.v_bias, words.rv)] {
                let out = tick.qkv.device_ptr() + (part * m2 * 8) as u64;
                self.affine("field_affine_x32", words, weight, bias, wmax, m2, dw, tick.read.device_ptr(), dw, out, 2 * m2, 0, false)?;
            }
            // A value is linear in its site's moment (§15.1).
            self.launch("field_moment_add", Self::cells((sites * m2) as u64), THREADS, &mut [arg(words)])?;
            card.zero_octets(&tick.bits, 0, 16).map_err(device)?;
            self.launch_shared("field_classes", (heads * regions.len()).clamp(1, 1 << 20) as u32, 32, buckets, &mut [arg(words)])?;
            self.launch("field_frame", Self::cells((heads * sites * n) as u64), THREADS, &mut [arg(words)])?;
            let mut qs = tick.qscale.device_ptr();
            self.launch("field_unit", Self::warps((heads * sites) as u64), THREADS, &mut [arg(words), arg(&mut qs)])?;
            self.affine("field_affine_x32", words, words.probe, words.probe_bias, words.rprobe, m2, dw, tick.read.device_ptr(), dw, pr.device_ptr(), m2, 0, false)?;
            self.launch("field_frame_probe", Self::cells((heads * sites * n) as u64), THREADS, &mut [arg(words)])?;
            let mut ps = tick.pscale.device_ptr();
            self.launch("field_unit_probe", Self::warps((heads * sites) as u64), THREADS, &mut [arg(words), arg(&mut ps)])?;
            // The definite sites' prefix sums (§14.10), read by the contact's crowds.
            self.launch("field_sums", Self::cells((heads * regions.len() * (2 * span + 1)) as u64), THREADS, &mut [arg(words)])?;
            let mut store = u32::from(stored);
            if keep.is_some() && k + 1 == d.ticks {
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
            let spread = self.timed(Kind::Copy, || card.fetch(&tick.bits)).map_err(device)?[1] as u64;
            if std::env::var_os("FIELD_SPREAD").is_some() {
                eprintln!("FIELD_SPREAD tick={k} sites={sites} spread={spread} bound_limbs={}", row_limbs(field, spread).map_or(0, |l| l));
            }
            self.mark("tick_exposure_wait");
            let limbs = row_limbs(field, spread)?;
            let contact: &'static str = ["field_contact_l5", "field_contact_l6", "field_contact_l7", "field_contact_l8", "field_contact_l9", "field_contact_l10", "field_contact_l11", "field_contact_l12", "field_contact_l13", "field_contact_l14", "field_contact_l15", "field_contact_l16", "field_contact_l17", "field_contact_l18", "field_contact_l19", "field_contact_l20"][limbs - MIN_LIMBS];
            self.launch(contact, Self::rows_grid((heads * sites) as u64, rows_per_block), (rows_per_block * 32) as u32, &mut [arg(words), arg(&mut store)])?;
            // The echo's round trips of this tick against the last (§15.3).
            if logits && k > 0 {
                words.e_prev = ticks[k - 1].e.device_ptr();
                self.launch("field_echo_trips", Self::rows_grid((heads * sites) as u64, rows_per_block), (rows_per_block * 32) as u32, &mut [arg(words)])?;
            }
            self.affine("field_affine_x64", words, words.out, words.out_bias, words.rout, dw, m2, tick.y.device_ptr(), m2, 0, dw, words.x, false)?;
            self.chart(words, words.x, &tick.read2, &tick.scale2, false)?;
            self.affine("field_affine_x32", words, words.wa, words.a_bias, words.ra, f, dw, tick.read2.device_ptr(), dw, tick.pa.device_ptr(), f, 0, false)?;
            self.affine("field_affine_x32", words, words.wb, words.b_bias, words.rb, f, dw, tick.read2.device_ptr(), dw, tick.pb.device_ptr(), f, 0, false)?;
            self.launch("field_pair", Self::cells((sites * f / 2) as u64), THREADS, &mut [arg(words)])?;
            self.affine("field_affine_x64", words, words.w, words.w_bias, words.rw, dw, f, tick.pc.device_ptr(), f, 0, dw, words.x, false)?;
            self.mark("tick_launch_post");
        }
        // A held read's rows by where their mass lies (a reading for the receipts): each kept tick's shares.
        if let Some(questions) = self.held_questions.borrow().as_ref() {
            let starts: Vec<u32> = (0..regions.len()).map(|r| questions[at_region + r] as u32).collect();
            let starts_c = self.timed(Kind::Copy, || self.take_up(&starts)).map_err(device)?;
            let acc = self.timed(Kind::Alloc, || self.take_zeroed::<i128>(d.ticks * heads * 5)).map_err(device)?;
            for (k, tick) in ticks.iter().enumerate() {
                set(words, tick);
                let (mut sp, mut tk, mut ap) = (starts_c.device_ptr(), k as u32, acc.device_ptr());
                self.launch("field_held_rows", Self::warps((heads * sites) as u64), THREADS, &mut [arg(words), arg(&mut sp), arg(&mut tk), arg(&mut ap)])?;
            }
            let cells = self.timed(Kind::Copy, || self.card.fetch_range(&*acc, 0, d.ticks * heads * 5)).map_err(device)?;
            let mut total = self.held_cells.borrow_mut();
            if total.is_empty() {
                total.resize(cells.len(), 0);
            }
            for (t, c) in total.iter_mut().zip(cells) {
                *t += c;
            }
        }
        // A held read's answer rows by their concentration on the question (a reading for the receipts).
        if let Some((questions, digit)) = self.held_peaks.borrow().as_ref() {
            let starts: Vec<u32> = (0..regions.len()).map(|r| questions[at_region + r] as u32).collect();
            let starts_c = self.timed(Kind::Copy, || self.take_up(&starts)).map_err(device)?;
            let digit_c = self.timed(Kind::Copy, || self.take_up(digit)).map_err(device)?;
            let mut cells = Vec::with_capacity(ticks.len());
            for tick in ticks.iter() {
                set(words, tick);
                let out = self.timed(Kind::Alloc, || self.take_zeroed::<i128>(heads * sites * 6)).map_err(device)?;
                let (mut sp, mut dp, mut op) = (starts_c.device_ptr(), digit_c.device_ptr(), out.device_ptr());
                self.launch("field_held_peaks", Self::warps((heads * sites) as u64), THREADS, &mut [arg(words), arg(&mut sp), arg(&mut dp), arg(&mut op)])?;
                cells.push(self.timed(Kind::Copy, || self.card.fetch_range(&*out, 0, heads * sites * 6)).map_err(device)?);
            }
            let mut rows = self.peak_rows.borrow_mut();
            for (r, region) in regions.iter().enumerate() {
                let first = region_off[r] as usize;
                for (k, cell) in cells.iter().enumerate() {
                    for h in 0..heads {
                        for t in (0..region.classes.len()).filter(|&t| region.unresolved[t]) {
                            let c = &cell[(h * sites + first + t) * 6..][..6];
                            rows.push(HeldPeak { tick: k as u32, head: h as u32, site: t as u32, question: c[0] as u128, collision: c[1] as u128, top: c[2] as u64, top_site: c[3] as u32, digits: c[4] as u128, right: c[5] as u128 });
                        }
                    }
                }
            }
        }
        // The faces at the unresolved sites.
        let fread = self.timed(Kind::Alloc, || self.take::<i32>(sites * dw)).map_err(device)?;
        let fscale = self.timed(Kind::Alloc, || self.take_zeroed::<i128>(sites)).map_err(device)?;
        let z = self.timed(Kind::Alloc, || self.take::<i64>(sites * a)).map_err(device)?;
        let masses = self.timed(Kind::Alloc, || self.take::<u64>(sites * a)).map_err(device)?;
        let totals = self.timed(Kind::Alloc, || self.take_zeroed::<i128>(sites)).map_err(device)?;
        self.chart(words, words.x, &fread, &fscale, true)?;
        self.affine("field_affine_x32", words, words.read, words.read_bias, words.rread, a, dw, fread.device_ptr(), dw, z.device_ptr(), a, 0, true)?;
        // The cavity field (§15.3): a carried site's read less its own echo.
        if echo_has.iter().any(|&h| h != 0) {
            let mut zp = z.device_ptr();
            self.launch("field_echo_apply", Self::cells((sites * a) as u64), THREADS, &mut [arg(words), arg(&mut zp)])?;
        }
        let (mut zp, mut mp, mut tp) = (z.device_ptr(), masses.device_ptr(), totals.device_ptr());
        self.launch("field_face", Self::warps(t64), THREADS, &mut [arg(words), arg(&mut zp), arg(&mut mp), arg(&mut tp)])?;
        self.mark("face_launch");
        if let Some(g) = g {
            self.reverse(field, words, &ticks, g, &fread, &fscale, &masses, &totals, &classes, &unresolved, &site_pos, &mix_off, &mix_class, &mix_share, sites, pairs)?;
        }
        self.mark("reverse_launch");
        self.status(&status)?;
        self.mark("status_wait");
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
        Ok((out, out_z, rows, out_echo))
    }

    /// [definition; agent-inferred, November 1] **The site moments of a batch** (§15.1; the host's
    /// `Field::moments_of`, [`holonics::hnn::tower::field::moment`]), every moment mode (a turned head that
    /// is not a clock, each of its modes) in the same launches: the strands' encodings of each mode's ring
    /// slot gathered at every site (`field_moment_strands_all`), admitted by the l1 certificate, scanned to
    /// the prefix sums and read at every site (`kernels/field_moment.cuh` through its `_all` entries, a mode
    /// to a grid row), and placed at the unframed value's modes.
    fn moments(&self, field: &Field, words: &Words, regions: usize, sites: usize) -> Result<()> {
        let d = field.declaration;
        let tm = d.moment_modes();
        if tm == 0 {
            return Ok(());
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
        let grid = |x: usize| Dim3 { x: x.max(1) as u32, y: tm as u32, z: 1 };
        let _ = n;
        self.launch("field_moment_strands_all", Self::cells((sites * tm) as u64), THREADS, &mut [arg(&mut w2), arg(&mut base_b), arg(&mut base_a), arg(&mut tm32), arg(&mut bp), arg(&mut ap)])?;
        self.launch_grid("field_moment_admit_all", grid(regions), MOMENT_BLOCK, 3 * MOMENT_BLOCK * 16, &mut [arg(&mut wsp), arg(&mut bp), arg(&mut ap), arg(&mut stride), arg(&mut zero32)])?;
        self.launch_grid("field_moment_prefix_all", grid(regions), MOMENT_BLOCK, MOMENT_BLOCK * 32, &mut [arg(&mut wsp), arg(&mut bp), arg(&mut upp), arg(&mut stride), arg(&mut pre_stride), arg(&mut zero32)])?;
        self.launch_grid("field_moment_prefix_all", grid(regions), MOMENT_BLOCK, MOMENT_BLOCK * 32, &mut [arg(&mut wsp), arg(&mut ap), arg(&mut dnp), arg(&mut stride), arg(&mut pre_stride), arg(&mut zero32)])?;
        self.launch_grid("field_moment_all", Dim3 { x: Self::cells(sites as u64), y: tm as u32, z: 1 }, THREADS, 0, &mut [arg(&mut wsp), arg(&mut bp), arg(&mut ap), arg(&mut upp), arg(&mut dnp), arg(&mut sp), arg(&mut stride), arg(&mut pre_stride)])?;
        self.launch("field_moment_scatter_all", Self::cells((sites * tm) as u64), THREADS, &mut [arg(&mut w2), arg(&mut sp), arg(&mut cmp), arg(&mut tm32)])?;
        let _ = &mut none;
        Ok(())
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
                cmap.push((h * d.modes + li) as u32);
            }
        }
        let card = self.card;
        Ok((self.timed(Kind::Copy, || self.take_up(&packed)).map_err(device)?, self.timed(Kind::Copy, || self.take_up(&cmap)).map_err(device)?))
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
        let alloc64 = |len: usize| self.timed(Kind::Alloc, || self.take::<i64>(len.max(1))).map_err(device);
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
        // A listener's probe role, its own chart's covector (§15.12).
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
        // The face.
        let (mut mp, mut tp, mut dzp) = (masses.device_ptr(), totals.device_ptr(), dz.device_ptr());
        self.launch("field_face_covector", Self::cells((sites * a) as u64), THREADS, &mut [arg(words), arg(&mut mp), arg(&mut tp), arg(&mut dzp)])?;
        self.outer(words, g, words.read_bias, a, 0, dz.device_ptr(), a, 0, 0, false, true)?;
        self.outer(words, g, words.read, a, dw, dz.device_ptr(), a, fread.device_ptr(), dw, false, true)?;
        self.transposed(words, words.read, a, dw, dz.device_ptr(), a, dr.device_ptr(), false, true)?;
        self.ratio_adjoint(words, fread.device_ptr(), fscale.device_ptr(), dr.device_ptr(), 0, dx.device_ptr(), true)?;
        for (at, tick) in ticks.iter().enumerate().rev() {
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
            words.pb = tick.pb.device_ptr();
            words.pc = tick.pc.device_ptr();
            // The pair contact: x_out = x_mid + W_c c + b_c.
            self.outer(words, g, words.w_bias, dw, 0, dx.device_ptr(), dw, 0, 0, false, false)?;
            self.outer(words, g, words.w, dw, f, dx.device_ptr(), dw, tick.pc.device_ptr(), f, true, false)?;
            self.transposed(words, words.w, dw, f, dx.device_ptr(), dw, dc.device_ptr(), false, false)?;
            let (mut dcp, mut dap, mut dbp) = (dc.device_ptr(), da.device_ptr(), db.device_ptr());
            self.launch("field_pair_back", Self::cells((sites * f / 2) as u64), THREADS, &mut [arg(words), arg(&mut dcp), arg(&mut dap), arg(&mut dbp)])?;
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
            card.zero_octets(&dp, 0, 8 * sites * m2).map_err(device)?;
            for h in 0..heads {
                // The crowds' difference arrays start empty a head (§14.10).
                card.zero_octets(&cv, 0, 16 * rows * span).map_err(device)?;
                card.zero_octets(&cw, 0, 16 * rows * span).map_err(device)?;
                let (mut hh, mut closes, mut dyhp, mut dsp, mut dqp) = (h as u32, if self.closure.get() && field.declaration.closes(at, h) { field.declaration.copies() as u32 } else { 0 }, dyh.device_ptr(), ds.device_ptr(), dq.device_ptr());
                self.launch("field_contact_rows", Self::rows_grid(sites as u64, REV_ROWS), (REV_ROWS * 32) as u32, &mut [arg(words), arg(&mut hh), arg(&mut closes), arg(&mut dyhp), arg(&mut dsp), arg(&mut dqp)])?;
                let (mut hh, mut dyhp, mut dsp, mut dqp, mut dvp) = (h as u32, dyh.device_ptr(), ds.device_ptr(), dq.device_ptr(), dv.device_ptr());
                self.launch("field_contact_columns", Self::rows_grid(sites as u64, CONTACT_ROWS), (CONTACT_ROWS * 32) as u32, &mut [arg(words), arg(&mut hh), arg(&mut dyhp), arg(&mut dsp), arg(&mut dqp), arg(&mut dvp)])?;
                let (mut hh, mut dqp, mut dvp) = (h as u32, dq.device_ptr(), dv.device_ptr());
                self.launch("field_spread", (regions as u32).clamp(1, 65_535), THREADS, &mut [arg(words), arg(&mut hh), arg(&mut dqp), arg(&mut dvp)])?;
            }
            let (mut qs, mut dqp) = (tick.qscale.device_ptr(), dq.device_ptr());
            self.launch("field_unit_back", Self::warps((heads * sites) as u64), THREADS, &mut [arg(words), arg(&mut qs), arg(&mut dqp)])?;
            // The probe's return through its own power, alike (§15.12).
            let (mut ps, mut dpp) = (tick.pscale.device_ptr(), dp.device_ptr());
            self.launch("field_unit_back_probe", Self::warps((heads * sites) as u64), THREADS, &mut [arg(words), arg(&mut ps), arg(&mut dpp)])?;
            for chart in [&dq, &dv, &dp] {
                let mut cp = chart.device_ptr();
                self.launch("field_unframe", Self::cells((sites * m) as u64), THREADS, &mut [arg(words), arg(&mut cp)])?;
            }
            // The values' covector, summed over the ticks, for the moments (§15.1).
            let (mut dvp, mut dmp) = (dv.device_ptr(), dm.device_ptr());
            self.launch("field_moment_accumulate", Self::cells((sites * m2) as u64), THREADS, &mut [arg(words), arg(&mut dvp), arg(&mut dmp)])?;
            card.zero_octets(&dr, 0, 8 * sites * dw).map_err(device)?;
            for (weight, bias, chart) in [(words.q, words.q_bias, &dq), (words.v, words.v_bias, &dv), (words.probe, words.probe_bias, &dp)] {
                self.outer(words, g, weight, m2, dw, chart.device_ptr(), m2, tick.read.device_ptr(), dw, false, false)?;
                self.outer(words, g, bias, m2, 0, chart.device_ptr(), m2, 0, 0, false, false)?;
                self.transposed(words, weight, m2, dw, chart.device_ptr(), m2, dr.device_ptr(), true, false)?;
            }
            self.ratio_adjoint(words, tick.read.device_ptr(), tick.scale.device_ptr(), dr.device_ptr(), dmid.device_ptr(), dx.device_ptr(), false)?;
        }
        // The moments' return (§15.1): each moment mode's value covector, summed over the ticks, through the
        // strands to the families (the host's `moments_return`).
        self.moments_return(field, words, g, &dm, regions, sites)?;
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
        Ok(())
    }

    /// [definition; agent-inferred, November 1] **The moments' return** (the host's `Field::moments_return`,
    /// the released law of §15.1): every moment mode's covector `dm` at its value (fit to 64 bits), admitted by
    /// the return's certificate, the prefix of the covector turned and released once a term, the return at
    /// every site, and the strands' encodings' rows (or a carried site's classes by their shares) added into
    /// `g`; all modes in the same launches.
    fn moments_return(&self, field: &Field, words: &Words, g: &CardBuffer<'c, i128>, dm: &CardBuffer<'c, i128>, regions: usize, sites: usize) -> Result<()> {
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
        let (mut wsp, mut cmp, mut dmp) = (ws.device_ptr(), cmap.device_ptr(), dm.device_ptr());
        let (mut dsp, mut qp, mut dbp, mut dap, mut gp, mut none) = (ds.device_ptr(), q.device_ptr(), d_before.device_ptr(), d_after.device_ptr(), g.device_ptr(), 0u64);
        let (mut w2, mut base_b, mut base_a, mut tm32) = (*words, l.moment_before as u64, l.moment_after as u64, tm as u32);
        let (mut one32, mut stride, mut pre_stride) = (1u32, strand, prefix);
        let grid = |x: usize| Dim3 { x: x.max(1) as u32, y: tm as u32, z: 1 };
        self.launch("field_moment_ds_all", Self::cells((sites * tm) as u64), THREADS, &mut [arg(&mut w2), arg(&mut dmp), arg(&mut cmp), arg(&mut tm32), arg(&mut dsp)])?;
        self.launch_grid("field_moment_admit_all", grid(regions), MOMENT_BLOCK, 3 * MOMENT_BLOCK * 16, &mut [arg(&mut wsp), arg(&mut dsp), arg(&mut none), arg(&mut stride), arg(&mut one32)])?;
        self.launch_grid("field_moment_prefix_all", grid(regions), MOMENT_BLOCK, MOMENT_BLOCK * 32, &mut [arg(&mut wsp), arg(&mut dsp), arg(&mut qp), arg(&mut stride), arg(&mut pre_stride), arg(&mut one32)])?;
        self.launch_grid("field_moment_return_all", Dim3 { x: Self::cells(sites as u64), y: tm as u32, z: 1 }, THREADS, 0, &mut [arg(&mut wsp), arg(&mut dsp), arg(&mut qp), arg(&mut dbp), arg(&mut dap), arg(&mut stride), arg(&mut pre_stride)])?;
        self.launch("field_moment_strand_return_all", Self::cells((sites * tm) as u64), THREADS, &mut [arg(&mut w2), arg(&mut base_b), arg(&mut base_a), arg(&mut tm32), arg(&mut dbp), arg(&mut dap), arg(&mut gp)])?;
        Ok(())
    }

    /// The batch's refusals, read off the card.
    fn status(&self, status: &CardBuffer<'c, u32>) -> Result<()> {
        let bits = self.timed(Kind::Copy, || self.card.fetch(status)).map_err(device)?[0];
        if bits == 0 {
            return Ok(());
        }
        let names = [(1, "a sum outgrew its 128-bit carrier"), (2, "a released value outgrew its 64-bit carrier"), (4, "a released value outgrew its 32-bit carrier"), (8, "a current's covector outgrew its 128-bit carrier"), (16, "a moment's strand outruns its resident ring or skin")];
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
    read_octets(d, returning, false, sites)
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
    let probe_site = 4 * h * (1 + 2 * ((1u64 << d.class_trits()) - 1));
    let tick_site = 4 * dw + 16 + 8 * 2 * m2 + 2 * 8 * h * span + 16 * h + 8 * h + 4 * h + 4 * h + 8 * m2 + 4 * dw + 16 + 3 * 8 * f + (2 * 16 * span + 8) * h + 8 * h * slots + probe_site + 4 * h * span + 8 * h * span + 4 * h * span + 16 * h;
    let tick_fixed = tick_fixed_octets(d);
    let face_site = 8 * dw + 4 * dw + 16 + 8 * a + 8 * a + 16 + 16;
    // A site's carried mixture, definite bit, clock, echo (a flag, `B` and logits) and the round trips.
    let mixture_site = 5 + 2 * 4 * a + 4 + 9 + 8 * a + 16;
    // The moments: the pass's values `[t][2M]`, and a mode's strands, moments, prefix sums and admission
    // (112 octets a site), batched over the modes.
    let tm = d.moment_modes() as u64;
    let moment_site = if tm > 0 { 8 * m2 + 112 * tm } else { 0 };
    // The reverse adds its covectors, the values' sum over the ticks and the moments' return, and the
    // crowds' two difference arrays.
    let reverse_site = if returning { 8 * m2 + 8 * a + 5 * 8 * dw + 3 * 8 * f + 8 * m2 + 8 * h * span + 2 * 8 * m2 + 16 * m2 + 2 * 16 * span + 112 * tm } else { 0 };
    let (s, pairs) = (sites as u64, (sites * sites) as u64);
    // The shares are kept for a return and an echo; the reverse holds one head's covector a pair on 64 bits.
    let weights = h * 8 * pairs * if returning { 2 } else { 1 };
    ticks_kept * (weights + s * tick_site + tick_fixed) + s * (face_site + mixture_site + moment_site + reverse_site + 8 * m2) + if returning { 24 * pairs } else { 0 }
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
        let (faces, _, g, _, _) = self.run(field, regions, true, false, None)?;
        Ok((faces, g))
    }

    fn read_faces(&mut self, field: &Field, regions: &[Region]) -> Result<Vec<Vec<Option<TowerFace>>>> {
        Ok(self.run(field, regions, false, false, None)?.0)
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

    fn read_and_return_open(&mut self, field: &Field, regions: &[Region]) -> Result<(Vec<Vec<Option<TowerFace>>>, Vec<i128>)> {
        self.closure.set(false);
        let read = self.run(field, regions, true, false, None);
        self.closure.set(true);
        let (faces, _, g, _, _) = read?;
        Ok((faces, g))
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
        let cells = if cells.is_empty() { vec![0i128; ticks * heads * 5] } else { cells };
        Ok(cells.chunks_exact(5).map(|c| HeldRows { rows: c[0] as u64, question: c[1] as u128, soft_near: c[2] as u128, other: c[3] as u128, question_current: c[4] }).collect())
    }

    fn read_row_peaks(&mut self, field: &Field, regions: &[Region], questions: &[usize], digit: &[bool]) -> Result<Vec<HeldPeak>> {
        if regions.len() != questions.len() || digit.len() != field.declaration.alphabet {
            return Err(TowerError::Refused("a held read's answer starts that are not one a region, or digit classes not one a class"));
        }
        // The shares of every tick are kept (a logits read keeps them), and read once each by `field_held_peaks`.
        *self.held_peaks.borrow_mut() = Some((questions.to_vec(), digit.iter().map(|&b| u8::from(b)).collect()));
        self.peak_rows.borrow_mut().clear();
        let read = self.run(field, regions, false, true, None);
        *self.held_peaks.borrow_mut() = None;
        read?;
        Ok(std::mem::take(&mut *self.peak_rows.borrow_mut()))
    }
}

/// Each kept site's still heads' rows: the met sources with their weights, and the row's mass.
type Rows = Vec<Vec<(Vec<(u32, u64)>, u64)>>;

#[cfg(test)]
mod tests {
    use super::*;

    fn declaration(width: usize, heads: usize, contacts: usize) -> FieldDeclaration {
        FieldDeclaration { alphabet: 122, width, heads, modes: 8, still: 2, contacts, ticks: 2, frames: 4, reach: 2221, clocks: 0 }
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

    /// The carrier follows the spread read and is the declaration's `row_bits` at its bound: a row of the
    /// widest spread the declaration allows needs exactly `row_bits`, one past it is refused.
    #[test]
    fn the_carrier_follows_the_spread_and_ends_at_the_declarations_bound() {
        let d = declaration(32, 4, 32);
        let keys: Vec<u8> = (0..1u64 << 18).flat_map(|i| (i.wrapping_add(1).wrapping_mul(0x9E37_79B9_7F4A_7C15) ^ (i << 17)).to_be_bytes()).collect();
        let field = Field::found(d, &keys).unwrap();
        // The gain is read from the largest temperature the material holds (§15.10).
        let l = field.layout();
        let top = field.theta[l.temper..l.temper + 2 * d.heads].iter().map(|v| v.unsigned_abs() as u128).max().unwrap();
        let gain = ((4 * d.modes as u128 * top) >> MATERIAL_BITS) as u64 + 1;
        let bound = gain + (usize::BITS - 1 - d.reach.leading_zeros()) as u64 + 2;
        assert_eq!(row_limbs(&field, bound).ok(), Some((field.row_bits() as usize).div_ceil(64).max(MIN_LIMBS)).filter(|&l| l <= MAX_LIMBS));
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
            // pair on 64 bits, and one tick's otherwise; each kept tick adds its carrier widths and class offsets.
            let weights = |returning: bool| if returning { d.ticks as u64 * d.heads as u64 * 16 * n * n + 24 * n * n } else { d.heads as u64 * 8 * n * n };
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

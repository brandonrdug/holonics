//! **The resident realization: a batch's state on the card and the schedule of its phases.** `Resident` implements the host's
//! `Realization` (`crates/engine/src/realization.rs`): the constitution uploaded whole, a section's regions packed into batches that fit
//! the card's measured memory, the forward's ticks and the reverse run over them, and the faces, logits and covectors fetched back. Its
//! own launches are the batch's base, the opening, the faces and the readings' gathers. THE_ENGINE §3 lists each kernel beside the
//! phase it serves, and the host is the reference these bits are read against (`athena parity`).

#[allow(unused_imports)]
use crate::hnn::field::*;
#[allow(unused_imports)]
use core::ffi::c_void;
#[allow(unused_imports)]
use std::time::Instant;
use rayon::prelude::*;
#[allow(unused_imports)]
use holonics_engine::field::{band_bits, landmarks_of, BlankClocks, CarryGates, Constitution, Declaration, ReadLogits, Realization, HeldRows, NearOffsets, RealizationCounters, RowCurrent, Region, Scale, TickRead, NEAR, SHARE_BITS, STATE_BITS};
#[allow(unused_imports)]
use holonics_engine::field::{level_cut, level_section, PACE_BITS};
#[allow(unused_imports)]
use holonics_engine::field::{TowerError, TowerFace, MATERIAL_BITS, UNCOMPARED};
#[allow(unused_imports)]
use crate::cuda::{Dim3, Module};
#[allow(unused_imports)]
use crate::hnn::card::{Card, CardBuffer, CardError};

pub(crate) const IMAGE: &[u8] = include_bytes!(concat!(env!("OUT_DIR"), "/field.ptx"));

pub(crate) const THREADS: u32 = 256;
/// [realization; November 15] The sites a thread of the open places' per-entry sums walks (the kernels' `BLANK_TILE`).
pub(crate) const BLANK_TILE: u64 = 512;
/// [realization; November 16] The blocks of `field_spread` (a region a block) and `field_sums` (a head and a region a block), the kernels'
/// `SPREAD_THREADS` and `SUMS_THREADS`.
pub(crate) const SPREAD_THREADS: u32 = 672;
pub(crate) const SUMS_THREADS: u32 = 1024;
/// [realization; November 16] The block of `field_blank_live_scan`, one block a batch (the kernel's `BLANK_SCAN_THREADS`).
pub(crate) const BLANK_SCAN_THREADS: u32 = 1024;
/// [realization; November 15] The block of `field_paces`, whose clocks are block scans (the kernel's `PACE_SCAN_THREADS`).
pub(crate) const PACE_SCAN_THREADS: u32 = 256;
/// [realization; November 15] The block of `field_blank_dz`, one block a site (the kernel's `BLANK_DZ_THREADS`).
pub(crate) const BLANK_DZ_THREADS: u32 = 256;

/// The device octets the runs keep to (the board's, the desktop included): 14.5 GiB of the 4080 SUPER's 16, about 1.5 GiB left to the
/// desktop (Brandon, November 19 19:24 UTC; 12 GiB before, under which a section of the store line was cut into three batches).
pub(crate) const BOARD_CEILING: u64 = 29 << 29;

/// Octets kept free beside a batch's counted allocations for the driver, the material and the
/// allocator's grain.
pub(crate) const MARGIN: u64 = 1 << 30;

pub(crate) type Result<T> = std::result::Result<T, TowerError>;

pub(crate) fn device(error: CardError) -> TowerError {
    TowerError::Realization(format!("the card: {error}"))
}

/// The batch's words (`FieldWords` in `kernels/field.cu`, field for field).
#[repr(C)]
#[derive(Clone, Copy, Default)]
pub(crate) struct Words {
    pub(crate) d: u32,
    pub(crate) h: u32,
    pub(crate) n: u32,
    pub(crate) still: u32,
    pub(crate) f: u32,
    pub(crate) a: u32,
    pub(crate) frames: u32,
    pub(crate) lanes: u32,
    pub(crate) beta: i32,
    pub(crate) ctrits: u32,
    pub(crate) nclasses: u32,
    pub(crate) dsbits: u32,
    pub(crate) m: u32,
    pub(crate) m2: u32,
    pub(crate) span: u32,
    pub(crate) digits: u32,
    pub(crate) t: u32,
    pub(crate) r: u32,
    pub(crate) slots: u32,
    pub(crate) band: u32,
    pub(crate) pairs: u64,
    pub(crate) ln2_lo: u64,
    pub(crate) ln2_hi: u64,
    pub(crate) theta: u64,
    pub(crate) enc: u64,
    pub(crate) enc_before: u64,
    pub(crate) enc_after: u64,
    pub(crate) q: u64,
    pub(crate) q_bias: u64,
    pub(crate) v: u64,
    pub(crate) v_bias: u64,
    pub(crate) out: u64,
    pub(crate) out_bias: u64,
    pub(crate) wa: u64,
    pub(crate) a_bias: u64,
    pub(crate) wb: u64,
    pub(crate) b_bias: u64,
    pub(crate) w: u64,
    pub(crate) w_bias: u64,
    pub(crate) read: u64,
    pub(crate) read_bias: u64,
    pub(crate) rq: u64,
    pub(crate) rv: u64,
    pub(crate) rout: u64,
    pub(crate) ra: u64,
    pub(crate) rb: u64,
    pub(crate) rw: u64,
    pub(crate) rread: u64,
    pub(crate) phasor: u64,
    pub(crate) ring_off: u64,
    pub(crate) ring_n: u64,
    pub(crate) decay: u64,
    pub(crate) dreach: u64,
    pub(crate) roots: u64,
    pub(crate) site_region: u64,
    pub(crate) site_pos: u64,
    pub(crate) region_off: u64,
    pub(crate) region_eoff: u64,
    pub(crate) classes: u64,
    pub(crate) unresolved: u64,
    pub(crate) definite: u64,
    // [E] Each site's row computed where its region's room is cut to its windows (`Region::window`); none where no region of
    // the batch is cut.
    pub(crate) computed: u64,
    // Each site whose blank face a clock reads: silent, and at or before its region's silent stretch's first place (every
    // silent site under the per-blank clock). The blank clock's face kernels read these sites alone.
    pub(crate) blank_read: u64,
    pub(crate) mix_off: u64,
    pub(crate) mix_class: u64,
    pub(crate) mix_share: u64,
    pub(crate) status: u64,
    pub(crate) met: u64,
    pub(crate) x: u64,
    pub(crate) qkv: u64,
    pub(crate) qf: u64,
    pub(crate) vf: u64,
    pub(crate) cls: u64,
    pub(crate) class_off: u64,
    pub(crate) members: u64,
    pub(crate) pn: u64,
    pub(crate) pcls: u64,
    pub(crate) poff: u64,
    pub(crate) pmem: u64,
    pub(crate) e: u64,
    pub(crate) e_prev: u64,
    pub(crate) y: u64,
    pub(crate) pa: u64,
    pub(crate) pb: u64,
    pub(crate) pc: u64,
    pub(crate) bits: u64,
    pub(crate) face: u64,
    pub(crate) amin: u64,
    pub(crate) sw: u64,
    pub(crate) sv: u64,
    pub(crate) sc: u64,
    pub(crate) ce: u64,
    pub(crate) cv: u64,
    pub(crate) cw: u64,
    pub(crate) moment: u64,
    pub(crate) echo_has: u64,
    pub(crate) echo_b: u64,
    pub(crate) echo_logits: u64,
    pub(crate) trips: u64,
    pub(crate) qf32: u64,
    pub(crate) decay_t: u64,
    pub(crate) dpb: u64,
    pub(crate) dlist: u64,
    pub(crate) dstart: u64,
    pub(crate) olist: u64,
    pub(crate) ostart: u64,
    pub(crate) temper_at: u64,
    /// [the lead, November 21] Each head's friction of distance (`theta[friction_at + 2 h + kind]` on `2^(−16)` bits an octave,
    /// [`holonics_engine::field::Declaration::friction`]); `u64::MAX` where the field has none.
    pub(crate) friction_at: u64,
    /// [the lead, November 21] The friction's gate (`theta[gate_at + h D + i]`, `a_h` on `2^(−24)`,
    /// [`holonics_engine::field::Declaration::friction_gate`]; `u64::MAX` where none), its largest word, and the tick's gate `[t][H]` on
    /// `2^(−16)` bits an octave and its covector `[t][H]` on `2^(−24)` (zero pointers where none).
    pub(crate) gate_at: u64,
    pub(crate) rgate: u64,
    pub(crate) fgate: u64,
    pub(crate) dfgate: u64,
    pub(crate) fine_roots: u64,
    pub(crate) gcov: u64,
    pub(crate) sb: u64,
    pub(crate) pr: u64,
    pub(crate) pq: u64,
    pub(crate) pq32: u64,
    pub(crate) pscale: u64,
    pub(crate) dp: u64,
    pub(crate) probe: u64,
    pub(crate) probe_bias: u64,
    pub(crate) rprobe: u64,
    // The turned heads' own clocks (§16, `FieldWords`' tail, field for field).
    pub(crate) paced: u32,
    pub(crate) pace_at: u64,
    pub(crate) pi_lo: u64,
    pub(crate) pi_hi: u64,
    pub(crate) kappa: u64,
    pub(crate) tau: u64,
    pub(crate) sigma: u64,
    pub(crate) plain: u64,
    pub(crate) pframe: u64,
    pub(crate) gtau: u64,
    pub(crate) gsig: u64,
    pub(crate) cds: u64,
    pub(crate) dsshare: u64,
    // [§16.44] A tick's blanks' rates, and the face they were read from (zero where the tick reads the pass's clocks).
    pub(crate) blank_rate: u64,
    pub(crate) blank_masses: u64,
    pub(crate) blank_totals: u64,
    // [measurement] Every silent place runs its own rate past the last arrival too (the host's `Constitution::per_blank_clock`).
    pub(crate) per_blank: u64,
    // The depth rings' count (`Declaration::depth`).
    pub(crate) depth: u64,
    // [the unified-theory reading of November 6, 10:31] Past the last arrival a silent place runs at the bare rate (the host's
    // `Constitution::bare_stretch`).
    pub(crate) bare_stretch: u64,
    // [definition; theory, November 11 17:25 and November 12 (G98)] The carry circles (`Declaration::carry`): their count `C`, their charts' and
    // biases' offsets in the material (`Loci::carry`, `carry_bias`) and the charts' reach, and (set per tick) the charts' reads `q`, `ℓ` `[t][2C]`,
    // the gate `γ` `[t][2C]`, the scan's operand `[t][2C]` and the drive coupled through the leak `[t][2C]`.
    pub(crate) carry: u64,
    pub(crate) wg: u64,
    pub(crate) wgb: u64,
    pub(crate) rg: u64,
    pub(crate) pg: u64,
    pub(crate) pgam: u64,
    pub(crate) pqm: u64,
    pub(crate) pkb: u64,
    // [theory, November 11 04:14, step S] The skin's site addresses `[p][l][t]` three words each (`FieldWords::saddr`), the clock's own beside `sigma`.
    pub(crate) saddr: u64,
    // [definition; theory, November 12; the triad record (`2026-11-12_THE_LAW_ACROSS_A_PLACE_IS_HELD_BY_A_PUMPED_CONTACT…`) §3 and §4] The triads
    // (`Declaration::triads`): their count `J`, the chart's and its biases' offsets in the material (`Loci::triad`, `triad_bias`) and the
    // chart's reach, the return's offset (`Loci::w_triad`) and reach, and (set per tick) the chart's read `abg` `[t][6J]` and the products `p`
    // and `c^T` `[t][2J]`. Zero where `J = 0`, where no kernel reads them.
    pub(crate) triads: u64,
    pub(crate) wt: u64,
    pub(crate) wtb: u64,
    pub(crate) rt: u64,
    pub(crate) wtr: u64,
    pub(crate) rwt: u64,
    pub(crate) pabg: u64,
    pub(crate) ptp: u64,
    pub(crate) pct: u64,
    // [theory, November 16 19:10Z] Whether the triads' legs stand at the site (`Declaration::crossing`): one where they do, zero where they are the
    // strand's.
    pub(crate) crossing: u64,
    // [theory, November 12, P50 step 1] The clock's skins (`FieldWords::skin`, `cskin`): a paced head's skin of each support pair `[p][pair][l]` and
    // of each crowd edge `[p][t][slot][l]`, 32 bits each, formed once a clock by `field_skin_fill`. Zero where the batch keeps none.
    pub(crate) skin: u64,
    pub(crate) cskin: u64,
    // [theory, November 12, P51] The skins' support stride: each region's prefix of `S_r K_r` (`FieldWords::region_soff`) and their sum `E2`.
    pub(crate) region_soff: u64,
    pub(crate) skin_entries: u64,
    // [theory, November 12, P50 step 2] A clock's near phases and skins (`FieldWords::mphase`, `mskin`), the moment modes' map and their count.
    pub(crate) mphase: u64,
    pub(crate) mskin: u64,
    pub(crate) mcmap: u64,
    pub(crate) tm: u64,
    // [definition; agent-inferred, November 14, the ring record §4] The field that reads twice (`FieldWords::mark_at`, `mark_share`): the strengths'
    // offset in the material, and on the second read each silent site's shares of the face the first read gave it `[t][A]` (zero elsewhere and on a
    // first read).
    pub(crate) mark_at: u64,
    pub(crate) mark_share: u64,
    // [measurement; the lead, November 18, the frontier record §6] The known stream (`FieldWords::before`): one where every site of the batch
    // hears only what stands before it (the host's ruler at `3`, `Constitution::ruler_far`), zero under the law.
    pub(crate) before: u64,
    // [the lead, November 18] A passage read by two streams (`FieldWords::site_place`, `region_heard`): each site's place and each region's
    // count of sites that can be heard, zero (null) where the batch holds no strand.
    pub(crate) site_place: u64,
    pub(crate) region_heard: u64,
    // [the lead, November 19 (G-1119-7)] The pumped circles (`FieldWords::pump`): one where the circles are pumped (`Declaration::pump`), the pump
    // chart's and its bias's offsets in the material (`Loci::pump`, `pump_bias`) and its reach, and (set per tick) the chart's read `p` `[t][2C]` and
    // the pump `η` `[t][2C]`. Zero where the circles are not pumped.
    pub(crate) pump: u64,
    pub(crate) wp: u64,
    pub(crate) wpb: u64,
    pub(crate) rp: u64,
    pub(crate) pp: u64,
    pub(crate) peta: u64,
    // [the lead, November 24] Each turned ring's skin denominator and rate of fade (`FieldWords::skin_k`, `skin_b`: the host's
    // `Constitution::skin_denominator_of` and `skin_rate`), and the covector's fades where the rings hold them (`FieldWords::gfade`, zero
    // where they do not).
    pub(crate) skin_k: u64,
    pub(crate) skin_b: u64,
    pub(crate) gfade: u64,
    // [the lead, November 25] Where the classes fade at their own rates, the material's offset of the paced heads' fade rows
    // (`FieldWords::fade_rate_at`, the host's `Loci::fade_rate`); `u64::MAX` where they do not.
    pub(crate) fade_rate_at: u64,
    // [the lead, November 25] Each site's stretch start in a passage read as its stretches (`FieldWords::site_stretch`); zero (null) where the
    // batch holds none.
    pub(crate) site_stretch: u64,
}

pub(crate) fn arg<T>(v: &mut T) -> *mut c_void {
    (v as *mut T).cast()
}

/// One tick's carriers on the card.
/// A field's uploaded run buffers ([`Resident::upload`]), held while its words are read.
pub(crate) struct Upload<'c> {
    pub(crate) _pack: Pooled<'c, u8>,
    pub(crate) _face: Option<Pooled<'c, u64>>,
    pub(crate) met: Pooled<'c, u64>,
}

/// A batch's staged tables ([`Resident::stage`]).
pub(crate) struct Staged<'c> {
    pub(crate) site_pos: Vec<u32>,
    pub(crate) region_off: Vec<u32>,
    pub(crate) classes: Vec<u32>,
    pub(crate) unresolved: Vec<u8>,
    pub(crate) definite: Vec<u8>,
    pub(crate) echo_has: Vec<u8>,
    pub(crate) mix_off: Vec<u32>,
    pub(crate) mix_class: Vec<u32>,
    pub(crate) mix_share: Vec<u32>,
    pub(crate) site_weight: Vec<(u64, u64)>,
    pub(crate) pairs: usize,
    /// [theory, November 12, P51] The skins' support entries `E2 = Σ_r S_r K_r`.
    pub(crate) skin_entries: usize,
    pub(crate) sites: usize,
    pub(crate) _tables: Pooled<'c, u8>,
    pub(crate) status: Pooled<'c, u32>,
    /// Read through `words.x`; held here for its memory.
    pub(crate) _x: Pooled<'c, i64>,
}

/// [realization; agent-inferred, November 14, the ring record §4] **What a batch's reads stand on** ([`Resident::batch_base`]): everything a
/// read does before its opening `x⁰`, none of which the opening's state reaches. The host's `Constitution::pass_with` reads the region's clocks
/// (`paces`) and moments (`moments_of`) from the region and the constitution alone, the opening's comparison from the cavity openings, which open
/// no site on a mark (`cavity_forward` passes none), and the level's news from that comparison (`level_news`); only `open` takes the marks. So a
/// field that reads twice ([`Declaration::mark`]) stages its regions, forms the base clock and its moments, reads the opening's comparison,
/// fetches the news and cuts its level once a batch, and both reads stand on them: the first read's opening is the built one, the second's carries
/// the marks, and from the opening on each read is its own. The opening's comparison is kept here until the first read that returns returns
/// through it. [G180] Where the field reads twice both reads are compared, and the opening's comparison returns the same bits in each (it reads
/// the base clock and the cavity openings, no read's state): the first read takes it twice into the covector and leaves the base clock's
/// covectors it gave (`early`) for the second read's reverse. The clock's stores (the skins, the near phases) are each clock's: a read after
/// the first forms the base clock's again before its first tick (`reads`).
pub(crate) struct BatchBase<'c> {
    pub(crate) st: Staged<'c>,
    /// The base clock (§16): its rates, clocks, variations, skin addresses, plainness and frames, and the site moments on it (§15.1).
    pub(crate) kappa: Pooled<'c, i64>,
    pub(crate) tau: Pooled<'c, i64>,
    pub(crate) sigma: Pooled<'c, i64>,
    pub(crate) saddr: Pooled<'c, i64>,
    pub(crate) plain: Pooled<'c, u8>,
    pub(crate) pframe: Pooled<'c, i64>,
    pub(crate) moment: Pooled<'c, i64>,
    /// The clock's skins and its near phases and skins, one store each for the batch, formed again at each clock.
    pub(crate) _skins: Option<(Pooled<'c, u32>, Pooled<'c, u32>)>,
    pub(crate) _clock_store: Option<(Pooled<'c, u32>, Pooled<'c, u32>)>,
    /// [the lead, November 25] The base clock's second skin addresses, near skins, crowd skins and moments ([`SecondFade`]).
    pub(crate) _second: Option<(Pooled<'c, i64>, Pooled<'c, u32>, Pooled<'c, u32>, Pooled<'c, i64>)>,
    pub(crate) opening: Option<Opening<'c>>,
    /// [G180] The base clock's covectors the opening's comparison gave (`τ`, `σ`), left by the first read for the second's reverse.
    pub(crate) early: Option<(Pooled<'c, i128>, Pooled<'c, i128>)>,
    pub(crate) tb: Option<TowerBatch<'c>>,
    /// The reads taken on this base so far.
    pub(crate) reads: usize,
}

/// [the lead, November 18] **The cavity's kept forward of a strand batch** ([`Resident::strand_cavity`]): the standing moments' kept operands
/// (none on a field with no moment mode), the cavity moments `[t][2M]` the open places read and their two sides.
pub(crate) struct StrandBase<'c> {
    pub(crate) keep: Option<MomentKeep<'c>>,
    pub(crate) cmoment: Pooled<'c, i64>,
    pub(crate) sb: Pooled<'c, i64>,
    pub(crate) sa: Pooled<'c, i64>,
    /// [the lead, November 25] The same at the rings' second fades ([`SecondFade`]), where they hold them.
    pub(crate) second: Option<Box<StrandBase<'c>>>,
}

/// [the lead, November 25] **The rings' second fades on the card** (the host's `Declaration::twin`): the run's second decays, skin
/// denominators and rates of fade (uploaded with the material), the covector's second fades (set where the run returns), and the base clock's
/// second skin addresses, near skins, crowd skins and moments (taken by the batch's base). The second fades' moments are the first's kernels
/// on words whose skins are these ([`Resident::second_words`]): the same clock, phases, strands and encodings, at the second skins.
#[derive(Clone, Copy, Default)]
pub(crate) struct SecondFade {
    pub(crate) decay: u64,
    pub(crate) skin_k: u64,
    pub(crate) skin_b: u64,
    pub(crate) gfade: u64,
    pub(crate) saddr: u64,
    pub(crate) mskin: u64,
    pub(crate) cskin: u64,
    pub(crate) moment: u64,
}

impl BatchBase<'_> {
    /// The words of the base clock, in [`set_clock`]'s order.
    pub(crate) fn clock(&self) -> [u64; 7] {
        [self.kappa.device_ptr(), self.tau.device_ptr(), self.sigma.device_ptr(), self.plain.device_ptr(), self.pframe.device_ptr(), self.moment.device_ptr(), self.saddr.device_ptr()]
    }
}

/// What a profiled call's time is charged to.
#[derive(Clone, Copy)]
pub(crate) enum Kind {
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
/// its class (P58 item 1, at [`Resident::take`]), and otherwise the largest kept ones are freed first, one at a time. The contents of a taken buffer are undefined, zeroed where
/// the call says so; the work of the stream is ordered, so a buffer a queued kernel still reads is never
/// overwritten before it has.
pub(crate) trait Poolable: Copy + Sized + 'static {
    fn list<'a, 'c>(pools: &'a mut Pools<'c>) -> &'a mut Vec<(usize, CardBuffer<'c, Self>)>;
}

#[derive(Default)]
pub(crate) struct Pools<'c> {
    pub(crate) u8s: Vec<(usize, CardBuffer<'c, u8>)>,
    pub(crate) u32s: Vec<(usize, CardBuffer<'c, u32>)>,
    pub(crate) i32s: Vec<(usize, CardBuffer<'c, i32>)>,
    pub(crate) u64s: Vec<(usize, CardBuffer<'c, u64>)>,
    pub(crate) i64s: Vec<(usize, CardBuffer<'c, i64>)>,
    pub(crate) i128s: Vec<(usize, CardBuffer<'c, i128>)>,
    /// The octets of the buffers taken and not yet returned, and of those kept.
    pub(crate) live: u64,
    pub(crate) retained: u64,
    /// [measurement; G143] The live octets by the line of the take that holds them.
    pub(crate) live_by_line: std::collections::BTreeMap<u32, u64>,
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
    pub(crate) fn free_largest(&mut self) -> u64 {
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
pub(crate) fn size_class(len: usize) -> usize {
    let len = len.max(4);
    let top = len.next_power_of_two();
    let step = (top / 8).max(4);
    len.div_ceil(step) * step
}

/// Host arrays packed into one buffer for one transfer, each at a 16-octet boundary (a transfer of its own
/// costs tens of microseconds and drains the stream; a batch's fourteen were a tenth of its host time).
#[derive(Default)]
pub(crate) struct Packed {
    pub(crate) bytes: Vec<u8>,
}

impl Packed {
    /// The octet offset of `values`, appended (plain integers only).
    pub(crate) fn put<T: Copy>(&mut self, values: &[T]) -> u64 {
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
pub(crate) struct Pooled<'c, T: Poolable> {
    pub(crate) buf: Option<(usize, CardBuffer<'c, T>)>,
    pub(crate) pools: std::rc::Rc<std::cell::RefCell<Pools<'c>>>,
    /// [measurement; G143] The line of the take that holds it (the live set by take site, a reading).
    pub(crate) line: u32,
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

/// **The field on the card**: its image, the card it runs on and the octets a batch may take.
/// [realization; the lead, November 22] The largest magnitude two signed digits of eight bits hold as `tc_digits` cuts a word
/// (`d₀ + 2⁸ d₁`, each `d ∈ [−128, 127]`): a weight within it takes two planes.
const TC_TWO: u32 = 127 + 256 * 127;
/// The uploads whose units are kept: a section's fine field and its level's, with room for a reading's own.
const UNIT_TABLES: usize = 4;

pub struct Resident<'c> {
    pub(crate) card: &'c Card,
    pub(crate) module: Module,
    pub(crate) budget: u64,
    pub(crate) times: FieldTimes,
    pub(crate) profile: Option<std::cell::RefCell<FieldProfile>>,
    /// The head a launch is made for, where the launches go a head at a time (a profile's reading by head).
    pub(crate) head: std::cell::Cell<Option<u32>>,
    /// [measurement; theory, November 15 20:38Z] The tick a launch is made for: `k` in the forward, `RETURN_TICK + k` in the return (a profile's
    /// reading by tick).
    pub(crate) tick: std::cell::Cell<Option<u32>>,
    /// [measurement; P61 item 3] The last launch's timed ns, under the profile.
    pub(crate) last_ns: std::cell::Cell<u128>,
    /// [realization; P61 item 4f] The outer passes' slots for their largest words and the next slot ([`Resident::outer_slot`]).
    pub(crate) outer_maxima: std::cell::RefCell<Option<(Pooled<'c, u64>, usize)>>,
    /// [realization; the lead, November 22] **Each family's unit as the card reads it**, keyed by the material's address on the card and the
    /// family's first entry: the places every entry of the family holds under its read part (the common trailing zeros of its words) and the
    /// digit planes of eight bits its words take once read in that unit (two where every `|θ ≫ s|` stands within `TC_TWO`, else four). Read
    /// from the material as each upload writes it ([`Resident::upload`]); a family on its lattice ([`holonics_engine::field::Lattice`]) is read
    /// as its count, the same integers.
    pub(crate) units: std::cell::RefCell<std::collections::VecDeque<(u64, std::collections::HashMap<u64, (u32, u32)>)>>,
    /// [theory, November 12, P50 step 1] The test build's negative control: the clock's fill withheld, its store left at `SKIN_UNFILLED`.
    #[cfg(test)]
    pub(crate) unfilled: std::cell::Cell<bool>,
    /// [measurement; theory, November 12, P54 item 1] The ruler build's histograms of the words' bits (`BITS_NAMES` by clock by bit length).
    #[cfg(feature = "ruler-bits")]
    pub(crate) bits: std::cell::RefCell<Option<CardBuffer<'c, u64>>>,
    pub(crate) pools: std::rc::Rc<std::cell::RefCell<Pools<'c>>>,
    /// A held read's rows by where their mass lies (a reading for the receipts): the regions' answer starts
    /// while it is read, and the cells `[tick · heads + head][rows, question, soft_near, other, current, question_far, far_effective, far_rows]` summed.
    pub(crate) held_questions: std::cell::RefCell<Option<Vec<usize>>>,
    /// [measurement, §16.20] While a covector's shares are read, `[h][near, far]` summed over the batches.
    pub(crate) covector_shares: std::cell::RefCell<Option<Vec<i128>>>,
    /// [measurement, §16.21] While the held rows' currents are read: the regions' answer starts, the rows read region by
    /// region, and the batch's current covectors a tick `[h][t][2n]` where read with a return.
    pub(crate) row_questions: std::cell::RefCell<Option<Vec<usize>>>,
    pub(crate) row_out: std::cell::RefCell<Vec<Vec<RowCurrent>>>,
    pub(crate) row_cov: std::cell::RefCell<Option<Vec<Vec<i64>>>>,
    pub(crate) held_cells: std::cell::RefCell<Vec<i128>>,
    /// [measurement, November 4] While the ticks are read: each region's tick reads, region by region.
    pub(crate) tick_reads: std::cell::RefCell<Option<Vec<Vec<TickRead>>>>,
    /// [measurement; theory, November 11 18:33, part P2] While the carry circles' gates are read: each circle's `|γ|` sum, then its `ℓ ≥ 0` count,
    /// then the reads (`2C + 1` words, [`CarryGates`]), summed over the batches from each tick's forward.
    pub(crate) carry_gates: std::cell::RefCell<Option<Vec<u128>>>,
    /// [measurement, §16.42] While a near field is read: the named sites of the batch's one region, and each one's near field
    /// by offset at every kept tick and head.
    pub(crate) near_sites: std::cell::RefCell<Option<Vec<usize>>>,
    pub(crate) near_out: std::cell::RefCell<Vec<NearOffsets>>,
    /// [measurement, §16.44] While the blanks' clocks are read: the named sites of the batch's one region, and each one's
    /// clocks by tick.
    pub(crate) clock_sites: std::cell::RefCell<Option<Vec<usize>>>,
    pub(crate) clock_out: std::cell::RefCell<Vec<BlankClocks>>,
    /// The host's wall time between marks, by name (`FIELD_PHASES`), no stream synchronized.
    pub(crate) phases: Option<std::cell::RefCell<(Instant, std::collections::BTreeMap<&'static str, (u64, u128)>)>>,
    /// [measurement; theory, November 13, P56 item 4] Each phase's timed card ns (launches, copies, takes, zeroings) when also profiled, and the
    /// profile's running total at the last mark.
    pub(crate) phase_card: std::cell::RefCell<(u128, std::collections::BTreeMap<&'static str, u128>)>,
    /// [realization; theory, November 13, P58 item 3] While the training path reads its faces at their classes
    /// ([`Realization::read_and_return_at_class`]): set, and each region's open sites' `(m_c, T)` gathered on the card.
    pub(crate) narrow: std::cell::Cell<bool>,
    pub(crate) narrow_out: std::cell::RefCell<Vec<Vec<Option<(u128, u128)>>>>,
    /// [measurement; theory, November 13, P57 item 2 (G132)] While the charts are read by stage
    /// ([`Realization::read_tick_charts`]): each region's open sites' chart rows at each tick's opening and after the last tick.
    pub(crate) tick_charts: std::cell::RefCell<Option<Vec<Vec<Vec<i32>>>>>,
    /// [measurement; Brandon, November 15 00:58Z] While the lane powers are read by stage ([`Realization::read_tick_scales`]): each
    /// region's open sites' lane scales at each tick's opening and after the last tick.
    pub(crate) tick_scales: std::cell::RefCell<Option<Vec<Vec<Vec<i128>>>>>,
    /// [measurement; P57 item 1] The last phase marked, which a trace's launches are read under.
    pub(crate) last_mark: std::cell::Cell<&'static str>,
    /// [realization; theory, November 13, P60 items 1d and 2] While the training path reads the opening's codes
    /// ([`Realization::read_and_return_opening`]): set, and each region's opening code at every compared place.
    pub(crate) opening_wanted: std::cell::Cell<bool>,
    pub(crate) opening_out: std::cell::RefCell<Vec<Vec<Option<i64>>>>,
    /// [the lead, November 18] The batch being staged holds passages read by two streams (`Region::strand`, staged as their known stream's
    /// sites and then as many open places): each of its regions' count of sites that can be heard, its known stream's. Empty where the
    /// batch holds none; set by the run for the batch it stages ([`Resident::run`]).
    pub(crate) strand_heard: std::cell::RefCell<Vec<u32>>,
    /// The same counts over every region of the run being made (`Resident::run`'s group of strands), from which each batch takes its own.
    pub(crate) strand_run: std::cell::RefCell<Vec<u32>>,
    /// [the lead, November 23, an act answered in kind] The batch being staged: each strand's open places read and not compared
    /// (`holonics_engine::field::UNCOMPARED`), weight zero in the reverse; empty where none is. Set by the run for the batch it stages.
    pub(crate) strand_skip: std::cell::RefCell<Vec<Vec<bool>>>,
    /// The same over every region of the run being made, from which each batch takes its own.
    pub(crate) strand_skip_run: std::cell::RefCell<Vec<Vec<bool>>>,
    /// [the lead, November 25] The batch being staged: each strand's stretch starts (`Region::stretches`), empty where none is joined; and the
    /// same over every region of the run being made.
    pub(crate) strand_stretch: std::cell::RefCell<Vec<Vec<u32>>>,
    pub(crate) strand_stretch_run: std::cell::RefCell<Vec<Vec<u32>>>,
    /// [the record of the two streams §15] Whether the group a run reads takes the row of the second site before (`Region::second`): the
    /// second bit of the known stream's word (`FieldWords::before`), set by [`Resident::run`] for the run of that group.
    pub(crate) second_run: std::cell::Cell<bool>,
    /// The cavity's kept forward of the strand batch being read (the standing moments' operands, the cavity moments and their two sides),
    /// which the batch's reverse returns the open places' moments through; taken when the batch ends.
    pub(crate) strand_cavity: std::cell::RefCell<Option<StrandBase<'c>>>,
    /// [the lead, November 25] The rings' second fades of the run being made ([`SecondFade`]); none where the field holds none.
    pub(crate) second_fade: std::cell::Cell<Option<SecondFade>>,
}

impl<'c> Resident<'c> {
    /// Load the field's image; a batch's stores take the card's free memory at its open less the
    /// margin, kept under the 12 GB the runs keep the board to.
    pub fn open(card: &'c Card) -> std::result::Result<Self, CardError> {
        card.current()?;
        let module = Module::load_ptx(IMAGE)?;
        let memory = card.census().memory;
        let (free, total) = (memory.free_bytes as u64, memory.total_bytes as u64);
        let used = total.saturating_sub(free);
        let budget = free.min(BOARD_CEILING.saturating_sub(used)).saturating_sub(MARGIN);
        Ok(Self { card, module, budget, strand_heard: Default::default(), strand_run: Default::default(), strand_skip: Default::default(), strand_skip_run: Default::default(), strand_stretch: Default::default(), strand_stretch_run: Default::default(), second_run: Default::default(), strand_cavity: Default::default(), second_fade: Default::default(), times: FieldTimes::default(), profile: None, head: Default::default(), tick: Default::default(), last_ns: Default::default(), outer_maxima: Default::default(), units: Default::default(), #[cfg(test)] unfilled: Default::default(), #[cfg(feature = "ruler-bits")] bits: Default::default(), pools: Default::default(), held_questions: Default::default(), covector_shares: Default::default(), row_questions: Default::default(), row_out: Default::default(), row_cov: Default::default(), held_cells: Default::default(), tick_reads: Default::default(), carry_gates: Default::default(), near_sites: Default::default(), near_out: Default::default(), clock_sites: Default::default(), clock_out: Default::default(), phases: None, phase_card: Default::default(), narrow: Default::default(), narrow_out: Default::default(), last_mark: std::cell::Cell::new("open"), tick_charts: Default::default(), tick_scales: Default::default(), opening_wanted: Default::default(), opening_out: Default::default() })
    }

    /// The octets a batch's weight and contact stores may take.
    pub fn budget(&self) -> u64 {
        self.budget
    }

    /// A buffer of at least `len` elements, contents undefined (`Pooled`).
    #[track_caller]
    pub(crate) fn take<T: Poolable>(&self, len: usize) -> std::result::Result<Pooled<'c, T>, CardError> {
        self.take_with(len, true, std::panic::Location::caller().line())
    }

    /// [`take`](Self::take), `wide` where a kept buffer longer than twice the class may serve it.
    pub(crate) fn take_with<T: Poolable>(&self, len: usize, wide: bool, line: u32) -> std::result::Result<Pooled<'c, T>, CardError> {
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
    pub(crate) fn take_zeroed<T: Poolable>(&self, len: usize) -> std::result::Result<Pooled<'c, T>, CardError> {
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
    pub(crate) fn take_up<T: Poolable>(&self, values: &[T]) -> std::result::Result<Pooled<'c, T>, CardError> {
        let buffer = self.take::<T>(values.len())?;
        self.card.write(&*buffer, 0, values)?;
        Ok(buffer)
    }

    pub(crate) fn launch(&self, entry: &'static str, grid: u32, block: u32, params: &mut [*mut c_void]) -> Result<()> {
        self.launch_shared(entry, grid, block, 0, params)
    }

    /// A launch with `shared` octets of the block's dynamic shared memory.
    pub(crate) fn launch_shared(&self, entry: &'static str, grid: u32, block: u32, shared: u32, params: &mut [*mut c_void]) -> Result<()> {
        self.launch_grid(entry, Dim3::x(grid.max(1)), block, shared, params)
    }

    /// A launch over a grid of `grid` blocks of `block` threads and `shared` octets of dynamic shared memory.
    pub(crate) fn launch_grid(&self, entry: &'static str, grid: Dim3, block: u32, shared: u32, params: &mut [*mut c_void]) -> Result<()> {
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
            if let Some(k) = self.tick.get() {
                let slot = p.by_tick.entry((entry, k)).or_insert((0, 0));
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
    pub(crate) fn cells(cells: u64) -> u32 {
        cells.div_ceil(THREADS as u64).clamp(1, 65_535) as u32
    }

    /// A grid striding `rows` with one warp a row.
    pub(crate) fn warps(rows: u64) -> u32 {
        rows.div_ceil((THREADS / 32) as u64).clamp(1, 1 << 20) as u32
    }

    /// A grid of blocks of `per_block` warps, one warp a row.
    /// [realization; November 15] A tile-form map's grid (`map_tile` in `kernels/field.cu`): a block a tile of 64 outputs by 64 sites.
    pub(crate) fn map_grid(outs: usize, sites: usize) -> u32 {
        (outs as u64).div_ceil(64).saturating_mul((sites as u64).div_ceil(64)).clamp(1, 65_535) as u32
    }

    pub(crate) fn rows_grid(rows: u64, per_block: u64) -> u32 {
        rows.div_ceil(per_block).clamp(1, 1 << 20) as u32
    }


    /// A field's material, rings, skins and exponential uploaded once a run, and the words that read them; a tower's packets'
    /// field reads the fine field's resident exponential (`shared_face`). Returns the words, the buffers they point into and
    /// the octets of the resident face this upload holds.
    pub(crate) fn upload(&self, field: &Constitution, shared_face: Option<u64>) -> Result<(Words, Upload<'c>, u64)> {
        let d = field.declaration;
        // [the lead, November 17] The closed face has no card realization yet.
        if d.closed > 0 {
            return Err(TowerError::Refused("a field with closed characters has no card realization yet (hnn-field-v14c is the host forward's)"));
        }
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
        // [the lead, November 24] Each turned ring's skin denominator and rate of fade, one word where no slot is turned.
        let slots = field.rings().len();
        let skin_k: Vec<i128> = if slots == 0 { vec![1] } else { field.skin_denominators() };
        let skin_b: Vec<i128> = if slots == 0 { vec![0] } else { (0..slots).map(|slot| field.skin_rate(slot)).collect() };
        let (skin_k_at, skin_b_at) = (pack.put(&skin_k), pack.put(&skin_b));
        // [the lead, November 25] The rings' second decays, skin denominators and rates of fade, where they hold them.
        let second_at = if d.twin {
            let decay2: Vec<i64> = field.twin_decays().iter().flatten().copied().collect();
            let skin_b2: Vec<i128> = (0..slots).map(|slot| field.skin_rate_with(true, slot)).collect();
            Some((pack.put(&decay2), pack.put(field.twin_skin_denominators()), pack.put(&skin_b2)))
        } else {
            None
        };
        let decay_t_at = pack.put(&decay_t);
        // The temperatures' fine roots, past the resident face's sixteen (§16.12).
        let fine: Vec<u64> = field.fine_exponential().roots()[roots.len()..].iter().map(|&r| u64::try_from(r).map_err(|_| TowerError::Refused("the exponential's roots lie below 2^63"))).collect::<Result<_>>()?;
        let fine_at = pack.put(&fine);
        let run_pack = self.timed(Kind::Copy, || self.take_up(&pack.bytes)).map_err(device)?;
        let run_base = run_pack.device_ptr();
        self.second_fade.set(second_at.map(|(decay, skin_k, skin_b)| SecondFade { decay: run_base + decay, skin_k: run_base + skin_k, skin_b: run_base + skin_b, ..SecondFade::default() }));
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
        // [the formal thread, November 21] The lane leak is built on the host, its card realization next: a field with it is refused here, so no
        // card pass reads it as the built tick.
        if d.lane_leak {
            return Err(TowerError::Refused("the lane leak has no card realization yet (the host's is the reference)"));
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
            // [the lead, November 19] The pump's chart (`2C` rows of `D`, zero long and so zero where the circles are not pumped).
            pump: u64::from(d.pump),
            wp: l.pump as u64,
            wpb: l.pump_bias as u64,
            rp: reach(l.pump, 2 * d.carry * usize::from(d.pump) * dw),
            // [theory, November 12; the triad record §4] The triads' chart (`6J` rows of `D`) and return (`D` rows of `2J`), their reaches over the
            // families as the host's `Reaches` reads them (zero long, and so zero, where `J = 0`).
            triads: d.triads as u64,
            wt: l.triad as u64,
            wtb: l.triad_bias as u64,
            rt: reach(l.triad, 6 * d.triads * dw),
            wtr: l.w_triad as u64,
            rwt: reach(l.w_triad, dw * 2 * d.triads),
            crossing: u64::from(d.crossing),
            rb: reach(l.b, f * dw),
            rw: reach(l.w, dw * f),
            rread: reach(l.read, dw * dw),
            phasor: run_base + phasor_at,
            ring_off: run_base + ring_off_at,
            ring_n: run_base + ring_n_at,
            skin_k: run_base + skin_k_at,
            skin_b: run_base + skin_b_at,
            decay: run_base + decay_at,
            decay_t: run_base + decay_t_at,
            dreach: d.reach as u64,
            roots: run_base + roots_at,
            met: met.device_ptr(),
            temper_at: l.temper as u64,
            friction_at: if d.friction { l.friction as u64 } else { u64::MAX },
            gate_at: if d.friction_gate { l.friction_gate as u64 } else { u64::MAX },
            fade_rate_at: if d.fade_rate { l.fade_rate as u64 } else { u64::MAX },
            rgate: if d.friction_gate { reach(l.friction_gate, d.heads * dw) } else { 0 },
            fgate: 0,
            dfgate: 0,
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
            // (one more than two bits where every site hears only what stands before it: the strand's odd contacts also facing the past,
            // and the row of the site after reading the second site before, the run's group's word, `Resident::second_run`)
            before: match field.ruler_far {
                3 => 1 + 2 * u64::from(self.second_run.get()),
                9 => 2 + 2 * u64::from(self.second_run.get()),
                _ => 0,
            },
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
        // [realization; the lead, November 22] Each family's unit read from the material as it is uploaded ([`Resident::units`]).
        {
            let mut table = std::collections::HashMap::new();
            for &(start, len, _) in &l.families {
                let block = &field.theta[start..start + len];
                let held = block.iter().fold(0u32, |o, &v| o | v.unsigned_abs());
                let shift = if held == 0 { 0 } else { held.trailing_zeros() };
                let most = block.iter().map(|&v| (v >> shift).unsigned_abs()).max().unwrap_or(0);
                table.insert(start as u64, (shift, if most <= TC_TWO { 2 } else { 4 }));
            }
            // The materials of the last few uploads (a section uploads the fine field and its level's), the oldest released.
            let mut units = self.units.borrow_mut();
            units.retain(|(at, _)| *at != words.theta);
            units.push_back((words.theta, table));
            while units.len() > UNIT_TABLES {
                units.pop_front();
            }
        }
        Ok((words, Upload { _pack: run_pack, _face: face, met }, face_octets))
    }

    /// Each region's faces (and their logits when `logits`) and, when `returning`, the covector
    /// over the regions; with `keep`, the still heads' last-tick weight rows of those sites of the one
    /// region read ([`Realization::read_landmarks`]).
    #[allow(clippy::type_complexity)]
    /// A run of regions through the card: each region's faces and readings and, where it returns, the section's covector (both reads' mean
    /// where the field reads twice, [`Constitution::both_reads_mean`]).
    ///
    /// [definition; the lead, November 18, the frontier record §6; `agent-inferred`] **A section holding known streams** ([`Region::before`]): its
    /// regions of the law run as they did, and its known streams run as a second group under the known stream's forward (`FieldWords::before`: one
    /// read, the level unheard), which is a batch's word, so the groups are a schedule and every sum meets at the covector's grain. Where the
    /// field reads twice a known stream's one read stands for both (the host's `Constitution::returned`): its covector enters the sum twice
    /// before the mean. The faces and the training path's words stand in the regions' own order. A ruler's forward and the readings take
    /// regions of one kind.
    #[allow(clippy::type_complexity)]
    pub(crate) fn run(&mut self, field: &Constitution, regions: &[Region], returning: bool, logits: bool, keep: Option<&[usize]>) -> Result<(Vec<Vec<Option<TowerFace>>>, Vec<Vec<Option<Vec<i64>>>>, Vec<i128>, Rows, Vec<Vec<u64>>)> {
        // [the lead, November 25] A passage read as its consecutive stretches is a strand's alone (the host refuses it elsewhere).
        if regions.iter().any(|r| r.stretches.is_some() && !r.strand) {
            return Err(TowerError::Refused("stretches on a region not read by two streams"));
        }
        if !regions.iter().any(|r| r.before || r.strand) {
            let (faces, read_logits, g, rows, echoes) = self.run_one(field, regions, returning, logits, keep)?;
            return Ok((faces, read_logits, field.both_reads_mean(g), rows, echoes));
        }
        if field.ruler_far != 0 || logits || keep.is_some() {
            return Err(TowerError::Refused("a section holding known streams is read and returned under the law; a ruler's forward and the readings take regions of one kind"));
        }
        let n = regions.len();
        // [the record of the two streams §9] The one-sided groups are cut again by the word `past` (`Region::past`): its regions run under the
        // forward whose odd strand contacts face the past (`FieldWords::before` at two, the host's ruler at `9`).
        let law: Vec<usize> = (0..n).filter(|&r| !regions[r].before && !regions[r].strand).collect();
        // [definition; the lead, November 18, the frontier record §6] **A passage read by two streams on the card** (`Region::strand`, the host's
        // `Constitution::strand_pass`): staged as its known stream's sites and then as many open places, each carrying the class it is compared
        // with, under the known stream's forward (`FieldWords::before`, `site_place`, `region_heard`). Its faces are the open places', none at
        // the first place.
        if (0..n).any(|r| regions[r].strand && (regions[r].unresolved.iter().any(|&u| u) || regions[r].faces.iter().any(Option::is_some) || regions[r].locked.iter().any(|&l| l) || regions[r].echo.iter().any(Option::is_some) || regions[r].port.is_some())) {
            return Err(TowerError::Refused("a passage read by two streams whose sites are not all known, or that has a port"));
        }
        // [the record of the two streams §9 and §15] The one-sided regions are cut by their words into groups, each run under the known
        // stream's forward with its own word (`FieldWords::before`: the odd contacts facing the past, the host's ruler at `9`; the row of
        // the site after reading the second site before, `Resident::second_run`): known streams, then passages read by two streams.
        struct Group {
            at: Vec<usize>,
            strand: bool,
            past: bool,
            second: bool,
            staged: Vec<(Vec<usize>, Vec<bool>)>,
        }
        let mut groups: Vec<Group> = Vec::new();
        for strand in [false, true] {
            for past in [false, true] {
                for second in [false, true] {
                    let at: Vec<usize> = (0..n).filter(|&r| (if strand { regions[r].strand } else { regions[r].before && !regions[r].strand }) && regions[r].past == past && regions[r].second == second).collect();
                    if at.is_empty() {
                        continue;
                    }
                    // [the lead, November 23] A place read and not compared stages a class of the alphabet and takes weight zero (`strand_skip`).
                    let staged = if strand { at.iter().map(|&r| (regions[r].classes.iter().chain(regions[r].targets.unwrap_or(regions[r].classes)).map(|&c| if c == UNCOMPARED { 0 } else { c }).collect(), (0..2 * regions[r].classes.len()).map(|t| t >= regions[r].classes.len()).collect())).collect() } else { Vec::new() };
                    groups.push(Group { at, strand, past, second, staged });
                }
            }
        }
        let law_regions: Vec<Region> = law.iter().map(|&r| regions[r]).collect();
        let (narrow_from, opening_from) = (self.narrow_out.borrow().len(), self.opening_out.borrow().len());
        let mut faces: Vec<Vec<Option<TowerFace>>> = vec![Vec::new(); n];
        let mut rows: Rows = vec![Vec::new(); n];
        let mut echoes: Vec<Vec<u64>> = vec![Vec::new(); n];
        let mut g = if returning { vec![0i128; field.material_len()] } else { Vec::new() };
        let times: i128 = if field.declaration.mark { 2 } else { 1 };
        let mut order: Vec<usize> = Vec::with_capacity(n);
        for k in 0..=groups.len() {
            // (the law's regions first, then each one-sided group)
            let group = k.checked_sub(1).map(|k| &groups[k]);
            let at: &[usize] = group.map_or(&law, |gr| &gr.at);
            if at.is_empty() {
                continue;
            }
            order.extend_from_slice(at);
            let views: Vec<Region> = match group {
                None => law_regions.clone(),
                Some(gr) if gr.strand => gr.staged.iter().map(|(c, u)| Region { classes: c, unresolved: u, faces: &[], locked: &[], echo: &[], domain: None, port: None, before: false, strand: false, past: false, second: false, targets: None, stretches: None }).collect(),
                Some(gr) => gr.at.iter().map(|&r| Region { before: false, past: false, second: false, ..regions[r] }).collect(),
            };
            let heard: Vec<u32> = group.filter(|gr| gr.strand).map_or(Vec::new(), |gr| gr.at.iter().map(|&r| regions[r].classes.len() as u32).collect());
            let ruled = group.map(|gr| {
                let mut f = field.clone();
                f.ruler_far = if gr.past { 9 } else { 3 };
                f
            });
            let (f, weight) = (ruled.as_ref().unwrap_or(field), if group.is_some() { times } else { 1 });
            let two = !heard.is_empty();
            let (narrow_group, opening_group) = (self.narrow_out.borrow().len(), self.opening_out.borrow().len());
            if two {
                *self.strand_run.borrow_mut() = heard.clone();
                let skips: Vec<Vec<bool>> = group.map_or(Vec::new(), |gr| gr.at.iter().map(|&r| regions[r].targets.map_or(Vec::new(), |t| t.iter().map(|&c| c == UNCOMPARED).collect())).collect());
                if skips.iter().any(|s| s.iter().any(|&b| b)) {
                    *self.strand_skip_run.borrow_mut() = skips;
                }
                let stretches: Vec<Vec<u32>> = group.map_or(Vec::new(), |gr| gr.at.iter().map(|&r| regions[r].stretches.map_or(Vec::new(), |s| s.iter().map(|&p| p as u32).collect())).collect());
                if stretches.iter().any(|s| !s.is_empty()) {
                    *self.strand_stretch_run.borrow_mut() = stretches;
                }
            }
            self.second_run.set(group.is_some_and(|gr| gr.second));
            let ran = self.run_one(f, &views, returning, false, None);
            self.strand_run.borrow_mut().clear();
            self.strand_skip_run.borrow_mut().clear();
            self.strand_stretch_run.borrow_mut().clear();
            self.second_run.set(false);
            let (mut gf, _, gg, gr, ge) = ran?;
            if two {
                // An open place stands `heard` sites past the known site of its place: a region's faces and the training path's words are
                // its open places', one a place and none at the first; the opening's codes are the known stream's places'.
                for (k, face) in gf.iter_mut().enumerate() {
                    let h = heard[k] as usize;
                    *face = (0..h).map(|t| if t == 0 { None } else { face[h + t].take() }).collect();
                }
                let mut narrow = self.narrow_out.borrow_mut();
                if narrow.len() == narrow_group + views.len() {
                    // [the lead, November 23] None at a place read and not compared, as the host's `faces_at_class` reads it.
                    let targets: Vec<Option<&[usize]>> = group.map_or(Vec::new(), |gr| gr.at.iter().map(|&r| regions[r].targets).collect());
                    for (k, row) in narrow[narrow_group..].iter_mut().enumerate() {
                        let h = heard[k] as usize;
                        let compared = |t: usize| targets.get(k).copied().flatten().is_none_or(|tg| tg[t] != UNCOMPARED);
                        *row = (0..h).map(|t| if t == 0 || !compared(t) { None } else { row[h + t] }).collect();
                    }
                }
                let mut opening = self.opening_out.borrow_mut();
                if opening.len() == opening_group + views.len() {
                    for (k, row) in opening[opening_group..].iter_mut().enumerate() {
                        row.truncate(heard[k] as usize);
                    }
                }
            }
            for (k, face) in gf.into_iter().enumerate() {
                faces[at[k]] = face;
            }
            if gr.len() == views.len() {
                for (k, row) in gr.into_iter().enumerate() {
                    rows[at[k]] = row;
                }
            }
            if ge.len() == views.len() {
                for (k, echo) in ge.into_iter().enumerate() {
                    echoes[at[k]] = echo;
                }
            }
            for (x, &y) in g.iter_mut().zip(&gg) {
                *x += weight * y;
            }
        }
        // The training path's words by region (`narrow_out`, `opening_out`) were gathered group by group: set in the regions' order.
        fn placed<T: Default>(out: &std::cell::RefCell<Vec<T>>, from: usize, order: &[usize]) {
            let mut out = out.borrow_mut();
            if out.len() != from + order.len() {
                return;
            }
            let gathered: Vec<T> = out.drain(from..).collect();
            let mut set: Vec<T> = (0..order.len()).map(|_| T::default()).collect();
            for (k, item) in gathered.into_iter().enumerate() {
                set[order[k]] = item;
            }
            out.extend(set);
        }
        placed(&self.narrow_out, narrow_from, &order);
        placed(&self.opening_out, opening_from, &order);
        Ok((faces, Vec::new(), field.both_reads_mean(g), rows, echoes))
    }

    /// One group's run ([`Resident::run`]): regions of one kind, the covector as the reads returned it (the mean is the caller's).
    #[allow(clippy::type_complexity)]
    fn run_one(&mut self, field: &Constitution, regions: &[Region], returning: bool, logits: bool, keep: Option<&[usize]>) -> Result<(Vec<Vec<Option<TowerFace>>>, Vec<Vec<Option<Vec<i64>>>>, Vec<i128>, Rows, Vec<Vec<u64>>)> {
        let d = field.declaration;
        // [the strand's two streams] The run's passages read by two streams, each staged as its known stream's sites and then as many open
        // places (`Resident::strand_run`): a place is a known site's, so the reach is asked of the passage.
        let strands: Vec<u32> = {
            let s = self.strand_run.borrow();
            if s.len() == regions.len() { s.clone() } else { Vec::new() }
        };
        for (k, region) in regions.iter().enumerate() {
            if region.classes.len() != region.unresolved.len() || region.classes.len() < 2 {
                return Err(TowerError::Refused("a region needs one class and one resolution a site, and two sites to meet"));
            }
            if strands.get(k).map_or(region.classes.len(), |&n| n as usize) > d.reach {
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
        // [measurement; the lead, November 18, the frontier record §6] **A ruler's forward on the card** (the host's `Constitution::ruler_far`). At `3`
        // (the known stream: every site hears only what stands before it, `FieldWords::before`) and at `4` the level is not heard and the field reads
        // once, as the host's `Constitution::pass` does; the level's material takes no covector, so the run is the unlevelled field's and its covector
        // stands over the level's material as zeros. The far fields at `1` and `2` are the host's alone.
        if !matches!(field.ruler_far, 0 | 3 | 4 | 9) {
            return Err(TowerError::Refused("a ruler's forward other than the known stream's (3, 9) and the unlevelled one (4) is a host reading, with no card realization"));
        }
        // [the record of the two streams §11] A run of passages read by two streams on a tower that carries its one-sided block hears the
        // level (the host's `Constitution::scale_forward_before`): the level stays, its words under the known stream's.
        let strand_level = !self.strand_run.borrow().is_empty() && field.scale.as_deref().is_some_and(|s| s.before_offsets(d.width).is_some());
        if field.ruler_far >= 3 && field.scale.is_some() && !strand_level {
            let mut unlevelled = field.clone();
            unlevelled.scale = None;
            let (faces, read_logits, mut g, rows, echoes) = self.run_one(&unlevelled, regions, returning, logits, keep)?;
            if returning {
                g.resize(field.material_len(), 0);
            }
            return Ok((faces, read_logits, g, rows, echoes));
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
            Some(s) => Some(self.tower_run(field, s, words.face, returning, if strand_level { words.before } else { 0 })?),
            None => None,
        };
        let met = &upload.met;
        let heads = d.heads;
        let g = if returning { Some(self.timed(Kind::Alloc, || self.take_zeroed::<i128>(l.len)).map_err(device)?) } else { None };
        words.gcov = g.as_ref().map_or(0, |g| g.device_ptr());
        // [the lead, November 24] Where the rings hold their fades, the kernels add each ring's fade covector into the covector's own entries.
        words.gfade = if d.fade { g.as_ref().map_or(0, |g| g.device_ptr() + 16 * l.fade as u64) } else { 0 };
        // [the lead, November 25] And each ring's second fade's, where they hold them.
        if let Some(mut s) = self.second_fade.get() {
            s.gfade = g.as_ref().map_or(0, |g| g.device_ptr() + 16 * l.twin_fade as u64);
            self.second_fade.set(Some(s));
        }
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
            *self.strand_heard.borrow_mut() = if strands.is_empty() { Vec::new() } else { strands[batch.clone()].to_vec() };
            *self.strand_skip.borrow_mut() = {
                let all = self.strand_skip_run.borrow();
                if all.len() == regions.len() { all[batch.clone()].to_vec() } else { Vec::new() }
            };
            *self.strand_stretch.borrow_mut() = {
                let all = self.strand_stretch_run.borrow();
                if all.len() == regions.len() { all[batch.clone()].to_vec() } else { Vec::new() }
            };
            self.mark("run_setup");
            // [definition; agent-inferred, November 14, the ring record §4] **The field that reads twice** (the host's `Constitution::pass`): the batch's
            // first read is the built read with no readings, and leaves each silent site's shares of its face on the card (`field_mark_shares`);
            // the second read opens each silent site on its mark and is the batch's read, its faces and readings the field's. [G180] Where the run
            // returns, both reads return into the one covector (the host's `Constitution::returned` with `Forward::first`), halved once below. A region's
            // marks are its own first read's, so the two reads run batch by batch. [realization; agent-inferred, November 14] Both stand on one base
            // (`batch_base`): what comes before the opening is formed once a batch.
            let mut base = self.batch_base(field, &regions[batch.clone()], &mut words, tower.as_mut(), returning)?;
            // [measurement] A ruler's forward at `3` or `4` is one read (the host's `Constitution::pass`).
            let (f, z, r, e) = if d.mark && field.ruler_far < 3 {
                let mut shares = None;
                self.batch(field, &regions[batch.clone()], batch.start, &mut words, &mut base, g.as_deref(), false, None, tower.as_mut(), Some(&mut shares))?;
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
            self.strand_heard.borrow_mut().clear();
            self.strand_skip.borrow_mut().clear();
            self.strand_stretch.borrow_mut().clear();
            self.strand_cavity.borrow_mut().take();
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
        // [definition; agent-inferred, November 14, G180] Where the field reads twice, the run's covector is both reads' over every batch, released
        // by one bit once, the host's own law (`Constitution::both_reads_mean`), so it is the two reads' mean on any partition; unchanged for a field that
        // reads once. The release is the caller's (`Resident::run`), once over every group of the section.
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

    /// A batch's site and region tables uploaded in one transfer, its status word and its faces' buffer, and the words
    /// that read them (the host's tables kept beside them for the reverse and the readings).
    pub(crate) fn stage(&self, regions: &[Region], a: usize, dw: usize, declaration: &Declaration, words: &mut Words) -> Result<Staged<'c>> {
        // The batch's sites, region by region, and the carried mixtures as one list a site.
        // [realization; November 15, Brandon 15:19 "40 minutes a lap is a lot"] Each region's lists are built on its own core and then
        // joined in region order, so every list is the regions' lists one after another, the same words as the one-thread walk; only the
        // offsets (`region_off`, `region_eoff`, `region_soff`, `dstart`, `ostart`, `mix_off`) are prefixes over the regions before.
        let any_echo = regions.iter().any(|r| r.echo.iter().any(Option::is_some));
        // [E] The cut rooms' windows, each site's row computed or not (every site of an uncut region); kept whole where the field has carry
        // circles (the host's `Declaration::room_window`, the one owner of the cut's admission).
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
        // [the known stream] A region's first site has nothing before it: it meets no source and its current is zero (the host's tick under
        // `Sided::Before`), which is a row not computed.
        let before = words.before != 0;
        // [the strand's two streams] The batch's passages read by two streams (`Resident::strand_heard`): a region staged as `heard` known
        // sites and then as many open places, each at the place of the known site of its index less `heard`. An open place at the first
        // place has nothing before it, as the known stream's first site: its row is not computed, and it is not compared (weight zero).
        let heard: Vec<u32> = {
            let h = self.strand_heard.borrow();
            if h.len() == regions.len() { h.clone() } else { Vec::new() }
        };
        let first_place = |r: usize, t: usize| t == 0 || heard.get(r).is_some_and(|&n| t == n as usize);
        let computed: Vec<u8> = if before || windows.iter().any(Option::is_some) { regions.iter().zip(&windows).enumerate().flat_map(|(k, (r, w))| (0..r.classes.len()).map(move |t| (k, t, w))).map(|(k, t, w)| u8::from(w.as_ref().is_none_or(|w| w[t]) && !(before && first_place(k, t)))).collect() } else { Vec::new() };
        // One region's lists: its sites' rows, its definite sites and its open ones by place (§15.9: an open receiver hears every definite
        // site, and a definite source is heard by every open one), its echoes (§15.3) and its carried mixtures, `mix_off` counted from the
        // region's own first mixture.
        #[derive(Default)]
        struct RegionLists {
            classes: Vec<u32>,
            unresolved: Vec<u8>,
            definite: Vec<u8>,
            dlist: Vec<u32>,
            olist: Vec<u32>,
            echo_has: Vec<u8>,
            echo_b: Vec<u64>,
            echo_logits: Vec<i64>,
            mix_class: Vec<u32>,
            mix_share: Vec<u32>,
            mix_off: Vec<u32>,
        }
        let parts: Vec<RegionLists> = regions
            .par_iter()
            .zip(windows.par_iter())
            .map(|(region, window)| {
                let s = region.classes.len();
                let mut l = RegionLists { classes: Vec::with_capacity(s), unresolved: Vec::with_capacity(s), definite: Vec::with_capacity(s), echo_has: Vec::with_capacity(s), echo_b: Vec::with_capacity(s), mix_off: Vec::with_capacity(s), ..Default::default() };
                for t in 0..s {
                    l.classes.push(region.classes[t] as u32);
                    l.unresolved.push(u8::from(region.unresolved[t]));
                    let carried = region.faces.get(t).and_then(Option::as_ref).is_some();
                    let is_definite = (!region.unresolved[t] && !carried) || region.locked.get(t).copied().unwrap_or(false);
                    l.definite.push(u8::from(is_definite));
                    if is_definite {
                        l.dlist.push(t as u32);
                    } else if window.as_ref().is_none_or(|w| w[t]) {
                        // [E] A definite source is heard by every open receiver its region computes (the host's `Constitution::tick`
                        // skips the rest), so the receivers its return walks are those alone.
                        l.olist.push(t as u32);
                    }
                    match region.echo.get(t).and_then(Option::as_ref) {
                        Some(e) => {
                            l.echo_has.push(1u8);
                            l.echo_b.push(e.b);
                            l.echo_logits.extend_from_slice(&e.logits);
                        }
                        None => {
                            l.echo_has.push(0u8);
                            l.echo_b.push(0u64);
                            // (the logits are read only where a site carries an echo, so a batch with none keeps none)
                            if any_echo {
                                l.echo_logits.extend(std::iter::repeat_n(0i64, a));
                            }
                        }
                    }
                    for &(c, w) in region.faces.get(t).and_then(Option::as_ref).into_iter().flatten() {
                        l.mix_class.push(c);
                        l.mix_share.push(w);
                    }
                    l.mix_off.push(l.mix_class.len() as u32);
                }
                l
            })
            .collect();
        let sites = regions.iter().map(|r| r.classes.len()).sum::<usize>();
        let mixtures = parts.iter().map(|l| l.mix_class.len()).sum::<usize>();
        let mut site_region = Vec::with_capacity(sites);
        let mut site_pos = Vec::with_capacity(sites);
        let mut region_off = Vec::with_capacity(regions.len() + 1);
        region_off.push(0u32);
        let mut region_eoff = Vec::with_capacity(regions.len());
        // [theory, November 12, P51] The skins' support stride: each region's prefix of `S_r K_r`, and their sum.
        let (mut region_soff, mut skin_entries) = (Vec::<u64>::with_capacity(regions.len() + 1), 0usize);
        let mut classes = Vec::with_capacity(sites);
        let mut unresolved = Vec::with_capacity(sites);
        // A definite site (§14.1): known (resolved, carrying no mixture) or locked (a foil).
        let mut definite = Vec::with_capacity(sites);
        // Each site's echo (§15.3): its `B`, and its logits a class (zero where none).
        let (mut echo_has, mut echo_b, mut echo_logits) = (Vec::with_capacity(sites), Vec::with_capacity(sites), Vec::new());
        let (mut mix_off, mut mix_class, mut mix_share) = (Vec::with_capacity(sites + 1), Vec::with_capacity(mixtures), Vec::with_capacity(mixtures));
        mix_off.push(0u32);
        let mut pairs = 0usize;
        let (mut dlist, mut dstart, mut olist, mut ostart) = (Vec::<u32>::new(), Vec::<u32>::with_capacity(regions.len() + 1), Vec::<u32>::new(), Vec::<u32>::with_capacity(regions.len() + 1));
        // Each site's region's weight in the joint code (§16.23, `Region::weight`), for the reverse.
        let mut site_weight: Vec<(u64, u64)> = Vec::with_capacity(sites);
        // [the lead, November 23] An open place read and not compared (`Resident::strand_skip`) takes weight zero, as the first place does.
        let skip: Vec<Vec<bool>> = {
            let k = self.strand_skip.borrow();
            if k.len() == regions.len() { k.clone() } else { Vec::new() }
        };
        for (r, (region, l)) in regions.iter().zip(parts).enumerate() {
            let s = region.classes.len();
            let weight = region.weight();
            let skipped = |t: usize| heard.get(r).is_some_and(|&n| t >= n as usize && skip.get(r).and_then(|k| k.get(t - n as usize)).copied().unwrap_or(false));
            site_weight.extend((0..s).map(|t| if heard.get(r).is_some_and(|&n| t == n as usize) || skipped(t) { (0, 1) } else { weight }));
            region_eoff.push(pairs as u64);
            pairs += s * s;
            region_soff.push(skin_entries as u64);
            dstart.push(dlist.len() as u32);
            ostart.push(olist.len() as u32);
            site_region.extend(std::iter::repeat_n(r as u32, s));
            site_pos.extend(0..s as u32);
            classes.extend_from_slice(&l.classes);
            unresolved.extend_from_slice(&l.unresolved);
            definite.extend_from_slice(&l.definite);
            let definites = l.dlist.len();
            dlist.extend_from_slice(&l.dlist);
            olist.extend_from_slice(&l.olist);
            echo_has.extend_from_slice(&l.echo_has);
            echo_b.extend_from_slice(&l.echo_b);
            echo_logits.extend_from_slice(&l.echo_logits);
            let before = mix_class.len() as u32;
            mix_off.extend(l.mix_off.iter().map(|&o| before + o));
            mix_class.extend_from_slice(&l.mix_class);
            mix_share.extend_from_slice(&l.mix_share);
            region_off.push(site_region.len() as u32);
            // [theory, November 12, P51] The region's support stride `K_r = NEAR_SLOTS + D_r` a row (the clock's skins).
            skin_entries += s * (2 * (NEAR - 1) + definites);
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
        // [the strand's two streams] Each site's place and each region's heard sites, where the batch holds a strand.
        let strand_at = (!heard.is_empty()).then(|| {
            let place: Vec<u32> = regions.iter().zip(&heard).flat_map(|(r, &n)| (0..r.classes.len() as u32).map(move |t| if t >= n { t - n } else { t })).collect();
            (pack.put(&place), pack.put(&heard))
        });
        // [the lead, November 25] Each open place's stretch start in a joined passage (`FieldWords::site_stretch`): the last start at or before its place.
        let stretch_at = {
            let starts = self.strand_stretch.borrow();
            (!heard.is_empty() && starts.len() == regions.len() && starts.iter().any(|s| !s.is_empty())).then(|| {
                let at: Vec<u32> = regions
                    .iter()
                    .zip(&heard)
                    .zip(starts.iter())
                    .flat_map(|((r, &n), s)| (0..r.classes.len() as u32).map(move |t| if t >= n { let p = t - n; s.iter().copied().take_while(|&b| b <= p).last().unwrap_or(0) } else { 0 }))
                    .collect();
                pack.put(&at)
            })
        };
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
        (words.site_place, words.region_heard) = strand_at.map_or((0, 0), |(p, h)| (base + p, base + h));
        words.site_stretch = stretch_at.map_or(0, |at| base + at);
        (words.mcmap, words.tm) = (base + mcmap_at, mcmap.len() as u64);
        words.skin_entries = skin_entries as u64;
        words.dlist = base + dlist_at;
        words.dstart = base + dstart_at;
        words.olist = base + olist_at;
        words.ostart = base + ostart_at;
        words.status = status.device_ptr();
        words.x = x.device_ptr();
        Ok(Staged { site_pos, region_off, classes, unresolved, definite, echo_has, mix_off, mix_class, mix_share, site_weight, pairs, skin_entries, sites, _tables: tables, status, _x: x })
    }

    /// [realization; agent-inferred, November 14, the ring record §4] **A batch's base** ([`BatchBase`]): the regions staged, the base clock formed
    /// (its paces, skin addresses and frames), the site moments on it, the opening's comparison's forward wherever a read of the batch reads it
    /// (`returning`: the batch's last read returns; a level reads its news in every read), the level's news fetched and its cut staged. The
    /// opening's forward is kept only where the last read compares it (it returns through it before its ticks), and dropped here otherwise.
    pub(crate) fn batch_base(&self, field: &Constitution, regions: &[Region], words: &mut Words, tower: Option<&mut TowerRun<'c>>, returning: bool) -> Result<BatchBase<'c>> {
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
        // [the lead, November 25] The base clock's second skin addresses, near and crowd skins and moments, where the rings hold second fades.
        let second_stores = match self.second_fade.get() {
            Some(mut s) => {
                let saddr2 = self.timed(Kind::Alloc, || self.take::<i64>((3 * paced * n * sites).max(1))).map_err(device)?;
                let mskin2 = self.timed(Kind::Alloc, || self.take::<u32>((tm * sites * CLOCK_NEAR).max(1))).map_err(device)?;
                let cskin2 = self.timed(Kind::Alloc, || self.take::<u32>((paced * sites * words.slots as usize * n).max(1))).map_err(device)?;
                let moment2 = self.timed(Kind::Alloc, || self.take_zeroed::<i64>((sites * m2).max(1))).map_err(device)?;
                s.saddr = saddr2.device_ptr();
                s.mskin = if words.mskin != 0 { mskin2.device_ptr() } else { 0 };
                s.cskin = if words.cskin != 0 { cskin2.device_ptr() } else { 0 };
                s.moment = moment2.device_ptr();
                self.second_fade.set(Some(s));
                Some((saddr2, mskin2, cskin2, moment2))
            }
            None => None,
        };
        // [measurement; theory, November 13, P56 item 4] The batch's clocks' takes.
        self.mark("batch_takes");
        // [the strand's two streams] A batch of passages read by two streams (the stage's `region_heard`).
        let strand = words.region_heard != 0;
        if paced > 0 {
            self.launch("field_paces", ((paced * regions.len()) as u64).clamp(1, 65_535) as u32, PACE_SCAN_THREADS, &mut [arg(words)])?;
            if strand {
                // The open places' clocks: the clock of the known site before each and one bare stride, at every tick.
                self.launch("field_twin_clocks", Self::cells((paced * sites) as u64), THREADS, &mut [arg(words)])?;
            }
            self.launch("field_skin_addresses", Self::cells((paced * n * sites) as u64), THREADS, &mut [arg(words)])?;
            self.launch("field_pframes", Self::cells((paced * sites * n) as u64), THREADS, &mut [arg(words)])?;
        }
        // [P60 item 2] The opening is compared in a training read where the field has the opening's lift: the standing moments' operands are kept.
        let compared = d.opening && returning;
        // [theory, November 13, the design record §4.9] A level reads the opening's news in every pass, so the opening's forward runs
        // wherever a level stands; its comparison and return only where the pass returns.
        let opened = d.opening && (returning || field.scale.is_some());
        let kept_moments = self.moments(field, words, regions.len(), sites, opened || strand)?;
        // [the lead, November 25] The second fades' moments on the same clock at the second skins ([`SecondFade`]): their skin addresses, then
        // the moments' own kernels on the second words, kept where the opening or a strand reads their cavity.
        let kept_second = match self.second_words(words) {
            Some(mut w2) => {
                if paced > 0 {
                    self.launch("field_skin_addresses", Self::cells((paced * n * sites) as u64), THREADS, &mut [arg(&mut w2)])?;
                }
                Some(self.moments(field, &w2, regions.len(), sites, opened || strand)?)
            }
            None => None,
        };
        // [the strand's two streams] The open places read the known stream's retarded cavity moments (`field_twin_moment`): the opening's
        // forward formed them where the opening is compared; where it is not, the cavity's forward alone forms them, kept for the reverse.
        let opening = if opened {
            Some(self.opening_forward(field, words, regions, &st, kept_moments, kept_second)?)
        } else {
            if strand {
                let (cmoment, sb, sa) = self.cavity_forward(field, words, regions.len(), sites, kept_moments.as_ref())?;
                let second = match (self.second_words(words), kept_second) {
                    (Some(w2), Some(keep2)) => {
                        let (cmoment, sb, sa) = self.cavity_forward(field, &w2, regions.len(), sites, keep2.as_ref())?;
                        Some(Box::new(StrandBase { keep: keep2, cmoment, sb, sa, second: None }))
                    }
                    _ => None,
                };
                *self.strand_cavity.borrow_mut() = Some(StrandBase { keep: kept_moments, cmoment, sb, sa, second });
            }
            None
        };
        if strand {
            let (mut cp, mut cp2) = match (opening.as_ref(), self.strand_cavity.borrow().as_ref()) {
                (Some(op), _) => (op.cmoment.device_ptr(), op.second.as_ref().map(|s| s.cmoment.device_ptr())),
                (None, Some(c)) => (c.cmoment.device_ptr(), c.second.as_ref().map(|s| s.cmoment.device_ptr())),
                (None, None) => return Err(TowerError::Refused("a strand batch with no cavity moments")),
            };
            self.launch("field_twin_moment", Self::cells((sites * m2) as u64), THREADS, &mut [arg(words), arg(&mut cp)])?;
            // The open places' second moments, the known stream's second cavity moments.
            if let (Some(mut w2), Some(cp2)) = (self.second_words(words), cp2.as_mut()) {
                self.launch("field_twin_moment", Self::cells((sites * m2) as u64), THREADS, &mut [arg(&mut w2), arg(cp2)])?;
            }
        }
        // [G145] The level's news at every place, from the opening's face (`field_level_news`, the host's `Constitution::level_news`), read to the
        // host, which cuts each region's epochs (`level_cut`, a kind of work placed on the host; its bits are the host's own function's).
        // [the record of the two streams §11] A strand's level reads each known site's news and its place's expected news (an open place's
        // news is the expected code of the retarded opening's face of its place), and nothing at the open places, whose own rows of the
        // face are not formed (`field_level_news_strand`, the host's `Constitution::strand_news`).
        let strand_level = tower.as_ref().is_some_and(|tr| tr.before.is_some());
        let (news, open_news) = match (opening.as_ref(), field.scale.is_some()) {
            (Some(op), true) if strand_level => {
                let out = self.timed(Kind::Alloc, || self.take::<i64>(sites.max(1))).map_err(device)?;
                let expected = self.timed(Kind::Alloc, || self.take::<i64>(sites.max(1))).map_err(device)?;
                let (mut mp, mut tp, mut np, mut ep) = (op.masses.device_ptr(), op.totals.device_ptr(), out.device_ptr(), expected.device_ptr());
                self.launch("field_level_news_strand", Self::warps(sites as u64), THREADS, &mut [arg(words), arg(&mut mp), arg(&mut tp), arg(&mut np), arg(&mut ep)])?;
                (Some(self.timed(Kind::Copy, || card.fetch_range(&out, 0, sites)).map_err(device)?), Some(self.timed(Kind::Copy, || card.fetch_range(&expected, 0, sites)).map_err(device)?))
            }
            (Some(op), true) => {
                let out = self.timed(Kind::Alloc, || self.take::<i64>(sites.max(1))).map_err(device)?;
                let (mut mp, mut tp, mut np) = (op.masses.device_ptr(), op.totals.device_ptr(), out.device_ptr());
                self.launch("field_level_news", Self::warps(sites as u64), THREADS, &mut [arg(words), arg(&mut mp), arg(&mut tp), arg(&mut np)])?;
                (Some(self.timed(Kind::Copy, || card.fetch_range(&out, 0, sites)).map_err(device)?), None)
            }
            _ => (None, None),
        };
        // The opening's forward ends here where no read compares it (a strand batch keeps the cavity's part of it for its reverse or its ticks).
        let opening = match opening {
            Some(op) if !compared && strand => {
                let Opening { keep, cmoment, sb, sa, second, .. } = op;
                *self.strand_cavity.borrow_mut() = Some(StrandBase { keep, cmoment, sb, sa, second });
                None
            }
            other => other.filter(|_| compared),
        };
        let tb = match tower {
            Some(tr) => Some(self.tower_batch(field, tr, &st, regions.len(), news.as_deref().ok_or(TowerError::Refused("a level without the opening's news"))?, open_news.as_deref())?),
            None => None,
        };
        self.mark("batch_base");
        Ok(BatchBase { st, kappa, tau, sigma, saddr, plain, pframe, moment, _skins: skins, _clock_store: clock_store, _second: second_stores, opening, early: None, tb, reads: 0 })
    }

    /// One read of a batch of regions on its base ([`Resident::batch_base`]): the opening and the forward, each unresolved site's face (and its
    /// logits when `logits`), when `g` is given the reverse added into it, and with `keep` the still heads' last-tick weight rows of those sites
    /// (the batch's one region). With `first` (a field that reads twice, [`Declaration::mark`]) it is the batch's first read: the forward to
    /// the faces with no reading, its return added into `g` where given ([G180] both reads are compared), and each silent site's shares of its
    /// face left on the card in `first`, nothing fetched.
    #[allow(clippy::type_complexity)]
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn batch(&self, field: &Constitution, regions: &[Region], at_region: usize, words: &mut Words, base: &mut BatchBase<'c>, g: Option<&CardBuffer<'c, i128>>, logits: bool, keep: Option<&[usize]>, mut tower: Option<&mut TowerRun<'c>>, first: Option<&mut Option<Pooled<'c, u32>>>) -> Result<(Vec<Vec<Option<TowerFace>>>, Vec<Vec<Option<Vec<i64>>>>, Rows, Vec<Vec<u64>>)> {
        if field.scale.is_some() != tower.is_some() || field.scale.is_some() != base.tb.is_some() {
            return Err(TowerError::Refused("a tower is read with its packets' level"));
        }
        // [the ring record §4] A first read is the built read: no logits, no kept rows, no mark of its own, and none of the readings below (they
        // read the second read, the field's). [definition; agent-inferred, November 14, G180] Where the pass returns, the first read returns too,
        // into the same covector: both reads are compared (the host's `Constitution::returned` with `Forward::first`), and the run halves the sum once.
        let reading = first.is_none();
        if !reading && (logits || keep.is_some() || words.mark_share != 0) {
            return Err(TowerError::Refused("a field's first read with a reading or a mark"));
        }
        let card = self.card;
        let d = field.declaration;
        let (dw, m, n, a, heads) = (d.width, d.complex(), d.modes, d.alphabet, d.heads);
        let m2 = 2 * m;
        let st = &base.st;
        let (sites, pairs) = (st.sites, st.pairs);
        let (site_pos, region_off, classes, unresolved) = (&st.site_pos, &st.region_off, &st.classes, &st.unresolved);
        let (echo_has, mix_off, mix_class, mix_share, site_weight) = (&st.echo_has, &st.mix_off, &st.mix_class, &st.mix_share, &st.site_weight);
        let status = &st.status;
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
        self.launch("field_open", Self::cells(t64 * dw as u64), THREADS, &mut [arg(words)])?;
        // [realization; agent-inferred, November 14] A read after the first forms the base clock's phases and skins again (`clock_fill`, as the base's
        // moments did): the first read's blanks formed their own clocks' in the same stores, and the crowds and the moments read the clock's.
        if base.reads > 0 {
            self.clock_fill(field, words, sites)?;
        }
        base.reads += 1;
        // The moment's chart into the face (§16.22, the host's `Constitution::open`): `x⁰ += release(C s + b, 24)`.
        let (mface, mface_bias, rmface) = moment_face(field);
        self.affine("field_affine_x64", words, mface, mface_bias, rmface, dw, m2, words.moment, m2, 0, dw, words.x, false)?;
        // [the lead, November 25] The second fades' chart into the face (the host's `Constitution::twin_term`): `x⁰ += release(C′ s′, 24)`, no bias.
        if let Some(s2) = self.second_fade.get() {
            let (tface, rtface) = twin_face(field);
            self.affine("field_affine_x64", words, tface, u64::MAX, rtface, dw, m2, s2.moment, m2, 0, dw, words.x, false)?;
        }
        // [realization; theory, November 13, G144] **The opening's return runs at the end of its own forward, before the ticks.** It reads only its
        // forward's buffers, the constitution, the base clock's frames and clocks (the words hold the base clock here and again at the reverse's start,
        // and its kernels read no filled clock store) and the stage's host arrays; it adds into `g` and into the base clock's two covectors, taken here
        // zeroed and handed to the reverse as its own, every one an integer sum, so the order is the realization's. Its forward's buffers end here,
        // so none stands beside the ticks, the face or the reverse: held across them they added a buffer to each class they share, and the card's pool
        // passed its budget by about a tenth of a gigabyte, freeing and allocating again at three take sites every section (G143's profiled logs).
        // [realization; agent-inferred, November 14] The forward is the base's (formed once a batch), and the first read that returns takes it.
        // [G180] Where the field reads twice both reads return, and the opening's comparison gives each the same bits (it reads the base clock and
        // the cavity openings, no read's own state, as the host's `opening_compare_return` reads `pass.paces`): the first read returns it once into
        // its own buffer, takes that twice into `g` (`field_wide_add`), and leaves a copy of the base clock's covectors it gave for the second
        // read (`BatchBase::early`), so the forward still ends before the first read's ticks.
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
                    cw.unresolved = op.compare.device_ptr();
                    let (mut mp, mut pp) = (op.masses.device_ptr(), picked.device_ptr());
                    self.launch("field_face_at_class", Self::cells(sites as u64), THREADS, &mut [arg(&mut cw), arg(&mut mp), arg(&mut pp)])?;
                    let picked = self.timed(Kind::Copy, || card.fetch_range(&picked, 0, sites)).map_err(device)?;
                    let totals = self.timed(Kind::Copy, || card.fetch_range(&op.totals, 0, sites)).map_err(device)?;
                    let mask = self.timed(Kind::Copy, || card.fetch_range(&op.compare, 0, sites)).map_err(device)?;
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
                let tables = (classes.as_slice(), unresolved.as_slice(), site_pos.as_slice(), mix_off.as_slice(), mix_class.as_slice(), mix_share.as_slice());
                if reading {
                    self.opening_back(field, words, &op, g, tables, sites)?;
                } else {
                    let len = field.layout().len;
                    let once = self.timed(Kind::Alloc, || self.take_zeroed::<i128>(len)).map_err(device)?;
                    self.opening_back(field, words, &op, &once, tables, sites)?;
                    let (mut gp, mut op1, mut count, mut times) = (g.device_ptr(), once.device_ptr(), len as u64, 2u32);
                    self.launch("field_wide_add", Self::cells(len as u64), THREADS, &mut [arg(&mut gp), arg(&mut op1), arg(&mut count), arg(&mut times)])?;
                    let words128 = (paced * sites).max(1);
                    let (tau2, sig2) = (self.timed(Kind::Alloc, || self.take::<i128>(words128)).map_err(device)?, self.timed(Kind::Alloc, || self.take::<i128>(words128)).map_err(device)?);
                    let stream = card.stream();
                    stream.copy_device_to_device_async(tau2.device_ptr(), gtau.device_ptr(), 16 * words128).map_err(|e| device(e.into()))?;
                    stream.copy_device_to_device_async(sig2.device_ptr(), gsig.device_ptr(), 16 * words128).map_err(|e| device(e.into()))?;
                    base.early = Some((tau2, sig2));
                }
                // [the strand's two streams] The cavity's part of the opening's forward stays for the open places' return.
                if words.region_heard != 0 {
                    let Opening { keep, cmoment, sb, sa, second, .. } = op;
                    *self.strand_cavity.borrow_mut() = Some(StrandBase { keep, cmoment, sb, sa, second });
                } else {
                    drop(op);
                }
                Some((gtau, gsig))
            }
            // [G180] The second read's base clock covectors from the opening's comparison, as the first read's gave them.
            None => base.early.take(),
        };
        // The level's ticks, the read's own.
        if let Some(tb) = base.tb.as_mut() {
            tb.ticks = self.level_ticks(field, tb, regions.len(), stored, returning, kept)?;
        }
        let tb = base.tb.as_ref();
        self.mark("batch_setup");
        // [§16.44] The blanks run at the bare rate in the first tick, and each later tick at the faces the tick before
        // gave them (the host's `pass`).
        // [the strand's two streams] An open place of a strand runs on the bare clock at every tick: no clock is read again there.
        let blanks = paced > 0 && words.region_heard == 0 && (0..sites).any(|t| unresolved[t] != 0 && st.mix_off[t] == st.mix_off[t + 1]);
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
            self.tick.set(Some(k as u32));
            self.tick_forward(field, words, &ticks, k, kept, stored, keep.is_some(), logits, returning, pr.device_ptr(), sites, pairs, regions.len())?;
            self.tick.set(None);
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
        // [measurement; Brandon, November 15 00:58Z] The lanes' scales by stage, where they are read: each tick's at its opening (below),
        // and after the last tick the face's (the stage the faces read). Every site's scales are fetched and the open sites' kept.
        let mut stage_scales: Option<Vec<Vec<i128>>> = None;
        if reading && self.tick_scales.borrow().is_some() {
            let lanes = field.declaration.lanes;
            let mut stages = Vec::with_capacity(ticks.len() + 1);
            for tick in &ticks {
                stages.push(self.timed(Kind::Copy, || card.fetch_range(&tick.scale, 0, sites * lanes)).map_err(device)?);
            }
            stage_scales = Some(stages);
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
        if let Some(stages) = stage_scales.as_mut() {
            stages.push(self.timed(Kind::Copy, || card.fetch_range(&fscale, 0, sites * field.declaration.lanes)).map_err(device)?);
        }
        // [P57 item 2] The chart after the last tick, the stage the faces read, gathered at the open sites beside each tick's.
        if let (Some(stages), Some(at)) = (stage_rows.as_mut(), open_buf.as_ref()) {
            stages.push(gather(fread.device_ptr(), at)?);
        }
        // The face read through the encoding (§16.26, the host's `Constitution::tied`): the lift `y = R r̂ + b_R`, then
        // `z(a) = rel(⟨E(a), y⟩, 16) + c_a`. [P58 item 2] The lift unzeroed: `affine` writes an open site's every output, and its readers,
        // `field_tied_face` and the reverse's `field_tied_back_e`, read it at open sites alone.
        let lift = self.timed(Kind::Alloc, || self.take::<i64>(sites * dw)).map_err(device)?;
        let lift_bias = field.layout().lift_bias as u64;
        self.affine("field_affine_x32", words, words.read, lift_bias, words.rread, dw, dw, fread.device_ptr(), dw, lift.device_ptr(), dw, 0, true)?;
        // [Brandon, November 15 02:06Z] Where the face reads its sites' loudness (the host's `Constitution::loud_beta` and `Constitution::tied_sharp`): each open
        // site's sharpness from the face's lanes' powers, then the face at it, the plain face kept for the return.
        let loud = if field.declaration.loud {
            let lanes = field.declaration.lanes;
            let beta = self.timed(Kind::Alloc, || self.take::<i128>(sites.max(1))).map_err(device)?;
            let lambda = self.timed(Kind::Alloc, || self.take::<i64>((sites * lanes).max(1))).map_err(device)?;
            let plain = self.timed(Kind::Alloc, || self.take::<i64>((sites * a).max(1))).map_err(device)?;
            let (mut sp, mut at, mut bp, mut lp) = (fscale.device_ptr(), field.layout().loud as u64, beta.device_ptr(), lambda.device_ptr());
            self.launch("field_loud_beta", Self::cells(t64), THREADS, &mut [arg(words), arg(&mut sp), arg(&mut at), arg(&mut bp), arg(&mut lp)])?;
            Some((beta, lambda, plain))
        } else {
            None
        };
        if let Some((beta, _, plain)) = loud.as_ref() {
            let (mut enc, mut cb, mut yp, mut bp, mut zp, mut vp) = (words.enc, words.read_bias, lift.device_ptr(), beta.device_ptr(), z.device_ptr(), plain.device_ptr());
            self.launch("field_tied_face_sharp", Self::cells(t64 * a as u64), THREADS, &mut [arg(words), arg(&mut enc), arg(&mut cb), arg(&mut yp), arg(&mut bp), arg(&mut zp), arg(&mut vp)])?;
        } else {
            let (mut enc, mut cb, mut yp, mut zp) = (words.enc, words.read_bias, lift.device_ptr(), z.device_ptr());
            self.launch("field_tied_face_tiled", Self::map_grid(a, t64 as usize), THREADS, &mut [arg(words), arg(&mut enc), arg(&mut cb), arg(&mut yp), arg(&mut zp)])?;
        }
        // The cavity field (§15.3): a carried site's read less its own echo.
        if echo_has.iter().any(|&h| h != 0) {
            let mut zp = z.device_ptr();
            self.launch("field_echo_apply", Self::cells((sites * a) as u64), THREADS, &mut [arg(words), arg(&mut zp)])?;
        }
        let (mut zp, mut mp, mut tp) = (z.device_ptr(), masses.device_ptr(), totals.device_ptr());
        self.launch("field_face", Self::warps(t64), THREADS, &mut [arg(words), arg(&mut zp), arg(&mut mp), arg(&mut tp)])?;
        self.mark("face_launch");
        // [the ring record §4] A first read's faces give each silent site's shares (the host's `shares`), which stay on the card for the second
        // read's marks; nothing is fetched. [G180] Where the pass returns, the first read then returns from those faces (below), its readings off.
        let marks = match first.as_ref() {
            Some(_) => {
                let shares = self.timed(Kind::Alloc, || self.take::<u32>((sites * a).max(1))).map_err(device)?;
                let mut sp = shares.device_ptr();
                self.launch("field_mark_shares", Self::cells((sites * a) as u64), THREADS, &mut [arg(words), arg(&mut mp), arg(&mut tp), arg(&mut sp)])?;
                Some(shares)
            }
            None => None,
        };
        if let Some(g) = g {
            // The covector's magnitude near and far, where read (§16.20).
            let shares = match reading && self.covector_shares.borrow().is_some() {
                true => Some(self.timed(Kind::Alloc, || self.take_zeroed::<i128>(2 * heads)).map_err(device)?),
                false => None,
            };
            words.dsshare = shares.as_ref().map_or(0, |b| b.device_ptr());
            // The held rows' current covectors, where read (§16.21).
            if reading && self.row_questions.borrow().is_some() {
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
                    let (rows, _) = holonics_engine::field::port_reading(&at, &port)?;
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
            self.reverse(field, words, &ticks, (&clocks, base_clock), g, &fread, &fscale, &lift, &masses, &totals, &classes, &unresolved, &site_pos, &mix_off, &mix_class, &mix_share, &site_weight, &ported, sites, pairs, tower.as_deref_mut().zip(tb), early_clocks, loud.as_ref().map(|(b, l, v)| (&**b, &**l, &**v)))?;
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
        if let Some(out) = first {
            *out = marks;
            return Ok((Vec::new(), Vec::new(), Rows::new(), Vec::new()));
        }
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
        // The lanes' scales by stage, each region's open sites in site order.
        if let Some(out) = self.tick_scales.borrow_mut().as_mut() {
            let lanes = field.declaration.lanes;
            let stages = stage_scales.unwrap_or_default();
            for r in 0..regions.len() {
                let span = region_off[r] as usize..region_off[r + 1] as usize;
                out.push(stages.iter().map(|s| span.clone().filter(|&t| unresolved[t] != 0).flat_map(|t| s[t * lanes..(t + 1) * lanes].iter().copied()).collect()).collect());
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

    /// The batch's refusals, read off the card.
    pub(crate) fn status(&self, status: &CardBuffer<'c, u32>) -> Result<()> {
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
/// ([`Resident::batch`], `tick`, `reverse`): each kept tick's carriers (the chart's read and scale,
/// the word and the value and their framed copies, the word's powers, the classes and members, the
/// masses, the current, the pair contact's read, scale and drives), its class offsets and its weights
/// `H·S²` (their dense reservation), the opening's carried mixtures at most one share a class, the
/// face's carriers, and on a return the reverse's per-site covectors and the contact's return `δs`
/// (`S²` on 128 bits). Measured November 1: sized by the weights and the contact's return alone, a
/// batched release's per-site carriers took the board to 13,372 MiB; sized by its carriers too, the
/// same release peaked at 11,256 MiB.
pub fn region_octets(d: &Declaration, returning: bool, sites: usize, definite: usize) -> u64 {
    read_octets(d, returning, false, sites) + skin_octets(d, sites, definite).0
}

/// [`region_octets`] for a read of `logits` too: a logits read keeps every tick and its shares (the echo's
/// round trips of consecutive ticks, §15.3), as a return does.
pub fn read_octets(d: &Declaration, returning: bool, echo: bool, sites: usize) -> u64 {
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
    // [theory, November 11 17:25] The carry circles' charts' reads `[t][2C]` (64 bits), and their gate, scan operand and coupled drive `[t][2C]` each
    // (32 bits: the gate since November 19, the operand and the drive since November 21).
    let carry_site = (16 + 8 + 8 + 8) * d.carry as u64;
    // [the lead, November 19] The pump's chart read `[t][2C]` (64 bits) and its `η` `[t][2C]` (32 bits) a tick, and its covector `[t][2C]` on the return.
    let pump_site = if d.pump { 24 * d.carry as u64 } else { 0 };
    let carry_site = carry_site + pump_site;
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
    // [the lead, November 21] The circles' pair part `h` `[t][2C]` on 64 bits beside their covector (it had stood on 128 bits, uncounted).
    let reverse_site = if returning { 8 * 8 * d.triads as u64 + 16 * d.carry as u64 + 16 * d.carry as u64 + if d.pump { 16 * d.carry as u64 } else { 0 } + 8 * m2 + 8 * a + 5 * 8 * dw + 3 * 8 * f + 8 * m2 + 8 * h * span + 2 * 8 * m2 + 16 * m2 + 2 * 16 * span + 112 * tm } else { 0 };
    // [the ring record §4] A field that reads twice holds its first read's shares `[t][A]` through the second read, and its return the marked
    // sites' list and `release(α_b dx, 24)` in each of the three encodings (`[3][t][D]` at most). [G180] Where both reads return, the first
    // leaves the base clock's two covectors from the opening's comparison (`[p][t]` on 128 bits each) for the second; the reads' own carriers
    // are each read's, one read at a time.
    let mark_site = if d.mark { 4 * a + if returning { 4 + 3 * 8 * dw + 2 * 16 * d.paced_heads() as u64 } else { 0 } } else { 0 };
    let (s, pairs) = (sites as u64, (sites * sites) as u64);
    // The shares are kept for a return and an echo; the reverse holds one head's covector a pair on 64 bits.
    let weights = h * 8 * pairs * if returning { 2 } else { 1 };
    ticks_kept * (weights + s * tick_site + tick_fixed) + s * (face_site + mixture_site + moment_site + reverse_site + mark_site + 8 * m2) + if returning { 24 * pairs } else { 0 }
}

/// A kept tick's octets a region beside its sites': the carrier's width (one word), the class
/// offsets `H (2·3^b + 1)` words (each class's definite members and the rest) and the prefix sums'
/// extra row (a region's `S + 1` rows, §14.10), which the reverse's difference arrays share.
pub(crate) fn tick_fixed_octets(d: &Declaration) -> u64 {
    4 + 4 * d.heads as u64 * (2 * d.classes() as u64 + 1) + 4 * d.heads as u64 * (d.classes() as u64 + 1) + (2 * 16 * 2 * d.modes as u64 + 8) * d.heads as u64 + 2 * 16 * 2 * d.modes as u64
}

/// An encoding's entries sorted by the row they opened on (`rows` holds each entry's row, site and
/// share, `rows_n` the encoding's rows), and each row's entries cut into segments of at most
/// `OUTER_TILE` (each its row, first and end in the sorted entries): one thread a segment and a column.
pub(crate) fn encoding_partition(rows: &[(usize, u32, u32)], rows_n: usize) -> (Vec<u32>, Vec<u32>, Vec<u32>) {
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

impl Realization for Resident<'_> {
    fn read_and_return(&mut self, field: &Constitution, regions: &[Region]) -> Result<(Vec<Vec<Option<TowerFace>>>, Vec<i128>)> {
        let (faces, _, g, _, _) = self.run(field, regions, true, false, None)?;
        Ok((faces, g))
    }

    /// [realization; theory, November 13, P58 item 3] The faces' masses at their classes and their totals gathered on the card (`narrow`, read
    /// at the batch's end), the whole faces where a region has a port (its coupling reads every class of its places).
    fn read_and_return_at_class(&mut self, field: &Constitution, regions: &[Region]) -> Result<(Vec<Vec<Option<(u128, u128)>>>, Vec<i128>)> {
        if regions.iter().any(|r| r.port.is_some()) {
            let (faces, g) = self.read_and_return(field, regions)?;
            return Ok((holonics_engine::field::faces_at_class(&faces, regions), g));
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
    fn read_and_return_opening(&mut self, field: &Constitution, regions: &[Region]) -> Result<(Vec<Vec<Option<(u128, u128)>>>, Vec<i128>, Vec<Vec<Option<i64>>>)> {
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

    fn read_faces(&mut self, field: &Constitution, regions: &[Region]) -> Result<Vec<Vec<Option<TowerFace>>>> {
        Ok(self.run(field, regions, false, false, None)?.0)
    }

    /// [measurement; theory, November 13, P57 item 2 (G132)] The faces and the open sites' charts by stage, from one forward that keeps every tick.
    fn read_tick_charts(&mut self, field: &Constitution, regions: &[Region]) -> Result<(Vec<Vec<Option<TowerFace>>>, Vec<Vec<Vec<i32>>>)> {
        *self.tick_charts.borrow_mut() = Some(Vec::new());
        let read = self.run(field, regions, false, true, None);
        let charts = self.tick_charts.borrow_mut().take().unwrap_or_default();
        let faces = read?.0;
        if charts.len() != regions.len() {
            return Err(TowerError::Refused("a read of the charts by stage that did not return one a region"));
        }
        Ok((faces, charts))
    }

    /// [measurement; Brandon, November 15 00:58Z] The faces and the open sites' lane scales by stage, from one forward that keeps every tick.
    fn read_tick_scales(&mut self, field: &Constitution, regions: &[Region]) -> Result<(Vec<Vec<Option<TowerFace>>>, Vec<Vec<Vec<i128>>>)> {
        *self.tick_scales.borrow_mut() = Some(Vec::new());
        let read = self.run(field, regions, false, true, None);
        let scales = self.tick_scales.borrow_mut().take().unwrap_or_default();
        let faces = read?.0;
        if scales.len() != regions.len() {
            return Err(TowerError::Refused("a read of the lane powers by stage that did not return one a region"));
        }
        Ok((faces, scales))
    }

    /// [measurement; the lead, November 24, Brandon's 17:36Z on iteration pace] The faces, the open sites' charts and their lane scales by
    /// stage from one forward that keeps every tick: `run` gathers the charts and fetches the scales under their own cells, so one pass with
    /// both cells set returns what the two reads return one after the other.
    fn read_tick_charts_scales(&mut self, field: &Constitution, regions: &[Region]) -> Result<(Vec<Vec<Option<TowerFace>>>, Vec<Vec<Vec<i32>>>, Vec<Vec<Vec<i128>>>)> {
        *self.tick_charts.borrow_mut() = Some(Vec::new());
        *self.tick_scales.borrow_mut() = Some(Vec::new());
        let read = self.run(field, regions, false, true, None);
        let charts = self.tick_charts.borrow_mut().take().unwrap_or_default();
        let scales = self.tick_scales.borrow_mut().take().unwrap_or_default();
        let faces = read?.0;
        if charts.len() != regions.len() || scales.len() != regions.len() {
            return Err(TowerError::Refused("a read of the charts and the lane powers by stage that did not return one of each a region"));
        }
        Ok((faces, charts, scales))
    }

    /// [measurement; part P2] The faces and the carry circles' gates from the same pass: every tick's gate and leak reads are summed on the card
    /// over the open sites (`field_carry_gates_read`), so no face and no other read changes.
    fn read_faces_gated(&mut self, field: &Constitution, regions: &[Region]) -> Result<(Vec<Vec<Option<TowerFace>>>, CarryGates)> {
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

    fn read_logits(&mut self, field: &Constitution, regions: &[Region]) -> Result<Vec<ReadLogits>> {
        let (_, logits, _, _, echo) = self.run(field, regions, false, true, None)?;
        Ok(logits.into_iter().zip(echo).map(|(logits, echo)| ReadLogits { logits, echo }).collect())
    }

    fn read_landmarks(&mut self, field: &Constitution, region: &Region, question: usize, sites: &[usize], count: usize) -> Result<Vec<Vec<(usize, u64)>>> {
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

    fn read_row_currents(&mut self, field: &Constitution, regions: &[Region], questions: &[usize], returning: bool) -> Result<Vec<Vec<RowCurrent>>> {
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

    fn read_covector_shares(&mut self, field: &Constitution, regions: &[Region]) -> Result<Vec<[u128; 2]>> {
        *self.covector_shares.borrow_mut() = Some(vec![0i128; 2 * field.declaration.heads]);
        let read = self.run(field, regions, true, false, None);
        let total = self.covector_shares.borrow_mut().take().unwrap_or_default();
        read?;
        Ok(total.chunks_exact(2).map(|c| [c[0] as u128, c[1] as u128]).collect())
    }

    fn read_ticks(&mut self, field: &Constitution, regions: &[Region]) -> Result<Vec<Vec<TickRead>>> {
        // Every tick is kept where a logits read keeps them; its reads are fetched after the forward.
        *self.tick_reads.borrow_mut() = Some(Vec::new());
        let read = self.run(field, regions, false, true, None);
        let out = self.tick_reads.borrow_mut().take().unwrap_or_default();
        read?;
        Ok(out)
    }

    fn read_blank_clocks(&mut self, field: &Constitution, region: &Region, sites: &[usize]) -> Result<Vec<BlankClocks>> {
        *self.clock_sites.borrow_mut() = Some(sites.to_vec());
        self.clock_out.borrow_mut().clear();
        let read = self.run(field, std::slice::from_ref(region), false, true, None);
        *self.clock_sites.borrow_mut() = None;
        read?;
        Ok(std::mem::take(&mut *self.clock_out.borrow_mut()))
    }

    fn read_near_offsets(&mut self, field: &Constitution, region: &Region, sites: &[usize]) -> Result<Vec<NearOffsets>> {
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

    fn read_row_shares(&mut self, field: &Constitution, regions: &[Region], questions: &[usize]) -> Result<Vec<HeldRows>> {
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
pub(crate) type Rows = Vec<Vec<(Vec<(u32, u64)>, u64)>>;

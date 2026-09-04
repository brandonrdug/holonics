//! mount-link-gate — the SECOND rung of the CUDA/PTX mount recut. It gates the CUDA port of the
//! CONFIGURATION FOLD entry family (`link_grain` · `link_sum` · `link_finish`) BYTE-EXACT against
//! the cpu reference fold, on the headless RTX 4080 SUPER.
//!
//!   stage a bounded co-present configuration (pre-light standing ⊕ N disjoint OWN planes, built
//!   through `body`'s law) -> compute the cpu reference with `body::medium::integrate` (the SAME
//!   fold the SPIR-V card reproduces) -> upload -> dispatch the three CUDA entries in the same
//!   two-pass geometry the wgpu card uses (block 64, 2-D grid, the dispatch boundary is the pass
//!   boundary) -> read back -> assert the card's final standing, topology reads, and touched map are
//!   BYTE-EXACT with the cpu's.
//!
//! Byte-exactness is the gate; the printed figures are whatever the honestly-staged data produces.
//! The staging replicates the GATE DATA (the forms that cross into the fold), never the fold itself
//! — the fold is `body`'s, run once cpu-side as the reference and once on the card. Nothing is
//! scored. On any driver fault the exact CUresult name prints and the gate stops — no retry.

use std::ffi::c_void;
use std::time::Instant;

use body::medium::{integrate, RegionalForm, FORM_WORDS};
use body::num::{Cog, Rung};
use mount::{Context, Device, DeviceBuffer, Dim3, Module, Result};

/// The committed PTX boundary artifact, built by soma-kernel-cuda/build-ptx.sh (like kernel/soma.spv
/// is the Vulkan boundary and mount_smoke_kernel.ptx is the smoke boundary).
const PTX: &[u8] = include_bytes!("../../../../accelerators/cuda-kernel/soma_kernel_cuda.ptx");

/// The staged configuration. 65,536 places · 3 co-present OWN planes — the same shape/scale as the
/// card's SEAM_CELLS three-lineage gate (the figures differ because the forms are staged here, not
/// carried from a real light; byte-exactness against the cpu reference is the gate).
const CELLS: usize = 1 << 16; // 65,536
const LANES: usize = 3;
const BLOCK: u32 = 64; // mirrors the SPIR-V `threads(64)`

/// Deterministic staging of one OWN form at (lane, cell) — the GATE DATA. Occupied ~3/4 of the time;
/// lane-varying resultant ranks (so the grain max across lanes is genuinely exercised) and mixed
/// one-/two-armed fibers (so the fiber and two-armed reads are non-vacuous). Cells at the reserved
/// standing stride are FORCED unborn in every lane, so those pre-light standing forms stay untouched
/// — exercising link_finish's read-standing-and-count branch. Pure `body` law construction.
fn own_form(lane: usize, cell: usize) -> RegionalForm {
    if cell % 257 == 0 {
        return RegionalForm::UNBORN; // reserved for an untouched pre-light standing form
    }
    if (cell * 7 + lane * 3) % 4 == 0 {
        return RegionalForm::UNBORN; // ~1/4 unborn per lane
    }
    let base = (cell % 1000 + 1) as i64;
    let same = Cog::lit(base << (lane * 11)); // lane-varying resultant rank
    let other = if cell % 5 == 0 {
        Cog::lit((base + 3) << (lane * 5))
    } else {
        Cog::lit(0)
    };
    let this_way = if cell % 2 == 0 {
        Rung::of(((cell % 200) + 1) as i32)
    } else {
        Rung::ZERO
    };
    let that_way = if cell % 3 == 0 {
        Rung::of(((cell % 150) + 1) as i32)
    } else {
        Rung::ZERO
    };
    RegionalForm::from_components(same, other, this_way, that_way).occupy()
}

/// A pre-light standing form at `cell` — occupied only on the reserved stride the OWN planes leave
/// untouched, so the fold must carry it through unchanged and still count it in the topology read.
fn standing_form(cell: usize) -> RegionalForm {
    if cell % 257 == 0 {
        let v = (cell % 400 + 1) as i64;
        RegionalForm::from_components(Cog::lit(v), Cog::lit(0), Rung::of(1), Rung::ZERO).occupy()
    } else {
        RegionalForm::UNBORN
    }
}

/// Pass an owned scalar (a device pointer or a length) as a `cuLaunchKernel` argument slot.
fn arg(v: &mut u64) -> *mut c_void {
    v as *mut u64 as *mut c_void
}

fn run() -> Result<()> {
    let t_all = Instant::now();

    // --- stage the GATE DATA ------------------------------------------------------------------
    let words = CELLS * FORM_WORDS;
    let mut pre_light = vec![0u32; words];
    for cell in 0..CELLS {
        standing_form(cell).pack(&mut pre_light, cell * FORM_WORDS);
    }
    let mut owns = vec![0u32; LANES * words];
    for lane in 0..LANES {
        for cell in 0..CELLS {
            own_form(lane, cell).pack(&mut owns, (lane * CELLS + cell) * FORM_WORDS);
        }
    }

    // --- the CPU REFERENCE: one fold per touched place, `body::medium::integrate` --------------
    // Identical to life's `integrate_light`: forms = [pre-light standing, own0, own1, ...]; a place
    // is touched iff any OWN plane is occupied; touched places fold once, untouched stay as staged.
    let mut cpu_standing = pre_light.clone();
    let mut expected_touched = vec![0u32; CELLS];
    let mut forms: Vec<RegionalForm> = Vec::with_capacity(LANES + 1);
    for cell in 0..CELLS {
        let at = cell * FORM_WORDS;
        forms.clear();
        forms.push(RegionalForm::unpack(&pre_light, at));
        let mut touched = false;
        for lane in 0..LANES {
            let f = RegionalForm::unpack(&owns, (lane * CELLS + cell) * FORM_WORDS);
            touched |= f != RegionalForm::UNBORN;
            forms.push(f);
        }
        if touched {
            expected_touched[cell] = 1;
            integrate(&forms).pack(&mut cpu_standing, at);
        }
    }
    // The topology projection over the FINAL standing (occupied · resultant · fiber · two-armed).
    let mut expected_reads = [0u64; 4];
    for cell in 0..CELLS {
        let form = RegionalForm::unpack(&cpu_standing, cell * FORM_WORDS);
        if form != RegionalForm::UNBORN {
            let (same, other) = form.resultant();
            let (this_way, that_way) = form.fiber();
            expected_reads[0] += 1;
            expected_reads[1] += (same.mag != 0 || other.mag != 0) as u64;
            expected_reads[2] += (this_way.mag != 0 || that_way.mag != 0) as u64;
            expected_reads[3] += (this_way.mag != 0 && that_way.mag != 0) as u64;
        }
    }

    // --- init + device selection (refuse to run anywhere but the 4080) --------------------------
    mount::cuda::init()?;
    let count = Device::count()?;
    if count < 1 {
        eprintln!("FAILED: no CUDA device visible (cuDeviceGetCount == 0)");
        std::process::exit(1);
    }
    let mut chosen: Option<Device> = None;
    for ord in 0..count {
        let dev = Device::get(ord)?;
        if dev.name.contains("4080") {
            chosen = Some(dev);
            break;
        }
    }
    let device = match chosen {
        Some(d) => d,
        None => {
            eprintln!("FAILED: no device whose name contains \"4080\" (refusing to run elsewhere)");
            std::process::exit(1);
        }
    };
    println!("device: {}", device.name);
    let _ctx = Context::create(&device)?;

    // --- load the Rust-emitted PTX --------------------------------------------------------------
    let ptx_head = String::from_utf8_lossy(PTX)
        .lines()
        .find(|l| l.trim_start().starts_with(".target"))
        .unwrap_or("<no .target>")
        .trim()
        .to_string();
    println!("ptx:    {} ({} bytes)", ptx_head, PTX.len());
    let t_load = Instant::now();
    let module = Module::load_ptx(PTX)?;
    let grain = module.function("link_grain")?;
    let sum = module.function("link_sum")?;
    let finish = module.function("link_finish")?;
    println!(
        "load:   {} us (cuModuleLoadData + 3 cuModuleGetFunction)",
        t_load.elapsed().as_micros()
    );
    println!(
        "staged: {} places · {} co-present OWN planes · {} u32 standing words · {} u32 own words",
        CELLS,
        LANES,
        words,
        LANES * words
    );

    // --- upload every buffer (the exact contract the SPIR-V entries bind) ------------------------
    let standing_b: DeviceBuffer<u32> = DeviceBuffer::alloc(words)?;
    standing_b.copy_from_slice(&pre_light)?;
    let owns_b: DeviceBuffer<u32> = DeviceBuffer::alloc(LANES * words)?;
    owns_b.copy_from_slice(&owns)?;
    let cog_grains_b: DeviceBuffer<u64> = DeviceBuffer::alloc_zeroed(CELLS * 2)?;
    let arm_grains_b: DeviceBuffer<u32> = DeviceBuffer::alloc_zeroed(CELLS * 2)?;
    let cog_sums_b: DeviceBuffer<u64> = DeviceBuffer::alloc_zeroed(CELLS * 2)?;
    let arm_sums_b: DeviceBuffer<u64> = DeviceBuffer::alloc_zeroed(CELLS * 2)?;
    let touched_b: DeviceBuffer<u32> = DeviceBuffer::alloc_zeroed(CELLS)?;
    let reads_b: DeviceBuffer<u64> = DeviceBuffer::alloc_zeroed(4)?;

    // --- dispatch geometry — mirrors surface::resolve_resident --------------------------------
    let cell_groups = (CELLS as u64).div_ceil(BLOCK as u64);
    let source_groups = ((CELLS as u64) * (LANES as u64 + 1)).div_ceil(BLOCK as u64);
    let work_x = cell_groups as u32; // fits CUDA's grid.x (<= 2^31-1) directly at this scale
    let source_y = source_groups.div_ceil(work_x as u64) as u32;
    let finish_y = cell_groups.div_ceil(work_x as u64) as u32;
    let params: [u32; 3] = [CELLS as u32, LANES as u32, work_x * BLOCK];
    let params_b: DeviceBuffer<u32> = DeviceBuffer::alloc(params.len())?;
    params_b.copy_from_slice(&params)?;
    println!(
        "grid:   block {} · grain/sum {}x{} · finish {}x{} · params[2]={}",
        BLOCK, work_x, source_y, work_x, finish_y, params[2]
    );

    // Owned scalar arg slots (device pointers + lengths), rebuilt per launch in declared order.
    let (mut p_st, mut l_st) = (standing_b.device_ptr(), words as u64);
    let (mut p_ow, mut l_ow) = (owns_b.device_ptr(), (LANES * words) as u64);
    let (mut p_cg, mut l_cg) = (cog_grains_b.device_ptr(), (CELLS * 2) as u64);
    let (mut p_ag, mut l_ag) = (arm_grains_b.device_ptr(), (CELLS * 2) as u64);
    let (mut p_cs, mut l_cs) = (cog_sums_b.device_ptr(), (CELLS * 2) as u64);
    let (mut p_as, mut l_as) = (arm_sums_b.device_ptr(), (CELLS * 2) as u64);
    let (mut p_tc, mut l_tc) = (touched_b.device_ptr(), CELLS as u64);
    let (mut p_rd, mut l_rd) = (reads_b.device_ptr(), 4u64);
    let (mut p_pr, mut l_pr) = (params_b.device_ptr(), params.len() as u64);

    let t_fold = Instant::now();
    // PASS 1 — link_grain(standing, owns, cog_grains, arm_grains, touched, params)
    {
        let mut a: [*mut c_void; 12] = [
            arg(&mut p_st),
            arg(&mut l_st),
            arg(&mut p_ow),
            arg(&mut l_ow),
            arg(&mut p_cg),
            arg(&mut l_cg),
            arg(&mut p_ag),
            arg(&mut l_ag),
            arg(&mut p_tc),
            arg(&mut l_tc),
            arg(&mut p_pr),
            arg(&mut l_pr),
        ];
        grain.launch(
            Dim3 {
                x: work_x,
                y: source_y,
                z: 1,
            },
            Dim3::x(BLOCK),
            &mut a,
        )?;
        _ctx.synchronize()?;
    }
    // PASS 2 — link_sum(standing, owns, cog_grains, arm_grains, cog_sums, arm_sums, touched, params)
    {
        let mut a: [*mut c_void; 16] = [
            arg(&mut p_st),
            arg(&mut l_st),
            arg(&mut p_ow),
            arg(&mut l_ow),
            arg(&mut p_cg),
            arg(&mut l_cg),
            arg(&mut p_ag),
            arg(&mut l_ag),
            arg(&mut p_cs),
            arg(&mut l_cs),
            arg(&mut p_as),
            arg(&mut l_as),
            arg(&mut p_tc),
            arg(&mut l_tc),
            arg(&mut p_pr),
            arg(&mut l_pr),
        ];
        sum.launch(
            Dim3 {
                x: work_x,
                y: source_y,
                z: 1,
            },
            Dim3::x(BLOCK),
            &mut a,
        )?;
        _ctx.synchronize()?;
    }
    // FINISH — link_finish(standing, cog_grains, arm_grains, cog_sums, arm_sums, touched, reads, params)
    {
        let mut a: [*mut c_void; 16] = [
            arg(&mut p_st),
            arg(&mut l_st),
            arg(&mut p_cg),
            arg(&mut l_cg),
            arg(&mut p_ag),
            arg(&mut l_ag),
            arg(&mut p_cs),
            arg(&mut l_cs),
            arg(&mut p_as),
            arg(&mut l_as),
            arg(&mut p_tc),
            arg(&mut l_tc),
            arg(&mut p_rd),
            arg(&mut l_rd),
            arg(&mut p_pr),
            arg(&mut l_pr),
        ];
        finish.launch(
            Dim3 {
                x: work_x,
                y: finish_y,
                z: 1,
            },
            Dim3::x(BLOCK),
            &mut a,
        )?;
        _ctx.synchronize()?;
    }
    let fold_us = t_fold.elapsed().as_micros();

    // --- read back and assert BYTE-EXACT --------------------------------------------------------
    let mut card_standing = vec![0u32; words];
    standing_b.copy_to_slice(&mut card_standing)?;
    let mut card_owns = vec![0u32; LANES * words];
    owns_b.copy_to_slice(&mut card_owns)?;
    let mut card_touched = vec![0u32; CELLS];
    touched_b.copy_to_slice(&mut card_touched)?;
    let mut card_reads = [0u64; 4];
    reads_b.copy_to_slice(&mut card_reads)?;

    let standing_ok = card_standing == cpu_standing;
    let owns_ok = card_owns == owns;
    let touched_ok = card_touched == expected_touched;
    let reads_ok = card_reads == expected_reads;

    println!(
        "link:   {} occupied/resultant · {} fiber · {} two-armed   (cpu {} · {} · {})",
        card_reads[0],
        card_reads[2],
        card_reads[3],
        expected_reads[0],
        expected_reads[2],
        expected_reads[3]
    );
    println!(
        "        reads card {:?}  cpu {:?}",
        card_reads, expected_reads
    );

    if standing_ok && owns_ok && touched_ok && reads_ok {
        println!(
            "GATE configuration-fold: EXACT  (card standing == cpu standing, {} u32 words; \
OWN planes intact; touched map exact; topology read exact; {} us)",
            words, fold_us
        );
        println!("total:  {} us", t_all.elapsed().as_micros());
        println!("mount link gate: EXACT");
        Ok(())
    } else {
        if !standing_ok {
            let bad = card_standing
                .iter()
                .zip(cpu_standing.iter())
                .position(|(c, h)| c != h)
                .unwrap();
            let cell = bad / FORM_WORDS;
            let at = cell * FORM_WORDS;
            eprintln!(
                "  standing DIVERGES at cell {} (word {}): card {:?} cpu {:?}",
                cell,
                bad % FORM_WORDS,
                RegionalForm::unpack(&card_standing, at),
                RegionalForm::unpack(&cpu_standing, at),
            );
        }
        println!(
            "GATE configuration-fold: FAILED (standing {} · owns {} · touched {} · reads {})",
            yn(standing_ok),
            yn(owns_ok),
            yn(touched_ok),
            yn(reads_ok)
        );
        std::process::exit(1);
    }
}

fn yn(b: bool) -> &'static str {
    if b {
        "ok"
    } else {
        "BAD"
    }
}

fn main() {
    if let Err(e) = run() {
        eprintln!("FAILED: {}", e); // the driver's own error name + description (e.g. an Xid), then stop
        std::process::exit(2);
    }
}

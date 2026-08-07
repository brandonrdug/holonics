//! mount-founded-gate — the M5 rung of the CUDA/PTX mount recut. It gates the CUDA port of the
//! FOUNDED-CELL fold (`link_founded_grain` · `link_founded_sum`, resolved by the shared
//! `link_finish`) BYTE-EXACT against the host reference fold, on the headless RTX 4080 SUPER.
//!
//!   stage a reservation-sized OWN buffer (a concatenation of live founded cells, each carrying its
//!   founding POSITION beside its accumulated form, built through `body`'s law) ⊕ a dense pre-light
//!   standing plane -> compute the host reference with `body::medium::integrate` per receiving grip
//!   (the SAME fold the SPIR-V card reproduces; each founded cell re-grounds to its standing grip via
//!   `place::ground`) -> upload -> dispatch the two founded passes and the shared finish in the same
//!   two-pass geometry the wgpu card uses (block 64, 2-D grid, the dispatch boundary is the pass
//!   boundary) -> read back -> assert the card's final standing, topology reads, touched map, and the
//!   untouched OWN reservation are BYTE-EXACT with the host's.
//!
//! Five representative sizes are swept — 0, 1, 64 (one workgroup), 100 (a non-multiple of 64), and a
//! multi-block reservation — so every dispatch-boundary and guard path is exercised. Byte-exactness
//! is the gate; the printed figures are whatever the honestly-staged data produces. The staging
//! replicates the GATE DATA (the founded cells that cross into the fold), never the fold itself — the
//! fold is `body`'s, run once host-side as the reference and once on the card. Nothing is scored. On
//! any driver fault the exact CUresult name prints and the gate stops — no retry.

use std::ffi::c_void;
use std::time::Instant;

use body::manifold::{
    cog_packed_word, COG_WORDS, OWN_CELL_FORM, OWN_CELL_LIVE, OWN_CELL_POSITION, OWN_CELL_WORDS,
};
use body::medium::{integrate, RegionalForm, FORM_WORDS};
use body::num::{Cog, Rung};
use body::place::{self, Place};
use mount::{Context, DeviceBuffer, Dim3, Function, Module, Result};

/// The committed PTX boundary artifact, built by soma-kernel-cuda/build-ptx.sh.
const PTX: &[u8] = include_bytes!("../../soma-kernel-cuda/soma_kernel_cuda.ptx");

const BLOCK: u32 = 64; // mirrors the SPIR-V `threads(64)`
/// The receiving standing chart's dyadic axis (a power of two). 64 → 4,096 standing places, itself a
/// multi-block dispatch, so the standing (`!own`) leg is always exercised beside the founded cells.
const STANDING_AXIS: usize = 64;
const STANDING_CELLS: usize = STANDING_AXIS * STANDING_AXIS;
/// The founded-cell counts swept: empty · single · one workgroup · a non-multiple of 64 · multi-block.
const OWN_COUNTS: [usize; 5] = [0, 1, 64, 100, 5000];

/// Pass an owned scalar (a device pointer or a length) as a `cuLaunchKernel` argument slot.
fn arg(v: &mut u64) -> *mut c_void {
    v as *mut u64 as *mut c_void
}

/// Deterministic staging of one founded OWN cell's founding POSITION — a swung complex place that
/// `place::ground` bands into some standing grip. Varied so the sum across many founded cells landing
/// on one grip is genuinely exercised. Pure `body` construction (a `Place` is `(Cog, Cog)`).
fn own_position(i: usize) -> Place {
    let a = ((i as u64).wrapping_mul(2654435761) & 0xffff) as i64 + 1;
    let b = ((i as u64).wrapping_mul(40503).wrapping_add(12345) & 0xffff) as i64 + 1;
    (Cog::lit(a), Cog::lit(b))
}

/// Deterministic staging of one founded OWN cell's accumulated form (occupied; mixed resultant ranks
/// and one-/two-armed fibers so every read branch is non-vacuous). Pure `body` law construction.
fn own_form(i: usize) -> RegionalForm {
    let base = (i % 1000 + 1) as i64;
    let same = Cog::lit(base << (i % 7));
    let other = if i % 5 == 0 {
        Cog::lit((base + 3) << (i % 3))
    } else {
        Cog::lit(0)
    };
    let this_way = if i % 2 == 0 {
        Rung::of(((i % 200) + 1) as i32)
    } else {
        Rung::ZERO
    };
    let that_way = if i % 3 == 0 {
        Rung::of(((i % 150) + 1) as i32)
    } else {
        Rung::ZERO
    };
    RegionalForm::from_components(same, other, this_way, that_way).occupy()
}

/// A pre-light standing form — an occupied third of the chart, so touched grips fold standing ⊕ owns
/// and untouched grips carry their standing form through unchanged (link_finish's read-standing leg).
fn standing_form(cell: usize) -> RegionalForm {
    if cell % 3 == 0 {
        let v = (cell % 400 + 1) as i64;
        RegionalForm::from_components(Cog::lit(v), Cog::lit(0), Rung::of(1), Rung::ZERO).occupy()
    } else {
        RegionalForm::UNBORN
    }
}

/// Pack one founded OWN cell (live flag ⊕ founding position ⊕ form) into the reservation at `at`,
/// exactly the layout `own_cell_position` / the founded passes read.
fn pack_founded_cell(owns: &mut [u32], at: usize, live: bool, position: Place, form: RegionalForm) {
    owns[at + OWN_CELL_LIVE] = live as u32;
    for w in 0..COG_WORDS {
        owns[at + OWN_CELL_POSITION + w] = cog_packed_word(position.0, w);
        owns[at + OWN_CELL_POSITION + COG_WORDS + w] = cog_packed_word(position.1, w);
    }
    form.pack(owns, at + OWN_CELL_FORM);
}

/// One swept size: stage, host-reference, dispatch the three passes, read back, assert BYTE-EXACT.
#[allow(clippy::too_many_arguments)]
fn founded_case(
    ctx: &Context,
    grain: &Function,
    sum: &Function,
    finish: &Function,
    own_cells: usize,
) -> Result<bool> {
    // --- stage the GATE DATA ------------------------------------------------------------------
    let standing_words = STANDING_CELLS * FORM_WORDS;
    let mut pre_light = vec![0u32; standing_words];
    for cell in 0..STANDING_CELLS {
        standing_form(cell).pack(&mut pre_light, cell * FORM_WORDS);
    }
    let mut owns = vec![0u32; own_cells * OWN_CELL_WORDS];
    for i in 0..own_cells {
        let live = i % 9 != 0; // ~1/9 staged dead, exercising the live-flag guard
        pack_founded_cell(
            &mut owns,
            i * OWN_CELL_WORDS,
            live,
            own_position(i),
            own_form(i),
        );
    }

    // --- the HOST REFERENCE: read the SAME staged reservation, ground each live cell, fold once ---
    let mut host_standing = pre_light.clone();
    let mut expected_touched = vec![0u32; STANDING_CELLS];
    let mut at_cell: Vec<Vec<RegionalForm>> = vec![Vec::new(); STANDING_CELLS];
    for i in 0..own_cells {
        let at = i * OWN_CELL_WORDS;
        if owns[at + OWN_CELL_LIVE] == 0 {
            continue;
        }
        let position = body::manifold::own_cell_position(&owns, at);
        let target = place::ground(position, STANDING_AXIS as i64) as usize;
        if target >= STANDING_CELLS {
            continue; // ground() is bounded by axis², so this never fires here — mirrors the card guard
        }
        at_cell[target].push(RegionalForm::unpack(&owns, at + OWN_CELL_FORM));
    }
    for cell in 0..STANDING_CELLS {
        if at_cell[cell].is_empty() {
            continue;
        }
        expected_touched[cell] = 1;
        let mut forms: Vec<RegionalForm> = Vec::with_capacity(1 + at_cell[cell].len());
        forms.push(RegionalForm::unpack(&pre_light, cell * FORM_WORDS));
        forms.extend_from_slice(&at_cell[cell]);
        integrate(&forms).pack(&mut host_standing, cell * FORM_WORDS);
    }
    let mut expected_reads = [0u64; 4];
    for cell in 0..STANDING_CELLS {
        let form = RegionalForm::unpack(&host_standing, cell * FORM_WORDS);
        if form != RegionalForm::UNBORN {
            let (same, other) = form.resultant();
            let (this_way, that_way) = form.fiber();
            expected_reads[0] += 1;
            expected_reads[1] += (same.mag != 0 || other.mag != 0) as u64;
            expected_reads[2] += (this_way.mag != 0 || that_way.mag != 0) as u64;
            expected_reads[3] += (this_way.mag != 0 && that_way.mag != 0) as u64;
        }
    }

    // --- upload the exact buffer contract the founded passes bind -------------------------------
    let owns_len = own_cells * OWN_CELL_WORDS;
    let standing_b: DeviceBuffer<u32> = DeviceBuffer::alloc(standing_words)?;
    standing_b.copy_from_slice(&pre_light)?;
    let owns_b: DeviceBuffer<u32> = DeviceBuffer::alloc(owns_len.max(1))?;
    owns_b.copy_from_slice(&{
        let mut o = owns.clone();
        if o.is_empty() {
            o.push(0); // a one-word placeholder for the empty reservation (never read; guards fire)
        }
        o
    })?;
    let cog_grains_b: DeviceBuffer<u64> = DeviceBuffer::alloc_zeroed(STANDING_CELLS * 2)?;
    let arm_grains_b: DeviceBuffer<u32> = DeviceBuffer::alloc_zeroed(STANDING_CELLS * 2)?;
    let cog_sums_b: DeviceBuffer<u64> = DeviceBuffer::alloc_zeroed(STANDING_CELLS * 2)?;
    let arm_sums_b: DeviceBuffer<u64> = DeviceBuffer::alloc_zeroed(STANDING_CELLS * 2)?;
    let touched_b: DeviceBuffer<u32> = DeviceBuffer::alloc_zeroed(STANDING_CELLS)?;
    let reads_b: DeviceBuffer<u64> = DeviceBuffer::alloc_zeroed(4)?;

    // --- dispatch geometry — mirrors surface::resolve_resident (work_x from the finish range) ----
    let cell_groups = (STANDING_CELLS as u64).div_ceil(BLOCK as u64);
    let source_groups = ((STANDING_CELLS + own_cells) as u64).div_ceil(BLOCK as u64);
    let work_x = cell_groups as u32;
    let source_y = source_groups.div_ceil(work_x as u64) as u32;
    let finish_y = cell_groups.div_ceil(work_x as u64) as u32;
    let params: [u32; 4] = [
        STANDING_CELLS as u32,
        own_cells as u32,
        work_x * BLOCK,
        STANDING_AXIS as u32,
    ];
    let params_b: DeviceBuffer<u32> = DeviceBuffer::alloc(params.len())?;
    params_b.copy_from_slice(&params)?;

    let (mut p_st, mut l_st) = (standing_b.device_ptr(), standing_words as u64);
    let (mut p_ow, mut l_ow) = (owns_b.device_ptr(), owns_len.max(1) as u64);
    let (mut p_cg, mut l_cg) = (cog_grains_b.device_ptr(), (STANDING_CELLS * 2) as u64);
    let (mut p_ag, mut l_ag) = (arm_grains_b.device_ptr(), (STANDING_CELLS * 2) as u64);
    let (mut p_cs, mut l_cs) = (cog_sums_b.device_ptr(), (STANDING_CELLS * 2) as u64);
    let (mut p_as, mut l_as) = (arm_sums_b.device_ptr(), (STANDING_CELLS * 2) as u64);
    let (mut p_tc, mut l_tc) = (touched_b.device_ptr(), STANDING_CELLS as u64);
    let (mut p_rd, mut l_rd) = (reads_b.device_ptr(), 4u64);
    let (mut p_pr, mut l_pr) = (params_b.device_ptr(), params.len() as u64);

    let t = Instant::now();
    // PASS 1 — link_founded_grain(standing, owns, cog_grains, arm_grains, touched, params)
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
        ctx.synchronize()?;
    }
    // PASS 2 — link_founded_sum(standing, owns, cog_grains, arm_grains, cog_sums, arm_sums, touched, params)
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
        ctx.synchronize()?;
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
        ctx.synchronize()?;
    }
    let fold_us = t.elapsed().as_micros();

    // --- read back and assert BYTE-EXACT --------------------------------------------------------
    let mut card_standing = vec![0u32; standing_words];
    standing_b.copy_to_slice(&mut card_standing)?;
    let mut card_touched = vec![0u32; STANDING_CELLS];
    touched_b.copy_to_slice(&mut card_touched)?;
    let mut card_reads = [0u64; 4];
    reads_b.copy_to_slice(&mut card_reads)?;
    let mut card_owns = vec![0u32; owns_len.max(1)];
    owns_b.copy_to_slice(&mut card_owns)?;

    let standing_ok = card_standing == host_standing;
    let touched_ok = card_touched == expected_touched;
    let reads_ok = card_reads == expected_reads;
    let owns_ok = card_owns[..owns_len] == owns[..];

    if standing_ok && touched_ok && reads_ok && owns_ok {
        println!(
            "  own_cells {:>5}: EXACT  (standing {} u32 · {} touched · reads {:?} · {} us)",
            own_cells,
            standing_words,
            expected_touched.iter().sum::<u32>(),
            card_reads,
            fold_us
        );
        Ok(true)
    } else {
        if !standing_ok {
            let bad = card_standing
                .iter()
                .zip(host_standing.iter())
                .position(|(c, h)| c != h)
                .unwrap();
            let cell = bad / FORM_WORDS;
            eprintln!(
                "  own_cells {}: standing DIVERGES at cell {} (word {}): card {:?} host {:?}",
                own_cells,
                cell,
                bad % FORM_WORDS,
                RegionalForm::unpack(&card_standing, cell * FORM_WORDS),
                RegionalForm::unpack(&host_standing, cell * FORM_WORDS),
            );
        }
        eprintln!(
            "  own_cells {}: FAILED (standing {} · touched {} · reads {} · owns {})",
            own_cells,
            yn(standing_ok),
            yn(touched_ok),
            yn(reads_ok),
            yn(owns_ok)
        );
        Ok(false)
    }
}

fn yn(b: bool) -> &'static str {
    if b {
        "ok"
    } else {
        "BAD"
    }
}

fn run() -> Result<()> {
    let t_all = Instant::now();

    mount::cuda::init()?;
    let count = mount::Device::count()?;
    if count < 1 {
        eprintln!("FAILED: no CUDA device visible (cuDeviceGetCount == 0)");
        std::process::exit(1);
    }
    let mut chosen: Option<mount::Device> = None;
    for ord in 0..count {
        let dev = mount::Device::get(ord)?;
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
    let ctx = Context::create(&device)?;

    let ptx_head = String::from_utf8_lossy(PTX)
        .lines()
        .find(|l| l.trim_start().starts_with(".target"))
        .unwrap_or("<no .target>")
        .trim()
        .to_string();
    println!("ptx:    {} ({} bytes)", ptx_head, PTX.len());
    let module = Module::load_ptx(PTX)?;
    let grain = module.function("link_founded_grain")?;
    let sum = module.function("link_founded_sum")?;
    let finish = module.function("link_finish")?;
    println!(
        "staged: standing axis {} ({} places) · founded OWN reservation · block {}",
        STANDING_AXIS, STANDING_CELLS, BLOCK
    );

    let mut all_ok = true;
    for own_cells in OWN_COUNTS {
        all_ok &= founded_case(&ctx, &grain, &sum, &finish, own_cells)?;
    }

    println!("total:  {} us", t_all.elapsed().as_micros());
    if all_ok {
        println!("mount founded gate: EXACT");
        Ok(())
    } else {
        println!("mount founded gate: FAILED");
        std::process::exit(1);
    }
}

fn main() {
    if let Err(e) = run() {
        eprintln!("FAILED: {}", e); // the driver's own error name + description (e.g. an Xid), then stop
        std::process::exit(2);
    }
}

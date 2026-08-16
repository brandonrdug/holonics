//! mount-chart-gate — the §XXXII-b rung of the CUDA/PTX mount recut. It gates the CUDA port of the
//! CHART family (`chart_mark` · `chart_count` · `chart_recast`) BYTE-EXACT against cpu references,
//! on the headless RTX 4080 SUPER.
//!
//!   chart_mark   — every live founded OWN cell casts its grip into the candidate receiving gauge
//!                  (`place::ground`, presence only, atomic max). Assert the mark plane exact.
//!   chart_count  — one thread stands at each distinct arriving grip; a grip already occupied by
//!                  zero-extended standing is residence and contributes nothing, every genuinely new
//!                  grip performs one register increment and reads its own transition for the hand
//!                  carry. Assert the register `[occupancy, carried]` exact.
//!   chart_recast — each occupied old grip zero-extends its unchanged form into the widened chart
//!                  (`chart::zero_extend_grip`). Assert the new standing plane exact.
//!
//! Each is swept across five representative sizes — 0, 1, 64 (one workgroup), 100 (a non-multiple of
//! 64), and a multi-block extent — so every dispatch-boundary and guard path is exercised; chart_count
//! adds one seeded case that forces a hand carry so the carried branch is covered. Byte-exactness is
//! the gate; nothing is scored. The cpu references read the SAME staged buffers the card binds, so
//! only the port can diverge. On any driver fault the exact CUresult name prints and the gate stops.

use std::ffi::c_void;
use std::time::Instant;

use body::chart::{carried_into_hand, zero_extend_grip, zero_extended_source};
use body::manifold::{
    cog_packed_word, own_cell_position, COG_WORDS, OWN_CELL_FORM, OWN_CELL_LIVE, OWN_CELL_POSITION,
    OWN_CELL_WORDS,
};
use body::medium::{RegionalForm, FORM_WORDS};
use body::num::{Cog, Rung};
use body::place::{self, Place};
use mount::{Context, DeviceBuffer, Dim3, Function, Module, Result};

const PTX: &[u8] = include_bytes!("../../soma-kernel-cuda/soma_kernel_cuda.ptx");

const BLOCK: u32 = 64; // mirrors the SPIR-V `threads(64)`

/// The five representative active-item counts each sub-gate sweeps.
const MARK_OWN_COUNTS: [usize; 5] = [0, 1, 64, 100, 5000];
const COUNT_GRIPS: [usize; 5] = [0, 1, 64, 100, 4096];
const RECAST_GRIPS: [usize; 5] = [0, 1, 64, 100, 1024];

fn arg(v: &mut u64) -> *mut c_void {
    v as *mut u64 as *mut c_void
}

/// Grid over `items` linear work-items (block 64). `work_x` is capped so the 2-D `id.y` flatten is
/// exercised at the larger sizes; `items == 0` still yields a one-block grid whose guards all fire.
fn grid_1d(items: u64) -> (Dim3, u32) {
    let groups = items.div_ceil(BLOCK as u64).max(1);
    let work_x = groups.min(16).max(1) as u32;
    let y = groups.div_ceil(work_x as u64) as u32;
    (Dim3 { x: work_x, y, z: 1 }, work_x * BLOCK)
}

fn own_position(i: usize) -> Place {
    let a = ((i as u64).wrapping_mul(2654435761) & 0xffff) as i64 + 1;
    let b = ((i as u64).wrapping_mul(40503).wrapping_add(12345) & 0xffff) as i64 + 1;
    (Cog::lit(a), Cog::lit(b))
}

fn own_form(i: usize) -> RegionalForm {
    let base = (i % 1000 + 1) as i64;
    let same = Cog::lit(base << (i % 7));
    let this_way = if i % 2 == 0 {
        Rung::of(((i % 200) + 1) as i32)
    } else {
        Rung::ZERO
    };
    RegionalForm::from_components(same, Cog::lit(0), this_way, Rung::ZERO).occupy()
}

fn pack_founded_cell(owns: &mut [u32], at: usize, live: bool, position: Place, form: RegionalForm) {
    owns[at + OWN_CELL_LIVE] = live as u32;
    for w in 0..COG_WORDS {
        owns[at + OWN_CELL_POSITION + w] = cog_packed_word(position.0, w);
        owns[at + OWN_CELL_POSITION + COG_WORDS + w] = cog_packed_word(position.1, w);
    }
    form.pack(owns, at + OWN_CELL_FORM);
}

/// An occupied old-gauge standing form (a deterministic third of the chart occupied).
fn standing_form(cell: usize) -> RegionalForm {
    if cell % 3 == 0 {
        let v = (cell % 400 + 1) as i64;
        RegionalForm::from_components(Cog::lit(v), Cog::lit(0), Rung::of(1), Rung::ZERO).occupy()
    } else {
        RegionalForm::UNBORN
    }
}

// --- chart_mark ----------------------------------------------------------------------------------
fn mark_case(ctx: &Context, mark: &Function, mark_axis: usize, own_cells: usize) -> Result<bool> {
    let marks_len = mark_axis * mark_axis;
    let mut owns = vec![0u32; own_cells * OWN_CELL_WORDS];
    for i in 0..own_cells {
        let live = i % 9 != 0;
        pack_founded_cell(
            &mut owns,
            i * OWN_CELL_WORDS,
            live,
            own_position(i),
            own_form(i),
        );
    }
    // cpu reference: read the SAME reservation, ground each live cell, mark its grip.
    let mut expected = vec![0u32; marks_len];
    for i in 0..own_cells {
        let at = i * OWN_CELL_WORDS;
        if owns[at + OWN_CELL_LIVE] == 0 {
            continue;
        }
        let grip = place::ground(own_cell_position(&owns, at), mark_axis as i64) as usize;
        if grip < marks_len {
            expected[grip] = 1;
        }
    }

    let owns_len = (own_cells * OWN_CELL_WORDS).max(1);
    let owns_b: DeviceBuffer<u32> = DeviceBuffer::alloc(owns_len)?;
    let mut up = owns.clone();
    up.resize(owns_len, 0);
    owns_b.copy_from_slice(&up)?;
    let marks_b: DeviceBuffer<u32> = DeviceBuffer::alloc_zeroed(marks_len)?;

    let (grid, xstride) = grid_1d(own_cells as u64);
    let params: [u32; 3] = [own_cells as u32, mark_axis as u32, xstride];
    let params_b: DeviceBuffer<u32> = DeviceBuffer::alloc(3)?;
    params_b.copy_from_slice(&params)?;

    let (mut p_ow, mut l_ow) = (owns_b.device_ptr(), owns_len as u64);
    let (mut p_mk, mut l_mk) = (marks_b.device_ptr(), marks_len as u64);
    let (mut p_pr, mut l_pr) = (params_b.device_ptr(), 3u64);

    let t = Instant::now();
    let mut a: [*mut c_void; 6] = [
        arg(&mut p_ow),
        arg(&mut l_ow),
        arg(&mut p_mk),
        arg(&mut l_mk),
        arg(&mut p_pr),
        arg(&mut l_pr),
    ];
    mark.launch(grid, Dim3::x(BLOCK), &mut a)?;
    ctx.synchronize()?;
    let us = t.elapsed().as_micros();

    let mut card = vec![0u32; marks_len];
    marks_b.copy_to_slice(&mut card)?;
    let ok = card == expected;
    println!(
        "  chart_mark  own_cells {:>5}: {}  ({} grips marked · {} us)",
        own_cells,
        if ok { "EXACT" } else { "FAILED" },
        expected.iter().sum::<u32>(),
        us
    );
    if !ok {
        let bad = card
            .iter()
            .zip(expected.iter())
            .position(|(c, h)| c != h)
            .unwrap();
        eprintln!(
            "    marks DIVERGE at grip {}: card {} cpu {}",
            bad, card[bad], expected[bad]
        );
    }
    Ok(ok)
}

// --- chart_count ---------------------------------------------------------------------------------
fn count_case(
    ctx: &Context,
    count: &Function,
    old_axis: usize,
    new_axis: usize,
    grip_count: usize,
    seed: u64,
) -> Result<bool> {
    let old_cells = old_axis * old_axis;
    let marks_len = new_axis * new_axis;
    let mut standing = vec![0u32; old_cells * FORM_WORDS];
    for cell in 0..old_cells {
        standing_form(cell).pack(&mut standing, cell * FORM_WORDS);
    }
    // marks: a deterministic set of cast arrivals in the new gauge.
    let mut marks = vec![0u32; marks_len];
    for (g, m) in marks.iter_mut().enumerate() {
        *m = (g % 2 == 0) as u32;
    }

    // cpu reference: replay the register over the new grips in [0, grip_count), skipping residence.
    let mut occ = seed;
    let mut carried = 0u64;
    for grip in 0..grip_count.min(marks_len) {
        if marks[grip] == 0 {
            continue;
        }
        let residence = zero_extended_source(grip as u32, old_axis as u32, new_axis as u32)
            .map(|old_grip| {
                RegionalForm::unpack(&standing, old_grip as usize * FORM_WORDS).occupied()
            })
            .unwrap_or(false);
        if residence {
            continue;
        }
        let before = occ;
        occ = occ.wrapping_add(1);
        if carried_into_hand(before, occ, new_axis as u32) {
            carried = 1;
        }
    }
    let expected = [occ, carried];

    let standing_b: DeviceBuffer<u32> = DeviceBuffer::alloc(old_cells * FORM_WORDS)?;
    standing_b.copy_from_slice(&standing)?;
    let marks_b: DeviceBuffer<u32> = DeviceBuffer::alloc(marks_len)?;
    marks_b.copy_from_slice(&marks)?;
    let reg_b: DeviceBuffer<u64> = DeviceBuffer::alloc(2)?;
    reg_b.copy_from_slice(&[seed, 0])?;

    let (grid, xstride) = grid_1d(grip_count as u64);
    let params: [u32; 4] = [old_axis as u32, new_axis as u32, grip_count as u32, xstride];
    let params_b: DeviceBuffer<u32> = DeviceBuffer::alloc(4)?;
    params_b.copy_from_slice(&params)?;

    let (mut p_st, mut l_st) = (standing_b.device_ptr(), (old_cells * FORM_WORDS) as u64);
    let (mut p_mk, mut l_mk) = (marks_b.device_ptr(), marks_len as u64);
    let (mut p_rg, mut l_rg) = (reg_b.device_ptr(), 2u64);
    let (mut p_pr, mut l_pr) = (params_b.device_ptr(), 4u64);

    let t = Instant::now();
    let mut a: [*mut c_void; 8] = [
        arg(&mut p_st),
        arg(&mut l_st),
        arg(&mut p_mk),
        arg(&mut l_mk),
        arg(&mut p_rg),
        arg(&mut l_rg),
        arg(&mut p_pr),
        arg(&mut l_pr),
    ];
    count.launch(grid, Dim3::x(BLOCK), &mut a)?;
    ctx.synchronize()?;
    let us = t.elapsed().as_micros();

    let mut card = [0u64; 2];
    reg_b.copy_to_slice(&mut card)?;
    let ok = card == expected;
    println!(
        "  chart_count grips {:>5} seed {:>4}: {}  (register card {:?} cpu {:?} · {} us)",
        grip_count,
        seed,
        if ok { "EXACT" } else { "FAILED" },
        card,
        expected,
        us
    );
    Ok(ok)
}

// --- chart_recast --------------------------------------------------------------------------------
fn recast_case(
    ctx: &Context,
    recast: &Function,
    old_axis: usize,
    new_axis: usize,
    grip_count: usize,
) -> Result<bool> {
    let old_cells = old_axis * old_axis;
    let new_cells = new_axis * new_axis;
    let mut old_standing = vec![0u32; old_cells * FORM_WORDS];
    for cell in 0..old_cells {
        standing_form(cell).pack(&mut old_standing, cell * FORM_WORDS);
    }
    // cpu reference: each occupied old grip in [0, grip_count) zero-extends its unchanged form.
    let mut expected = vec![0u32; new_cells * FORM_WORDS];
    for old_grip in 0..grip_count.min(old_cells) {
        let form = RegionalForm::unpack(&old_standing, old_grip * FORM_WORDS);
        if !form.occupied() {
            continue;
        }
        let new_grip = zero_extend_grip(old_grip as u32, old_axis as u32, new_axis as u32) as usize;
        form.pack(&mut expected, new_grip * FORM_WORDS);
    }

    let old_b: DeviceBuffer<u32> = DeviceBuffer::alloc(old_cells * FORM_WORDS)?;
    old_b.copy_from_slice(&old_standing)?;
    let new_b: DeviceBuffer<u32> = DeviceBuffer::alloc_zeroed(new_cells * FORM_WORDS)?;

    let (grid, xstride) = grid_1d(grip_count as u64);
    let params: [u32; 4] = [old_axis as u32, new_axis as u32, grip_count as u32, xstride];
    let params_b: DeviceBuffer<u32> = DeviceBuffer::alloc(4)?;
    params_b.copy_from_slice(&params)?;

    let (mut p_o, mut l_o) = (old_b.device_ptr(), (old_cells * FORM_WORDS) as u64);
    let (mut p_n, mut l_n) = (new_b.device_ptr(), (new_cells * FORM_WORDS) as u64);
    let (mut p_pr, mut l_pr) = (params_b.device_ptr(), 4u64);

    let t = Instant::now();
    let mut a: [*mut c_void; 6] = [
        arg(&mut p_o),
        arg(&mut l_o),
        arg(&mut p_n),
        arg(&mut l_n),
        arg(&mut p_pr),
        arg(&mut l_pr),
    ];
    recast.launch(grid, Dim3::x(BLOCK), &mut a)?;
    ctx.synchronize()?;
    let us = t.elapsed().as_micros();

    let mut card = vec![0u32; new_cells * FORM_WORDS];
    new_b.copy_to_slice(&mut card)?;
    let ok = card == expected;
    let recast_count = (0..grip_count.min(old_cells))
        .filter(|&g| RegionalForm::unpack(&old_standing, g * FORM_WORDS).occupied())
        .count();
    println!(
        "  chart_recast grips {:>5}: {}  ({} forms zero-extended · {} us)",
        grip_count,
        if ok { "EXACT" } else { "FAILED" },
        recast_count,
        us
    );
    if !ok {
        let bad = card
            .iter()
            .zip(expected.iter())
            .position(|(c, h)| c != h)
            .unwrap();
        eprintln!(
            "    new standing DIVERGES at cell {} (word {})",
            bad / FORM_WORDS,
            bad % FORM_WORDS
        );
    }
    Ok(ok)
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
    let mark = module.function("chart_mark")?;
    let count_fn = module.function("chart_count")?;
    let recast = module.function("chart_recast")?;

    let mut all_ok = true;

    println!("chart_mark  (cast into the candidate gauge; mark axis 64 → 4,096 grips):");
    for own_cells in MARK_OWN_COUNTS {
        all_ok &= mark_case(&ctx, &mark, 64, own_cells)?;
    }

    println!(
        "chart_count (occupancy register OWN carry; old axis 32 → new axis 64; hand = 2,048):"
    );
    for grips in COUNT_GRIPS {
        all_ok &= count_case(&ctx, &count_fn, 32, 64, grips, 0)?;
    }
    // one seeded case that forces the register across the hand (2,048), covering the carried branch.
    all_ok &= count_case(&ctx, &count_fn, 32, 64, 4096, 2040)?;

    println!("chart_recast (zero-extend into the widened chart; old axis 32 → new axis 64):");
    for grips in RECAST_GRIPS {
        all_ok &= recast_case(&ctx, &recast, 32, 64, grips)?;
    }

    println!("total:  {} us", t_all.elapsed().as_micros());
    if all_ok {
        println!("mount chart gate: EXACT");
        Ok(())
    } else {
        println!("mount chart gate: FAILED");
        std::process::exit(1);
    }
}

fn main() {
    if let Err(e) = run() {
        eprintln!("FAILED: {}", e); // the driver's own error name + description (e.g. an Xid), then stop
        std::process::exit(2);
    }
}

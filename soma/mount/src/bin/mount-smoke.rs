//! mount-smoke — proves the full CUDA mount path ONCE, end to end, with exact asserts only.
//!
//!   init -> pick the RTX 4080 SUPER -> load the Rust-emitted PTX -> alloc -> memcpy ->
//!   launch (fill_identity, then atomic_fold) -> synchronize -> readback -> exact assert.
//!
//! Nothing is scored. Each gate prints EXACT or FAILED. No floats in the kernel; cpu timing
//! prints are integer microseconds. On any driver fault the exact CUresult name is printed and
//! the smoke stops — no retry loop.

use std::ffi::c_void;
use std::time::Instant;

use mount::{Context, Device, DeviceBuffer, Dim3, Module, FOLD_CONSTANT};

/// The PTX payload, built by mount-smoke-kernel/build-ptx.sh and committed as the boundary
/// artifact (exactly as kernel/soma.spv is the Vulkan boundary). The workspace compiles without
/// the nvptx target present because this file already exists on disk.
const PTX: &[u8] = include_bytes!("../../mount-smoke-kernel/mount_smoke_kernel.ptx");

const IDENTITY_N: usize = 1 << 20; // 1,048,576 u32 cells
const IDENTITY_BLOCK: u32 = 256;
const IDENTITY_GRID: u32 = (IDENTITY_N as u32) / IDENTITY_BLOCK; // 4096

const FOLD_COUNT: usize = 1 << 16; // 65,536 threads
const FOLD_BLOCK: u32 = 256;
const FOLD_GRID: u32 = (FOLD_COUNT as u32) / FOLD_BLOCK; // 256

/// The `.version` line from the PTX artifact, for the report.
fn ptx_version_line(ptx: &[u8]) -> String {
    let text = String::from_utf8_lossy(ptx);
    for line in text.lines() {
        let t = line.trim();
        if t.starts_with(".version") || t.starts_with(".target") {
            return t.to_string();
        }
    }
    String::from("<no .version line>")
}

fn run() -> mount::Result<()> {
    let t_all = Instant::now();

    // --- init + device selection -------------------------------------------------------------
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

    // --- load the Rust-emitted PTX -----------------------------------------------------------
    println!("ptx:    {} ({} bytes)", ptx_version_line(PTX), PTX.len());
    let t_load = Instant::now();
    let module = Module::load_ptx(PTX)?;
    let load_us = t_load.elapsed().as_micros();
    let fill = module.function("fill_identity")?;
    let fold = module.function("atomic_fold")?;
    println!(
        "load:   {} us (cuModuleLoadData + 2 cuModuleGetFunction)",
        load_us
    );

    // --- gate 1: fill_identity ---------------------------------------------------------------
    let out: DeviceBuffer<u32> = DeviceBuffer::alloc(IDENTITY_N)?;
    let t_fill = Instant::now();
    {
        let mut dptr = out.device_ptr();
        let mut params: [*mut c_void; 1] = [&mut dptr as *mut _ as *mut c_void];
        fill.launch(Dim3::x(IDENTITY_GRID), Dim3::x(IDENTITY_BLOCK), &mut params)?;
        _ctx.synchronize()?;
    }
    let fill_us = t_fill.elapsed().as_micros();
    let mut cpu = vec![0u32; IDENTITY_N];
    out.copy_to_slice(&mut cpu)?;

    let mut first_bad: Option<(usize, u32)> = None;
    for (i, &v) in cpu.iter().enumerate() {
        if v != i as u32 {
            first_bad = Some((i, v));
            break;
        }
    }
    match first_bad {
        None => println!(
            "GATE fill_identity: EXACT  (out[i]==i for all {} cells; grid {}x{}; {} us)",
            IDENTITY_N, IDENTITY_GRID, IDENTITY_BLOCK, fill_us
        ),
        Some((i, v)) => {
            println!(
                "GATE fill_identity: FAILED (out[{}]=={} expected {})",
                i, v, i
            );
            std::process::exit(1);
        }
    }

    // --- gate 2: atomic_fold -----------------------------------------------------------------
    // Each thread adds FOLD_CONSTANT once and maxes its index once. The exact device add is the
    // 64-bit-wrapped product (atomics wrap mod 2^64, deterministically), so the cpu check uses
    // the same wrapping product — exactness, not approximation.
    let add_buf: DeviceBuffer<u64> = DeviceBuffer::alloc_zeroed(1)?;
    let max_buf: DeviceBuffer<u64> = DeviceBuffer::alloc_zeroed(1)?;
    let t_fold = Instant::now();
    {
        let mut a = add_buf.device_ptr();
        let mut m = max_buf.device_ptr();
        let mut params: [*mut c_void; 2] = [
            &mut a as *mut _ as *mut c_void,
            &mut m as *mut _ as *mut c_void,
        ];
        fold.launch(Dim3::x(FOLD_GRID), Dim3::x(FOLD_BLOCK), &mut params)?;
        _ctx.synchronize()?;
    }
    let fold_us = t_fold.elapsed().as_micros();

    let mut add_out = [0u64; 1];
    let mut max_out = [0u64; 1];
    add_buf.copy_to_slice(&mut add_out)?;
    max_buf.copy_to_slice(&mut max_out)?;

    let expected_add = (FOLD_COUNT as u64).wrapping_mul(FOLD_CONSTANT);
    let expected_max = (FOLD_COUNT - 1) as u64;
    let add_ok = add_out[0] == expected_add;
    let max_ok = max_out[0] == expected_max;
    if add_ok && max_ok {
        println!(
            "GATE atomic_fold:   EXACT  (add=={} == {}*{} mod 2^64; max=={} == count-1; {} threads; {} us)",
            add_out[0], FOLD_COUNT, FOLD_CONSTANT, max_out[0], FOLD_COUNT, fold_us
        );
    } else {
        println!(
            "GATE atomic_fold:   FAILED (add={} exp {} [{}]; max={} exp {} [{}])",
            add_out[0],
            expected_add,
            if add_ok { "ok" } else { "BAD" },
            max_out[0],
            expected_max,
            if max_ok { "ok" } else { "BAD" }
        );
        std::process::exit(1);
    }

    println!("total:  {} us", t_all.elapsed().as_micros());
    println!("mount smoke: EXACT");
    Ok(())
}

fn main() {
    if let Err(e) = run() {
        // The driver's own error name + description, then stop. No retry loop.
        eprintln!("FAILED: {}", e);
        std::process::exit(2);
    }
}

//! Compile the engine's two exact CUDA laws to PTX.
//!
//! **The virtual architecture is read off the device present at build time, not authored.** This
//! script pinned `--gpu-architecture=compute_75` — Turing — until 2026-08-10, while the machine it
//! builds on is Ada. `nvidia-smi --query-gpu=compute_cap` is the device stating its own capability,
//! exactly as `soma/mount`'s `Device::attribute` does at run time. When no device answers, the
//! floor `compute_75` is used and **said aloud** through `cargo:warning`, because a build that
//! silently targets a generation nobody has is how the pin survived.

use std::env;
use std::path::PathBuf;
use std::process::Command;

/// The oldest architecture these two kernels are known to assemble for. Used only when no device
/// answers, and reported when it is.
const UNATTENDED_FLOOR: &str = "compute_75";

/// Ask the mounted device what it is. `nvidia-smi` reports `8.9`; `nvcc` wants `compute_89`.
fn declared_architecture() -> String {
    let answered = Command::new("nvidia-smi")
        .args(["--query-gpu=compute_cap", "--format=csv,noheader"])
        .output()
        .ok()
        .filter(|output| output.status.success())
        .and_then(|output| {
            String::from_utf8(output.stdout)
                .ok()?
                .lines()
                .next()?
                .trim()
                .split('.')
                .map(str::to_owned)
                .collect::<Vec<_>>()
                .into_iter()
                .reduce(|major, minor| format!("{major}{minor}"))
        })
        .filter(|digits| !digits.is_empty() && digits.chars().all(|c| c.is_ascii_digit()));
    match answered {
        Some(digits) => format!("compute_{digits}"),
        None => {
            println!(
                "cargo:warning=no CUDA device answered `nvidia-smi --query-gpu=compute_cap`; \
                 building the exact CUDA laws for the floor {UNATTENDED_FLOOR}. The PTX will be \
                 re-JIT-ed by the driver on any newer device."
            );
            UNATTENDED_FLOOR.to_owned()
        }
    }
}

fn main() {
    println!("cargo:rerun-if-changed=kernels/exact_conic_support.cu");
    println!("cargo:rerun-if-changed=kernels/exact_relation_support.cu");
    println!("cargo:rerun-if-changed=kernels/refine_shell.cu");
    if env::var("CARGO_CFG_TARGET_OS").as_deref() != Ok("linux") {
        return;
    }
    let architecture = declared_architecture();
    let gpu_architecture = format!("--gpu-architecture={architecture}");
    println!("cargo:warning=exact CUDA laws built for {architecture}");
    let output = PathBuf::from(env::var_os("OUT_DIR").expect("Cargo supplies OUT_DIR"))
        .join("exact_conic_support.ptx");
    let status = Command::new("nvcc")
        .args([
            "--ptx",
            "-O3",
            // GCC 16 headers require the dialect explicitly; nvcc's default
            // predates char8_t and the requires-expression parse used in
            // <type_traits>. The C++ body set this on the first line of its
            // CMakeLists and this build script never passed it.
            "--std=c++20",
            &gpu_architecture,
            "kernels/exact_conic_support.cu",
            "-o",
        ])
        .arg(&output)
        .status()
        .expect("nvcc is required to compile the exact CUDA compute law");
    assert!(
        status.success(),
        "nvcc refused kernels/exact_conic_support.cu"
    );

    let relation_output = PathBuf::from(env::var_os("OUT_DIR").expect("Cargo supplies OUT_DIR"))
        .join("exact_relation_support.ptx");
    let relation_status = Command::new("nvcc")
        .args([
            "--ptx",
            "-O3",
            // GCC 16 headers require the dialect explicitly; nvcc's default
            // predates char8_t and the requires-expression parse used in
            // <type_traits>. The C++ body set this on the first line of its
            // CMakeLists and this build script never passed it.
            "--std=c++20",
            &gpu_architecture,
            "kernels/exact_relation_support.cu",
            "-o",
        ])
        .arg(&relation_output)
        .status()
        .expect("nvcc is required to compile the exact CUDA relation law");
    assert!(
        relation_status.success(),
        "nvcc refused kernels/exact_relation_support.cu"
    );

    let refine_output = PathBuf::from(env::var_os("OUT_DIR").expect("Cargo supplies OUT_DIR"))
        .join("refine_shell.ptx");
    let refine_status = Command::new("nvcc")
        .args([
            "--ptx",
            "-O3",
            "--std=c++20",
            &gpu_architecture,
            "kernels/refine_shell.cu",
            "-o",
        ])
        .arg(&refine_output)
        .status()
        .expect("nvcc is required to compile the partition refinement law");
    assert!(refine_status.success(), "nvcc refused kernels/refine_shell.cu");
}

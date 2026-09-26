//! Compile the resident HNN's kernels (`kernels/hnn.cu`, with `kernels/exact_integer.cuh`) to PTX
//! with `nvcc`, for the existing driver to load (`Module::load_ptx`; the driver lowers the PTX for
//! the mounted card).
//!
//! Ported from `13f8c734:crates/holonics-cuda/build.rs`, cut to one translation unit. Two of its
//! laws are kept:
//! - **The virtual architecture is read off the device present at build time, not authored.**
//!   `nvidia-smi --query-gpu=compute_cap` is the device stating its own capability. When no device
//!   answers, the floor `compute_75` is used and said aloud through `cargo:warning`.
//! - **The dialect is explicit** (`--std=c++20`): current GCC headers require it, and C++20 makes
//!   the signed reading of an unsigned ring word modular, which `exact_integer.cuh` relies on.
//!
//! [definition; agent-inferred] **`nvcc` is located, not assumed on `PATH`**: `$NVCC`, then
//! `$CUDA_PATH/bin`, `$CUDA_HOME/bin`, `PATH`, `/opt/cuda/bin` and `/usr/local/cuda/bin`. When none
//! answers, the build still succeeds (the host library builds without a CUDA toolchain) and says
//! so: the image is empty and `HOLONICS_CUDA_KERNELS` names the absence, so opening a card refuses
//! with that reason rather than failing to link or loading nothing silently.

use std::env;
use std::path::{Path, PathBuf};
use std::process::Command;

/// The oldest architecture the kernels are built for when no device answers; the driver JIT
/// lowers its PTX for any newer card.
const UNATTENDED_FLOOR: &str = "compute_75";

const SOURCES: [&str; 3] = [
    "kernels/hnn.cu",
    "kernels/exact_integer.cuh",
    "kernels/hnn_word.cuh",
];

/// Ask the mounted device what it is: `nvidia-smi` reports `8.9`, `nvcc` wants `compute_89`.
fn declared_architecture() -> String {
    let answered = Command::new("nvidia-smi")
        .args(["--query-gpu=compute_cap", "--format=csv,noheader"])
        .output()
        .ok()
        .filter(|output| output.status.success())
        .and_then(|output| {
            let text = String::from_utf8(output.stdout).ok()?;
            let line = text.lines().next()?.trim().to_owned();
            let digits: String = line.chars().filter(|c| *c != '.').collect();
            (!digits.is_empty() && digits.chars().all(|c| c.is_ascii_digit())).then_some(digits)
        });
    match answered {
        Some(digits) => format!("compute_{digits}"),
        None => {
            println!(
                "cargo:warning=no CUDA device answered `nvidia-smi --query-gpu=compute_cap`; \
                 building the HNN kernels for the floor {UNATTENDED_FLOOR}"
            );
            UNATTENDED_FLOOR.to_owned()
        }
    }
}

fn executable(path: &Path) -> Option<PathBuf> {
    path.is_file().then(|| path.to_path_buf())
}

/// Locate `nvcc`.
fn nvcc() -> Option<PathBuf> {
    if let Some(explicit) = env::var_os("NVCC") {
        return executable(Path::new(&explicit));
    }
    for root in ["CUDA_PATH", "CUDA_HOME"] {
        if let Some(found) = env::var_os(root)
            .and_then(|root| executable(&Path::new(&root).join("bin").join("nvcc")))
        {
            return Some(found);
        }
    }
    if let Some(found) = env::var_os("PATH").and_then(|path| {
        env::split_paths(&path).find_map(|directory| executable(&directory.join("nvcc")))
    }) {
        return Some(found);
    }
    ["/opt/cuda/bin/nvcc", "/usr/local/cuda/bin/nvcc"]
        .iter()
        .find_map(|candidate| executable(Path::new(candidate)))
}

fn main() {
    for source in SOURCES {
        println!("cargo:rerun-if-changed={source}");
    }
    // The notebook's exposure command (`research/notebook/hnn_design/hnn_exposure.rs`) is an
    // example of both crates; built here it may run its exposure on the card (`realization card`).
    println!("cargo:rustc-check-cfg=cfg(holonics_card)");
    println!("cargo:rustc-cfg=holonics_card");
    for variable in ["NVCC", "CUDA_PATH", "CUDA_HOME"] {
        println!("cargo:rerun-if-env-changed={variable}");
    }
    let output =
        PathBuf::from(env::var_os("OUT_DIR").expect("Cargo supplies OUT_DIR")).join("hnn.ptx");
    let absent = |reason: &str| {
        std::fs::write(&output, b"").expect("OUT_DIR is writable");
        println!("cargo:warning=the HNN kernels are not built: {reason}");
        println!("cargo:rustc-env=HOLONICS_CUDA_KERNELS=absent: {reason}");
    };
    if env::var("CARGO_CFG_TARGET_OS").as_deref() != Ok("linux") {
        absent("the CUDA backend builds its kernels on Linux only");
        return;
    }
    let Some(nvcc) = nvcc() else {
        absent(
            "no nvcc at $NVCC, $CUDA_PATH/bin, $CUDA_HOME/bin, PATH, /opt/cuda/bin or /usr/local/cuda/bin",
        );
        return;
    };
    let architecture = declared_architecture();
    let status = Command::new(&nvcc)
        .args([
            "--ptx",
            "-O3",
            "--std=c++20",
            &format!("--gpu-architecture={architecture}"),
            "kernels/hnn.cu",
            "-o",
        ])
        .arg(&output)
        .status()
        .unwrap_or_else(|error| panic!("{} could not run: {error}", nvcc.display()));
    assert!(status.success(), "nvcc refused kernels/hnn.cu");
    println!("cargo:rustc-env=HOLONICS_CUDA_KERNELS={architecture}");
}

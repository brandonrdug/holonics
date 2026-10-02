//! Compile the resident HNN's kernels (`kernels/hnn.cu`, with `kernels/exact_integer.cuh`) to PTX
//! with `nvcc`, for the existing driver to load (`Module::load_ptx`; the driver lowers the PTX for
//! the mounted card); and the landmark tree's kernels (`kernels/tree.cu`, campaign 2) as their own
//! image, `tree.ptx`, which `src/hnn/tree.rs` loads.
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
//!
//! [definition; agent-inferred, October 2] **The image is addressed by its sources' content, not
//! their modification times.** Cargo reruns a build script when a watched file's time passes the
//! script's last run, so a target directory seeded by copying (newer times than the checked-out
//! kernels) kept an older build's kernels and ran them against newer host code (the U6 PC runner's
//! gate 3 of October 2). The script now reruns on every build (it watches a path that never exists
//! in `OUT_DIR`), hashes the kernel sources, this script (which carries `nvcc`'s arguments), the
//! architecture, and `nvcc`'s path and `--version` output with SHA-256, and calls `nvcc` only when
//! that digest differs from the one stamped beside the images; the digest enters the crate as
//! `HOLONICS_CUDA_KERNEL_SOURCES`, so a changed image recompiles the crate.

use std::env;
use std::path::{Path, PathBuf};
use std::process::Command;

/// The oldest architecture the kernels are built for when no device answers; the driver JIT
/// lowers its PTX for any newer card.
const UNATTENDED_FLOOR: &str = "compute_75";

const SOURCES: [&str; 4] = [
    "kernels/hnn.cu",
    "kernels/exact_integer.cuh",
    "kernels/hnn_word.cuh",
    "kernels/tree.cu",
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

/// SHA-256 (FIPS 180-4) of a byte string, as 64 lowercase hex digits.
fn sha256(data: &[u8]) -> String {
    const K: [u32; 64] = [
        0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
        0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
        0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
        0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
        0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
        0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
        0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
        0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2,
    ];
    let mut h: [u32; 8] = [
        0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19,
    ];
    let mut message = data.to_vec();
    let bits = (data.len() as u64).wrapping_mul(8);
    message.push(0x80);
    while message.len() % 64 != 56 {
        message.push(0);
    }
    message.extend_from_slice(&bits.to_be_bytes());
    for block in message.chunks(64) {
        let mut w = [0u32; 64];
        for (i, word) in block.chunks(4).enumerate() {
            w[i] = u32::from_be_bytes([word[0], word[1], word[2], word[3]]);
        }
        for i in 16..64 {
            let s0 = w[i - 15].rotate_right(7) ^ w[i - 15].rotate_right(18) ^ (w[i - 15] >> 3);
            let s1 = w[i - 2].rotate_right(17) ^ w[i - 2].rotate_right(19) ^ (w[i - 2] >> 10);
            w[i] = w[i - 16].wrapping_add(s0).wrapping_add(w[i - 7]).wrapping_add(s1);
        }
        let [mut a, mut b, mut c, mut d, mut e, mut f, mut g, mut hh] = h;
        for i in 0..64 {
            let s1 = e.rotate_right(6) ^ e.rotate_right(11) ^ e.rotate_right(25);
            let choice = (e & f) ^ (!e & g);
            let t1 = hh.wrapping_add(s1).wrapping_add(choice).wrapping_add(K[i]).wrapping_add(w[i]);
            let s0 = a.rotate_right(2) ^ a.rotate_right(13) ^ a.rotate_right(22);
            let majority = (a & b) ^ (a & c) ^ (b & c);
            let t2 = s0.wrapping_add(majority);
            hh = g;
            g = f;
            f = e;
            e = d.wrapping_add(t1);
            d = c;
            c = b;
            b = a;
            a = t1.wrapping_add(t2);
        }
        for (slot, value) in h.iter_mut().zip([a, b, c, d, e, f, g, hh]) {
            *slot = slot.wrapping_add(value);
        }
    }
    h.iter().map(|word| format!("{word:08x}")).collect()
}

fn main() {
    for source in SOURCES {
        println!("cargo:rerun-if-changed={source}");
    }
    // A path that never exists: Cargo then reruns this script on every build, and the content
    // digest below decides whether `nvcc` runs (module header).
    let out_dir = PathBuf::from(env::var_os("OUT_DIR").expect("Cargo supplies OUT_DIR"));
    println!(
        "cargo:rerun-if-changed={}",
        out_dir.join("the-kernels-are-addressed-by-content").display()
    );
    // The notebook's exposure command (`research/notebook/hnn_design/hnn_exposure.rs`) is an
    // example of both crates; built here it may run its exposure on the card (`realization card`).
    println!("cargo:rustc-check-cfg=cfg(holonics_card)");
    println!("cargo:rustc-cfg=holonics_card");
    for variable in ["NVCC", "CUDA_PATH", "CUDA_HOME"] {
        println!("cargo:rerun-if-env-changed={variable}");
    }
    let output =
        PathBuf::from(env::var_os("OUT_DIR").expect("Cargo supplies OUT_DIR")).join("hnn.ptx");
    // The landmark tree's kernels are their own translation unit (`src/hnn/tree.rs` loads them).
    let tree_output =
        PathBuf::from(env::var_os("OUT_DIR").expect("Cargo supplies OUT_DIR")).join("tree.ptx");
    let absent = |reason: &str| {
        let _ = std::fs::remove_file(out_dir.join("kernels.sha256"));
        std::fs::write(&output, b"").expect("OUT_DIR is writable");
        std::fs::write(&tree_output, b"").expect("OUT_DIR is writable");
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
    let mut addressed = Vec::new();
    for source in SOURCES {
        addressed.extend_from_slice(source.as_bytes());
        addressed.push(0);
        addressed.extend(std::fs::read(source).unwrap_or_else(|error| panic!("{source}: {error}")));
        addressed.push(0);
    }
    // This script carries `nvcc`'s arguments, so a change to them changes the address.
    addressed.extend_from_slice(include_bytes!("build.rs"));
    addressed.push(0);
    addressed.extend_from_slice(architecture.as_bytes());
    addressed.push(0);
    addressed.extend_from_slice(nvcc.as_os_str().as_encoded_bytes());
    addressed.push(0);
    // A toolkit upgraded in place keeps its path; its version line tells the two apart.
    if let Ok(version) = Command::new(&nvcc).arg("--version").output() {
        addressed.extend_from_slice(&version.stdout);
    }
    let digest = sha256(&addressed);
    println!("cargo:rustc-env=HOLONICS_CUDA_KERNEL_SOURCES={digest}");
    let stamp = out_dir.join("kernels.sha256");
    let fresh = std::fs::read_to_string(&stamp).is_ok_and(|stamped| stamped.trim() == digest)
        && std::fs::metadata(&output).is_ok_and(|m| m.len() > 0)
        && std::fs::metadata(&tree_output).is_ok_and(|m| m.len() > 0);
    if fresh {
        println!("cargo:rustc-env=HOLONICS_CUDA_KERNELS={architecture}");
        return;
    }
    // A stale or absent image: remove the stamp first, so an interrupted compile is never taken
    // for a fresh one.
    let _ = std::fs::remove_file(&stamp);
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
    let status = Command::new(&nvcc)
        .args([
            "--ptx",
            "-O3",
            "--std=c++20",
            &format!("--gpu-architecture={architecture}"),
            "kernels/tree.cu",
            "-o",
        ])
        .arg(&tree_output)
        .status()
        .unwrap_or_else(|error| panic!("{} could not run: {error}", nvcc.display()));
    assert!(status.success(), "nvcc refused kernels/tree.cu");
    std::fs::write(&stamp, &digest).expect("OUT_DIR is writable");
    println!("cargo:warning=compiled the HNN kernels, sources {digest}");
    println!("cargo:rustc-env=HOLONICS_CUDA_KERNELS={architecture}");
}

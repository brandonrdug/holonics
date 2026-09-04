use std::env;
use std::path::PathBuf;
use std::process::Command;

fn main() {
    println!("cargo:rerun-if-changed=kernels/exact_conic_support.cu");
    println!("cargo:rerun-if-changed=kernels/exact_relation_support.cu");
    if env::var("CARGO_CFG_TARGET_OS").as_deref() != Ok("linux") {
        return;
    }
    let output = PathBuf::from(env::var_os("OUT_DIR").expect("Cargo supplies OUT_DIR"))
        .join("exact_conic_support.ptx");
    let status = Command::new("nvcc")
        .args([
            "--ptx",
            "-O3",
            "--gpu-architecture=compute_75",
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
            "--gpu-architecture=compute_75",
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
}

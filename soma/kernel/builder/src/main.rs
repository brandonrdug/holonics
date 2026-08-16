//! THE LOWERING — compile the soma kernel to SPIR-V (rust-gpu; ONE language, the body's own law shared by
//! `#[path]`). Run from `kernel/builder/` on the pinned nightly (`rust-toolchain.toml`); the emitted module
//! lands at `kernel/soma.spv` — the boundary crossing the cpu `include_bytes!`s.
use spirv_builder::{Capability, SpirvBuilder};

fn main() {
    let out = SpirvBuilder::new("..", "spirv-unknown-vulkan1.2")
        .capability(Capability::Int64) // the u64 construction words (the 64-bit substrate grain)
        .capability(Capability::Int64Atomics) // exact order-free grain/sum composition on the card
        .build()
        .expect("the kernel lowers to SPIR-V");
    let module = out.module.unwrap_single().to_owned();
    std::fs::copy(&module, "../soma.spv").expect("the module crosses to soma.spv");
    println!("soma.spv ← {}", module.display());
}

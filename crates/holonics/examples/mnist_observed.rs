//! Host parity entrypoint for the shared observed MNIST runner.
//! For the CUDA-default entrypoint and explicit `--backend host` parity selector, use
//! `cargo run --release -p holonics-cuda --example mnist_observed -- DATA_DIR ...`.

#[path = "mnist_observed/common.rs"]
mod shared;

use holonics::hnn::Reference;
use std::error::Error;

fn main() -> std::result::Result<(), Box<dyn Error>> {
    let args: Vec<_> = std::env::args().skip(1).collect();
    let port = Reference::new(4, shared::BUDGET);
    println!("execution_backend=host_reference gpu_used=false");
    shared::run(&port, &args, |field, current, material| {
        port.mount_with(field, current, material)
    })
}

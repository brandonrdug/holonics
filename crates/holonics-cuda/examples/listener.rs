//! CUDA exterior for the shared octet-section listener.
//!
//! The host and CUDA commands share the same frame parser, codec, learning/release loop, and
//! reporting path. CUDA is the default; `--backend host` is an explicit parity run and never a
//! fallback. `--reception carry|rest` is forwarded as the same resident opening law.
//!
//! Example:
//! `cargo run --release -p holonics-cuda --example listener -- --route sections --learn TRAIN.hlsn --learn-count 1 --max-release-octets N`

#[path = "../../holonics/examples/listener/octets.rs"]
mod octets;
#[path = "../../holonics/examples/listener/sections.rs"]
mod sections;

use holonics::hnn::{Reference, reference::Reception};
use holonics_cuda::hnn::{Card, Resident as CudaResident};
use std::error::Error;

// [declaration] The inherited execution port declares four pending handles.
// Route grammar, backend/reception labels and exterior diagnostics are run declarations.

type Result<T> = std::result::Result<T, Box<dyn Error>>;

#[derive(Clone, Copy)]
enum Backend {
    Cuda,
    Host,
}

fn arguments() -> Result<(Backend, bool, Vec<String>)> {
    let mut args: Vec<_> = std::env::args().skip(1).collect();
    let mut backend = Backend::Cuda;
    let mut reception_rest = false;
    let mut at = 0;
    while at < args.len() {
        match args[at].as_str() {
            "--backend" => {
                let value = args.get(at + 1).ok_or("--backend needs cuda or host")?;
                backend = match value.as_str() {
                    "cuda" => Backend::Cuda,
                    "host" => Backend::Host,
                    other => {
                        return Err(
                            format!("unknown backend {other:?}; expected cuda or host").into()
                        );
                    }
                };
                args.drain(at..at + 2);
            }
            "--reception" => {
                let value = args.get(at + 1).ok_or("--reception needs carry or rest")?;
                reception_rest = match value.as_str() {
                    "carry" => false,
                    "rest" => true,
                    other => {
                        return Err(
                            format!("unknown reception {other:?}; expected carry or rest").into(),
                        );
                    }
                };
                args.drain(at..at + 2);
            }
            _ => at += 1,
        }
    }
    let route = octets::take_route(&mut args)?;
    if route == "observed" {
        return Err(
            "--route observed is unavailable on the CUDA example until its device fork lands"
                .into(),
        );
    }
    Ok((backend, reception_rest, args))
}

fn run() -> Result<()> {
    let (backend, reception_rest, args) = arguments()?;
    match backend {
        Backend::Host => {
            let port = if reception_rest {
                Reference::new(4, octets::BUDGET).with_reception(Reception::Rest)
            } else {
                Reference::new(4, octets::BUDGET)
            };
            println!("execution_backend=host_reference gpu_used=false explicit_parity_mode=true");
            octets::run(
                &port,
                &args,
                |field, current, material| port.mount_with(field, current, material),
                |field, current, material, state| {
                    port.mount_continued(field, current, material, state)
                },
            )
        }
        Backend::Cuda => {
            // An unavailable card is a visible error. There is no silent fallback to host.
            let card = Card::open(0)?;
            let port = if reception_rest {
                CudaResident::new(&card, 4, octets::BUDGET).with_reception(Reception::Rest)
            } else {
                CudaResident::new(&card, 4, octets::BUDGET)
            };
            let label = if reception_rest { "rest" } else { "carry" };
            println!("execution_backend=cuda card_ordinal=0 gpu_used=true reception={label}");
            octets::run(
                &port,
                &args,
                |field, current, material| port.mount_with(field, current, material),
                |field, current, material, state| {
                    port.mount_continued(field, current, material, state)
                },
            )
        }
    }
}

fn main() -> Result<()> {
    run()
}

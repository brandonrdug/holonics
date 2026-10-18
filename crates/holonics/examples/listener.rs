//! Host entry for the one continuing listener: the sections of
//! `listener/sections.rs` on the octet chart of `listener/octets.rs`, learned and released by the
//! host reference realization.
//!
//! `cargo run --release -p holonics --example listener -- --route sections --learn LEARN.hlsn [--learn-count N]
//! [--release RELEASE.hlsn --keys KEYS.bin [--release-count N]] [--population N]
//! --max-release-octets N [--reception carry|rest] [--checkpoint-dir DIR
//! --checkpoint-every 1,2,4,...] [--checkpoint-latest STATE --wall-seconds SECS]
//! [--checkpoint-in STATE --population N --learn-from N] [--arrival-context]`
//!
//! `--route observed --learn STREAM.hlsn --population N --keys KEYS.bin [--learn-count N]`
//! compares every delivered source and answer cell on one continuing resident. At each question
//! end it releases on a clone and writes the release before delivering the answer. The release
//! maximum is the longest passage delivered so far. Precision publication, resume and the device
//! fork remain separate work. Every delivered cell is read by this run.
//!
//! The receiving layout stays at the original single-map default unless `--arrival-context`
//! explicitly selects the paired finite-candidate layout used by the v26 MNIST comparison.
//! Teacher-forced `--read` and question-only `--release` require separate processes; release
//! frames with nonempty targets are refused before any model setup or ingestion.
//!
//! `--reception` declares what each reception's word opens on (`Reception`): `carry`, the
//! production default (the carry at `A = 0`, opening on the continuing motion), or `rest`
//! (`A = I`, every word opened at rest).

#[path = "listener/continuing.rs"]
mod continuing;
#[path = "listener/octets.rs"]
mod octets;
#[path = "listener/sections.rs"]
mod sections;

use holonics::hnn::Reference;
use holonics::hnn::reference::Reception;
use std::error::Error;

// [declaration] The inherited execution port declares four pending handles.
// Route grammar, backend/reception labels and exterior diagnostics are run declarations.

fn main() -> std::result::Result<(), Box<dyn Error>> {
    let mut args: Vec<_> = std::env::args().skip(1).collect();
    let mut port = Reference::new(4, octets::BUDGET);
    let mut reception = "carry";
    if let Some(at) = args.iter().position(|arg| arg == "--reception") {
        let value = args.get(at + 1).ok_or("--reception needs carry or rest")?;
        match value.as_str() {
            "carry" => {}
            "rest" => {
                port = port.with_reception(Reception::Rest);
                reception = "rest";
            }
            other => return Err(format!("--reception {other}: expected carry or rest").into()),
        }
        args.drain(at..at + 2);
    }
    let route = octets::take_route(&mut args)?;
    println!("execution_backend=host_reference gpu_used=false reception={reception}");
    if route == "observed" {
        return continuing::run(&port, &args);
    }
    octets::run(
        &port,
        &args,
        |field, current, material| port.mount_with(field, current, material),
        |field, current, material, state| port.mount_continued(field, current, material, state),
    )
}

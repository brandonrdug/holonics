//! One observed listener with explicitly selected actual epoch execution.
//!
//! `cargo run --release -p holonics-cuda --example listener_observed --
//! --backend cuda --route observed ...`

#[path = "../../holonics/examples/listener/continuing.rs"]
mod continuing;
#[path = "../../holonics/examples/listener/octets.rs"]
mod octets;
#[path = "../../holonics/examples/listener/sections.rs"]
mod sections;

use holonics::hnn::Reference;
use holonics_cuda::hnn::ObservedEpochDevice;
use std::error::Error;

fn main() -> Result<(), Box<dyn Error>> {
    let mut args: Vec<_> = std::env::args().skip(1).collect();
    let mut backend = "cuda".to_owned();
    if let Some(at) = args.iter().position(|arg| arg == "--backend") {
        backend = args
            .get(at + 1)
            .ok_or("--backend needs cuda or host")?
            .clone();
        args.drain(at..at + 2);
    }
    if let Some(at) = args.iter().position(|arg| arg == "--route") {
        if args.get(at + 1).map(String::as_str) != Some("observed") {
            return Err("listener_observed requires --route observed".into());
        }
        args.drain(at..at + 2);
    }
    let port = Reference::new(4, octets::BUDGET);
    match backend.as_str() {
        "host" => {
            println!(
                "execution_backend=host_reference gpu_used=false reception=carry explicit_parity_mode=true"
            );
            continuing::run(&port, &args)
        }
        "cuda" => {
            let execution = ObservedEpochDevice::open(0)?;
            println!(
                "execution_backend=cuda_observed_epoch gpu_used=true reception=carry persistent_whole_life_kernel=false"
            );
            println!(
                "cuda_epoch_card=chart_arithmetic,word_forward,word_adjoint,receiving_source_return,grouped_G_deltaH_support"
            );
            println!(
                "cuda_epoch_host=source_prefix_scan,comparison_ratio_partition,chart_decisions,algebraic_readout,native_composition,joint_certificate_and_apply,precision,release_forks,keys_and_close"
            );
            println!(
                "cuda_epoch_bus=owned_operands,exact_forward_readings,exact_returns,grouped_statistics"
            );
            continuing::run_with_execution(&port, &args, &execution)
        }
        _ => return Err("--backend needs cuda or host".into()),
    }
}

//! CUDA-default MNIST example, with explicit host-reference parity mode.
//! Usage: `cargo run --release -p holonics-cuda --example mnist_observed -- [--backend cuda|host] DATA_DIR ...`

#[path = "../../holonics/examples/mnist_observed/common.rs"]
mod shared;

use holonics::hnn::{Current, Reference};
use holonics_cuda::hnn::{Card, Resident as CudaResident};
use std::error::Error;

type Result<T> = std::result::Result<T, Box<dyn Error>>;

#[derive(Clone, Copy)]
enum Backend {
    Cuda,
    Host,
}

fn arguments() -> Result<(Backend, Vec<String>)> {
    let mut args: Vec<_> = std::env::args().skip(1).collect();
    let backend = if args.first().is_some_and(|arg| arg == "--backend") {
        if args.len() < 2 {
            return Err("--backend requires `cuda` or `host`".into());
        }
        let backend = match args[1].as_str() {
            "cuda" => Backend::Cuda,
            "host" => Backend::Host,
            other => {
                return Err(format!("unknown backend {other:?}; choose `cuda` or `host`").into());
            }
        };
        args.drain(..2);
        backend
    } else {
        // CUDA is the default; a missing/unavailable card is a visible error, never a host fallback.
        Backend::Cuda
    };
    Ok((backend, args))
}

fn run() -> Result<()> {
    let (backend, args) = arguments()?;
    match backend {
        Backend::Host => {
            let port = Reference::new(4, shared::BUDGET);
            println!("execution_backend=host_reference gpu_used=false explicit_parity_mode=true");
            shared::run(&port, &args, |field, current, material| {
                port.mount_with(field, current, material)
            })
        }
        Backend::Cuda => {
            let card = Card::open(0)?;
            let port = CudaResident::new(&card, 4, shared::BUDGET);
            let memory_at_open = card.census().memory;
            println!("execution_backend=cuda card_ordinal=0 gpu_used=true");
            println!(
                "cuda_memory_reading phase=card_open_after_context_before_hnn_image_and_stream free_octets={} total_octets={} free_bits={} total_bits={} program_allocation_not_isolated=true",
                memory_at_open.free_bytes,
                memory_at_open.total_bytes,
                u128::from(memory_at_open.free_bytes as u64) * 8,
                u128::from(memory_at_open.total_bytes as u64) * 8
            );
            println!(
                "cuda_split_on_card=source_moment_ingest,published_loci,chart_refinement,word_forward_and_reverse,tree_mirror_splits_and_deposits,release_word_read"
            );
            println!(
                "cuda_split_on_host=lift_and_active_address,moment_mirror,constitution_and_certificates,chart_decisions,algebraic_faces_and_release_decision,compare_scoring_and_covectors,successor_material,keys_collapse_ledger_and_receipts"
            );
            println!(
                "cuda_split_bus=encoded_cells(4_octets_each),plans_and_weights,operators_and_charts,certificates,word_records_and_logits,moved_words,receipts"
            );
            println!(
                "cuda_split_method=mount card=locus_publication host=field_holarchy_and_admission_certificates bus=loci_once_whole"
            );
            println!(
                "cuda_split_method=ingest card=resident_source_moment host=lift_active_address_and_checked_moment_mirror bus=cells_4_octets_each_and_receipt"
            );
            println!(
                "cuda_split_method=refine card=chart_kernels_word_forward_ticks_receiving_read host=chart_decisions_algebraic_face_and_energy_reads bus=plan_weights_operators_charts_certificates_word_record_logits"
            );
            println!(
                "cuda_split_method=compare card=word_reverse_and_tree_splits host=class_faces_ratio_score_and_source_material_covectors bus=carried_reads_and_full_return"
            );
            println!(
                "cuda_split_method=deposit card=successor_scatter_and_tree_mirror host=successor_constitution_and_certificates bus=moved_words_and_mirror_receipts"
            );
            println!(
                "cuda_split_method=release card=release_word_read host=width_and_decision bus=word"
            );
            println!(
                "cuda_split_method=close_aeon card=re_read_and_descended_loci host=collapse_first_law_ledger_and_boundary bus=word_and_moved_words"
            );
            println!(
                "cuda_split_method=read_discard card=handle_buffer_free host=handle_bits bus=none"
            );
            let result = shared::run(&port, &args, |field, current, material| {
                port.mount_with(field, current, material)
            });
            let traffic = port.traffic();
            let total_octets = u128::from(traffic.words)
                + u128::from(traffic.returns)
                + u128::from(traffic.publications)
                + u128::from(traffic.ingest);
            println!(
                "cuda_bus_volume scope=all_port_residents_since_port_creation octets_both_directions=true words_octets={} returns_octets={} publications_octets={} ingest_octets={} total_octets={} total_bits={} word_count={} return_count={} mode_view_projection_ns={} mode_view_publication_ns={} mode_view_publication_octets={} mode_view_max_exponent_extra={} mode_view_bytes_are_subcount_of_publications=true",
                traffic.words,
                traffic.returns,
                traffic.publications,
                traffic.ingest,
                total_octets,
                total_octets * 8,
                traffic.word_count,
                traffic.return_count,
                traffic.mode_view_projection_ns,
                traffic.mode_view_publication_ns,
                traffic.mode_view_publication_octets,
                traffic.mode_view_max_exponent_extra
            );
            result
        }
    }
}

fn main() -> Result<()> {
    run()
}

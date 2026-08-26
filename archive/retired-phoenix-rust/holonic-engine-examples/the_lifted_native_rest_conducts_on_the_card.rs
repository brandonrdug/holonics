//! W2 base deed: conduct the lifted native rest on the resident card.
//!
//! This deed conducts the lifted native rest and compares its exact receiver faces against
//! Station C's committed artifact. It does not condense or cultivate the result. The native rest
//! is the sole material source; the streamed tower owns the 43-segment circulation and its
//! terminal read occurs only after the one conducting-current synchronization.

#[path = "phoenix/native_streamed.rs"]
mod native_streamed;
#[path = "phoenix/resident_layer.rs"]
mod resident_layer;
#[path = "phoenix/streamed.rs"]
mod streamed;
#[path = "phoenix/tower.rs"]
mod tower;
#[path = "phoenix/tower_receiver.rs"]
mod tower_receiver;

use std::io::Write;

use holonic_engine::embedding_fiber::ResidentReadout;
use holonic_engine::foreign_codec_rest::ExteriorCodebookRest;
use holonic_engine::resident_section::{ResidentGrain, ResidentSurface, SeriesAperture};
use native_streamed::NativeMaterialSource;
use tower_receiver::{Vocabulary, compare, future_section, read_committed};

const TOKENS: [usize; 5] = [818, 5279, 529, 7001, 563];
const COMMITTED: &str = "output/the_tower_conducts/tower-5-inputs-grain-48-terms-14.form";

fn main() {
    let mut positional = Vec::new();
    let mut codebook_path = None;
    let mut committed_path = COMMITTED.to_owned();
    let mut it = std::env::args().skip(1);
    while let Some(arg) = it.next() {
        match arg.as_str() {
            "--codebook" => codebook_path = Some(it.next().expect("--codebook <CODEBOOK_TSV>")),
            "--committed" => committed_path = it.next().expect("--committed <STATION_C_ARTIFACT>"),
            _ => positional.push(arg),
        }
    }
    let rest_path = positional.first().cloned().unwrap_or_else(|| {
        eprintln!("REFUSED: usage: the_lifted_native_rest_conducts_on_the_card <REST> [OUT]");
        std::process::exit(2);
    });
    let out_path = positional
        .get(1)
        .cloned()
        .unwrap_or_else(|| "output/phoenix-w2/native_card_conduct.form".to_owned());

    // ResidentReadout is the card admission.  A host-only or absent card is a refusal, never a
    // CPU substitute for the semantic deed.
    let readout = match ResidentReadout::new() {
        Ok(readout) => Box::leak(Box::new(readout)) as &'static ResidentReadout,
        Err(error) => {
            eprintln!("REFUSED: no resident card readout: {error:?}");
            std::process::exit(3);
        }
    };
    let surface = match ResidentSurface::on(readout) {
        Ok(surface) => Box::leak(Box::new(surface)) as &'static ResidentSurface<'static>,
        Err(error) => {
            eprintln!("REFUSED: no resident card surface: {error:?}");
            std::process::exit(4);
        }
    };
    let mut source = match NativeMaterialSource::open(&rest_path) {
        Ok(source) => source,
        Err(error) => {
            eprintln!("REFUSED: native rest did not mount: {error}");
            std::process::exit(5);
        }
    };

    let before = surface.census();
    let circulated = match streamed::circulate(
        surface,
        readout,
        &mut source,
        &TOKENS,
        ResidentGrain(48),
        SeriesAperture(14),
        tower::Chart::Midpoint,
        true,
        tower::LAYERS,
        false,
    ) {
        Ok(circulated) => circulated,
        Err(error) => {
            eprintln!("REFUSED: resident native circulation: {error}");
            std::process::exit(6);
        }
    };

    // The streamed deed exposes the loop-open/loop-close receiver shadows.  A semantic section
    // read during the loop would change this counter; it is forbidden by W4.
    let no_cpu_section_readout = circulated.census_at_loop_open.section_read_outs
        == circulated.census_at_loop_close.section_read_outs
        && circulated.census_at_loop_open.egress_section_octets
            == circulated.census_at_loop_close.egress_section_octets;
    let no_obstructions =
        circulated.obstructions.is_empty() && circulated.terminal_refusal.is_none();
    let complete_segments = circulated.segments.len() == tower::LAYERS + 1;
    let complete_launches = circulated.deed_launches == tower::LAYERS as u64 + 1;
    let one_terminal_sync = circulated.streamed.terminal_synchronizations == 1;
    if !complete_segments
        || !complete_launches
        || !one_terminal_sync
        || !no_obstructions
        || !no_cpu_section_readout
    {
        eprintln!(
            "REFUSED: W2 closure failed: segments={} launches={} terminal_syncs={} obstructions={} no_cpu_readout={}",
            circulated.segments.len(),
            circulated.deed_launches,
            circulated.streamed.terminal_synchronizations,
            circulated.obstructions.len(),
            no_cpu_section_readout
        );
        std::process::exit(7);
    }
    if let Err(error) = source.rest.verify_still() {
        eprintln!("REFUSED: native rest moved: {error}");
        std::process::exit(8);
    }

    // W1's mounted rest is the default codebook owner.  An external TSV is accepted only when
    // its authenticated digest is exactly the mounted rest's codebook; no source tokenizer is
    // opened and no surface is invented here.
    let external_codebook = match codebook_path {
        Some(path) => match ExteriorCodebookRest::read_tsv(&path) {
            Ok(codebook) => Some(codebook),
            Err(error) => {
                eprintln!("REFUSED: CODEBOOK_TSV did not mount: {error}");
                std::process::exit(12);
            }
        },
        None => None,
    };
    if let Some(codebook) = &external_codebook {
        if codebook.codebook_sha256 != source.rest.codebook().codebook_sha256 {
            eprintln!("REFUSED: CODEBOOK_TSV is not the mounted W1 codebook");
            std::process::exit(13);
        }
    }
    let codebook = external_codebook
        .as_ref()
        .unwrap_or_else(|| source.rest.codebook());
    let vocabulary = Vocabulary::new(codebook);
    let future = match future_section(
        &circulated.potential,
        TOKENS.len() - 1,
        &vocabulary,
        ResidentGrain(48),
        64,
    ) {
        Ok(future) => future,
        Err(error) => {
            eprintln!("REFUSED: native future receiver did not return: {error}");
            std::process::exit(14);
        }
    };
    let collapsed = format!(
        "(quotients, Σ widths, widest, nonzero): {:?}",
        circulated
            .segments
            .iter()
            .filter(|s| s.layer.is_some())
            .map(|s| (
                s.layer.unwrap(),
                s.quotients,
                s.collapsed_width_sum,
                s.collapsed_width_max,
                s.collapsed_nonzero
            ))
            .collect::<Vec<_>>()
    );
    let committed = match read_committed(&committed_path, &TOKENS) {
        Ok(committed) => committed,
        Err(error) => {
            eprintln!("REFUSED: Station C artifact did not return: {error}");
            std::process::exit(15);
        }
    };
    let comparison = match compare(
        &committed,
        &future,
        &vocabulary,
        &circulated.final_normed,
        &collapsed,
    ) {
        Ok(comparison) => comparison,
        Err(error) => {
            eprintln!("REFUSED: W2 receiver comparison did not return: {error}");
            std::process::exit(16);
        }
    };
    if !comparison.future_equal || !comparison.final_normed_equal || !comparison.collapsed_equal {
        eprintln!(
            "REFUSED: W2 receiver mismatch: {}\n  future mine {}\n  committed {}\n  candidates mine {:?}\n  committed {:?}\n  final first difference {:?}",
            comparison.summary,
            comparison.future_line,
            committed.future,
            comparison.candidates,
            committed.candidates,
            comparison.final_difference
        );
        std::process::exit(16);
    }

    let after = surface.census();
    let mut opened = Vec::new();
    if let Ok(entries) = std::fs::read_dir("/proc/self/fd") {
        for entry in entries.flatten() {
            if let Ok(target) = std::fs::read_link(entry.path()) {
                opened.push(target.to_string_lossy().into_owned());
            }
        }
    }
    let source_path_abs = std::fs::canonicalize(&rest_path)
        .map(|path| path.to_string_lossy().into_owned())
        .unwrap_or(rest_path.clone());
    let source_path_seen = opened.iter().any(|path| path == &source_path_abs);
    let foreign_source_seen = opened.iter().any(|path| {
        path.contains("model.safetensors")
            || path.contains("modeling_gemma4.py")
            || path.contains("config.json")
            || path.contains("tokenizer.json")
    });
    if foreign_source_seen {
        eprintln!("REFUSED: a foreign source descriptor remained open: {opened:?}");
        std::process::exit(9);
    }
    let source_path_audit = format!(
        "rest={} native_rest_seen={} foreign_source_seen={} opened={:?}",
        source_path_abs, source_path_seen, foreign_source_seen, opened
    );

    if let Some(parent) = std::path::Path::new(&out_path).parent() {
        if let Err(error) = std::fs::create_dir_all(parent) {
            eprintln!("REFUSED: create receipt directory: {error}");
            std::process::exit(10);
        }
    }
    let mut receipt = match std::fs::File::create(&out_path) {
        Ok(file) => file,
        Err(error) => {
            eprintln!("REFUSED: create receipt: {error}");
            std::process::exit(11);
        }
    };
    writeln!(
        receipt,
        "PHOENIX W2 BASE — LIFTED NATIVE REST CONDUCTS ON THE CARD"
    )
    .unwrap();
    writeln!(receipt, "rest {}", rest_path).unwrap();
    writeln!(
        receipt,
        "device {} mode {:?}",
        readout.device_name(),
        surface.mode()
    )
    .unwrap();
    writeln!(
        receipt,
        "tokens {:?} grain 2^-48 terms 14 chart Midpoint fuse true",
        TOKENS
    )
    .unwrap();
    writeln!(
        receipt,
        "segments {} launches {} terminal_synchronizations {}",
        circulated.segments.len(),
        circulated.deed_launches,
        circulated.streamed.terminal_synchronizations
    )
    .unwrap();
    writeln!(
        receipt,
        "no_obstructions {} no_cpu_section_readout {}",
        no_obstructions, no_cpu_section_readout
    )
    .unwrap();
    writeln!(receipt, "rest_verify_still true").unwrap();
    writeln!(
        receipt,
        "wall_s {:.6} loop_wall_s {:.6}",
        circulated.wall_s, circulated.loop_wall_s
    )
    .unwrap();
    writeln!(receipt, "exact_work {:?}", circulated.tower_work).unwrap();
    writeln!(receipt, "streamed_census {:?}", circulated.streamed).unwrap();
    writeln!(receipt, "surface_census_before {:?}", before).unwrap();
    writeln!(receipt, "surface_census_after {:?}", after).unwrap();
    writeln!(receipt, "graph_key {:?}", circulated.graph_key).unwrap();
    writeln!(receipt, "source_path_audit {}", source_path_audit).unwrap();
    writeln!(receipt, "station_c_committed {}", committed_path).unwrap();
    writeln!(
        receipt,
        "committed_source_runtime_cross_chart_face {}",
        committed.source_runtime_cross_chart
    )
    .unwrap();
    writeln!(receipt, "codebook_sha256 {}", codebook.codebook_sha256).unwrap();
    writeln!(
        receipt,
        "receiver_comparison_summary {}",
        comparison.summary
    )
    .unwrap();
    writeln!(receipt, "plural_future_exact {}", comparison.future_line).unwrap();
    writeln!(
        receipt,
        "plural_candidates_exact {:?}",
        comparison.candidates
    )
    .unwrap();
    writeln!(receipt, "collapsed_population_exact {}", collapsed).unwrap();
    writeln!(receipt, "final_normed_exact {:?}", circulated.final_normed).unwrap();
    writeln!(receipt, "potential_exact {:?}", circulated.potential).unwrap();
    println!(
        "W2 BASE PASS: native rest conducted on {} in {:.3}s; receipt {}",
        readout.device_name(),
        circulated.wall_s,
        out_path
    );
}

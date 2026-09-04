//! SKE1: the return through the body.  One cycle on a context, then the continuing occurrence
//! enters and the differential of the receiver returns through every operation of the cycle,
//! depositing on every cross-section it reaches; the cycle then completes on the deposited body.
//! Mode `control` enacts no return on the same two occurrences. Mode `repeat` also advances a
//! third cycle, so its second return must use the morphology retained by the first.

use std::path::Path;

use athena_alpha::AthenaTokenApplication;
use holonic_engine::{
    embedding_fiber::ResidentReadout,
    native_ecology::holonic_intelligence::{
        NativeFullOperatorSession, NativeMorphologyTransition,
        NativeOperatorResidence, NativeReturnAperture, dismantle_full_native_operator,
        mount_operator_surface,
    },
};
use serde::Serialize;

#[derive(Serialize)]
struct LayerSupport {
    layer: Option<u16>,
    operations: usize,
    nonzero_coordinates: usize,
    widest_interval: u64,
}

#[derive(Serialize)]
struct Receipt {
    mode: String,
    aperture: Option<NativeReturnAperture>,
    context: Vec<u32>,
    entering: Vec<u32>,
    first_face_selected: u32,
    first_face_rendered: String,
    first_cycle_milliseconds: u128,
    transition_changed: bool,
    operations_returned: usize,
    layers_replayed: usize,
    deposits: usize,
    populations_deposited: usize,
    deposit_ranks_all_equal_context: bool,
    lookups_reached: usize,
    supports_by_layer: Vec<LayerSupport>,
    return_milliseconds: u128,
    overlay_rank_after: usize,
    second_cycle_milliseconds: u128,
    second_face_selected: u32,
    second_face_rendered: String,
    second_emission_digest: String,
    repeated_return: Option<RepeatedReturn>,
}

#[derive(Serialize)]
struct RepeatedReturn {
    predecessor_generation: u64,
    successor_generation: u64,
    overlay_rank_before: usize,
    overlay_rank_used_by_return: usize,
    overlay_rank_after: usize,
    operations_returned: usize,
    cross_sections_deposited: usize,
    cycle_milliseconds: u128,
    emission_digest: String,
}

static LAST_STEP: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);

fn step(name: &str) {
    let now = std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_secs();
    LAST_STEP.store(now, std::sync::atomic::Ordering::Relaxed);
    eprintln!("adjoint return: {name}");
}

fn guard() {
    step("starting");
    std::thread::spawn(|| loop {
        std::thread::sleep(std::time::Duration::from_secs(1));
        let now = std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_secs();
        if now.saturating_sub(LAST_STEP.load(std::sync::atomic::Ordering::Relaxed)) > 180 {
            eprintln!("adjoint return hung at its last reported step for 180 seconds");
            std::process::exit(124);
        }
    });
}

fn digest(intervals: &[(i64, i64)]) -> String {
    let mut fold: u64 = 0xcbf2_9ce4_8422_2325;
    for (lo, hi) in intervals {
        for word in [*lo as u64, *hi as u64] {
            fold ^= word;
            fold = fold.wrapping_mul(0x0100_0000_01b3);
        }
    }
    format!("{fold:016x}")
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    guard();
    let mut args = std::env::args().skip(1);
    let root = args
        .next()
        .unwrap_or_else(|| "/home/b/models/gemma-4-E4B-it".to_owned());
    let mode = args.next().unwrap_or_else(|| "return".to_owned());
    let aperture = match mode.as_str() {
        "return" | "repeat" => Some(NativeReturnAperture {
            learning_shift: 16,
            series_terms: 14,
        }),
        "control" => None,
        other => return Err(format!("unknown mode {other}").into()),
    };
    let application = AthenaTokenApplication::open(Path::new(&root))?;
    let context = application.encode("Explain holonics briefly.")?;
    let continuation = application.encode(" Holonics is the study of")?;
    let entering: Vec<u32> = context.iter().chain(continuation.iter()).copied().collect();
    let returned = dismantle_full_native_operator(Path::new(&root))?;
    let readout = ResidentReadout::new()?;
    let surface = mount_operator_surface(&readout)?;
    step("mounting coefficients");
    let mut residence =
        NativeOperatorResidence::mount(&surface, &returned.native, &returned.exterior)?;
    let session = match aperture {
        Some(aperture) => {
            NativeFullOperatorSession::found_with_return(&returned.native, &mut residence, aperture)?
        }
        None => NativeFullOperatorSession::found(&returned.native, &mut residence)?,
    };
    step("first cycle");
    let started = std::time::Instant::now();
    let first = session.advance_cycle(&context)?;
    let first_cycle_milliseconds = started.elapsed().as_millis();
    let face = application.render(&first.final_emission)?;
    let session = first.successor;
    step("first return and second cycle");
    let started = std::time::Instant::now();
    let second = session.advance_cycle(&entering)?;
    let second_cycle_milliseconds = started.elapsed().as_millis();
    let (changed, adjoint) = match &second.traces[0].morphology_transition {
        NativeMorphologyTransition::Changed { adjoint, .. } => (true, Some(adjoint.clone())),
        NativeMorphologyTransition::Unchanged => (false, None),
    };
    let second_face = application.render(&second.final_emission)?;
    let mut supports_by_layer: Vec<LayerSupport> = Vec::new();
    if let Some(adjoint) = &adjoint {
        for support in &adjoint.supports {
            match supports_by_layer.iter_mut().find(|entry| entry.layer == support.layer) {
                Some(entry) => {
                    entry.operations += 1;
                    entry.nonzero_coordinates += support.nonzero_coordinates;
                    entry.widest_interval = entry.widest_interval.max(support.widest_interval);
                }
                None => supports_by_layer.push(LayerSupport {
                    layer: support.layer,
                    operations: 1,
                    nonzero_coordinates: support.nonzero_coordinates,
                    widest_interval: support.widest_interval,
                }),
            }
        }
    }
    let second_emission_digest = digest(&second.final_emission.intervals);
    let overlay_rank_after = second.successor.morphology_overlay_rank();
    let repeated_return = if mode == "repeat" {
        let predecessor_generation = second.successor.generation();
        let mut next = entering.clone();
        next.push(second_face.selected);
        step("second return through retained overlays and third cycle");
        let started = std::time::Instant::now();
        let third = second.successor.advance_cycle(&next)?;
        let NativeMorphologyTransition::Changed { adjoint, .. } = &third.traces[0].morphology_transition else {
            return Err("the second continuation did not return a morphology change".into());
        };
        let after = third.successor.morphology_overlay_rank();
        let cross_sections_deposited = adjoint.populations_deposited.len() + 1;
        if overlay_rank_after == 0
            || adjoint.held_overlay_rank != overlay_rank_after
            || after != overlay_rank_after + entering.len() * cross_sections_deposited {
            return Err("the repeated return did not retain the prior and newly deposited atoms".into());
        }
        Some(RepeatedReturn {
            predecessor_generation,
            successor_generation: third.successor.generation(),
            overlay_rank_before: overlay_rank_after,
            overlay_rank_used_by_return: adjoint.held_overlay_rank,
            overlay_rank_after: after,
            operations_returned: adjoint.operations_returned,
            cross_sections_deposited,
            cycle_milliseconds: started.elapsed().as_millis(),
            emission_digest: digest(&third.final_emission.intervals),
        })
    } else { None };
    let receipt = Receipt {
        mode,
        aperture,
        first_face_selected: face.selected,
        first_face_rendered: face.rendered,
        first_cycle_milliseconds,
        transition_changed: changed,
        operations_returned: adjoint.as_ref().map(|a| a.operations_returned).unwrap_or(0),
        layers_replayed: adjoint.as_ref().map(|a| a.layers_replayed).unwrap_or(0),
        deposits: adjoint.as_ref().map(|a| a.deposits.len()).unwrap_or(0),
        populations_deposited: adjoint.as_ref().map(|a| a.populations_deposited.len()).unwrap_or(0),
        deposit_ranks_all_equal_context: adjoint
            .as_ref()
            .map(|a| a.deposits.iter().all(|d| d.rank == context.len()))
            .unwrap_or(false),
        lookups_reached: adjoint.as_ref().map(|a| a.lookups_reached.len()).unwrap_or(0),
        supports_by_layer,
        return_milliseconds: adjoint.as_ref().map(|a| a.elapsed_milliseconds).unwrap_or(0),
        overlay_rank_after,
        second_cycle_milliseconds,
        second_face_selected: second_face.selected,
        second_face_rendered: second_face.rendered,
        second_emission_digest,
        context,
        entering,
        repeated_return,
    };
    println!("{}", serde_json::to_string_pretty(&receipt)?);
    Ok(())
}

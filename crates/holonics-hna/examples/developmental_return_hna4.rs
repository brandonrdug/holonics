//! HNA4, reconciled: a continuing occurrence meets the retained emitted face and the return
//! deposits on the tied cross-section; the next cycle's contraction applies the overlay.
//!
//! The driver supplies only ordinary addressed occurrences and the declared apertures. It carries
//! no factor, verdict, label, or status. Run once with `return` and once with `control` (no
//! apertures) on the same two occurrences; the two receipts differ exactly where the successor
//! morphology differs.

use std::path::Path;

use holonics_hna::AthenaTokenApplication;
use holonic_engine::{
    embedding_fiber::ResidentReadout,
    native_ecology::holonic_intelligence::{
        NativeFullOperatorSession, NativeMorphologyDeposit, NativeMorphologyTransition,
        NativeOperatorResidence, NativeReturnAperture, dismantle_full_native_operator,
        mount_operator_surface,
    },
};
use serde::Serialize;

#[derive(Serialize)]
struct Face {
    selected: u32,
    rendered: String,
    equal_maxima: usize,
    collapsed_intervals: usize,
    generation: u64,
}

#[derive(Serialize)]
struct Receipt {
    mode: String,
    aperture: Option<NativeReturnAperture>,
    context: Vec<u32>,
    entering: Vec<u32>,
    first_face: Face,
    second_transition_changed: bool,
    deposit: Option<NativeMorphologyDeposit>,
    overlay_rank_carried_by_terminal_operations: Vec<usize>,
    second_face: Face,
    second_emission_digest: String,
    driver_supplied_no_morphology_field: bool,
}

fn digest(intervals: &[(i64, i64)]) -> String {
    // A fold over the exact words, for comparing two receipts; not an identity.
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
    let mut args = std::env::args().skip(1);
    let root = args
        .next()
        .unwrap_or_else(|| "/home/b/models/gemma-4-E4B-it".to_owned());
    let mode = args.next().unwrap_or_else(|| "return".to_owned());
    let aperture = match mode.as_str() {
        "return" => Some(NativeReturnAperture {
            learning_shift: 16,
            series_terms: 14,
        }),
        "control" => None,
        other => return Err(format!("unknown mode {other}; use `return` or `control`").into()),
    };
    let application = AthenaTokenApplication::open(Path::new(&root))?;
    let context = application.encode("Explain holonics briefly.")?;
    let continuation = application.encode(" Holonics is the study of")?;
    let entering: Vec<u32> = context.iter().chain(continuation.iter()).copied().collect();
    let returned = dismantle_full_native_operator(Path::new(&root))?;
    let readout = ResidentReadout::new()?;
    let surface = mount_operator_surface(&readout)?;
    let mut residence =
        NativeOperatorResidence::mount(&surface, &returned.native, &returned.exterior)?;
    let session = match aperture {
        Some(aperture) => {
            NativeFullOperatorSession::found_with_return(&returned.native, &mut residence, aperture)?
        }
        None => NativeFullOperatorSession::found(&returned.native, &mut residence)?,
    };
    let first = session.advance_cycle(&context)?;
    let face = application.render(&first.final_emission)?;
    let first_face = Face {
        selected: face.selected,
        rendered: face.rendered,
        equal_maxima: face.equal_score_population.len(),
        collapsed_intervals: face.collapsed_interval_population,
        generation: first.successor.generation(),
    };
    let second = first.successor.advance_cycle(&entering)?;
    let (second_transition_changed, deposit) = match &second.traces[0].morphology_transition {
        NativeMorphologyTransition::Changed { deposit, .. } => (true, Some(deposit.clone())),
        NativeMorphologyTransition::Unchanged => (false, None),
    };
    let overlay_rank_carried_by_terminal_operations = second
        .traces
        .iter()
        .rev()
        .take(5)
        .map(|trace| trace.morphology_overlay_rank)
        .collect();
    let face = application.render(&second.final_emission)?;
    let second_face = Face {
        selected: face.selected,
        rendered: face.rendered,
        equal_maxima: face.equal_score_population.len(),
        collapsed_intervals: face.collapsed_interval_population,
        generation: second.successor.generation(),
    };
    println!(
        "{}",
        serde_json::to_string_pretty(&Receipt {
            mode,
            aperture,
            context,
            entering,
            first_face,
            second_transition_changed,
            deposit,
            overlay_rank_carried_by_terminal_operations,
            second_face,
            second_emission_digest: digest(&second.final_emission.intervals),
            driver_supplied_no_morphology_field: true,
        })?
    );
    Ok(())
}

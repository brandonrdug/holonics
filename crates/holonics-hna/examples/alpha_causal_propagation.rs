//! Stored-model comparison through the public native owners; no replay, learner or emitter.
use holonic_engine::native_ecology::constitutive_fibre::CausalContactPropagation;
use holonics_hna::alpha::{checkpoint::SavedTextField, material::AlphaMaterialError};
use serde_json::json;
use std::{fs, io::Write, time::Instant};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let args = std::env::args().skip(1).collect::<Vec<_>>();
    if args.len() != 2 {
        return Err("usage: alpha_causal_propagation MODEL.hna NEW_REPORT.json".into());
    }
    let start = Instant::now();
    let saved = SavedTextField::read(&args[0])?;
    let mut report=saved.with_session(|session,_,_,_| {
        let before=session.field().census();
        let (source,native,reference,native_seconds,inspection_seconds,reference_seconds)={
            let view=session.stage_operative_contacts()?;
            let source=view.inspect()?;
            let native_start=Instant::now();
            let propagated=view.propagate_causal_contacts()?;
            let native_seconds=native_start.elapsed().as_secs_f64();
            let inspect_start=Instant::now();
            let native=propagated.inspect()?;
            let inspection_seconds=inspect_start.elapsed().as_secs_f64();
            let reference_start=Instant::now();
            let reference=CausalContactPropagation::at_enclosed(&source.births,&source.contacts,
                &source.contacts_radius,&source.internal,source.fractional_bits)
                .map_err(|e|AlphaMaterialError::Apparatus(e.to_string()))?;
            (source,native,reference,native_seconds,inspection_seconds,reference_start.elapsed().as_secs_f64())
        };
        let same_current=native.internal.center==reference.internal.center;
        let same_rounding=native.rounding_radius==reference.rounding_radius;
        let contains_reference_radius=native.internal.radius>=reference.internal.radius;
        let same_joins=native.joins.iter().map(|j|(j.before,j.after)).collect::<Vec<_>>()==reference.joins;
        let result=json!({"grade":"established-bounded","evidence":["implemented-exact","computational-witness","measured"],
            "scope":"One complete stored-model propagation word. Same continuing source is borrowed, not advanced. Cold reference/inspection costs are separate from resident staging.",
            "model":args[0],"field_cut":source.field_cut,"contacts":source.contacts.len(),
            "joins":native.joins.len(),"fractional_bits":source.fractional_bits,
            "native_staging_seconds":native_seconds,"inspection_seconds":inspection_seconds,
            "reference_seconds":reference_seconds,"census_before":before,"census_after_inspection":session.field().census(),
            "comparison_passed":same_current && same_rounding && contains_reference_radius && same_joins,
            "comparison":{"same_current":same_current,"same_rounding":same_rounding,
                "contains_reference_radius":contains_reference_radius,"same_joins":same_joins},
            "native":native,"reference":reference});
        Ok(result)
    })?;
    report["whole_read_remount_and_comparison_seconds"] = json!(start.elapsed().as_secs_f64());
    let mut file = fs::OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(&args[1])?;
    file.write_all(serde_json::to_string_pretty(&report)?.as_bytes())?;
    file.write_all(b"\n")?;
    if report["comparison_passed"] != json!(true) {
        return Err(
            "resident causal propagation differs from its declared reference; report retained"
                .into(),
        );
    }
    println!("stored-model resident propagation and complete reference agree");
    Ok(())
}

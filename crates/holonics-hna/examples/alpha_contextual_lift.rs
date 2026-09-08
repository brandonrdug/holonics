//! Exact exterior derivation over a saved conversation model's actual receiving passages.
//! This creates no learner and changes no native state; it does not claim useful language.
use holonic_engine::{
    exact_linear::ContextualFactorization,
    native_ecology::constitutive_fibre::NativeContextContrastStatus,
};
use holonics_hna::{
    alpha::{checkpoint::SavedTextField, material::AlphaMaterialError},
    publish_new,
};
use serde_json::json;
use std::{io::Write, path::PathBuf, time::Instant};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut args = std::env::args().skip(1);
    let path = PathBuf::from(
        args.next()
            .ok_or("usage: alpha_contextual_lift MODEL RECEIVING,RECEIVING [--enclosed-pair] --report NEW.json")?,
    );
    let occurrences = args
        .next()
        .ok_or("receiving occurrences required")?
        .split(',')
        .map(str::parse::<usize>)
        .collect::<Result<Vec<_>, _>>()?;
    let mut option = args.next();
    let enclosed_pair = option.as_deref() == Some("--enclosed-pair");
    if enclosed_pair {
        option = args.next();
    }
    if option.as_deref() != Some("--report") {
        return Err("--report required".into());
    }
    let output = PathBuf::from(args.next().ok_or("report destination required")?);
    if args.next().is_some() || output.exists() {
        return Err("unexpected arguments or existing destination".into());
    }
    let start = Instant::now();
    let saved = SavedTextField::read(&path)?;
    let result=saved.with_session(|session,_,_,_|{
        let field=session.field();let count=field.occurrence_count();let before=field.census();
        let (inspection,rank,unobserved)=if enclosed_pair {
            let pair: [usize;2]=occurrences.as_slice().try_into().map_err(|_|AlphaMaterialError::Apparatus("enclosed-pair requires two actual receiving occurrences".into()))?;
            let p=field.inspect_contextual_pair(pair)?;
            let rank=(p.status==NativeContextContrastStatus::ContextContrastCertifiedNonzero).then_some(1usize);
            (serde_json::to_value(p).map_err(|e|AlphaMaterialError::Apparatus(e.to_string()))?,rank,None)
        }else {
            let p=field.inspect_contextual_lift(&occurrences)?;
            let (rank,unobserved)=match &p.factorization {
                ContextualFactorization::Lifted(l)=>(Some(l.demonstrated_context_rank),Some(l.returned_map.free_row_directions.len())),
                _=>(None,None),
            };
            (serde_json::to_value(p).map_err(|e|AlphaMaterialError::Apparatus(e.to_string()))?,rank,unobserved)
        };
        let material=occurrences.iter().map(|at|field.inspect_contextual_material_transport(*at)).collect::<Result<Vec<_>,_>>()?;
        let after=field.census();
        if field.occurrence_count()!=count || after.deed_launches!=before.deed_launches{return Err(AlphaMaterialError::Apparatus("cold derivation changed native operation".into()));}
        Ok(json!({"schema":"holonics.contextual-lift-inspection.v1","enclosed_pair":enclosed_pair,"model":path,"native_occurrences":count,
            "native_deeds":after.deed_launches-before.deed_launches,"cold_section_readouts":after.section_read_outs-before.section_read_outs,
            "demonstrated_context_rank":rank,"unobserved_map_directions":unobserved,"ordinary_material_receipts":material,"inspection":inspection,"language_quality_established":false}))
    })?;
    let mut result = result;
    result["whole_wall_seconds"] = json!(start.elapsed().as_secs_f64());
    let bytes = serde_json::to_vec_pretty(&result)?;
    publish_new(&output, |file| file.write_all(&bytes))?;
    println!(
        "{}",
        json!({"report":output,"demonstrated_context_rank":result["demonstrated_context_rank"],"native_deeds":result["native_deeds"],"whole_wall_seconds":result["whole_wall_seconds"]})
    );
    Ok(())
}

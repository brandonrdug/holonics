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

fn normalized_returns(
    path: PathBuf, occurrences: Vec<usize>, group_width: usize, output: PathBuf, source_pullback: bool,
) -> Result<(), Box<dyn std::error::Error>> {
    let start=Instant::now();
    let saved=SavedTextField::read(&path)?;
    let mut result=saved.with_session(|session,_,_,_| {
        let field=session.field();let count=field.occurrence_count();let mut returns=Vec::new();
        for at in occurrences.iter().copied() {
            let before=field.census();let clock=Instant::now();
            let returned=field.normalized_material_return(at,group_width,holonic_engine::resident_section::SeriesAperture(32))?
                .ok_or_else(||AlphaMaterialError::Apparatus(format!("occurrence {at} has no received material prediction")))?;
            let seconds=clock.elapsed().as_secs_f64();let after=field.census();
            let reading=returned.inspect()?;
            if after.section_read_outs!=before.section_read_outs || field.occurrence_count()!=count {
                return Err(AlphaMaterialError::Apparatus("receiver read numerical current or changed recurrence".into()));
            }
            let mut pullbacks=Vec::new();
            if source_pullback {
                use holonic_engine::native_ecology::constitutive_fibre::NativeMaterialPullbackMetric;
                for metric in [NativeMaterialPullbackMetric::RelativeEntropy,NativeMaterialPullbackMetric::SquaredProbability] {
                    let before=field.census();let clock=Instant::now();
                    let pulled=field.pull_back_material_source(&returned,metric)?;
                    let elapsed=clock.elapsed().as_secs_f64();let after=field.census();
                    if after.section_read_outs!=before.section_read_outs || field.occurrence_count()!=count {
                        return Err(AlphaMaterialError::Apparatus("material pullback read numerical current or changed recurrence".into()));
                    }
                    pullbacks.push(json!({"reading":pulled.inspect()?,"resident_seconds":elapsed,
                        "resident_deeds":after.deed_launches-before.deed_launches,
                        "numerical_section_readouts":after.section_read_outs-before.section_read_outs,
                        "native_ingress_octets":after.ingress_octets-before.ingress_octets}));
                }
            }
            returns.push(json!({"reading":reading,"source_pullbacks":pullbacks,"resident_seconds":seconds,
                "resident_deeds":after.deed_launches-before.deed_launches,
                "numerical_section_readouts":after.section_read_outs-before.section_read_outs,
                "native_ingress_octets":after.ingress_octets-before.ingress_octets}));
        }
        Ok(json!({"schema":"holonics.normalized-material-return.v1","model":path,
            "field_cut":count,"group_width":group_width,"returns":returns,
            "morphology_changed":false,"language_quality_established":false}))
    })?;
    result["whole_wall_seconds"]=json!(start.elapsed().as_secs_f64());
    publish_new(&output,|file|file.write_all(&serde_json::to_vec_pretty(&result)?))?;
    println!("{}",json!({"report":output,"field_cut":result["field_cut"],
        "returns":result["returns"].as_array().map(Vec::len),"whole_wall_seconds":result["whole_wall_seconds"]}));
    Ok(())
}

fn operative_contacts(path: PathBuf, output: PathBuf) -> Result<(), Box<dyn std::error::Error>> {
    let start = Instant::now();
    let saved = SavedTextField::read(&path)?;
    let mut report=saved.with_session(|session,_,_,_| {
        let count=session.field().occurrence_count();
        let reference=session.field().inspect_internal_current_enclosures()?.ok_or_else(||AlphaMaterialError::Apparatus("enclosed field required".into()))?;
        let before=session.field().census();
        let staging_start=Instant::now();let view=session.stage_operative_contacts()?;let staging_seconds=staging_start.elapsed().as_secs_f64();let after=view.census();let reading=view.inspect()?;
        if reading.births.len()!=reference.len() || reading.contacts_radius!=num_rational::BigRational::from_integer(0.into()) {
            return Err(AlphaMaterialError::Apparatus("this exact numerical comparison requires exact birth-map coordinates".into()));
        }
        for (i,old) in reference.iter().enumerate() {
            if reading.births[i].source!=old.source_occurrence || reading.births[i].receiving!=old.receiving_occurrence
                || reading.contacts[i]!=old.contact || reading.internal.center[i]!=old.current.center[0] {
                return Err(AlphaMaterialError::Apparatus(format!("operative carrier disagrees at contact {i}")));
            }
        }
        if view.field_cut()!=count || after.section_read_outs!=before.section_read_outs {
            return Err(AlphaMaterialError::Apparatus("staging changed the field cut or read numerical sections".into()));
        }
        Ok(json!({"schema":"holonics.operative-contact-staging.v1","model":path,"field_cut":count,"contact_population":reading.births.len(),
            "all_native_contact_and_current_centres_match_reference":true,"field_changed":false,"native_staging_deeds":after.deed_launches-before.deed_launches,
            "native_staging_wall_seconds":staging_seconds,"native_staging_section_readouts":after.section_read_outs-before.section_read_outs,
            "native_staging_ingress_octets":after.ingress_octets-before.ingress_octets,
            "resident_octets_after_staging":after.resident_octets_now,"resident_octets_peak":after.resident_octets_peak,
            "map_radius":reading.contacts_radius,"internal_radius":reading.internal.radius,
            "covariance":reading.covariance,"covariance_radius":reading.covariance_radius,
            "aggregate":reading.aggregate,"numerical_contact_norm_upper":reading.numerical_contact_norm_upper,
            "numerical_internal_norm_upper":reading.numerical_internal_norm_upper,"native_joint_return_integrated":false,"language_quality_established":false}))
    })?;
    report["whole_wall_seconds"] = json!(start.elapsed().as_secs_f64());
    publish_new(&output, |file| {
        file.write_all(&serde_json::to_vec_pretty(&report)?)
    })?;
    println!(
        "{}",
        json!({"report":output,"contact_population":report["contact_population"],"all_centres_match":report["all_native_contact_and_current_centres_match_reference"],"whole_wall_seconds":report["whole_wall_seconds"]})
    );
    Ok(())
}

// Explicit cold observer over the saved owner. No corpus replay, native development or
// model-current selection occurs here. One wire codeword is written per exact point pair.
fn material_history(path: PathBuf, output: PathBuf) -> Result<(), Box<dyn std::error::Error>> {
    let start = Instant::now();
    let saved = SavedTextField::read(&path)?;
    let receipt = saved.with_session(|session, _, _, _| {
        let field = session.field();
        let count = field.occurrence_count();
        let before = field.census();
        publish_new(&output, |file| {
            let mut writer = std::io::BufWriter::new(file);
            for at in 0..count {
                let wire = field.inspect_material_transport_wire(at)
                    .map_err(std::io::Error::other)?
                    .ok_or_else(|| std::io::Error::other("missing material report"))?;
                if wire.intervals.iter().any(|(lo, hi)| lo != hi) {
                    return Err(std::io::Error::other("non-point report codeword"));
                }
                serde_json::to_writer(&mut writer, &json!({
                    "occurrence":at,"lineage":field.lineage(at),
                    "rows":wire.rows,"width":wire.width,"grain":wire.grain.0,
                    "words":wire.intervals.iter().map(|v|v.0).collect::<Vec<_>>()
                }))?;
                writer.write_all(b"\n")?;
            }
            writer.flush()
        }).map_err(|e| AlphaMaterialError::Apparatus(e.to_string()))?;
        let after = field.census();
        if count != field.occurrence_count() || before.deed_launches != after.deed_launches {
            return Err(AlphaMaterialError::Apparatus("cold observer changed native recurrence".into()));
        }
        Ok(json!({"schema":"holonics.contextual-material-history.v1","model":path,
            "report":output,"native_occurrences":count,"material_source":field.material_transport_source(),
            "native_deeds":after.deed_launches-before.deed_launches,
            "cold_section_readouts":after.section_read_outs-before.section_read_outs,
            "cold_section_octets":after.egress_section_octets-before.egress_section_octets}))
    })?;
    let mut receipt = receipt;
    receipt["whole_wall_seconds"] = json!(start.elapsed().as_secs_f64());
    println!("{receipt}");
    Ok(())
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut args = std::env::args().skip(1);
    let path = PathBuf::from(
        args.next()
            .ok_or("usage: alpha_contextual_lift MODEL (RECEIVING,RECEIVING [--enclosed-pair] | --material-history | --operative-contacts) --report NEW")?,
    );
    let selection = args
        .next()
        .ok_or("receiving occurrences or --material-history required")?;
    if selection=="--normalized-return" || selection=="--material-pullback" {
        let occurrences=args.next().ok_or("receiving occurrences required")?
            .split(',').map(str::parse::<usize>).collect::<Result<Vec<_>,_>>()?;
        if args.next().as_deref()!=Some("--group-width"){return Err("--group-width required".into());}
        let group=args.next().ok_or("group width required")?.parse()?;
        if args.next().as_deref()!=Some("--report"){return Err("--report required".into());}
        let output=PathBuf::from(args.next().ok_or("report destination required")?);
        if args.next().is_some()||output.exists(){return Err("unexpected arguments or existing destination".into());}
        return normalized_returns(path,occurrences,group,output,selection=="--material-pullback");
    }
    if selection == "--material-history" || selection == "--operative-contacts" {
        if args.next().as_deref() != Some("--report") {
            return Err("--report required".into());
        }
        let output = PathBuf::from(args.next().ok_or("report destination required")?);
        if args.next().is_some() || output.exists() {
            return Err("unexpected arguments or existing destination".into());
        }
        return if selection == "--material-history" {
            material_history(path, output)
        } else {
            operative_contacts(path, output)
        };
    }
    let occurrences = selection
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

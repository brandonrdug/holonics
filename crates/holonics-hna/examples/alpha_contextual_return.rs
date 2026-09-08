//! Native contextual section, condition contact and current re-entry on one saved text field.
//! The addressed passages and single self-return are a declared construction study. This does
//! not select a response from the corpus or claim automatic general contextual cultivation.
use holonic_engine::native_ecology::constitutive_fibre::ConditionContactMetric;
use holonics_hna::{
    alpha::{checkpoint::SavedTextField, material::AlphaMaterialError, text_codec::TextSymbol},
    publish_new,
};
use serde_json::json;
use std::{io::Write, path::PathBuf, time::Instant};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut args = std::env::args().skip(1);
    let first = args.next().ok_or("model path or --continue required")?;
    if first == "--continue" {
        return continue_model(args);
    }
    let model = PathBuf::from(first);
    let receiving = args
        .next()
        .ok_or("receiving pair required")?
        .split(',')
        .map(str::parse::<usize>)
        .collect::<Result<Vec<_>, _>>()?;
    let receiving: [usize; 2] = receiving
        .try_into()
        .map_err(|_| "two receiving occurrences required")?;
    let (mut report_path, mut checkpoint, mut prompt, mut limit) = (None, None, None, None);
    while let Some(option) = args.next() {
        let value = args.next().ok_or("option value required")?;
        match option.as_str() {
            "--report" => report_path = Some(PathBuf::from(value)),
            "--checkpoint" => checkpoint = Some(PathBuf::from(value)),
            "--prompt" => prompt = Some(std::fs::read_to_string(value)?),
            "--emit-symbols" => limit = Some(value.parse::<usize>()?),
            _ => return Err("unknown option".into()),
        }
    }
    let report_path = report_path.ok_or("--report required")?;
    let checkpoint = checkpoint.ok_or("--checkpoint required")?;
    if report_path.exists() || checkpoint.exists() {
        return Err("destinations must be new".into());
    }
    if prompt.is_some() && limit.is_none() {
        return Err("--emit-symbols required with a prompt".into());
    }
    let start = Instant::now();
    let saved = SavedTextField::read(&model)?;
    let mut report=saved.with_session(|session,_,anchors,app|{
        let native_from=session.field().occurrence_count();let before=session.field().census();let native_start=Instant::now();
        let section=session.derive_contextual_contrast(receiving)?;
        let mut condition=section.retain_condition_current(section.zero_change(),ConditionContactMetric::UnitAdmittanceRealification)?;
        // The first contact receives an actual retained observation, without remounting its values.
        let observed=section.second_observed_return().ok_or_else(||AlphaMaterialError::Apparatus("field section lacks its actual endpoint".into()))?;
        let first_family=section.preimage_absolute(observed)?;let first=condition.contact(&first_family)?;
        // One explicitly declared self-return: the learned current change returns to the same
        // condition owner through the same preimage/contact law. It is not an external verdict.
        let emitted_change=section.read_change(condition.current())?;
        let second_family=section.preimage_change(condition.current(),emitted_change.current())?;
        let second=condition.contact(&second_family)?;
        let generated=section.read_absolute(condition.current())?;
        let symbol=session.receive_native_return(generated)?;
        let after=session.field().census();let native_seconds=native_start.elapsed().as_secs_f64();
        let native_until=session.field().occurrence_count();
        if native_until!=native_from+1{return Err(AlphaMaterialError::Apparatus("unexpected field chronology".into()));}
        let application=serde_json::to_vec(&json!({"schema":"holonics.native-contextual-return-study.v1","source_application_bytes":app,
            "source_model":model,"origin":section.origin(),"native_from":native_from,"native_until":native_until}))
            .map_err(|e|AlphaMaterialError::Apparatus(e.to_string()))?;
        session.checkpoint(&checkpoint,&anchors.iter().collect::<Vec<_>>(),&application)?;
        let mut result=json!({"schema":"holonics.native-contextual-return-study.v1","model":model,"checkpoint":checkpoint,
            "origin":section.origin(),"native_from":native_from,"native_until":native_until,"native_seconds":native_seconds,
            "native_deeds":after.deed_launches-before.deed_launches,"terminal_section_reads":after.section_read_outs-before.section_read_outs,
            "terminal_section_octets":after.egress_section_octets-before.egress_section_octets,"ingress_octets":after.ingress_octets-before.ingress_octets,
            "first_contact":first.inspect()?,"self_contact":second.inspect()?,"accepted_symbol":symbol,
            "actual_native_input":session.field().inspect_incoming(native_from)?,"actual_lineage":session.field().lineage(native_from),
            "proof":section.inspect_constraint()?.intervals,"language_quality_established":false,
            "checkpoint_boundary":"after-native-current-before-prompt"});
        if let Some(prompt)=&prompt {
            session.begin_part(None)?;
            for symbol in prompt.bytes().map(TextSymbol::Octet).chain([TextSymbol::EndPart]){session.receive(symbol)?;}
            let response=session.generate(limit.unwrap());
            result["prompt"]=json!(prompt);result["utf8"]=json!(std::str::from_utf8(&response.emitted_octets).ok());
            result["generation"]=json!(response);
        }
        Ok(result)
    })?;
    report["whole_wall_seconds"] = json!(start.elapsed().as_secs_f64());
    let bytes = serde_json::to_vec_pretty(&report)?;
    publish_new(&report_path, |f| f.write_all(&bytes))?;
    println!(
        "{}",
        json!({"report":report_path,"checkpoint":checkpoint,"native_from":report["native_from"],"native_until":report["native_until"],
        "native_seconds":report["native_seconds"],"utf8":report["utf8"],"whole_wall_seconds":report["whole_wall_seconds"]})
    );
    Ok(())
}

/// Resume the actual saved successor for a prompt, without repeating contextual construction
/// or the already committed native input. The SDK restores native and application chronology.
fn continue_model(
    mut args: impl Iterator<Item = String>,
) -> Result<(), Box<dyn std::error::Error>> {
    let model = PathBuf::from(args.next().ok_or("--continue requires a saved model")?);
    let (mut output, mut prompt, mut limit) = (None, None, None);
    while let Some(option) = args.next() {
        let value = args.next().ok_or("option value required")?;
        match option.as_str() {
            "--report" => output = Some(PathBuf::from(value)),
            "--prompt" => prompt = Some(std::fs::read_to_string(value)?),
            "--emit-symbols" => limit = Some(value.parse::<usize>()?),
            _ => return Err("unknown continuation option".into()),
        }
    }
    let output = output.ok_or("--report required")?;
    let prompt = prompt.ok_or("--prompt required")?;
    let limit = limit.ok_or("--emit-symbols required")?;
    if output.exists() {
        return Err("report destination must be new".into());
    }
    let start = Instant::now();
    let saved = SavedTextField::read(&model)?;
    let report=saved.with_session(|session,_,_,_|{
        let restored=session.field().occurrence_count();let before=session.field().census();
        session.begin_part(None)?;
        for symbol in prompt.bytes().map(TextSymbol::Octet).chain([TextSymbol::EndPart]){session.receive(symbol)?;}
        let generated=session.generate(limit);
        Ok(json!({"schema":"holonics.native-contextual-return-continuation.v1","model":model,"restored_occurrences":restored,
            "restored_native_input":restored.checked_sub(1).map(|at|session.field().inspect_incoming(at)).transpose()?,
            "native_deeds":session.field().census().deed_launches-before.deed_launches,"prompt":prompt,
            "utf8":std::str::from_utf8(&generated.emitted_octets).ok(),"generation":generated,"language_quality_established":false}))
    })?;
    let mut report = report;
    report["whole_wall_seconds"] = json!(start.elapsed().as_secs_f64());
    let bytes = serde_json::to_vec_pretty(&report)?;
    publish_new(&output, |f| f.write_all(&bytes))?;
    println!(
        "{}",
        json!({"report":output,"restored_occurrences":report["restored_occurrences"],"utf8":report["utf8"],"whole_wall_seconds":report["whole_wall_seconds"]})
    );
    Ok(())
}

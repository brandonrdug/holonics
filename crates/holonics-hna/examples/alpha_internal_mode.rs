//! Read-only mode study of an actual saved conversation field. Exterior triples propose a
//! chronological experimental aperture; native full-contact equality alone admits the mode.
//! This is not a semantic classifier, a new exposure loop, or a claim of useful language.
use holonic_engine::{
    embedding_fiber::ResidentReadout,
    native_ecology::constitutive_fibre::{NativeSharedDriveMode, NativeSharedDriveModeRest},
    resident_section::{ResidentSurface, TransferCensus},
};
use holonics_hna::alpha::checkpoint::SavedTextField;
use serde_json::{Value, json};
use std::{
    collections::BTreeMap, error::Error, fs::OpenOptions, io::Write, path::PathBuf, time::Instant,
};
type E = Box<dyn Error>;
fn work(a: TransferCensus, b: TransferCensus) -> Value {
    json!({"deeds":b.deed_launches-a.deed_launches,
    "section_readouts":b.section_read_outs-a.section_read_outs,"ingress_octets":b.ingress_octets-a.ingress_octets,
    "numerical_egress_octets":b.egress_section_octets-a.egress_section_octets,
    "receipt_egress_octets":b.egress_receipt_octets-a.egress_receipt_octets})
}
fn write_new(path: &std::path::Path, bytes: &[u8]) -> Result<(), E> {
    let mut options = OpenOptions::new();
    options.write(true).create_new(true);
    #[cfg(unix)]
    {
        use std::os::unix::fs::OpenOptionsExt;
        options.mode(0o600);
    }
    let mut f = options.open(path)?;
    f.write_all(bytes)?;
    f.sync_all()?;
    Ok(())
}
fn main() -> Result<(), E> {
    let mut args = std::env::args().skip(1);
    let source = PathBuf::from(
        args.next()
            .ok_or("usage: alpha_internal_mode MODEL.hna NEW.json")?,
    );
    let output = PathBuf::from(args.next().ok_or("missing new report path")?);
    let model_path = output.with_extension("hnm");
    if output.exists() || model_path.exists() {
        return Err("output already exists".into());
    }
    let start = Instant::now();
    let saved = SavedTextField::read(&source)?;
    let occurrences = saved.occurrences();
    let (bytes,record)=saved.with_session(|session,_,_,_|{
        let mut earlier:BTreeMap<Vec<u8>,Vec<usize>>=BTreeMap::new();let mut refused=Vec::new();
        for at in 0..session.field().occurrence_count(){
            let event=session.field().lineage(at).expect("existing lineage");
            let Some(parent)=event.received_from else{continue};
            let parent=session.field().lineage(parent).expect("existing source");
            let previous=parent.predecessor_state.and_then(|p|session.field().lineage(p));
            let (Some(a),Some(b),Some(c))=(previous.and_then(|p|p.incoming.exterior()),parent.incoming.exterior(),event.incoming.exterior()) else{continue};
            let key=serde_json::to_vec(&(a,b,c)).map_err(|e|holonics_hna::alpha::material::AlphaMaterialError::Apparatus(e.to_string()))?;
            for &left in earlier.get(&key).into_iter().flatten(){
                let before=session.field().census();
                match session.condense_shared_drive_mode(left,at){
                    Ok(mode)=>{
                        let capture_work=work(before,session.field().census());
                        let observed=mode.unfold(0)?.inspect()?;
                        let mut bytes=Vec::new();mode.rest()?.write(&mut bytes)?;
                        return Ok((bytes,json!({"receiving_pair":[left,at],"mode_at_capture":observed,
                            "capture_work":capture_work,"rejected_candidates":refused,
                            "experimental_aperture":"first native-admitted pair proposed by repeated exterior input triples",
                            "field_occurrences_unchanged":session.field().occurrence_count()==occurrences})));
                    }
                    Err(e)=>refused.push(json!({"receiving_pair":[left,at],"reason":e.to_string()})),
                }
            }
            earlier.entry(key).or_default().push(at);
        }
        Err(holonics_hna::alpha::material::AlphaMaterialError::Apparatus("no proposed pair has the native shared drive".into()))
    })?;
    // The saved session and its source field are gone. Only the mode's exact cold chart enters.
    let readout = ResidentReadout::new()?;
    let surface = ResidentSurface::on(&readout)?;
    let rest = NativeSharedDriveModeRest::read(&mut bytes.as_slice(), bytes.len() as u64)?;
    let before = surface.census();
    let mode = NativeSharedDriveMode::remount(&surface, rest)?;
    let remount_work = work(before, surface.census());
    let before = surface.census();
    let future = mode.unfold(17)?;
    let future_work = work(before, surface.census());
    let report = json!({"schema":"holonics.conversation-internal-mode-study.v1","truth_status":"established-bounded",
        "evidence_tags":["measured"],"source_model":source,"saved_native_occurrences":occurrences,
        "capture":record,"mode_artifact":model_path,"mode_octets":bytes.len(),"remount_work":remount_work,
        "future_steps":17,"independent_future_work":future_work,"independent_future":future.inspect()?,
        "source_session_dropped_before_remount":true,"whole_seconds":start.elapsed().as_secs_f64(),
        "additional_conversation_exposure":false,"conversation_quality_established":false});
    let mut report_bytes = serde_json::to_vec_pretty(&report)?;
    report_bytes.push(b'\n');
    write_new(&model_path, &bytes)?;
    write_new(&output, &report_bytes)?;
    println!(
        "{}",
        json!({"report":output,"mode":model_path,"mode_octets":bytes.len(),"source_occurrences":occurrences})
    );
    Ok(())
}

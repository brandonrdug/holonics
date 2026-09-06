//! Actual document occurrences cultivate the shared native boundary map. The file is exposure
//! material, never a generated answer substituted for the model. The same probe is measured
//! before/after, then the native model itself produces its text and paired rest.
use holonics_hna::{
    publish_new, AthenaTokenApplication, HnaModel, HnaOccurrence, HnaSession, HnaSessionError,
    HnaTextApplication, HnaTextDisposition, NativeEmissionReadout,
};
use serde_json::json;
use std::{io::Write, path::Path, time::Instant};

fn err(e: impl std::fmt::Display) -> HnaSessionError {
    HnaSessionError::Base(e.to_string())
}
fn material(
    session: &mut HnaSession<'_, '_>,
    source: &Path,
    rows: &[u32],
    out: &Path,
    index: usize,
) -> Result<(), HnaSessionError> {
    if !session.missing_input_rows(rows).is_empty() {
        session.acquire_input_material(
            source,
            rows,
            &out.join(format!("input-{index:04}.safetensors")),
        )?;
    }
    Ok(())
}
fn emit(value: serde_json::Value) -> Result<(), HnaSessionError> {
    let mut out = std::io::stdout().lock();
    serde_json::to_writer(&mut out, &value).map_err(err)?;
    out.write_all(b"\n").and_then(|_| out.flush()).map_err(err)
}
fn main() -> Result<(), Box<dyn std::error::Error>> {
    let args: Vec<_> = std::env::args().collect();
    if args.len() != 7 {
        return Err("BASE CODEC_SOURCE MATERIAL_FILE PROBE OUTPUT_DIR CYCLES".into());
    }
    let source = Path::new(&args[2]);
    let out = Path::new(&args[5]);
    let cycles: usize = args[6].parse()?;
    if out.exists() {
        return Err("use a new output directory".into());
    }
    std::fs::create_dir_all(out)?;
    let bytes = std::fs::read(&args[3])?;
    let document = std::str::from_utf8(&bytes)?;
    let codec = AthenaTokenApplication::open(source)?;
    let words = codec.encode(document)?;
    if words.len() < 2 {
        return Err("exposure has no next arrival".into());
    }
    let app = HnaTextApplication::open(source)?;
    let probe = codec.encode_turn(&args[4])?;
    let model = HnaModel::from_native_rest_with_boundary_contact(&args[1], None)?;
    let started = Instant::now();
    model.with_session(|session| {
        material(session,source,&probe,out,0)?;
        let before=session.advance_native_readout(&HnaOccurrence {row_addresses:probe.clone(),history:vec![]},
            NativeEmissionReadout::LastRow)?.output.final_emission;
        let before_face=codec.render(&before).map_err(err)?;
        let mut returned=Vec::new();
        // These are ordered, causally next document occurrences, not epochs or packet-size
        // dependent events. The application does not compute a loss, contact or morphology.
        let development=(||->Result<(),HnaSessionError> {
            for end in 1..=words.len() {
                material(session,source,&words[..end],out,end)?;
                session.advance_native_readout(&HnaOccurrence {row_addresses:words[..end].to_vec(),history:vec![]},
                    NativeEmissionReadout::LastRow)?;
                if let Some(receipt)=session.last_boundary_return() {returned.push(receipt.clone());}
                emit(json!({"event":"actual-material","addresses":end,"returned":session.last_boundary_return(),
                    "maps":session.anatomy().boundary_contact_maps}))?;
            }
            Ok(())
        })().err().map(|e|e.to_string());
        session.checkpoint(&out.join("developed.hna"))?;
        if let Some(failure)=development {
            emit(json!({"event":"development-obstructed","error":failure,"anatomy":session.anatomy()}))?;
            return Err(err(failure))
        }
        let after=session.advance_native_readout(&HnaOccurrence {row_addresses:probe,history:vec![]},
            NativeEmissionReadout::LastRow)?.output.final_emission;
        let after_face=codec.render(&after).map_err(err)?;
        let altered=before.intervals.iter().zip(&after.intervals).filter(|(a,b)|a!=b).count();
        let mut state=app.begin(session,&args[4])?;
        let maps=session.anatomy().boundary_contact_maps;
        let generation=(||->Result<(),HnaSessionError> {
            for at in 0..cycles {
                if matches!(state.disposition,HnaTextDisposition::Completed{..}|HnaTextDisposition::Obstructed{..}) {break}
                material(session,source,&state.next_addresses(),out,words.len()+at+1)?;
                let step=app.step(session,&mut state)?;
                emit(json!({"event":"text-step","step":step,"returned":session.last_boundary_return()}))?;
                assert_eq!(session.anatomy().boundary_contact_maps,maps,"a matched self-return deposited again");
            }
            Ok(())
        })().err().map(|e|e.to_string());
        state.interrupt("declared application budget or delivery boundary");
        app.save(session,&state,&out.join("model.hna"),&out.join("text.json"))?;
        let result=json!({"schema":"holonics.hnp4.boundary-contact-result.v1","material_file":args[3],
            "material_octets":bytes.len(),"material_addresses":words.len(),"probe":args[4],
            "before":before_face,"after":after_face,"altered_terminal_intervals":altered,
            "returned":returned,"text":app.text(&state)?,"state":state,"anatomy":session.anatomy(),
            "generation_error":generation,"elapsed_ms":started.elapsed().as_millis()});
        publish_new(out.join("result.json"),|output|{
            serde_json::to_writer(&mut *output,&result).map_err(std::io::Error::other)?;
            output.write_all(b"\n")
        }).map_err(err)?;
        emit(result)
    })?;
    Ok(())
}

//! A text application using one resident native owner, live input acquisition, ordinary
//! self-occurrences, declared codec completion and a paired durable application/model artifact.
use holonics_hna::{
    publish_new, HnaCultivationAperture, HnaModel, HnaSession, HnaSessionError, HnaTextApplication,
    HnaTextContinuation, HnaTextDisposition,
};
use serde_json::json;
use std::{io::Write, path::Path, time::Instant};

fn emit(value: &serde_json::Value) -> Result<(), HnaSessionError> {
    let mut out = std::io::stdout().lock();
    serde_json::to_writer(&mut out, value)
        .map_err(|error| HnaSessionError::Base(format!("text output: {error}")))?;
    out.write_all(b"\n")
        .and_then(|_| out.flush())
        .map_err(|error| HnaSessionError::Base(format!("text output: {error}")))
}

fn drive(
    app: &HnaTextApplication,
    session: &mut HnaSession<'_, '_>,
    state: &mut HnaTextContinuation,
    source: &Path,
    output: &Path,
    cycles: usize,
) -> Result<(), HnaSessionError> {
    let mut completed = 0usize;
    for at in 0..cycles {
        if matches!(
            state.disposition,
            HnaTextDisposition::Completed { .. } | HnaTextDisposition::Obstructed { .. }
        ) {
            break;
        }
        let rows = state.next_addresses();
        if !session.missing_input_rows(&rows).is_empty() {
            let path = output.join(format!("input-{at:04}.safetensors"));
            match session.acquire_input_material(source, &rows, &path) {
                Ok(receipt) => emit(&json!({"event":"input-acquired","receipt":receipt}))?,
                Err(error) => {
                    state.disposition = HnaTextDisposition::AwaitingMaterial {
                        rows: session.missing_input_rows(&rows),
                    };
                    let _ = writeln!(
                        std::io::stderr().lock(),
                        "input acquisition refused: {error}"
                    );
                    break;
                }
            }
        }
        match app.step(session, state) {
            Ok(step) => {
                let advanced = step.selected.is_some();
                emit(&json!({"event":"text-step","step":step}))?;
                if advanced {
                    completed += 1;
                } else {
                    break;
                }
            }
            Err(error) => {
                let _ = writeln!(std::io::stderr().lock(), "text operation refused: {error}");
                break;
            }
        }
    }
    if completed == cycles {
        state.interrupt("declared application cycle budget exhausted");
    }
    Ok(())
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let args: Vec<_> = std::env::args().collect();
    let started = Instant::now();
    let (model,app,initial,source,output,cycles,prompt,observe)=match args.get(1).map(String::as_str) {
        Some("fresh") if args.len()==9=>{
            let source=Path::new(&args[3]);
            let shift=args[8].parse()?;
            let model=HnaModel::from_native_rest(&args[2],None,HnaCultivationAperture {learning_shift:shift,series_terms:14})?;
            let observe=match args[7].as_str() {"develop"=>false,"observe"=>true,_=>return Err("receiver must be develop or observe".into())};
            (model,HnaTextApplication::open(source)?,None,source,Path::new(&args[5]),args[6].parse::<usize>()?,Some(args[4].as_str()),observe)
        }
        Some("resume") if args.len()==6=>{
            let (model,app,mut state)=HnaTextApplication::load(Path::new(&args[2]))?;
            if matches!(state.disposition,HnaTextDisposition::Interrupted{..}) {state.resume()?;}
            let observe=state.observation_only;
            (model,app,Some(state),Path::new(&args[3]),Path::new(&args[4]),args[5].parse::<usize>()?,None,observe)
        }
        _=>return Err("fresh REST CODEC_SOURCE TEXT OUT_DIR CYCLES develop|observe SHIFT | resume TEXT_MANIFEST SOURCE OUT_DIR CYCLES".into()),
    };
    std::fs::create_dir_all(output)?;
    if output.join("model.hna").exists() || output.join("text.json").exists() {
        return Err("use a new output directory".into());
    }
    eprintln!("HNP4 text: mounting at {:?}", started.elapsed());
    model.with_session(|session| {
        let mut state=match initial {Some(state)=>state,None=>app.begin(session,prompt.expect("fresh prompt"))?};
        state.observation_only=observe;
        let delivery=drive(&app,session,&mut state,source,output,cycles).err().map(|error|error.to_string());
        if let Some(error)=&delivery {state.interrupt(format!("exterior delivery: {error}"));}
        app.save(session,&state,&output.join("model.hna"),&output.join("text.json"))?;
        let result=json!({"schema":"holonics.hnp4.text-result.v1","text":app.text(&state)?,"state":state,
            "anatomy":session.anatomy(),"elapsed_ms":started.elapsed().as_millis(),"delivery_error":delivery,"manifest":output.join("text.json")});
        publish_new(output.join("result.json"),|out|{
            serde_json::to_writer(&mut *out,&result).map_err(std::io::Error::other)?;out.write_all(b"\n")
        }).map_err(|error|HnaSessionError::Base(error.to_string()))?;
        emit(&result)
    })?;
    Ok(())
}

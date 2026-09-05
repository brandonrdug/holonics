//! Actual input-material extension and continuing native-domain control. Text is only an
//! exterior codec here; neither prepared material nor expected answers define the native return.
use holonics_hna::{
    read_checkpoint, AthenaTokenApplication, HnaModel, HnaOccurrence, HnaSessionError,
};
use serde_json::json;
use std::{path::Path, time::Instant};

const TEXTS: [&str; 2] = ["Describe a red cube.", "Correction: the cube is blue."];
fn main() -> Result<(), Box<dyn std::error::Error>> {
    let args: Vec<_> = std::env::args().collect();
    let started = Instant::now();
    match args.get(1).map(String::as_str) {
        Some("fresh") if args.len()==5 => {
            let model=HnaModel::from_native_rest(&args[2],None,holonics_hna::HnaCultivationAperture {
                learning_shift:16,series_terms:14,
            })?.with_input_material(&args[3])?;
            let codec=AthenaTokenApplication::open(Path::new(&args[4]))?;
            let occurrence=HnaOccurrence {row_addresses:codec.encode_turn(TEXTS[0])?,history:vec![]};
            model.with_session(|session| {
                let before=session.anatomy();
                let cycle=session.advance_native(&occurrence)?;
                let face=codec.render(&cycle.output.final_emission).map_err(|e|HnaSessionError::Base(e.to_string()))?;
                println!("{}",json!({"event":"fresh-native","text":TEXTS[0],"before":before,
                    "admission":cycle.admission,"face":face,"after":session.anatomy()}));
                Ok(())
            })?;
        }
        Some("request") if args.len()==3 => {
            let codec=AthenaTokenApplication::open(Path::new(&args[2]))?;
            println!("{}",serde_json::to_string(&holonics_hna::HnaStreamRequest {
                schema:holonics_hna::HNA_STREAM_REQUEST_SCHEMA.into(),
                command:holonics_hna::HnaStreamCommand::AdvanceNative {
                    occurrence:HnaOccurrence {row_addresses:codec.encode_turn(TEXTS[0])?,history:vec![]},
                    full_emission:false,
                }
            })?);
        }
        Some("prepare") if args.len()==5 => {
            let model=HnaModel::from_checkpoint(&args[2],None)?;
            let codec=AthenaTokenApplication::open(Path::new(&args[3]))?;
            let mut addresses=Vec::new();
            for text in TEXTS { addresses.extend(codec.encode_turn(text)?); }
            let receipt=model.acquire_input_material(Path::new(&args[3]),&addresses,Path::new(&args[4]))?;
            println!("{}",serde_json::to_string(&receipt)?);
        }
        Some("exercise") if args.len()==7 => {
            let model=HnaModel::from_checkpoint(&args[2],None)?.with_input_material(&args[3])?;
            let codec=AthenaTokenApplication::open(Path::new(&args[4]))?;
            let directory=Path::new(&args[5]); std::fs::create_dir_all(directory)?;
            let ordinary=model.declared_occurrences()[0].occurrence.clone();
            let text_occurrences:Vec<_>=TEXTS.iter().map(|text|codec.encode_turn(text).map(|row_addresses|
                HnaOccurrence {row_addresses,history:Vec::new()})).collect::<Result<_,_>>()?;
            eprintln!("HNP4: material acquired; mounting at {:?}",started.elapsed());
            model.with_session(|session| {
                let before=session.anatomy();
                assert!(session.advance(&text_occurrences[0]).is_err(),"old family must not silently expand");
                assert_eq!(session.anatomy(),before);
                let old=session.advance(&ordinary)?;
                session.checkpoint(directory.join("old-family-after.hna"))?;
                let (_,actual)=read_checkpoint(directory.join("old-family-after.hna"))?;
                let (_,expected)=read_checkpoint(&args[6])?;
                assert!(actual==expected,"input extension changed the old complete successor");
                println!("{}",json!({"event":"old-family-control","complete_successor_equal":true,
                    "generation":old.final_emission.generation,"anatomy":session.anatomy()}));
                let invalid=HnaOccurrence {row_addresses:vec![u32::MAX],history:vec![]};
                let before=session.anatomy();
                assert!(matches!(session.advance_native(&invalid),Err(HnaSessionError::MissingInput{..})));
                assert_eq!(session.anatomy(),before);
                for (text,occurrence) in TEXTS.iter().zip(&text_occurrences) {
                    let cycle=session.advance_native(occurrence)?;
                    assert_eq!(cycle.admission.original_family_class,None);
                    let face=codec.render(&cycle.output.final_emission).map_err(|e|HnaSessionError::Base(e.to_string()))?;
                    println!("{}",json!({"event":"native-text-occurrence","text":text,"admission":cycle.admission,
                        "face":face,"anatomy":session.anatomy()}));
                }
                session.checkpoint(directory.join("developed.hna"))?;
                session.advance_native(&text_occurrences[0])?;
                session.checkpoint(directory.join("expected-after.hna"))?;
                Ok(())
            })?;
        }
        Some("resume") if args.len()==5 => {
            let model=HnaModel::from_checkpoint(&args[2],None)?;
            let codec=AthenaTokenApplication::open(Path::new(&args[3]))?;
            let occurrence=HnaOccurrence {row_addresses:codec.encode_turn(TEXTS[0])?,history:vec![]};
            let output=Path::new(&args[2]).with_file_name("resumed-after.hna");
            model.with_session(|session| {
                session.advance_native(&occurrence)?;
                session.checkpoint(&output)?;
                let (_,actual)=read_checkpoint(&output)?;
                let (_,expected)=read_checkpoint(&args[4])?;
                assert!(actual==expected,"extended native continuation differs after process restart");
                println!("{}",json!({"event":"extended-process-continuation","complete_successor_equal":true,
                    "anatomy":session.anatomy()}));
                Ok(())
            })?;
        }
        _=>return Err("prepare CHECKPOINT SOURCE_ROOT NEW.safetensors | exercise CHECKPOINT MATERIAL SOURCE_ROOT OUT_DIR OLD_EXPECTED | resume DEVELOPED SOURCE_ROOT EXPECTED".into()),
    }
    eprintln!("HNP4 input control finished at {:?}", started.elapsed());
    Ok(())
}

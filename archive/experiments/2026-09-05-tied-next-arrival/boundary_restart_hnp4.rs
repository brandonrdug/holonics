//! Complete-state native restart control, not an application quality experiment.
use holonics_hna::{
    read_checkpoint, HnaModel, HnaOccurrence, HnaSessionError, NativeEmissionReadout,
};
use serde_json::json;
use std::path::Path;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let args: Vec<_> = std::env::args().collect();
    let (source, remounted, expected, actual) = match args.get(1).map(String::as_str) {
        Some("reference") if args.len() == 5 => (&args[2], Some(&args[3]), &args[4], None),
        Some("resume") if args.len() == 5 => (&args[2], None, &args[3], Some(&args[4])),
        _ => {
            return Err(
                "reference SOURCE REMOUNTED EXPECTED | resume REMOUNTED EXPECTED ACTUAL".into(),
            )
        }
    };
    let (_, original) = read_checkpoint(source)?;
    let boundary = original
        .boundary
        .as_ref()
        .ok_or("not a boundary-contact model")?;
    let prior = original
        .header
        .previous_context
        .as_ref()
        .ok_or("no retained input word")?;
    let predicted = boundary
        .last_face
        .as_ref()
        .ok_or("no pending face")?
        .address;
    // Deliberate unmatched receiver control from actual already-present input material. This
    // choice belongs to the test apparatus; the production law never chooses its next arrival.
    let received = prior
        .iter()
        .copied()
        .find(|value| *value != predicted)
        .ok_or("no unmatched held input")?;
    let mut word = prior.clone();
    word.push(received);
    let model = HnaModel::from_checkpoint(source, None)?;
    model.with_session(|session| {
        if let Some(path)=remounted {
            session.checkpoint(Path::new(path))?;
            let (_,restored)=read_checkpoint(path)?;
            assert!(restored==original,"fresh mount altered complete native state");
        }
        let maps=session.anatomy().boundary_contact_maps;
        session.advance_native_readout(&HnaOccurrence {row_addresses:word,history:vec![]},NativeEmissionReadout::LastRow)?;
        assert_eq!(session.anatomy().boundary_contact_maps,maps+1,"the unmatched held-material control did not develop");
        let path=actual.unwrap_or(expected);
        session.checkpoint(Path::new(path))?;
        if actual.is_some() {
            let (_,reference)=read_checkpoint(expected)?;
            let (_,continued)=read_checkpoint(path)?;
            assert!(reference==continued,"process-separated learned successors differ");
        }
        println!("{}",json!({"event":"boundary-restart","mode":args[1],"full_state_equal":true,
            "received":received,"returned":session.last_boundary_return(),"anatomy":session.anatomy()}));
        Ok::<_,HnaSessionError>(())
    })?;
    Ok(())
}

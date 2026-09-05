//! Receiver-only projection control on the actual cultivated native model.
use holonics_hna::{HnaModel,NativeEmissionReadout as Readout,NativeEmissionProjection,read_checkpoint};
use serde_json::json;
use std::{path::Path,time::Instant};

fn main()->Result<(),Box<dyn std::error::Error>> {
    let args:Vec<_>=std::env::args().collect();
    if args.len()!=4 {return Err("CHECKPOINT FULL_REFERENCE NEW_CHECKPOINT".into());}
    let (_,reference)=read_checkpoint(&args[2])?;
    let terminal=reference.terminal_carrier.as_ref().ok_or("reference lacks its terminal state")?;
    let expected_last:Vec<_>=terminal.sections.iter().flat_map(|section|
        section.intervals[(section.rows-1)*section.width..].iter().copied()).collect();
    let source_rows=terminal.rows;
    let model=HnaModel::from_checkpoint(&args[1],None)?;
    let occurrence=model.declared_occurrences()[0].occurrence.clone();
    model.with_session(|session| {
        let before=session.transfer_census();let start=Instant::now();
        let cycle=session.advance_native_readout(&occurrence,Readout::LastRow)?;
        let elapsed=start.elapsed().as_millis();let after=session.transfer_census();
        assert_eq!(cycle.output.final_emission.rows,1);
        assert_eq!(cycle.output.final_emission.projection,
            Some(NativeEmissionProjection::LastRow {source_rows,row:source_rows-1}));
        assert_eq!(cycle.output.final_emission.intervals,expected_last);
        session.checkpoint(Path::new(&args[3]))?;
        let (_,projected)=read_checkpoint(&args[3])?;
        assert!(projected==reference,"readout changed complete native successor");
        println!("{}",json!({"event":"projected-productive","complete_successor_equal":true,
            "source_rows":source_rows,"returned_rows":1,"egress_octets":after.egress_section_octets-before.egress_section_octets,
            "elapsed_ms":elapsed,"anatomy":session.anatomy()}));
        // Warmed fixed-morphology comparisons answer readback cost only; they are not a learner.
        let mut last=None;
        for (at,receiver) in [Readout::Complete,Readout::Complete,Readout::LastRow,Readout::Complete].into_iter().enumerate() {
            let before=session.transfer_census();let start=Instant::now();
            let cycle=session.observe_native_readout(&occurrence,receiver)?;
            let elapsed=start.elapsed().as_millis();let after=session.transfer_census();
            let emission=cycle.output.final_emission;
            let current=emission.intervals[(emission.rows-1)*emission.width..].to_vec();
            if let Some(expected)=&last {assert_eq!(&current,expected);}
            last=Some(current);
            println!("{}",json!({"event":"readout-comparison","ordinal":at,"receiver":format!("{receiver:?}"),
                "rows":emission.rows,"egress_octets":after.egress_section_octets-before.egress_section_octets,
                "elapsed_ms":elapsed,"generation":session.anatomy().generation}));
        }
        Ok(())
    })?;
    Ok(())
}

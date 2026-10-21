//! One bounded synthetic native-prediction/contact control; no dataset.
use super::*;
use holonics::hnn::Charts;
use holonics::hnn::reference::native_context::NativeExecutionChart;
#[test]
fn native_producer_contact()->Result<()>{
    let started=Instant::now();
    let reference=port();
    let cache=std::env::var_os("V93_NATIVE_CODE_SEED").map(std::path::PathBuf::from);
    let checkpoint=if let Some(path)=cache.as_ref().filter(|p|p.exists()){
        let (cp,hash)=Checkpoint::load(path.to_str().ok_or("CODE seed path")?,READ_BUDGET)?;
        println!("REUSED_SYNTHETIC20_SEED sha={hash}");cp
    }else{
        let mut cp=fresh_family_local_checkpoint_at_representation(16384,ObservedEpochDepositionScope::LocalReceivingReturnWithHeldMap,true)?;
        let (_,_,pairing)=cp.declaration()?;cp.stream.select_source_framing_prepared_input(&pairing)?;
        let classes:Vec<usize>=(0..20).map(|j|j%4).collect();
        cp.stream.receive(&reference,&pairing,&classes)?;
        if let Some(path)=&cache{cp.publish(path.to_str().ok_or("CODE seed path")?)?;}
        println!("CREATED_SYNTHETIC20_SEED actual20 paired_forward40 paired_return40");cp
    };
    let (_,_,pairing)=checkpoint.declaration()?;
    assert_eq!(checkpoint.stream.accepted_cells()?,20);assert_eq!(checkpoint.stream.pending_classes().len(),0);
    let mut resolved=checkpoint.stream.resident().clone();
    // ONE predeclared qualification variant. Lossless representation refinement happens
    // before a prediction exists; no coarse result is rebound or given a larger step.
    resolved.refine_contact_grain(24)?;
    let resident=&resolved;
    let before=resident.continuing_state(0)?;
    let boundary=PairedObservation::admit(resident.field(),resident.constitution(),&pairing)?;
    let targets=boundary.encode(&[1])?;
    let predictor=reference.prepare_native_current_prediction(resident,NativeExecutionChart::ExactUnsplit,64)?;
    let reading=predictor.reading();
    assert_eq!(reading.law,"native-current-prediction-v1");
    let score=predictor.score(&targets)?;
    let drawn=predictor.draw(0,&rat(1,2))?;
    println!("NATIVE_F_SOURCE reading={reading:?} score={score:?} draw={drawn:?}");
    let returned=predictor.observe(&targets)?;
    assert_eq!(returned.reading(),&reading);assert_eq!(returned.scores(),score);
    let mut charts=Charts::new();
    let publication=returned.publish_contact_carry(&mut charts)?;
    assert_eq!(publication.constitution.receiving_map(2),resident.constitution().receiving_map(2));
    let changed=(0..resident.field().contacts().len()).any(|a|
        publication.constitution.contact_storage(a)!=resident.constitution().contact_storage(a)
        ||publication.constitution.contact_stiffness(a)!=resident.constitution().contact_stiffness(a)
        ||publication.constitution.contact_dissipation(a)!=resident.constitution().contact_dissipation(a));
    println!("NATIVE_CONTACT changed={changed} alignment={:?} error={:?} paired_readout={:?} before={:?} committed={:?} work={:?} contact_moves={} elapsed_ns={}",publication.actual_alignment,publication.actual_error_charge,publication.paired_readout_norm,publication.continuation.before,publication.continuation.committed,publication.continuation.deposition_work,publication.continuation.material.len(),started.elapsed().as_nanos());
    assert!(changed,"D5 requires actual factor publication, not a nonzero adjoint or receiving-only success");
    assert!(publication.actual_alignment>publication.actual_error_charge);
    assert_eq!(resident.continuing_state(0)?,before);
    Ok(())
}

#[test]
fn native_context_event_cold_and_future()->Result<()>{
    use holonics::hnn::reference::prepared_input::ContextChart;
    let started=Instant::now();let reference=port();let work_before=holonics::hnn::word::work::read();
    let cache=std::env::var("V93_NATIVE_CODE_SEED")?;let (seed,_)=Checkpoint::load(&cache,READ_BUDGET)?;
    let old=seed.stream.resident();let field=old.field().clone();let (_,_,pairing)=seed.declaration()?;
    // Declared CODE calibration prior, not a newly learned native R path or a migrated model.
    let mut native=reference.mount_with(&field,&Current::at_rest(&field),old.constitution().clone())?;
    let empty=PairedObservation::admit(&field,native.constitution(),&pairing)?.encode(&[])?;
    reference.ingest(&mut native,None,&empty)?;native.refine_contact_grain(24)?;
    native.select_native_current_prepared_input(&pairing)?;
    assert_eq!(native.prepared_input().unwrap().context_chart(),ContextChart::LaggedReceiverBoundaryV1);
    assert!(native.prepared_input().unwrap().material().parts().iter().all(|p|p.normal().len()==90&&p.observations()==0));
    let mut frozen=native.clone();frozen.freeze_prepared_forecast()?;
    let mut crib=ObservedCrib::new(0);let mut frozen_crib=crib.clone();
    let first=reference.observe_native_current_contact(&mut native,&mut crib,&pairing,1,64)?;
    let frozen_first=reference.continue_native_current_forecast(&mut frozen,&mut frozen_crib,&pairing,1,64)?;
    assert_eq!(first.prediction,frozen_first.prediction);
    reference.observe_native_current_contact(&mut native,&mut crib,&pairing,2,64)?;
    reference.continue_native_current_forecast(&mut frozen,&mut frozen_crib,&pairing,2,64)?;
    assert_eq!(native.constitution().receiving_map(2),frozen.constitution().receiving_map(2));
    let a=reference.prepare_native_current_prediction(&native,NativeExecutionChart::ExactUnsplit,64)?.reading();
    let b=reference.prepare_native_current_prediction(&frozen,NativeExecutionChart::ExactUnsplit,64)?.reading();
    assert_ne!(a.waves,b.waves,"actual contact factors must affect a future native F with R/M held");
    assert!(a.masses[0].iter().zip(&b.masses[0]).any(|(a,b)|a.upper<b.lower||b.upper<a.lower),"future F effect must exceed its numerical enclosure");
    println!("NATIVE_F_FUTURE learned={:?} frozen={:?}",a.waves,b.waves);
    for class in [3,0]{reference.observe_native_current_contact(&mut native,&mut crib,&pairing,class,64)?;}
    assert_eq!(native.prepared_input().unwrap().frontiers(),(4,0,0));
    let formed=native.prepared_input().unwrap().material().observations();let pending=native.prepared_input().unwrap().outstanding().len();
    println!("NATIVE_CONTEXT90 formed={formed} pending={pending} material_refusal={:?}",native.prepared_input().unwrap().material_refusal());
    assert!(formed>0);assert_eq!(formed+pending as u64,2);
    for (part,m) in native.prepared_input().unwrap().material().parts().iter().enumerate(){println!("NATIVE_M_PART part={part} observations={} H00={:?} B00={:?} M00={:?} error={:?}",m.observations(),m.normal()[0][0],m.cross()[0][0],m.applied()[0][0],m.coefficient_error_upper());}
    let state=native.continuing_state(0)?;let text=state.to_text();let parsed=ContinuingState::from_text(&text,READ_BUDGET)?;
    let cold=reference.mount_continued(&field,native.current(),native.constitution().clone(),&parsed)?;
    assert_eq!(cold.continuing_state(0)?,state);
    assert_eq!(reference.prepare_native_current_prediction(&native,NativeExecutionChart::ExactUnsplit,64)?.reading(),reference.prepare_native_current_prediction(&cold,NativeExecutionChart::ExactUnsplit,64)?.reading());
    let before=native.continuing_state(0)?;let crib_before=crib.clone();
    assert!(reference.observe_native_current_contact(&mut native,&mut crib,&pairing,4,64).is_err());
    assert_eq!(native.continuing_state(0)?,before);assert_eq!(crib,crib_before);
    let material=native.prepared_input().unwrap().material().clone();native.freeze_prepared_forecast()?;native.begin_hypothesized_output()?;
    for class in [1,0]{reference.continue_native_current_forecast(&mut native,&mut crib,&pairing,class,64)?;}
    assert_eq!(native.prepared_input().unwrap().frontiers(),(4,0,2));assert_eq!(native.prepared_input().unwrap().material(),&material);
    println!("NATIVE_CONTEXT_WORK {:?}",holonics::hnn::word::work::read().since(work_before).unwrap());
    println!("NATIVE_CONTEXT90 actual4 hypothetical2 original_returns2 fresh90=true cold_exact=true input_rollback=true elapsed_ns={} D3_R_publication_UNJOINED=true",started.elapsed().as_nanos());
    Ok(())
}

#[test]
fn native_charted_contact_refuses()->Result<()>{
    let reference=port();let cache=std::env::var("V93_NATIVE_CODE_SEED")?;let (seed,_)=Checkpoint::load(&cache,READ_BUDGET)?;
    let resident=seed.stream.resident();let pairing=seed.declaration()?.2;
    let before=resident.continuing_state(0)?;let boundary=PairedObservation::admit(resident.field(),resident.constitution(),&pairing)?;
    let target=boundary.encode(&[1])?;let producer=reference.prepare_native_current_prediction(resident,NativeExecutionChart::Declared,64)?;
    assert!(producer.score(&boundary.encode(&[])?) .is_err());let actual=producer.observe(&target)?;
    let mut charts=Charts::new();let before_charts=charts.clone();
    let error=actual.publish_contact_carry(&mut charts).err().ok_or("charted paired contact must retain guard")?;
    assert!(format!("{error:?}").contains("exact unsplit"));assert_eq!(charts,before_charts);assert_eq!(resident.continuing_state(0)?,before);
    println!("NATIVE_CHARTED_GUARD exact_refusal={error:?} immutable=true no_fallback=true");Ok(())
}

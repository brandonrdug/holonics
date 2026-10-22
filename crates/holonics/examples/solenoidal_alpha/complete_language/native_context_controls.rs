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


/// Distinct qualification from 7c3e: fresh native R -> NEW contact -> next R suffix.
/// Deliberately independent of V93_NATIVE_CODE_SEED and all old fitted material.
#[test]
fn native_fresh_r_contact_successor_connected()->Result<()>{
    use holonics::hnn::word::work;
    struct FinalCount;
    impl Drop for FinalCount {fn drop(&mut self){
        let c=work::process_native_calls();let total=c.forward_attempts+c.response_attempts+c.return_attempts+c.response_return_attempts;
        let text=format!("{{\"final\":true,\"total_attempts\":{total},\"forward_constructors\":{},\"response_companions\":{},\"actual_returns\":{},\"fresh_returns\":{}}}\n",c.forward_attempts,c.response_attempts,c.return_attempts,c.response_return_attempts);
        println!("NATIVE_PROCESS_FINAL {text}");
        if let Some(path)=std::env::var_os("V93_NATIVE_COUNT_PATH"){std::fs::write(path,text).expect("durable native count receipt");}
    }}
    let _final_count=FinalCount;
    let limit=std::env::var("V93_NATIVE_ATTEMPT_LIMIT")?.parse()?;
    work::limit_process_native_attempts(limit);
    let started=Instant::now();let reference=port();
    let (field,mut initial,pairing)=declaration_with_input_context(16384,true,true)?;
    initial.bind_family_local_receiving_return(2)?;initial.bind_bounded_receiving_representation(2)?;
    let mut resident=reference.mount_declared_receiving_law(&field,&Current::at_rest(&field),initial,holonics::hnn::receiving::ReceivingLaw::RetainedFibreV1)?;
    let empty=PairedObservation::admit(&field,resident.constitution(),&pairing)?.encode(&[])?;
    reference.ingest(&mut resident,None,&empty)?;
    resident.refine_contact_grain(24)?; // ONE fixed lossless representation, before any prediction.
    resident.select_native_current_prepared_input(&pairing)?;
    assert!(resident.constitution().receiving_map(2).unwrap().entries().iter().all(num_traits::Zero::is_zero));
    let opening=resident.constitution().clone();
    let mut stream=ObservedStream::new(resident,ObservedCrib::new(0),ObservedEpochDepositionScope::LocalReceivingReturnWithHeldMap)?;
    fn cold(reference:&Reference,stream:&ObservedStream,opening:&Constitution)->Result<ObservedStream>{
        let before=stream.resident().continuing_state(0)?;
        let parsed=ContinuingState::from_text(&before.to_text(),READ_BUDGET)?;
        let field=stream.resident().field();
        let resident=reference.mount_continued(field,&Current::at_rest(field),opening.clone(),&parsed)?;
        assert_eq!(resident.continuing_state(0)?,before);
        let published=stream.crib().next_position();
        let crib=ObservedCrib::from_unplaced_checkpoint(field,resident.current(),published,&stream.crib().unplaced_checkpoint()?)?;
        let result=ObservedStream::restore_checkpoint(resident,crib,&stream.pending_checkpoint())?;
        assert_eq!(result.pending_checkpoint(),stream.pending_checkpoint());Ok(result)
    }
    let data:Vec<usize>=(0..30).map(|j|j%4).collect();
    let mut one_shot=stream.clone();
    stream.receive_native_current(&reference,&pairing,&data[..6],64)?;
    assert_eq!(stream.accepted_cells()?,6);assert_eq!(stream.pending_classes().len(),6);
    stream=cold(&reference,&stream,&opening)?;
    println!("NATIVE_CONNECTED_CUT accepted6/published0/pending6 cold_exact=true attempts={:?}",work::process_native_calls());
    let before_r=stream.resident().continuing_state(0)?;
    let first=match stream.receive_native_current(&reference,&pairing,&data[6..10],64){Ok(x)=>x,Err(e)=>{
        assert_eq!(stream.resident().continuing_state(0)?,before_r);assert_eq!(stream.pending_classes(),&data[..6]);
        println!("NATIVE_CONNECTED_REFUSAL stage=fresh_R actual_source0 accepted6/pending6 immutable=true error={e:?}");return Err(e.into());}};
    assert_eq!(first.len(),1);assert_eq!(first[0].events.len(),10);
    one_shot.receive_native_current(&reference,&pairing,&data[..10],64)?;
    assert_eq!(one_shot.resident().continuing_state(0)?,stream.resident().continuing_state(0)?);
    assert_eq!(one_shot.pending_checkpoint(),stream.pending_checkpoint());assert_eq!(one_shot.crib(),stream.crib());
    let r_changed=stream.resident().constitution().receiving_map(2)!=opening.receiving_map(2);
    println!("NATIVE_CONNECTED_FIRST_R changed={r_changed} publication={:?} source={}/{} attempts={:?}",first[0].publication,first[0].start_source,first[0].end_source,work::process_native_calls());
    assert!(r_changed,"positive native R causal control remains unestablished if only Held/no motion");
    let before_contact=stream.resident().continuing_state(0)?;let material_before=stream.resident().constitution().clone();
    let e=stream.observe_native_current_contact(&reference,&pairing,data[10],64)?;
    let contact=e.contact.as_ref().ok_or("actual contact receipt")?;
    let changed=(0..field.contacts().len()).any(|a|contact.constitution.contact_storage(a)!=material_before.contact_storage(a)||contact.constitution.contact_stiffness(a)!=material_before.contact_stiffness(a)||contact.constitution.contact_dissipation(a)!=material_before.contact_dissipation(a));
    assert_eq!(contact.constitution.receiving_map(2),material_before.receiving_map(2));
    println!("NATIVE_CONNECTED_NEW_CONTACT source10/11 factors_changed={changed} alignment={:?} error={:?} work={:?} attempts={:?}",contact.actual_alignment,contact.actual_error_charge,contact.continuation.deposition_work,work::process_native_calls());
    assert!(changed,"fresh native contact factor effect is required, never forced");
    assert_ne!(stream.resident().continuing_state(0)?,before_contact);
    let second=stream.receive_native_current(&reference,&pairing,&data[11..20],64)?;
    assert_eq!(second.len(),1);assert_eq!(second[0].events.len(),9);assert_eq!(second[0].contact_prefix_cells,1);
    assert_eq!((second[0].start_source,second[0].end_source),(11,20));
    let material=stream.resident().prepared_input().unwrap();
    println!("NATIVE_CONNECTED_M actual={:?} formed={} pending={} range_refusal={:?}",material.frontiers(),material.material().observations(),material.outstanding().len(),material.material_refusal());
    stream=cold(&reference,&stream,&opening)?;
    let (mut warm,mut warm_crib)=stream.native_current_query_fork(&reference,&pairing,64)?;
    warm.begin_hypothesized_output()?;
    let state=warm.continuing_state(0)?;let parsed=ContinuingState::from_text(&state.to_text(),READ_BUDGET)?;
    let mut restored=reference.mount_continued(&field,&Current::at_rest(&field),opening.clone(),&parsed)?;
    let mut cold_crib=ObservedCrib::from_unplaced_checkpoint(&field,restored.current(),warm_crib.next_position(),&warm_crib.unplaced_checkpoint()?)?;
    assert_eq!(restored.continuing_state(0)?,state);
    let plastic=warm.constitution().clone();let m=warm.prepared_input().unwrap().material().clone();
    for (i,key) in [rat(1,7),rat(2,7),rat(3,7),rat(4,7)].iter().enumerate(){
        let a=reference.release_native_current_forecast(&mut warm,&mut warm_crib,&pairing,key,64)?;
        let b=reference.release_native_current_forecast(&mut restored,&mut cold_crib,&pairing,key,64)?;
        assert_eq!(a.prediction,b.prediction);assert_eq!(a.scores,b.scores);assert_eq!(a.draw,b.draw);assert_eq!(a.selected_class,b.selected_class);
        assert_eq!(warm.continuing_state(0)?,restored.continuing_state(0)?);
        assert_eq!(warm.constitution(),&plastic);assert_eq!(warm.prepared_input().unwrap().material(),&m);
        println!("NATIVE_CONNECTED_FROZEN decision={i} class={} source={} draw={:?}",a.selected_class,a.prediction.source_cells,a.draw);
    }
    assert_eq!(warm.prepared_input().unwrap().frontiers(),(20,0,4));
    assert_eq!(stream.accepted_cells()?,20);assert_eq!(stream.pending_classes().len(),0);
    println!("NATIVE_CONNECTED_PASS actual20 fresh_R_then_NEWcontact_then_R9 cold_pending6=true same_producer_four_frozen=true elapsed_ns={} attempts={:?}",started.elapsed().as_nanos(),work::process_native_calls());
    Ok(())
}

#[test]
#[ignore="isolated fixed CODE/attempt envelope"]
fn native_quadratic_work_connected_prefix()->Result<()>{
    use holonics::hnn::word::work;
    struct Meter;impl Drop for Meter{fn drop(&mut self){let c=work::process_native_calls();let t=c.forward_attempts+c.response_attempts+c.return_attempts+c.response_return_attempts;let s=format!("{{\"final\":true,\"total_attempts\":{t},\"forward_constructors\":{},\"response_companions\":{},\"actual_returns\":{},\"fresh_returns\":{}}}\n",c.forward_attempts,c.response_attempts,c.return_attempts,c.response_return_attempts);println!("QUADRATIC_CONNECTED_FINAL {s}");if let Some(p)=std::env::var_os("V93_NATIVE_COUNT_PATH"){std::fs::write(p,s).unwrap();}}}
    let _meter=Meter;work::limit_process_native_attempts(std::env::var("V93_NATIVE_ATTEMPT_LIMIT")?.parse()?);
    let started=Instant::now();let reference=port();let(field,mut initial,pairing)=declaration_with_input_context(16384,true,true)?;initial.bind_family_local_receiving_return(2)?;initial.bind_bounded_receiving_representation(2)?;
    let mut resident=reference.mount_declared_receiving_law(&field,&Current::at_rest(&field),initial,holonics::hnn::receiving::ReceivingLaw::RetainedFibreV1)?;
    let empty=PairedObservation::admit(&field,resident.constitution(),&pairing)?.encode(&[])?;reference.ingest(&mut resident,None,&empty)?;resident.refine_contact_grain(24)?;resident.select_native_quadratic_work_prepared_input(&pairing)?;
    assert!(resident.constitution().receiving_map(2).unwrap().entries().iter().all(num_traits::Zero::is_zero));
    let opening=resident.constitution().clone();let mut stream=ObservedStream::new(resident,ObservedCrib::new(0),ObservedEpochDepositionScope::LocalReceivingReturnWithHeldMap)?;
    fn cold(reference:&Reference,stream:&ObservedStream,opening:&Constitution)->Result<ObservedStream>{
        let state=stream.resident().continuing_state(0)?;let parsed=ContinuingState::from_text(&state.to_text(),READ_BUDGET)?;let field=stream.resident().field();let resident=reference.mount_continued(field,&Current::at_rest(field),opening.clone(),&parsed)?;assert_eq!(resident.continuing_state(0)?,state);
        let crib=ObservedCrib::from_unplaced_checkpoint(field,resident.current(),stream.crib().next_position(),&stream.crib().unplaced_checkpoint()?)?;
        let text=stream.pending_checkpoint();assert!(text.starts_with("observed-stream-pending-native-current-v2"));
        let changed=text.replacen("1048576","1048575",1);assert!(ObservedStream::restore_checkpoint(resident.clone(),crib.clone(),&changed).is_err());
        let restored=ObservedStream::restore_checkpoint(resident,crib,&text)?;assert_eq!(restored.pending_checkpoint(),text);Ok(restored)
    }
    let data:Vec<_>=(0..30).map(|i|i%4).collect();stream.receive_native_current(&reference,&pairing,&data[..6],64)?;stream=cold(&reference,&stream,&opening)?;
    println!("QUADRATIC_PENDING_COLD accepted6/published0/pending6 native_policy_resources_exact=true mismatch_refused=true");
    let before=stream.resident().continuing_state(0)?;let pending=stream.pending_checkpoint();let mut seen7=false;let mut observed=0;
    let outcome=stream.receive_native_current_diagnosed(&reference,&pairing,&data[6..10],64,&mut |e|{
        observed+=1;
        if e.prediction.source_cells==7{
            let receipt=e.preparation.as_ref().expect("source7 actual preparation");let r=receipt.quadratic_work.as_ref().expect("new private work carrier");
            let captured=Rat::new("51564025503142025724633702171333565477839602018262442180103416381733773829048987453642701117582441066181057391566130098304758509976933898410653964848328685074019118599927583053254770629577698244842880393017724348808904362643832108931305119651518354414673594465825438666030285830918268463504266119585360990590528111".parse().unwrap(),"22047267733340713048940158349214507467643823909519974157522241104760090223066576032924786842675813207198282257472108484449990867834675484277115873809660291195993146826927099026296864779242370390778269105246036983513853630109287239444143229113361694201038019485686046577441025195335936000000000000000000000000000000".parse().unwrap());assert_eq!(receipt.work,captured);
            assert_eq!(r.metric,rat(1,2));assert!(r.charged_arithmetic_bits<=1048576);
            let cross=&r.metric*integer(2)*r.old.iter().zip(&r.added).map(|(m,a)|m*a).sum::<Rat>();let quadratic=&r.metric*r.added.iter().map(|a|a*a).sum::<Rat>();assert_eq!(cross,receipt.cross);assert_eq!(quadratic,receipt.quadratic);assert_eq!(&cross+&quadratic,receipt.work);
            assert_eq!((receipt.work.numer().bits(),receipt.work.denom().bits()),(1043,1041));assert!(receipt.work<integer(65536));assert!(receipt.closes());
            assert!(r.added.iter().all(|x|x.numer().bits()<=1024&&x.denom().bits()<=1024));
            println!("QUADRATIC_REAL_CUT7 staged_not_published=true source={} metric={:?} old={:?} added={:?} control={:?} work={:?} cross={:?} quadratic={:?} derived_bound={}/{} bitwork={}",r.source_cells,r.metric,r.old,r.added,r.control,receipt.work,receipt.cross,receipt.quadratic,r.numerator_bound_bits,r.denominator_bound_bits,r.charged_arithmetic_bits);seen7=true;
        }
        // Exact producer feature witness for any later unchanged EpochFlow packing refusal.
        if let Some((at,x))=e.prediction.features[0].iter().enumerate().find(|(_,x)|{let z=x.denom().trailing_zeros().unwrap();(x.denom()>>z as usize)!=num_bigint::BigInt::from(1)}){
            println!("QUADRATIC_NATIVE_FEATURE source={} coordinate={at} value={x} declared_feature_divisor=1",e.prediction.source_cells);
        }
    });
    match outcome{
        Err(e)=>{assert!(seen7,"the reviewed wide-work case must be reached before any later refusal");assert_eq!(stream.resident().continuing_state(0)?,before);assert_eq!(stream.pending_checkpoint(),pending);println!("QUADRATIC_LATER_REFUSAL staged_events={observed} cut7_accepted=true whole_delivery_rollback=true error={e:?}");return Err(e.into());},
        Ok(events)=>{assert!(seen7);assert_eq!(events.len(),1);println!("QUADRATIC_FIRST_R publication={:?} reuse={:?}",events[0].publication,stream.resident().native_rank_reuse_reading());}
    }
    stream=cold(&reference,&stream,&opening)?;
    let c=work::process_native_calls();let used=c.forward_attempts+c.response_attempts+c.return_attempts+c.response_return_attempts;
    // Fixed conservative branch reservation. Never start a suffix that cannot fit.
    let limit=std::env::var("V93_NATIVE_ATTEMPT_LIMIT")?.parse::<u64>()?;
    if limit-used<180{println!("QUADRATIC_SUCCESSOR_NOT_RUN remaining_attempts={} required_conservative180 elapsed_ns={}",limit-used,started.elapsed().as_nanos());return Ok(());}
    let event=stream.observe_native_current_contact(&reference,&pairing,data[10],64)?;println!("QUADRATIC_CONTACT source10_new=true changed_receipt={:?}",event.contact.as_ref().map(|x|&x.publication));
    stream.receive_native_current(&reference,&pairing,&data[11..20],64)?;stream=cold(&reference,&stream,&opening)?;
    let(mut fork,mut crib)=stream.native_current_query_fork(&reference,&pairing,64)?;fork.begin_hypothesized_output()?;let material=fork.constitution().clone();let m=fork.prepared_input().unwrap().material().clone();
    for key in [rat(1,7),rat(2,7),rat(3,7),rat(4,7)]{reference.release_native_current_forecast(&mut fork,&mut crib,&pairing,&key,64)?;assert_eq!(fork.constitution(),&material);assert_eq!(fork.prepared_input().unwrap().material(),&m);}
    println!("QUADRATIC_CONNECTED_SUCCESSOR_PASS actual20 four_frozen=true elapsed_ns={}",started.elapsed().as_nanos());Ok(())
}

#[test]
#[ignore="isolated fixed CODE/attempt envelope"]
fn native_rational_flow_connected_prefix()->Result<()>{
    use holonics::hnn::word::work;
    struct Meter;impl Drop for Meter{fn drop(&mut self){let c=work::process_native_calls();let t=c.forward_attempts+c.response_attempts+c.return_attempts+c.response_return_attempts;let s=format!("{{\"final\":true,\"total_attempts\":{t},\"forward_constructors\":{},\"response_companions\":{},\"actual_returns\":{},\"fresh_returns\":{}}}\n",c.forward_attempts,c.response_attempts,c.return_attempts,c.response_return_attempts);println!("RATIONAL_CONNECTED_FINAL {s}");if let Some(p)=std::env::var_os("V93_NATIVE_COUNT_PATH"){std::fs::write(p,s).unwrap();}}}
    let _meter=Meter;work::limit_process_native_attempts(std::env::var("V93_NATIVE_ATTEMPT_LIMIT")?.parse()?);
    let started=Instant::now();let reference=port();let(field,mut initial,pairing)=declaration_with_input_context(16384,true,true)?;initial.bind_family_local_receiving_return(2)?;initial.bind_bounded_receiving_representation(2)?;initial.bind_native_rational_receiving(2)?;
    let mut resident=reference.mount_declared_receiving_law(&field,&Current::at_rest(&field),initial,holonics::hnn::receiving::ReceivingLaw::RetainedFibreV1)?;
    let empty=PairedObservation::admit(&field,resident.constitution(),&pairing)?.encode(&[])?;reference.ingest(&mut resident,None,&empty)?;resident.refine_contact_grain(24)?;resident.select_native_quadratic_work_prepared_input(&pairing)?;
    assert!(resident.constitution().receiving_map(2).unwrap().entries().iter().all(num_traits::Zero::is_zero));
    let opening=resident.constitution().clone();let mut stream=ObservedStream::new(resident,ObservedCrib::new(0),ObservedEpochDepositionScope::LocalReceivingReturnWithHeldMap)?;
    fn cold(reference:&Reference,stream:&ObservedStream,opening:&Constitution)->Result<ObservedStream>{
        let state=stream.resident().continuing_state(0)?;let parsed=ContinuingState::from_text(&state.to_text(),READ_BUDGET)?;let field=stream.resident().field();let resident=reference.mount_continued(field,&Current::at_rest(field),opening.clone(),&parsed)?;assert_eq!(resident.continuing_state(0)?,state);
        let crib=ObservedCrib::from_unplaced_checkpoint(field,resident.current(),stream.crib().next_position(),&stream.crib().unplaced_checkpoint()?)?;
        let text=stream.pending_checkpoint();assert!(text.starts_with("observed-stream-pending-native-rational-v1"));
        let changed=text.replacen("1048576","1048575",1);assert!(ObservedStream::restore_checkpoint(resident.clone(),crib.clone(),&changed).is_err());
        let restored=ObservedStream::restore_checkpoint(resident,crib,&text)?;assert_eq!(restored.pending_checkpoint(),text);Ok(restored)
    }
    let data:Vec<_>=(0..30).map(|i|i%4).collect();stream.receive_native_current(&reference,&pairing,&data[..6],64)?;stream=cold(&reference,&stream,&opening)?;
    println!("RATIONAL_PENDING_COLD accepted6/published0/pending6 native_policy_resources_exact=true mismatch_refused=true");
    let before=stream.resident().continuing_state(0)?;let pending=stream.pending_checkpoint();let mut seen7=false;let mut observed=0;
    let outcome=stream.receive_native_current_diagnosed(&reference,&pairing,&data[6..10],64,&mut |e|{
        observed+=1;
        if e.prediction.source_cells==7{
            let receipt=e.preparation.as_ref().expect("source7 actual preparation");let r=receipt.quadratic_work.as_ref().expect("new private work carrier");
            let captured=Rat::new("51564025503142025724633702171333565477839602018262442180103416381733773829048987453642701117582441066181057391566130098304758509976933898410653964848328685074019118599927583053254770629577698244842880393017724348808904362643832108931305119651518354414673594465825438666030285830918268463504266119585360990590528111".parse().unwrap(),"22047267733340713048940158349214507467643823909519974157522241104760090223066576032924786842675813207198282257472108484449990867834675484277115873809660291195993146826927099026296864779242370390778269105246036983513853630109287239444143229113361694201038019485686046577441025195335936000000000000000000000000000000".parse().unwrap());assert_eq!(receipt.work,captured);
            assert_eq!(r.metric,rat(1,2));assert!(r.charged_arithmetic_bits<=1048576);
            let cross=&r.metric*integer(2)*r.old.iter().zip(&r.added).map(|(m,a)|m*a).sum::<Rat>();let quadratic=&r.metric*r.added.iter().map(|a|a*a).sum::<Rat>();assert_eq!(cross,receipt.cross);assert_eq!(quadratic,receipt.quadratic);assert_eq!(&cross+&quadratic,receipt.work);
            assert_eq!((receipt.work.numer().bits(),receipt.work.denom().bits()),(1043,1041));assert!(receipt.work<integer(65536));assert!(receipt.closes());
            assert!(r.added.iter().all(|x|x.numer().bits()<=1024&&x.denom().bits()<=1024));
            println!("RATIONAL_REAL_CUT7 staged_not_published=true source={} metric={:?} old={:?} added={:?} control={:?} work={:?} cross={:?} quadratic={:?} derived_bound={}/{} bitwork={}",r.source_cells,r.metric,r.old,r.added,r.control,receipt.work,receipt.cross,receipt.quadratic,r.numerator_bound_bits,r.denominator_bound_bits,r.charged_arithmetic_bits);seen7=true;
        }
        // Exact producer feature witness for any later unchanged EpochFlow packing refusal.
        if let Some((at,x))=e.prediction.features[0].iter().enumerate().find(|(_,x)|{let z=x.denom().trailing_zeros().unwrap();(x.denom()>>z as usize)!=num_bigint::BigInt::from(1)}){
            println!("RATIONAL_NATIVE_FEATURE source={} coordinate={at} value={x} declared_feature_divisor=1",e.prediction.source_cells);
        }
    });
    match outcome{
        Err(e)=>{assert!(seen7,"the reviewed wide-work case must be reached before any later refusal");assert_eq!(stream.resident().continuing_state(0)?,before);assert_eq!(stream.pending_checkpoint(),pending);println!("RATIONAL_LATER_REFUSAL staged_events={observed} cut7_accepted=true whole_delivery_rollback=true error={e:?}");return Err(e.into());},
        Ok(events)=>{assert!(seen7);assert_eq!(events.len(),1);println!("RATIONAL_FIRST_R publication={:?} reuse={:?}",events[0].publication,stream.resident().native_rank_reuse_reading());}
    }
    stream=cold(&reference,&stream,&opening)?;
    let(mut fork,mut crib)=stream.native_current_query_fork(&reference,&pairing,64)?;fork.begin_hypothesized_output()?;let material=fork.constitution().clone();let m=fork.prepared_input().unwrap().material().clone();
    for key in [rat(1,7),rat(2,7),rat(3,7),rat(4,7)]{reference.release_native_current_forecast(&mut fork,&mut crib,&pairing,&key,64)?;assert_eq!(fork.constitution(),&material);assert_eq!(fork.prepared_input().unwrap().material(),&m);}
    println!("RATIONAL_CONNECTED_SUCCESSOR_PASS actual10 four_frozen=true elapsed_ns={}",started.elapsed().as_nanos());Ok(())
}

#[test]
#[ignore="isolated fixed CODE/attempt envelope"]
fn native_rational_full_transition()->Result<()>{
    use holonics::hnn::word::work;
    struct Meter;impl Drop for Meter{fn drop(&mut self){let c=work::process_native_calls();let t=c.forward_attempts+c.response_attempts+c.return_attempts+c.response_return_attempts;let s=format!("{{\"final\":true,\"total_attempts\":{t},\"forward_constructors\":{},\"response_companions\":{},\"actual_returns\":{},\"fresh_returns\":{}}}\n",c.forward_attempts,c.response_attempts,c.return_attempts,c.response_return_attempts);println!("RESOURCE_TRANSITION_CONNECTED_FINAL {s}");if let Some(p)=std::env::var_os("V93_NATIVE_COUNT_PATH"){std::fs::write(p,s).unwrap();}}}
    let _meter=Meter;work::limit_process_native_attempts(std::env::var("V93_NATIVE_ATTEMPT_LIMIT")?.parse()?);
    let started=Instant::now();let reference=port();let(field,mut initial,pairing)=declaration_with_input_context(16384,true,true)?;initial.bind_family_local_receiving_return(2)?;initial.bind_bounded_receiving_representation(2)?;initial.bind_native_rational_receiving(2)?;
    let mut resident=reference.mount_declared_receiving_law(&field,&Current::at_rest(&field),initial,holonics::hnn::receiving::ReceivingLaw::RetainedFibreV1)?;
    let empty=PairedObservation::admit(&field,resident.constitution(),&pairing)?.encode(&[])?;reference.ingest(&mut resident,None,&empty)?;resident.refine_contact_grain(24)?;resident.select_native_quadratic_work_prepared_input(&pairing)?;
    assert!(resident.constitution().receiving_map(2).unwrap().entries().iter().all(num_traits::Zero::is_zero));
    let opening=resident.constitution().clone();let mut stream=ObservedStream::new(resident,ObservedCrib::new(0),ObservedEpochDepositionScope::LocalReceivingReturnWithHeldMap)?;
    fn cold(reference:&Reference,stream:&ObservedStream,opening:&Constitution)->Result<ObservedStream>{
        let state=stream.resident().continuing_state(0)?;let parsed=ContinuingState::from_text(&state.to_text(),READ_BUDGET)?;let field=stream.resident().field();let resident=reference.mount_continued(field,&Current::at_rest(field),opening.clone(),&parsed)?;assert_eq!(resident.continuing_state(0)?,state);
        let crib=ObservedCrib::from_unplaced_checkpoint(field,resident.current(),stream.crib().next_position(),&stream.crib().unplaced_checkpoint()?)?;
        let text=stream.pending_checkpoint();assert!(text.starts_with("observed-stream-pending-native-rational-v1"));
        let changed=text.replacen("1048576","1048575",1);assert!(ObservedStream::restore_checkpoint(resident.clone(),crib.clone(),&changed).is_err());
        let restored=ObservedStream::restore_checkpoint(resident,crib,&text)?;assert_eq!(restored.pending_checkpoint(),text);Ok(restored)
    }
    let data:Vec<_>=(0..30).map(|i|i%4).collect();stream.receive_native_current(&reference,&pairing,&data[..6],64)?;stream=cold(&reference,&stream,&opening)?;
    println!("RESOURCE_TRANSITION_PENDING_COLD accepted6/published0/pending6 native_policy_resources_exact=true mismatch_refused=true");
    let before=stream.resident().continuing_state(0)?;let pending=stream.pending_checkpoint();let mut seen7=false;let mut observed=0;
    let outcome=stream.receive_native_current_diagnosed(&reference,&pairing,&data[6..10],64,&mut |e|{
        observed+=1;
        println!("RESOURCE_TRANSITION_PRODUCER source={} commit={} features={:?} waves={:?}",e.prediction.source_cells,e.prediction.producing_commit,e.prediction.features,e.prediction.waves);
        if e.prediction.source_cells==7{
            let receipt=e.preparation.as_ref().expect("source7 actual preparation");let r=receipt.quadratic_work.as_ref().expect("new private work carrier");
            let captured=Rat::new("51564025503142025724633702171333565477839602018262442180103416381733773829048987453642701117582441066181057391566130098304758509976933898410653964848328685074019118599927583053254770629577698244842880393017724348808904362643832108931305119651518354414673594465825438666030285830918268463504266119585360990590528111".parse().unwrap(),"22047267733340713048940158349214507467643823909519974157522241104760090223066576032924786842675813207198282257472108484449990867834675484277115873809660291195993146826927099026296864779242370390778269105246036983513853630109287239444143229113361694201038019485686046577441025195335936000000000000000000000000000000".parse().unwrap());assert_eq!(receipt.work,captured);
            assert_eq!(r.metric,rat(1,2));assert!(r.charged_arithmetic_bits<=1048576);
            let cross=&r.metric*integer(2)*r.old.iter().zip(&r.added).map(|(m,a)|m*a).sum::<Rat>();let quadratic=&r.metric*r.added.iter().map(|a|a*a).sum::<Rat>();assert_eq!(cross,receipt.cross);assert_eq!(quadratic,receipt.quadratic);assert_eq!(&cross+&quadratic,receipt.work);
            assert_eq!((receipt.work.numer().bits(),receipt.work.denom().bits()),(1043,1041));assert!(receipt.work<integer(65536));assert!(receipt.closes());
            assert!(r.added.iter().all(|x|x.numer().bits()<=1024&&x.denom().bits()<=1024));
            println!("RESOURCE_TRANSITION_REAL_CUT7 staged_not_published=true source={} metric={:?} old={:?} added={:?} control={:?} work={:?} cross={:?} quadratic={:?} derived_bound={}/{} bitwork={}",r.source_cells,r.metric,r.old,r.added,r.control,receipt.work,receipt.cross,receipt.quadratic,r.numerator_bound_bits,r.denominator_bound_bits,r.charged_arithmetic_bits);seen7=true;
        }
        // Exact producer feature witness for any later unchanged EpochFlow packing refusal.
        if let Some((at,x))=e.prediction.features[0].iter().enumerate().find(|(_,x)|{let z=x.denom().trailing_zeros().unwrap();(x.denom()>>z as usize)!=num_bigint::BigInt::from(1)}){
            println!("RESOURCE_TRANSITION_NATIVE_FEATURE source={} coordinate={at} value={x} declared_feature_divisor=1",e.prediction.source_cells);
        }
    });
    match outcome{
        Err(e)=>{assert!(seen7,"the reviewed wide-work case must be reached before any later refusal");assert_eq!(stream.resident().continuing_state(0)?,before);assert_eq!(stream.pending_checkpoint(),pending);println!("RESOURCE_TRANSITION_LATER_REFUSAL staged_events={observed} cut7_accepted=true whole_delivery_rollback=true error={e:?}");return Err(e.into());},
        Ok(events)=>{assert!(seen7);assert_eq!(events.len(),1);println!("RESOURCE_TRANSITION_FIRST_R publication={:?} reuse={:?}",events[0].publication,stream.resident().native_rank_reuse_reading());}
    }
    stream=cold(&reference,&stream,&opening)?;
    assert!(stream.pending_checkpoint().ends_with("\n"));
    let at10=stream.resident().continuing_state(0)?;
    let contact=stream.observe_native_current_contact(&reference,&pairing,data[10],64)?;
    assert_eq!(contact.prediction.source_cells,10);
    assert!(contact.contact.is_some(),"a new actual contact event must execute its own publication owner");
    println!("RESOURCE_TRANSITION_NEW_CONTACT source10to11=true publication={:?}",contact.contact.as_ref().map(|c|&c.publication));
    let before_second=stream.resident().continuing_state(0)?;let pending_second=stream.pending_checkpoint();
    let second=stream.receive_native_current_diagnosed(&reference,&pairing,&data[11..20],64,&mut|e|println!("RESOURCE_TRANSITION_SECOND_PRODUCER source={} commit={} features={:?} waves={:?}",e.prediction.source_cells,e.prediction.producing_commit,e.prediction.features,e.prediction.waves));
    let sections=match second{Ok(x)=>x,Err(e)=>{assert_eq!(stream.resident().continuing_state(0)?,before_second);assert_eq!(stream.pending_checkpoint(),pending_second);println!("RESOURCE_TRANSITION_SECOND_REFUSAL rollback_source11_exact=true error={e:?}");return Err(e.into());}};
    assert_eq!(sections.len(),1);assert_eq!(sections[0].start_source,11);assert_eq!(sections[0].end_source,20);assert_eq!(sections[0].contact_prefix_cells,1);
    println!("RESOURCE_TRANSITION_SECOND_R source11to20=true publication={:?}",sections[0].publication);
    let warm=stream.clone();let cold_stream=cold(&reference,&stream,&opening)?;
    assert_eq!(warm.resident().continuing_state(0)?,cold_stream.resident().continuing_state(0)?);assert_eq!(warm.pending_checkpoint(),cold_stream.pending_checkpoint());
    let retained=warm.resident().continuing_state(0)?;
    let(mut a,mut ac)=warm.native_current_query_fork(&reference,&pairing,64)?;let(mut b,mut bc)=cold_stream.native_current_query_fork(&reference,&pairing,64)?;
    a.begin_hypothesized_output()?;b.begin_hypothesized_output()?;
    let material=a.constitution().clone();let m=a.prepared_input().unwrap().material().clone();
    for (index,key) in [rat(1,7),rat(2,7),rat(3,7),rat(4,7)].into_iter().enumerate(){
        let ar=reference.release_native_current_forecast(&mut a,&mut ac,&pairing,&key,64)?;let br=reference.release_native_current_forecast(&mut b,&mut bc,&pairing,&key,64)?;
        assert_eq!(ar.prediction,br.prediction);assert_eq!(ar.selected_class,br.selected_class);assert_eq!(a.carried(),b.carried());
        assert_eq!(a.constitution(),&material);assert_eq!(b.constitution(),&material);assert_eq!(a.prepared_input().unwrap().material(),&m);assert_eq!(b.prepared_input().unwrap().material(),&m);
        println!("RESOURCE_TRANSITION_FROZEN decision={index} key={key} class={} warm_cold_prediction_equal=true",ar.selected_class);
    }
    assert_eq!(warm.resident().continuing_state(0)?,retained);
    assert_ne!(at10,retained);
    println!("RESOURCE_TRANSITION_COMPLETE_PASS actual20 R_contact_R=true pending6_cold=true final_native_cold=true four_warm_cold_frozen_equal=true elapsed_ns={}",started.elapsed().as_nanos());Ok(())
}

#[test]
#[ignore="isolated fixed CODE/attempt envelope"]
fn native_original_word_final_ingress_transition()->Result<()>{
    use holonics::hnn::word::work;
    struct Meter;impl Drop for Meter{fn drop(&mut self){let c=work::process_native_calls();let t=c.forward_attempts+c.response_attempts+c.return_attempts+c.response_return_attempts;let s=format!("{{\"final\":true,\"total_attempts\":{t},\"forward_constructors\":{},\"response_companions\":{},\"actual_returns\":{},\"fresh_returns\":{}}}\n",c.forward_attempts,c.response_attempts,c.return_attempts,c.response_return_attempts);println!("FINAL_INGRESS_CONNECTED_FINAL {s}");if let Some(p)=std::env::var_os("V93_NATIVE_COUNT_PATH"){std::fs::write(p,s).unwrap();}}}
    let _meter=Meter;work::limit_process_native_attempts(std::env::var("V93_NATIVE_ATTEMPT_LIMIT")?.parse()?);
    let started=Instant::now();let reference=port();let(field,mut initial,pairing)=declaration_with_input_context(16384,true,true)?;initial.bind_family_local_receiving_return(2)?;initial.bind_bounded_receiving_representation(2)?;initial.bind_native_rational_receiving(2)?;
    let mut resident=reference.mount_declared_receiving_law(&field,&Current::at_rest(&field),initial,holonics::hnn::receiving::ReceivingLaw::RetainedFibreV1)?;
    let empty=PairedObservation::admit(&field,resident.constitution(),&pairing)?.encode(&[])?;reference.ingest(&mut resident,None,&empty)?;resident.refine_contact_grain(24)?;resident.select_native_quadratic_work_prepared_input(&pairing)?;
    assert!(resident.constitution().receiving_map(2).unwrap().entries().iter().all(num_traits::Zero::is_zero));
    let opening=resident.constitution().clone();let mut stream=ObservedStream::new(resident,ObservedCrib::new(0),ObservedEpochDepositionScope::LocalReceivingReturnWithHeldMap)?;
    fn cold(reference:&Reference,stream:&ObservedStream,opening:&Constitution)->Result<ObservedStream>{
        let state=stream.resident().continuing_state(0)?;let text_state=state.to_text();let at=stream.crib().next_position();println!("FINAL_INGRESS_COLD_BEGIN addressed_frontier={at:?} state_bytes={} pending={}",text_state.len(),stream.pending_checkpoint());
        let parsed=ContinuingState::from_text(&text_state,READ_BUDGET).map_err(|e|{println!("FINAL_INGRESS_COLD_REFUSAL boundary=decode addressed_frontier={at:?} error={e:?}");e})?;let field=stream.resident().field();let resident=reference.mount_continued(field,&Current::at_rest(field),opening.clone(),&parsed).map_err(|e|{println!("FINAL_INGRESS_COLD_REFUSAL boundary=mount addressed_frontier={at:?} error={e:?}");e})?;assert_eq!(resident.continuing_state(0)?,state);
        let crib=ObservedCrib::from_unplaced_checkpoint(field,resident.current(),stream.crib().next_position(),&stream.crib().unplaced_checkpoint()?)?;
        let text=stream.pending_checkpoint();assert!(text.starts_with("observed-stream-pending-native-rational-v1"));
        let changed=text.replacen("1048576","1048575",1);assert!(ObservedStream::restore_checkpoint(resident.clone(),crib.clone(),&changed).is_err());
        let restored=ObservedStream::restore_checkpoint(resident,crib,&text).map_err(|e|{println!("FINAL_INGRESS_COLD_REFUSAL boundary=pending addressed_frontier={at:?} error={e:?}");e})?;assert_eq!(restored.pending_checkpoint(),text);println!("FINAL_INGRESS_COLD_PASS addressed_frontier={at:?} full_native_and_pending_equal=true");Ok(restored)
    }
    let data:Vec<_>=(0..30).map(|i|i%4).collect();stream.receive_native_current(&reference,&pairing,&data[..6],64)?;stream=cold(&reference,&stream,&opening)?;
    println!("FINAL_INGRESS_PENDING_COLD accepted6/published0/pending6 native_policy_resources_exact=true mismatch_refused=true");
    let before=stream.resident().continuing_state(0)?;let pending=stream.pending_checkpoint();let mut seen7=false;let mut observed=0;
    let outcome=stream.receive_native_current_diagnosed(&reference,&pairing,&data[6..10],64,&mut |e|{
        observed+=1;
        println!("FINAL_INGRESS_PRODUCER source={} commit={} features={:?} waves={:?}",e.prediction.source_cells,e.prediction.producing_commit,e.prediction.features,e.prediction.waves);
        if e.prediction.source_cells==7{
            let receipt=e.preparation.as_ref().expect("source7 actual preparation");let r=receipt.quadratic_work.as_ref().expect("new private work carrier");
            let captured=Rat::new("51564025503142025724633702171333565477839602018262442180103416381733773829048987453642701117582441066181057391566130098304758509976933898410653964848328685074019118599927583053254770629577698244842880393017724348808904362643832108931305119651518354414673594465825438666030285830918268463504266119585360990590528111".parse().unwrap(),"22047267733340713048940158349214507467643823909519974157522241104760090223066576032924786842675813207198282257472108484449990867834675484277115873809660291195993146826927099026296864779242370390778269105246036983513853630109287239444143229113361694201038019485686046577441025195335936000000000000000000000000000000".parse().unwrap());assert_eq!(receipt.work,captured);
            assert_eq!(r.metric,rat(1,2));assert!(r.charged_arithmetic_bits<=1048576);
            let cross=&r.metric*integer(2)*r.old.iter().zip(&r.added).map(|(m,a)|m*a).sum::<Rat>();let quadratic=&r.metric*r.added.iter().map(|a|a*a).sum::<Rat>();assert_eq!(cross,receipt.cross);assert_eq!(quadratic,receipt.quadratic);assert_eq!(&cross+&quadratic,receipt.work);
            assert_eq!((receipt.work.numer().bits(),receipt.work.denom().bits()),(1043,1041));assert!(receipt.work<integer(65536));assert!(receipt.closes());
            assert!(r.added.iter().all(|x|x.numer().bits()<=1024&&x.denom().bits()<=1024));
            println!("FINAL_INGRESS_REAL_CUT7 staged_not_published=true source={} metric={:?} old={:?} added={:?} control={:?} work={:?} cross={:?} quadratic={:?} derived_bound={}/{} bitwork={}",r.source_cells,r.metric,r.old,r.added,r.control,receipt.work,receipt.cross,receipt.quadratic,r.numerator_bound_bits,r.denominator_bound_bits,r.charged_arithmetic_bits);seen7=true;
        }
        // Exact producer feature witness for any later unchanged EpochFlow packing refusal.
        if let Some((at,x))=e.prediction.features[0].iter().enumerate().find(|(_,x)|{let z=x.denom().trailing_zeros().unwrap();(x.denom()>>z as usize)!=num_bigint::BigInt::from(1)}){
            println!("FINAL_INGRESS_NATIVE_FEATURE source={} coordinate={at} value={x} declared_feature_divisor=1",e.prediction.source_cells);
        }
    });
    match outcome{
        Err(e)=>{assert!(seen7,"the reviewed wide-work case must be reached before any later refusal");assert_eq!(stream.resident().continuing_state(0)?,before);assert_eq!(stream.pending_checkpoint(),pending);println!("FINAL_INGRESS_LATER_REFUSAL staged_events={observed} cut7_accepted=true whole_delivery_rollback=true error={e:?}");return Err(e.into());},
        Ok(events)=>{assert!(seen7);assert_eq!(events.len(),1);assert_eq!(events[0].publication_source,9);assert!(events[0].blind_carry_preserved);assert_eq!(events[0].events.last().unwrap().prediction.source_cells,9);println!("FINAL_INGRESS_FIRST_R publication={:?} reuse={:?}",events[0].publication,stream.resident().native_rank_reuse_reading());}
    }
    stream=cold(&reference,&stream,&opening)?;
    assert!(stream.pending_checkpoint().ends_with("\n"));
    let at10=stream.resident().continuing_state(0)?;
    let pending10=stream.pending_checkpoint();
    let contact=match stream.observe_native_current_contact(&reference,&pairing,data[10],64){Ok(x)=>x,Err(e)=>{assert_eq!(stream.resident().continuing_state(0)?,at10);assert_eq!(stream.pending_checkpoint(),pending10);println!("FINAL_INGRESS_CONTACT_REFUSAL source10 target={} rollback_exact=true error={e:?}",data[10]);return Err(e.into());}};
    assert_eq!(contact.prediction.source_cells,10);
    assert!(contact.contact.is_some(),"a new actual contact event must execute its own publication owner");
    println!("FINAL_INGRESS_NEW_CONTACT source10to11=true publication={:?}",contact.contact.as_ref().map(|c|&c.publication));
    let before_second=stream.resident().continuing_state(0)?;let pending_second=stream.pending_checkpoint();
    let second=stream.receive_native_current_diagnosed(&reference,&pairing,&data[11..20],64,&mut|e|println!("FINAL_INGRESS_SECOND_PRODUCER source={} commit={} features={:?} waves={:?}",e.prediction.source_cells,e.prediction.producing_commit,e.prediction.features,e.prediction.waves));
    let sections=match second{Ok(x)=>x,Err(e)=>{assert_eq!(stream.resident().continuing_state(0)?,before_second);assert_eq!(stream.pending_checkpoint(),pending_second);println!("FINAL_INGRESS_SECOND_REFUSAL rollback_source11_exact=true error={e:?}");if std::env::var("V93_NATIVE_PREFIX_DIAGNOSTIC").as_deref()==Ok("1"){assert!(matches!(e,holonics::hnn::HnnError::NativePreparationRefusal{..}));println!("CONTROL_PREFIX_DIAGNOSTIC_CAPTURED stopped_before_next_R=true no_retry=true");return Ok(());}return Err(e.into());}};
    assert_ne!(std::env::var("V93_NATIVE_PREFIX_DIAGNOSTIC").as_deref(),Ok("1"),"diagnostic must stop at captured refusal; no continuation permitted");
    assert_eq!(sections.len(),1);assert_eq!(sections[0].start_source,11);assert_eq!(sections[0].end_source,20);assert_eq!(sections[0].contact_prefix_cells,1);assert_eq!(sections[0].publication_source,19);assert!(sections[0].blind_carry_preserved);
    println!("FINAL_INGRESS_SECOND_R source11to20=true publication={:?}",sections[0].publication);
    let before_third=stream.resident().continuing_state(0)?;let pending_third=stream.pending_checkpoint();
    let third=stream.receive_native_current_diagnosed(&reference,&pairing,&data[20..30],64,&mut|e|println!("FINAL_INGRESS_THIRD_PRODUCER source={} commit={} features={:?} waves={:?}",e.prediction.source_cells,e.prediction.producing_commit,e.prediction.features,e.prediction.waves));
    let last=match third{Ok(x)=>x,Err(e)=>{assert_eq!(stream.resident().continuing_state(0)?,before_third);assert_eq!(stream.pending_checkpoint(),pending_third);println!("FINAL_INGRESS_THIRD_REFUSAL rollback_source20_exact=true error={e:?}");return Err(e.into());}};
    assert_eq!(last.len(),1);assert_eq!((last[0].start_source,last[0].end_source,last[0].publication_source),(20,30,29));assert!(last[0].blind_carry_preserved);assert!(last[0].aeon_closed,"actual source30 deferred whole-carry close must execute");
    assert!(last[0].events.last().unwrap().input.close.is_none()); // close belongs to deferred whole section, not duplicate ingress
    println!("FINAL_INGRESS_THIRD_R source20to30=true publication_before_ingress29=true publication={:?} final_pending={}",last[0].publication,stream.pending_checkpoint());
    let warm=stream.clone();let cold_stream=cold(&reference,&stream,&opening)?;
    assert_eq!(warm.resident().continuing_state(0)?,cold_stream.resident().continuing_state(0)?);assert_eq!(warm.pending_checkpoint(),cold_stream.pending_checkpoint());
    let retained=warm.resident().continuing_state(0)?;
    let(mut a,mut ac)=warm.native_current_query_fork(&reference,&pairing,64)?;let(mut b,mut bc)=cold_stream.native_current_query_fork(&reference,&pairing,64)?;
    a.begin_hypothesized_output()?;b.begin_hypothesized_output()?;
    let material=a.constitution().clone();let m=a.prepared_input().unwrap().material().clone();
    for (index,key) in [rat(1,7),rat(2,7),rat(3,7),rat(4,7)].into_iter().enumerate(){
        let ar=reference.release_native_current_forecast(&mut a,&mut ac,&pairing,&key,64)?;let br=reference.release_native_current_forecast(&mut b,&mut bc,&pairing,&key,64)?;
        assert_eq!(ar.prediction,br.prediction);assert_eq!(ar.selected_class,br.selected_class);assert_eq!(a.carried(),b.carried());
        assert_eq!(a.constitution(),&material);assert_eq!(b.constitution(),&material);assert_eq!(a.prepared_input().unwrap().material(),&m);assert_eq!(b.prepared_input().unwrap().material(),&m);
        println!("FINAL_INGRESS_FROZEN decision={index} key={key} class={} warm_cold_prediction_equal=true",ar.selected_class);
    }
    assert_eq!(warm.resident().continuing_state(0)?,retained);
    assert_ne!(at10,retained);
    println!("FINAL_INGRESS_COMPLETE_PASS actual30 R_contact_R_close30=true pending6_cold=true final_native_cold=true four_warm_cold_frozen_equal=true elapsed_ns={}",started.elapsed().as_nanos());Ok(())
}

#[test]
#[ignore="isolated represented native data/160-attempt envelope"]
fn represented_native_policy_pending_cold_and_guard()->Result<()>{
    use holonics::hnn::word::work;
    use holonics::hnn::reference::native_context::NativeExecutionChart;
    struct Meter;impl Drop for Meter{fn drop(&mut self){let c=work::process_native_calls();let total=c.forward_attempts+c.response_attempts+c.return_attempts+c.response_return_attempts;let s=format!("{{\"final\":true,\"total_attempts\":{total},\"forward_constructors\":{},\"response_companions\":{},\"actual_returns\":{},\"fresh_returns\":{}}}\n",c.forward_attempts,c.response_attempts,c.return_attempts,c.response_return_attempts);println!("REPRESENTED_DATA_COUNTS {s}");if let Some(p)=std::env::var_os("V93_NATIVE_COUNT_PATH"){std::fs::write(p,s).unwrap();}}}
    let _meter=Meter;work::limit_process_native_attempts(std::env::var("V93_NATIVE_ATTEMPT_LIMIT")?.parse()?);
    let started=Instant::now();let reference=port();let(field,mut initial,pairing)=declaration_with_input_context(16384,true,true)?;
    initial.bind_family_local_receiving_return(2)?;initial.bind_bounded_receiving_representation(2)?;initial.bind_native_rational_receiving(2)?;
    let mut resident=reference.mount_declared_receiving_law(&field,&Current::at_rest(&field),initial,holonics::hnn::receiving::ReceivingLaw::RetainedFibreV1)?;
    let empty=PairedObservation::admit(&field,resident.constitution(),&pairing)?.encode(&[])?;reference.ingest(&mut resident,None,&empty)?;
    resident.select_represented_native_prepared_input(&pairing)?;
    let opening=resident.constitution().clone();let mut stream=ObservedStream::new(resident,ObservedCrib::new(0),ObservedEpochDepositionScope::LocalReceivingReturnWithHeldMap)?;
    stream.receive_native_current(&reference,&pairing,&[0,1,2,3,0,1],64)?;
    let pending=stream.pending_checkpoint();assert!(pending.starts_with("observed-stream-pending-native-represented-v1"));
    let saved=stream.resident().continuing_state(0)?;let parsed=ContinuingState::from_text(&saved.to_text(),READ_BUDGET)?;
    let restored=reference.mount_continued(&field,&Current::at_rest(&field),opening.clone(),&parsed)?;
    let crib=ObservedCrib::from_unplaced_checkpoint(&field,restored.current(),stream.crib().next_position(),&stream.crib().unplaced_checkpoint()?)?;
    assert!(ObservedStream::restore_checkpoint(restored.clone(),crib.clone(),&pending.replacen("observed-stream-pending-native-represented-v1","observed-stream-pending-native-rational-v1",1)).is_err());
    let restored=ObservedStream::restore_checkpoint(restored,crib,&pending)?;assert_eq!(restored.resident().continuing_state(0)?,saved);
    println!("REPRESENTED_PENDING6_COLD_PASS explicit_policy=true exact_policy_substitution_refused=true");
    let(warm,_)=restored.native_current_query_fork(&reference,&pairing,64)?;
    let state=warm.continuing_state(0)?;let parsed=ContinuingState::from_text(&state.to_text(),READ_BUDGET)?;
    let cold=reference.mount_continued(&field,&Current::at_rest(&field),opening,&parsed)?;assert_eq!(cold.continuing_state(0)?,state);
    let mut prior=None;
    for (name,r) in [("warm",&warm),("cold",&cold)]{
        let predicted=reference.prepare_native_current_prediction(r,NativeExecutionChart::RepresentedV1,64)?;
        let reading=predicted.reading();assert!(reading.execution_lattice.is_some());let(_,balance,preparation)=predicted.forward_receipt()?;assert!(balance.closes());assert!(preparation.as_ref().is_none_or(|p|p.closes()));
        if let Some((old,old_balance))=&prior{assert_eq!(&reading,old);assert_eq!(&balance,old_balance);}else{prior=Some((reading.clone(),balance.clone()));}
        let target=PairedObservation::admit(&field,r.constitution(),&pairing)?.encode(&[2])?;
        let returned=predicted.observe(&target)?;let mut charts=holonics::hnn::chart::Charts::default();
        match returned.publish_contact_carry(&mut charts){
            Err(holonics::hnn::HnnError::RepresentedNativeGainUnavailable{source_cells,commit,lattice,state_radii,class_error_l1})=>{
                let context=state_radii.context_bounds()?;assert_eq!(source_cells,6);assert_eq!(context.len(),reading.features.len());
                println!("REPRESENTED_CONTACT_BOUNDARY name={name} source={source_cells} commit={commit} lattice={lattice:?} genuine_actual_fresh_radii={state_radii:?} class_error={class_error_l1} missing=uniform_changed_chart_material_ray_response no_publication=true release={:?}",balance.released);
            },Err(e)=>return Err(e.into()),Ok(p)=>{
                let physical=p.physical_reference.as_ref().ok_or("represented physical-reference reading")?;
                assert_eq!(physical.stored_pairing,integer(0));assert_eq!(physical.lower,integer(0));
                println!("REPRESENTED_CONTACT_ZERO_R name={name} physical_reference={physical:?} no_general_positive_ray_claim=true");
            },
        }
        assert_eq!(r.continuing_state(0)?,state);
    }
    println!("REPRESENTED_FORWARD_COLD_PASS frozen_material=true same_represented_face_and_balance=true unsplit_equivalence_claim=false elapsed_ns={}",started.elapsed().as_nanos());Ok(())
}

#[test]
#[ignore="one pre-reserved represented native connected/640-attempt guard; no dataset"]
fn represented_native_full_transition()->Result<()>{
    use holonics::hnn::word::work;
    use holonics::hnn::field::ConstitutionRead;
    struct Meter;impl Drop for Meter{fn drop(&mut self){let c=work::process_native_calls();let total=c.forward_attempts+c.response_attempts+c.return_attempts+c.response_return_attempts;let s=format!("{{\"final\":true,\"total_attempts\":{total},\"forward_constructors\":{},\"response_companions\":{},\"actual_returns\":{},\"fresh_returns\":{}}}\n",c.forward_attempts,c.response_attempts,c.return_attempts,c.response_return_attempts);println!("REPRESENTED_CONNECTED_COUNTS {s} work={:?}",work::read());if let Some(p)=std::env::var_os("V93_NATIVE_COUNT_PATH"){std::fs::write(p,s).unwrap();}}}
    let _meter=Meter;work::limit_process_native_attempts(std::env::var("V93_NATIVE_ATTEMPT_LIMIT")?.parse()?);
    let started=Instant::now();let reference=port();let(field,mut initial,pairing)=declaration_with_input_context(16384,true,true)?;
    initial.bind_family_local_receiving_return(2)?;initial.bind_bounded_receiving_representation(2)?;initial.bind_native_rational_receiving(2)?;
    let mut resident=reference.mount_declared_receiving_law(&field,&Current::at_rest(&field),initial,holonics::hnn::receiving::ReceivingLaw::RetainedFibreV1)?;
    let empty=PairedObservation::admit(&field,resident.constitution(),&pairing)?.encode(&[])?;reference.ingest(&mut resident,None,&empty)?;
    resident.refine_contact_grain(24)?;resident.select_represented_native_prepared_input(&pairing)?;
    let opening=resident.constitution().clone();let mut stream=ObservedStream::new(resident,ObservedCrib::new(0),ObservedEpochDepositionScope::LocalReceivingReturnWithHeldMap)?;
    fn cold(reference:&Reference,stream:&ObservedStream,opening:&Constitution,label:&str)->Result<ObservedStream>{
        let state=stream.resident().continuing_state(0)?;let text=state.to_text();let parsed=ContinuingState::from_text(&text,READ_BUDGET)?;
        let field=stream.resident().field();let resident=reference.mount_continued(field,&Current::at_rest(field),opening.clone(),&parsed)?;
        assert_eq!(resident.continuing_state(0)?,state);
        let crib=ObservedCrib::from_unplaced_checkpoint(field,resident.current(),stream.crib().next_position(),&stream.crib().unplaced_checkpoint()?)?;
        let pending=stream.pending_checkpoint();assert!(pending.starts_with("observed-stream-pending-native-represented-v1"));
        assert!(ObservedStream::restore_checkpoint(resident.clone(),crib.clone(),&pending.replacen("observed-stream-pending-native-represented-v1","observed-stream-pending-native-rational-v1",1)).is_err());
        let restored=ObservedStream::restore_checkpoint(resident,crib,&pending)?;assert_eq!(restored.pending_checkpoint(),pending);
        println!("REPRESENTED_CONNECTED_COLD_PASS boundary={label} bytes={} pending_equal=true",text.len());Ok(restored)
    }
    let data:Vec<_>=(0..30).map(|i|i%4).collect();stream.receive_native_current(&reference,&pairing,&data[..6],64)?;
    stream=cold(&reference,&stream,&opening,"pending-six")?;
    let at6=stream.resident().continuing_state(0)?;let pending6=stream.pending_checkpoint();
    // Print only existing reached readings; no diagnostic Word or inverse trajectory.
    let first=stream.receive_native_current_diagnosed(&reference,&pairing,&data[6..10],64,&mut|e|{
        let bits=e.prediction.features.iter().flatten().map(|q|q.numer().bits().max(q.denom().bits())).max().unwrap_or(0);
        println!("REPRESENTED_CONNECTED_SOURCE source={} commit={} feature_max_bits={bits} lattice={:?} work={:?}",e.prediction.source_cells,e.prediction.producing_commit,e.prediction.execution_lattice,e.preparation.as_ref().map(|p|&p.work));
    });
    let first=match first{Ok(x)=>x,Err(e)=>{assert_eq!(stream.resident().continuing_state(0)?,at6);assert_eq!(stream.pending_checkpoint(),pending6);println!("REPRESENTED_CONNECTED_REFUSAL boundary=first-R rollback_exact=true error={e:?}");return Err(e.into());}};
    assert_eq!(first.len(),1);assert_eq!(first[0].publication_source,9);assert!(first[0].blind_carry_preserved);
    assert!(stream.resident().constitution().receiving_map(2).unwrap().entries().iter().any(|q|!num_traits::Zero::is_zero(q)));
    println!("REPRESENTED_CONNECTED_FIRST_R_PASS publication={:?}",first[0].publication);
    stream=cold(&reference,&stream,&opening,"post-first-R")?;
    let at10=stream.resident().continuing_state(0)?;let pending10=stream.pending_checkpoint();let theta10=stream.resident().constitution().clone();
    let contact=match stream.observe_native_current_contact(&reference,&pairing,data[10],64){Ok(x)=>x,Err(e)=>{assert_eq!(stream.resident().continuing_state(0)?,at10);assert_eq!(stream.pending_checkpoint(),pending10);println!("REPRESENTED_CONNECTED_REFUSAL boundary=contact10to11 rollback_exact=true error={e:?}");return Err(e.into());}};
    let p=contact.contact.as_ref().ok_or("actual new represented contact owner")?;let proof=p.physical_reference.as_ref().ok_or("physical-reference witness")?;
    assert!(proof.lower>integer(0));assert!(p.actual_alignment>p.actual_error_charge);
    let moved=(0..field.contacts().len()).any(|a|theta10.contact_storage(a)!=p.constitution.contact_storage(a)||theta10.contact_stiffness(a)!=p.constitution.contact_stiffness(a)||theta10.contact_dissipation(a)!=p.constitution.contact_dissipation(a));
    assert!(moved,"genuine contact requires actual represented C/K/D motion, not statistic-only publication");
    println!("REPRESENTED_CONNECTED_CONTACT_PASS source10to11=true actual_factor_motion=true physical_reference={proof:?} work={:?}",p.continuation);
    for (label,start,end) in [("next-R",11,20),("source30-close",20,30)]{
        let before=stream.resident().continuing_state(0)?;let pending=stream.pending_checkpoint();
        let outcome=stream.receive_native_current_diagnosed(&reference,&pairing,&data[start..end],64,&mut|e|{
            let bits=e.prediction.features.iter().flatten().map(|q|q.numer().bits().max(q.denom().bits())).max().unwrap_or(0);
            println!("REPRESENTED_CONNECTED_SOURCE source={} commit={} feature_max_bits={bits}",e.prediction.source_cells,e.prediction.producing_commit);
        });
        let sections=match outcome{Ok(x)=>x,Err(e)=>{assert_eq!(stream.resident().continuing_state(0)?,before);assert_eq!(stream.pending_checkpoint(),pending);println!("REPRESENTED_CONNECTED_REFUSAL boundary={label} rollback_exact=true error={e:?}");return Err(e.into());}};
        assert_eq!(sections.len(),1);assert_eq!(sections[0].publication_source,end as u64-1);assert!(sections[0].blind_carry_preserved);
        if end==30{assert!(sections[0].aeon_closed);}
        println!("REPRESENTED_CONNECTED_SECTION_PASS boundary={label} publication={:?}",sections[0].publication);
    }
    let retained=stream.resident().continuing_state(0)?;let cold=cold(&reference,&stream,&opening,"final-source30")?;
    let(mut a,mut ac)=stream.native_current_query_fork(&reference,&pairing,64)?;let(mut b,mut bc)=cold.native_current_query_fork(&reference,&pairing,64)?;
    a.begin_hypothesized_output()?;b.begin_hypothesized_output()?;let theta=a.constitution().clone();let m=a.prepared_input().unwrap().material().clone();
    for(index,key)in [rat(1,7),rat(2,7),rat(3,7),rat(4,7)].into_iter().enumerate(){
        let x=reference.release_native_current_forecast(&mut a,&mut ac,&pairing,&key,64)?;let y=reference.release_native_current_forecast(&mut b,&mut bc,&pairing,&key,64)?;
        assert_eq!(x.prediction,y.prediction);assert_eq!(x.selected_class,y.selected_class);assert_eq!(a.carried(),b.carried());
        assert_eq!(a.constitution(),&theta);assert_eq!(b.constitution(),&theta);assert_eq!(a.prepared_input().unwrap().material(),&m);assert_eq!(b.prepared_input().unwrap().material(),&m);
        println!("REPRESENTED_CONNECTED_FROZEN_PASS decision={index} key={key} class={}",x.selected_class);
    }
    assert_eq!(stream.resident().continuing_state(0)?,retained);
    println!("REPRESENTED_CONNECTED_COMPLETE_PASS actual30=true firstR_contact_nextR_source30=true cold_and_frozen=true unsplit_trajectory_equivalence=false elapsed_ns={}",started.elapsed().as_nanos());Ok(())
}

#[test]
#[ignore="one bounded continuity control; positive factor influence is a separate verdict"]
fn represented_native_zero_motion_continuity()->Result<()>{
    use holonics::hnn::word::work;
    use holonics::hnn::field::ConstitutionRead;
    struct Meter;impl Drop for Meter{fn drop(&mut self){let c=work::process_native_calls();let total=c.forward_attempts+c.response_attempts+c.return_attempts+c.response_return_attempts;let s=format!("{{\"final\":true,\"total_attempts\":{total},\"forward_constructors\":{},\"response_companions\":{},\"actual_returns\":{},\"fresh_returns\":{}}}\n",c.forward_attempts,c.response_attempts,c.return_attempts,c.response_return_attempts);println!("ZERO_MOTION_CONTINUITY_COUNTS {s} work={:?}",work::read());if let Some(p)=std::env::var_os("V93_NATIVE_COUNT_PATH"){std::fs::write(p,s).unwrap();}}}
    let _meter=Meter;work::limit_process_native_attempts(std::env::var("V93_NATIVE_ATTEMPT_LIMIT")?.parse()?);
    let started=Instant::now();let reference=port();let(field,mut initial,pairing)=declaration_with_input_context(16384,true,true)?;
    initial.bind_family_local_receiving_return(2)?;initial.bind_bounded_receiving_representation(2)?;initial.bind_native_rational_receiving(2)?;
    let mut resident=reference.mount_declared_receiving_law(&field,&Current::at_rest(&field),initial,holonics::hnn::receiving::ReceivingLaw::RetainedFibreV1)?;
    let empty=PairedObservation::admit(&field,resident.constitution(),&pairing)?.encode(&[])?;reference.ingest(&mut resident,None,&empty)?;
    resident.refine_contact_grain(24)?;resident.select_represented_native_prepared_input(&pairing)?;
    let opening=resident.constitution().clone();let mut stream=ObservedStream::new(resident,ObservedCrib::new(0),ObservedEpochDepositionScope::LocalReceivingReturnWithHeldMap)?;
    fn cold(reference:&Reference,stream:&ObservedStream,opening:&Constitution,label:&str)->Result<ObservedStream>{
        let state=stream.resident().continuing_state(0)?;let text=state.to_text();let parsed=ContinuingState::from_text(&text,READ_BUDGET)?;
        let root=std::path::PathBuf::from(std::env::var("V93_CONTROL_ARTIFACT_DIR")?);let folder=root.join(label);std::fs::create_dir_all(&folder)?;
        let crib_text=stream.crib().unplaced_checkpoint()?;let pending_text=stream.pending_checkpoint();
        std::fs::write(folder.join("native.state"),&text)?;std::fs::write(folder.join("crib.txt"),&crib_text)?;std::fs::write(folder.join("pending.txt"),&pending_text)?;
        std::fs::write(folder.join("opening-material.state"),opening.continuing_state(0)?.to_text())?;
        let meta=format!("{{\"accepted\":{},\"native_published\":{},\"exterior_pending\":{},\"native_sha256\":\"{}\",\"crib_sha256\":\"{}\",\"pending_sha256\":\"{}\"}}\n",stream.accepted_cells()?,stream.resident().continuing().ok_or("same native source")?.1,stream.pending_classes().len(),sha256(text.as_bytes())?,sha256(crib_text.as_bytes())?,sha256(pending_text.as_bytes())?);std::fs::write(folder.join("META.json"),meta)?;
        let field=stream.resident().field();let resident=reference.mount_continued(field,&Current::at_rest(field),opening.clone(),&parsed)?;
        assert_eq!(resident.continuing_state(0)?,state);
        let crib=ObservedCrib::from_unplaced_checkpoint(field,resident.current(),stream.crib().next_position(),&stream.crib().unplaced_checkpoint()?)?;
        let pending=stream.pending_checkpoint();assert!(pending.starts_with("observed-stream-pending-native-represented-v1"));
        assert!(ObservedStream::restore_checkpoint(resident.clone(),crib.clone(),&pending.replacen("observed-stream-pending-native-represented-v1","observed-stream-pending-native-rational-v1",1)).is_err());
        let restored=ObservedStream::restore_checkpoint(resident,crib,&pending)?;assert_eq!(restored.pending_checkpoint(),pending);
        println!("ZERO_MOTION_CONTINUITY_COLD_PASS boundary={label} bytes={} pending_equal=true",text.len());Ok(restored)
    }
    let data:Vec<_>=(0..30).map(|i|i%4).collect();stream.receive_native_current(&reference,&pairing,&data[..6],64)?;
    stream=cold(&reference,&stream,&opening,"pending-six")?;
    let at6=stream.resident().continuing_state(0)?;let pending6=stream.pending_checkpoint();
    // Print only existing reached readings; no diagnostic Word or inverse trajectory.
    let first=stream.receive_native_current_diagnosed(&reference,&pairing,&data[6..10],64,&mut|e|{
        let bits=e.prediction.features.iter().flatten().map(|q|q.numer().bits().max(q.denom().bits())).max().unwrap_or(0);
        println!("ZERO_MOTION_CONTINUITY_SOURCE source={} commit={} feature_max_bits={bits} lattice={:?} work={:?}",e.prediction.source_cells,e.prediction.producing_commit,e.prediction.execution_lattice,e.preparation.as_ref().map(|p|&p.work));
    });
    let first=match first{Ok(x)=>x,Err(e)=>{assert_eq!(stream.resident().continuing_state(0)?,at6);assert_eq!(stream.pending_checkpoint(),pending6);println!("ZERO_MOTION_CONTINUITY_REFUSAL boundary=first-R rollback_exact=true error={e:?}");return Err(e.into());}};
    assert_eq!(first.len(),1);assert_eq!(first[0].publication_source,9);assert!(first[0].blind_carry_preserved);
    assert!(stream.resident().constitution().receiving_map(2).unwrap().entries().iter().any(|q|!num_traits::Zero::is_zero(q)));
    println!("ZERO_MOTION_CONTINUITY_FIRST_R_PASS publication={:?}",first[0].publication);
    stream=cold(&reference,&stream,&opening,"post-first-R")?;
    let at10=stream.resident().continuing_state(0)?;let pending10=stream.pending_checkpoint();let theta10=stream.resident().constitution().clone();
    let contact=match stream.observe_native_current_contact(&reference,&pairing,data[10],64){Ok(x)=>x,Err(e)=>{assert_eq!(stream.resident().continuing_state(0)?,at10);assert_eq!(stream.pending_checkpoint(),pending10);println!("ZERO_MOTION_CONTINUITY_REFUSAL boundary=contact10to11 rollback_exact=true error={e:?}");return Err(e.into());}};
    let p=contact.contact.as_ref().ok_or("actual new represented contact owner")?;let proof=p.physical_reference.as_ref().ok_or("physical-reference witness")?;
    let mut actual_delta=Vec::new();
    for a in 0..field.contacts().len(){
        let before=[theta10.contact_storage(a),theta10.contact_stiffness(a),theta10.contact_dissipation(a)];
        let after=[p.constitution.contact_storage(a),p.constitution.contact_stiffness(a),p.constitution.contact_dissipation(a)];
        for family in 0..3{actual_delta.push((a,family,before[family].clone(),after[family].clone(),after[family].subtract(before[family])?));}
    }
    let moved=actual_delta.iter().any(|(_,_,_,_,d)|d.entries().iter().any(|q|!num_traits::Zero::is_zero(q)));
    let before_scales=(0..field.contacts().len()).map(|a|(a,theta10.contact_scales(a).clone())).collect::<Vec<_>>();
    let after_scales=(0..field.contacts().len()).map(|a|(a,p.constitution.contact_scales(a).clone())).collect::<Vec<_>>();
    let contact_carry=|theta:&Constitution|theta.carried_remainders().into_iter().filter(|(l,..)|matches!(l,holonics::hnn::constitution::Locus::Channel(_))).collect::<Vec<_>>();
    let packet=format!("ZERO_MOTION_CONTINUITY_CONTACT_PACKET original_prediction={:?} current_after={:?} full_actual_factor_delta={actual_delta:?} before_scales={before_scales:?} after_scales={after_scales:?} before_contact_carry={:?} after_contact_carry={:?} publication={:?} physical_reference={proof:?} continuation={:?} input={:?}\n",contact.prediction,stream.resident().current(),contact_carry(&theta10),contact_carry(&p.constitution),p.publication,p.continuation,contact.input);
    println!("{packet}");let root=std::path::PathBuf::from(std::env::var("V93_CONTROL_ARTIFACT_DIR")?);std::fs::create_dir_all(&root)?;std::fs::write(root.join("contact_packet.txt"),packet)?;
    // Continuity is distinct from the stronger positive-material influence requirement.
    if moved{assert!(proof.lower>integer(0));assert!(p.actual_alignment>p.actual_error_charge);}
    else{assert_eq!(proof.stored_pairing,integer(0));assert_eq!(proof.lower,integer(0));}
    assert_eq!(stream.accepted_cells()?,11);assert_eq!(stream.resident().prepared_input().unwrap().frontiers(),(11,0,0));
    println!("ZERO_MOTION_CONTINUITY_CONTACT_VERDICT outcome={} positive_material_influence={} selected_steps={} vanished={:?} retained_tails={} released_tails={} original_positive_motion_fixture_unchanged=true",if moved{"Applied"}else{"NoRealizedMotion"},moved,p.publication.steps.len(),p.publication.vanished,p.publication.unresolved_contact_material.len(),p.publication.released.len());
    stream=cold(&reference,&stream,&opening,"post-contact-source11")?;
    for (label,start,end) in [("next-R",11,20),("source30-close",20,30)]{
        let before=stream.resident().continuing_state(0)?;let pending=stream.pending_checkpoint();
        let outcome=stream.receive_native_current_diagnosed(&reference,&pairing,&data[start..end],64,&mut|e|{
            let bits=e.prediction.features.iter().flatten().map(|q|q.numer().bits().max(q.denom().bits())).max().unwrap_or(0);
            println!("ZERO_MOTION_CONTINUITY_SOURCE source={} commit={} feature_max_bits={bits}",e.prediction.source_cells,e.prediction.producing_commit);
        });
        let sections=match outcome{Ok(x)=>x,Err(e)=>{assert_eq!(stream.resident().continuing_state(0)?,before);assert_eq!(stream.pending_checkpoint(),pending);println!("ZERO_MOTION_CONTINUITY_REFUSAL boundary={label} rollback_exact=true error={e:?}");return Err(e.into());}};
        assert_eq!(sections.len(),1);assert_eq!(sections[0].publication_source,end as u64-1);assert!(sections[0].blind_carry_preserved);
        if end==30{assert!(sections[0].aeon_closed);}
        println!("ZERO_MOTION_CONTINUITY_SECTION_PASS boundary={label} publication={:?}",sections[0].publication);
    }
    let retained=stream.resident().continuing_state(0)?;let cold=cold(&reference,&stream,&opening,"final-source30")?;
    let(mut a,mut ac)=stream.native_current_query_fork(&reference,&pairing,64)?;let(mut b,mut bc)=cold.native_current_query_fork(&reference,&pairing,64)?;
    a.begin_hypothesized_output()?;b.begin_hypothesized_output()?;let theta=a.constitution().clone();let m=a.prepared_input().unwrap().material().clone();
    for(index,key)in [rat(1,7),rat(2,7),rat(3,7),rat(4,7)].into_iter().enumerate(){
        let x=reference.release_native_current_forecast(&mut a,&mut ac,&pairing,&key,64)?;let y=reference.release_native_current_forecast(&mut b,&mut bc,&pairing,&key,64)?;
        assert_eq!(x.prediction,y.prediction);assert_eq!(x.selected_class,y.selected_class);assert_eq!(a.carried(),b.carried());
        assert_eq!(a.constitution(),&theta);assert_eq!(b.constitution(),&theta);assert_eq!(a.prepared_input().unwrap().material(),&m);assert_eq!(b.prepared_input().unwrap().material(),&m);
        println!("ZERO_MOTION_CONTINUITY_FROZEN_PASS decision={index} key={key} class={}",x.selected_class);
    }
    assert_eq!(stream.resident().continuing_state(0)?,retained);
    println!("ZERO_MOTION_CONTINUITY_COMPLETE_PASS continuity=true positive_material_influence={moved} actual30=true firstR_contact_nextR_source30=true cold_and_frozen=true unsplit_trajectory_equivalence=false elapsed_ns={}",started.elapsed().as_nanos());Ok(())
}

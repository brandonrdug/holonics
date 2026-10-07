//! Native falsifiers of the consumed charted physical error contract, not a task accuracy gate.

use super::support::{contact, encoded, ring};
use crate::compression::landmark::context::{BaseMeasure, StopPrior};
use crate::hnn::constitution::{CAMPAIGN_ONE_BUDGET, Constitution};
use crate::hnn::field::{CribDeclaration, Current, Field, FieldDeclaration, FieldMaterial, ReceiverDeclaration};
use crate::hnn::moment::SourceMoment;
use crate::hnn::prediction::{DamagedSection, RepairedCell, repair_by_field};
use crate::hnn::prediction::charted::{ChartedPhysicalPublication, ChartedPhysicalResident, ChartedTolerance};
use crate::hnn::ratio::{Faces, HolonRatio, RatioCovector, target_phases};
use crate::hnn::receiving::ReceivingPhases;
use crate::hnn::retention::Diamond;
use crate::hnn::word::{Absorption, EndChange, ReceptionCarry, Word, WordOpening};
use crate::ratio::linear::ExactRatMatrix;
use crate::ratio::{Rat, integer, rat};
use num_traits::{Signed, Zero};

fn receiver() -> ReceiverDeclaration {
    ReceiverDeclaration { ring:0, aperture:3, tolerance:rat(1,16), depth:1,
        prior:StopPrior::half(),mass:1,base:BaseMeasure::Even,receiving_prior:0 }
}

fn field() -> Field {
    Field::declare(FieldDeclaration { rings:vec![ring(4,(0..4).collect()),ring(3,Vec::new())],
        contacts:vec![contact(0,1,3,0)],loops:Vec::new(),sources:vec![0],offsets:Vec::new(),
        alphabet:4,step:integer(1),exponent_grain:1,receivers:vec![receiver()],
        crib:CribDeclaration {window:16,offset:1},population:1<<16,lattice:Default::default(),
    }.by_lattice_rule()).unwrap()
}

/// One third of the original source map forces a genuine non-dyadic opening split. It is a
/// declared source relation, chosen independently of every target and comparison mask.
fn material(field:&Field, receiving:bool) -> Constitution {
    let theta=Constitution::initial(field,CAMPAIGN_ONE_BUDGET).unwrap();
    let source=theta.source_port(0).unwrap().scaled(&rat(1,3));
    theta.with_ports(0,None,Some(source),receiving.then(||ExactRatMatrix::identity(8).unwrap())).unwrap()
}

fn tolerance() -> ChartedTolerance {
    ChartedTolerance {logits:rat(1,16),receiving_covector:rat(1,16),source_covector:rat(1,16)}
}

fn positive(change:&EndChange)->bool {
    change.storage.iter().flatten().chain(change.arrivals.iter().flatten().flatten())
        .chain(change.states.iter().flatten().flatten()).chain(change.resonators.iter().flatten().flatten().flatten())
        .any(|x|!x.is_zero())
}

fn contains(actual:&EndChange,exact:&EndChange,radius:&EndChange) {
    let check=|a:&[Rat],e:&[Rat],r:&[Rat]| {
        assert_eq!(a.len(),e.len());assert_eq!(a.len(),r.len());
        for ((a,e),r) in a.iter().zip(e).zip(r) {assert!((a-e).abs()<=*r,"exact {e} charted {a} radius {r}");}
    };
    for ((a,e),r) in actual.storage.iter().zip(&exact.storage).zip(&radius.storage) {check(a,e,r);}
    for ((a,e),r) in actual.arrivals.iter().zip(&exact.arrivals).zip(&radius.arrivals) {
        for k in 0..2 {check(&a[k],&e[k],&r[k]);}
    }
    for ((a,e),r) in actual.states.iter().zip(&exact.states).zip(&radius.states) {
        for k in 0..2 {check(&a[k],&e[k],&r[k]);}
    }
    for ((a,e),r) in actual.resonators.iter().zip(&exact.resonators).zip(&radius.resonators) {
        if let (Some(a),Some(e),Some(r))=(a,e,r) {for k in 0..2 {check(&a[k],&e[k],&r[k]);}}
    }
    assert_eq!(actual.resonator_phases,exact.resonator_phases);
}

/// The existing exact Word and composition supply the comparison control. The observed
/// target enters after its physical forward; the second control continues its exact carry
/// on the learner's contemporary R, rather than resetting or teaching a separate control.
fn exact_comparison(field:&Field,theta:&Constitution,current:&Current,section:&DamagedSection,
    opening:&WordOpening,observed:&crate::hnn::encoding::Encoded,
) -> (RatioCovector,ExactRatMatrix,Vec<Vec<Rat>>,ReceptionCarry) {
    let phases=ReceivingPhases::declare(field,theta,current,&receiver()).unwrap();
    let mut source=SourceMoment::open_with(field,current,theta).unwrap();
    for &g in field.sources() {source=source.station_section(field,current,g,&section.placed()).unwrap();}
    let (mut word,_)=Word::open_exact_received(field,theta,current,&source,opening).unwrap();
    for _ in 1..phases.junction_steps() {word.tick().unwrap();}
    let entered_last=word.change().unwrap();
    word.last_junction().unwrap();
    let reads=phases.epochs().map(|crossing|phases.read(field,theta,current,word.anchor(crossing,0).unwrap()).unwrap()).collect::<Vec<_>>();
    let carry=word.reception_end().unwrap();
    assert_eq!(carry.change,entered_last,"the retained carry opens on the producing crossing");
    let emitted=word.released().unwrap().end;
    assert!(carry.change.storage!=emitted.storage || carry.change.arrivals!=emitted.arrivals,
        "the nonzero terminal scatter distinguishes emitted state from returned carry");
    let ratio=HolonRatio::compare_partition(Faces::of_reads(&reads,phases.grain()).unwrap(),
        &observed.classes_read().collect::<Vec<_>>(),&target_phases(field,current.lift(),0,observed).unwrap(),
        &[false,false,true]).unwrap();
    let g=ratio.covector().unwrap();
    let back=word.pull_back(&g,theta.receiving_map(0).unwrap(),&current.lift()[0],&phases).unwrap();
    let composed=crate::hnn::reference::compose_return(field,theta,
        &Diamond::opened(field,&phases,&opening.support(field)),current.lift(),current,&source,&back).unwrap();
    (g,composed.pullback.receiving.1,back.opening,carry)
}

fn comparison_contains(field:&Field,actual:&ChartedPhysicalPublication,
    exact:&(RatioCovector,ExactRatMatrix,Vec<Vec<Rat>>,ReceptionCarry),
) {
    let g=actual.teaching.ratio.covector().unwrap();
    for ((a,e),r) in g.logits().iter().flatten().zip(exact.0.logits().iter().flatten())
        .zip(actual.error.logit_covectors.iter().flatten()) {assert!((a-e).abs()<=*r);}
    for ((a,e),r) in actual.teaching.pullback.receiving.1.entries().iter().zip(exact.1.entries())
        .zip(actual.error.receiving_covector.entries()) {assert!((a-e).abs()<=*r);}
    for &ring in field.sources() {
        for ((a,e),r) in actual.error.source_opening[ring].iter().zip(&exact.2[ring])
            .zip(&actual.error.source_covectors[ring]) {assert!((a-e).abs()<=*r);}
    }
}

#[test]
fn charted_source_and_carry_error_enclose_the_same_exact_physical_passage() {
    let started=std::time::Instant::now();
    let field=field();let theta=material(&field,true);let current=Current::at_rest(&field);
    let observed=encoded(&field,&[0,1,2]);let damaged=DamagedSection::damage(&observed,&[2]).unwrap();
    let phases=ReceivingPhases::declare(&field,&theta,&current,&receiver()).unwrap();
    let mut resident=ChartedPhysicalResident::new(&field,theta.clone(),current.clone(),WordOpening::Rest,tolerance()).unwrap();
    let first=resident.receive(&damaged,&receiver(),|blind| {
        println!("charted blind input [0,1,missing] output {:?} reads {:?}",blind.cells,blind.reads);
        None
    }).unwrap();
    let exact=repair_by_field(&field,&theta,&current,&damaged,&WordOpening::Rest,&phases).unwrap();
    assert!(first.prediction.error.opening.closes());
    assert!(positive(&first.prediction.error.opening.error));
    assert!(first.prediction.physical.word.closes());
    contains(&first.prediction.physical.carry.change,&exact.carry.change,&first.prediction.error.end);
    for ((a,e),bound) in first.prediction.physical.reads.iter().zip(&exact.reads).zip(&first.prediction.error.stations) {
        for ((a,e),r) in a.read.logits.iter().zip(&e.read.logits).zip(&bound.logits) {assert!((a-e).abs()<=*r);}
    }
    assert!(matches!(first.prediction.physical.cells[2],RepairedCell::Held {..}));
    let exact_opening=WordOpening::Received {carry:exact.carry.clone(),absorption:Absorption::Nothing};
    let exact_second=repair_by_field(&field,&theta,&current,&damaged,&exact_opening,&phases).unwrap();
    let second=resident.receive(&damaged,&receiver(),|_|None).unwrap();
    contains(&second.prediction.physical.carry.change,&exact_second.carry.change,&second.prediction.error.end);
    assert_eq!(second.prediction.error.stations[0].tick,first.prediction.physical.carry.ticks);
    let old=&first.prediction.error.end;
    let entered=&second.prediction.error.initial;
    for (e,old) in entered.arrivals.iter().flatten().flatten().zip(old.arrivals.iter().flatten().flatten()) {assert!(e>=old);}
    for (e,old) in entered.states.iter().flatten().flatten().zip(old.states.iter().flatten().flatten()) {assert!(e>=old);}
    assert!(positive(resident.carry_error().unwrap()));
    println!("unit charted exact/carry enclosure elapsed_ms={}",started.elapsed().as_millis());
}

#[test]
fn charted_receiving_learning_charges_both_covectors_and_keeps_its_physical_carry() {
    let started=std::time::Instant::now();
    let field=field();let theta=material(&field,false);let current=Current::at_rest(&field);
    let observed=encoded(&field,&[0,1,2]);let damaged=DamagedSection::damage(&observed,&[2]).unwrap();
    let exact_first=exact_comparison(&field,&theta,&current,&damaged,&WordOpening::Rest,&observed);
    let source=theta.source_port(0).unwrap().clone();
    let mut resident=ChartedPhysicalResident::new(&field,theta.clone(),current.clone(),WordOpening::Rest,tolerance()).unwrap();
    let first=resident.receive(&damaged,&receiver(),|blind| {
        println!("charted before teaching input [0,1,missing] whole output {:?} reads {:?}",blind.cells,blind.reads);
        Some((observed,vec![false,false,true]))
    }).unwrap();
    let publication=first.comparison.unwrap().unwrap();
    comparison_contains(&field,&publication,&exact_first);
    assert!(publication.teaching.publication.stepped>0);
    assert!(publication.error.applied.holds());
    assert!(publication.error.applied.decrease>Rat::zero());
    assert!(publication.error.receiving_covector.entries().iter().any(|e|!e.is_zero()));
    assert_eq!(resident.constitution().source_port(0).unwrap(),&source);
    assert_ne!(resident.constitution().receiving_map(0),theta.receiving_map(0));
    let learned=resident.constitution().clone();
    let observed=encoded(&field,&[1,0,3]);let damaged=DamagedSection::damage(&observed,&[2]).unwrap();
    let exact_opening=WordOpening::Received {carry:exact_first.3,absorption:Absorption::Nothing};
    let exact_second=exact_comparison(&field,&learned,&current,&damaged,&exact_opening,&observed);
    let second=resident.receive(&damaged,&receiver(),|blind| {
        println!("charted learned blind input [1,0,missing] whole output {:?} reads {:?}",blind.cells,blind.reads);
        Some((observed,vec![false,false,true]))
    }).unwrap();
    let second_publication=second.comparison.unwrap().unwrap();
    comparison_contains(&field,&second_publication,&exact_second);
    assert!(second_publication.error.source_covectors[0].iter().any(|e|!e.is_zero()));
    assert!(second_publication.error.return_remainders.entries>0);
    assert_eq!(second.prediction.error.stations[0].tick,first.prediction.physical.carry.ticks);
    assert_eq!(second_publication.teaching.publication.commit,learned.commit()+1);
    assert!(second_publication.error.applied.holds());
    println!("charted learned source error {:?}, source rounding {:?}, receiving error {:?}, applied {:?}, adjoint remainder {:?}",
        second_publication.error.source_covectors,second_publication.error.source_rounding,
        second_publication.error.receiving_covector,second_publication.error.applied,second_publication.error.return_remainders);
    println!("unit charted receiving comparison elapsed_ms={}",started.elapsed().as_millis());
}

#[test]
fn charted_zero_tolerance_refuses_the_actual_opening_error_and_retains_the_blind_end() {
    let started=std::time::Instant::now();
    let field=field();let theta=material(&field,false);let current=Current::at_rest(&field);
    let observed=encoded(&field,&[0,1,2]);let damaged=DamagedSection::damage(&observed,&[2]).unwrap();
    let zero=ChartedTolerance {logits:Rat::zero(),receiving_covector:Rat::zero(),source_covector:Rat::zero()};
    let mut resident=ChartedPhysicalResident::new(&field,theta.clone(),current,WordOpening::Rest,zero).unwrap();
    let reception=resident.receive(&damaged,&receiver(),|blind| {
        println!("charted zero-tolerance blind whole output {:?}",blind.cells);
        Some((observed,vec![false,false,true]))
    }).unwrap();
    assert!(reception.comparison.is_err());
    assert_eq!(resident.constitution(),&theta);
    assert!(positive(&reception.prediction.error.opening.error));
    assert_eq!(resident.carry_error(),Some(&reception.prediction.error.end));
    let WordOpening::Received {carry,..}=resident.opening() else {panic!("a refusal retains its actual physical end")};
    assert_eq!(carry,&reception.prediction.physical.carry);
    println!("unit zero-tolerance refusal completed elapsed_ms={}",started.elapsed().as_millis());
}

#[test]
fn charted_loaded_pump_error_keeps_the_absolute_clock_across_the_carry() {
    let started=std::time::Instant::now();
    let field=field();let theta=super::prediction::pumped_at(&field,material(&field,true),0);
    let current=Current::at_rest(&field);let observed=encoded(&field,&[0,1,2]);
    let damaged=DamagedSection::damage(&observed,&[2]).unwrap();
    let phases=ReceivingPhases::declare(&field,&theta,&current,&receiver()).unwrap();
    let exact=repair_by_field(&field,&theta,&current,&damaged,&WordOpening::Rest,&phases).unwrap();
    let opening=WordOpening::Received {carry:exact.carry.clone(),absorption:Absorption::Nothing};
    let mut resident=ChartedPhysicalResident::new(&field,theta.clone(),current.clone(),opening.clone(),tolerance()).unwrap();
    let charted=resident.receive(&damaged,&receiver(),|_|None).unwrap();
    let continued=repair_by_field(&field,&theta,&current,&damaged,&opening,&phases).unwrap();
    contains(&charted.prediction.physical.carry.change,&continued.carry.change,&charted.prediction.error.end);
    assert_eq!(charted.prediction.error.stations[0].tick,exact.carry.ticks);
    assert!(charted.prediction.error.opening.closes());
    assert!(charted.prediction.physical.word.closes());
    assert!(positive(&charted.prediction.error.end));
    println!("unit charted loaded clock elapsed_ms={}",started.elapsed().as_millis());
}

#[test]
fn exact_sparse_comparison_keeps_the_complete_forward_and_receiving_return() {
    use crate::hnn::prediction::{Unresolved, predict_by_field, predict_sparse_by_field};
    let field=field();let theta=material(&field,false);let current=Current::at_rest(&field);
    let observed=encoded(&field,&[0,1,2]);let damaged=DamagedSection::damage(&observed,&[2]).unwrap();
    let phases=ReceivingPhases::declare(&field,&theta,&current,&receiver()).unwrap();
    let complete=predict_by_field(&field,&theta,&current,&damaged,&WordOpening::Rest,&phases).unwrap();
    let sparse=predict_sparse_by_field(&field,&theta,&current,&damaged,&WordOpening::Rest,&phases).unwrap();
    assert_eq!(sparse.prediction().reads,complete.prediction().reads);
    assert_eq!(sparse.prediction().carry,complete.prediction().carry);
    assert_eq!(sparse.prediction().opening,complete.prediction().opening);
    assert!(sparse.prediction().domains.iter().all(Option::is_none));
    assert!(complete.prediction().domains[2].is_some());
    assert!(matches!(&sparse.prediction().cells[2],RepairedCell::Held {unresolved:Unresolved::UncertifiedDomain,..}));
    let complete=complete.observe(&theta,&observed,&[false,false,true]).unwrap();
    let sparse=sparse.observe(&theta,&observed,&[false,false,true]).unwrap();
    assert_eq!(sparse.ratio,complete.ratio);
    assert_eq!(sparse.pullback.receiving,complete.pullback.receiving);
    assert_eq!(sparse.constitution,complete.constitution);
}

/// The matched notebook used the exact source predicate on a charted physical receipt.
/// Force its missing signed work through an actual non-dyadic source, and refuse corrupted
/// opening, Word and local tick receipts rather than bypassing any balance assertion.
#[test]
fn charted_physical_balance_consumes_its_actual_opening_split() {
    use crate::hnn::prediction::predict_sparse_by_field;
    let started = std::time::Instant::now();
    let field = field();
    let theta = material(&field, true);
    let current = Current::at_rest(&field);
    let observed = encoded(&field, &[0, 1, 2]);
    let damaged = DamagedSection::damage(&observed, &[2]).unwrap();
    let phases = ReceivingPhases::declare(&field, &theta, &current, &receiver()).unwrap();
    let exact = predict_sparse_by_field(&field, &theta, &current, &damaged,
        &WordOpening::Rest, &phases).unwrap().finish();
    assert!(exact.opening.closes() && exact.word.closes());
    assert!(exact.balances.iter().all(|balance| balance.closes()));
    let mut resident = ChartedPhysicalResident::new(&field, theta, current,
        WordOpening::Rest, tolerance()).unwrap();
    let prediction = resident.receive(&damaged, &receiver(), |_| None).unwrap().prediction;
    let split = prediction.error.opening.split.clone();
    assert!(!split.is_zero(), "the source must exercise the omitted opening work");
    let residual = &prediction.physical.opening.after - &prediction.physical.opening.before
        - &prediction.physical.opening.imposed + &prediction.physical.opening.absorbed;
    assert_eq!(residual, -&split, "the exact-only residual is the negative split work");
    assert!(!prediction.physical.opening.closes(), "the exact-only predicate must expose the omission");
    assert!(prediction.closes(), "the full actual charted work balance must close");

    let mut omitted = prediction.clone();
    omitted.error.opening.split = Rat::zero();
    assert!(!omitted.closes(), "missing actual split work must refuse");
    let mut foreign = prediction.clone();
    foreign.physical.opening.after += &split;
    assert!(foreign.physical.opening.closes());
    assert!(!foreign.closes(), "an exact-closing substituted source receipt must refuse");
    let mut detached = prediction.clone();
    detached.physical.word.open += &split;
    detached.physical.word.end += &split;
    assert!(detached.physical.word.closes(), "the isolated Word identity can still close");
    assert!(!detached.closes(), "a different Word opening must refuse");
    let mut word = prediction.clone();
    word.physical.word.end += &split;
    assert!(!word.closes(), "Word balance corruption must refuse");
    let mut tick = prediction.clone();
    tick.physical.balances[0].after += &split;
    assert!(!tick.closes(), "local tick balance corruption must refuse");
    println!("charted balance falsifier; split={split}; exact_only_opening_residual={residual}; charged_opening_residual={}; whole_output={:?}; elapsed_ns={}",
        &residual + &split, prediction.physical.cells, started.elapsed().as_nanos());
}

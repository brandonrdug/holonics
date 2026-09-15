use super::super::tests::{populate, seed};
use super::*;
use crate::embedding_fiber::ResidentReadout;
use num_bigint::BigInt;
use num_traits::Zero;

#[test]
#[ignore = "requires CUDA; resident field source joins outgoing and operative internal carriers"]
fn source_packs_boundary_and_internal_b_without_host_readout() {
    let readout = ResidentReadout::new().unwrap();
    let surface = ResidentSurface::on(&readout).unwrap();
    let mut field =
        NativeConstitutiveField::found_with_enclosed_junction(&surface, seed(), ResidentGrain(72))
            .unwrap();
    populate(&mut field);
    let before = field.census().section_read_outs;
    let source = field.read_current_source().unwrap();
    assert_eq!(field.census().section_read_outs, before);
    assert_eq!(source.field_cut(), field.occurrence_count());
    assert_eq!(source.occurrence(), Some(field.occurrence_count() - 1));
    assert_eq!(source.boundary_components(), 6);
    assert!(source.internal_components() >= 4);
    assert_eq!(
        source.enclosure().components(),
        6 + source.internal_components()
    );
    assert!(source.same_owner(&source));
    let births = source.births().to_vec();
    let actual = source.enclosure().inspect().unwrap();
    let boundary = field
        .inspect_junction_enclosure(3)
        .unwrap()
        .unwrap()
        .outgoing;
    let interior = field
        .stage_operative_contacts()
        .unwrap()
        .inspect()
        .unwrap()
        .internal;
    let expected = boundary
        .center
        .into_iter()
        .chain(interior.center)
        .collect::<Vec<_>>();
    assert_eq!(actual.center, expected);
    assert_eq!(actual.radius, boundary.radius + interior.radius);
    assert!(
        actual.center[3..]
            .iter()
            .any(|v| *v != ExactComplexWaveCurrent::zero())
    );
    let mut later =
        NativeFieldOccurrence::entering(vec![NativePhaseCurrent::new(2, 0, 1).unwrap()]);
    field.advance_resident(&mut later).unwrap();
    assert_eq!(source.field_cut(), 4);
    assert_eq!(source.internal_components(), 2 * births.len());
    assert_eq!(source.births(), births);
    assert_eq!(source.enclosure().inspect().unwrap(), actual);
}

#[test]
#[ignore = "requires CUDA; an aggregate-dark boundary still exposes its opposite internal currents"]
fn source_retains_dark_internal_pair() {
    use crate::native_ecology::constitutive_fibre::field::internal_current::tests::dark;
    let ro = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&ro).unwrap();
    let (mut field, _) = dark(&s, true, NativePhaseCurrent::new(0, 1, 1).unwrap());
    let exact = field.inspect_internal_currents().unwrap().unwrap();
    let source = field.read_current_source().unwrap();
    let read = source.enclosure().inspect().unwrap();
    let boundary = field
        .inspect_junction_enclosure(field.occurrence_count() - 1)
        .unwrap()
        .unwrap();
    let zero = ExactComplexWaveCurrent::zero();
    assert!(boundary.outgoing.contains(&vec![zero.clone(); 3]));
    assert!(boundary.held_current.contains(&vec![zero.clone(); 3]));
    assert!(exact.iter().any(|v| v.current != zero));
    let mut complete = vec![zero; 3];
    complete.extend(exact.into_iter().map(|v| v.current));
    assert!(read.contains(&complete));
}

#[test]
#[ignore="requires CUDA; operative material is a source with its own bound and caused column identities"]
fn material_source_retains_geometry_and_only_proven_points_enter_point_ports(){
    let ro=ResidentReadout::new().unwrap();let s=ResidentSurface::on(&ro).unwrap();
    let mut field=NativeConstitutiveField::found_with_enclosed_junction(&s,seed(),ResidentGrain(72)).unwrap();
    let empty=field.read_current_source().unwrap();assert!(empty.material().unwrap().is_none());
    let mut previous=None;
    for at in 0..4 {let incoming=vec![NativePhaseCurrent::new(at+1,1,1).unwrap()];
        let mut event=match previous.take(){Some(old)=>NativeFieldOccurrence::through(old,incoming),None=>NativeFieldOccurrence::entering(incoming)};
        previous=Some(field.advance_resident(&mut event).unwrap().source);
    }
    let source=field.read_current_source().unwrap();
    let before=s.census().section_read_outs;
    let material=source.material().unwrap().unwrap();let point=material.read_exact_point().unwrap();
    assert_eq!(s.census().section_read_outs,before);
    let actual=material.inspect().unwrap();assert_eq!(actual.radius,Rat::zero());
    assert_eq!(actual.center.len(),3*source.births().len());
    let words=s.read_out(&point).unwrap();let den=BigInt::from(words.last().unwrap().0);
    for (pair,v) in words[..words.len()-1].chunks_exact(2).zip(&actual.center){
        assert_eq!(v.real,Rat::new(pair[0].0.into(),den.clone()));
        assert_eq!(v.imaginary,Rat::new(pair[1].0.into(),den.clone()));
    }
    assert_eq!(source.material_difference(&source).unwrap().inspect().unwrap().radius,Rat::zero());
    let mut event=NativeFieldOccurrence::entering(vec![NativePhaseCurrent::unit()]);
    field.advance_resident(&mut event).unwrap();assert_eq!(source.material().unwrap().unwrap().inspect().unwrap(),actual);
    let current=field.read_current_source().unwrap();assert!(current.material_difference(&source).is_ok());
    let mut other=NativeConstitutiveField::found_with_enclosed_junction(&s,seed(),ResidentGrain(72)).unwrap();
    populate(&mut other);let uncertain=other.read_current_source().unwrap();
    assert!(uncertain.material_difference(&source).is_err());
    assert!(uncertain.material().unwrap().unwrap().inspect().unwrap().radius>Rat::zero());
    assert!(uncertain.material().unwrap().unwrap().read_exact_point().is_err());
    let bound=[0i128,0,1];let values=bound.into_iter().flat_map(|v|[v as i64,(v>>64) as i64]).map(|v|(v,v)).collect();
    let packet=s.mount_section_rest(&ResidentSectionRest::found(1,6,ResidentGrain(0),64,values).unwrap()).unwrap();
    assert!(ResidentNormalEnclosureView{surface:&s,section:&packet,offset:0,width:2,grain:ResidentGrain(72)}.read_exact_point().is_err());
}

#[test]
#[ignore="requires CUDA; the compiled material reflection encloses the exact physical operator and retains its signed residual"]
fn reflection_source_reuses_its_factor_and_preserves_the_complete_bound(){
    use crate::native_ecology::constitutive_fibre::PairedJunctionLinearization;
    let ro=ResidentReadout::new().unwrap();let s=ResidentSurface::on(&ro).unwrap();
    let mut field=NativeConstitutiveField::found_with_enclosed_junction(&s,seed(),ResidentGrain(32)).unwrap();populate(&mut field);
    let source=field.read_current_source().unwrap();let input=source.enclosure();
    let before=s.census().section_read_outs;let reflected=source.reflect(input).unwrap();
    assert_eq!(s.census().section_read_outs,before);
    let factor=source.reflection.get().unwrap() as *const _;
    let again=source.reflect(input).unwrap();assert_eq!(source.reflection.get().unwrap() as *const _,factor);
    assert_eq!(reflected.output().inspect().unwrap(),again.output().inspect().unwrap());
    let x=input.inspect().unwrap();let material=source.material().unwrap().unwrap().inspect().unwrap();
    let m=source.boundary_components()/2;let columns=material.center.chunks_exact(m).map(|v|v.to_vec()).collect::<Vec<_>>();
    let exact=PairedJunctionLinearization::at(columns.clone(),&x.center[..m],&x.center[m..]).unwrap();
    let expected=exact.outgoing().iter().chain(exact.internal()).cloned().collect::<Vec<_>>();
    let actual=reflected.output().inspect().unwrap();assert!(actual.contains(&expected));
    let v=actual.center[..m].iter().zip(&x.center[..m]).map(|(a,b)|a.add(b)).collect::<Vec<_>>();
    let dots=columns.iter().map(|d|d.iter().zip(&v).fold(ExactComplexWaveCurrent::zero(),|a,(d,v)|a.add(&d.conjugate().multiply(v)))).collect::<Vec<_>>();
    let residual=(0..m).map(|j|{
        columns.iter().zip(&dots).zip(&x.center[m..]).fold(v[j].subtract(&x.center[j].scaled(&Rat::from_integer(2.into()))),
            |a,((d,dv),b)|a.add(&d[j].multiply(&dv.subtract(&b.scaled(&Rat::from_integer(2.into()))))))
    }).collect::<Vec<_>>();
    assert_eq!(reflected.inspect_residual().unwrap(),residual);
    assert_eq!(field.occurrence_count(),source.field_cut());
}

use super::*;
use crate::alpha::{checkpoint::SavedTextField, text_codec::with_text_field_source};
use holonic_engine::{
    native_ecology::constitutive_fibre::{
        NativeFieldIncoming, NativeMaterialTransportSource, ResidentConstitutiveCurrent,
    },
    resident_section::{ResidentGrain, ResidentSectionRest},
};
use num_traits::Zero;

fn prepare<'c>(
    session: &mut TextFieldSession<'_, 'c>,
) -> Result<ResidentContextualSection<'c>, AlphaMaterialError> {
    session.receive(TextSymbol::Octet(b'A'))?;
    let anchor = session.retain_part_source()?;
    session.begin_part(Some(&anchor))?;
    session.receive(TextSymbol::Octet(b'B'))?;
    session.begin_part(Some(&anchor))?;
    session.receive(TextSymbol::Octet(b'C'))?;
    session.derive_contextual_contrast([1, 2])
}
fn excited<'c>(
    section: &ResidentContextualSection<'c>,
    numerator: i64,
    denominator: i64,
) -> ResidentConstitutiveReturn<'c> {
    let current = section
        .surface()
        .mount_section_rest(
            &ResidentSectionRest::found(
                1,
                3,
                ResidentGrain(0),
                64,
                vec![(numerator, numerator), (0, 0), (denominator, denominator)],
            )
            .unwrap(),
        )
        .unwrap();
    section
        .read_absolute(ResidentConstitutiveCurrent::rational(&current).unwrap())
        .unwrap()
}

#[test]
#[ignore = "requires CUDA; ordinary constitutive generation retains an actual supported current"]
fn constitutive_generation_preserves_its_native_return() {
    with_text_field_source(72, NativeMaterialTransportSource::HomogeneousMoment, |field| {
        let first = field.advance_resident(&mut NativeFieldOccurrence::entering(
            TextSymbol::Octet(b'A').inputs(),
        ))?;
        let anchor = field.retain_source(&first.source)?;
        let expected: Vec<_> = TextSymbol::Octet(b'Z').inputs().iter().map(|current| {
            if *current == holonic_engine::native_ecology::constitutive_fibre::NativePhaseCurrent::zero() {
                *current
            } else {
                holonic_engine::native_ecology::constitutive_fibre::NativePhaseCurrent::new(2,0,1).unwrap()
            }
        }).collect();
        field.advance_resident(&mut NativeFieldOccurrence::through_anchor(&anchor,expected.clone()))?;
        // The original emission is still available: only its immutable anchor was used above.
        let mut session = TextFieldSession::on(field)?;
        session.latest = Some(TextFieldSource { source:first.source, occurrence:0 });
        let before = session.field().census();
        let generation = session.generate_with_receiver(1, TextCurrentReceiver::Constitutive);
        assert_eq!(generation.emitted_octets, vec![b'Z']);
        assert!(matches!(generation.disposition, TextGenerationDisposition::Interrupted));
        assert_eq!(session.field().occurrence_count(),3);
        assert_eq!(session.field().census().section_read_outs-before.section_read_outs,1);
        assert!(matches!(session.field().lineage(2).unwrap().incoming,
            NativeFieldIncoming::Resident { resident_nodes:18 }));
        assert_eq!(session.field().inspect_incoming(2)?,expected);
        assert_ne!(expected,TextSymbol::Octet(b'Z').inputs());
        Ok(())
    }).unwrap();
}

#[test]
#[ignore = "requires CUDA; generated amplitude enters the continuing text field and survives restart without unit-codeword replay"]
fn generated_current_reenters_and_restarts_in_its_actual_chart() {
    let dir = tempfile::tempdir().unwrap();
    let path = dir.path().join("native-input.hna");
    let expected = with_text_field_source(
        72,
        NativeMaterialTransportSource::HomogeneousMoment,
        |field| {
            let mut session = TextFieldSession::on(field)?;
            let section = prepare(&mut session)?;
            let returned = excited(&section, 2, 1);
            let before = session.field().census();
            let symbol = session.receive_native_return(returned)?;
            assert_eq!(symbol, TextSymbol::Octet(b'C'));
            // The only host projection is the five-word terminal codeword/status receiver.
            assert_eq!(
                session.field().census().section_read_outs - before.section_read_outs,
                1
            );
            assert_eq!(
                session.field().census().egress_section_octets - before.egress_section_octets,
                80
            );
            assert_eq!(session.field().occurrence_count(), 4);
            assert!(matches!(
                session.field().lineage(3).unwrap().incoming,
                NativeFieldIncoming::Resident { resident_nodes: 18 }
            ));
            let actual = session.field().inspect_incoming(3)?;
            assert_ne!(actual, symbol.inputs());
            session.checkpoint(&path, &[], b"native-current")?;
            Ok(actual)
        },
    )
    .unwrap();
    SavedTextField::read(&path)
        .unwrap()
        .with_session(|session, _, _, app| {
            assert_eq!(app, b"native-current");
            assert_eq!(session.field().inspect_incoming(3)?, expected);
            session.receive(TextSymbol::Octet(b'D'))?;
            assert_eq!(session.field().occurrence_count(), 5);
            Ok(())
        })
        .unwrap();
}

#[test]
#[ignore = "requires CUDA; a refused generated current retains its exact input and source across checkpoint and retry"]
fn pending_native_input_preserves_amplitude_and_source_capability() {
    let dir = tempfile::tempdir().unwrap();
    let path = dir.path().join("pending-native.hna");
    let pending = with_text_field_source(
        72,
        NativeMaterialTransportSource::HomogeneousMoment,
        |field| {
            let mut session = TextFieldSession::on(field)?;
            let section = prepare(&mut session)?;
            let returned = excited(&section, -1, 2);
            assert_eq!(
                session.stage_native_return(returned)?,
                TextSymbol::Octet(b'B')
            );
            assert!(session.retry_pending().is_err());
            assert_eq!(session.field().occurrence_count(), 3);
            assert_eq!(session.pending_symbol(), Some(TextSymbol::Octet(b'B')));
            let pending =
                serde_json::to_value(session.pending_native.as_ref().unwrap().rest()?).unwrap();
            session.checkpoint(&path, &[], b"pending-native")?;
            Ok(pending)
        },
    )
    .unwrap();
    SavedTextField::read(&path)
        .unwrap()
        .with_session(|session, _, _, _| {
            assert_eq!(
                serde_json::to_value(session.pending_native.as_ref().unwrap().rest()?).unwrap(),
                pending
            );
            assert!(session.retry_pending().is_err());
            assert_eq!(session.field().occurrence_count(), 3);
            assert!(session.pending.as_ref().unwrap().1.source_ref().is_some());
            assert_eq!(
                serde_json::to_value(session.pending_native.as_ref().unwrap().rest()?).unwrap(),
                pending
            );
            Ok(())
        })
        .unwrap();
}

#[test]
#[ignore = "requires CUDA; ordinary text intake forms every source-family return with no selected historical pair"]
fn ordinary_text_intake_forms_contextual_references_and_restarts() {
    let dir = tempfile::tempdir().unwrap();
    let path = dir.path().join("ordinary-context.hna");
    with_text_field_source(
        72,
        NativeMaterialTransportSource::BilinearContextual,
        |field| {
            let mut session = TextFieldSession::on(field)?;
            let before = session.field().census();
            for byte in b"ababac" {
                session.receive(TextSymbol::Octet(*byte))?;
            }
            assert_eq!(
                session.field().census().section_read_outs,
                before.section_read_outs
            );
            let invariant = session
                .field()
                .inspect_contextual_material_transport(4)?
                .unwrap();
            let changed = session
                .field()
                .inspect_contextual_material_transport(5)?
                .unwrap();
            assert_eq!(invariant.reference_receiving_occurrence, Some(2));
            assert_eq!(changed.reference_receiving_occurrence, Some(3));
            assert_eq!(changed.input_context_occurrence, Some(4));
            assert_eq!(changed.source_occurrence, Some(4));
            assert!(changed.condition_change.unwrap().radius.is_zero());
            assert!(changed.parameter_change.unwrap().radius.is_zero());
            session.checkpoint(&path, &[], b"ordinary-context")?;
            Ok(())
        },
    )
    .unwrap();
    SavedTextField::read(&path)
        .unwrap()
        .with_session(|session, _, _, _| {
            assert_eq!(
                session.field().material_transport_source(),
                Some(NativeMaterialTransportSource::BilinearContextual)
            );
            assert_eq!(session.field().occurrence_count(), 6);
            session.receive(TextSymbol::Octet(b'b'))?;
            assert_eq!(session.field().occurrence_count(), 7);
            Ok(())
        })
        .unwrap();
}

#[test]
#[ignore="requires CUDA; directed native intake, quadrature replies and pending-direction persistence"]
fn duplex_intake_and_emission_keep_their_boundary_current_across_restart(){
    use crate::alpha::text_codec::{with_text_field_chart,read_text_symbol_on,TextDirection};
    use holonic_engine::native_ecology::constitutive_fibre::{NativeMaterialTarget,NativePacketQuadrature};
    let dir=tempfile::tempdir().unwrap();let path=dir.path().join("duplex.hna");
    let (expected,generation)=with_text_field_chart(72,NativeMaterialTransportSource::OperativeBoundary,
        NativeMaterialTarget::TensorProduct{factor_width:2},|field|{
        let mut session=TextFieldSession::on(field)?;session.enable_duplex()?;
        session.receive(TextSymbol::Octet(b'A'))?;
        session.receive_on(TextSymbol::Octet(b'B'),TextDirection::Outgoing)?;
        let observed=session.field().inspect_contextual_material_transport(1)?.unwrap().observed;
        assert_eq!(observed.center[b'B' as usize].real,num_rational::BigRational::from_integer(0.into()));
        assert_eq!(observed.center[b'B' as usize].imaginary,num_rational::BigRational::from_integer(1.into()));
        assert!(matches!(read_text_symbol_on(session.field(),1,TextDirection::Outgoing)?.disposition,
            TextCodeDisposition::Symbol{symbol:TextSymbol::Octet(b'B')}));
        assert!(matches!(read_text_symbol_on(session.field(),1,TextDirection::Incoming)?.disposition,TextCodeDisposition::Open));
        let packed=session.field().pack_material_report(1)?;
        assert_eq!(packed.read_packet_quadrature(NativePacketQuadrature::Imaginary)?.selected,Some(b'B' as usize));
        session.stage_on(TextSymbol::Octet(b'C'),TextDirection::Outgoing)?;
        assert_eq!(session.pending.as_ref().unwrap().1.incoming(),TextSymbol::Octet(b'C').inputs_on(TextDirection::Outgoing));
        session.checkpoint(&path,&[],b"directional pending input")?;
        session.retry_pending()?;
        let generation=session.generate(4);
        assert!(!generation.readings.is_empty());
        for reading in &generation.readings {
            let crate::alpha::text_codec::TextNativeReading::Packet(native)=&reading.native else{panic!("joint packet receiver required")};
            assert_eq!(native.quadrature,NativePacketQuadrature::Imaginary);
        }
        for at in generation.native_from..generation.native_until {
            assert!(TextSymbol::from_inputs_on(&session.field().inspect_incoming(at)?,TextDirection::Outgoing).is_some());
        }
        Ok((session.field().rest(&[session.latest.as_ref().map(|s|&s.source)],&[])?,serde_json::to_value(generation).unwrap()))
    }).unwrap();
    let saved=SavedTextField::read(&path).unwrap();assert!(saved.duplex());
    saved.with_session(|session,_,_,app|{
        assert_eq!(app,b"directional pending input");assert!(session.duplex());
        assert_eq!(session.pending_direction(),Some(TextDirection::Outgoing));
        assert_eq!(session.pending.as_ref().unwrap().1.incoming(),TextSymbol::Octet(b'C').inputs_on(TextDirection::Outgoing));
        session.retry_pending()?;
        assert_eq!(serde_json::to_value(session.generate(4)).unwrap(),generation);
        assert_eq!(session.field().rest(&[session.latest.as_ref().map(|s|&s.source)],&[])?,expected);
        Ok(())
    }).unwrap();
}

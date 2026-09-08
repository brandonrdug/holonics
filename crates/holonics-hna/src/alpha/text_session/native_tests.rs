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

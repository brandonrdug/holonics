use super::*;

#[test]
#[ignore = "requires CUDA and HOLONICS_ALPHA_TEST_EXPOSURE; resumes an actual partly admitted reply"]
fn partial_actual_part_keeps_its_parent_and_enacts_the_staged_symbol_once() {
    let path = std::env::var("HOLONICS_ALPHA_TEST_EXPOSURE").expect("private exposure path");
    let mut expected_records = Vec::new();
    let expected = with_text_field(72, |field| {
        let mut session = TextFieldSession::on(field)?;
        let mut reader = ExposureReader::open(&path).map_err(exposure_error)?;
        cultivate(
            &mut reader,
            &mut session,
            2,
            &mut expected_records,
            &mut AnchorMap::new(),
        )?;
        Ok(session.field().rest(&[], &[])?)
    })
    .unwrap();
    let dir = tempfile::tempdir().unwrap();
    let checkpoint = dir.path().join("partial.hna");
    let mut reader = ExposureReader::open(&path).unwrap();
    let mut records = Vec::new();
    let mut anchor_families = Vec::new();
    with_text_field(72, |field| {
        let mut session = TextFieldSession::on(field)?;
        let mut anchors = AnchorMap::new();
        cultivate(&mut reader, &mut session, 1, &mut records, &mut anchors)?;
        let frame = reader.peek().map_err(exposure_error)?.unwrap().clone();
        let parts = frame.development_parts().map_err(exposure_error)?;
        let part = &parts[0];
        let parent = frame.shared_prior_parent().map_err(exposure_error)?.unwrap();
        let (anchor, parent_at) = anchors.get(&parent).expect("actual admitted parent");
        session.begin_part(Some(anchor))?;
        let start = session.field().occurrence_count();
        let symbols = part.text.as_ref().unwrap().bytes().map(TextSymbol::Octet)
            .chain([TextSymbol::EndPart]).collect::<Vec<_>>();
        let pending_index = 10;
        assert!(symbols.len() > pending_index);
        for symbol in &symbols[..pending_index] {
            session.receive(*symbol)?;
        }
        session.stage(symbols[pending_index])?;
        records.push(json!({"sequence":frame.sequence,"family":frame.family,
            "native_from":start,"native_until":session.field().occurrence_count(),"complete":false,
            "parts":[{"ordinal":part.ordinal,"pointer":part.pointer,"kind":part.kind,
                "source_octets":part.text.as_ref().unwrap().len(),"native_from":start,
                "native_until":session.field().occurrence_count(),"parent_source_occurrence":parent_at,
                "failure":{"symbol_index":pending_index,"symbol":symbols[pending_index],
                    "error":"test interruption before enactment"}}]}));
        anchor_families = anchors.iter().map(|(family, (_, at))| (family.clone(), *at)).collect();
        let sources = anchors.values().map(|(source, _)| source).collect::<Vec<_>>();
        session.checkpoint(&checkpoint, &sources, b"partial actual reply")?;
        Ok(())
    })
    .unwrap();
    // The preceding owner is gone. The original cold reader still owns the unacknowledged
    // occurrence; resume that exact cursor in a fresh reader alongside the saved native state.
    let cursor = reader.cursor();
    drop(reader);
    SavedTextField::read(&checkpoint)
        .unwrap()
        .with_session(|session, _, restored, _| {
            assert_eq!(session.field().census().deed_launches, 0);
            let before = session.field().occurrence_count();
            let mut reader = ExposureReader::resume(cursor).map_err(exposure_error)?;
            let mut anchors = anchor_families
                .into_iter()
                .zip(restored)
                .map(|((family, at), source)| (family, (source, at)))
                .collect();
            cultivate(&mut reader, session, 1, &mut records, &mut anchors)?;
            assert_eq!(records, expected_records);
            assert_eq!(session.field().rest(&[], &[])?, expected);
            assert_eq!(
                session.field().census().deed_launches as usize,
                session.field().occurrence_count() - before
            );
            assert!(session.pending_symbol().is_none());
            assert_eq!(reader.cursor().next_sequence, 2);
            Ok(())
        })
        .unwrap();
}

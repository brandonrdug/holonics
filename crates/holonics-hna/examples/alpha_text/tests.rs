use super::*;
use holonics_hna::alpha::text_codec::with_text_field_source;

#[test]
#[ignore = "requires CUDA; leading unmounted material cannot remove the first textual part's actual parent"]
fn leading_nontext_material_preserves_the_available_native_parent() {
    let dir = tempfile::tempdir().unwrap();
    let path = dir.path().join("source.jsonl");
    let manifest = json!({"schema":"holonics.conversation-exposure.v1","kind":"manifest",
        "temporal_cut":"2026-09-04T00:00:00Z","temporal_cut_normalized":"2026-09-04T00:00:00.000000+00:00",
        "private_sources":[{"source":1,"provider":"codex","private_path":"fixture/source.jsonl","captured_octets":1000,"records":2}],
        "visible_parts":{"human":["human-text","human-material"]},"boundary":{}});
    let frame = |sequence: u64, id: &str, text: &str, time: &str| {
        json!({
        "schema":"holonics.conversation-exposure.v1","kind":"occurrence-family","sequence":sequence,
        "position":{"first_source":1,"first_record":sequence+1,"first_event":sequence+1},"conflicts":[],
        "family":{"provider":"codex","record_group":format!("declared:{id}")},"partition":"development","partition_reasons":[],
        "views":[{"event":sequence+1,"source":1,"provider":"codex",
            "record":{"number":sequence+1,"byte_start":sequence*100,"byte_end":(sequence+1)*100},
            "timestamp":time,"normalized_timestamp":time,"native_id":id,"parent_id":null,"session_id":"fixture",
            "branch_id":null,"workspace":null,"phase":null,"turn_id":null,"model":null,"author_class":"human",
            "record_kind":"message","flags":[],"provider_metadata":{},"previous_record":null,
            "visible_parts":[{"ordinal":1,"pointer":"/text","kind":"human-text","text":text}],
            "nonvisible_part_references":[],"links":[]}]})
    };
    let parent = frame(0, "parent", "A", "2026-09-03T00:00:00.000000+00:00");
    let mut child = frame(1, "child", "B", "2026-09-03T00:00:01.000000+00:00");
    child["views"][0]["visible_parts"]
        .as_array_mut()
        .unwrap()
        .insert(
            0,
            json!({"ordinal":0,"pointer":"/image","kind":"human-material","text":null}),
        );
    child["views"][0]["links"] = json!([{"kind":"provider-parent","target_event":1,"reference":null,"evidence":"fixture parent",
        "target":{"event":1,"source":1,"provider":"codex","record_group":"declared:parent",
            "timestamp":"2026-09-03T00:00:00.000000+00:00","normalized_timestamp":"2026-09-03T00:00:00.000000+00:00"},"availability":"prior"}]);
    let mut bytes = Vec::new();
    for value in [manifest, parent, child] {
        bytes.extend(serde_json::to_vec(&value).unwrap());
        bytes.push(b'\n');
    }
    std::fs::write(&path, bytes).unwrap();
    with_text_field_source(
        72,
        NativeMaterialTransportSource::CompleteCurrent,
        |field| {
            let mut session = TextFieldSession::on(field)?;
            let mut reader = ExposureReader::open(&path).map_err(exposure_error)?;
            let mut records = Vec::new();
            cultivate(
                &mut reader,
                &mut session,
                2,
                &mut records,
                &mut AnchorMap::new(),
            )?;
            assert_eq!(records[1]["parts"][0]["ordinal"], 1);
            assert_eq!(records[1]["parts"][0]["parent_source_occurrence"], 1);
            assert_eq!(session.field().lineage(2).unwrap().received_from, Some(1));
            assert_eq!(session.field().occurrence_count(), 4);
            Ok(())
        },
    )
    .unwrap();
    // A legacy pending inscription may already have been staged without a parent. Do not
    // relabel its actual receiving history when completing it under the corrected driver.
    with_text_field_source(72,NativeMaterialTransportSource::CompleteCurrent,|field|{
        let mut session=TextFieldSession::on(field)?;let mut reader=ExposureReader::open(&path).map_err(exposure_error)?;
        let mut records=Vec::new();let mut anchors=AnchorMap::new();
        cultivate(&mut reader,&mut session,1,&mut records,&mut anchors)?;
        session.begin_part(None)?;session.stage(TextSymbol::Octet(b'B'))?;
        let frame=reader.peek().map_err(exposure_error)?.unwrap();
        records.push(json!({"sequence":frame.sequence,"family":frame.family,"native_from":2,"native_until":2,"complete":false,
            "parts":[{"ordinal":1,"pointer":"/text","kind":"human-text","source_octets":1,"native_from":2,"native_until":2,
                "parent_source_occurrence":null,"failure":{"symbol_index":0,"symbol":TextSymbol::Octet(b'B'),"error":"legacy pending inscription"}}]}));
        cultivate(&mut reader,&mut session,1,&mut records,&mut anchors)?;
        assert_eq!(session.field().lineage(2).unwrap().received_from,None);
        assert!(records[1]["parts"][0]["parent_source_occurrence"].is_null());Ok(())
    }).unwrap();
}

#[test]
#[ignore = "requires CUDA and HOLONICS_ALPHA_TEST_EXPOSURE; resumes an actual partly admitted reply"]
fn partial_actual_part_keeps_its_parent_and_enacts_the_staged_symbol_once() {
    let path = std::env::var("HOLONICS_ALPHA_TEST_EXPOSURE").expect("private exposure path");
    let mut expected_records = Vec::new();
    let expected = with_text_field_source(
        72,
        NativeMaterialTransportSource::CompleteCurrent,
        |field| {
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
        },
    )
    .unwrap();
    let dir = tempfile::tempdir().unwrap();
    let checkpoint = dir.path().join("partial.hna");
    let mut reader = ExposureReader::open(&path).unwrap();
    let mut records = Vec::new();
    let mut anchor_families = Vec::new();
    with_text_field_source(72, NativeMaterialTransportSource::CompleteCurrent, |field| {
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
        .with_session_archived(
            dir.path().join("historical-sections"),
            |session, _, restored, _| {
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
            },
        )
        .unwrap();
}

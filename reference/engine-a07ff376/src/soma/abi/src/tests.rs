use super::{contact, current, holon, presentation, register};

#[test]
fn active_event_rows_have_one_world_local_tag_and_exact_payload_extent() {
    let header = current::EventHeader::new(7, 13).unwrap();
    assert_eq!(header.words(), [7, 13]);
    assert_eq!(header.local_tag(), 7);
    assert_eq!(header.payload_words(), 13);
    assert_eq!(current::EventHeader::from_words([7, 13]), Some(header));
    assert_eq!(current::EventHeader::new(0, 13), None);
    assert_eq!(current::EventHeader::new(7, 0), None);
    assert_eq!(current::U64_WORDS, 2);
    assert_eq!(current::U128_WORDS, 4);
    assert_eq!(current::SHA256_WORDS, 8);
}

#[test]
fn register_rows_retain_the_existing_word_contract() {
    assert_eq!(register::STATUS_WORDS, 3);
    assert_eq!(register::LANE_WORDS, 10);
    assert_eq!(register::LANE_OWN_WORD_BASE, 6);
    assert_eq!(register::LANE_CAPACITY_CELLS, 7);
    assert_eq!(register::LANE_CARRIER_WORD_BASE, 8);
    assert_eq!(register::LANE_CARRIER_ROW_WORDS, 9);
    assert_eq!(register::StatusRow::complete().words(), [0, 0, 0]);
    assert_eq!(
        register::StatusRow::needs_own_recast(64, 128).words(),
        [1, 64, 128]
    );
    assert_eq!(register::StatusRow::continuing().words(), [2, 0, 0]);
    let pressure = register::StatusRow::needs_carrier_rebase((1u64 << 40) + 7);
    assert_eq!(pressure.words(), [3, 7, 256]);
    assert_eq!(
        pressure.kind(),
        Some(register::StatusKind::NeedsCarrierRebase)
    );
    assert_eq!(pressure.required_carrier_depth(), (1u64 << 40) + 7);
}

#[test]
fn presentation_rows_keep_events_configurations_and_incidence_typed_apart() {
    let header = presentation::Header::new((1u64 << 33) + 19, 3, 2, 5).unwrap();
    assert_eq!(header.events(), (1u64 << 33) + 19);
    assert_eq!(header.currents(), 3);
    assert_eq!(header.configurations(), 2);
    assert_eq!(header.incidences(), 5);
    assert_eq!(
        presentation::Header::from_words(header.words()),
        Some(header)
    );
    assert_eq!(presentation::Header::new(0, 3, 2, 5), None);

    let current = presentation::CurrentSpan::new((1u64 << 32) + 7, 23).unwrap();
    assert_eq!(current.event_offset(), (1u64 << 32) + 7);
    assert_eq!(current.events(), 23);
    assert_eq!(presentation::CurrentSpan::new(7, 0), None);

    let configuration = presentation::ConfigurationSpan::new((1u64 << 32) + 11, 4).unwrap();
    assert_eq!(configuration.incidence_offset(), (1u64 << 32) + 11);
    assert_eq!(configuration.incidences(), 4);
    assert_eq!(presentation::ConfigurationSpan::new(11, 0), None);

    let incidence =
        presentation::Incidence::new((1u64 << 40) + 5, (1u64 << 33) + 9, (1u64 << 32) + 7).unwrap();
    assert_eq!(incidence.current(), (1u64 << 40) + 5);
    assert_eq!(incidence.current_event_offset(), (1u64 << 33) + 9);
    assert_eq!(incidence.current_events(), (1u64 << 32) + 7);
    assert_eq!(presentation::Incidence::new(0, 9, 0), None);
}

#[test]
fn holon_rows_retain_sparse_shared_cuts_and_complete_return_order() {
    let header = holon::Header::new((1u64 << 33) + 7, 2, 9, 1, 2, 2, 3).unwrap();
    assert_eq!(header.cuts(), (1u64 << 33) + 7);
    assert_eq!(header.holons(), 2);
    assert_eq!(header.cut_incidences(), 9);
    assert_eq!(header.receipts(), 1);
    assert_eq!(header.receipt_incidences(), 2);
    assert_eq!(header.residuals(), 2);
    assert_eq!(header.residual_incidences(), 3);
    assert_eq!(holon::Header::from_words(header.words()), Some(header));

    let cut = holon::BoundaryCut::new((1u64 << 40) + 3, (1u64 << 32) + 5);
    assert_eq!(cut.presentation(), (1u64 << 40) + 3);
    assert_eq!(cut.configuration(), (1u64 << 32) + 5);

    let open = holon::HolonSpan::new(4, 3, 0, 0, 0, 0).unwrap();
    assert_eq!(open.cut_incidence_offset(), 4);
    assert_eq!(open.cut_incidences(), 3);
    assert_eq!(open.receipt_incidences(), 0);
    assert_eq!(open.residual_incidences(), 0);
    assert_eq!(holon::HolonSpan::new(4, 3, 9, 0, 0, 0), None);

    let residual = holon::ResidualSpan::new(8, (1u64 << 32) + 2, 4).unwrap();
    assert_eq!(residual.cut(), 8);
    assert_eq!(residual.configuration_incidence_offset(), (1u64 << 32) + 2);
    assert_eq!(residual.incidences(), 4);

    let receipt = holon::TransitionReceipt::new(1, 2, 3, 4, 5, 6, 7, 2).unwrap();
    assert_eq!(receipt.before_cut(), 1);
    assert_eq!(receipt.meeting_cut(), 2);
    assert_eq!(receipt.deed_cut(), 3);
    assert_eq!(receipt.consequence_cut(), 4);
    assert_eq!(receipt.return_cut(), 5);
    assert_eq!(receipt.after_cut(), 6);
    assert_eq!(receipt.residual_incidence_offset(), 7);
    assert_eq!(receipt.residual_incidences(), 2);
    assert_eq!(holon::TransitionReceipt::new(1, 2, 3, 4, 5, 6, 7, 0), None);

    let silent = holon::SilentReceipt::new(1, 2, 3, 6, 7, 2).unwrap();
    assert_eq!(silent.before_cut(), 1);
    assert_eq!(silent.meeting_cut(), 2);
    assert_eq!(silent.deed_cut(), 3);
    assert_eq!(silent.after_cut(), 6);
    assert_eq!(silent.residual_incidence_offset(), 7);
    assert_eq!(silent.residual_incidences(), 2);
    assert_eq!(
        holon::SilentReceipt::from_words(silent.words()),
        Some(silent)
    );
    assert_eq!(holon::SilentReceipt::new(1, 2, 3, 6, 7, 0), None);

    let standing = holon::SourceDispositionRow::standing();
    let continued = holon::SourceDispositionRow::continued((1u64 << 40) + 5);
    let ended = holon::SourceDispositionRow::ended();
    assert_eq!(standing.returned_current(), None);
    assert_eq!(continued.returned_current(), Some((1u64 << 40) + 5));
    assert_eq!(ended.returned_current(), None);
    assert_eq!(
        holon::SourceDispositionRow::from_words(standing.words()),
        Some(standing)
    );
    assert_eq!(
        holon::SourceDispositionRow::from_words(continued.words()),
        Some(continued)
    );
    assert_eq!(
        holon::SourceDispositionRow::from_words(ended.words()),
        Some(ended)
    );
    assert_eq!(
        holon::SourceDispositionRow::from_words([holon::SOURCE_STANDING, 1, 0]),
        None
    );

    let birth = holon::ReturnOriginRow::birth();
    let return_continued = holon::ReturnOriginRow::continued((1u64 << 39) + 7);
    assert_eq!(birth.source_current(), None);
    assert_eq!(return_continued.source_current(), Some((1u64 << 39) + 7));
    assert_eq!(
        holon::ReturnOriginRow::from_words(birth.words()),
        Some(birth)
    );
    assert_eq!(
        holon::ReturnOriginRow::from_words(return_continued.words()),
        Some(return_continued)
    );
    assert_eq!(
        holon::ReturnOriginRow::from_words([holon::RETURN_BIRTH, 1, 0]),
        None
    );

    let lineage = holon::LineageIncidenceRow::new(
        (1u64 << 35) + 3,
        (1u64 << 34) + 5,
        (1u64 << 36) + 9,
        (1u64 << 33) + 7,
    );
    assert_eq!(lineage.source_incidence(), (1u64 << 35) + 3);
    assert_eq!(lineage.source_event_offset(), (1u64 << 34) + 5);
    assert_eq!(lineage.returned_incidence(), (1u64 << 36) + 9);
    assert_eq!(lineage.returned_event_offset(), (1u64 << 33) + 7);
    assert_eq!(
        holon::LineageIncidenceRow::from_words(lineage.words()),
        lineage
    );

    let settlement = holon::SettlementSpan::returned(7, 3, 11, 2, 13, 1, 17, 4).unwrap();
    assert_eq!(settlement.transition(), 7);
    assert_eq!(settlement.kind(), holon::SETTLEMENT_RETURNED);
    assert_eq!(settlement.receipt(), 3);
    assert_eq!((settlement.source_offset(), settlement.sources()), (11, 2));
    assert_eq!((settlement.origin_offset(), settlement.origins()), (13, 1));
    assert_eq!(
        (settlement.lineage_offset(), settlement.lineages()),
        (17, 4)
    );
    assert_eq!(
        holon::SettlementSpan::from_words(settlement.words()),
        Some(settlement)
    );
    let silent_settlement = holon::SettlementSpan::silent(8, 5, 19, 3).unwrap();
    assert_eq!(silent_settlement.kind(), holon::SETTLEMENT_SILENT);
    assert_eq!(silent_settlement.origins(), 0);
    assert_eq!(silent_settlement.lineages(), 0);
    let settlement_header = holon::SettlementHeader::new(2, 1, 5, 1, 4).unwrap();
    assert_eq!(settlement_header.settlements(), 2);
    assert_eq!(settlement_header.silent_receipts(), 1);
    assert_eq!(settlement_header.source_dispositions(), 5);
    assert_eq!(settlement_header.return_origins(), 1);
    assert_eq!(settlement_header.lineage_incidences(), 4);
    assert_eq!(
        holon::SettlementHeader::from_words(settlement_header.words()),
        Some(settlement_header)
    );

    assert_eq!(holon::CutIncidence::new(11).ordinal(), 11);
    assert_eq!(holon::ReceiptIncidence::new(12).ordinal(), 12);
    assert_eq!(holon::ResidualIncidence::new(13).ordinal(), 13);
}

#[test]
fn holon_header_refuses_partial_population_pairs() {
    assert_eq!(holon::Header::new(1, 1, 1, 1, 0, 0, 0), None);
    assert_eq!(holon::Header::new(1, 1, 1, 0, 1, 0, 0), None);
    assert_eq!(holon::Header::new(1, 1, 1, 0, 0, 1, 0), None);
    assert_eq!(holon::Header::new(1, 1, 1, 0, 0, 0, 1), None);
    assert_eq!(holon::Header::new(1, 1, 1, 0, 0, 0, 0).unwrap().cuts(), 1);
}

#[test]
fn cooperative_contact_sheet_retains_the_existing_extent() {
    assert_eq!(contact::OUTPUT_WORDS, 1 + 2 * body::num::COG_WORDS);
    assert_eq!(
        contact::RECEIPT,
        contact::OUTPUT + body::register::REGISTER as usize * contact::OUTPUT_WORDS
    );
    assert_eq!(
        contact::SURFACE_WORDS,
        contact::RECEIPT + body::register::REGISTER as usize
    );
}

#[test]
fn register_entry_symbols_are_exact() {
    assert_eq!(register::Entry::Scope.symbol(), "scope_register");
    assert_eq!(
        register::Entry::ScopeSurface.symbol(),
        "scope_register_surface"
    );
    assert_eq!(register::Entry::Recast.symbol(), "register_own_recast");
    assert_eq!(
        register::Entry::RecastFinish.symbol(),
        "register_own_recast_finish"
    );
    assert_eq!(register::Entry::Scope.buffer_pairs(), 10);
    assert_eq!(register::Entry::ScopeSurface.buffer_pairs(), 11);
    assert_eq!(register::Entry::Recast.buffer_pairs(), 7);
    assert_eq!(register::Entry::RecastFinish.buffer_pairs(), 7);
    assert_eq!(register::Entry::Scope.cuda_parameter_words(), 20);
    assert_eq!(register::Entry::ScopeSurface.cuda_parameter_words(), 22);
    assert_eq!(register::Entry::Recast.cuda_parameter_words(), 14);
    assert_eq!(register::Entry::RecastFinish.cuda_parameter_words(), 14);
}

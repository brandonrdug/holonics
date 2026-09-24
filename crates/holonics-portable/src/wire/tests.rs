use super::{contact, register};

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
fn cooperative_contact_sheet_retains_the_existing_extent() {
    assert_eq!(contact::OUTPUT_WORDS, 1 + 2 * crate::num::COG_WORDS);
    assert_eq!(
        contact::RECEIPT,
        contact::OUTPUT + crate::register::REGISTER as usize * contact::OUTPUT_WORDS
    );
    assert_eq!(
        contact::SURFACE_WORDS,
        contact::RECEIPT + crate::register::REGISTER as usize
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

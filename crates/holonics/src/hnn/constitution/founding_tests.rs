use super::*;
#[test]
fn r4b_13_new_loci_follow_the_initial_rules_and_old_loci_are_unchanged() {
    let field = Field::declare(crate::hnn::field::founding_tests::listener(1, 1 << 16)).unwrap();
    let previous = Constitution::initial(&field, 1 << 40)
        .unwrap()
        .with_ports(0, Some(vec![rat(3, 8); field.ring(0).width()]), None, None)
        .unwrap();
    let expanded = field
        .found(crate::hnn::FoundedRing { period: 2, key: 1 })
        .unwrap();
    let declared = Constitution::initial(&expanded, 1 << 40).unwrap();
    let found = previous.clone().found_ring(&expanded, 3, 1 << 40).unwrap();
    assert_eq!(&found.rings[..3], previous.rings);
    assert_eq!(&found.contacts[..2], previous.contacts);
    assert_eq!(found.rings[3], declared.rings[3]);
    assert_eq!(found.contacts[2], declared.contacts[2]);
    assert!(found.source_law(3).unwrap().symmetry.is_none());
    assert_eq!(
        found.rings[3].transport,
        found.founding_transport(&expanded, 3).unwrap()
    );
    assert!(found.rings[3].resonator.is_some());
    for (locus, lattice) in &previous.lattices {
        assert_eq!(found.lattices.get(locus), Some(lattice));
    }
    assert_eq!(found.carries, previous.carries);
    assert_eq!(found.clocks, previous.clocks);
    assert_eq!(found.released, previous.released);
    assert_eq!(found.storage_product, previous.storage_product);
    assert!(matches!(
        previous.found_ring(&expanded, 3, 1),
        Err(HnnError::ConstitutionBudget { .. })
    ));
}

/// The state text has no schema header: the founded declaration follows `state g`, so a save
/// written before the founded lines existed is refused, typed, at that line, never misread.
#[test]
fn r4b_a_state_without_its_founded_lines_is_refused_at_them() {
    let field = Field::declare(crate::hnn::field::founding_tests::listener(1, 1 << 16)).unwrap();
    let text = Constitution::initial(&field, 1 << 40)
        .unwrap()
        .continuing_state(0)
        .unwrap()
        .to_text();
    assert!(text.starts_with("E "));
    assert!(text.contains("\nstate 0\nfounded 0\nfounding 0 -\n"));
    assert!(ContinuingState::from_text(&text).is_ok());
    let earlier = text.replacen("\nfounded 0\nfounding 0 -\n", "\n", 1);
    let check_at = earlier.rfind("\ncheck ").unwrap();
    let body = &earlier[..check_at + 1];
    let earlier = format!("{body}check {} {}\nend\n", body.len(), text_residue(body));
    assert!(matches!(
        ContinuingState::from_text(&earlier),
        Err(HnnError::ContinuingState {
            what: "the founded rings"
        })
    ));
}

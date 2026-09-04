use super::*;
use holonic_engine::image::{ExactRaster, ExactRgb, ImageExtent};

fn integer(value: i64) -> Rat {
    Rat::from_integer(BigInt::from(value))
}

fn fixture_occurrence(
    artifact: &ArtifactIdentity,
    ordinal: u64,
    payload: &[u8],
    left: i64,
    top: i64,
    right: i64,
    bottom: i64,
) -> PlacedCarrier {
    PlacedCarrier::new(
        artifact,
        ordinal,
        payload.to_vec(),
        Some(ordinal),
        ExactBox::new(integer(left), integer(top), integer(right), integer(bottom)).unwrap(),
    )
    .unwrap()
}

#[test]
fn decimal_coordinates_never_pass_through_float() {
    assert_eq!(
        exact_decimal("-12.375", 16).unwrap(),
        Rat::new((-99).into(), 8.into())
    );
    assert!(exact_decimal("1.2.3", 16).is_err());
    assert!(matches!(
        exact_decimal("12345", 4),
        Err(SourceLayoutError::DecimalApertureExceeded { .. })
    ));
}

#[test]
fn links_are_derived_and_equal_payloads_remain_distinct_occurrences() {
    let artifact = ArtifactIdentity::of_bytes("fixture-event", "fixture", b"whole").unwrap();
    let occurrences = vec![
        fixture_occurrence(&artifact, 0, b"same", 0, 0, 2, 2),
        fixture_occurrence(&artifact, 1, b"same", 3, 0, 5, 2),
        fixture_occurrence(&artifact, 2, b"third", 1, 4, 4, 6),
    ];
    assert_eq!(occurrences[0].payload_sha256, occurrences[1].payload_sha256);
    assert_ne!(occurrences[0].address, occurrences[1].address);
    let demand = layout_demand(&occurrences).unwrap();
    let returned = derive_layout(
        TestimonyChart::BornDigital,
        artifact,
        ExactExtent::new(integer(6), integer(8)).unwrap(),
        occurrences,
        &SourceLayoutWorkCover::exactly(&demand),
    )
    .unwrap();
    assert!(returned.contacts.iter().any(|contact| {
        contact.from == 0 && contact.to == 1 && contact.relation == LayoutRelation::HorizontalNext
    }));
    assert_eq!(returned.complex.as_ref().unwrap().sites().len(), 3);
}

#[test]
fn diagonal_pixel_contact_remains_a_two_population_fiber() {
    let white = ExactRgb {
        red: 255,
        green: 255,
        blue: 255,
    };
    let black = ExactRgb::default();
    let raster = ExactRaster::new(
        ImageExtent {
            width: 2,
            height: 2,
        },
        vec![black, white, white, black],
    )
    .unwrap();
    let demand = raster_demand(&raster).unwrap();
    let returned = derive_raster_fiber(
        "diagonal-event",
        "diagonal.png",
        b"encoded",
        &raster,
        white,
        &SourceLayoutWorkCover::exactly(&demand),
    )
    .unwrap();
    assert_eq!(returned.four_connected.occurrences.len(), 2);
    assert_eq!(returned.eight_connected.occurrences.len(), 1);
    assert_ne!(
        returned.four_connected.occurrences[0].address,
        returned.eight_connected.occurrences[0].address
    );
    let four_demand = raster_component_admission_demand(&returned.four_connected).unwrap();
    let four_layout = admit_raster_components(
        &returned.four_connected,
        ExactExtent::new(integer(2), integer(2)).unwrap(),
        &SourceLayoutWorkCover::exactly(&four_demand),
    )
    .unwrap();
    assert!(four_layout.contacts.is_empty());
    assert!(four_layout.complex.is_none());
    assert!(returned.omitted_background_alternatives_open);
}

#[test]
fn correspondence_keeps_every_overlap_and_every_unmatched_occurrence() {
    let left_artifact = ArtifactIdentity::of_bytes("left-event", "left", b"left").unwrap();
    let right_artifact = ArtifactIdentity::of_bytes("right-event", "right", b"right").unwrap();
    let left = vec![fixture_occurrence(&left_artifact, 0, b"l", 0, 0, 5, 5)];
    let right = vec![
        fixture_occurrence(&right_artifact, 0, b"r0", 1, 1, 2, 2),
        fixture_occurrence(&right_artifact, 1, b"r1", 3, 3, 4, 4),
        fixture_occurrence(&right_artifact, 2, b"far", 8, 8, 9, 9),
        fixture_occurrence(&right_artifact, 3, b"touch", 5, 0, 6, 1),
    ];
    let extent = ExactExtent::new(integer(10), integer(10)).unwrap();
    let left_demand = layout_demand(&left).unwrap();
    let left = derive_layout(
        TestimonyChart::BornDigital,
        left_artifact,
        extent.clone(),
        left,
        &SourceLayoutWorkCover::exactly(&left_demand),
    )
    .unwrap();
    let right_demand = layout_demand(&right).unwrap();
    let right = derive_layout(
        TestimonyChart::Raster,
        right_artifact,
        extent,
        right,
        &SourceLayoutWorkCover::exactly(&right_demand),
    )
    .unwrap();
    let demand = correspondence_demand(&left, &right).unwrap();
    let fiber = correspond(&left, &right, &SourceLayoutWorkCover::exactly(&demand)).unwrap();
    assert_eq!(fiber.left_candidates[&left.occurrences[0].address].len(), 2);
    assert_eq!(
        fiber.unmatched_right,
        BTreeSet::from([
            right.occurrences[2].address.clone(),
            right.occurrences[3].address.clone(),
        ])
    );
}

#[test]
fn reflow_can_preserve_serial_face_while_moving_spatial_incidence() {
    let artifact = ArtifactIdentity::of_bytes("base-event", "base", b"base").unwrap();
    let moved_artifact = ArtifactIdentity::of_bytes("moved-event", "moved", b"moved").unwrap();
    let base_occurrences = vec![
        fixture_occurrence(&artifact, 0, b"a", 0, 0, 2, 2),
        fixture_occurrence(&artifact, 1, b"b", 3, 0, 5, 2),
    ];
    let base_demand = layout_demand(&base_occurrences).unwrap();
    let base = derive_layout(
        TestimonyChart::BornDigital,
        artifact.clone(),
        ExactExtent::new(integer(10), integer(10)).unwrap(),
        base_occurrences,
        &SourceLayoutWorkCover::exactly(&base_demand),
    )
    .unwrap();
    let moved_occurrences = vec![
        fixture_occurrence(&moved_artifact, 0, b"a", 0, 0, 2, 2),
        fixture_occurrence(&moved_artifact, 1, b"b", 0, 3, 2, 5),
    ];
    let moved_demand = layout_demand(&moved_occurrences).unwrap();
    let moved = derive_layout(
        TestimonyChart::BornDigital,
        moved_artifact.clone(),
        ExactExtent::new(integer(10), integer(10)).unwrap(),
        moved_occurrences,
        &SourceLayoutWorkCover::exactly(&moved_demand),
    )
    .unwrap();
    let comparison = compare_presentations(&base, &moved);
    assert!(comparison.serial_payload_face_equal);
    assert!(!comparison.departed_contacts.is_empty());
    assert!(!comparison.arrived_contacts.is_empty());
    assert!(comparison.first_payload_separator.is_none());
}

#[test]
fn work_is_admitted_before_contacts_and_serial_ties_refuse() {
    let artifact = ArtifactIdentity::of_bytes("work-event", "work", b"work").unwrap();
    let mut occurrences = vec![
        fixture_occurrence(&artifact, 0, b"a", 0, 0, 1, 1),
        fixture_occurrence(&artifact, 1, b"b", 2, 0, 3, 1),
    ];
    let demand = layout_demand(&occurrences).unwrap();
    let starved = SourceLayoutWorkCover {
        pair_visits: demand.pair_visits.saturating_sub(1),
        sample_visits: demand.sample_visits,
        carried_octets: demand.carried_octets,
    };
    assert!(matches!(
        derive_layout(
            TestimonyChart::BornDigital,
            artifact.clone(),
            ExactExtent::new(integer(4), integer(2)).unwrap(),
            occurrences.clone(),
            &starved,
        ),
        Err(SourceLayoutError::WorkCoverInsufficient { .. })
    ));
    occurrences[1].serial_ordinal = Some(0);
    assert!(matches!(
        derive_layout(
            TestimonyChart::BornDigital,
            artifact,
            ExactExtent::new(integer(4), integer(2)).unwrap(),
            occurrences,
            &SourceLayoutWorkCover::exactly(&demand),
        ),
        Err(SourceLayoutError::DuplicateSerialOrdinal(0))
    ));
}

#[test]
fn presentation_contact_comparison_is_invariant_to_storage_permutation() {
    let before_artifact = ArtifactIdentity::of_bytes("before-event", "before", b"before").unwrap();
    let after_artifact = ArtifactIdentity::of_bytes("after-event", "after", b"after").unwrap();
    let before_occurrences = vec![
        fixture_occurrence(&before_artifact, 0, b"a", 0, 0, 1, 1),
        fixture_occurrence(&before_artifact, 1, b"b", 2, 0, 3, 1),
    ];
    let mut after_occurrences = vec![
        fixture_occurrence(&after_artifact, 0, b"a", 0, 0, 1, 1),
        fixture_occurrence(&after_artifact, 1, b"b", 2, 0, 3, 1),
    ];
    after_occurrences.reverse();
    let before_demand = layout_demand(&before_occurrences).unwrap();
    let after_demand = layout_demand(&after_occurrences).unwrap();
    let extent = ExactExtent::new(integer(4), integer(2)).unwrap();
    let before = derive_layout(
        TestimonyChart::BornDigital,
        before_artifact,
        extent.clone(),
        before_occurrences,
        &SourceLayoutWorkCover::exactly(&before_demand),
    )
    .unwrap();
    let after = derive_layout(
        TestimonyChart::BornDigital,
        after_artifact,
        extent,
        after_occurrences,
        &SourceLayoutWorkCover::exactly(&after_demand),
    )
    .unwrap();
    let comparison = compare_presentations(&before, &after);
    assert!(comparison.serial_payload_face_equal);
    assert!(comparison.departed_contacts.is_empty());
    assert!(comparison.arrived_contacts.is_empty());
}

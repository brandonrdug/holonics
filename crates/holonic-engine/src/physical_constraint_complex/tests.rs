use num_bigint::BigInt;

use super::*;

fn rat(n: i64, d: i64) -> Rat {
    Rat::new(BigInt::from(n), BigInt::from(d))
}

fn residue(source_ordinal: i32, monomer: &str, x: i64, y: i64) -> ResidueMaterial {
    ResidueMaterial {
        source_ordinal,
        monomer: monomer.to_owned(),
        position: CoordinateBox3::point(
            Rat::from_integer(BigInt::from(x)),
            Rat::from_integer(BigInt::from(y)),
            Rat::zero(),
        ),
    }
}

fn uncertainty(left: usize, right: usize) -> BTreeMap<(u32, u32), PairUncertainty> {
    let mut result = BTreeMap::new();
    for a in 1..=left as u32 {
        for b in 1..=right as u32 {
            result.insert(
                (a, b),
                PairUncertainty {
                    source_lineage: "exact-testimony".to_owned(),
                    row_given_column_bits: 0x3c00,
                    column_given_row_bits: 0x3c00,
                    row_given_column: ExactInterval::point(Rat::from_integer(BigInt::from(1))),
                    column_given_row: ExactInterval::point(Rat::from_integer(BigInt::from(1))),
                    row_given_column_ulp: rat(1, 1024),
                    column_given_row_ulp: rat(1, 1024),
                },
            );
        }
    }
    result
}

fn material(first_target_y: i64) -> Vec<ComponentMaterial> {
    vec![
        ComponentMaterial {
            lineage: "primary occurrence".to_owned(),
            residues: vec![
                residue(1, "A", 0, 0),
                residue(2, "B", 1, 0),
                residue(3, "C", 2, 0),
            ],
        },
        ComponentMaterial {
            lineage: "secondary occurrence".to_owned(),
            residues: vec![residue(1, "D", 0, first_target_y), residue(2, "E", 2, 1)],
        },
    ]
}

fn exact_classes(
    complex: &PhysicalConstraintComplex,
    left: ConstraintComponentId,
    right: ConstraintComponentId,
    aperture: &DistanceAperture,
) -> Vec<ContactClass> {
    let left = &complex.component(left).unwrap().vertices;
    let right = &complex.component(right).unwrap().vertices;
    left.iter()
        .flat_map(|a| {
            right.iter().map(|b| {
                aperture.classify(
                    &complex.vertices[a]
                        .position
                        .squared_distance(&complex.vertices[b].position),
                )
            })
        })
        .collect()
}

#[test]
fn contacts_found_higher_cells_and_return_their_algebraic_boundary() {
    let mut complex = PhysicalConstraintComplex::found("left", EventId(1), material(1)).unwrap();
    let aperture = DistanceAperture {
        lineage: "squared distance at or below two".to_owned(),
        squared: Rat::from_integer(BigInt::from(2)),
    };
    let enacted = exact_classes(
        &complex,
        ConstraintComponentId(1),
        ConstraintComponentId(2),
        &aperture,
    );
    complex
        .found_contact_family(
            ConstraintComponentId(1),
            ConstraintComponentId(2),
            aperture,
            &enacted,
            &uncertainty(3, 2),
        )
        .unwrap();

    assert_eq!(complex.contact_families[0].readings.len(), 6);
    assert_eq!(complex.contact_edges.len(), 4);
    assert_eq!(complex.faces.len(), 2);
    assert_eq!(complex.boundary.polygonal_ends.len(), 2);
    assert!(!complex.boundary.two_chain_boundary.is_empty());
    // Every face closes under boundary-of-boundary: each oriented edge's two endpoint hands cancel.
    for face in complex.faces.values() {
        let mut endpoints = BTreeMap::<ConstraintVertexId, i64>::new();
        for (edge, hand) in face.boundary().unwrap() {
            *endpoints.entry(edge.lower).or_default() -= i64::from(hand);
            *endpoints.entry(edge.upper).or_default() += i64::from(hand);
        }
        endpoints.retain(|_, coefficient| *coefficient != 0);
        assert!(endpoints.is_empty());
    }
}

#[test]
fn the_cross_presentation_fibre_preserves_kinship_and_returns_the_first_separator() {
    let aperture = DistanceAperture {
        lineage: "squared distance at or below two".to_owned(),
        squared: Rat::from_integer(BigInt::from(2)),
    };
    let mut left = PhysicalConstraintComplex::found("free", EventId(1), material(1)).unwrap();
    let mut right = PhysicalConstraintComplex::found("occluded", EventId(2), material(3)).unwrap();
    let left_enacted = exact_classes(
        &left,
        ConstraintComponentId(1),
        ConstraintComponentId(2),
        &aperture,
    );
    let right_enacted = exact_classes(
        &right,
        ConstraintComponentId(1),
        ConstraintComponentId(2),
        &aperture,
    );
    left.found_contact_family(
        ConstraintComponentId(1),
        ConstraintComponentId(2),
        aperture.clone(),
        &left_enacted,
        &uncertainty(3, 2),
    )
    .unwrap();
    right
        .found_contact_family(
            ConstraintComponentId(1),
            ConstraintComponentId(2),
            aperture,
            &right_enacted,
            &uncertainty(3, 2),
        )
        .unwrap();

    let fibre = cross_presentation_fibre(
        &left,
        &right,
        (ConstraintComponentId(1), ConstraintComponentId(2)),
        (ConstraintComponentId(1), ConstraintComponentId(2)),
    )
    .unwrap();
    assert_eq!(fibre.component_sequence_kinship.len(), 2);
    assert!(!fibre.shared_inside.is_empty());
    assert_eq!(
        fibre.shortest_separator,
        Some(ContactSeparator {
            left_primary_ordinal: 1,
            secondary_ordinal: 1,
            left_class: ContactClass::Inside,
            right_class: ContactClass::Outside,
        })
    );
}

#[test]
fn a_coordinate_box_crossing_the_aperture_remains_open() {
    let point = CoordinateBox3::point(Rat::zero(), Rat::zero(), Rat::zero());
    let uncertain = CoordinateBox3 {
        x: ExactInterval {
            lower: rat(19, 10),
            upper: rat(21, 10),
        },
        y: ExactInterval::point(Rat::zero()),
        z: ExactInterval::point(Rat::zero()),
    };
    let aperture = DistanceAperture {
        lineage: "radius two".to_owned(),
        squared: Rat::from_integer(BigInt::from(4)),
    };
    assert_eq!(
        aperture.classify(&point.squared_distance(&uncertain)),
        ContactClass::Open
    );
}

#[test]
fn a_carrier_disagreement_refuses_before_it_founds_incidence() {
    let mut complex = PhysicalConstraintComplex::found("left", EventId(1), material(1)).unwrap();
    let aperture = DistanceAperture {
        lineage: "squared distance at or below two".to_owned(),
        squared: Rat::from_integer(BigInt::from(2)),
    };
    let mut enacted = exact_classes(
        &complex,
        ConstraintComponentId(1),
        ConstraintComponentId(2),
        &aperture,
    );
    enacted[0] = ContactClass::Outside;
    assert!(matches!(
        complex.found_contact_family(
            ConstraintComponentId(1),
            ConstraintComponentId(2),
            aperture,
            &enacted,
            &uncertainty(3, 2),
        ),
        Err(ConstraintError::CarrierDisagrees { .. })
    ));
    assert!(complex.contact_edges.is_empty());
    assert!(complex.faces.is_empty());
}

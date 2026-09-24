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

// ==============================================================================================
// the within-component (intra-chain) contact family
// ==============================================================================================

/// A five-occurrence chain that folds back on itself: only the pair `(1,5)` is within the
/// aperture, so exactly one intra-chain contact closes the whole chain into a loop.
fn folded_chain() -> Vec<ComponentMaterial> {
    vec![ComponentMaterial {
        lineage: "one folded chain".to_owned(),
        residues: vec![
            residue(1, "A", 0, 0),
            residue(2, "B", 2, 0),
            residue(3, "C", 3, 2),
            residue(4, "D", 1, 3),
            residue(5, "E", -1, 1),
        ],
    }]
}

fn within_aperture() -> DistanceAperture {
    DistanceAperture {
        lineage: "squared distance at or below two".to_owned(),
        squared: Rat::from_integer(BigInt::from(2)),
    }
}

fn exact_within_classes(
    complex: &PhysicalConstraintComplex,
    component: ConstraintComponentId,
    separation: u32,
    aperture: &DistanceAperture,
) -> Vec<ContactClass> {
    let vertices = complex.component(component).unwrap().vertices.clone();
    complex
        .within_component_pairs(component, separation)
        .unwrap()
        .into_iter()
        .map(|(left, right)| {
            let a = vertices[left as usize - 1];
            let b = vertices[right as usize - 1];
            aperture.classify(
                &complex.vertices[&a]
                    .position
                    .squared_distance(&complex.vertices[&b].position),
            )
        })
        .collect()
}

fn within_uncertainty(
    complex: &PhysicalConstraintComplex,
    component: ConstraintComponentId,
    separation: u32,
) -> BTreeMap<(u32, u32), PairUncertainty> {
    let mut result = BTreeMap::new();
    let full = uncertainty(1, 1);
    let one = full.get(&(1, 1)).expect("one reading").clone();
    for pair in complex
        .within_component_pairs(component, separation)
        .unwrap()
    {
        result.insert(pair, one.clone());
    }
    result
}

/// **A second founding on the same component pair founds no second two-cell.**
///
/// Before the fix each founding minted a fresh `ConstraintFaceId` for every qualifying
/// (step-pair, junction) with no check for a face already standing on the same vertex triple, so
/// founding a second family on the same pair — a second aperture, which `contact_family`'s own
/// doc names as normal use — took the fixture below from two 2-cells to four and **doubled** every
/// `two_chain_boundary` coefficient, silently.
#[test]
fn a_second_founding_on_the_same_pair_founds_no_second_two_cell() {
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
            aperture.clone(),
            &enacted,
            &uncertainty(3, 2),
        )
        .unwrap();
    let faces_after_one = complex.faces.len();
    let boundary_after_one = complex.boundary.two_chain_boundary.clone();
    let edges_after_one = complex.contact_edges.clone();
    assert_eq!(faces_after_one, 2);

    // The same pair again, under a *wider* aperture that admits strictly more contacts. The
    // second family is its own reading; the 2-cells it reaches that already stand are not minted
    // again and the boundary is not added again.
    let wider = DistanceAperture {
        lineage: "squared distance at or below three".to_owned(),
        squared: Rat::from_integer(BigInt::from(3)),
    };
    let enacted_wider = exact_classes(
        &complex,
        ConstraintComponentId(1),
        ConstraintComponentId(2),
        &wider,
    );
    complex
        .found_contact_family(
            ConstraintComponentId(1),
            ConstraintComponentId(2),
            wider,
            &enacted_wider,
            &uncertainty(3, 2),
        )
        .unwrap();

    assert_eq!(complex.contact_families.len(), 2, "two founded families");
    assert_eq!(
        complex.faces.len(),
        faces_after_one,
        "the wider aperture admits no contact the first did not, so it reaches no new triple"
    );
    assert_eq!(
        complex.boundary.two_chain_boundary, boundary_after_one,
        "no boundary coefficient is added a second time"
    );
    assert_eq!(complex.contact_edges, edges_after_one);
    // Each founding's own two-cell population is recorded, and the two populations agree here
    // because the two apertures admit the same contacts.
    assert_eq!(complex.family_faces(0).unwrap().len(), 2);
    assert_eq!(complex.family_faces(1).unwrap(), complex.family_faces(0).unwrap());
    assert_eq!(
        complex.two_chain_boundary_of_family(0).unwrap(),
        complex.boundary.two_chain_boundary
    );
    assert_eq!(
        complex.two_chain_boundary_of_family(1).unwrap(),
        complex.two_chain_boundary_of_family(0).unwrap()
    );
    assert!(complex.family_faces(2).is_none());
    assert!(matches!(
        complex.two_chain_boundary_of_family(2),
        Err(ConstraintError::NoSuchFounding(2))
    ));
    assert_boundary_of_boundary_is_zero(&complex);
}

/// **The two-cell law is asked of each family's own contacts, not of the union.**
///
/// Two within-component families on one component at two declared separations. The `k = 2` family
/// admits a contact the `k = 4` family cannot even read, and the `k = 4` founding must not stand a
/// 2-cell on it. Before the fix `found_faces_over` consulted the complex-wide `contact_edges`, so
/// the later founding saw the earlier family's edges and founded cells its own aperture and
/// separation never admitted.
#[test]
fn the_two_cell_law_is_asked_of_each_familys_own_contacts() {
    let mut complex =
        PhysicalConstraintComplex::found("chain", EventId(1), folded_chain()).unwrap();
    let component = ConstraintComponentId(1);
    let aperture = DistanceAperture {
        lineage: "the folded chain's contact aperture".to_owned(),
        squared: Rat::from_integer(BigInt::from(2)),
    };

    let near = exact_within_classes(&complex, component, 2, &aperture);
    complex
        .found_within_component_contact_family(
            component,
            2,
            aperture.clone(),
            &near,
            &within_uncertainty(&complex, component, 2),
        )
        .unwrap();
    let near_faces: Vec<_> = complex.family_faces(0).unwrap().to_vec();
    let faces_after_near = complex.faces.len();

    let far = exact_within_classes(&complex, component, 4, &aperture);
    complex
        .found_within_component_contact_family(
            component,
            4,
            aperture,
            &far,
            &within_uncertainty(&complex, component, 4),
        )
        .unwrap();

    // Every 2-cell the far family stands over is founded on two contacts the far family itself
    // admits — never on one only the near family read.
    let far_admitted: BTreeSet<ConstraintEdge> = complex.contact_families[1]
        .readings
        .iter()
        .filter(|reading| reading.class == ContactClass::Inside)
        .map(|reading| ConstraintEdge::new(reading.left, reading.right).unwrap().0)
        .collect();
    for id in complex.family_faces(1).unwrap() {
        let face = &complex.faces[id];
        let first = ConstraintEdge::new(face.vertices[0], face.vertices[2]).unwrap().0;
        let second = ConstraintEdge::new(face.vertices[1], face.vertices[2]).unwrap().0;
        assert!(
            far_admitted.contains(&first) && far_admitted.contains(&second),
            "a two-cell of the k=4 family stands on a contact only the k=2 family admitted"
        );
    }
    // The near family's population is untouched by the later founding.
    assert_eq!(complex.family_faces(0).unwrap(), near_faces.as_slice());
    assert!(complex.faces.len() >= faces_after_near);
    assert_boundary_of_boundary_is_zero(&complex);
}

/// `∂∘∂ = 0` on the whole carried two-chain, and on each founded family's own two-chain.
fn assert_boundary_of_boundary_is_zero(complex: &PhysicalConstraintComplex) {
    let mut chains = vec![complex.boundary.two_chain_boundary.clone()];
    for founding in 0..complex.contact_families.len() {
        chains.push(complex.two_chain_boundary_of_family(founding).unwrap());
    }
    for chain in chains {
        let mut endpoints = BTreeMap::<ConstraintVertexId, i64>::new();
        for (edge, hand) in &chain {
            *endpoints.entry(edge.lower).or_default() -= *hand;
            *endpoints.entry(edge.upper).or_default() += *hand;
        }
        endpoints.retain(|_, coefficient| *coefficient != 0);
        assert!(endpoints.is_empty(), "∂∘∂ = 0");
    }
}

/// A remounted complex passes a structural re-check: the wire route is `TryFrom`, not a bare
/// `Deserialize`, and a forged boundary, a duplicated two-cell, an absent occurrence or a
/// misaligned per-family population is refused rather than carried.
///
/// The round trip is taken through `ron` because this complex's maps are keyed by exact ids and
/// not by strings; the format is incidental, the gate is not.
#[test]
fn a_remounted_complex_is_structurally_rechecked() {
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
    let wire = ron::to_string(&complex).expect("serializes");
    let remounted: PhysicalConstraintComplex =
        ron::from_str(&wire).expect("a coherent complex remounts");
    assert_eq!(remounted.faces.len(), complex.faces.len());
    assert_eq!(
        remounted.boundary.two_chain_boundary,
        complex.boundary.two_chain_boundary
    );
    assert_eq!(remounted.family_faces, complex.family_faces);

    // The `TryFrom` gate itself, exercised on the wire this module's `Deserialize` routes through.
    // `tests` is a child of the defining module, so the wire is constructible here and nowhere
    // else.
    let bare = |complex: &PhysicalConstraintComplex| PhysicalConstraintComplexWire {
        schema: complex.schema.clone(),
        presentation_lineage: complex.presentation_lineage.clone(),
        source_event: complex.source_event,
        components: complex.components.clone(),
        vertices: complex.vertices.clone(),
        polygonal_edges: complex.polygonal_edges.clone(),
        contact_families: complex.contact_families.clone(),
        contact_edges: complex.contact_edges.clone(),
        faces: complex.faces.clone(),
        family_faces: complex.family_faces.clone(),
        boundary: complex.boundary.clone(),
        next_face: complex.next_face,
    };
    assert!(PhysicalConstraintComplex::try_from(bare(&complex)).is_ok());

    let mut forged = bare(&complex);
    forged.schema = "holonic-engine.not-this.v1".to_owned();
    assert!(matches!(
        PhysicalConstraintComplex::try_from(forged),
        Err(ConstraintError::RemountedSchemaMismatch(_))
    ));

    // A doubled boundary coefficient — exactly what the unfixed second founding produced — is
    // refused, because the boundary is recomputed from the carried two-cells.
    let mut forged = bare(&complex);
    for hand in forged.boundary.two_chain_boundary.values_mut() {
        *hand *= 2;
    }
    assert!(matches!(
        PhysicalConstraintComplex::try_from(forged),
        Err(ConstraintError::RemountedBoundaryDisagrees)
    ));

    // A second two-cell on a vertex triple that already carries one — the other half of the same
    // defect — is refused.
    let mut forged = bare(&complex);
    let standing = complex.faces.values().next().unwrap().clone();
    let duplicate = ConstraintFaceId(forged.next_face);
    forged.next_face += 1;
    forged.faces.insert(
        duplicate,
        ConstraintFace {
            id: duplicate,
            source_event: standing.source_event,
            vertices: standing.vertices,
        },
    );
    assert!(matches!(
        PhysicalConstraintComplex::try_from(forged),
        Err(ConstraintError::RemountedDuplicateFace(_))
    ));

    // A per-family population naming a two-cell the complex does not carry is refused.
    let mut forged = bare(&complex);
    forged.family_faces[0].push(ConstraintFaceId(9_999));
    assert!(matches!(
        PhysicalConstraintComplex::try_from(forged),
        Err(ConstraintError::RemountedFaceMisaddressed(_))
    ));

    // A misaligned per-family population is refused.
    let mut forged = bare(&complex);
    forged.family_faces.clear();
    assert!(matches!(
        PhysicalConstraintComplex::try_from(forged),
        Err(ConstraintError::RemountedFamilyFacesMisaligned { .. })
    ));

    // A two-cell standing on an occurrence the complex does not present is refused.
    let mut forged = bare(&complex);
    let absent = ConstraintVertexId(9_999);
    let id = *forged.faces.keys().next().unwrap();
    forged.faces.get_mut(&id).unwrap().vertices[2] = absent;
    assert!(matches!(
        PhysicalConstraintComplex::try_from(forged),
        Err(ConstraintError::RemountedVertexAbsent(_))
    ));
}

/// The declared domain of `within_component_pair_count` is `k ≥ 2`, which is the domain the
/// founders declare. Below it the answer is `None` rather than a number for a family nobody may
/// found: at `k = 0` the Lean family `withinComponentPairs n 0` carries the whole diagonal, so its
/// cardinality is `C(n + 1, 2)` and not the `C(n, 2)` an unordered-pair reading would name.
#[test]
fn the_within_component_population_is_undefined_below_the_declared_separation() {
    for extent in 0..=8_usize {
        assert_eq!(within_component_pair_count(extent, 0), None);
        assert_eq!(within_component_pair_count(extent, 1), None);
        assert!(within_component_pair_count(extent, 2).is_some());
    }
}

/// `C(n − k + 1, 2)` is not asserted: it is checked against the enumeration it claims to count,
/// over every extent and every declared separation in a bounded square.
#[test]
fn the_within_component_population_is_n_minus_k_plus_one_choose_two() {
    for extent in 0..=24_usize {
        for separation in 2..=8_u32 {
            let brute = (0..extent)
                .flat_map(|left| (0..extent).map(move |right| (left, right)))
                .filter(|(left, right)| *right >= *left + separation as usize)
                .count();
            let closed = within_component_pair_count(extent, separation)
                .expect("a bounded extent does not overflow");
            let span = extent.saturating_sub(separation as usize);
            assert_eq!(
                closed, brute,
                "extent {extent}, separation {separation}: the closed form C(n − k + 1, 2) must \
                 count the pairs it names"
            );
            assert_eq!(
                closed,
                span * (span + 1) / 2,
                "C(n − k + 1, 2) = (n − k)(n − k + 1)/2"
            );
        }
    }
}

#[test]
fn the_enumeration_is_ordered_separated_and_of_the_declared_population() {
    let complex = PhysicalConstraintComplex::found("chain", EventId(1), folded_chain()).unwrap();
    let component = ConstraintComponentId(1);
    for separation in 2..=5_u32 {
        let pairs = complex.within_component_pairs(component, separation).unwrap();
        assert_eq!(
            pairs.len(),
            within_component_pair_count(5, separation).unwrap()
        );
        let mut previous: Option<(u32, u32)> = None;
        for pair in &pairs {
            assert!(pair.0 < pair.1, "an unordered pair is presented as i < j");
            assert!(
                pair.1 - pair.0 >= separation,
                "the declared sequence separation is excluded, not approximated"
            );
            if let Some(previous) = previous {
                assert!(previous < *pair, "ascending i, then ascending j");
            }
            previous = Some(*pair);
        }
    }
    assert_eq!(
        complex.within_component_pairs(component, 2).unwrap(),
        vec![(1, 3), (1, 4), (1, 5), (2, 4), (2, 5), (3, 5)]
    );
}

#[test]
fn a_separation_of_one_names_the_covalent_step_and_is_refused() {
    let mut complex =
        PhysicalConstraintComplex::found("chain", EventId(1), folded_chain()).unwrap();
    let component = ConstraintComponentId(1);
    for separation in [0_u32, 1] {
        assert!(matches!(
            complex.within_component_pairs(component, separation),
            Err(ConstraintError::SeparationIsCovalent(_))
        ));
        assert!(matches!(
            complex.found_within_component_contact_family(
                component,
                separation,
                within_aperture(),
                &[],
                &BTreeMap::new(),
            ),
            Err(ConstraintError::SeparationIsCovalent(_))
        ));
    }
    // And the covalent step it names is a one-cell of the presentation regardless.
    assert_eq!(complex.polygonal_edges.len(), 4);
    assert!(complex.contact_families.is_empty());
}

#[test]
fn the_within_component_family_founds_the_intra_chain_contact_that_closes_the_chain() {
    let mut complex =
        PhysicalConstraintComplex::found("chain", EventId(1), folded_chain()).unwrap();
    let component = ConstraintComponentId(1);
    let aperture = within_aperture();
    let enacted = exact_within_classes(&complex, component, 2, &aperture);
    complex
        .found_within_component_contact_family(
            component,
            2,
            aperture,
            &enacted,
            &within_uncertainty(&complex, component, 2),
        )
        .unwrap();

    let family = complex.within_component_family(component, 2).unwrap();
    assert_eq!(family.left, component);
    assert_eq!(family.right, component);
    assert_eq!(
        family.kind,
        ContactFamilyKind::WithinComponent {
            minimum_separation: 2
        }
    );
    assert_eq!(family.minimum_separation(), Some(2));
    assert_eq!(family.readings.len(), 6);
    let inside = family
        .readings
        .iter()
        .filter(|reading| reading.class == ContactClass::Inside)
        .map(|reading| (reading.left_ordinal, reading.right_ordinal))
        .collect::<Vec<_>>();
    assert_eq!(inside, vec![(1, 5)], "only the fold closes");
    // The 1-cell exists, and it is not a chain step: the chain steps are the covalent class.
    let (closing, _) = ConstraintEdge::new(ConstraintVertexId(1), ConstraintVertexId(5)).unwrap();
    assert!(complex.contact_edges.contains(&closing));
    assert!(!complex.polygonal_edges.contains(&closing));
    // One contact founds no triangle: a 2-cell needs two contacts to the same junction.
    assert!(complex.faces.is_empty());
}

#[test]
fn a_within_component_carrier_disagreement_refuses_before_it_founds_incidence() {
    let mut complex =
        PhysicalConstraintComplex::found("chain", EventId(1), folded_chain()).unwrap();
    let component = ConstraintComponentId(1);
    let aperture = within_aperture();
    let mut enacted = exact_within_classes(&complex, component, 2, &aperture);
    let at = enacted
        .iter()
        .position(|class| *class == ContactClass::Inside)
        .expect("the fold is inside");
    enacted[at] = ContactClass::Outside;
    assert!(matches!(
        complex.found_within_component_contact_family(
            component,
            2,
            aperture.clone(),
            &enacted,
            &within_uncertainty(&complex, component, 2),
        ),
        Err(ConstraintError::CarrierDisagrees {
            left_ordinal: 1,
            right_ordinal: 5,
            ..
        })
    ));
    assert!(complex.contact_edges.is_empty());
    assert!(complex.contact_families.is_empty());

    // A short population is refused before any allocation is sized by it.
    let enacted = exact_within_classes(&complex, component, 2, &aperture);
    assert!(matches!(
        complex.found_within_component_contact_family(
            component,
            2,
            aperture.clone(),
            &enacted[..3],
            &within_uncertainty(&complex, component, 2),
        ),
        Err(ConstraintError::ContactPopulationDisagrees {
            expected: 6,
            enacted: 3
        })
    ));
    let mut thin = within_uncertainty(&complex, component, 2);
    thin.remove(&(1, 5));
    assert!(matches!(
        complex.found_within_component_contact_family(
            component,
            2,
            aperture,
            &enacted,
            &thin,
        ),
        Err(ConstraintError::UncertaintyPopulationDisagrees {
            expected: 6,
            supplied: 5
        })
    ));
    assert!(complex.contact_families.is_empty());
}

/// The cross law is untouched: the same material, the same aperture, the same six readings, four
/// contact edges and two two-cells the cross test measures, with a within-component family founded
/// beside it.
#[test]
fn founding_a_within_component_family_leaves_the_cross_family_exactly_as_it_was() {
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
            aperture.clone(),
            &enacted,
            &uncertainty(3, 2),
        )
        .unwrap();
    let cross_before = complex.contact_families[0].clone();
    let edges_before = complex.contact_edges.clone();
    let faces_before = complex.faces.len();
    let boundary_before = complex.boundary.two_chain_boundary.clone();
    assert_eq!(cross_before.kind, ContactFamilyKind::Cross);
    assert_eq!(cross_before.readings.len(), 6);
    assert_eq!(edges_before.len(), 4);
    assert_eq!(faces_before, 2);

    let within = exact_within_classes(&complex, ConstraintComponentId(1), 2, &aperture);
    complex
        .found_within_component_contact_family(
            ConstraintComponentId(1),
            2,
            aperture,
            &within,
            &within_uncertainty(&complex, ConstraintComponentId(1), 2),
        )
        .unwrap();

    assert_eq!(complex.contact_families[0], cross_before);
    assert_eq!(complex.contact_families.len(), 2);
    assert_eq!(
        complex
            .contact_family(ConstraintComponentId(1), ConstraintComponentId(2))
            .unwrap(),
        &cross_before
    );
    // The component has three occurrences and separation two, so C(3 − 2 + 1, 2) = 1 pair.
    assert_eq!(complex.contact_families[1].readings.len(), 1);
    assert_eq!(complex.contact_edges, edges_before);
    assert_eq!(complex.faces.len(), faces_before);
    assert_eq!(complex.boundary.two_chain_boundary, boundary_before);
}

// ==============================================================================================
// the measured within-component reading on the authenticated M5 release
// ==============================================================================================

const STRUCTURE_ROOT_ENV: &str = "HOLONICS_M5_STRUCTURE_ROOT";
const DEFAULT_STRUCTURE_ROOT: &str = "/home/b/Downloads/holonics-m5-rbx1-rank05";
/// The RBX1 chain is the one component present in all three presentations.
const RBX1_RESIDUES: usize = 108;
/// The residue window `rigidity_receiver` and `hodge_receiver` were measured on in wave 3, so the
/// readings below are comparable to the recorded ones rather than a different object.
const M5_WINDOW: usize = 24;
/// Eight angstroms, squared, on the exact decimal wire the intake reads.
const M5_CONTACT_SQUARED: i64 = 64;

const M5_STRUCTURES: [(&str, &str); 3] = [
    ("designed-free", "designed-free-rbx1.cif"),
    ("protenix-free-seed2", "ptxv2-free-rbx1-seed2.cif"),
    ("protenix-cul1-seed0", "ptxv2-cul1-rbx1-seed0.cif"),
];

/// The measured within-component inside population of the whole RBX1 chain of each authenticated
/// release, per declared separation. Recorded rather than printed: a change here is a change in
/// the reading of the release, and the test says so instead of leaving it to a reader of stdout.
const M5_WHOLE_CHAIN_INSIDE: [(&str, u32, usize); 6] = [
    ("designed-free", 3, 224),
    ("designed-free", 4, 159),
    ("protenix-free-seed2", 3, 214),
    ("protenix-free-seed2", 4, 160),
    ("protenix-cul1-seed0", 3, 175),
    ("protenix-cul1-seed0", 4, 138),
];

fn m5_aperture() -> DistanceAperture {
    DistanceAperture {
        lineage: "eight angstroms, squared, on the deposited decimal wire".to_owned(),
        squared: Rat::from_integer(BigInt::from(M5_CONTACT_SQUARED)),
    }
}

/// One declared uncertainty reading per addressed pair, whose lineage says what it is: this path
/// reads geometry only and no predictor array is mounted on it. It is a declaration, not a
/// fabricated confidence, and it never enters a class.
fn declared_geometry_only(pairs: &[(u32, u32)]) -> BTreeMap<(u32, u32), PairUncertainty> {
    let mut result = BTreeMap::new();
    for pair in pairs {
        result.insert(
            *pair,
            PairUncertainty {
                source_lineage:
                    "declared by this reading: geometry only, no predictor array mounted".to_owned(),
                row_given_column_bits: 0x3c00,
                column_given_row_bits: 0x3c00,
                row_given_column: ExactInterval::point(Rat::from_integer(BigInt::from(1))),
                column_given_row: ExactInterval::point(Rat::from_integer(BigInt::from(1))),
                row_given_column_ulp: rat(1, 1024),
                column_given_row_ulp: rat(1, 1024),
            },
        );
    }
    result
}

/// The RBX1 chain of one release file, as one presented component of `window` alpha carbons.
fn m5_window(lineage: &str, path: &std::path::Path, window: usize) -> PhysicalConstraintComplex {
    use crate::physical_intake::mmcif::StructurePresentation;
    let presentation = StructurePresentation::read(path)
        .unwrap_or_else(|error| panic!("{lineage}: {}: {error}", path.display()));
    let chain = presentation
        .chain_with_residue_count(RBX1_RESIDUES)
        .unwrap_or_else(|error| panic!("{lineage}: one RBX1 chain: {error}"));
    let mut residues = Vec::with_capacity(window);
    for residue in chain.residues.iter().take(window) {
        let at = residue
            .labelled_atom("CA")
            .unwrap_or_else(|error| panic!("{lineage}: {error}"))
            .unwrap_or_else(|| panic!("{lineage}: residue {} carries no CA", residue.source_ordinal));
        let atom = &residue.atoms[at];
        let place = |token: &crate::physical_intake::mmcif::DecimalToken| {
            token
                .exact_centre()
                .unwrap_or_else(|error| panic!("{lineage}: {error}"))
        };
        residues.push(ResidueMaterial {
            source_ordinal: residue.source_ordinal,
            monomer: residue.monomer.clone(),
            position: CoordinateBox3::point(place(&atom.x), place(&atom.y), place(&atom.z)),
        });
    }
    assert_eq!(
        residues.len(),
        window,
        "{lineage}: the RBX1 chain supplied fewer than {window} alpha carbons"
    );
    PhysicalConstraintComplex::found(
        format!("m5/{lineage}/rbx1[..{window}]"),
        EventId(1),
        vec![ComponentMaterial {
            lineage: "RBX1".to_owned(),
            residues,
        }],
    )
    .unwrap_or_else(|error| panic!("{lineage}: {error}"))
}

fn found_m5_within(complex: &mut PhysicalConstraintComplex, separation: u32) {
    let component = ConstraintComponentId(1);
    let aperture = m5_aperture();
    let enacted = crate::physical_intake::enacted_within_component_classes(
        complex, component, separation, &aperture,
    )
    .expect("the within-component classification stands");
    let pairs = complex
        .within_component_pairs(component, separation)
        .expect("the population stands");
    let uncertainty = declared_geometry_only(&pairs);
    complex
        .found_within_component_contact_family(
            component,
            separation,
            aperture,
            &enacted,
            &uncertainty,
        )
        .expect("the within-component family stands");
}

fn census(complex: &PhysicalConstraintComplex, separation: u32) -> (usize, usize, usize) {
    let family = complex
        .within_component_family(ConstraintComponentId(1), separation)
        .expect("the family stands");
    let inside = family
        .readings
        .iter()
        .filter(|reading| reading.class == ContactClass::Inside)
        .count();
    let open = family
        .readings
        .iter()
        .filter(|reading| reading.class == ContactClass::Open)
        .count();
    (family.readings.len(), inside, open)
}

/// **The measured within-component reading on the authenticated M5 release.**
///
/// Absent the release this test refuses rather than reporting success. Every law the
/// within-component family owns is checked above on synthetic exact material that needs no
/// fixture, so nothing here is the only check of anything.
#[test]
fn the_within_component_family_measures_the_m5_structures() {
    use crate::hodge_receiver::{BoundaryLaw, MetricDeclaration, hodge_member};
    use crate::physical_constraint_grading::{
        OpenContactLaw, graded_constraint_family, graded_constraint_member,
    };
    use holonics::rebase_invariants::PivotRule;
    use crate::rebase_invariants::{rebase_invariants};
    use crate::rigidity_receiver::{ExactConfiguration, rigidity_family};

    let root = std::env::var_os(STRUCTURE_ROOT_ENV)
        .map(std::path::PathBuf::from)
        .unwrap_or_else(|| std::path::PathBuf::from(DEFAULT_STRUCTURE_ROOT));
    assert!(
        root.is_dir(),
        "the authenticated M5 structure root {} is absent, so the measured intra-chain contact \
         reading cannot be taken, and this test refuses to report success without taking it. \
         Place the authenticated release at that path, or set {STRUCTURE_ROOT_ENV} to the \
         directory carrying designed-free-rbx1.cif, ptxv2-free-rbx1-seed2.cif and \
         ptxv2-cul1-rbx1-seed0.cif.",
        root.display()
    );

    for (lineage, file) in M5_STRUCTURES {
        let path = root.join(file);

        // (a) The contact census over the whole RBX1 chain, per declared separation. The inside
        //     population is **pinned**, not printed: these are the measured readings of the
        //     authenticated release, and a change in them is a change in the reading.
        for separation in [3_u32, 4] {
            let mut whole = m5_window(lineage, &path, RBX1_RESIDUES);
            found_m5_within(&mut whole, separation);
            let (pairs, inside, open) = census(&whole, separation);
            assert_eq!(
                pairs,
                within_component_pair_count(RBX1_RESIDUES, separation).unwrap(),
                "{lineage}: C(n − k + 1, 2)"
            );
            let recorded = M5_WHOLE_CHAIN_INSIDE
                .iter()
                .find(|(name, k, _)| *name == lineage && *k == separation)
                .map(|(_, _, inside)| *inside)
                .unwrap_or_else(|| panic!("{lineage}: no recorded census at k={separation}"));
            assert_eq!(
                inside, recorded,
                "{lineage}: the recorded within-component inside population at k={separation}"
            );
            assert_eq!(
                open, 0,
                "{lineage}: the centre presentation is a point, so no pair is left open"
            );
            println!(
                "within-component M5 | {lineage} | chain {RBX1_RESIDUES} | k={separation} | \
                 pairs {pairs} | inside {inside} | open {open}"
            );
        }

        // (b) The window every wave-3 receiver number was read on, so the readings compare.
        let configuration = {
            let bare = m5_window(lineage, &path, M5_WINDOW);
            ExactConfiguration::from_presented(&bare).expect("deposited centres are points")
        };
        let bare = m5_window(lineage, &path, M5_WINDOW);
        let backbone_only = rigidity_family(&bare, &configuration).expect("the chain alone");
        assert_eq!(
            backbone_only.refusing.constraint_count,
            M5_WINDOW - 1,
            "{lineage}: with no contact family the presentation carries only its chain steps"
        );

        for separation in [2_u32, 3, 4] {
            let mut windowed = m5_window(lineage, &path, M5_WINDOW);
            found_m5_within(&mut windowed, separation);
            let (pairs, inside, open) = census(&windowed, separation);
            let family = graded_constraint_family(&windowed).expect("the graded family stands");
            let member =
                graded_constraint_member(&windowed, &OpenContactLaw::RefuseEveryOpen).unwrap();
            let invariants = rebase_invariants(&member.complex, PivotRule::FirstNonzero).unwrap();
            let betti = invariants.betti_vector();
            let rigidity = rigidity_family(&windowed, &configuration).expect("the family stands");
            let hodge = hodge_member(
                &windowed,
                &OpenContactLaw::RefuseEveryOpen,
                &MetricDeclaration::unit("unit"),
                &BoundaryLaw::Free,
                1,
            )
            .expect("the grade-one reading stands");
            println!(
                "within-component M5 | {lineage} | window {M5_WINDOW} | k={separation} | pairs \
                 {pairs} | inside {inside} | open {open} | family 2^{} | cells v{} e{} f{} | \
                 betti {:?} | rank J {} | dim ker J {} | dim ker J^T {} | H1 exact {} coexact {} \
                 harmonic {}",
                family.open_contacts.len(),
                member.vertex_cells.len(),
                member.edge_cells.len(),
                member.face_cells.len(),
                betti,
                rigidity.refusing.rank,
                rigidity.refusing.motion_dimension,
                rigidity.refusing.self_stress_dimension,
                hodge.exact_dimension,
                hodge.coexact_dimension,
                hodge.harmonic_dimension,
            );
            assert_eq!(
                member.vertex_cells.len(),
                M5_WINDOW,
                "{lineage}: the window's occurrences"
            );
            assert_eq!(
                member.edge_cells.len(),
                (M5_WINDOW - 1) + inside,
                "{lineage}: the covalent chain steps stand beside every admitted contact"
            );
            assert_eq!(
                betti.first().copied().unwrap_or(0),
                1,
                "{lineage}: one chain, one component"
            );
            assert_eq!(
                hodge.harmonic_dimension,
                betti.get(1).copied().unwrap_or(0),
                "{lineage}: dim ker Δ₁ is the grade-one Betti number"
            );
        }
    }
}

/// The same RBX1 window, presented as the **deposited enclosures** rather than their declared
/// centres: each coordinate box is one last decimal place wide on each side, which is where the
/// `Open` class comes from at all.
fn m5_enclosure_window(
    lineage: &str,
    path: &std::path::Path,
    window: usize,
) -> PhysicalConstraintComplex {
    use crate::physical_intake::mmcif::StructurePresentation;
    let presentation = StructurePresentation::read(path)
        .unwrap_or_else(|error| panic!("{lineage}: {}: {error}", path.display()));
    let chain = presentation
        .chain_with_residue_count(RBX1_RESIDUES)
        .unwrap_or_else(|error| panic!("{lineage}: one RBX1 chain: {error}"));
    let mut residues = Vec::with_capacity(window);
    for residue in chain.residues.iter().take(window) {
        let at = residue
            .labelled_atom("CA")
            .unwrap_or_else(|error| panic!("{lineage}: {error}"))
            .unwrap_or_else(|| {
                panic!("{lineage}: residue {} carries no CA", residue.source_ordinal)
            });
        residues.push(ResidueMaterial {
            source_ordinal: residue.source_ordinal,
            monomer: residue.monomer.clone(),
            position: residue.atoms[at]
                .source_box()
                .unwrap_or_else(|error| panic!("{lineage}: {error}")),
        });
    }
    PhysicalConstraintComplex::found(
        format!("m5/{lineage}/rbx1[..{window}]/enclosure"),
        EventId(1),
        vec![ComponentMaterial {
            lineage: "RBX1".to_owned(),
            residues,
        }],
    )
    .unwrap_or_else(|error| panic!("{lineage}: {error}"))
}

/// **The open class of the intra-chain family, and the loops it closes.**
///
/// Two readings the centre presentation cannot take: the deposited enclosure leaves contacts
/// `Open`, so the intra-chain family is plural and its two bounds are read; and
/// `topological_receiver::presented_contact_loops` takes the loop reading from this owner's family
/// with the filtration held to agreement.
#[test]
fn the_within_component_family_carries_the_open_class_and_closes_the_m5_loops() {
    use crate::physical_constraint_grading::graded_constraint_family;
    use holonics::rebase_invariants::PivotRule;
    use crate::rebase_invariants::{rebase_invariants};
    use crate::rigidity_receiver::ExactConfiguration;
    use crate::topological_receiver::{
        ApertureFiltration, TopologicalError, contact_loops, presented_contact_loops,
    };

    let root = std::env::var_os(STRUCTURE_ROOT_ENV)
        .map(std::path::PathBuf::from)
        .unwrap_or_else(|| std::path::PathBuf::from(DEFAULT_STRUCTURE_ROOT));
    assert!(
        root.is_dir(),
        "the authenticated M5 structure root {} is absent, so the open-class and loop readings of \
         the intra-chain family cannot be taken, and this test refuses to report success without \
         taking them. Place the authenticated release at that path, or set {STRUCTURE_ROOT_ENV} \
         to the directory carrying designed-free-rbx1.cif, ptxv2-free-rbx1-seed2.cif and \
         ptxv2-cul1-rbx1-seed0.cif.",
        root.display()
    );
    /// The window `topological_receiver` measured its loop reading on in wave 3.
    const LOOP_WINDOW: usize = 20;
    /// The span wave 3's loop reading declared, and the separation this family declares with it.
    const LOOP_SPAN: u32 = 4;

    for (lineage, file) in M5_STRUCTURES {
        let path = root.join(file);

        // (a) The enclosure presentation: the intra-chain family is plural, and both bounds read.
        for separation in [3_u32, 4] {
            let mut enclosed = m5_enclosure_window(lineage, &path, M5_WINDOW);
            found_m5_within(&mut enclosed, separation);
            let (pairs, inside, open) = census(&enclosed, separation);
            let family = graded_constraint_family(&enclosed).expect("the family stands");
            assert!(
                ExactConfiguration::from_presented(&enclosed).is_err(),
                "{lineage}: a deposited enclosure is a box with width, so this reading is not the                  centre reading under another name"
            );
            let refusing =
                rebase_invariants(&family.refusing.complex, PivotRule::FirstNonzero).unwrap();
            let admitting =
                rebase_invariants(&family.admitting.complex, PivotRule::FirstNonzero).unwrap();
            println!(
                "within-component M5 enclosure | {lineage} | window {M5_WINDOW} | \
                 k={separation} | pairs {pairs} | inside {inside} | open {open} | family 2^{} | \
                 e {}→{} | betti refusing {:?} admitting {:?}",
                family.open_contacts.len(),
                family.refusing.edge_cells.len(),
                family.admitting.edge_cells.len(),
                refusing.betti_vector(),
                admitting.betti_vector(),
            );
            assert_eq!(
                family.open_contacts.len(),
                open,
                "{lineage}: every open intra-chain reading is carried into the family, and \
                 nothing else is"
            );
            assert_eq!(
                family.admitting.edge_cells.len() - family.refusing.edge_cells.len(),
                open,
                "{lineage}: the two bounds differ by exactly the open class"
            );
        }

        // (b) The loop reading taken from this owner's family, with the filtration held to
        //     agreement. Wave 3 read the same loops from the filtration alone because the owner
        //     could not present the contact at all.
        let mut windowed = m5_window(lineage, &path, LOOP_WINDOW);
        found_m5_within(&mut windowed, LOOP_SPAN);
        let configuration =
            ExactConfiguration::from_presented(&windowed).expect("deposited centres are points");
        let centres = windowed
            .vertices
            .iter()
            .map(|(id, vertex)| (*id, vertex.position.clone()))
            .collect::<BTreeMap<_, _>>();
        let components = windowed
            .vertices
            .iter()
            .map(|(id, vertex)| (*id, vertex.component))
            .collect::<BTreeMap<_, _>>();
        let ceiling = Rat::from_integer(BigInt::from(M5_CONTACT_SQUARED));
        let filtration = ApertureFiltration::found(
            format!("m5/{lineage}/rbx1[..{LOOP_WINDOW}]"),
            EventId(1),
            &centres,
            &components,
            ceiling.clone(),
            2,
            8192,
        )
        .expect("the centre filtration stands");

        let presented = presented_contact_loops(
            &windowed,
            ConstraintComponentId(1),
            LOOP_SPAN,
            &filtration,
            &configuration,
            &ceiling,
            LOOP_SPAN as usize,
        );
        let from_filtration = contact_loops(
            &filtration,
            &configuration,
            &ceiling,
            LOOP_SPAN as usize,
        );
        match (&presented, &from_filtration) {
            (Ok(owned), Ok(filtered)) => {
                assert_eq!(
                    owned.len(),
                    filtered.len(),
                    "{lineage}: the owner's family and the filtration read the same loops"
                );
                let longest = owned
                    .iter()
                    .map(|one| one.occurrences.len())
                    .max()
                    .unwrap_or(0);
                println!(
                    "within-component M5 loops | {lineage} | window {LOOP_WINDOW} | \
                     k={LOOP_SPAN} | loops {} (longest {longest}) | closing pairs {:?}",
                    owned.len(),
                    owned
                        .iter()
                        .map(|one| (one.first_ordinal, one.last_ordinal))
                        .collect::<Vec<_>>()
                );
            }
            (
                Err(TopologicalError::NoCycle { .. }),
                Err(TopologicalError::NoCycle { .. }),
            ) => {
                println!(
                    "within-component M5 loops | {lineage} | window {LOOP_WINDOW} | \
                     k={LOOP_SPAN} | the typed NoCycle refusal, from the owner's family and from \
                     the filtration alike"
                );
            }
            (left, right) => panic!("{lineage}: {left:?} against {right:?}"),
        }

        // The cross-check is not decorative: a span below the declared separation is refused
        // rather than compared, because the two sources would be answering different questions.
        assert!(matches!(
            presented_contact_loops(
                &windowed,
                ConstraintComponentId(1),
                LOOP_SPAN,
                &filtration,
                &configuration,
                &ceiling,
                2,
            ),
            Err(TopologicalError::SpanBelowDeclaredSeparation { .. })
        ));
    }
}

/// The owner-backed loop reading, and the three disagreements it refuses on — checked on
/// synthetic exact material that needs no release.
#[test]
fn the_presented_loop_reading_is_held_to_the_filtration_and_refuses_on_disagreement() {
    use crate::rigidity_receiver::ExactConfiguration;
    use crate::topological_receiver::{
        ApertureFiltration, TopologicalError, presented_contact_loops,
    };

    let mut complex =
        PhysicalConstraintComplex::found("chain", EventId(1), folded_chain()).unwrap();
    let component = ConstraintComponentId(1);
    let aperture = within_aperture();
    let enacted = exact_within_classes(&complex, component, 2, &aperture);
    complex
        .found_within_component_contact_family(
            component,
            2,
            aperture.clone(),
            &enacted,
            &within_uncertainty(&complex, component, 2),
        )
        .unwrap();
    let configuration = ExactConfiguration::from_presented(&complex).unwrap();
    let positions = complex
        .vertices
        .iter()
        .map(|(id, vertex)| (*id, vertex.position.clone()))
        .collect::<BTreeMap<_, _>>();
    let components = complex
        .vertices
        .iter()
        .map(|(id, vertex)| (*id, vertex.component))
        .collect::<BTreeMap<_, _>>();

    let filtration = ApertureFiltration::found(
        "chain",
        EventId(1),
        &positions,
        &components,
        aperture.squared.clone(),
        2,
        4096,
    )
    .unwrap();
    let loops = presented_contact_loops(
        &complex,
        component,
        2,
        &filtration,
        &configuration,
        &aperture.squared,
        2,
    )
    .expect("the fold closes one loop");
    assert_eq!(loops.len(), 1);
    assert_eq!((loops[0].first_ordinal, loops[0].last_ordinal), (1, 5));
    assert_eq!(
        loops[0].occurrences.len(),
        5,
        "the loop carries j − i + 1 = 5 occurrences"
    );

    // A span below the declared separation is a difference of question, not a disagreement.
    assert!(matches!(
        presented_contact_loops(
            &complex,
            component,
            2,
            &filtration,
            &configuration,
            &aperture.squared,
            1,
        ),
        Err(TopologicalError::SpanBelowDeclaredSeparation { .. })
    ));
    // A reading taken at another aperture than the family was classified against.
    assert!(matches!(
        presented_contact_loops(
            &complex,
            component,
            2,
            &filtration,
            &configuration,
            &Rat::from_integer(BigInt::from(3)),
            2,
        ),
        Err(TopologicalError::PresentedApertureDisagrees { .. })
    ));
    // A filtration whose ceiling never founds the closing contact: the presentation carries the
    // loop and the filtration does not, and neither source is preferred.
    let narrow = ApertureFiltration::found(
        "chain/narrow",
        EventId(1),
        &positions,
        &components,
        Rat::from_integer(BigInt::from(1)),
        2,
        4096,
    )
    .unwrap();
    assert!(matches!(
        presented_contact_loops(
            &complex,
            component,
            2,
            &narrow,
            &configuration,
            &aperture.squared,
            2,
        ),
        Err(TopologicalError::PresentedLoopsDisagree {
            pair: (1, 5),
            presented: true,
            ..
        })
    ));
}

/// **A remounted family passes the kind coherence its founders enforce.** A within-component word
/// below two, a within-component word over two components, and a cross word over one component are
/// each refused at the wire; the lawful forms round-trip.
#[test]
fn a_contact_family_wire_whose_kind_disagrees_with_its_components_is_refused() {
    let family = |left: u64, right: u64, kind: ContactFamilyKind| ContactFamily {
        left: ConstraintComponentId(left),
        right: ConstraintComponentId(right),
        kind,
        aperture: DistanceAperture {
            lineage: "wire/aperture".to_owned(),
            squared: Rat::from_integer(BigInt::from(64)),
        },
        readings: Vec::new(),
    };
    let within = |k: u32| ContactFamilyKind::WithinComponent {
        minimum_separation: k,
    };
    let remount = |value: &ContactFamily| {
        serde_json::from_str::<ContactFamily>(&serde_json::to_string(value).unwrap())
    };
    for lawful in [family(1, 2, ContactFamilyKind::Cross), family(1, 1, within(2))] {
        assert_eq!(remount(&lawful).unwrap(), lawful);
    }
    for hostile in [
        family(1, 1, within(0)),
        family(1, 1, within(1)),
        family(1, 2, within(3)),
        family(1, 1, ContactFamilyKind::Cross),
    ] {
        assert!(remount(&hostile).is_err());
    }
}

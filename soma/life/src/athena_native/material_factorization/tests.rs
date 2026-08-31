use super::*;
use crate::mathematical_source::{
    EquationGlyphFibre, ExactOpticalIncidenceReceipt, ExactOpticalScale,
    NativeEquationConstraintSection, OpticalAlternativeCover, OpticalBounds, OpticalHolon,
    OpticalHolonGrain, OpticalHolonIncidence, OpticalHolonIncidenceKind, OpticalHolonIntervention,
    OpticalObjectClassFace, RepeatedOpticalFormFibre, OPTICAL_HOLON_SCHEMA,
};

fn testimony(name: &str) -> ExteriorWorldReturnTestimony {
    ExteriorWorldReturnTestimony::found(
        format!("world/{name}"),
        "bounded-test-world",
        true,
        b"returned",
        vec!["outside the bounded population remains open".to_owned()],
    )
    .unwrap()
}

fn cells(prefix: &str, product: bool) -> Vec<CausalResultCell> {
    if product {
        (0..2)
            .flat_map(|left| {
                (0..2).map(move |right| CausalResultCell {
                    occurrence: format!("{prefix}/result/{left}/{right}"),
                    left_member: Some(format!("{prefix}/left/{left}")),
                    right_member: Some(format!("{prefix}/right/{right}")),
                })
            })
            .collect()
    } else {
        (0..2)
            .map(|at| CausalResultCell {
                occurrence: format!("{prefix}/result/left/{at}"),
                left_member: Some(format!("{prefix}/left/{at}")),
                right_member: None,
            })
            .chain((0..2).map(|at| CausalResultCell {
                occurrence: format!("{prefix}/result/right/{at}"),
                left_member: None,
                right_member: Some(format!("{prefix}/right/{at}")),
            }))
            .collect()
    }
}

fn returned(prefix: &str, product: bool) -> CausalOperationWorldReturn {
    CausalOperationWorldReturn::found(
        format!("{prefix}/return"),
        format!("{prefix}/material"),
        (0..2).map(|at| format!("{prefix}/left/{at}")).collect(),
        (0..2).map(|at| format!("{prefix}/right/{at}")).collect(),
        cells(prefix, product),
        testimony(prefix),
        vec!["successor histories outside the one-member intervention remain open".to_owned()],
    )
    .unwrap()
}

fn optical_digest(value: &impl Serialize) -> String {
    hex_sha256(&serde_json::to_vec(value).unwrap())
}

fn optical_holon(
    occurrence: &str,
    grain: OpticalHolonGrain,
    bounds: OpticalBounds,
    constituents: Vec<String>,
    glyph_ordinals: Vec<u32>,
    inherited_face: Option<String>,
) -> OpticalHolon {
    let form_members = Vec::new();
    let form_sha256 = optical_digest(&(
        "optical-form-v1",
        grain,
        &form_members,
        inherited_face.as_deref(),
    ));
    let address_sha256 = optical_digest(&(
        "optical-holon-occurrence-v1",
        occurrence,
        grain,
        bounds,
        &constituents,
        &form_sha256,
    ));
    OpticalHolon {
        address_sha256,
        form_sha256,
        grain,
        bounds,
        constituents,
        glyph_ordinals,
        component_ordinals: Vec::new(),
        inherited_face,
        form_members,
    }
}

struct OpticalFixture {
    passage: HierarchicalOpticalPassage,
    before: String,
    after: String,
    payload: Vec<u8>,
}

fn hierarchical_optical_fixture() -> OpticalFixture {
    let occurrence = "test/hierarchical-optical";
    let payload = b"bounded optical carrier".to_vec();
    let before = optical_holon(
        occurrence,
        OpticalHolonGrain::GlyphOrSubfigure,
        OpticalBounds {
            left: 0,
            top: 0,
            right: 1,
            bottom: 1,
        },
        Vec::new(),
        vec![0],
        Some("left-face".to_owned()),
    );
    let relation = optical_holon(
        occurrence,
        OpticalHolonGrain::GlyphOrSubfigure,
        OpticalBounds {
            left: 2,
            top: 0,
            right: 3,
            bottom: 1,
        },
        Vec::new(),
        vec![1],
        Some("relation-face".to_owned()),
    );
    let after = optical_holon(
        occurrence,
        OpticalHolonGrain::GlyphOrSubfigure,
        OpticalBounds {
            left: 4,
            top: 0,
            right: 5,
            bottom: 1,
        },
        Vec::new(),
        vec![2],
        Some("right-face".to_owned()),
    );
    let before_address = before.address_sha256.clone();
    let relation_address = relation.address_sha256.clone();
    let after_address = after.address_sha256.clone();
    let equation = optical_holon(
        occurrence,
        OpticalHolonGrain::RelationOrEquation,
        OpticalBounds {
            left: 0,
            top: 0,
            right: 5,
            bottom: 1,
        },
        vec![
            before_address.clone(),
            relation_address.clone(),
            after_address.clone(),
        ],
        vec![0, 1, 2],
        Some("equation-face".to_owned()),
    );
    let equation_address = equation.address_sha256.clone();
    let complete_glyph_holon_addresses = vec![
        before_address.clone(),
        relation_address.clone(),
        after_address.clone(),
    ];
    let constraint_form_sha256 = optical_digest(&(
        "bounded-constraint-form",
        &equation_address,
        &complete_glyph_holon_addresses,
    ));
    let incidences = complete_glyph_holon_addresses
        .iter()
        .map(|child| OpticalHolonIncidence {
            from_address: child.clone(),
            to_address: equation_address.clone(),
            kind: OpticalHolonIncidenceKind::Contains,
            device_contact_class: None,
        })
        .collect();
    let passage = HierarchicalOpticalPassage {
        schema: OPTICAL_HOLON_SCHEMA.to_owned(),
        truth_status: "implemented-exact".to_owned(),
        predecessor_occurrence: "test/raw-optical".to_owned(),
        predecessor_source_sha256: hex_sha256(&payload),
        occurrence: occurrence.to_owned(),
        width: 6,
        height: 2,
        intervention: OpticalHolonIntervention::None,
        scale: ExactOpticalScale {
            lower_median_height: 1,
            upper_median_height: 1,
            lower_median_width: 1,
            upper_median_width: 1,
            lower_median_nearest_gap: 1,
            upper_median_nearest_gap: 1,
            term_gap: 1,
            line_gap: 1,
            authored_capacity_constant: false,
        },
        holons: vec![before, relation, after, equation],
        incidences,
        local_relations: Vec::new(),
        alternative_covers: vec![OpticalAlternativeCover {
            subject_address: relation_address.clone(),
            alternative_parent_addresses: vec![before_address.clone(), after_address.clone()],
            separating_relation_kinds: vec![OpticalHolonIncidenceKind::ReadingTransport],
            complete_within_resident_relation_word: true,
            richer_receiver_reopens: true,
        }],
        classifications: Vec::<OpticalObjectClassFace>::new(),
        repeated_forms: Vec::<RepeatedOpticalFormFibre>::new(),
        native_consequence: NativeHierarchicalOpticalConsequence {
            term_addresses: Vec::new(),
            assembly_addresses: Vec::new(),
            equation_addresses: vec![equation_address.clone()],
            block_addresses: Vec::new(),
            equation_glyph_fibres: vec![EquationGlyphFibre {
                equation_address: equation_address.clone(),
                glyph_holon_addresses: complete_glyph_holon_addresses.clone(),
                glyph_ordinals: vec![0, 1, 2],
                complete_constituent_reconstruction: true,
            }],
            equation_constraint_sections: vec![NativeEquationConstraintSection {
                equation_address,
                relation_glyph_address: relation_address,
                relation_glyph_ordinals: vec![1],
                inherited_relation_face: "relation-face".to_owned(),
                before_member_addresses: vec![before_address.clone()],
                after_member_addresses: vec![after_address.clone()],
                crossing_member_addresses: Vec::new(),
                complete_glyph_holon_addresses,
                constraint_form_sha256,
                exact_ordered_constraint_geometry: true,
            }],
            higher_equation_objects_change_native_consequence: true,
            glyph_fibres_retained: true,
            open_exterior: vec![
                "symbol identity remains open to a later receiver consequence".to_owned(),
            ],
        },
        relation_receipt: ExactOpticalIncidenceReceipt {
            atom_population: 3,
            complete_pair_population: 3,
            complete_relation_words_sha256: optical_digest(&"bounded-relation-word"),
        },
        productive_transcript_present: false,
        productive_text_layer_present: false,
        productive_anchor_labels_present: false,
    };
    passage.validate().unwrap();
    OpticalFixture {
        passage,
        before: before_address,
        after: after_address,
        payload,
    }
}

fn optical_world_return(
    material: &AddressedMaterialOccurrence,
    fixture: &OpticalFixture,
    name: &str,
    product: bool,
) -> CausalOperationWorldReturn {
    let result_cells = if product {
        vec![CausalResultCell {
            occurrence: format!("world/{name}/result"),
            left_member: Some(fixture.before.clone()),
            right_member: Some(fixture.after.clone()),
        }]
    } else {
        vec![
            CausalResultCell {
                occurrence: format!("world/{name}/left"),
                left_member: Some(fixture.before.clone()),
                right_member: None,
            },
            CausalResultCell {
                occurrence: format!("world/{name}/right"),
                left_member: None,
                right_member: Some(fixture.after.clone()),
            },
        ]
    };
    CausalOperationWorldReturn::found(
        format!("world/{name}"),
        material.occurrence.clone(),
        vec![fixture.before.clone()],
        vec![fixture.after.clone()],
        result_cells,
        testimony(name),
        vec!["unobserved successor histories remain open".to_owned()],
    )
    .unwrap()
}

struct InsufficiencyStanding;

impl MaterialFactorizationStanding for InsufficiencyStanding {
    fn validate_material_standing(&self) -> Result<(), String> {
        Ok(())
    }

    fn material_standing_identity(&self) -> &str {
        "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
    }

    fn material_standing_branches(&self) -> &[crate::athena_native::SituatedCultivationBranch] {
        unreachable!("an insufficient candidate family never enters situated support")
    }

    fn material_standing_ecology(
        &self,
    ) -> &holonic_engine::native_spool::NativeSituatedSpoolBundle {
        unreachable!("an insufficient candidate family never enters situated support")
    }

    fn material_standing_realization(
        &self,
    ) -> &crate::athena_native::ReceiverHistoryRealizationPassage {
        unreachable!("an insufficient candidate family never enters situated support")
    }
}

#[test]
fn equal_value_union_and_product_are_separated_by_the_next_history() {
    let union = returned("union", false).invariant().unwrap();
    let product = returned("product", true).invariant().unwrap();
    assert_eq!(union.returned_population, 4);
    assert_eq!(product.returned_population, 4);
    assert_ne!(
        union.identity_sha256().unwrap(),
        product.identity_sha256().unwrap()
    );
    let separator = shortest_separator(&union, &product).unwrap();
    assert_eq!(separator.left_returned_population, 5);
    assert_eq!(separator.right_returned_population, 6);
}

#[test]
fn presentation_names_do_not_enter_the_operation_invariant() {
    let prose = returned("prose", false).invariant().unwrap();
    let notation = returned("notation", false).invariant().unwrap();
    assert_eq!(prose, notation);
    assert_eq!(
        prose.identity_sha256().unwrap(),
        notation.identity_sha256().unwrap()
    );
}

#[test]
fn incomplete_incidence_is_refused_instead_of_guessed() {
    let mut incomplete = cells("broken", false);
    incomplete.pop();
    let error = CausalOperationWorldReturn::found(
        "broken/return",
        "broken/material",
        (0..2).map(|at| format!("broken/left/{at}")).collect(),
        (0..2).map(|at| format!("broken/right/{at}")).collect(),
        incomplete,
        testimony("broken"),
        vec!["open".to_owned()],
    )
    .unwrap_err();
    assert_eq!(error, MaterialFactorizationError::OperationGeometry);
}

#[test]
fn hierarchical_optical_candidates_retain_the_passage_and_return_operation_insufficiency() {
    let fixture = hierarchical_optical_fixture();
    let material = AddressedMaterialOccurrence::found(
        "material/optical",
        &fixture.payload,
        None,
        vec!["raster-apparatus".to_owned()],
        vec!["exterior identity remains open".to_owned()],
    )
    .unwrap();
    let returned = vec![
        optical_world_return(&material, &fixture, "union", false),
        optical_world_return(&material, &fixture, "product", true),
    ];
    let candidates =
        HierarchicalOpticalMaterialCandidates::found(&material, &fixture.passage, &returned)
            .unwrap();
    assert_eq!(candidates.bindings().len(), 2);
    assert_eq!(candidates.passage().holons.len(), 4);
    assert_eq!(candidates.passage().alternative_covers.len(), 1);
    assert_eq!(
        candidates.native_consequence().equation_glyph_fibres.len(),
        1
    );

    let standing = InsufficiencyStanding;
    let aperture = MaterialFactorizationAperture {
        rest: &standing,
        chart: MaterialReceiverChart {
            axes: Vec::new(),
            forward: Vec::new(),
            inverse: Vec::new(),
            forward_then_inverse_is_identity: true,
            inverse_then_forward_is_identity: true,
        },
        shared_affine_transports: RefCell::new(BTreeMap::new()),
    };
    let returned = aperture
        .factor_hierarchical_optical_candidates(&candidates)
        .unwrap();
    let HierarchicalOpticalMaterialReturn::Insufficient {
        passage,
        bindings,
        material_return: MaterialFactorizationReturn::Insufficient(insufficiency),
        open_identity,
    } = returned
    else {
        panic!("plural operation identities were guessed closed")
    };
    assert_eq!(
        passage.alternative_covers,
        fixture.passage.alternative_covers
    );
    assert_eq!(bindings, candidates.bindings());
    assert_eq!(insufficiency.candidate_sections.len(), 2);
    assert!(open_identity
        .iter()
        .any(|face| face.contains("separating receiver history")));
}

#[test]
fn world_return_outside_every_optical_constraint_section_is_refused() {
    let fixture = hierarchical_optical_fixture();
    let material = AddressedMaterialOccurrence::found(
        "material/optical/unmatched",
        &fixture.payload,
        None,
        Vec::new(),
        vec!["open".to_owned()],
    )
    .unwrap();
    let outside = "outside-the-hierarchical-passage".to_owned();
    let returned = CausalOperationWorldReturn::found(
        "world/unmatched",
        material.occurrence.clone(),
        vec![outside.clone()],
        vec![fixture.after.clone()],
        vec![
            CausalResultCell {
                occurrence: "world/unmatched/left".to_owned(),
                left_member: Some(outside),
                right_member: None,
            },
            CausalResultCell {
                occurrence: "world/unmatched/right".to_owned(),
                left_member: None,
                right_member: Some(fixture.after.clone()),
            },
        ],
        testimony("unmatched"),
        vec!["open".to_owned()],
    )
    .unwrap();
    let error = HierarchicalOpticalMaterialCandidates::found(
        &material,
        &fixture.passage,
        std::slice::from_ref(&returned),
    )
    .unwrap_err();
    assert_eq!(
        error,
        MaterialFactorizationError::OpticalCandidateLineage {
            world_return_occurrence: returned.occurrence,
        }
    );
}

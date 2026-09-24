use super::*;
use crate::ported_operation::PortedOperationComplex;
use crate::source_occurrence::OccurrenceWitness;

mod population;

fn rat(value: i64) -> Rat {
    Rat::from_integer(value.into())
}

fn boundary(id: BoundaryId) -> TypedMathematicalBoundary {
    TypedMathematicalBoundary::new(id, "Q", None, Vec::new()).expect("typed boundary")
}

#[test]
fn law_identity_not_display_name_routes_the_license() {
    let mut complex = PortedOperationComplex::new("licensed");
    let input = complex.port("input");
    let output = complex.port("output");
    let law = complex
        .bind_operation(
            "original display",
            OperationSpecies::Transport,
            vec![input],
            vec![output],
            None,
            Vec::new(),
        )
        .expect("law");
    let base = crate::quantity::BaseUnits::declare(["one"]).expect("base");
    let dimensionless = base.dimensionless();
    let typed_input = TypedMathematicalBoundary::coordinate_word(
        input,
        "Q",
        vec![dimensionless.clone(), dimensionless.clone()],
        Vec::new(),
    )
    .expect("two input coordinates");
    let typed_output = TypedMathematicalBoundary::new(output, "Q", Some(dimensionless), Vec::new())
        .expect("one output coordinate");
    let matrix = ExactRatMatrix::new(vec![vec![rat(1), rat(-1)]]).expect("matrix");
    let license = ExactOwnerLicense::exact_linear(
        law,
        "lineage-only display",
        "contract-tiled(apparatus tile)",
        OperationSpecies::Transport,
        vec![typed_input],
        vec![typed_output],
        &matrix,
        &[rat(2), rat(2)],
        BTreeMap::new(),
    )
    .expect("zero constraint");
    complex.shape.laws.get_mut(&law).expect("law").name = "renamed display".to_owned();
    let witness = ExactOwnerOccurrence::new(vec![license]).expect("witness");
    let validated = witness.validate(&complex).expect("name does not route");
    assert_eq!(validated[0].operation, "renamed display");
    assert_eq!(validated[0].exact_owner_licenses[0].constraint().law(), law);
}

#[test]
fn evidence_identity_omits_display_name_and_covers_semantic_structure() {
    let law = crate::evolution::EvolutionLawId(7);
    let output = BoundaryId(1);
    let matrix = ExactRatMatrix::new(vec![vec![rat(0)]]).expect("zero");
    let issue = |display: &str, parameter: &str| {
        ExactOwnerLicense::exact_linear(
            law,
            display,
            "enter",
            OperationSpecies::Construction,
            Vec::new(),
            vec![boundary(output)],
            &matrix,
            &[rat(0)],
            BTreeMap::from([("population".to_owned(), parameter.to_owned())]),
        )
        .expect("license")
    };
    let left = issue("first display", "x");
    let renamed = issue("renamed display", "x");
    let moved = issue("first display", "y");
    assert_eq!(left.evidence_sha256(), renamed.evidence_sha256());
    assert_ne!(left.evidence_sha256(), moved.evidence_sha256());
}

#[test]
fn an_exact_linear_nonzero_residual_does_not_issue_a_license() {
    let matrix = ExactRatMatrix::new(vec![vec![rat(1)]]).expect("matrix");
    let refusal = ExactOwnerLicense::exact_linear(
        crate::evolution::EvolutionLawId(1),
        "constraint",
        "contract-tiled(apparatus tile)",
        OperationSpecies::Transport,
        Vec::new(),
        Vec::new(),
        &matrix,
        &[rat(1)],
        BTreeMap::new(),
    )
    .expect_err("nonzero is a refusal");
    assert!(matches!(
        refusal,
        ExactOwnerWitnessRefusal::ExactLinearResidualNonzero { .. }
    ));
}

#[test]
fn contraction_typing_pairs_across_boundaries_but_exact_linear_keeps_it_open() {
    let left = BoundaryId(1);
    let right = BoundaryId(2);
    let base = crate::quantity::BaseUnits::declare(["one"]).expect("base");
    let dimensionless = base.dimensionless();
    let left_address = TensorSlotAddress {
        boundary: left,
        ordinal: 0,
    };
    let right_address = TensorSlotAddress {
        boundary: right,
        ordinal: 0,
    };
    let left_boundary = TypedMathematicalBoundary::new(
        left,
        "tensor",
        Some(dimensionless.clone()),
        vec![TensorSlot {
            ordinal: 0,
            binder: 7,
            variance: TensorVariance::Covariant,
            role: TensorSlotRole::ContractedWith(right_address),
        }],
    )
    .expect("left");
    let right_boundary = TypedMathematicalBoundary::new(
        right,
        "tensor",
        Some(dimensionless.clone()),
        vec![TensorSlot {
            ordinal: 0,
            binder: 7,
            variance: TensorVariance::Contravariant,
            role: TensorSlotRole::ContractedWith(left_address),
        }],
    )
    .expect("right");
    let free = TypedMathematicalBoundary::new(
        BoundaryId(3),
        "tensor",
        Some(dimensionless),
        vec![
            TensorSlot {
                ordinal: 0,
                binder: 10,
                variance: TensorVariance::Covariant,
                role: TensorSlotRole::Free,
            },
            TensorSlot {
                ordinal: 1,
                binder: 11,
                variance: TensorVariance::Covariant,
                role: TensorSlotRole::Free,
            },
        ],
    )
    .expect("free slots");
    let zero = ExactRatMatrix::new(vec![vec![rat(0), rat(0)]]).expect("zero");
    validate_contractions([&left_boundary, &right_boundary, &free].into_iter())
        .expect("the tensor typing itself pairs across boundaries");
    assert_eq!(
        ExactOwnerLicense::exact_linear(
            crate::evolution::EvolutionLawId(1),
            "contraction",
            "contract-tiled(apparatus tile)",
            OperationSpecies::Transport,
            vec![left_boundary, right_boundary],
            vec![free],
            &zero,
            &[rat(0), rat(0)],
            BTreeMap::new(),
        )
        .unwrap_err(),
        ExactOwnerWitnessRefusal::ExactLinearTensorContractionOpen
    );
}

#[test]
fn quantity_license_requires_total_boundary_column_incidence() {
    let base = crate::quantity::BaseUnits::declare(["L"]).expect("base");
    let dimensionless = base.dimensionless();
    let dimensions = DimensionMatrix::declare(
        base,
        vec![
            ("input".to_owned(), dimensionless.clone()),
            ("output".to_owned(), dimensionless.clone()),
        ],
    )
    .expect("dimensions");
    let kernel = dimensions.buckingham().expect("kernel").basis[0]
        .exponents
        .clone();
    let input = BoundaryId(1);
    let output = BoundaryId(2);
    let refusal = ExactOwnerLicense::quantity(
        crate::evolution::EvolutionLawId(1),
        "quantity",
        "contract-tiled(apparatus tile)",
        OperationSpecies::Construction,
        vec![
            TypedMathematicalBoundary::coordinate_word(
                input,
                "Q",
                vec![dimensionless.clone(), dimensionless.clone()],
                Vec::new(),
            )
            .expect("input"),
        ],
        vec![
            TypedMathematicalBoundary::new(output, "Q", Some(dimensionless), Vec::new())
                .expect("output"),
        ],
        BTreeMap::new(),
        &dimensions,
        &kernel,
        BTreeMap::new(),
    )
    .expect_err("the input coordinate word is unmapped");
    assert_eq!(
        refusal,
        ExactOwnerWitnessRefusal::QuantityBoundaryColumnsDisagree
    );
}

#[test]
fn quantity_license_checks_the_exact_dimension_at_each_mapped_column() {
    let base = crate::quantity::BaseUnits::declare(["L"]).expect("base");
    let dimensionless = base.dimensionless();
    let length = base.unit("L").expect("length");
    let dimensions = DimensionMatrix::declare(
        base,
        vec![
            ("input".to_owned(), dimensionless.clone()),
            ("output".to_owned(), length),
        ],
    )
    .expect("dimensions");
    let input = BoundaryId(1);
    let output = BoundaryId(2);
    let refusal = ExactOwnerLicense::quantity(
        crate::evolution::EvolutionLawId(1),
        "quantity",
        "contract-tiled(apparatus tile)",
        OperationSpecies::Construction,
        vec![
            TypedMathematicalBoundary::coordinate_word(
                input,
                "Q",
                vec![dimensionless.clone(), dimensionless.clone()],
                Vec::new(),
            )
            .expect("input"),
        ],
        vec![
            TypedMathematicalBoundary::new(output, "Q", Some(dimensionless), Vec::new())
                .expect("output"),
        ],
        BTreeMap::from([(input, vec![0, 1])]),
        &dimensions,
        &[rat(1), rat(0)],
        BTreeMap::new(),
    )
    .expect_err("input coordinate one says dimensionless but the column says length");
    assert_eq!(
        refusal,
        ExactOwnerWitnessRefusal::QuantityBoundaryDimensionDisagrees {
            boundary: input,
            coordinate: 1,
            column: 1,
        }
    );
}

#[test]
fn width_three_quantity_boundary_carries_a_nontrivial_kernel_word() {
    let base = crate::quantity::BaseUnits::declare(["U"]).expect("base");
    let unit = base.unit("U").expect("unit");
    let dimensionless = base.dimensionless();
    let dimensions = DimensionMatrix::declare(
        base,
        vec![
            ("u0".to_owned(), unit.clone()),
            ("u1".to_owned(), unit.clone()),
            ("u2".to_owned(), unit.clone()),
        ],
    )
    .expect("dimensions");
    let input = BoundaryId(1);
    let output = BoundaryId(2);
    let kernel = vec![rat(1), rat(1), rat(-2)];
    let license = ExactOwnerLicense::quantity(
        crate::evolution::EvolutionLawId(1),
        "quantity",
        "contract-tiled(apparatus tile)",
        OperationSpecies::Transport,
        vec![
            TypedMathematicalBoundary::coordinate_word(
                input,
                "Q",
                vec![unit.clone(), unit.clone(), unit],
                Vec::new(),
            )
            .expect("input"),
        ],
        vec![
            TypedMathematicalBoundary::new(output, "Q", Some(dimensionless), Vec::new())
                .expect("output"),
        ],
        BTreeMap::from([(input, vec![0, 1, 2])]),
        &dimensions,
        &kernel,
        BTreeMap::new(),
    )
    .expect("nontrivial kernel");
    assert_eq!(
        license.constraint().quantity_kernel_word(),
        Some(kernel.as_slice())
    );
}

#[test]
fn quantity_column_words_refuse_overlap_and_reordering() {
    let base = crate::quantity::BaseUnits::declare(["U"]).expect("base");
    let unit = base.unit("U").expect("unit");
    let dimensionless = base.dimensionless();
    let dimensions = DimensionMatrix::declare(
        base,
        vec![
            ("u".to_owned(), unit.clone()),
            ("one".to_owned(), dimensionless.clone()),
        ],
    )
    .expect("dimensions");
    let left = BoundaryId(1);
    let right = BoundaryId(2);
    let overlap = ExactOwnerLicense::quantity(
        crate::evolution::EvolutionLawId(1),
        "overlap",
        "contract-tiled(apparatus tile)",
        OperationSpecies::Transport,
        vec![
            TypedMathematicalBoundary::new(left, "Q", Some(unit.clone()), Vec::new())
                .expect("left"),
            TypedMathematicalBoundary::new(right, "Q", Some(dimensionless.clone()), Vec::new())
                .expect("right"),
        ],
        Vec::new(),
        BTreeMap::from([(left, vec![0]), (right, vec![0])]),
        &dimensions,
        &[rat(0), rat(1)],
        BTreeMap::new(),
    )
    .expect_err("column zero overlaps");
    assert_eq!(
        overlap,
        ExactOwnerWitnessRefusal::QuantityBoundaryColumnsOverlap { column: 0 }
    );

    let reordered = ExactOwnerLicense::quantity(
        crate::evolution::EvolutionLawId(1),
        "reordered",
        "contract-tiled(apparatus tile)",
        OperationSpecies::Transport,
        vec![
            TypedMathematicalBoundary::coordinate_word(
                left,
                "Q",
                vec![unit, dimensionless],
                Vec::new(),
            )
            .expect("word"),
        ],
        Vec::new(),
        BTreeMap::from([(left, vec![1, 0])]),
        &dimensions,
        &[rat(0), rat(1)],
        BTreeMap::new(),
    )
    .expect_err("the column word is reversed");
    assert!(matches!(
        reordered,
        ExactOwnerWitnessRefusal::QuantityBoundaryDimensionDisagrees {
            coordinate: 0,
            column: 1,
            ..
        }
    ));
}

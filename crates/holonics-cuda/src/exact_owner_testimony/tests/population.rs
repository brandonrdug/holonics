use super::*;

use crate::resident_law::{Enter, EnteringRows, ResidentLaw, ResidentMaterial};
use crate::resident_section::Dyadic;

fn bf16_integer(value: i32) -> u16 {
    if value == 0 {
        return 0;
    }
    let negative = value < 0;
    let magnitude = value.unsigned_abs();
    let exponent = 31 - magnitude.leading_zeros();
    let significand = if exponent <= 7 {
        magnitude << (7 - exponent)
    } else {
        magnitude >> (exponent - 7)
    };
    ((negative as u16) << 15) | (((exponent + 127) as u16) << 7) | (significand as u16 - 128)
}

#[test]
fn exact_linear_population_identity_matches_all_three_resident_rows() {
    let matrix = ExactRatMatrix::new(vec![vec![rat(1), rat(1), rat(-2)]]).unwrap();
    let standing = vec![
        rat(3),
        rat(-1),
        rat(1),
        rat(5),
        rat(-1),
        rat(2),
        rat(-2),
        rat(8),
        rat(3),
    ];
    let license = ExactOwnerLicense::exact_linear_population(
        crate::evolution::EvolutionLawId(1),
        "batch",
        "enter",
        OperationSpecies::Construction,
        Vec::new(),
        vec![boundary(BoundaryId(1))],
        &matrix,
        3,
        3,
        &standing,
        BTreeMap::new(),
    )
    .unwrap();
    assert_eq!(license.constraint().input_shape(), (3, 3));
    assert_eq!(license.constraint().residual(), &[rat(0), rat(0), rat(0)]);

    let mut material = ResidentMaterial::empty();
    material.entering.insert(
        "x".to_owned(),
        EnteringRows {
            words: standing
                .iter()
                .map(|value| bf16_integer(value.to_integer().try_into().unwrap()))
                .collect(),
            rows: 3,
            width: 3,
        },
    );
    let enter = Enter {
        population: "x".to_owned(),
        scale: Dyadic::ONE,
    };
    assert_eq!(
        enter.exact_input_identity(&material).unwrap().unwrap(),
        license.constraint().input_identity()
    );
}

#[test]
fn exact_linear_population_refuses_missing_reordered_and_one_bad_row() {
    let matrix = ExactRatMatrix::new(vec![vec![rat(1), rat(1), rat(-2)]]).unwrap();
    let standing = vec![
        rat(3),
        rat(-1),
        rat(1),
        rat(5),
        rat(-1),
        rat(2),
        rat(-2),
        rat(8),
        rat(3),
    ];
    let identity = exact_input_population_identity(3, 3, &standing).unwrap();
    let mut reordered = standing.clone();
    reordered.rotate_left(3);
    assert_ne!(
        identity,
        exact_input_population_identity(3, 3, &reordered).unwrap()
    );
    assert!(matches!(
        exact_input_population_identity(3, 3, &standing[..6]),
        Err(ExactOwnerWitnessRefusal::ExactInputPopulationExtent { .. })
    ));
    let mut bad = standing.clone();
    bad[8] = rat(4);
    assert!(matches!(
        ExactOwnerLicense::exact_linear_population(
            crate::evolution::EvolutionLawId(1),
            "bad-row",
            "enter",
            OperationSpecies::Construction,
            Vec::new(),
            vec![boundary(BoundaryId(1))],
            &matrix,
            3,
            3,
            &bad,
            BTreeMap::new(),
        ),
        Err(ExactOwnerWitnessRefusal::ExactLinearResidualNonzero { residual })
            if residual == vec![rat(0), rat(0), rat(-2)]
    ));
}

#[test]
fn exact_linear_transport_coordinate_words_must_cover_the_matrix_domain_and_codomain() {
    let base = crate::quantity::BaseUnits::declare(["one"]).unwrap();
    let dimensionless = base.dimensionless();
    let typed = |boundary| {
        TypedMathematicalBoundary::new(boundary, "Q", Some(dimensionless.clone()), Vec::new())
            .unwrap()
    };
    let one_by_two = ExactRatMatrix::new(vec![vec![rat(0), rat(0)]]).unwrap();
    assert_eq!(
        ExactOwnerLicense::exact_linear(
            crate::evolution::EvolutionLawId(1),
            "short-domain",
            "contract-tiled(apparatus tile)",
            OperationSpecies::Transport,
            vec![typed(BoundaryId(1))],
            vec![typed(BoundaryId(2))],
            &one_by_two,
            &[rat(0), rat(0)],
            BTreeMap::new(),
        )
        .unwrap_err(),
        ExactOwnerWitnessRefusal::ExactLinearCoordinateExtentDisagrees {
            input_coordinates: 1,
            output_coordinates: 1,
            matrix_rows: 1,
            matrix_columns: 2,
        }
    );

    let two_by_one = ExactRatMatrix::new(vec![vec![rat(0)], vec![rat(0)]]).unwrap();
    assert_eq!(
        ExactOwnerLicense::exact_linear(
            crate::evolution::EvolutionLawId(1),
            "short-codomain",
            "contract-tiled(apparatus tile)",
            OperationSpecies::Transport,
            vec![typed(BoundaryId(1))],
            vec![typed(BoundaryId(2))],
            &two_by_one,
            &[rat(0)],
            BTreeMap::new(),
        )
        .unwrap_err(),
        ExactOwnerWitnessRefusal::ExactLinearCoordinateExtentDisagrees {
            input_coordinates: 1,
            output_coordinates: 1,
            matrix_rows: 2,
            matrix_columns: 1,
        }
    );

    let two_by_two = ExactRatMatrix::new(vec![vec![rat(0), rat(0)], vec![rat(0), rat(0)]]).unwrap();
    assert!(
        ExactOwnerLicense::exact_linear(
            crate::evolution::EvolutionLawId(1),
            "total-coordinate-cover",
            "contract-tiled(apparatus tile)",
            OperationSpecies::Transport,
            vec![typed(BoundaryId(1)), typed(BoundaryId(2))],
            vec![typed(BoundaryId(3)), typed(BoundaryId(4))],
            &two_by_two,
            &[rat(0), rat(0)],
            BTreeMap::new(),
        )
        .is_ok()
    );
}

#[test]
fn exact_linear_transport_cannot_erase_free_indices_or_claim_an_untyped_contraction() {
    let input = BoundaryId(1);
    let output = BoundaryId(2);
    let base = crate::quantity::BaseUnits::declare(["one"]).unwrap();
    let dimensionless = base.dimensionless();
    let free = TensorSlot {
        ordinal: 0,
        binder: 10,
        variance: TensorVariance::Covariant,
        role: TensorSlotRole::Free,
    };
    let typed_input =
        TypedMathematicalBoundary::new(input, "Q", Some(dimensionless.clone()), vec![free])
            .unwrap();
    let erased_output =
        TypedMathematicalBoundary::new(output, "Q", Some(dimensionless.clone()), Vec::new())
            .unwrap();
    let matrix = ExactRatMatrix::new(vec![vec![rat(0)]]).unwrap();
    assert_eq!(
        ExactOwnerLicense::exact_linear(
            crate::evolution::EvolutionLawId(1),
            "erases-mu",
            "contract-tiled(apparatus tile)",
            OperationSpecies::Transport,
            vec![typed_input],
            vec![erased_output],
            &matrix,
            &[rat(1)],
            BTreeMap::new(),
        )
        .unwrap_err(),
        ExactOwnerWitnessRefusal::ExactLinearFreeTensorWordDisagrees
    );

    let left = TensorSlotAddress {
        boundary: input,
        ordinal: 0,
    };
    let right = TensorSlotAddress {
        boundary: output,
        ordinal: 0,
    };
    let contracted_input = TypedMathematicalBoundary::new(
        input,
        "Q",
        Some(dimensionless.clone()),
        vec![TensorSlot {
            role: TensorSlotRole::ContractedWith(right),
            ..free
        }],
    )
    .unwrap();
    let contracted_output = TypedMathematicalBoundary::new(
        output,
        "Q",
        Some(dimensionless),
        vec![TensorSlot {
            variance: TensorVariance::Contravariant,
            role: TensorSlotRole::ContractedWith(left),
            ..free
        }],
    )
    .unwrap();
    assert_eq!(
        ExactOwnerLicense::exact_linear(
            crate::evolution::EvolutionLawId(1),
            "untyped-contraction",
            "contract-tiled(apparatus tile)",
            OperationSpecies::Transport,
            vec![contracted_input],
            vec![contracted_output],
            &matrix,
            &[rat(1)],
            BTreeMap::new(),
        )
        .unwrap_err(),
        ExactOwnerWitnessRefusal::ExactLinearTensorContractionOpen
    );
}

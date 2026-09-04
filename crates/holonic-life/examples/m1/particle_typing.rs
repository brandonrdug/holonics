//! Typed operation complex, exact-owner licensing, and the one resident passage.

use std::collections::{BTreeMap, BTreeSet};

use holonic_engine::category::BoundaryId;
use holonic_engine::exact_linear::ExactRatMatrix;
use holonic_engine::exact_owner_testimony::{
    ExactOwnerLicense, ExactOwnerOccurrence, ExactOwnerWitnessRefusal,
};
use holonic_engine::ported_operation::{
    OperationSpecies, PortedOperationComplex, PortedTransport, PortedWord,
};
use holonic_engine::quantity::{BaseUnits, DimensionMatrix, Quantity};
use life::mathematical_particle::{
    conduct_exact_linear, conduct_exact_linear_population, conduct_exact_quantity,
    ExactLinearOwnerReturn, ExactQuantityOwnerReturn, OperationWordStep, PassageBranchId,
    TensorSlot, TensorSlotRole, TensorVariance, TypedConstructionStep, TypedMathematicalBoundary,
    TypedOperationWord, TypedPassage,
};
use num_bigint::BigInt;
use num_rational::BigRational as Rat;

use super::particle_operation::{self, EventIds, LawIds, PortIds};
use super::resident_affine::{self, ResidentEvents};

pub struct TypedBoundaries {
    pub affine_input: TypedMathematicalBoundary,
    pub affine_output: TypedMathematicalBoundary,
    pub heat_input: TypedMathematicalBoundary,
    pub heat_output: TypedMathematicalBoundary,
    pub quantity_input: TypedMathematicalBoundary,
    pub quantity_output: TypedMathematicalBoundary,
}

pub struct OperationAssembly {
    pub operation: PortedOperationComplex,
    pub ports: PortIds,
    pub laws: LawIds,
    pub boundaries: TypedBoundaries,
    pub passage: TypedPassage,
    pub affine_standing: Vec<Rat>,
    pub affine_return: ExactLinearOwnerReturn,
    pub heat_return: ExactLinearOwnerReturn,
    pub quantity_return: ExactQuantityOwnerReturn,
    pub licenses: Vec<ExactOwnerLicense>,
    pub exact_owner: ExactOwnerOccurrence,
    pub refused_attempt: Result<Vec<ExactOwnerLicense>, ExactOwnerWitnessRefusal>,
    pub resident: resident_affine::ResidentDeed,
}

pub fn construct(
    all_sources: &BTreeSet<String>,
    affine_sources: &BTreeSet<String>,
    heat_sources: &BTreeSet<String>,
) -> Result<OperationAssembly, String> {
    let particle_operation::OperationTopology {
        operation,
        ports,
        laws,
        events,
    } = particle_operation::construct()?;
    let base = BaseUnits::declare(["U"]).map_err(|error| error.to_string())?;
    let unit = base.unit("U").map_err(|error| error.to_string())?;
    let dimensionless = base.dimensionless();
    let free_covariant = vec![
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
    ];
    let boundaries = TypedBoundaries {
        affine_input: TypedMathematicalBoundary::coordinate_word(
            ports.affine_in,
            "Q",
            vec![dimensionless.clone(); 3],
            Vec::new(),
        )
        .map_err(|error| error.to_string())?,
        affine_output: TypedMathematicalBoundary::new(
            ports.affine_out,
            "Q",
            Some(dimensionless.clone()),
            Vec::new(),
        )
        .map_err(|error| error.to_string())?,
        heat_input: TypedMathematicalBoundary::coordinate_word(
            ports.heat_in,
            "Q",
            vec![dimensionless.clone(); 2],
            free_covariant.clone(),
        )
        .map_err(|error| error.to_string())?,
        heat_output: TypedMathematicalBoundary::new(
            ports.heat_out,
            "Q",
            Some(dimensionless.clone()),
            free_covariant,
        )
        .map_err(|error| error.to_string())?,
        quantity_input: TypedMathematicalBoundary::coordinate_word(
            ports.quantity_in,
            "Q",
            vec![unit.clone(), unit.clone(), unit.clone()],
            Vec::new(),
        )
        .map_err(|error| error.to_string())?,
        quantity_output: TypedMathematicalBoundary::new(
            ports.quantity_out,
            "Q",
            Some(dimensionless.clone()),
            Vec::new(),
        )
        .map_err(|error| error.to_string())?,
    };
    let affine_zero = matrix(&[&[0, 0, 0]])?;
    let affine_matrix = matrix(&[&[1, 1, -2]])?;
    let affine_values = rats(&[3, -1, 1, 3, -1, 1, -1, 3, 1, -1, 3, 1]);
    let heat_zero = matrix(&[&[0, 0]])?;
    let heat_matrix = matrix(&[&[1, -1]])?;
    let heat_values = rats(&[2, 2]);
    let dimensions = DimensionMatrix::declare(
        base.clone(),
        vec![
            ("u0".to_owned(), unit.clone()),
            ("u1".to_owned(), unit.clone()),
            ("u2".to_owned(), unit.clone()),
        ],
    )
    .map_err(|error| error.to_string())?;
    let kernel_word = rats(&[1, 1, -2]);
    if !dimensions
        .buckingham()
        .map_err(|error| error.to_string())?
        .contains(&kernel_word)
    {
        return Err("the quantity kernel left the exact dimension kernel".to_owned());
    }
    let quantity_columns = BTreeMap::from([(ports.quantity_in, vec![0, 1, 2])]);
    let licenses = vec![
        ExactOwnerLicense::exact_linear_population(
            laws.affine_enter,
            "affine-enter lineage",
            "enter",
            OperationSpecies::Construction,
            Vec::new(),
            vec![boundaries.affine_input.clone()],
            &affine_zero,
            4,
            3,
            &affine_values,
            semantic_parameters("affine-x", true),
        ),
        ExactOwnerLicense::exact_linear_population(
            laws.affine_contract,
            "affine-contract lineage",
            "contract-tiled(apparatus tile)",
            OperationSpecies::Transport,
            vec![boundaries.affine_input.clone()],
            vec![boundaries.affine_output.clone()],
            &affine_matrix,
            4,
            3,
            &affine_values,
            semantic_parameters("affine-map", false),
        ),
        ExactOwnerLicense::exact_linear(
            laws.heat_enter,
            "heat-enter conditional fixture lineage",
            "enter",
            OperationSpecies::Construction,
            Vec::new(),
            vec![boundaries.heat_input.clone()],
            &heat_zero,
            &heat_values,
            semantic_parameters("heat-x", true),
        ),
        ExactOwnerLicense::exact_linear(
            laws.heat_contract,
            "heat-contract conditional fixture lineage",
            "contract-tiled(apparatus tile)",
            OperationSpecies::Transport,
            vec![boundaries.heat_input.clone()],
            vec![boundaries.heat_output.clone()],
            &heat_matrix,
            &heat_values,
            semantic_parameters("heat-map", false),
        ),
        ExactOwnerLicense::quantity(
            laws.quantity_enter,
            "quantity-enter lineage",
            "enter",
            OperationSpecies::Construction,
            Vec::new(),
            vec![boundaries.quantity_input.clone()],
            quantity_columns.clone(),
            &dimensions,
            &kernel_word,
            semantic_parameters("quantity-x", true),
        ),
        ExactOwnerLicense::quantity(
            laws.quantity_contract,
            "quantity-contract lineage",
            "contract-tiled(apparatus tile)",
            OperationSpecies::Transport,
            vec![boundaries.quantity_input.clone()],
            vec![boundaries.quantity_output.clone()],
            quantity_columns.clone(),
            &dimensions,
            &kernel_word,
            semantic_parameters("quantity-map", false),
        ),
    ]
    .into_iter()
    .collect::<Result<Vec<_>, _>>()
    .map_err(|error| error.to_string())?;
    let exact_owner =
        ExactOwnerOccurrence::new(licenses.clone()).map_err(|error| error.to_string())?;
    let passage = passage(
        all_sources,
        affine_sources,
        heat_sources,
        &operation,
        laws,
        events,
    )?;
    let affine_return = conduct_exact_linear_population(
        passage.reference(PassageBranchId(0)).map_err(debug)?,
        &passage,
        &realization(
            "affine-exact-realization",
            "affine-contract",
            ports.affine_in,
            ports.affine_out,
            "Q-chart",
            affine_matrix.clone(),
        )?,
        &BTreeMap::from([
            (laws.affine_enter, affine_zero),
            (laws.affine_contract, affine_matrix.clone()),
        ]),
        &BTreeMap::from([
            (laws.affine_enter, licenses[0].clone()),
            (laws.affine_contract, licenses[1].clone()),
        ]),
        4,
        3,
        &affine_values,
    )
    .map_err(debug)?;
    let heat_return = conduct_exact_linear(
        passage.reference(PassageBranchId(1)).map_err(debug)?,
        &passage,
        &realization(
            "heat-exact-realization",
            "heat-contract",
            ports.heat_in,
            ports.heat_out,
            "conditional-Euclidean-chart",
            heat_matrix.clone(),
        )?,
        &BTreeMap::from([
            (laws.heat_enter, heat_zero),
            (laws.heat_contract, heat_matrix.clone()),
        ]),
        &BTreeMap::from([
            (laws.heat_enter, licenses[2].clone()),
            (laws.heat_contract, licenses[3].clone()),
        ]),
        &heat_values,
    )
    .map_err(debug)?;
    let quantity_return = conduct_exact_quantity(
        passage.reference(PassageBranchId(2)).map_err(debug)?,
        &passage,
        dimensions.clone(),
        BTreeMap::from([
            (laws.quantity_enter, quantity_columns.clone()),
            (laws.quantity_contract, quantity_columns.clone()),
        ]),
        &BTreeMap::from([
            (laws.quantity_enter, licenses[4].clone()),
            (laws.quantity_contract, licenses[5].clone()),
        ]),
        vec![
            Quantity::integer(2, unit.clone()),
            Quantity::integer(3, unit.clone()),
            Quantity::integer(6, unit.clone()),
        ],
    )
    .map_err(debug)?;
    if !quantity_return.returned().dimension().is_dimensionless() {
        return Err("the exact quantity return retained a unit".to_owned());
    }
    let resident = resident_affine::conduct(
        &operation,
        &exact_owner,
        ResidentEvents {
            affine_enter: events.affine_enter,
            affine_contract: events.affine_contract,
            heat_enter: events.heat_enter,
            heat_contract: events.heat_contract,
            quantity_enter: events.quantity_enter,
            quantity_contract: events.quantity_contract,
        },
        &affine_matrix,
        &heat_matrix,
        &dimensions
            .as_exact_matrix()
            .map_err(|error| error.to_string())?,
    )?;
    let refused_dimensions = DimensionMatrix::declare(
        base,
        vec![
            ("u0".to_owned(), unit.clone()),
            ("u1".to_owned(), unit),
            ("u2".to_owned(), dimensionless),
        ],
    )
    .map_err(|error| error.to_string())?;
    let refused_attempt = ExactOwnerLicense::quantity(
        laws.quantity_contract,
        "dimension-refusal-control",
        "contract-tiled(apparatus tile)",
        OperationSpecies::Transport,
        vec![boundaries.quantity_input.clone()],
        vec![boundaries.quantity_output.clone()],
        quantity_columns,
        &refused_dimensions,
        &kernel_word,
        semantic_parameters("quantity-map", false),
    )
    .map(|license| vec![license]);
    Ok(OperationAssembly {
        operation,
        ports,
        laws,
        boundaries,
        passage,
        affine_standing: affine_values,
        affine_return,
        heat_return,
        quantity_return,
        licenses,
        exact_owner,
        refused_attempt,
        resident,
    })
}

fn passage(
    all_sources: &BTreeSet<String>,
    affine_sources: &BTreeSet<String>,
    heat_sources: &BTreeSet<String>,
    operation: &PortedOperationComplex,
    laws: LawIds,
    events: EventIds,
) -> Result<TypedPassage, String> {
    let word = |occurrence, event, law, input, output| {
        TypedOperationWord::found(
            occurrence,
            vec![OperationWordStep {
                event,
                law,
                inputs: vec![input],
                outputs: vec![output],
            }],
            operation,
        )
        .map_err(debug)
    };
    TypedPassage::found(
        "m1-shared-passage",
        BTreeMap::from([
            (PassageBranchId(0), affine_sources.clone()),
            (PassageBranchId(1), heat_sources.clone()),
            (PassageBranchId(2), affine_sources.clone()),
        ]),
        BTreeMap::from([
            (
                PassageBranchId(0),
                TypedConstructionStep {
                    event: events.affine_enter,
                    law: laws.affine_enter,
                    outputs: vec![operation.shape.laws[&laws.affine_enter].outputs[0]],
                },
            ),
            (
                PassageBranchId(1),
                TypedConstructionStep {
                    event: events.heat_enter,
                    law: laws.heat_enter,
                    outputs: vec![operation.shape.laws[&laws.heat_enter].outputs[0]],
                },
            ),
            (
                PassageBranchId(2),
                TypedConstructionStep {
                    event: events.quantity_enter,
                    law: laws.quantity_enter,
                    outputs: vec![operation.shape.laws[&laws.quantity_enter].outputs[0]],
                },
            ),
        ]),
        BTreeMap::from([
            (
                PassageBranchId(0),
                word(
                    "affine-word",
                    events.affine_contract,
                    laws.affine_contract,
                    operation.shape.laws[&laws.affine_contract].inputs[0],
                    operation.shape.laws[&laws.affine_contract].outputs[0],
                )?,
            ),
            (
                PassageBranchId(1),
                word(
                    "heat-word",
                    events.heat_contract,
                    laws.heat_contract,
                    operation.shape.laws[&laws.heat_contract].inputs[0],
                    operation.shape.laws[&laws.heat_contract].outputs[0],
                )?,
            ),
            (
                PassageBranchId(2),
                word(
                    "quantity-word",
                    events.quantity_contract,
                    laws.quantity_contract,
                    operation.shape.laws[&laws.quantity_contract].inputs[0],
                    operation.shape.laws[&laws.quantity_contract].outputs[0],
                )?,
            ),
        ]),
        operation,
        all_sources,
    )
    .map_err(debug)
}

fn realization(
    name: &str,
    step: &str,
    source: BoundaryId,
    target: BoundaryId,
    chart: &str,
    matrix: ExactRatMatrix,
) -> Result<PortedWord, String> {
    PortedWord::founded(
        name,
        vec![PortedTransport::new(step, source, target, chart, matrix)],
    )
    .map_err(|error| error.to_string())
}

fn matrix(rows: &[&[i64]]) -> Result<ExactRatMatrix, String> {
    ExactRatMatrix::new(
        rows.iter()
            .map(|row| row.iter().copied().map(integer).collect())
            .collect(),
    )
    .map_err(|error| error.to_string())
}

fn rats(values: &[i64]) -> Vec<Rat> {
    values.iter().copied().map(integer).collect()
}

fn integer(value: i64) -> Rat {
    Rat::from_integer(BigInt::from(value))
}

fn semantic_parameters(population: &str, enter: bool) -> BTreeMap<String, String> {
    if enter {
        BTreeMap::from([
            ("population".to_owned(), population.to_owned()),
            ("scale-significand".to_owned(), "1".to_owned()),
            ("scale-exponent".to_owned(), "0".to_owned()),
        ])
    } else {
        BTreeMap::from([
            ("population".to_owned(), population.to_owned()),
            ("reduction-word".to_owned(), "Descending".to_owned()),
        ])
    }
}

fn debug(error: impl std::fmt::Debug) -> String {
    format!("{error:?}")
}

//! Focused M1 composition controls.

use std::collections::{BTreeMap, BTreeSet};
use std::sync::OnceLock;

use holonic_engine::embedding_fiber::{AlignedMaterial, ResidentReadout};
use holonic_engine::exact_linear::ExactRatMatrix;
use holonic_engine::exact_owner_testimony::{ExactOwnerLicense, ExactOwnerOccurrence};
use holonic_engine::exact_value::ExactValue;
use holonic_engine::front_passage::{
    AlignedMaterialPlan, ContractTiled, DeedReceiver, Enter, EnteringRows, FrontPassage,
    MountedPopulation, ResidentMaterial, ResidentRealization,
};
use holonic_engine::ported_operation::{
    OperationSpecies, PortedOperationComplex, PortedTransport, PortedWord, SourceTestimony,
};
use holonic_engine::quantity::{BaseUnits, DimensionMatrix, Quantity};
use num_bigint::BigInt;
use num_bigint::BigUint;
use num_rational::BigRational as Rat;
use num_traits::ToPrimitive;

use crate::mathematical_source::{
    correspond, correspondence_demand, derive_layout, layout_demand, ArtifactIdentity, ExactBox,
    ExactExtent, PlacedCarrier, SourceLayoutTestimony, SourceLayoutWorkCover, TestimonyChart,
};

use super::admission::ProposalOwnerAttempt;
use super::*;
use crate::causal_section::{
    CausalSectionReading, SectionPresentationReading, SectionReconstructionFiber, SectionWork,
};
use holonic_engine::receiver_exact_compression::{Partition, ReceiverExactCompression};
use holonic_engine::resident_section::{
    Dyadic, LaneTree, ResidentGrain, ResidentSurface, TileGeometry,
};

mod attacks;

fn integer(value: i64) -> Rat {
    Rat::from_integer(BigInt::from(value))
}

fn admitted_source(
    event: &str,
    locator: &str,
    artifact_bytes: &[u8],
    mark: &[u8],
) -> (SourceLayoutTestimony, String, ExactBox) {
    let artifact = ArtifactIdentity::of_bytes(event, locator, artifact_bytes).unwrap();
    let bounds = ExactBox::new(integer(0), integer(0), integer(2), integer(2)).unwrap();
    let occurrence =
        PlacedCarrier::new(&artifact, 0, mark.to_vec(), Some(0), bounds.clone()).unwrap();
    let address = occurrence.address.clone();
    let occurrences = vec![occurrence];
    let demand = layout_demand(&occurrences).unwrap();
    let testimony = derive_layout(
        TestimonyChart::BornDigital,
        artifact,
        ExactExtent::new(integer(4), integer(4)).unwrap(),
        occurrences,
        &SourceLayoutWorkCover::exactly(&demand),
    )
    .unwrap();
    (testimony, address, bounds)
}

fn history_reading(left: &str, right: &str) -> CausalSectionReading {
    let presentation = |identity: &str| SectionPresentationReading {
        identity: identity.to_owned(),
        lineage: identity.to_owned(),
        states: 1,
        sites: 1,
        bonds: 0,
        compounds: 0,
        contact_faces: BTreeSet::new(),
    };
    let block = BTreeSet::from([left.to_owned(), right.to_owned()]);
    CausalSectionReading {
        schema: "test.causal-section-reading".to_owned(),
        receivers: BTreeSet::from(["exact-value".to_owned()]),
        presentations: vec![presentation(left), presentation(right)],
        root_one_shot_blocks: vec![block.clone()],
        root_conduct_blocks: vec![block.clone()],
        reconstruction_fibers: vec![SectionReconstructionFiber {
            presentations: block,
            outside_declared_population_open: true,
        }],
        shortest_separators: Vec::new(),
        compression: ReceiverExactCompression {
            schema: "test.receiver-exact".to_owned(),
            one_shot: Partition { blocks: Vec::new() },
            conduct: Partition { blocks: Vec::new() },
            rounds: 0,
            collapsed: Vec::new(),
        },
        work: SectionWork {
            presentations: 2,
            states: 2,
            contacts: 0,
            transitions: 0,
            observations: 2,
            complete_state_pair_chart: BigUint::from(1_u8),
        },
    }
}

fn operation_typing(rows: &[(EvolutionLawId, usize, usize)]) -> Vec<TypedOperation> {
    rows.iter()
        .map(|(law, input_arity, output_arity)| TypedOperation {
            law: *law,
            input_arity: *input_arity,
            output_arity: *output_arity,
            hypotheses: BTreeSet::from([HypothesisId(1)]),
            branches: BTreeSet::from([BranchId(1)]),
        })
        .collect()
}

#[allow(clippy::too_many_arguments)]
fn card_deed_receipt(
    operation: &PortedOperationComplex,
    exact_owner: &ExactOwnerOccurrence,
    linear_enter: EventId,
    linear_contract: EventId,
    quantity_enter: EventId,
    quantity_contract: EventId,
    linear_matrix: &ExactRatMatrix,
    quantity_matrix: &ExactRatMatrix,
) -> Result<holonic_engine::front_passage::ExactOwnerDeedReceipt, String> {
    static RECEIPT: OnceLock<Result<holonic_engine::front_passage::ExactOwnerDeedReceipt, String>> =
        OnceLock::new();
    RECEIPT
        .get_or_init(|| {
            mint_card_deed_receipt(
                operation,
                exact_owner,
                linear_enter,
                linear_contract,
                quantity_enter,
                quantity_contract,
                linear_matrix,
                quantity_matrix,
            )
        })
        .clone()
}

#[allow(clippy::too_many_arguments)]
fn mint_card_deed_receipt(
    operation: &PortedOperationComplex,
    exact_owner: &ExactOwnerOccurrence,
    linear_enter: EventId,
    linear_contract: EventId,
    quantity_enter: EventId,
    quantity_contract: EventId,
    linear_matrix: &ExactRatMatrix,
    quantity_matrix: &ExactRatMatrix,
) -> Result<holonic_engine::front_passage::ExactOwnerDeedReceipt, String> {
    let readout: &'static ResidentReadout = Box::leak(Box::new(
        ResidentReadout::new().map_err(|error| format!("open resident readout: {error}"))?,
    ));
    let surface: &'static ResidentSurface<'static> = Box::leak(Box::new(
        ResidentSurface::on(readout).map_err(|error| format!("bind resident surface: {error}"))?,
    ));
    let passage =
        FrontPassage::new(surface, ResidentGrain(8)).reading([linear_contract, quantity_contract]);
    let plan = AlignedMaterialPlan::maps(vec![
        (
            "linear-map".to_owned(),
            linear_matrix.rows(),
            linear_matrix.columns(),
        ),
        (
            "quantity-map".to_owned(),
            quantity_matrix.rows(),
            quantity_matrix.columns(),
        ),
    ]);
    let prediction = passage.predict_aligned_material(&plan);
    let material_admission = passage
        .admit_material(&prediction)
        .map_err(|error| format!("admit aligned material: {error:?}"))?;
    let aligned = |matrix: &ExactRatMatrix| AlignedMaterial {
        entries: matrix
            .entries()
            .iter()
            .map(|value| value.to_integer().to_i64().unwrap())
            .collect(),
        exponent: 0,
        entry_octaves: 2,
        negatives: matrix
            .entries()
            .iter()
            .filter(|value| value < &&integer(0))
            .count() as u64,
    };
    let linear_readout = readout
        .mount(&aligned(linear_matrix), linear_matrix.columns())
        .map_err(|error| format!("mount linear map: {error}"))?;
    let quantity_readout = readout
        .mount(&aligned(quantity_matrix), quantity_matrix.columns())
        .map_err(|error| format!("mount quantity map: {error}"))?;
    let mut material = ResidentMaterial::empty();
    material.entering.insert(
        "linear-x".to_owned(),
        EnteringRows {
            words: vec![bf16_integer(2), bf16_integer(2)],
            rows: 1,
            width: 2,
        },
    );
    material.entering.insert(
        "quantity-x".to_owned(),
        EnteringRows {
            words: vec![bf16_integer(1), bf16_integer(1), bf16_integer(-2)],
            rows: 1,
            width: 3,
        },
    );
    material.populations.insert(
        "linear-map".to_owned(),
        MountedPopulation {
            readout: linear_readout,
            mass_value_octaves: 2,
        },
    );
    material.populations.insert(
        "quantity-map".to_owned(),
        MountedPopulation {
            readout: quantity_readout,
            mass_value_octaves: 2,
        },
    );
    if material_admission
        .reconcile(&material)
        .iter()
        .any(|(_, predicted, actual)| predicted != actual)
    {
        return Err("resident material disagrees with its admitted prediction".to_owned());
    }
    let tile = TileGeometry {
        tile_rows: 1,
        lanes: 32,
        outs_per_block: 1,
        k_tile: 4,
        splits: 1,
    };
    let mut realization = ResidentRealization::default();
    realization.bind(
        linear_enter,
        Enter {
            population: "linear-x".to_owned(),
            scale: Dyadic::ONE,
        },
    );
    realization.bind(
        quantity_enter,
        Enter {
            population: "quantity-x".to_owned(),
            scale: Dyadic::ONE,
        },
    );
    realization.bind(
        linear_contract,
        ContractTiled {
            population: "linear-map".to_owned(),
            tile,
            admitted_node_octaves: ResidentSurface::carrier_octaves(),
            tree: LaneTree::Descending,
        },
    );
    realization.bind(
        quantity_contract,
        ContractTiled {
            population: "quantity-map".to_owned(),
            tile,
            admitted_node_octaves: ResidentSurface::carrier_octaves(),
            tree: LaneTree::Descending,
        },
    );
    let compiled = passage
        .compile(
            operation,
            &realization,
            &material,
            exact_owner,
            linear_contract,
        )
        .map_err(|error| format!("compile exact-owner passage: {error:?}"))?;
    let admission = passage
        .admit(
            &compiled,
            &DeedReceiver::unbounded(),
            Some(&material_admission),
        )
        .map_err(|error| format!("admit exact-owner passage: {error:?}"))?;
    let bound = passage
        .realize(compiled, &material, admission)
        .map_err(|error| format!("realize exact-owner passage: {error:?}"))?;
    let (_, receipt) = bound
        .launch_with_exact_owner_receipt(&bound.mode)
        .map_err(|error| format!("launch exact-owner passage: {error:?}"))?;
    Ok(receipt)
}

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

fn fixture() -> Result<MathematicalParticleInput, String> {
    let (left_source, left, left_box) = admitted_source("source-left", "left", b"left", b"mu");
    let (right_source, right, right_box) =
        admitted_source("source-right", "right", b"right", b"mu");
    let correspondence = correspondence_demand(&left_source, &right_source).unwrap();
    let presentation_fibre = correspond(
        &left_source,
        &right_source,
        &SourceLayoutWorkCover::exactly(&correspondence),
    )
    .unwrap();

    let mut operation = PortedOperationComplex::new("particle-operation");
    let linear_input = operation.port("linear-input");
    let linear_output = operation.port("linear-output");
    let quantity_input = operation.port("quantity-input");
    let quantity_output = operation.port("quantity-output");

    let linear_enter_law = operation
        .bind_operation(
            "linear-enter",
            OperationSpecies::Construction,
            Vec::new(),
            vec![linear_input],
            None,
            vec![SourceTestimony::Undecided {
                question: "exact owner pending".to_owned(),
            }],
        )
        .unwrap();
    let linear_contract_law = operation
        .bind_operation(
            "linear-contract",
            OperationSpecies::Transport,
            vec![linear_input],
            vec![linear_output],
            Some("Q".to_owned()),
            vec![SourceTestimony::Undecided {
                question: "exact owner pending".to_owned(),
            }],
        )
        .unwrap();
    let quantity_enter_law = operation
        .bind_operation(
            "quantity-enter",
            OperationSpecies::Construction,
            Vec::new(),
            vec![quantity_input],
            None,
            vec![SourceTestimony::Undecided {
                question: "exact owner pending".to_owned(),
            }],
        )
        .unwrap();
    let quantity_contract_law = operation
        .bind_operation(
            "quantity-contract",
            OperationSpecies::Transport,
            vec![quantity_input],
            vec![quantity_output],
            Some("Q".to_owned()),
            vec![SourceTestimony::Undecided {
                question: "exact owner pending".to_owned(),
            }],
        )
        .unwrap();

    let linear_enter = operation.occur(linear_enter_law).unwrap();
    let linear_contract = operation.occur(linear_contract_law).unwrap();
    let quantity_enter = operation.occur(quantity_enter_law).unwrap();
    let quantity_contract = operation.occur(quantity_contract_law).unwrap();
    operation
        .carries_precedence(
            "linear standing enters",
            linear_input,
            holonic_engine::interaction::OccurrencePort::output(linear_enter, 0),
            holonic_engine::interaction::OccurrencePort::input(linear_contract, 0),
        )
        .unwrap();
    operation
        .carries_precedence(
            "quantity standing enters",
            quantity_input,
            holonic_engine::interaction::OccurrencePort::output(quantity_enter, 0),
            holonic_engine::interaction::OccurrencePort::input(quantity_contract, 0),
        )
        .unwrap();

    let base = BaseUnits::declare(["U"]).unwrap();
    let unit = base.unit("U").unwrap();
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
    let linear_input_typed = TypedMathematicalBoundary::coordinate_word(
        linear_input,
        "Q",
        vec![dimensionless.clone(), dimensionless.clone()],
        free_covariant.clone(),
    )
    .unwrap();
    let linear_output_typed = TypedMathematicalBoundary::new(
        linear_output,
        "Q",
        Some(dimensionless.clone()),
        free_covariant,
    )
    .unwrap();
    let quantity_input_typed = TypedMathematicalBoundary::coordinate_word(
        quantity_input,
        "Q",
        vec![unit.clone(), unit.clone(), unit.clone()],
        Vec::new(),
    )
    .unwrap();
    let quantity_output_typed = TypedMathematicalBoundary::new(
        quantity_output,
        "Q",
        Some(dimensionless.clone()),
        Vec::new(),
    )
    .unwrap();

    let zero_linear = ExactRatMatrix::new(vec![vec![integer(0), integer(0)]]).unwrap();
    let linear_matrix = ExactRatMatrix::new(vec![vec![integer(1), integer(-1)]]).unwrap();
    let linear_values = vec![integer(2), integer(2)];
    let linear_enter_license = ExactOwnerLicense::exact_linear(
        linear_enter_law,
        "linear-enter lineage",
        "enter",
        OperationSpecies::Construction,
        Vec::new(),
        vec![linear_input_typed.clone()],
        &zero_linear,
        &linear_values,
        BTreeMap::from([
            ("population".to_owned(), "linear-x".to_owned()),
            ("scale-significand".to_owned(), "1".to_owned()),
            ("scale-exponent".to_owned(), "0".to_owned()),
        ]),
    )
    .unwrap();
    let linear_contract_license = ExactOwnerLicense::exact_linear(
        linear_contract_law,
        "linear-contract lineage",
        "contract-tiled(apparatus tile)",
        OperationSpecies::Transport,
        vec![linear_input_typed.clone()],
        vec![linear_output_typed.clone()],
        &linear_matrix,
        &linear_values,
        BTreeMap::from([
            ("population".to_owned(), "linear-map".to_owned()),
            ("reduction-word".to_owned(), "Descending".to_owned()),
        ]),
    )
    .unwrap();

    let dimensions = DimensionMatrix::declare(
        base.clone(),
        vec![
            ("u0".to_owned(), unit.clone()),
            ("u1".to_owned(), unit.clone()),
            ("u2".to_owned(), unit.clone()),
        ],
    )
    .unwrap();
    let kernel_word = vec![integer(1), integer(1), integer(-2)];
    assert!(dimensions.buckingham().unwrap().contains(&kernel_word));
    let quantity_columns = BTreeMap::from([(quantity_input, vec![0, 1, 2])]);
    let quantity_enter_license = ExactOwnerLicense::quantity(
        quantity_enter_law,
        "quantity-enter lineage",
        "enter",
        OperationSpecies::Construction,
        Vec::new(),
        vec![quantity_input_typed.clone()],
        quantity_columns.clone(),
        &dimensions,
        &kernel_word,
        BTreeMap::from([
            ("population".to_owned(), "quantity-x".to_owned()),
            ("scale-significand".to_owned(), "1".to_owned()),
            ("scale-exponent".to_owned(), "0".to_owned()),
        ]),
    )
    .unwrap();
    let quantity_contract_license = ExactOwnerLicense::quantity(
        quantity_contract_law,
        "quantity-contract lineage",
        "contract-tiled(apparatus tile)",
        OperationSpecies::Transport,
        vec![quantity_input_typed.clone()],
        vec![quantity_output_typed.clone()],
        quantity_columns.clone(),
        &dimensions,
        &kernel_word,
        BTreeMap::from([
            ("population".to_owned(), "quantity-map".to_owned()),
            ("reduction-word".to_owned(), "Descending".to_owned()),
        ]),
    )
    .unwrap();

    let licenses = vec![
        linear_enter_license.clone(),
        linear_contract_license.clone(),
        quantity_enter_license.clone(),
        quantity_contract_license.clone(),
    ];
    let exact_owner = ExactOwnerOccurrence::new(licenses.clone()).unwrap();

    let linear_word = TypedOperationWord::found(
        "linear-word",
        vec![OperationWordStep {
            event: linear_contract,
            law: linear_contract_law,
            inputs: vec![linear_input],
            outputs: vec![linear_output],
        }],
        &operation,
    )
    .unwrap();
    let quantity_word = TypedOperationWord::found(
        "quantity-word",
        vec![OperationWordStep {
            event: quantity_contract,
            law: quantity_contract_law,
            inputs: vec![quantity_input],
            outputs: vec![quantity_output],
        }],
        &operation,
    )
    .unwrap();
    let source_addresses = BTreeSet::from([left.clone(), right.clone()]);
    let passage = TypedPassage::found(
        "shared-passage",
        BTreeMap::from([
            (PassageBranchId(0), source_addresses.clone()),
            (PassageBranchId(1), source_addresses.clone()),
        ]),
        BTreeMap::from([
            (
                PassageBranchId(0),
                TypedConstructionStep {
                    event: linear_enter,
                    law: linear_enter_law,
                    outputs: vec![linear_input],
                },
            ),
            (
                PassageBranchId(1),
                TypedConstructionStep {
                    event: quantity_enter,
                    law: quantity_enter_law,
                    outputs: vec![quantity_input],
                },
            ),
        ]),
        BTreeMap::from([
            (PassageBranchId(0), linear_word),
            (PassageBranchId(1), quantity_word),
        ]),
        &operation,
        &source_addresses,
    )
    .unwrap();

    let realized_linear_word = PortedWord::founded(
        "linear-realization",
        vec![PortedTransport::new(
            "linear-contract",
            linear_input,
            linear_output,
            "Q-chart",
            linear_matrix.clone(),
        )],
    )
    .unwrap();
    let linear_return = conduct_exact_linear(
        passage.reference(PassageBranchId(0)).unwrap(),
        &passage,
        &realized_linear_word,
        &BTreeMap::from([
            (linear_enter_law, zero_linear.clone()),
            (linear_contract_law, linear_matrix.clone()),
        ]),
        &BTreeMap::from([
            (linear_enter_law, linear_enter_license.clone()),
            (linear_contract_law, linear_contract_license.clone()),
        ]),
        &linear_values,
    )
    .unwrap();
    let quantity_return = conduct_exact_quantity(
        passage.reference(PassageBranchId(1)).unwrap(),
        &passage,
        dimensions.clone(),
        BTreeMap::from([
            (quantity_enter_law, quantity_columns.clone()),
            (quantity_contract_law, quantity_columns.clone()),
        ]),
        &BTreeMap::from([
            (quantity_enter_law, quantity_enter_license.clone()),
            (quantity_contract_law, quantity_contract_license.clone()),
        ]),
        vec![
            Quantity::integer(2, unit.clone()),
            Quantity::integer(3, unit.clone()),
            Quantity::integer(6, unit.clone()),
        ],
    )
    .unwrap();
    assert!(quantity_return.returned().dimension().is_dimensionless());

    let presentation_fibres = vec![PresentationFiberOccurrence {
        occurrence: "presentation-fibre".to_owned(),
        fibre: presentation_fibre,
    }];
    let open_fibres = vec![OpenParticleFiber {
        occurrence: "open-fibre".to_owned(),
        question: "which source-layout candidate elaborates".to_owned(),
        candidates: BTreeSet::from(["proposal-a".to_owned(), "proposal-b".to_owned()]),
        would_be_decided_by: BTreeSet::from(["held-out receiver".to_owned()]),
    }];
    let selection = PassageSelection::posed(
        "shared-passage",
        BTreeSet::from([PassageBranchId(0), PassageBranchId(1)]),
    );
    let (accepted_proposal, no_refusal) = ParticleProposal::from_exact_owner_result(
        "proposal-a",
        selection.clone(),
        Ok(licenses.clone()),
    );
    assert!(no_refusal.is_none());

    let refused_dimensions = DimensionMatrix::declare(
        base.clone(),
        vec![
            ("u0".to_owned(), unit.clone()),
            ("u1".to_owned(), unit.clone()),
            ("u2".to_owned(), dimensionless.clone()),
        ],
    )
    .unwrap();
    let refused_attempt = ExactOwnerLicense::quantity(
        quantity_contract_law,
        "quantity-contract-refused",
        "contract-tiled(apparatus tile)",
        OperationSpecies::Transport,
        vec![quantity_input_typed.clone()],
        vec![quantity_output_typed.clone()],
        quantity_columns.clone(),
        &refused_dimensions,
        &kernel_word,
        BTreeMap::new(),
    )
    .map(|license| vec![license]);
    let (refused_proposal, refusal) =
        ParticleProposal::from_exact_owner_result("proposal-b", selection.clone(), refused_attempt);
    let refusal = refusal.unwrap();
    let open_proposal = ParticleProposal::open("proposal-open", selection.clone(), "open-fibre");

    let value_receiver = ValueReceiverReturn::found(
        "value-receiver",
        linear_output,
        BTreeSet::from([left.clone()]),
        linear_return.terminal_value_face().to_vec(),
    )
    .unwrap();
    let rendering_receiver = RenderingReceiverReturn::found(
        "render-receiver",
        quantity_output,
        BTreeSet::from([right.clone()]),
        "source-left",
    )
    .unwrap();
    let classification_receiver = ClassificationReceiverReturn::found(
        "classification-receiver",
        BTreeMap::from([
            (left.clone(), b"harmonic".to_vec()),
            (right.clone(), b"harmonic".to_vec()),
        ]),
    )
    .unwrap();
    let similarity_receiver = SimilarityReceiverReturn::found(
        "similarity-receiver",
        "projective-frame",
        BTreeMap::from([
            (
                left.clone(),
                BTreeMap::from([("cross-ratio".to_owned(), b"-1".to_vec())]),
            ),
            (
                right.clone(),
                BTreeMap::from([("cross-ratio".to_owned(), b"-1".to_vec())]),
            ),
        ]),
    )
    .unwrap();
    let quantity_matrix = dimensions.as_exact_matrix().unwrap();
    let passage_receipt = card_deed_receipt(
        &operation,
        &exact_owner,
        linear_enter,
        linear_contract,
        quantity_enter,
        quantity_contract,
        &linear_matrix,
        &quantity_matrix,
    )?;
    let history_return = ReceiverHistoryReturn::open_from_exact_deed(
        "history-receiver",
        &left,
        &right,
        &passage_receipt,
    )
    .unwrap();

    let evidence = BTreeSet::from([
        left.clone(),
        right.clone(),
        "particle-occurrence".to_owned(),
        "shared-passage".to_owned(),
        "linear-word".to_owned(),
        "quantity-word".to_owned(),
        "presentation-fibre".to_owned(),
        "open-fibre".to_owned(),
        "value-receiver".to_owned(),
        "render-receiver".to_owned(),
        "classification-receiver".to_owned(),
        "similarity-receiver".to_owned(),
        "history-receiver".to_owned(),
    ]);
    let relation_evidence =
        RelationWitness::established(BTreeSet::from(["shared-passage".to_owned()]));
    let interactions = operation
        .shape
        .interactions
        .keys()
        .map(|interaction| (*interaction, *interaction))
        .collect();
    let marked = MarkedDiagramRelation::found(
        BTreeMap::from([(left.clone(), right.clone()), (right.clone(), left.clone())]),
        [linear_input, linear_output, quantity_input, quantity_output]
            .into_iter()
            .map(|port| (port, port))
            .collect(),
        [
            linear_enter_law,
            linear_contract_law,
            quantity_enter_law,
            quantity_contract_law,
        ]
        .into_iter()
        .map(|law| (law, law))
        .collect(),
        [
            linear_enter,
            linear_contract,
            quantity_enter,
            quantity_contract,
        ]
        .into_iter()
        .map(|event| (event, event))
        .collect(),
        interactions,
        BTreeMap::from([
            ("linear-word".to_owned(), "linear-word".to_owned()),
            ("quantity-word".to_owned(), "quantity-word".to_owned()),
        ]),
        BTreeMap::from([
            (
                "presentation-fibre".to_owned(),
                "presentation-fibre".to_owned(),
            ),
            ("open-fibre".to_owned(), "open-fibre".to_owned()),
        ]),
        relation_evidence.clone(),
        &evidence,
        &source_addresses,
        &operation,
        std::slice::from_ref(&passage),
        &presentation_fibres,
        &open_fibres,
    )
    .unwrap();

    let identity = ExactRatMatrix::identity(1).unwrap();
    let doctrine = DoctrineEquivalenceRelation::from_transports(
        PortedTransport::new(
            "forward",
            linear_output,
            linear_output,
            "doctrine",
            identity.clone(),
        ),
        PortedTransport::new(
            "reverse",
            linear_output,
            linear_output,
            "doctrine",
            identity,
        ),
        relation_evidence.clone(),
    )
    .unwrap();
    let history_relation =
        ReceiverHistoryRelation::from_return(&left, &right, &history_return).unwrap();
    let receiver_face = ReceiverFaceRelation::from_return(&value_receiver, 0, 0).unwrap();
    let classification =
        ClassificationRelation::from_return(&classification_receiver, &left, &right).unwrap();
    let similarity = SimilarityRelation::from_return(&similarity_receiver, &left, &right).unwrap();
    let carrier_ids = BTreeSet::from([CarrierId(1)]);
    let sameness = TypedSamenessFamily::found(
        OccurrenceRelation {
            left: left.clone(),
            right: right.clone(),
            witness: RelationWitness::separated("shared-passage"),
        },
        vec![CarrierEqualityRelation::compare(
            CarrierId(1),
            CarrierId(1),
            ExactValue::rational(integer(1)),
            ExactValue::rational(integer(1)),
            relation_evidence.clone(),
        )],
        marked,
        doctrine,
        history_relation,
        vec![receiver_face],
        classification,
        similarity,
        PresentationRelation {
            chart_occurrence: "shared-passage".to_owned(),
            left: left_box,
            right: right_box,
            witness: relation_evidence.clone(),
        },
        ByteRelation {
            codec_occurrence: "shared-passage".to_owned(),
            left: b"mu".to_vec(),
            right: b"mu".to_vec(),
            witness: relation_evidence.clone(),
        },
        DigestRelation::sha256(b"mu", b"mu", relation_evidence),
        "particle-occurrence",
        &source_addresses,
        &carrier_ids,
        &operation,
        std::slice::from_ref(&passage),
        &presentation_fibres,
        &open_fibres,
        std::slice::from_ref(&value_receiver),
        std::slice::from_ref(&classification_receiver),
        std::slice::from_ref(&similarity_receiver),
        std::slice::from_ref(&history_return),
    )
    .unwrap();

    Ok(MathematicalParticleInput {
        occurrence: "particle-occurrence".to_owned(),
        source_testimonies: vec![left_source, right_source],
        exterior_artifacts: Vec::new(),
        presentation_fibres,
        operation,
        carriers: vec![CarrierOccurrence {
            id: CarrierId(1),
            source_occurrences: BTreeSet::from([left.clone()]),
            owner_carrier: "Q".to_owned(),
            equality_law_lineage: "exact rational equality".to_owned(),
        }],
        binders: vec![
            BinderScope {
                id: BinderId(10),
                source_occurrences: BTreeSet::from([left.clone()]),
                ports: BTreeSet::from([linear_input, linear_output]),
                laws: BTreeSet::from([linear_enter_law, linear_contract_law]),
            },
            BinderScope {
                id: BinderId(11),
                source_occurrences: BTreeSet::from([right.clone()]),
                ports: BTreeSet::from([linear_input, linear_output]),
                laws: BTreeSet::from([linear_enter_law, linear_contract_law]),
            },
        ],
        ports: vec![
            TypedPort {
                boundary: linear_input_typed,
                carrier: CarrierId(1),
                unit_frame: Vec::new(),
                exposed: true,
            },
            TypedPort {
                boundary: linear_output_typed,
                carrier: CarrierId(1),
                unit_frame: Vec::new(),
                exposed: true,
            },
            TypedPort {
                boundary: quantity_input_typed,
                carrier: CarrierId(1),
                unit_frame: Vec::new(),
                exposed: true,
            },
            TypedPort {
                boundary: quantity_output_typed,
                carrier: CarrierId(1),
                unit_frame: Vec::new(),
                exposed: true,
            },
        ],
        operations: operation_typing(&[
            (linear_enter_law, 0, 1),
            (linear_contract_law, 1, 1),
            (quantity_enter_law, 0, 1),
            (quantity_contract_law, 1, 1),
        ]),
        hypotheses: vec![HypothesisLicense {
            id: HypothesisId(1),
            source_occurrences: BTreeSet::from([left.clone()]),
            licenses: BTreeSet::from([
                linear_enter_law,
                linear_contract_law,
                quantity_enter_law,
                quantity_contract_law,
            ]),
            branches: BTreeSet::from([BranchId(1)]),
        }],
        passages: vec![passage],
        branches: vec![AnalyticBranch {
            id: BranchId(1),
            passage: selection,
            hypotheses: BTreeSet::from([HypothesisId(1)]),
        }],
        linear_returns: vec![linear_return],
        quantity_returns: vec![quantity_return],
        value_receivers: vec![value_receiver],
        rendering_receivers: vec![rendering_receiver],
        classification_receivers: vec![classification_receiver],
        similarity_receivers: vec![similarity_receiver],
        receiver_history_returns: vec![history_return],
        sameness: vec![sameness],
        proposals: vec![accepted_proposal, refused_proposal, open_proposal],
        refusals: vec![refusal],
        open_fibres,
        admission: ParticleAdmissionInput {
            proposal: "proposal-a".to_owned(),
            typing_occurrence: "shared-passage".to_owned(),
            exact_owner,
            passage_receipt: Some(passage_receipt),
        },
    })
}
#[test]
fn a_particle_owns_m0_typing_two_exact_returns_and_each_sameness_relation() {
    let input = fixture().expect("required M1 GPU fixture must return");
    let particle = MathematicalParticle::found(input).unwrap();
    assert_eq!(particle.source_testimonies().len(), 2);
    assert_eq!(particle.linear_returns().len(), 1);
    assert_eq!(particle.quantity_returns().len(), 1);
    assert_eq!(particle.admission().bindings().len(), 4);
    let deed = particle.admission().passage_receipt();
    let selected_events = deed
        .entailed_occurrences()
        .keys()
        .copied()
        .collect::<BTreeSet<_>>();
    assert!(!deed.operation_complex_identity().is_empty());
    assert!(!deed.selected_subcomplex_identity().is_empty());
    assert!(deed.matches_complex_and_selection(particle.operation(), &selected_events));
    assert!(particle.passages()[0].staging_front_depth() < particle.passages()[0].front_depth());
    assert_eq!(particle.passages()[0].staging().len(), 2);
    let slots = particle.ports()[0].boundary.tensor_slots();
    assert_eq!(slots.len(), 2);
    assert!(slots.iter().all(|slot| {
        slot.variance == TensorVariance::Covariant && slot.role == TensorSlotRole::Free
    }));
}

#[test]
fn a_foreign_source_cannot_type_a_binder() {
    let mut input = fixture().expect("required M1 GPU fixture must return");
    input.binders[0].source_occurrences = BTreeSet::from(["foreign".to_owned()]);
    assert!(matches!(
        MathematicalParticle::found(input),
        Err(MathematicalParticleError::UnknownSourceOccurrence(_))
    ));
}

#[test]
fn a_bare_diagram_assertion_cannot_replace_the_bijections() {
    let input = fixture().expect("required M1 GPU fixture must return");
    let source_addresses = input
        .source_testimonies
        .iter()
        .flat_map(|testimony| {
            testimony
                .occurrences
                .iter()
                .map(|occurrence| occurrence.address.clone())
        })
        .collect::<BTreeSet<_>>();
    let attempted = MarkedDiagramRelation::found(
        BTreeMap::new(),
        BTreeMap::new(),
        BTreeMap::new(),
        BTreeMap::new(),
        BTreeMap::new(),
        BTreeMap::new(),
        BTreeMap::new(),
        RelationWitness::established(BTreeSet::from(["shared-passage".to_owned()])),
        &BTreeSet::from(["shared-passage".to_owned()]),
        &source_addresses,
        &input.operation,
        &input.passages,
        &input.presentation_fibres,
        &input.open_fibres,
    );
    assert!(matches!(
        attempted,
        Err(MathematicalParticleError::MalformedRelation(
            "marked-diagram-isomorphism"
        ))
    ));
}

#[test]
fn accepted_typing_must_name_a_real_proposal_and_the_shared_passage() {
    let mut input = fixture().expect("required M1 GPU fixture must return");
    input.admission.proposal = "absent-proposal".to_owned();
    assert!(matches!(
        MathematicalParticle::found(input),
        Err(MathematicalParticleError::AdmissionNotCausallyLinked)
    ));
}

#[test]
fn proposal_renaming_moves_no_typed_passage_or_licensed_law() {
    let mut input = fixture().expect("required M1 GPU fixture must return");
    input.proposals[0].occurrence = "renamed-proposal".to_owned();
    input.admission.proposal = "renamed-proposal".to_owned();
    input.open_fibres[0].candidates =
        BTreeSet::from(["renamed-proposal".to_owned(), "proposal-b".to_owned()]);
    let particle = MathematicalParticle::found(input).unwrap();
    assert_eq!(particle.admission().proposal(), "renamed-proposal");
    assert_eq!(particle.admission().bindings().len(), 4);
}

#[test]
fn a_refusal_must_equal_the_exact_owner_attempt_return() {
    let mut input = fixture().expect("required M1 GPU fixture must return");
    input.proposals[1].owner_attempt = ProposalOwnerAttempt::ExactOwnerRefused(
        ExactOwnerWitnessRefusal::ExactLinearResidualNonzero {
            residual: vec![integer(1)],
        },
    );
    assert!(matches!(
        MathematicalParticle::found(input),
        Err(MathematicalParticleError::MalformedRefusal(_))
    ));
}

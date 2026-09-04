//! Proposal adjudication and the fixed, non-vacuous M1 sameness family.

use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::Path;

use holonic_engine::exact_linear::ExactRatMatrix;
use holonic_engine::exact_value::ExactValue;
use holonic_engine::ported_operation::PortedTransport;
use life::mathematical_particle::{
    ByteRelation, CarrierEqualityRelation, CarrierId, ClassificationReceiverReturn,
    ClassificationRelation, DigestRelation, DoctrineEquivalenceRelation, MarkedDiagramRelation,
    OccurrenceRelation, OpenParticleFiber, ParticleProposal, ParticleRefusal, PassageBranchId,
    PassageSelection, PresentationFiberOccurrence, PresentationRelation, ReceiverFaceRelation,
    ReceiverHistoryRelation, ReceiverHistoryReturn, RelationWitness, RenderingReceiverReturn,
    SimilarityReceiverReturn, SimilarityRelation, TypedSamenessFamily, ValueReceiverReturn,
};
use num_bigint::BigInt;
use num_rational::BigRational as Rat;

use super::particle::{ProposalReceipt, SamenessReceipt};
use super::particle_typing::OperationAssembly;
use super::source_material::RemountedM0;

pub struct RelationAssembly {
    pub presentation_fibres: Vec<PresentationFiberOccurrence>,
    pub open_fibres: Vec<OpenParticleFiber>,
    pub selection: PassageSelection,
    pub proposals: Vec<ParticleProposal>,
    pub proposal_receipts: Vec<ProposalReceipt>,
    pub refusal: ParticleRefusal,
    pub value_receiver: ValueReceiverReturn,
    pub rendering_receiver: RenderingReceiverReturn,
    pub classification_receiver: ClassificationReceiverReturn,
    pub similarity_receiver: SimilarityReceiverReturn,
    pub history_return: ReceiverHistoryReturn,
    pub sameness: TypedSamenessFamily,
    pub sameness_receipt: SamenessReceipt,
}

pub fn construct(
    root: &Path,
    remounted: &mut RemountedM0,
    all_sources: &BTreeSet<String>,
    affine_sources: &BTreeSet<String>,
    heat_sources: &BTreeSet<String>,
    affine_anchor_ordinal: usize,
    operation: &OperationAssembly,
) -> Result<RelationAssembly, String> {
    let passage = &operation.passage;
    let left = remounted.baseline.occurrences[affine_anchor_ordinal]
        .address
        .clone();
    let right = remounted.reflow.occurrences[affine_anchor_ordinal]
        .address
        .clone();
    let returned_values = operation.affine_return.terminal_value_face();
    if returned_values.len() != 4 {
        return Err("the affine presentation/rebase square did not return four faces".to_owned());
    }
    let value_receiver = ValueReceiverReturn::found(
        "m1-value-receiver",
        operation.ports.affine_out,
        affine_sources.clone(),
        returned_values.to_vec(),
    )
    .map_err(debug)?;
    let rendering_receiver = RenderingReceiverReturn::found(
        "m1-rendering-receiver",
        operation.ports.heat_out,
        heat_sources.clone(),
        remounted.natural_page5_vector.occurrence.clone(),
    )
    .map_err(debug)?;
    let rendering_artifact_occurrence = rendering_receiver.artifact_occurrence().to_owned();
    let classification_classes = BTreeMap::from([
        (left.clone(), exact_value_bytes(&returned_values[0])?),
        (right.clone(), exact_value_bytes(&returned_values[1])?),
    ]);
    let classification_receiver = ClassificationReceiverReturn::found(
        "m1-classification-receiver",
        classification_classes.clone(),
    )
    .map_err(debug)?;
    let input_arity = operation
        .boundaries
        .affine_input
        .dimensions()
        .len()
        .to_string()
        .into_bytes();
    let step_arity = passage
        .branch(PassageBranchId(0))
        .ok_or_else(|| "the affine passage branch disappeared".to_owned())?
        .steps
        .len()
        .to_string()
        .into_bytes();
    let characteristics = |value: &ExactValue| -> Result<_, String> {
        Ok(BTreeMap::from([
            ("input-coordinate-arity".to_owned(), input_arity.clone()),
            (
                "ordered-transport-step-arity".to_owned(),
                step_arity.clone(),
            ),
            ("returned-exact-value".to_owned(), exact_value_bytes(value)?),
        ]))
    };
    let similarity_characteristics = BTreeMap::from([
        (left.clone(), characteristics(&returned_values[0])?),
        (right.clone(), characteristics(&returned_values[1])?),
    ]);
    let similarity_receiver = SimilarityReceiverReturn::found(
        "m1-similarity-receiver",
        "exact-return-characteristics",
        similarity_characteristics.clone(),
    )
    .map_err(debug)?;
    let history_return = ReceiverHistoryReturn::open_from_exact_deed(
        "m1-receiver-history",
        &left,
        &right,
        &operation.resident.receipt,
    )
    .map_err(debug)?;
    let open_fibres = vec![
        OpenParticleFiber {
            occurrence: "natural-untyped-contraction-open".to_owned(),
            question: "which typed contraction, if any, may bind the natural tensor slots"
                .to_owned(),
            candidates: BTreeSet::from([
                "retain-mu-nu-free".to_owned(),
                "contract-under-an-independent-metric".to_owned(),
            ]),
            would_be_decided_by: BTreeSet::from([
                "an independently admitted contraction typing and metric".to_owned(),
            ]),
        },
        OpenParticleFiber {
            occurrence: "rigidity-coefficient-standing-open".to_owned(),
            question: "the exterior rigidity proposal has no typed coefficient-tensor standing"
                .to_owned(),
            candidates: BTreeSet::from([
                "operator-posed finite equilibrium with free mu".to_owned(),
                "operator-posed all-ones negative control".to_owned(),
                "operator-posed flipped-stress negative control".to_owned(),
            ]),
            would_be_decided_by: BTreeSet::from([
                "a future addressed coefficient-tensor owner and slot typing".to_owned(),
            ]),
        },
    ];
    let presentation_fibres = vec![PresentationFiberOccurrence {
        occurrence: "m0-baseline-reflow-fibre".to_owned(),
        fibre: remounted
            .presentation
            .take()
            .ok_or_else(|| "the M0 presentation fibre was already consumed".to_owned())?,
    }];
    let selection = PassageSelection::posed(
        passage.occurrence(),
        BTreeSet::from([PassageBranchId(0), PassageBranchId(1), PassageBranchId(2)]),
    );
    let (accepted, unexpected_refusal) = ParticleProposal::from_exact_owner_result(
        "addressed-three-branch-proposal",
        selection.clone(),
        Ok(operation.licenses.clone()),
    );
    if unexpected_refusal.is_some() {
        return Err("the licensed proposal unexpectedly returned a refusal".to_owned());
    }
    let (refused, refusal) = ParticleProposal::from_exact_owner_result(
        "dimension-refusal-proposal",
        selection.clone(),
        operation.refused_attempt.clone(),
    );
    let refusal = refusal.ok_or_else(|| "the changed unit frame did not refuse".to_owned())?;
    let natural_open = ParticleProposal::open(
        "natural-untyped-contraction-proposal",
        selection.clone(),
        "natural-untyped-contraction-open",
    );
    let rigidity_open = ParticleProposal::open(
        "rigidity-lineage-only-proposal",
        selection.clone(),
        "rigidity-coefficient-standing-open",
    );
    let branches = selection
        .branches()
        .iter()
        .map(|branch| branch.0)
        .collect::<Vec<_>>();
    let accepted_evidence = operation
        .licenses
        .iter()
        .map(|license| {
            (
                license.constraint().law().0,
                license.evidence_sha256().to_owned(),
            )
        })
        .collect();
    let proposal_receipts = vec![
        proposal_receipt(&accepted, &branches, "licensed", accepted_evidence, None),
        proposal_receipt(
            &refused,
            &branches,
            "exact-owner-refused",
            BTreeMap::new(),
            Some(format!("{:?}", refusal.obstruction())),
        ),
        proposal_receipt(
            &natural_open,
            &branches,
            "open",
            BTreeMap::new(),
            Some("natural-untyped-contraction-open".to_owned()),
        ),
        proposal_receipt(
            &rigidity_open,
            &branches,
            "open-lineage-only",
            BTreeMap::new(),
            Some("rigidity-coefficient-standing-open".to_owned()),
        ),
    ];

    let relation_evidence =
        RelationWitness::established(BTreeSet::from([passage.occurrence().to_owned()]));
    let mut evidence = all_sources.clone();
    evidence.extend([
        "m1-particle".to_owned(),
        passage.occurrence().to_owned(),
        "affine-word".to_owned(),
        "heat-word".to_owned(),
        "quantity-word".to_owned(),
        "m0-baseline-reflow-fibre".to_owned(),
        "natural-untyped-contraction-open".to_owned(),
        "rigidity-coefficient-standing-open".to_owned(),
        "m1-value-receiver".to_owned(),
        "m1-rendering-receiver".to_owned(),
        "m1-classification-receiver".to_owned(),
        "m1-similarity-receiver".to_owned(),
        "m1-receiver-history".to_owned(),
    ]);
    let mut source_mark_map = all_sources
        .iter()
        .cloned()
        .map(|source| (source.clone(), source))
        .collect::<BTreeMap<_, _>>();
    for (baseline, reflow) in remounted
        .baseline
        .occurrences
        .iter()
        .zip(&remounted.reflow.occurrences)
    {
        source_mark_map.insert(baseline.address.clone(), reflow.address.clone());
        source_mark_map.insert(reflow.address.clone(), baseline.address.clone());
    }
    let marked = MarkedDiagramRelation::found(
        source_mark_map.clone(),
        operation
            .operation
            .shape
            .boundaries
            .objects
            .keys()
            .map(|port| (*port, *port))
            .collect(),
        operation
            .operation
            .shape
            .laws
            .keys()
            .map(|law| (*law, *law))
            .collect(),
        operation
            .operation
            .shape
            .occurrences
            .keys()
            .map(|event| (*event, *event))
            .collect(),
        operation
            .operation
            .shape
            .interactions
            .keys()
            .map(|id| (*id, *id))
            .collect(),
        passage
            .branches()
            .values()
            .map(|word| (word.occurrence.clone(), word.occurrence.clone()))
            .collect(),
        open_fibres
            .iter()
            .map(|fibre| (fibre.occurrence.clone(), fibre.occurrence.clone()))
            .chain(
                presentation_fibres
                    .iter()
                    .map(|fibre| (fibre.occurrence.clone(), fibre.occurrence.clone())),
            )
            .collect(),
        relation_evidence.clone(),
        &evidence,
        all_sources,
        &operation.operation,
        std::slice::from_ref(passage),
        &presentation_fibres,
        &open_fibres,
    )
    .map_err(debug)?;
    let rebase = ExactRatMatrix::new(vec![
        vec![integer(0), integer(1), integer(0)],
        vec![integer(1), integer(0), integer(0)],
        vec![integer(0), integer(0), integer(1)],
    ])
    .map_err(|error| error.to_string())?;
    let standing = &operation.affine_standing;
    if standing.len() != 12
        || rebase
            .apply(&standing[0..3])
            .map_err(|error| error.to_string())?
            != standing[6..9]
        || rebase
            .apply(&standing[3..6])
            .map_err(|error| error.to_string())?
            != standing[9..12]
        || rebase
            .multiply(&rebase)
            .map_err(|error| error.to_string())?
            != ExactRatMatrix::identity(3).map_err(|error| error.to_string())?
    {
        return Err("the affine presentation/rebase square does not commute".to_owned());
    }
    let doctrine = DoctrineEquivalenceRelation::from_transports(
        PortedTransport::new(
            "swap-affine-A-A-prime-forward",
            operation.ports.affine_in,
            operation.ports.affine_in,
            "affine-input-chart",
            rebase.clone(),
        ),
        PortedTransport::new(
            "swap-affine-A-A-prime-reverse",
            operation.ports.affine_in,
            operation.ports.affine_in,
            "affine-input-chart",
            rebase.clone(),
        ),
        relation_evidence.clone(),
    )
    .map_err(debug)?;
    let history_relation =
        ReceiverHistoryRelation::from_return(&left, &right, &history_return).map_err(debug)?;
    let history_witness = history_relation.witness().clone();
    let baseline_bytes = fs::read(root.join(&remounted.baseline.artifact.locator))
        .map_err(|error| error.to_string())?;
    let reflow_bytes = fs::read(root.join(&remounted.reflow.artifact.locator))
        .map_err(|error| error.to_string())?;
    let sameness = TypedSamenessFamily::found(
        OccurrenceRelation {
            left: left.clone(),
            right: right.clone(),
            witness: RelationWitness::separated(passage.occurrence()),
        },
        vec![CarrierEqualityRelation::compare(
            CarrierId(1),
            CarrierId(1),
            returned_values[0].clone(),
            returned_values[1].clone(),
            relation_evidence.clone(),
        )],
        marked,
        doctrine,
        history_relation,
        vec![ReceiverFaceRelation::from_return(&value_receiver, 0, 1).map_err(debug)?],
        ClassificationRelation::from_return(&classification_receiver, &left, &right)
            .map_err(debug)?,
        SimilarityRelation::from_return(&similarity_receiver, &left, &right).map_err(debug)?,
        PresentationRelation {
            chart_occurrence: passage.occurrence().to_owned(),
            left: remounted.baseline.occurrences[affine_anchor_ordinal]
                .bounds
                .clone(),
            right: remounted.reflow.occurrences[affine_anchor_ordinal]
                .bounds
                .clone(),
            witness: RelationWitness::separated(passage.occurrence()),
        },
        ByteRelation {
            codec_occurrence: passage.occurrence().to_owned(),
            left: baseline_bytes.clone(),
            right: reflow_bytes.clone(),
            witness: RelationWitness::separated(passage.occurrence()),
        },
        DigestRelation::sha256(
            &baseline_bytes,
            &reflow_bytes,
            RelationWitness::separated(passage.occurrence()),
        ),
        "m1-particle",
        all_sources,
        &BTreeSet::from([CarrierId(1)]),
        &operation.operation,
        std::slice::from_ref(passage),
        &presentation_fibres,
        &open_fibres,
        std::slice::from_ref(&value_receiver),
        std::slice::from_ref(&classification_receiver),
        std::slice::from_ref(&similarity_receiver),
        std::slice::from_ref(&history_return),
    )
    .map_err(debug)?;
    Ok(RelationAssembly {
        presentation_fibres,
        open_fibres,
        selection,
        proposals: vec![accepted, refused, natural_open, rigidity_open],
        proposal_receipts,
        refusal,
        value_receiver,
        rendering_receiver,
        classification_receiver,
        similarity_receiver,
        history_return,
        sameness,
        sameness_receipt: SamenessReceipt {
            left_occurrence: left,
            right_occurrence: right,
            source_mark_map,
            doctrine_forward: rebase.clone(),
            doctrine_reverse: rebase,
            receiver_indices: [0, 1],
            classification_classes,
            similarity_characteristics,
            history_witness,
            rendering_artifact_occurrence,
        },
    })
}

fn proposal_receipt(
    proposal: &ParticleProposal,
    branches: &[u64],
    attempt: &str,
    owner_evidence: BTreeMap<u64, String>,
    obstruction: Option<String>,
) -> ProposalReceipt {
    ProposalReceipt {
        occurrence: proposal.occurrence().to_owned(),
        passage: proposal.passage().passage().to_owned(),
        branches: branches.to_vec(),
        attempt: attempt.to_owned(),
        owner_evidence,
        obstruction,
    }
}

fn exact_value_bytes(value: &ExactValue) -> Result<Vec<u8>, String> {
    serde_json::to_vec(value).map_err(|error| error.to_string())
}

fn integer(value: i64) -> Rat {
    Rat::from_integer(BigInt::from(value))
}

fn debug(error: impl std::fmt::Debug) -> String {
    format!("{error:?}")
}

use std::collections::BTreeMap;

use holonic_engine::corpus_census::{LexicalSpecies, Stratum, StratumDeclaration};
use holonic_engine::diffusion::{DiffusionBranch, DiffusionComplex, DiffusionNode};
use holonic_engine::{CurrentBranchId, CurrentNodeId};
use relational_geometry::integer;

use super::*;

const STRATA: [StratumDeclaration; 1] = [StratumDeclaration {
    stratum: Stratum(0),
    label: "experiment",
    relative_root: "",
    extension: "",
    recursive: false,
}];

fn census() -> CorpusCensus {
    let mut census = CorpusCensus::declaring(&STRATA, LexicalSpecies::Prose).unwrap();
    census.admit_whole(Stratum(0), "broken".to_owned(), "left vectro right");
    census.admit_whole(Stratum(0), "standing".to_owned(), "left vector right");
    census.admit_whole(Stratum(0), "other".to_owned(), "up tensor down");
    census.admit_whole(Stratum(0), "comma".to_owned(), "alpha , beta");
    census.admit_whole(Stratum(0), "bang".to_owned(), "alpha ! beta");
    census
}

fn address(census: &CorpusCensus, surface: &str) -> OccurrenceAddress {
    let id = census.lookup(surface).unwrap();
    for (whole, record) in census.wholes().iter().enumerate() {
        if let Some(position) = record.stream.iter().position(|standing| *standing == id) {
            return OccurrenceAddress {
                whole: whole as u32,
                position: position as u32,
                surface: id,
            };
        }
    }
    panic!("surface has an occurrence")
}

fn declaration(census: &CorpusCensus, family: ReceiverFamily) -> ReconstructionDeclaration {
    ReconstructionDeclaration {
        candidates: CandidatePopulation::Declared(BTreeSet::from([
            census.lookup("vectro").unwrap(),
            census.lookup("vector").unwrap(),
            census.lookup("tensor").unwrap(),
        ])),
        family,
        horizon: 1,
    }
}

fn run(
    census: &CorpusCensus,
    focus: OccurrenceAddress,
    declaration: &ReconstructionDeclaration,
) -> ReconstructionPassage {
    let atlas = ConductAtlas::found(census, 1);
    let demand = reconstruction_demand(census, focus, declaration).unwrap();
    reconstruct(
        census,
        &atlas,
        focus,
        declaration,
        &ReconstructionWorkCover::exactly(&demand),
        None,
    )
    .unwrap()
}

#[test]
fn context_refines_the_fiber_without_selecting_by_edit_grade() {
    let census = census();
    let focus = address(&census, "vectro");
    let coarse = run(
        &census,
        focus,
        &declaration(&census, ReceiverFamily::of([ReceiverAxis::Kind])),
    );
    assert_eq!(coarse.fiber.focus_candidates.len(), 3);
    assert!(coarse
        .fiber
        .focus_candidates
        .contains(&census.lookup("tensor").unwrap()));

    let richer = run(
        &census,
        focus,
        &declaration(
            &census,
            ReceiverFamily::of([ReceiverAxis::Kind, ReceiverAxis::Weight]),
        ),
    );
    assert_eq!(
        richer.fiber.focus_candidates,
        BTreeSet::from([
            census.lookup("vectro").unwrap(),
            census.lookup("vector").unwrap(),
        ])
    );
    assert_eq!(
        richer.fiber.edits[&census.lookup("vector").unwrap()].minimum_operations,
        1
    );
    assert_eq!(
        richer.fiber.edits[&census.lookup("tensor").unwrap()].minimum_operations,
        4
    );
}

#[test]
fn punctuation_occurrences_are_focal_roots_without_entering_the_word_population() {
    let census = census();
    let comma = address(&census, ",");
    let before_words = census.word_surfaces();
    let declaration = ReconstructionDeclaration {
        candidates: CandidatePopulation::Declared(BTreeSet::from([
            census.lookup(",").unwrap(),
            census.lookup("!").unwrap(),
        ])),
        family: ReceiverFamily::of([ReceiverAxis::Kind, ReceiverAxis::Weight]),
        horizon: 1,
    };
    let passage = run(&census, comma, &declaration);
    assert_eq!(passage.fiber.focus_candidates.len(), 2);
    assert_eq!(census.word_surfaces(), before_words);
    assert!(passage.fiber.focus_support.iter().all(|root| {
        root.surface == census.lookup(",").unwrap() || root.surface == census.lookup("!").unwrap()
    }));
}

#[test]
fn the_edit_dag_retains_all_minimal_routes_and_typed_rebases() {
    let deletion = edit_complex("aa", "a");
    assert_eq!(deletion.minimum_operations, 1);
    assert_eq!(deletion.minimal_path_count, BigUint::from(2u8));

    let transpose = edit_complex("matrix", "matirx");
    assert_eq!(transpose.minimum_operations, 1);
    assert!(transpose
        .edges
        .iter()
        .any(|edge| matches!(edge.operation, EditOperation::AdjacentTranspose { .. })));

    let case = edit_complex("Vector", "vector");
    assert_eq!(case.minimum_operations, 1);
    assert!(case
        .edges
        .iter()
        .any(|edge| matches!(edge.operation, EditOperation::CaseRebase { .. })));
}

#[test]
fn a_richer_rereading_deposits_the_departed_population_and_witness() {
    let census = census();
    let focus = address(&census, "vectro");
    let coarse = run(
        &census,
        focus,
        &declaration(&census, ReceiverFamily::of([ReceiverAxis::Kind])),
    );
    let richer = run(
        &census,
        focus,
        &declaration(
            &census,
            ReceiverFamily::of([ReceiverAxis::Kind, ReceiverAxis::Weight]),
        ),
    );
    let mut body = ReconstructionBody::new();
    let first = body.found(coarse).unwrap();
    let receipt = body.reflect(first, richer).unwrap();
    assert_eq!(
        receipt.departed,
        BTreeSet::from([census.lookup("tensor").unwrap()])
    );
    assert!(!receipt.separating_witnesses.is_empty());
    assert!(body.passage(receipt.successor).is_some());
}

#[test]
fn diffusion_returns_exactly_beside_and_cannot_change_the_fiber() {
    let census = census();
    let focus = address(&census, "vectro");
    let declaration = declaration(
        &census,
        ReceiverFamily::of([ReceiverAxis::Kind, ReceiverAxis::Weight]),
    );
    let atlas = ConductAtlas::found(&census, 1);
    let demand = reconstruction_demand(&census, focus, &declaration).unwrap();
    let cover = ReconstructionWorkCover::exactly(&demand);
    let without = reconstruct(&census, &atlas, focus, &declaration, &cover, None).unwrap();

    let left = CurrentNodeId(1);
    let right = CurrentNodeId(2);
    let complex = DiffusionComplex::new(
        [
            DiffusionNode {
                node: left,
                capacity: integer(1),
            },
            DiffusionNode {
                node: right,
                capacity: integer(1),
            },
        ],
        [DiffusionBranch {
            branch: CurrentBranchId(1),
            source: left,
            target: right,
            conductance: integer(1),
        }],
    )
    .unwrap();
    let law = ExactDiffusionLaw::new(complex).unwrap();
    let standing = law
        .initial_standing(BTreeMap::from([(left, integer(1)), (right, integer(0))]))
        .unwrap();
    let event = DiffusionEvent {
        interval: integer(1),
        source: BTreeMap::new(),
    };
    let with = reconstruct(
        &census,
        &atlas,
        focus,
        &declaration,
        &cover,
        Some(DeclaredDiffusionPassage {
            law: &law,
            standing: &standing,
            event: &event,
        }),
    )
    .unwrap();
    assert_eq!(with.fiber.focus_candidates, without.fiber.focus_candidates);
    assert_eq!(with.fiber.compression, without.fiber.compression);
    let returned = with.diffusion.unwrap();
    assert_eq!(returned.receipt.conservation_residual, integer(0));
    assert_eq!(
        returned.standing_after.content[&left],
        integer(2) / integer(3)
    );
}

#[test]
fn insufficient_work_cover_refuses_the_whole_population() {
    let census = census();
    let focus = address(&census, "vectro");
    let declaration = declaration(&census, ReceiverFamily::of([ReceiverAxis::Kind]));
    let atlas = ConductAtlas::found(&census, 1);
    let demand = reconstruction_demand(&census, focus, &declaration).unwrap();
    let error = reconstruct(
        &census,
        &atlas,
        focus,
        &declaration,
        &ReconstructionWorkCover {
            system_items: demand.system_items.saturating_sub(1),
            pair_chart: demand.pair_chart.clone(),
            edit_cells: demand.edit_cells.clone(),
        },
        None,
    )
    .unwrap_err();
    assert!(matches!(
        error,
        ReconstructionError::WorkCoverInsufficient { .. }
    ));
}

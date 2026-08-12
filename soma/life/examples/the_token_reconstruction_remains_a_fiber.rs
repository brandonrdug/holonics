//! Drive the bounded ReconstructionFiber on misspelling, punctuation, reflection, and exact
//! diffusion. The artifact is the returned population and its witnesses, never a corrected word.

use std::collections::{BTreeMap, BTreeSet};

use holonic_engine::corpus_census::{
    CorpusCensus, LexicalSpecies, Stratum, StratumDeclaration, SurfaceId,
};
use holonic_engine::diffusion::{
    DiffusionBranch, DiffusionComplex, DiffusionEvent, DiffusionNode, ExactDiffusionLaw,
};
use holonic_engine::token_invariance::{ConductAtlas, ReceiverAxis, ReceiverFamily};
use holonic_engine::{CurrentBranchId, CurrentNodeId};
use life::reconstruction_fiber::{
    edit_complex, reconstruct, reconstruction_demand, CandidatePopulation,
    DeclaredDiffusionPassage, OccurrenceAddress, ReconstructionBody, ReconstructionDeclaration,
    ReconstructionPassage, ReconstructionWorkCover,
};
use relational_geometry::integer;

const STRATA: [StratumDeclaration; 1] = [StratumDeclaration {
    stratum: Stratum(0),
    label: "language-experiment",
    relative_root: "",
    extension: "",
    recursive: false,
}];

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut census = CorpusCensus::declaring(&STRATA, LexicalSpecies::Prose)?;
    census.admit_whole(Stratum(0), "broken-vector".to_owned(), "left vectro right");
    census.admit_whole(Stratum(0), "vector".to_owned(), "left vector right");
    census.admit_whole(Stratum(0), "tensor".to_owned(), "up tensor down");
    census.admit_whole(Stratum(0), "matrix".to_owned(), "square matrix product");
    census.admit_whole(
        Stratum(0),
        "broken-matrix".to_owned(),
        "square matirx product",
    );
    census.admit_whole(Stratum(0), "commas".to_owned(), "well ,,, I pause");
    census.admit_whole(Stratum(0), "periods".to_owned(), "well ... I pause");
    census.admit_whole(Stratum(0), "call-add".to_owned(), "add ( 2 , 2 )");
    census.admit_whole(Stratum(0), "call-multiply".to_owned(), "multiply ( 2 , 2 )");

    let atlas = ConductAtlas::found(&census, 1);
    let focus = occurrence(&census, "vectro")?;
    let candidates = BTreeSet::from([
        surface(&census, "vectro")?,
        surface(&census, "vector")?,
        surface(&census, "tensor")?,
        surface(&census, "matrix")?,
    ]);

    let coarse_declaration = ReconstructionDeclaration {
        candidates: CandidatePopulation::Declared(candidates.clone()),
        family: ReceiverFamily::of([ReceiverAxis::Kind]),
        horizon: 1,
    };
    let coarse = run(&census, &atlas, focus, &coarse_declaration, None)?;

    let left = CurrentNodeId(1);
    let middle = CurrentNodeId(2);
    let right = CurrentNodeId(3);
    let diffusion_complex = DiffusionComplex::new(
        [
            DiffusionNode {
                node: left,
                capacity: integer(1),
            },
            DiffusionNode {
                node: middle,
                capacity: integer(1),
            },
            DiffusionNode {
                node: right,
                capacity: integer(1),
            },
        ],
        [
            DiffusionBranch {
                branch: CurrentBranchId(1),
                source: left,
                target: middle,
                conductance: integer(1),
            },
            DiffusionBranch {
                branch: CurrentBranchId(2),
                source: middle,
                target: right,
                conductance: integer(1),
            },
        ],
    )?;
    let diffusion_law = ExactDiffusionLaw::with_boundary(diffusion_complex, [left, right])?;
    let diffusion_standing = diffusion_law.initial_standing(BTreeMap::from([
        (left, integer(1)),
        (middle, integer(0)),
        (right, integer(0)),
    ]))?;
    let diffusion_event = DiffusionEvent {
        interval: integer(1),
        source: BTreeMap::new(),
    };

    let richer_declaration = ReconstructionDeclaration {
        candidates: CandidatePopulation::Declared(candidates),
        family: ReceiverFamily::of([ReceiverAxis::Kind, ReceiverAxis::Weight]),
        horizon: 1,
    };
    let richer = run(
        &census,
        &atlas,
        focus,
        &richer_declaration,
        Some(DeclaredDiffusionPassage {
            law: &diffusion_law,
            standing: &diffusion_standing,
            event: &diffusion_event,
        }),
    )?;

    println!("RECONSTRUCTION FIBER — THE RETURNED ARTIFACT");
    exhibit("coarse {kind}", &census, &coarse);
    exhibit("richer {kind,weight}", &census, &richer);

    let mut body = ReconstructionBody::new();
    let coarse_id = body.found(coarse)?;
    let reflection = body.reflect(coarse_id, richer)?;
    println!("\nRETROSPECTIVE REFLECTION");
    println!(
        "  passage                 {} -> {}",
        reflection.predecessor.0, reflection.successor.0
    );
    println!(
        "  retained                {:?}",
        names(&census, &reflection.retained)
    );
    println!(
        "  departed                {:?}",
        names(&census, &reflection.departed)
    );
    println!(
        "  shortest witnesses      {}",
        reflection.separating_witnesses.len()
    );

    let returned = body
        .passage(reflection.successor)
        .expect("the reflected passage was deposited");
    let diffusion = returned
        .diffusion
        .as_ref()
        .expect("the declared diffusion passage returned");
    println!("\nEXACT DIFFUSION FACE — ORTHOGONAL TO CANDIDATE IDENTITY");
    println!(
        "  boundary / interior     {:?} / {:?}",
        diffusion.receipt.transfer.certificate.boundary,
        diffusion.receipt.transfer.certificate.interior
    );
    println!(
        "  conservation residual   {}",
        diffusion.receipt.conservation_residual
    );
    println!(
        "  middle content after    {}",
        diffusion.standing_after.content[&middle]
    );

    let punctuation_focus = occurrence(&census, ",,,")?;
    let punctuation = ReconstructionDeclaration {
        candidates: CandidatePopulation::Declared(BTreeSet::from([
            surface(&census, ",,,")?,
            surface(&census, "...")?,
        ])),
        family: ReceiverFamily::of([ReceiverAxis::Kind, ReceiverAxis::Weight]),
        horizon: 1,
    };
    let punctuation_passage = run(&census, &atlas, punctuation_focus, &punctuation, None)?;
    println!("\nPUNCTUATION IS A FOCAL OCCURRENCE, NOT A SPECIAL CASE");
    println!(
        "  contextual fiber        {:?}",
        names(&census, &punctuation_passage.fiber.focus_candidates)
    );
    println!(
        "  word population intact  {} surfaces",
        census.word_surfaces().len()
    );

    let transpose = edit_complex("matrix", "matirx");
    println!("\nEDIT COMPLEX IS TESTIMONY, NOT THE GOVERNOR");
    println!(
        "  matrix -> matirx        minimum {} · paths {} · DAG {} nodes / {} edges",
        transpose.minimum_operations,
        transpose.minimal_path_count,
        transpose.nodes.len(),
        transpose.edges.len()
    );
    println!("  delivery boundary       OPEN (whitespace was not retained by this census)");
    println!("  selected correction     NONE");

    Ok(())
}

fn run<'a>(
    census: &CorpusCensus,
    atlas: &ConductAtlas,
    focus: OccurrenceAddress,
    declaration: &ReconstructionDeclaration,
    diffusion: Option<DeclaredDiffusionPassage<'a>>,
) -> Result<ReconstructionPassage, Box<dyn std::error::Error>> {
    let demand = reconstruction_demand(census, focus, declaration)?;
    Ok(reconstruct(
        census,
        atlas,
        focus,
        declaration,
        &ReconstructionWorkCover::exactly(&demand),
        diffusion,
    )?)
}

fn exhibit(label: &str, census: &CorpusCensus, passage: &ReconstructionPassage) {
    println!("\n  {label}");
    println!(
        "    focus fiber            {:?}",
        names(census, &passage.fiber.focus_candidates)
    );
    println!(
        "    supporting occurrences {}",
        passage.fiber.focus_support.len()
    );
    println!(
        "    root blocks            one-shot {} · conduct {}",
        passage.fiber.root_one_shot_blocks.len(),
        passage.fiber.root_conduct_blocks.len()
    );
    println!(
        "    work                    {} roots · {} items · pair chart {} · edit cells {}",
        passage.fiber.work.roots,
        passage.fiber.work.system_items,
        passage.fiber.work.pair_chart,
        passage.fiber.work.edit_cells
    );
    println!(
        "    open exterior           declared={} corpus={} delivery={}",
        passage.fiber.outside_declared_population_open,
        passage.fiber.outside_corpus_open,
        passage.fiber.delivery_boundary_open
    );
}

fn names(census: &CorpusCensus, surfaces: &BTreeSet<SurfaceId>) -> Vec<String> {
    surfaces
        .iter()
        .map(|surface| census.surface(*surface).to_owned())
        .collect()
}

fn surface(census: &CorpusCensus, text: &str) -> Result<SurfaceId, String> {
    census
        .lookup(text)
        .ok_or_else(|| format!("surface {text:?} was not admitted"))
}

fn occurrence(census: &CorpusCensus, text: &str) -> Result<OccurrenceAddress, String> {
    let surface = surface(census, text)?;
    for (whole, record) in census.wholes().iter().enumerate() {
        if let Some(position) = record
            .stream
            .iter()
            .position(|standing| *standing == surface)
        {
            return Ok(OccurrenceAddress {
                whole: whole as u32,
                position: position as u32,
                surface,
            });
        }
    }
    Err(format!("surface {text:?} has no occurrence"))
}

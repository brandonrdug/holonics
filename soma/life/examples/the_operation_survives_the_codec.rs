//! A bounded carrier-neutral section experiment. Exterior charts supply exact incidence and world
//! consequences; the machine receives no operation label. Receiver/history conduct alone founds
//! the reconstruction fibers and shortest separating interventions.

use std::collections::{BTreeMap, BTreeSet};

use holonic_engine::cuda_refine::CudaRefineExecutor;
use life::{
    causal_section::{CausalSection, CausalSectionEcology, CausalSectionReading, SectionState},
    form_mouth::deposit_form_or_message,
    incidence_production::{DeclaredContactFace, DeclaredOccurrence, IncidenceComplex},
};
use serde::Serialize;

const DRIVER: &str = "the_operation_survives_the_codec";
const FORM: &str = "causal-section-grade";
const SCHEMA: &str = "soma-life.operation-survives-codec.v2";

#[derive(Clone, Copy)]
enum ExteriorLaw {
    Sum,
    Product,
    Difference,
    ReverseDifference,
}

impl ExteriorLaw {
    const fn enact(self, left: i64, right: i64) -> i64 {
        match self {
            Self::Sum => left + right,
            Self::Product => left * right,
            Self::Difference => left - right,
            Self::ReverseDifference => right - left,
        }
    }
}

struct PresentationDeclaration<'a> {
    identity: &'a str,
    lineage: &'a str,
    surfaces: [&'a str; 3],
    contact_faces: [&'a str; 2],
    law: ExteriorLaw,
}

#[derive(Serialize)]
struct StateReceipt {
    observations: BTreeMap<String, String>,
    successors: BTreeMap<String, usize>,
}

#[derive(Serialize)]
struct BondReceipt {
    from: String,
    to: String,
    contact_faces: BTreeSet<String>,
    multiplicity: u64,
}

#[derive(Serialize)]
struct PresentationReceipt {
    identity: String,
    lineage: String,
    sites: Vec<String>,
    bonds: Vec<BondReceipt>,
    states: Vec<StateReceipt>,
    root: usize,
}

#[derive(Serialize)]
struct SeparatorReceipt {
    left: String,
    right: String,
    interventions: Vec<String>,
    receiver: Option<String>,
    left_observation: Option<String>,
    right_observation: Option<String>,
    separated_by_terminus: bool,
}

#[derive(Serialize)]
struct WorkReceipt {
    presentations: u64,
    states: u64,
    contacts: u64,
    transitions: u64,
    observations: u64,
    complete_state_pair_chart: String,
}

#[derive(Serialize)]
struct ApparatusReceipt {
    carrier: &'static str,
    device_name: String,
    quotient_launches: u64,
    block_threads: u32,
    warp_size: u32,
    host_semantic_replay: bool,
}

#[derive(Serialize)]
struct GradeReceipt {
    schema: &'static str,
    presentations: Vec<PresentationReceipt>,
    receivers: BTreeSet<String>,
    root_one_shot_blocks: Vec<BTreeSet<String>>,
    root_conduct_blocks: Vec<BTreeSet<String>>,
    reconstruction_fibers: Vec<BTreeSet<String>>,
    shortest_separators: Vec<SeparatorReceipt>,
    value_ablated_conduct_blocks: Vec<BTreeSet<String>>,
    renamed_conduct_shape: Vec<usize>,
    work: WorkReceipt,
    apparatus: ApparatusReceipt,
    same_operation_cross_codec_fiber: BTreeSet<String>,
    same_value_different_law_separated: Vec<String>,
    reversed_port_separated: Vec<String>,
    all_contact_faces_retained: bool,
    receiver_ablation_only_coarsened: bool,
    surface_renaming_preserved_shape: bool,
    material_kind_router_present: bool,
    selected_reconstruction_representative: Option<String>,
    outside_declared_population: &'static str,
}

fn main() -> Result<(), String> {
    let mut card = CudaRefineExecutor::new().map_err(|error| error.to_string())?;
    let launches_before = card.launches();
    let ecology =
        CausalSectionEcology::found(population(false)).map_err(|error| error.to_string())?;
    let reading = ecology.read(&mut card).map_err(|error| error.to_string())?;
    let ablated = ecology
        .read_without("value", &mut card)
        .map_err(|error| error.to_string())?;
    let renamed = CausalSectionEcology::found(population(true))
        .map_err(|error| error.to_string())?
        .read(&mut card)
        .map_err(|error| error.to_string())?;

    let cross_codec = reading
        .root_conduct_blocks
        .iter()
        .find(|block| {
            ["infix-sum", "call-sum", "word-sum"]
                .iter()
                .all(|identity| block.contains(*identity))
        })
        .cloned()
        .ok_or_else(|| "the three sum presentations did not found one conduct fiber".to_owned())?;
    let same_value_separator = separator_between(&reading, "infix-sum", "infix-product")
        .ok_or_else(|| "same-value sum/product returned no separator".to_owned())?;
    let reversed_separator = separator_between(&reading, "difference", "reverse-difference")
        .ok_or_else(|| "reversing a noncommuting port returned no separator".to_owned())?;
    if same_value_separator.interventions.len() != 1 || reversed_separator.interventions.len() != 1
    {
        return Err(
            "a declared one-step control did not return a shortest one-step separator".to_owned(),
        );
    }

    let complete_shape = block_shape(&reading.root_conduct_blocks);
    let renamed_shape = block_shape(&renamed.root_conduct_blocks);
    let receiver_ablation_only_coarsened = ablated.root_conduct_blocks.len() == 1
        && ablated.root_conduct_blocks[0].len() == reading.presentations.len();
    let surface_renaming_preserved_shape = complete_shape == renamed_shape;
    let all_contact_faces_retained = ecology.sections().iter().all(|section| {
        section
            .incidence
            .bonds()
            .iter()
            .all(|bond| !bond.contact_faces.is_empty())
    });
    if !receiver_ablation_only_coarsened
        || !surface_renaming_preserved_shape
        || !all_contact_faces_retained
    {
        return Err("one causal-section falsifier fired".to_owned());
    }

    let presentations = ecology
        .sections()
        .iter()
        .map(|section| PresentationReceipt {
            identity: section.identity.clone(),
            lineage: section.lineage.clone(),
            sites: section
                .incidence
                .sites()
                .iter()
                .map(|site| site.surface.clone())
                .collect(),
            bonds: section
                .incidence
                .bonds()
                .iter()
                .map(|bond| BondReceipt {
                    from: section.incidence.sites()[bond.from].surface.clone(),
                    to: section.incidence.sites()[bond.to].surface.clone(),
                    contact_faces: bond
                        .contact_faces
                        .iter()
                        .map(|face| face.name().to_owned())
                        .collect(),
                    multiplicity: bond.multiplicity,
                })
                .collect(),
            states: section
                .states
                .iter()
                .map(|state| StateReceipt {
                    observations: state.observations.clone(),
                    successors: state.successors.clone(),
                })
                .collect(),
            root: section.root,
        })
        .collect();
    let shortest_separators = reading
        .shortest_separators
        .iter()
        .map(|separator| SeparatorReceipt {
            left: separator.left.clone(),
            right: separator.right.clone(),
            interventions: separator.interventions.clone(),
            receiver: separator.receiver.clone(),
            left_observation: separator.left_observation.clone(),
            right_observation: separator.right_observation.clone(),
            separated_by_terminus: separator.separated_by_terminus,
        })
        .collect();
    let receipt = GradeReceipt {
        schema: SCHEMA,
        presentations,
        receivers: reading.receivers.clone(),
        root_one_shot_blocks: reading.root_one_shot_blocks.clone(),
        root_conduct_blocks: reading.root_conduct_blocks.clone(),
        reconstruction_fibers: reading
            .reconstruction_fibers
            .iter()
            .map(|fiber| fiber.presentations.clone())
            .collect(),
        shortest_separators,
        value_ablated_conduct_blocks: ablated.root_conduct_blocks,
        renamed_conduct_shape: renamed_shape,
        work: WorkReceipt {
            presentations: reading.work.presentations,
            states: reading.work.states,
            contacts: reading.work.contacts,
            transitions: reading.work.transitions,
            observations: reading.work.observations,
            complete_state_pair_chart: reading.work.complete_state_pair_chart.to_string(),
        },
        apparatus: ApparatusReceipt {
            carrier: "resident-cuda-exact-quotient",
            device_name: card.device_name().to_owned(),
            quotient_launches: card.launches().saturating_sub(launches_before),
            block_threads: card.block_threads(),
            warp_size: card.warp_size(),
            host_semantic_replay: false,
        },
        same_operation_cross_codec_fiber: cross_codec,
        same_value_different_law_separated: same_value_separator.interventions.clone(),
        reversed_port_separated: reversed_separator.interventions.clone(),
        all_contact_faces_retained,
        receiver_ablation_only_coarsened,
        surface_renaming_preserved_shape,
        material_kind_router_present: false,
        selected_reconstruction_representative: None,
        outside_declared_population: "OPEN",
    };
    let octets = serde_json::to_vec_pretty(&receipt).map_err(|error| error.to_string())?;
    let deposited = deposit_form_or_message(DRIVER, FORM, &octets)?;

    println!("THE OPERATION SURVIVES THE CODEC");
    println!("  presentations         {}", reading.presentations.len());
    println!(
        "  root one-shot blocks  {:?}",
        block_shape(&reading.root_one_shot_blocks)
    );
    println!("  root conduct blocks   {complete_shape:?}");
    println!(
        "  sum fiber             {:?}",
        receipt.same_operation_cross_codec_fiber
    );
    println!(
        "  sum/product separator {:?}",
        receipt.same_value_different_law_separated
    );
    println!(
        "  reversed port         {:?}",
        receipt.reversed_port_separated
    );
    println!(
        "  value receiver ablated {:?}",
        block_shape(&receipt.value_ablated_conduct_blocks)
    );
    println!(
        "  renamed shape         {:?}",
        receipt.renamed_conduct_shape
    );
    println!(
        "  work                  {} states · {} transitions · pair chart {}",
        receipt.work.states, receipt.work.transitions, receipt.work.complete_state_pair_chart
    );
    println!(
        "  resident quotient     {} · {} launches · {} threads/block",
        receipt.apparatus.device_name,
        receipt.apparatus.quotient_launches,
        receipt.apparatus.block_threads
    );
    println!("  selected representative NONE");
    println!("  outside population    OPEN");
    println!("  form                   {}", deposited.path.display());
    println!("  address                {}", deposited.address);
    Ok(())
}

fn population(renamed: bool) -> Vec<CausalSection> {
    declarations()
        .into_iter()
        .map(|declaration| found_section(declaration, renamed))
        .collect()
}

fn declarations() -> Vec<PresentationDeclaration<'static>> {
    vec![
        PresentationDeclaration {
            identity: "infix-sum",
            lineage: "symbolic-infix",
            surfaces: ["left", "plus", "right"],
            contact_faces: ["left-operand", "right-operand"],
            law: ExteriorLaw::Sum,
        },
        PresentationDeclaration {
            identity: "call-sum",
            lineage: "function-call",
            surfaces: ["add", "left", "right"],
            contact_faces: ["callee-argument", "argument-order"],
            law: ExteriorLaw::Sum,
        },
        PresentationDeclaration {
            identity: "word-sum",
            lineage: "word-presentation",
            surfaces: ["sum", "first", "second"],
            contact_faces: ["word-landmark", "word-landmark"],
            law: ExteriorLaw::Sum,
        },
        PresentationDeclaration {
            identity: "infix-product",
            lineage: "symbolic-infix",
            surfaces: ["left", "times", "right"],
            contact_faces: ["factor", "factor"],
            law: ExteriorLaw::Product,
        },
        PresentationDeclaration {
            identity: "call-product",
            lineage: "function-call",
            surfaces: ["multiply", "left", "right"],
            contact_faces: ["callee-argument", "argument-order"],
            law: ExteriorLaw::Product,
        },
        PresentationDeclaration {
            identity: "difference",
            lineage: "ordered-infix",
            surfaces: ["left", "minus", "right"],
            contact_faces: ["minuend", "subtrahend"],
            law: ExteriorLaw::Difference,
        },
        PresentationDeclaration {
            identity: "reverse-difference",
            lineage: "reversed-port-control",
            surfaces: ["right", "minus", "left"],
            contact_faces: ["subtrahend", "minuend"],
            law: ExteriorLaw::ReverseDifference,
        },
    ]
}

fn found_section(declaration: PresentationDeclaration<'_>, renamed: bool) -> CausalSection {
    let identity = if renamed {
        format!("renamed-{}", declaration.identity)
    } else {
        declaration.identity.to_owned()
    };
    let surfaces = declaration.surfaces.map(|surface| {
        if renamed {
            format!("r-{surface}")
        } else {
            surface.to_owned()
        }
    });
    let occurrence = DeclaredOccurrence {
        identity: format!("{identity}:incidence"),
        storage_ordinal: 0,
        caused_by: BTreeSet::new(),
        text: surfaces.join(" "),
    };
    let faces = vec![declaration
        .contact_faces
        .into_iter()
        .map(|face| DeclaredContactFace::new(face).expect("the exterior declares a face"))
        .collect::<Vec<_>>()];
    let incidence = IncidenceComplex::found_with_contact_faces(&[occurrence], 3, &faces)
        .expect("the exterior chart founds a section");
    let coordinates = [(2, 2), (3, 2), (2, 3), (3, 3)];
    let states = coordinates
        .iter()
        .enumerate()
        .map(|(at, (left, right))| {
            let successors = match at {
                0 => BTreeMap::from([("raise-left".to_owned(), 1), ("raise-right".to_owned(), 2)]),
                1 => BTreeMap::from([("raise-right".to_owned(), 3)]),
                2 => BTreeMap::from([("raise-left".to_owned(), 3)]),
                _ => BTreeMap::new(),
            };
            SectionState {
                observations: BTreeMap::from([
                    ("defined".to_owned(), "yes".to_owned()),
                    (
                        "value".to_owned(),
                        declaration.law.enact(*left, *right).to_string(),
                    ),
                ]),
                successors,
            }
        })
        .collect();
    CausalSection {
        identity,
        lineage: declaration.lineage.to_owned(),
        incidence,
        states,
        root: 0,
    }
}

fn separator_between<'a>(
    reading: &'a CausalSectionReading,
    left: &str,
    right: &str,
) -> Option<&'a life::causal_section::SectionSeparator> {
    reading.shortest_separators.iter().find(|separator| {
        (separator.left == left && separator.right == right)
            || (separator.left == right && separator.right == left)
    })
}

fn block_shape(blocks: &[BTreeSet<String>]) -> Vec<usize> {
    let mut shape = blocks.iter().map(BTreeSet::len).collect::<Vec<_>>();
    shape.sort_unstable();
    shape
}

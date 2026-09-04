//! Exact reconstruction of an opaque recurrent bit transducer.
//!
//! The instrument can call the black-box ABI and return its testimony. It
//! cannot inspect the target through the production `BitCausalLaw`, choose a
//! distinguishing query, supply a candidate program, or issue a semantic
//! certificate.

use std::collections::{BTreeMap, BTreeSet};
use std::error::Error;

use holonic_engine::{
    BitCausalEvent, BitCausalLaw, BitCausalStanding, BitInstructionResourceReceipt, BitLineageId,
    BitQuery, BitResponse, BitSearchWork, BitTransducerProgram, CausalWorld, EventId,
    ExecutableX86BitProgram, bit_cubical_geometry, compile_x86_64_bit_program,
};

#[derive(Clone, Debug)]
struct ReconstructionReceipt {
    standing: BitCausalStanding,
    declared_programs: u64,
    imported_landmarks: u64,
    returned_queries: u64,
    exhaustive_returns: u64,
    candidates_after_width: BTreeMap<u8, u64>,
    search_work: BitSearchWork,
}

fn mask(width: u8) -> u8 {
    if width == 8 {
        u8::MAX
    } else {
        (1_u8 << width) - 1
    }
}

fn rotate(value: u8, rotation: u8, width: u8) -> u8 {
    let word_mask = mask(width);
    let rotation = rotation % width;
    let value = u16::from(value & word_mask);
    if rotation == 0 {
        return value as u8;
    }
    (((value << rotation) | (value >> (width - rotation))) & u16::from(word_mask)) as u8
}

/// The opaque membrane. The reconstruction law receives only returned
/// `(query,response)` testimony and never receives this decomposition.
#[inline(never)]
fn opaque_transducer(query: BitQuery) -> BitResponse {
    let word_mask = mask(query.width);
    let mixed = query.state.wrapping_add(query.input) & word_mask;
    let turned = rotate(mixed, 5, query.width);
    let next_state = turned ^ (0xb7 & word_mask);
    let output = next_state.wrapping_add(rotate(query.input, 3, query.width)) & word_mask;
    BitResponse::new(query.width, next_state, output).expect("opaque response is in its receiver")
}

fn exhaustive_responses(width: u8) -> Vec<BitResponse> {
    let word_mask = u32::from(mask(width));
    (0..1_u32 << (2 * width))
        .map(|encoded| {
            opaque_transducer(
                BitQuery::new(
                    width,
                    ((encoded >> width) & word_mask) as u8,
                    (encoded & word_mask) as u8,
                )
                .expect("canonical query is in its receiver"),
            )
        })
        .collect()
}

fn landmark_queries(width: u8) -> BTreeSet<BitQuery> {
    BTreeSet::from([BitQuery::new(width, 0, 0).unwrap()])
}

fn add_work(total: &mut BitSearchWork, received: &BitSearchWork) {
    total.candidate_evaluations += received.candidate_evaluations;
    total.compared_program_pairs += received.compared_program_pairs;
    total.visited_query_vertices += received.visited_query_vertices;
}

fn reconstruct(
    with_landmarks: bool,
    event_base: u64,
) -> Result<ReconstructionReceipt, Box<dyn Error>> {
    let law = BitCausalLaw::new(8, 1)?;
    let standing = BitCausalStanding::new(8, 1)?;
    let declared_programs = u64::try_from(standing.candidates().len())?;
    let mut world = CausalWorld::new(law, standing);
    let mut next_event = event_base;
    let mut imported_landmarks = 0_u64;
    let mut returned_queries = 0_u64;
    let mut exhaustive_returns = 0_u64;
    let mut candidates_after_width = BTreeMap::new();
    let mut search_work = BitSearchWork::default();

    for width in 1..=8 {
        if width > 1 {
            let receipt = world.receive(&BitCausalEvent::FoundReceiver {
                event: EventId(next_event),
                width,
            })?;
            next_event += 1;
            add_work(&mut search_work, &receipt.radiation[0].search_work);
        }

        if with_landmarks {
            for query in landmark_queries(width) {
                let receipt = world.receive(&BitCausalEvent::InheritLandmark {
                    event: EventId(next_event),
                    lineage: BitLineageId(700 + u64::from(width)),
                    query,
                    response: opaque_transducer(query),
                })?;
                next_event += 1;
                imported_landmarks += 1;
                add_work(&mut search_work, &receipt.radiation[0].search_work);
            }
        }

        loop {
            if let Some(query) = world.standing().next_query() {
                let receipt = world.receive(&BitCausalEvent::ReturnObservation {
                    event: EventId(next_event),
                    receiver: BitLineageId(1),
                    query,
                    response: opaque_transducer(query),
                })?;
                next_event += 1;
                returned_queries += 1;
                add_work(&mut search_work, &receipt.radiation[0].search_work);
                continue;
            }
            if let Some(verification_width) = world.standing().verification_width() {
                let receipt = world.receive(&BitCausalEvent::ReturnExhaustiveReceiver {
                    event: EventId(next_event),
                    receiver: BitLineageId(1),
                    width: verification_width,
                    responses: exhaustive_responses(verification_width),
                })?;
                next_event += 1;
                exhaustive_returns += 1;
                add_work(&mut search_work, &receipt.radiation[0].search_work);
                continue;
            }
            break;
        }
        candidates_after_width.insert(width, u64::try_from(world.standing().candidates().len())?);
    }
    world.standing().validate()?;
    Ok(ReconstructionReceipt {
        standing: world.standing().clone(),
        declared_programs,
        imported_landmarks,
        returned_queries,
        exhaustive_returns,
        candidates_after_width,
        search_work,
    })
}

fn main() -> Result<(), Box<dyn Error>> {
    let cold = reconstruct(false, 1_000)?;
    let inherited = reconstruct(true, 1_000_000)?;
    if cold.standing.candidates() != inherited.standing.candidates() {
        return Err("cold and lineage-rich reconstruction reached different families".into());
    }
    if inherited.returned_queries > cold.returned_queries {
        return Err("imported lineage increased production query demand".into());
    }

    let certificate = inherited
        .standing
        .certificate()
        .ok_or("lineage-rich reconstruction has no exhaustive certificate")?;
    let representative: BitTransducerProgram = certificate.representative;
    let geometry = bit_cubical_geometry(representative, 8)?;
    let (absent_edge_relations, invariant_edge_relations, contextual_edge_relations) =
        geometry.directed_edge_flip_counts.iter().flatten().fold(
            (0_u64, 0_u64, 0_u64),
            |(absent, invariant, contextual), count| {
                if *count == 0 {
                    (absent + 1, invariant, contextual)
                } else if *count == geometry.vertex_count {
                    (absent, invariant + 1, contextual)
                } else {
                    (absent, invariant, contextual + 1)
                }
            },
        );
    let logical = representative.logical_resources()?;
    let instruction_resources: BitInstructionResourceReceipt =
        representative.instruction_resources();

    let image = compile_x86_64_bit_program(representative)?;
    let executable = ExecutableX86BitProgram::new(&image)?;
    let mut native_equal = true;
    for state in 0..=u8::MAX {
        for input in 0..=u8::MAX {
            let query = BitQuery::new(8, state, input)?;
            if executable.execute(query)? != opaque_transducer(query) {
                native_equal = false;
                break;
            }
        }
    }

    println!("schema\tholonic-engine.bit-black-box-reconstruction-instrument.v1");
    println!("declared_program_ecology\t{}", inherited.declared_programs);
    println!("receiver_widths\t{:?}", certificate.receiver_widths);
    println!(
        "exhaustively_testified_vertices\t{}",
        certificate.exhaustively_testified_query_vertices
    );
    println!("cold_returned_queries\t{}", cold.returned_queries);
    println!(
        "lineage_imported_landmarks\t{}",
        inherited.imported_landmarks
    );
    println!("lineage_returned_queries\t{}", inherited.returned_queries);
    println!("cold_exhaustive_returns\t{}", cold.exhaustive_returns);
    println!(
        "lineage_exhaustive_returns\t{}",
        inherited.exhaustive_returns
    );
    println!(
        "cold_candidates_after_width\t{:?}",
        cold.candidates_after_width
    );
    println!(
        "lineage_candidates_after_width\t{:?}",
        inherited.candidates_after_width
    );
    println!(
        "final_compatible_programs\t{}",
        certificate.compatible_programs
    );
    println!("representative\t{representative:?}");
    println!(
        "cold_search_candidate_evaluations\t{}",
        cold.search_work.candidate_evaluations
    );
    println!(
        "cold_search_program_pairs\t{}",
        cold.search_work.compared_program_pairs
    );
    println!(
        "cold_search_query_vertices\t{}",
        cold.search_work.visited_query_vertices
    );
    println!(
        "search_work_candidate_evaluations\t{}",
        inherited.search_work.candidate_evaluations
    );
    println!(
        "search_work_program_pairs\t{}",
        inherited.search_work.compared_program_pairs
    );
    println!(
        "search_work_query_vertices\t{}",
        inherited.search_work.visited_query_vertices
    );
    println!(
        "cubical_algebraic_degrees\t{:?}",
        geometry.algebraic_degrees
    );
    println!(
        "cubical_edge_flip_counts\t{:?}",
        geometry.directed_edge_flip_counts
    );
    println!(
        "cubical_edge_relation_absent_invariant_contextual\t({absent_edge_relations},{invariant_edge_relations},{contextual_edge_relations})"
    );
    println!(
        "logical_work_span_width\t({},{},{})",
        logical.work, logical.causal_span, logical.exposed_parallel_width
    );
    println!("instruction_resources\t{instruction_resources:?}");
    println!("x86_encoded_octets\t{}", image.encoded_octets());
    println!("x86_instructions\t{}", image.instructions.len());
    println!("x86_exhaustive_black_box_parity\t{native_equal}");
    println!("standing_exactly_validated\ttrue");
    Ok(())
}

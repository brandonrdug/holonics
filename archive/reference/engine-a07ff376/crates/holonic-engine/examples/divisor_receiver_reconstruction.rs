//! Reconstruct the dual divisor receivers through opaque contact alone.
//!
//! `ArithmeticFiberLaw` is the hidden grading world.  The reconstruction
//! world sees only chronology-local occurrence ordinals and boolean answers
//! to production-owned common-generator queries.

use std::env;

use holonic_engine::{
    ArithmeticDivisorMembrane, ArithmeticFiberEvent, ArithmeticFiberLaw, ArithmeticFiberStanding,
    CausalWorld, DivisorReceiverId, DivisorReconstructionDoctrine, DivisorReconstructionEvent,
    DivisorReconstructionLaw, DivisorReconstructionStanding, EventId,
};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut arguments = env::args().skip(1);
    let limit = arguments
        .next()
        .map(|value| value.parse::<u64>())
        .transpose()?
        .unwrap_or(30);
    let doctrine = match arguments.next().as_deref() {
        None | Some("witnessed") => DivisorReconstructionDoctrine::PrivateWitnessedGeneratorFacets,
        Some("complete") => DivisorReconstructionDoctrine::CompleteContactComplex,
        Some(other) => {
            return Err(format!(
                "unknown doctrine {other:?}; expected \"witnessed\" or \"complete\""
            )
            .into());
        }
    };
    if arguments.next().is_some() {
        return Err("unexpected arguments after the reconstruction doctrine".into());
    }
    if limit < 2 {
        return Err("the arithmetic aperture must include at least integer 2".into());
    }

    let mut arithmetic_world =
        CausalWorld::new(ArithmeticFiberLaw, ArithmeticFiberStanding::default());
    for value in 2..=limit {
        arithmetic_world.receive(&ArithmeticFiberEvent {
            event: EventId(value - 1),
            value,
        })?;
    }
    let receiver = DivisorReceiverId(1);
    let membrane = ArithmeticDivisorMembrane::new(arithmetic_world.standing(), receiver)?;
    let mut reconstruction_world = CausalWorld::new(
        DivisorReconstructionLaw::new(doctrine),
        DivisorReconstructionStanding::default(),
    );
    reconstruction_world.receive(&DivisorReconstructionEvent::FoundOccurrenceReceiver {
        event: EventId(1),
        receiver,
        chronology: membrane.chronology().to_vec(),
    })?;

    let mut event = 2_u64;
    while let Some(query) = reconstruction_world.standing().next_query().cloned() {
        let returned = membrane.returned_event(EventId(event), query)?;
        reconstruction_world.receive(&returned)?;
        event = event
            .checked_add(1)
            .ok_or("reconstruction event carrier overflow")?;
    }

    let standing = reconstruction_world.standing();
    standing.validate()?;
    let certificate = standing
        .certificate()
        .ok_or("reconstruction closed without a certificate")?;
    let grade = membrane.grade(standing, 4)?;
    println!(
        "receiver={:?} doctrine={:?} occurrences={} latent_generators={} exact={}",
        receiver,
        doctrine,
        certificate.chronology.len(),
        certificate.generator_supports.len(),
        grade.is_exact()
    );
    match doctrine {
        DivisorReconstructionDoctrine::PrivateWitnessedGeneratorFacets => println!(
            "returns: pairwise={} higher_order={} rejected_witnesses={} neighborhood_checks={}",
            standing.work().pairwise_returns,
            standing.work().higher_order_returns,
            standing.work().rejected_witness_candidates,
            standing.work().witness_neighborhood_checks
        ),
        DivisorReconstructionDoctrine::CompleteContactComplex => println!(
            "returns: pairwise={} higher_order={} negative_splits={} clique_search_nodes={}",
            standing.work().pairwise_returns,
            standing.work().higher_order_returns,
            standing.work().negative_candidate_splits,
            standing.work().maximal_clique_search_nodes
        ),
    }
    println!(
        "compression: memberships={} expanded_positive_pairs={} all_pair_slots={}",
        certificate.compression.support_memberships,
        certificate.compression.expanded_positive_pair_contacts,
        certificate.compression.all_pair_slots
    );
    println!(
        "dual_generator_f_vector={:?} boundary_squared_zero={} heldout_sections={} heldout_residuals=({}, {})",
        certificate.generator_f_vector(),
        certificate.generator_boundary_squared_zero(),
        grade.heldout_contact_sections,
        grade.heldout_false_positives,
        grade.heldout_false_negatives
    );
    println!("grading-only latent-generator correspondence:");
    for correspondence in &grade.correspondence {
        let support =
            &certificate.generator_supports[usize::try_from(correspondence.latent_generator.0)?];
        let values = support
            .occurrences
            .iter()
            .map(|occurrence| {
                membrane
                    .occurrence_value(*occurrence)
                    .ok_or("missing grading occurrence")
            })
            .collect::<Result<Vec<_>, _>>()?;
        println!(
            "  {:?} -> prime {} with occurrence support {:?}",
            correspondence.latent_generator, correspondence.grading_prime, values
        );
    }
    Ok(())
}

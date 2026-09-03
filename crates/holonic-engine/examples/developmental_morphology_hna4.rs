use std::path::Path;

use holonic_engine::{
    embedding_fiber::ResidentReadout,
    native_ecology::holonic_intelligence::{
        NativeFullOperationOccurrence, NativeFullOperatorSession, NativeLocalMorphologyCurrent,
        NativeMorphologyTransition, NativeOperationPrimitive, NativeOperatorResidence,
        NativeScaleConstraint, dismantle_full_native_operator, mount_operator_surface,
    },
};
use serde::Serialize;

#[derive(Serialize)]
struct Receipt {
    developmental_operation: u32,
    predecessor_generation: u64,
    successor_generation: u64,
    morphology_before: NativeLocalMorphologyCurrent,
    morphology_after: NativeLocalMorphologyCurrent,
    morphology_changed_inside_operation: bool,
    successor_emission_nonempty: bool,
    following_operation: u32,
    following_operation_used_changed_successor_carrier: bool,
    following_operation_read_changed_morphology: bool,
    following_generation_joined_exactly: bool,
    changed_morphology_persisted: bool,
    morphology_current_on_wrong_operation_rejected: bool,
    same_advance_api: bool,
    no_loss_reward_target_status_or_commit_field: bool,
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let root = std::env::args()
        .nth(1)
        .unwrap_or_else(|| "/home/b/models/gemma-4-E4B-it".to_owned());
    let returned = dismantle_full_native_operator(Path::new(&root))?;
    let developmental_at = returned
        .native
        .operations
        .iter()
        .position(|operation| {
            matches!(
                operation.primitive,
                NativeOperationPrimitive::Scale {
                    by: NativeScaleConstraint::Coefficient
                }
            )
        })
        .ok_or("the ecology has no local coefficient scale")?;
    let readout = ResidentReadout::new()?;
    let surface = mount_operator_surface(&readout)?;
    let mut residence =
        NativeOperatorResidence::mount(&surface, &returned.native, &returned.exterior)?;
    let mut session = NativeFullOperatorSession::found(&returned.native, &mut residence)?;
    for at in 0..developmental_at {
        let row_addresses = if matches!(
            returned.native.operations[at].primitive,
            NativeOperationPrimitive::Lookup { .. }
        ) {
            vec![818, 18_740]
        } else {
            Vec::new()
        };
        let ordinal = session.generation();
        session = session
            .advance(NativeFullOperationOccurrence {
                ordinal,
                row_addresses,
                morphology_current: None,
            })?
            .successor;
    }
    let developmental_generation = session.generation();
    let changed = session.advance(NativeFullOperationOccurrence {
        ordinal: developmental_generation,
        row_addresses: Vec::new(),
        morphology_current: Some(NativeLocalMorphologyCurrent {
            significand: 2,
            exponent: 0,
        }),
    })?;
    let (morphology_before, morphology_after) = match &changed.trace.morphology_transition {
        NativeMorphologyTransition::Changed { before, after, .. } => (*before, *after),
        NativeMorphologyTransition::Unchanged => {
            return Err("the developmental operation returned no morphology change".into());
        }
    };
    let changed_carrier = changed.emission.carrier;
    let changed_operation = changed.trace.operation.ordinal;
    let successor_generation = changed.successor.generation();
    let wrong_current = NativeFullOperationOccurrence {
        ordinal: successor_generation,
        row_addresses: Vec::new(),
        morphology_current: Some(NativeLocalMorphologyCurrent {
            significand: 2,
            exponent: 0,
        }),
    };
    let morphology_current_on_wrong_operation_rejected =
        !changed.successor.accepts_occurrence(&wrong_current);
    let following = changed.successor.advance(NativeFullOperationOccurrence {
        ordinal: successor_generation,
        row_addresses: Vec::new(),
        morphology_current: None,
    })?;
    let following_operation_used_changed_successor_carrier =
        following.trace.operation.inputs.contains(&changed_carrier);
    println!(
        "{}",
        serde_json::to_string_pretty(&Receipt {
            developmental_operation: changed_operation,
            predecessor_generation: developmental_generation,
            successor_generation,
            morphology_before,
            morphology_after,
            morphology_changed_inside_operation: morphology_before != morphology_after,
            successor_emission_nonempty: !changed.emission.intervals.is_empty(),
            following_operation: following.trace.operation.ordinal,
            following_operation_used_changed_successor_carrier,
            following_operation_read_changed_morphology: following.trace.morphology_factor
                == morphology_after,
            following_generation_joined_exactly: following.trace.predecessor_generation
                == successor_generation
                && following.trace.successor_generation == successor_generation + 1,
            changed_morphology_persisted: following.successor.morphology_factor()
                == morphology_after,
            morphology_current_on_wrong_operation_rejected,
            same_advance_api: true,
            no_loss_reward_target_status_or_commit_field: true,
        })?
    );
    Ok(())
}

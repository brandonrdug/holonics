use std::collections::{BTreeMap, BTreeSet};

use holonic_engine::receiver_history_compression::NativeStateId;

use super::{
    rest::{derive_holonomy, derive_recurrences, digest},
    types::{
        LongHorizonBoundaryError, RetainedBoundaryDecoder, RetainedBoundaryFibres,
        RetainedBoundaryStanding, LONG_HORIZON_DECODER_SCHEMA, LONG_HORIZON_FIBRES_SCHEMA,
        LONG_HORIZON_STANDING_SCHEMA,
    },
};

pub(super) fn validate_standing(
    standing: &RetainedBoundaryStanding,
) -> Result<(), LongHorizonBoundaryError> {
    let states = standing.native_states.len();
    if standing.schema != LONG_HORIZON_STANDING_SCHEMA
        || !is_digest(&standing.predecessor_identity)
        || !is_digest(&standing.boundary_identity)
        || !is_digest(&standing.source_compression_sha256)
        || states < 2
        || standing
            .native_states
            .iter()
            .enumerate()
            .any(|(at, state)| state.0 != at as u64)
        || standing.generator_table.is_empty()
        || standing.generator_table.len() % states != 0
        || standing
            .generator_table
            .iter()
            .any(|state| *state as usize >= states)
        || standing.source_physical_states < 2
        || standing.source_physical_action.is_empty()
        || standing.source_physical_action.len() % standing.source_physical_states as usize != 0
        || standing.physical_to_native.len() != standing.source_physical_states as usize
        || standing
            .physical_to_native
            .iter()
            .any(|state| state.0 as usize >= states)
        || standing.receiver_ids.is_empty()
        || standing.open_exterior.is_empty()
        || !is_digest(&standing.cultivation.dynamic_rest_sha256)
        || !is_digest(&standing.cultivation.predecessor_action_sha256)
        || !is_digest(&standing.cultivation.successor_action_sha256)
        || standing.cultivation.returned_occurrences.is_empty()
        || standing.cultivation.commutator_rank == 0
    {
        return Err(LongHorizonBoundaryError::Standing);
    }
    let generators = standing.generator_table.len() / states;
    if standing.source_physical_action.len()
        != generators * standing.source_physical_states as usize
    {
        return Err(LongHorizonBoundaryError::Standing);
    }
    for generator in 0..generators {
        for physical in 0..standing.source_physical_states as usize {
            let source_target = standing.source_physical_action
                [generator * standing.source_physical_states as usize + physical]
                as usize;
            if source_target >= standing.source_physical_states as usize {
                return Err(LongHorizonBoundaryError::Standing);
            }
            let native = standing.physical_to_native[physical];
            let left = standing.physical_to_native[source_target];
            let right = NativeStateId(
                standing.generator_table[generator * states + native.0 as usize] as u64,
            );
            if left != right {
                return Err(LongHorizonBoundaryError::Standing);
            }
        }
    }
    let receiver_set = standing
        .receiver_ids
        .iter()
        .copied()
        .collect::<BTreeSet<_>>();
    let factor_keys = standing
        .receiver_factors
        .iter()
        .map(|factor| (factor.native, factor.receiver))
        .collect::<BTreeSet<_>>();
    if factor_keys.len() != states * receiver_set.len()
        || standing.native_states.iter().any(|native| {
            receiver_set
                .iter()
                .any(|receiver| !factor_keys.contains(&(*native, *receiver)))
        })
        || standing.recurrences
            != derive_recurrences(&standing.native_states, &standing.generator_table)?
        || standing.ordered_holonomy
            != derive_holonomy(
                &standing.native_states,
                &standing.generator_table,
                standing.cultivation.commutator_rank,
            )?
    {
        return Err(LongHorizonBoundaryError::Standing);
    }
    Ok(())
}

pub(super) fn validate_decoder(
    decoder: &RetainedBoundaryDecoder,
    standing: &RetainedBoundaryStanding,
) -> Result<(), LongHorizonBoundaryError> {
    if decoder.schema != LONG_HORIZON_DECODER_SCHEMA || decoder.interiors.len() < 2 {
        return Err(LongHorizonBoundaryError::Decoder);
    }
    let mut occurrences = BTreeMap::new();
    for (at, interior) in decoder.interiors.iter().enumerate() {
        if interior.occurrence.is_empty()
            || !is_digest(&interior.payload_sha256)
            || digest(&interior.payload) != interior.payload_sha256
            || occurrences
                .insert(interior.occurrence.as_str(), at)
                .is_some()
            || interior
                .predecessor
                .as_deref()
                .is_some_and(|predecessor| !occurrences.contains_key(predecessor))
        {
            return Err(LongHorizonBoundaryError::Decoder);
        }
    }
    let expected = decoder.interiors.len() * standing.source_physical_states as usize;
    let mut items = BTreeSet::new();
    if decoder.source_members.len() != expected {
        return Err(LongHorizonBoundaryError::Decoder);
    }
    for member in &decoder.source_members {
        if !items.insert(member.item)
            || member.interior as usize >= decoder.interiors.len()
            || member.physical_state >= standing.source_physical_states
            || member.base_observations.len() != standing.receiver_ids.len()
            || member.item.0
                != member.interior as u64 * standing.source_physical_states as u64
                    + member.physical_state as u64
        {
            return Err(LongHorizonBoundaryError::Decoder);
        }
    }
    Ok(())
}

pub(super) fn validate_fibres(
    fibres: &RetainedBoundaryFibres,
    decoder: &RetainedBoundaryDecoder,
    standing: &RetainedBoundaryStanding,
) -> Result<(), LongHorizonBoundaryError> {
    if fibres.schema != LONG_HORIZON_FIBRES_SCHEMA
        || fibres.fibres.len() != standing.native_states.len()
        || fibres.richer_reopenings.is_empty()
    {
        return Err(LongHorizonBoundaryError::Fibre);
    }
    let members = decoder
        .source_members
        .iter()
        .map(|member| (member.item, member))
        .collect::<BTreeMap<_, _>>();
    let factor = standing
        .receiver_factors
        .iter()
        .map(|entry| ((entry.native, entry.receiver), entry.observation))
        .collect::<BTreeMap<_, _>>();
    let mut union = BTreeSet::new();
    for (at, (native, source)) in fibres.fibres.iter().enumerate() {
        if native.0 != at as u64 || source.is_empty() {
            return Err(LongHorizonBoundaryError::Fibre);
        }
        for item in source {
            let member = members.get(item).ok_or(LongHorizonBoundaryError::Fibre)?;
            if !union.insert(*item)
                || standing.physical_to_native[member.physical_state as usize] != *native
                || standing
                    .receiver_ids
                    .iter()
                    .enumerate()
                    .any(|(receiver_at, receiver)| {
                        factor.get(&(*native, *receiver))
                            != member.base_observations.get(receiver_at)
                    })
            {
                return Err(LongHorizonBoundaryError::Fibre);
            }
        }
    }
    if union != members.keys().copied().collect::<BTreeSet<_>>() {
        return Err(LongHorizonBoundaryError::Fibre);
    }
    for separator in &fibres.shortest_separators {
        if separator.left == separator.right
            || !union.contains(&separator.left)
            || !union.contains(&separator.right)
            || separator.distinguishing_word.is_empty()
        {
            return Err(LongHorizonBoundaryError::Fibre);
        }
    }
    for reopening in &fibres.richer_reopenings {
        let fibre = fibres
            .fibres
            .get(reopening.native.0 as usize)
            .ok_or(LongHorizonBoundaryError::Reopening)?;
        let left = members
            .get(&reopening.left_item)
            .ok_or(LongHorizonBoundaryError::Reopening)?;
        let right = members
            .get(&reopening.right_item)
            .ok_or(LongHorizonBoundaryError::Reopening)?;
        if !fibre.1.contains(&reopening.left_item)
            || !fibre.1.contains(&reopening.right_item)
            || left.interior == right.interior
            || reopening.left_occurrence != decoder.interiors[left.interior as usize].occurrence
            || reopening.right_occurrence != decoder.interiors[right.interior as usize].occurrence
            || reopening.left_reading_sha256
                != decoder.interiors[left.interior as usize].payload_sha256
            || reopening.right_reading_sha256
                != decoder.interiors[right.interior as usize].payload_sha256
            || reopening.left_reading_sha256 == reopening.right_reading_sha256
            || reopening.receiver_occurrence.is_empty()
            || !reopening.shortest_history.is_empty()
        {
            return Err(LongHorizonBoundaryError::Reopening);
        }
    }
    Ok(())
}

use holonic_engine::is_sha256_digest as is_digest;

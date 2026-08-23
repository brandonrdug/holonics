use std::collections::{BTreeMap, BTreeSet};

use holonic_engine::receiver_exact_compression::{ItemId, ObservedSystem, ReceiverExactCompression};
use holonic_engine::receiver_history_compression::{
    NativeStateId, ReceiverHistoryCompression,
};
use sha2::{Digest, Sha256};

use super::{
    system::AddressedHistorySystem,
    types::{
        BoundaryRecurrence, CultivatedActionLineage, HistoricalInterior,
        HistoricalSourceMember, LongHorizonBoundaryError, LongHorizonRetainedBoundary,
        OrderedBoundaryHolonomy, RetainedBoundaryDecoder, RetainedBoundaryFibres,
        RetainedBoundaryStanding, RicherReceiverReopening, LONG_HORIZON_DECODER_SCHEMA,
        LONG_HORIZON_FIBRES_SCHEMA, LONG_HORIZON_STANDING_SCHEMA,
    },
    validation::{validate_decoder, validate_fibres, validate_standing},
};

impl LongHorizonRetainedBoundary {
    pub fn found(
        predecessor_identity: impl Into<String>,
        boundary_identity: impl Into<String>,
        interiors: Vec<HistoricalInterior>,
        system: &AddressedHistorySystem,
        exact: &ReceiverExactCompression,
        cultivation: CultivatedActionLineage,
    ) -> Result<Self, LongHorizonBoundaryError> {
        if interiors.len() != system.interiors() {
            return Err(LongHorizonBoundaryError::Decoder);
        }
        let compression = ReceiverHistoryCompression::found(system, exact)
            .map_err(|error| LongHorizonBoundaryError::Compression(error.to_string()))?;
        let source_compression_bytes = serde_json::to_vec(&compression)
            .map_err(|error| LongHorizonBoundaryError::Wire(error.to_string()))?;
        let native_states = compression.native_population.clone();
        let receiver_ids = system.receivers();
        let mut squares = compression.generators.iter().collect::<Vec<_>>();
        squares.sort_by_key(|square| square.generator);
        let mut generator_table = Vec::with_capacity(squares.len() * native_states.len());
        for square in squares {
            let action = square
                .native
                .iter()
                .map(|edge| (edge.from, edge.to))
                .collect::<BTreeMap<_, _>>();
            for state in &native_states {
                generator_table.push(
                    u32::try_from(
                        action
                            .get(state)
                            .ok_or(LongHorizonBoundaryError::Standing)?
                            .0,
                    )
                    .map_err(|_| LongHorizonBoundaryError::Standing)?,
                );
            }
        }
        let encoded = compression
            .quotient
            .iter()
            .map(|assignment| (assignment.source, assignment.native))
            .collect::<BTreeMap<_, _>>();
        let physical_to_native = (0..system.states())
            .map(|state| {
                system
                    .source_item(0, state as u32)
                    .and_then(|item| encoded.get(&item).copied())
                    .ok_or(LongHorizonBoundaryError::Standing)
            })
            .collect::<Result<Vec<_>, _>>()?;
        let source_members = system
            .items()
            .into_iter()
            .map(|item| {
                let (interior, physical_state) = system
                    .coordinates(item)
                    .ok_or(LongHorizonBoundaryError::Decoder)?;
                Ok(HistoricalSourceMember {
                    item,
                    interior: u32::try_from(interior)
                        .map_err(|_| LongHorizonBoundaryError::Decoder)?,
                    physical_state,
                    base_observations: system
                        .base_observations(physical_state)
                        .ok_or(LongHorizonBoundaryError::Decoder)?,
                })
            })
            .collect::<Result<Vec<_>, _>>()?;
        let fibres = compression
            .reconstruction_fibres
            .iter()
            .map(|fibre| (fibre.native, fibre.sources.iter().copied().collect()))
            .collect::<Vec<_>>();
        let richer_reopenings = richer_reopenings(&fibres, &source_members, &interiors)?;
        let recurrences = derive_recurrences(&native_states, &generator_table)?;
        let ordered_holonomy = derive_holonomy(
            &native_states,
            &generator_table,
            cultivation.commutator_rank,
        )?;
        let boundary = Self {
            standing: RetainedBoundaryStanding {
                schema: LONG_HORIZON_STANDING_SCHEMA.to_owned(),
                predecessor_identity: predecessor_identity.into(),
                boundary_identity: boundary_identity.into(),
                source_compression_sha256: digest(&source_compression_bytes),
                native_states,
                source_physical_states: system.states() as u32,
                source_physical_action: system.generator_table().to_vec(),
                physical_to_native,
                generator_table,
                receiver_ids,
                receiver_factors: compression.receiver_factors,
                cultivation,
                recurrences,
                ordered_holonomy,
                open_exterior: vec![
                    "a receiver outside the admitted future family may reopen any retained interior"
                        .to_owned(),
                    "unmounted foreign-model histories remain outside this boundary".to_owned(),
                    "multimodal spatial incidence remains the R5 port widening".to_owned(),
                ],
            },
            decoder: RetainedBoundaryDecoder {
                schema: LONG_HORIZON_DECODER_SCHEMA.to_owned(),
                interiors,
                source_members,
            },
            fibres: RetainedBoundaryFibres {
                schema: LONG_HORIZON_FIBRES_SCHEMA.to_owned(),
                fibres,
                shortest_separators: compression.first_separators,
                richer_reopenings,
            },
        };
        boundary.validate()?;
        Ok(boundary)
    }

    pub fn read(
        standing_bytes: &[u8],
        decoder_bytes: &[u8],
        fibre_bytes: &[u8],
    ) -> Result<Self, LongHorizonBoundaryError> {
        let boundary = Self {
            standing: serde_json::from_slice(standing_bytes)
                .map_err(|error| LongHorizonBoundaryError::Wire(error.to_string()))?,
            decoder: serde_json::from_slice(decoder_bytes)
                .map_err(|error| LongHorizonBoundaryError::Wire(error.to_string()))?,
            fibres: serde_json::from_slice(fibre_bytes)
                .map_err(|error| LongHorizonBoundaryError::Wire(error.to_string()))?,
        };
        boundary.validate()?;
        Ok(boundary)
    }

    pub fn standing_bytes(&self) -> Result<Vec<u8>, LongHorizonBoundaryError> {
        self.validate()?;
        serde_json::to_vec(&self.standing)
            .map_err(|error| LongHorizonBoundaryError::Wire(error.to_string()))
    }

    pub fn decoder_bytes(&self) -> Result<Vec<u8>, LongHorizonBoundaryError> {
        self.validate()?;
        serde_json::to_vec(&self.decoder)
            .map_err(|error| LongHorizonBoundaryError::Wire(error.to_string()))
    }

    pub fn fibre_bytes(&self) -> Result<Vec<u8>, LongHorizonBoundaryError> {
        self.validate()?;
        serde_json::to_vec(&self.fibres)
            .map_err(|error| LongHorizonBoundaryError::Wire(error.to_string()))
    }

    pub fn native_of_source(
        &self,
        source: ItemId,
    ) -> Result<NativeStateId, LongHorizonBoundaryError> {
        self.fibres
            .fibres
            .iter()
            .find(|(_, members)| members.contains(&source))
            .map(|(native, _)| *native)
            .ok_or(LongHorizonBoundaryError::Fibre)
    }

    pub fn native_trace(
        &self,
        start: NativeStateId,
        word: &[u32],
    ) -> Result<Vec<NativeStateId>, LongHorizonBoundaryError> {
        trace(
            &self.standing.native_states,
            &self.standing.generator_table,
            start,
            word,
        )
    }

    /// Reconstruct an exact addressed predecessor chain without consulting an exterior source.
    pub fn reconstruct_history(
        &self,
        occurrence: &str,
    ) -> Result<Vec<u8>, LongHorizonBoundaryError> {
        let by_occurrence = self
            .decoder
            .interiors
            .iter()
            .map(|interior| (interior.occurrence.as_str(), interior))
            .collect::<BTreeMap<_, _>>();
        let mut chain = Vec::new();
        let mut current = occurrence;
        let mut seen = BTreeSet::new();
        loop {
            if !seen.insert(current) {
                return Err(LongHorizonBoundaryError::Decoder);
            }
            let interior = by_occurrence
                .get(current)
                .copied()
                .ok_or(LongHorizonBoundaryError::Decoder)?;
            chain.push(interior);
            match interior.predecessor.as_deref() {
                Some(predecessor) => current = predecessor,
                None => break,
            }
        }
        chain.reverse();
        let mut reconstructed = Vec::new();
        for interior in chain {
            let occurrence = interior.occurrence.as_bytes();
            reconstructed.extend_from_slice(&(occurrence.len() as u64).to_le_bytes());
            reconstructed.extend_from_slice(occurrence);
            reconstructed.extend_from_slice(&(interior.payload.len() as u64).to_le_bytes());
            reconstructed.extend_from_slice(&interior.payload);
        }
        Ok(reconstructed)
    }

    pub fn validate(&self) -> Result<(), LongHorizonBoundaryError> {
        validate_standing(&self.standing)?;
        validate_decoder(&self.decoder, &self.standing)?;
        validate_fibres(&self.fibres, &self.decoder, &self.standing)?;
        Ok(())
    }
}

fn richer_reopenings(
    fibres: &[(NativeStateId, Vec<ItemId>)],
    members: &[HistoricalSourceMember],
    interiors: &[HistoricalInterior],
) -> Result<Vec<RicherReceiverReopening>, LongHorizonBoundaryError> {
    let by_item = members
        .iter()
        .map(|member| (member.item, member))
        .collect::<BTreeMap<_, _>>();
    let mut reopenings = Vec::new();
    for (native, source) in fibres {
        let pair = source.iter().enumerate().find_map(|(at, left)| {
            source.iter().skip(at + 1).find_map(|right| {
                let left_member = by_item.get(left)?;
                let right_member = by_item.get(right)?;
                (left_member.interior != right_member.interior).then_some((*left, *right))
            })
        });
        let Some((left_item, right_item)) = pair else {
            continue;
        };
        let left_member = by_item[&left_item];
        let right_member = by_item[&right_item];
        let left = &interiors[left_member.interior as usize];
        let right = &interiors[right_member.interior as usize];
        if left.payload_sha256 == right.payload_sha256 {
            continue;
        }
        reopenings.push(RicherReceiverReopening {
            native: *native,
            left_item,
            right_item,
            left_occurrence: left.occurrence.clone(),
            right_occurrence: right.occurrence.clone(),
            receiver_occurrence: "r4/receiver/exact-historical-interior".to_owned(),
            left_reading_sha256: left.payload_sha256.clone(),
            right_reading_sha256: right.payload_sha256.clone(),
            shortest_history: Vec::new(),
        });
    }
    if reopenings.is_empty() {
        return Err(LongHorizonBoundaryError::Reopening);
    }
    Ok(reopenings)
}

pub(super) fn derive_recurrences(
    states: &[NativeStateId],
    table: &[u32],
) -> Result<Vec<BoundaryRecurrence>, LongHorizonBoundaryError> {
    let generators = table
        .len()
        .checked_div(states.len())
        .ok_or(LongHorizonBoundaryError::Standing)?;
    let mut recurrences = Vec::with_capacity(states.len() * generators);
    for generator in 0..generators {
        for entering in states {
            let mut seen = BTreeMap::new();
            let mut trace = Vec::new();
            let mut state = *entering;
            loop {
                if let Some(first_at) = seen.get(&state).copied() {
                    trace.push(state);
                    recurrences.push(BoundaryRecurrence {
                        generator: generator as u32,
                        entering: *entering,
                        trace,
                        first_repeated_state: state,
                        first_at,
                        returned_at: seen.len(),
                    });
                    break;
                }
                seen.insert(state, trace.len());
                trace.push(state);
                if trace.len() > states.len() {
                    return Err(LongHorizonBoundaryError::Standing);
                }
                state = NativeStateId(
                    *table
                        .get(generator * states.len() + state.0 as usize)
                        .ok_or(LongHorizonBoundaryError::Standing)? as u64,
                );
            }
        }
    }
    Ok(recurrences)
}

pub(super) fn derive_holonomy(
    states: &[NativeStateId],
    table: &[u32],
    commutator_rank: usize,
) -> Result<OrderedBoundaryHolonomy, LongHorizonBoundaryError> {
    let generators = table.len() / states.len();
    for left in 0..generators {
        for right in left + 1..generators {
            for entering in states {
                let left_word = vec![left as u32, right as u32];
                let right_word = vec![right as u32, left as u32];
                let left_trace = trace(states, table, *entering, &left_word)?;
                let right_trace = trace(states, table, *entering, &right_word)?;
                let left_endpoint = *left_trace.last().ok_or(LongHorizonBoundaryError::Holonomy)?;
                let right_endpoint = *right_trace.last().ok_or(LongHorizonBoundaryError::Holonomy)?;
                if left_endpoint != right_endpoint && commutator_rank > 0 {
                    return Ok(OrderedBoundaryHolonomy {
                        entering: *entering,
                        left_word,
                        right_word,
                        left_trace,
                        right_trace,
                        left_endpoint,
                        right_endpoint,
                        commutator_rank,
                    });
                }
            }
        }
    }
    Err(LongHorizonBoundaryError::Holonomy)
}

fn trace(
    states: &[NativeStateId],
    table: &[u32],
    start: NativeStateId,
    word: &[u32],
) -> Result<Vec<NativeStateId>, LongHorizonBoundaryError> {
    let generators = table.len() / states.len();
    if start.0 as usize >= states.len()
        || word.iter().any(|generator| *generator as usize >= generators)
    {
        return Err(LongHorizonBoundaryError::Standing);
    }
    let mut state = start;
    let mut returned = vec![state];
    for generator in word {
        state = NativeStateId(
            table[*generator as usize * states.len() + state.0 as usize] as u64,
        );
        returned.push(state);
    }
    Ok(returned)
}

pub(super) fn digest(bytes: &[u8]) -> String {
    Sha256::digest(bytes)
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect()
}

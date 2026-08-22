//! Found the M3 native action on the card and recover its complete finite transition monoid.

use std::collections::{BTreeMap, VecDeque};

use holonic_engine::cuda_refine::{CudaRefineExecutor, DeviceNativeWord};
use holonic_engine::generator_native_rest::{GeneratorNativeRest, NativeGenerator};
use holonic_engine::receiver_exact_compression::{InputId, ObservedSystem, compress_on_device};
use holonic_engine::receiver_history_compression::{NativeStateId, ReceiverHistoryCompression};
use serde::Serialize;

use super::active_cover::{Recovery, StateAddress};

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct RecoveredRelation {
    pub word: Vec<InputId>,
    pub normal_form: Vec<InputId>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct TransitionMonoidReceipt {
    pub elements: usize,
    pub normal_forms: Vec<Vec<InputId>>,
    pub relations: Vec<RecoveredRelation>,
    pub exact_native_cell_reads: u64,
    pub dependency_span: usize,
    pub first_noncommuting_pair: Option<(Vec<InputId>, Vec<InputId>, NativeStateId)>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct CompressionApparatus {
    pub device: String,
    pub block_threads: u32,
    pub warp_size: u32,
    pub quotient_launches: u64,
    pub quotient_calls: u64,
    pub quotient_host_ingress_octets: u64,
    pub quotient_host_egress_octets: u64,
    pub quotient_resident_octets_peak: u64,
    pub native_word: NativeWordApparatus,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct NativeWordApparatus {
    pub word: Vec<InputId>,
    pub population: usize,
    pub launches: u64,
    pub host_ingress_octets: u64,
    pub host_egress_octets: u64,
    pub resident_octets: u64,
    pub returned_endpoints: Vec<NativeStateId>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct NativeSemanticWork {
    pub quotient_assignments: u64,
    pub receiver_factor_reads: u64,
    pub source_transport_reads: u64,
    pub native_transport_entries: u64,
    pub generator_square_checks: u64,
    pub transition_monoid_cell_reads: u64,
    pub native_word_transport_reads: u64,
    pub complete_decoder_factor_reads: u64,
    pub complete_decoder_fibre_members_returned: u64,
    pub dependency_span: usize,
}

#[derive(Serialize)]
pub struct M3Deed {
    pub history: ReceiverHistoryCompression,
    pub native_rest: GeneratorNativeRest,
    pub monoid: TransitionMonoidReceipt,
    pub apparatus: CompressionApparatus,
    pub semantic_work: NativeSemanticWork,
    pub source_states: Vec<StateAddress>,
}

pub fn conduct(recovery: &Recovery) -> Result<M3Deed, String> {
    let mut card = CudaRefineExecutor::new().map_err(|error| error.to_string())?;
    let before = card.launches();
    let exact =
        compress_on_device(&recovery.system, &mut card).map_err(|error| error.to_string())?;
    let quotient_launches = card.launches() - before;
    if quotient_launches % 2 != 0 {
        return Err("the 64-bit quotient did not return two launches per exact key".to_owned());
    }
    let history = ReceiverHistoryCompression::found(&recovery.system, &exact)
        .map_err(|error| error.to_string())?;
    if history.native_population.len() >= history.source_population.len() {
        return Err(
            "the M2 receiver/history quotient did not reduce the source population".to_owned(),
        );
    }

    let native_rest = GeneratorNativeRest::new(
        history.native_population.clone(),
        history.receiver_factors.clone(),
        history
            .generators
            .iter()
            .map(|square| NativeGenerator {
                generator: square.generator,
                transport: square.native.clone(),
            })
            .collect(),
    )
    .map_err(|error| error.to_string())?;
    let monoid = recover_monoid(&native_rest)?;

    // Exercise the deepest returned separator and both chart crossings. The depth is read from the
    // material; no authored iteration aperture selects it.
    let mut word = history
        .first_separators
        .iter()
        .max_by_key(|separator| separator.distinguishing_word.len())
        .map(|separator| separator.distinguishing_word.clone())
        .unwrap_or_default();
    for generator in history.generators.iter().map(|square| square.generator) {
        word.push(generator);
    }
    for generator in history
        .generators
        .iter()
        .rev()
        .map(|square| square.generator)
    {
        word.push(generator);
    }
    let generator_row = history
        .generators
        .iter()
        .enumerate()
        .map(|(row, square)| (square.generator, row as u32))
        .collect::<BTreeMap<_, _>>();
    let device_word = word
        .iter()
        .map(|generator| {
            generator_row
                .get(generator)
                .copied()
                .ok_or_else(|| format!("generator {:?} has no table row", generator))
        })
        .collect::<Result<Vec<_>, _>>()?;
    let table = native_table(&native_rest)?;
    let start = native_rest
        .native_population
        .iter()
        .map(|state| u32::try_from(state.0).map_err(|_| "native state exceeds u32".to_owned()))
        .collect::<Result<Vec<_>, _>>()?;

    // Independent exact admission reference, calculated once before dispatch. There is no host
    // semantic callback between device steps and no post-deed source replay.
    let expected = native_rest
        .native_population
        .iter()
        .map(|state| conduct_native(&history, *state, &word))
        .collect::<Result<Vec<_>, _>>()?;
    let device = card
        .conduct_native_word_on_device(
            native_rest.native_population.len(),
            native_rest.generators.len(),
            &table,
            &device_word,
            &start,
        )
        .map_err(|error| error.to_string())?;
    let returned_endpoints = device
        .native_end
        .iter()
        .map(|state| NativeStateId(u64::from(*state)))
        .collect::<Vec<_>>();
    if returned_endpoints != expected {
        return Err(
            "the resident native word return disagrees with its admitted exact action".to_owned(),
        );
    }

    // Inspect every returned state through every declared receiver. This executes the exterior
    // decoder on its complete image and returns every fibre member it refuses to choose between.
    let receivers = recovery.system.receivers();
    let mut complete_decoder_factor_reads = 0u64;
    let mut complete_decoder_fibre_members_returned = 0u64;
    for state in &returned_endpoints {
        for receiver in &receivers {
            let decoded = history
                .decode(*state, *receiver)
                .map_err(|error| error.to_string())?;
            complete_decoder_factor_reads += 1;
            complete_decoder_fibre_members_returned += decoded.reconstruction_fibre.len() as u64;
        }
    }

    let quotient_calls = quotient_launches / 2;
    let source_cells = history.source_population.len() as u64;
    let capacity = (history.source_population.len() + 1).next_power_of_two() as u64;
    let quotient_host_ingress_octets = quotient_calls * source_cells * 16;
    let quotient_host_egress_octets = quotient_calls * source_cells * 8;
    let quotient_resident_octets_peak = capacity * 8 + source_cells * 12;
    let native_word = apparatus_word(&word, &device);
    let construction = history.construction_work;
    let semantic_work = NativeSemanticWork {
        quotient_assignments: construction.quotient_assignments,
        receiver_factor_reads: construction.receiver_factor_reads,
        source_transport_reads: construction.source_transport_reads,
        native_transport_entries: construction.native_transport_entries,
        generator_square_checks: construction.generator_square_checks,
        transition_monoid_cell_reads: monoid.exact_native_cell_reads,
        native_word_transport_reads: (word.len() * history.native_population.len()) as u64,
        complete_decoder_factor_reads,
        complete_decoder_fibre_members_returned,
        dependency_span: monoid.dependency_span.max(word.len()),
    };
    Ok(M3Deed {
        history,
        native_rest,
        monoid,
        apparatus: CompressionApparatus {
            device: card.device_name().to_owned(),
            block_threads: card.block_threads(),
            warp_size: card.warp_size(),
            quotient_launches,
            quotient_calls,
            quotient_host_ingress_octets,
            quotient_host_egress_octets,
            quotient_resident_octets_peak,
            native_word,
        },
        semantic_work,
        source_states: recovery.states.clone(),
    })
}

fn conduct_native(
    history: &ReceiverHistoryCompression,
    mut state: NativeStateId,
    word: &[InputId],
) -> Result<NativeStateId, String> {
    for generator in word {
        state = history
            .native_step(state, *generator)
            .map_err(|error| error.to_string())?;
    }
    Ok(state)
}

fn native_table(rest: &GeneratorNativeRest) -> Result<Vec<u32>, String> {
    let mut returned = Vec::with_capacity(rest.generators.len() * rest.native_population.len());
    for generator in &rest.generators {
        for state in &rest.native_population {
            let target = generator
                .transport
                .iter()
                .find(|edge| edge.from == *state)
                .ok_or_else(|| {
                    format!(
                        "native generator {:?} omits state {:?}",
                        generator.generator, state
                    )
                })?
                .to;
            returned
                .push(u32::try_from(target.0).map_err(|_| "native state exceeds u32".to_owned())?);
        }
    }
    Ok(returned)
}

fn recover_monoid(rest: &GeneratorNativeRest) -> Result<TransitionMonoidReceipt, String> {
    let state_count = rest.native_population.len();
    let tables = rest
        .generators
        .iter()
        .map(|generator| {
            generator
                .transport
                .iter()
                .map(|edge| {
                    u32::try_from(edge.to.0).map_err(|_| "native state exceeds u32".to_owned())
                })
                .collect::<Result<Vec<_>, _>>()
        })
        .collect::<Result<Vec<_>, _>>()?;
    if tables.iter().any(|table| table.len() != state_count) {
        return Err("a native generator is not total on Q".to_owned());
    }
    let identity = (0..state_count as u32).collect::<Vec<_>>();
    let mut transformations = vec![identity.clone()];
    let mut normal_forms = vec![Vec::<InputId>::new()];
    let mut identity_of = BTreeMap::from([(identity, 0usize)]);
    let mut frontier = VecDeque::from([0usize]);
    let mut relations = Vec::new();
    let mut exact_native_cell_reads = 0u64;
    while let Some(current) = frontier.pop_front() {
        for (generator_at, generator) in rest.generators.iter().enumerate() {
            let next = transformations[current]
                .iter()
                .map(|state| {
                    exact_native_cell_reads += 1;
                    tables[generator_at][*state as usize]
                })
                .collect::<Vec<_>>();
            let mut word = normal_forms[current].clone();
            word.push(generator.generator);
            if let Some(existing) = identity_of.get(&next).copied() {
                if word != normal_forms[existing] {
                    relations.push(RecoveredRelation {
                        word,
                        normal_form: normal_forms[existing].clone(),
                    });
                }
            } else {
                let at = transformations.len();
                identity_of.insert(next.clone(), at);
                transformations.push(next);
                normal_forms.push(word);
                frontier.push_back(at);
            }
        }
    }
    let mut first_noncommuting_pair = None;
    'pair: for left in 0..rest.generators.len() {
        for right in left + 1..rest.generators.len() {
            for state in 0..state_count {
                let lr = tables[right][tables[left][state] as usize];
                let rl = tables[left][tables[right][state] as usize];
                if lr != rl {
                    first_noncommuting_pair = Some((
                        vec![
                            rest.generators[left].generator,
                            rest.generators[right].generator,
                        ],
                        vec![
                            rest.generators[right].generator,
                            rest.generators[left].generator,
                        ],
                        NativeStateId(state as u64),
                    ));
                    break 'pair;
                }
            }
        }
    }
    let dependency_span = normal_forms.iter().map(Vec::len).max().unwrap_or(0);
    Ok(TransitionMonoidReceipt {
        elements: transformations.len(),
        normal_forms,
        relations,
        exact_native_cell_reads,
        dependency_span,
        first_noncommuting_pair,
    })
}

fn apparatus_word(word: &[InputId], device: &DeviceNativeWord) -> NativeWordApparatus {
    NativeWordApparatus {
        word: word.to_vec(),
        population: device.native_end.len(),
        launches: device.launches,
        host_ingress_octets: device.host_ingress_octets,
        host_egress_octets: device.host_egress_octets,
        resident_octets: device.resident_octets,
        returned_endpoints: device
            .native_end
            .iter()
            .map(|state| NativeStateId(u64::from(*state)))
            .collect(),
    }
}

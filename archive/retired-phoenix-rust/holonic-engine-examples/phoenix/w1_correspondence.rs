//! Reusable W1 topology construction for the Gemma lift.
//!
//! This site owns neither source populations nor their payloads.  It only poses the foreign
//! operation complexes already founded by [`tower`], keeps the parametric family axes beside each
//! concrete deed, and returns the exact resident-law/port correspondence which a later rest deed
//! may consume.  In particular, the `1_466` figure is a boundary census, never an identity.

use std::collections::{BTreeMap, BTreeSet};

use holonic_engine::front_passage::ResidentRealization;
use holonic_engine::native_rest::{NativeLawIdentity, NativeOwnerIdentity};
use holonic_engine::operation_correspondence::{
    NativeGraphIdentity, NativeOperationBinding, OperationCorrespondence,
    OperationCorrespondenceSeal, OperationResolution, PopulationCorrespondence,
    PopulationResolution, PortCorrespondence, SourceOperationOccurrence, topology_identity,
};
use holonic_engine::ported_operation::PortedOperationComplex;
use holonic_engine::resident_section::{Dyadic, SeriesAperture};
use holonic_engine::source_occurrence::SourceOccurrence;

use super::{resident_layer, tower};
#[path = "modality.rs"]
mod modality;
use tower::{Entry, KvRole, Species};

/// The reusable W1 return. The complete source inventory is admitted by the later rest deed.
pub struct W1Topology {
    pub complexes: Vec<PortedOperationComplex>,
    pub correspondence: OperationCorrespondenceSeal,
    pub laws: Vec<NativeLawIdentity>,
    pub tilings: Vec<NativeOwnerIdentity>,
    pub reductions: Vec<NativeOwnerIdentity>,
}

/// Found all 42 layer deeds, the final boundary, and the two already-declared modality projection
/// deeds.  The only concrete extent supplied to `found_layer` is the one-position family sample;
/// `tokens` remains a family parameter and is not made part of graph identity by a count.
pub fn found(source: &mut SourceOccurrence) -> Result<W1Topology, String> {
    let result = found_inner(source);
    source.configuration_scope = vec!["text_config".to_owned()];
    result
}

fn found_inner(source: &mut SourceOccurrence) -> Result<W1Topology, String> {
    let scales = tower::algebraic_scales()?;
    let terms = SeriesAperture(14);
    let scalar = Dyadic::ONE;
    let mut entries: Vec<(
        String,
        String,
        BTreeMap<String, String>,
        PortedOperationComplex,
        ResidentRealization,
    )> = Vec::new();

    for layer in 0..tower::LAYERS {
        let entry = if layer == 0 {
            Entry::Rows
        } else {
            Entry::Carried
        };
        let founded = tower::found_layer(
            layer,
            entry,
            tower::Chart::Interval,
            &scales,
            terms,
            scalar,
            &tower::Intervention::None,
            1,
        )?;
        entries.push((
            format!("layer-{layer}"),
            format!("layer-family-{}", Species::of(layer).layer_type()),
            layer_parameters(layer),
            founded.complex,
            founded.realization,
        ));
    }

    let final_deed =
        tower::found_final(tower::Chart::Interval, &tower::Intervention::None, &scales)?;
    entries.push((
        "final-boundary".to_owned(),
        "final-boundary-family".to_owned(),
        BTreeMap::new(),
        final_deed.complex,
        final_deed.realization,
    ));

    for (modality, width, population) in [
        (
            "vision",
            768usize,
            "model.embed_vision.embedding_projection.weight",
        ),
        (
            "audio",
            1536usize,
            "model.embed_audio.embedding_projection.weight",
        ),
    ] {
        let eps = Dyadic::of_binary64_bits(resident_layer::EPS_BITS)
            .map_err(|error| error.to_string())?;
        let width_field = if modality == "vision" {
            "hidden_size"
        } else {
            "output_proj_dims"
        };
        let (complex, realization) =
            modality::found(modality, width, width_field, population, "1e-06", eps)?;
        let mut parameters = BTreeMap::new();
        parameters.insert("modality".to_owned(), modality.to_owned());
        parameters.insert("input_width".to_owned(), width.to_string());
        entries.push((
            format!("modality-{modality}"),
            "modality-projection-family".to_owned(),
            parameters,
            complex,
            realization,
        ));
    }

    let graph = aggregate_graph(&entries)?;
    let mut complexes = Vec::with_capacity(entries.len());
    let mut source_operations = Vec::new();
    let mut operation_rows = Vec::new();
    let mut carrier_set = BTreeSet::new();
    let mut laws_by_name = BTreeMap::<String, NativeLawIdentity>::new();

    for (deed, family, parameters, complex, realization) in entries {
        realization
            .validate(&complex)
            .map_err(|refusal| format!("{deed}: resident realization refused: {refusal:?}"))?;
        let scope = if deed == "final-boundary" || deed.starts_with("layer-") {
            "text_config"
        } else if deed == "modality-vision" {
            "vision_config"
        } else if deed == "modality-audio" {
            "audio_config"
        } else {
            return Err(format!("{deed}: no declared configuration scope"));
        };
        source.configuration_scope = vec![scope.to_owned()];
        let validations = source
            .validate(&complex)
            .map_err(|refusal| format!("{deed}: source testimony refused: {refusal:?}"))?;
        let occurrences = SourceOperationOccurrence::from_complex_family(
            deed.clone(),
            family,
            parameters,
            &complex,
        )
        .map_err(|refusal| format!("{deed}: source occurrence refused: {refusal:?}"))?;
        for source in &occurrences {
            if let Some(carrier) = &source.carrier {
                carrier_set.insert(carrier.clone());
            }
            let law = realization.bindings.get(&source.event).ok_or_else(|| {
                format!(
                    "{}: occurrence {:?} has no resident law",
                    source.id, source.event
                )
            })?;
            let validation = validations
                .iter()
                .find(|candidate| candidate.operation == source.operation)
                .ok_or_else(|| format!("{}: source validation is absent", source.id))?;
            if validation.species != law.species() {
                return Err(format!(
                    "{}: source species {:?} disagrees with resident law {:?}",
                    source.id,
                    validation.species,
                    law.species()
                ));
            }
            law.entailment(validation).map_err(|refusal| {
                format!(
                    "{}: resident law entailment refused: {refusal:?}",
                    source.id
                )
            })?;
            let binding = NativeOperationBinding {
                source_id: source.id.clone(),
                resident_law: law.name().to_owned(),
                species: law.species(),
                native_population: source.carrier.clone(),
                inputs: source
                    .inputs
                    .iter()
                    .enumerate()
                    .map(|(ordinal, name)| PortCorrespondence {
                        ordinal,
                        source: name.clone(),
                        native: name.clone(),
                    })
                    .collect(),
                outputs: source
                    .outputs
                    .iter()
                    .enumerate()
                    .map(|(ordinal, name)| PortCorrespondence {
                        ordinal,
                        source: name.clone(),
                        native: name.clone(),
                    })
                    .collect(),
                graph_key: graph.key.clone(),
            };
            operation_rows.push(OperationCorrespondence {
                source_id: source.id.clone(),
                resolution: OperationResolution::Native(binding),
            });
            let law_name = source.operation.clone();
            laws_by_name
                .entry(law_name.clone())
                .or_insert_with(|| NativeLawIdentity {
                    law: law_name,
                    species: law.species(),
                    owner: format!("phoenix.w1.resident-law::{}", law.name()),
                    graph_identity: graph.key.clone(),
                });
        }
        source_operations.extend(occurrences);
        complexes.push(complex);
    }

    let graph_key = graph.key.clone();
    let reduction_identity = graph.reductions.join("|");
    let carriers: Vec<String> = carrier_set.into_iter().collect();
    let populations = carriers
        .iter()
        .map(|name| PopulationCorrespondence {
            source_population: name.clone(),
            resolution: PopulationResolution::Native {
                native_population: name.clone(),
            },
        })
        .collect();
    let correspondence = OperationCorrespondenceSeal::new(
        source_operations,
        operation_rows,
        carriers.clone(),
        populations,
        vec![graph],
    )
    .seal()
    .map_err(|refusal| format!("W1 operation correspondence refused: {refusal:?}"))?;
    correspondence
        .validate()
        .map_err(|refusal| format!("W1 operation correspondence did not validate: {refusal:?}"))?;

    Ok(W1Topology {
        complexes,
        correspondence,
        laws: laws_by_name.into_values().collect(),
        tilings: vec![NativeOwnerIdentity {
            owner: "phoenix.w1.tower-tiling".to_owned(),
            identity: graph_key.clone(),
        }],
        reductions: vec![NativeOwnerIdentity {
            owner: "phoenix.w1.reduction-junction".to_owned(),
            identity: reduction_identity,
        }],
    })
}

fn layer_parameters(layer: usize) -> BTreeMap<String, String> {
    let mut parameters = BTreeMap::new();
    parameters.insert("layer".to_owned(), layer.to_string());
    parameters.insert(
        "species".to_owned(),
        Species::of(layer).layer_type().to_owned(),
    );
    parameters.insert(
        "head_width".to_owned(),
        Species::of(layer).head_width().to_string(),
    );
    parameters.insert("kv_role".to_owned(), format!("{:?}", KvRole::of(layer)));
    parameters.insert("tokens".to_owned(), "runtime extent".to_owned());
    parameters
}

fn aggregate_graph(
    entries: &[(
        String,
        String,
        BTreeMap<String, String>,
        PortedOperationComplex,
        ResidentRealization,
    )],
) -> Result<NativeGraphIdentity, String> {
    let mut nodes = 0u64;
    let mut edges = 0u64;
    let mut chronology = Vec::new();
    let mut topology = Vec::new();
    for (deed, family, _, complex, _) in entries {
        let closure = complex
            .closure()
            .map_err(|error| format!("{deed}: closure: {error}"))?;
        nodes += closure.occurrences as u64;
        edges +=
            (complex.shape.interactions.len() + complex.shape.chronology.precedence.len()) as u64;
        let addressed_chronology = serde_json::to_string(&complex.shape.chronology)
            .map_err(|error| format!("{deed}: chronology serialization: {error}"))?;
        let addressed_bonds = serde_json::to_string(&complex.shape.interactions)
            .map_err(|error| format!("{deed}: interaction serialization: {error}"))?;
        chronology.push(format!("{deed}:{family}:chronology={addressed_chronology}"));
        chronology.push(format!("{deed}:{family}:bonds={addressed_bonds}"));
        topology.push(format!(
            "{deed}:{family}:topology-identity={}",
            topology_identity(complex)
        ));
    }
    chronology.sort();
    topology.sort();
    let reductions = vec![
        "precedence-junction".to_owned(),
        "front-assembly".to_owned(),
    ];
    Ok(NativeGraphIdentity::derived_with_topology(
        nodes,
        edges,
        "phoenix-w1/42-layer+final+2-modality/co-present-fronts",
        reductions,
        chronology,
        topology,
    ))
}

//! Receiver-relative cultivation for Athena alpha.
//!
//! This owner does not store exchanges. It finds recurring prompt faces across the complete
//! addressed aperture, recovers local token transports recurring across plural returned defects,
//! and binds each retained word to its complete parent family. Occurrence chronology remains causal
//! order; provider, file kind and transcript location never route conduct.

use std::collections::{BTreeMap, BTreeSet};

use serde::{Deserialize, Serialize};

use crate::{
    causal_language::lexical_tokens,
    exchange_world_tube::{
        ContinuationAperture, ContinuationFamily, ContinuationPartition, ExchangeWorldTube,
        VisibleMessageFace,
    },
    morphological_language::{MorphologicalGenerator, MorphologicalGeneratorRest},
};

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct GeneratorCondensationReceipt {
    pub schema: String,
    pub complete_exchange_families: usize,
    pub development_families: usize,
    pub response_sections_received: usize,
    pub heldout_or_control_response_sections_received: usize,
    pub recurring_transport_words: usize,
    pub generators: usize,
    pub recurring_route_features: usize,
    pub collapsed_occurrence_population: u64,
    pub language_families: usize,
    pub mathematical_families: usize,
    pub code_families: usize,
    pub exact_duplicate_realizations_collapsed: usize,
    pub chronology_preserved: bool,
    pub provider_or_material_kind_routed: bool,
    pub source_passages_retained: bool,
    pub open_fibres: Vec<String>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct EdgeAccumulator {
    causal_ordinal: u64,
    parent_defect_fibres: BTreeSet<String>,
    left_boundary_parent_fibres: BTreeSet<String>,
    left_boundary_occurrences: BTreeSet<String>,
    response_occurrences: BTreeSet<String>,
    route_support: BTreeMap<String, BTreeSet<String>>,
    tokens: Vec<String>,
    occurrence_population: u64,
    mathematical: bool,
    code: bool,
}

/// Condense the complete development return family into proper generator-native morphology.
/// `parent_defects` is keyed by continuation-family occurrence and must cover every development
/// family which contributes a generator.
pub fn condense_returned_generators(
    world: &ExchangeWorldTube,
    aperture: &ContinuationAperture,
    predecessor_product_sha256: String,
    parent_defects: &BTreeMap<String, String>,
    organ_features: &BTreeMap<String, BTreeSet<String>>,
) -> Result<(MorphologicalGeneratorRest, GeneratorCondensationReceipt), String> {
    let mut developments = aperture
        .families
        .iter()
        .filter(|family| family.partition == ContinuationPartition::Development)
        .collect::<Vec<_>>();
    developments.sort_by_key(|family| family.prompt.visible_index);
    let feature_support = prompt_feature_support(world, &developments)?;
    let recurring_features = feature_support
        .iter()
        .filter_map(|(feature, parents)| (parents.len() >= 2).then_some(feature.clone()))
        .collect::<BTreeSet<_>>();
    let whole_source_passages = world
        .visible_messages
        .iter()
        .map(|face| lexical_tokens(&face.text))
        .filter(|tokens| tokens.len() == 3)
        .collect::<BTreeSet<_>>();
    let mut edges = BTreeMap::<Vec<String>, EdgeAccumulator>::new();
    let mut feature_response_support = BTreeMap::<String, BTreeSet<String>>::new();
    let mut open = Vec::new();
    let mut response_sections = 0usize;
    for family in &developments {
        let prompt = visible(world, family.prompt.visible_index)?;
        let all_prompt_features = word_features(&prompt.text);
        let prompt_features = all_prompt_features
            .intersection(&recurring_features)
            .cloned()
            .collect::<BTreeSet<_>>();
        let parent = parent_defects.get(&family.occurrence).ok_or_else(|| {
            format!(
                "development family {} has no returned AA1 defect parent",
                family.occurrence
            )
        })?;
        for address in &family.response {
            response_sections += 1;
            let response = visible(world, address.visible_index)?;
            let tokens = lexical_tokens(&response.text);
            if tokens.len() < 3 {
                continue;
            }
            let mut routes = prompt_features.clone();
            if let Some(features) = organ_features.get(&family.occurrence) {
                routes.extend(features.iter().cloned());
            }
            let response_is_code = response.text.contains("```");
            for route in &routes {
                feature_response_support
                    .entry(route.clone())
                    .or_default()
                    .insert(address.occurrence.clone());
            }
            for (at, word) in tokens.windows(3).enumerate() {
                let pair = word.to_vec();
                let left_boundary = at == 0 || is_sentence_boundary(&tokens[at - 1]);
                let mathematical = pair.iter().any(|token| {
                    token.chars().any(|ch| ch.is_ascii_digit())
                        || matches!(
                            token.as_str(),
                            "=" | "+" | "-" | "*" | "/" | "^" | "∫" | "∂"
                        )
                });
                let code = response_is_code
                    || pair
                        .iter()
                        .any(|token| matches!(token.as_str(), "::" | "{" | "}"));
                let edge = edges
                    .entry(pair.clone())
                    .or_insert_with(|| EdgeAccumulator {
                        causal_ordinal: address.visible_index,
                        parent_defect_fibres: BTreeSet::new(),
                        left_boundary_parent_fibres: BTreeSet::new(),
                        left_boundary_occurrences: BTreeSet::new(),
                        response_occurrences: BTreeSet::new(),
                        route_support: BTreeMap::new(),
                        tokens: pair,
                        occurrence_population: 0,
                        mathematical: false,
                        code: false,
                    });
                edge.causal_ordinal = edge.causal_ordinal.min(address.visible_index);
                edge.parent_defect_fibres.insert(parent.clone());
                if left_boundary {
                    edge.left_boundary_parent_fibres.insert(parent.clone());
                    edge.left_boundary_occurrences
                        .insert(address.occurrence.clone());
                }
                edge.response_occurrences.insert(address.occurrence.clone());
                edge.occurrence_population = edge.occurrence_population.saturating_add(1);
                edge.mathematical |= mathematical;
                edge.code |= code;
                for route in &routes {
                    edge.route_support
                        .entry(route.clone())
                        .or_default()
                        .insert(address.occurrence.clone());
                }
            }
        }
    }

    // A native word exists only when the same two-edge transport triangle crosses plural response occurrences
    // and plural returned defect parents. Its route faces must themselves recur on that edge;
    // otherwise the edge's own surface is the only lawful local contact. Unique source sentences
    // and their proper prefixes never enter the rest.
    let mut language_families = 0usize;
    let mut mathematics_families = 0usize;
    let mut code_families = 0usize;
    let mut collapsed_population = 0u64;
    let mut duplicates = 0usize;
    let mut generators = Vec::new();
    let mut nonrecurring_edges = 0usize;
    for (_, edge) in edges {
        if whole_source_passages.contains(&edge.tokens)
            || edge.parent_defect_fibres.len() < 2
            || edge.response_occurrences.len() < 2
        {
            nonrecurring_edges += 1;
            continue;
        }
        if edge
            .tokens
            .iter()
            .filter(|token| token.chars().any(char::is_alphanumeric))
            .count()
            < 2
        {
            nonrecurring_edges += 1;
            continue;
        }
        let edge_response_population = edge.response_occurrences.len() as u128;
        let total_response_population = response_sections as u128;
        let mut routes = edge
            .route_support
            .into_iter()
            .filter_map(|(feature, occurrences)| {
                let feature_population = feature_response_support
                    .get(&feature)
                    .map_or(0, BTreeSet::len) as u128;
                let joint_population = occurrences.len() as u128;
                (occurrences.len() >= 2
                    && joint_population.saturating_mul(total_response_population)
                        > edge_response_population.saturating_mul(feature_population))
                .then_some(feature)
            })
            .collect::<BTreeSet<_>>();
        if routes.is_empty() {
            routes.extend(
                edge.tokens
                    .iter()
                    .filter(|token| token.chars().all(char::is_alphanumeric))
                    .map(|token| token.to_lowercase()),
            );
        }
        if routes.is_empty() {
            nonrecurring_edges += 1;
            continue;
        }
        collapsed_population = collapsed_population.saturating_add(edge.occurrence_population);
        duplicates = duplicates.saturating_add(
            usize::try_from(edge.occurrence_population.saturating_sub(1))
                .map_err(|_| "recurring edge population left usize".to_owned())?,
        );
        language_families += 1;
        mathematics_families += usize::from(edge.mathematical);
        code_families += usize::from(edge.code);
        generators.push(MorphologicalGenerator::found(
            edge.causal_ordinal,
            edge.parent_defect_fibres.clone(),
            edge.left_boundary_parent_fibres,
            edge.left_boundary_occurrences.len() as u64,
            routes,
            edge.tokens,
            edge.parent_defect_fibres.len() as u64,
            edge.occurrence_population,
            true,
        )?);
    }
    open.push(format!(
        "{nonrecurring_edges} unique or single-parent token transports remain in the source reconstruction fibre and do not enter native hexis"
    ));
    let rest =
        MorphologicalGeneratorRest::seal(predecessor_product_sha256, generators, open.clone())?;
    let receipt = GeneratorCondensationReceipt {
        schema: "soma-life.athena-alpha-generator-condensation.v1".to_owned(),
        complete_exchange_families: aperture.families.len(),
        development_families: developments.len(),
        response_sections_received: response_sections,
        heldout_or_control_response_sections_received: 0,
        recurring_transport_words: rest.generators.len(),
        generators: rest.generators.len(),
        recurring_route_features: rest
            .generators
            .iter()
            .flat_map(|generator| generator.routing_features.iter())
            .collect::<BTreeSet<_>>()
            .len(),
        collapsed_occurrence_population: collapsed_population,
        language_families,
        mathematical_families: mathematics_families,
        code_families,
        exact_duplicate_realizations_collapsed: duplicates,
        chronology_preserved: rest
            .generators
            .windows(2)
            .all(|pair| pair[0].causal_ordinal <= pair[1].causal_ordinal),
        provider_or_material_kind_routed: false,
        source_passages_retained: false,
        open_fibres: open,
    };
    Ok((rest, receipt))
}

fn prompt_feature_support(
    world: &ExchangeWorldTube,
    families: &[&ContinuationFamily],
) -> Result<BTreeMap<String, BTreeSet<String>>, String> {
    let mut support = BTreeMap::<String, BTreeSet<String>>::new();
    for family in families {
        let prompt = visible(world, family.prompt.visible_index)?;
        for feature in word_features(&prompt.text) {
            support
                .entry(feature)
                .or_default()
                .insert(family.occurrence.clone());
        }
    }
    Ok(support)
}

fn word_features(text: &str) -> BTreeSet<String> {
    lexical_tokens(text)
        .into_iter()
        .filter(|token| token.chars().all(char::is_alphanumeric))
        .map(|token| token.to_lowercase())
        .collect()
}

fn is_sentence_boundary(token: &str) -> bool {
    matches!(token, "." | "!" | "?")
}

fn visible(world: &ExchangeWorldTube, index: u64) -> Result<&VisibleMessageFace, String> {
    world
        .visible_messages
        .get(index as usize)
        .ok_or_else(|| format!("visible message {index} left the complete exchange aperture"))
}

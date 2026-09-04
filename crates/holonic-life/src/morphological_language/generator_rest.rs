//! Generator-native rest for a condensed morphological-language ecology.
//!
//! The rest cannot represent source passages, prompt strings, response lookups or provider faces.
//! It carries only recurring proper continuation generators and the receiver features through
//! which later current may contact them. Remount reconstructs the existing morphological owner on
//! the resident card; no developmental exchange source is consulted.

use std::{
    cmp::Reverse,
    collections::{BTreeMap, BTreeSet},
};

use body::num::Cog;
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use soma_abi::active::ActionCurrent;

use crate::causal_language::{lexical_tokens, render_tokens};

use super::{
    CudaMorphologicalConditioner, MorphologicalConditionApparatusReceipt,
    MorphologicalConditionSemanticReceipt, MorphologicalLanguageEcology,
    MorphologicalLanguageError, MorphologicalLanguagePassage,
};

pub const MORPHOLOGICAL_GENERATOR_REST_SCHEMA: &str =
    "soma-life.morphological-generator-native-rest.v1";
const GENERATOR_RECEIVER: u64 = 0x414c_5048_4147_454e;

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct MorphologicalGenerator {
    pub identity_sha256: String,
    /// Causal position of the first developmental return which founded this generator. It is not
    /// a caller-selected training order: the complete exchange aperture supplies it.
    pub causal_ordinal: u64,
    /// Canonical identity of the complete plural AA1 parent-defect family below.
    pub parent_defect_sha256: String,
    /// Complete plural AA1 defect family over which this transport triangle recurred. The singular
    /// address above is the canonical identity of this set, never a selected representative.
    pub parent_defect_fibres: BTreeSet<String>,
    /// Parent defects in which this local triangle begins immediately after an admitted sentence
    /// boundary. Plural support lets inference enter at a founded boundary without storing the
    /// sentence which followed it.
    pub left_boundary_parent_fibres: BTreeSet<String>,
    pub left_boundary_occurrence_population: u64,
    pub routing_features: BTreeSet<String>,
    pub tokens: Vec<String>,
    pub distinct_parent_fibres: u64,
    pub collapsed_occurrence_population: u64,
    pub proper_subcontinuation: bool,
}

impl MorphologicalGenerator {
    pub fn found(
        causal_ordinal: u64,
        parent_defect_fibres: BTreeSet<String>,
        left_boundary_parent_fibres: BTreeSet<String>,
        left_boundary_occurrence_population: u64,
        routing_features: BTreeSet<String>,
        tokens: Vec<String>,
        distinct_parent_fibres: u64,
        collapsed_occurrence_population: u64,
        proper_subcontinuation: bool,
    ) -> Result<Self, String> {
        let parent_defect_sha256 = parent_family_identity(&parent_defect_fibres);
        let identity_sha256 = generator_identity(
            causal_ordinal,
            &parent_defect_fibres,
            &left_boundary_parent_fibres,
            left_boundary_occurrence_population,
            &routing_features,
            &tokens,
        );
        let generator = Self {
            identity_sha256,
            causal_ordinal,
            parent_defect_sha256,
            parent_defect_fibres,
            left_boundary_parent_fibres,
            left_boundary_occurrence_population,
            routing_features,
            tokens,
            distinct_parent_fibres,
            collapsed_occurrence_population,
            proper_subcontinuation,
        };
        generator.validate()?;
        Ok(generator)
    }

    fn validate(&self) -> Result<(), String> {
        if self.identity_sha256
            != generator_identity(
                self.causal_ordinal,
                &self.parent_defect_fibres,
                &self.left_boundary_parent_fibres,
                self.left_boundary_occurrence_population,
                &self.routing_features,
                &self.tokens,
            )
            || self.parent_defect_sha256 != parent_family_identity(&self.parent_defect_fibres)
            || self.parent_defect_fibres.len() < 2
            || self
                .parent_defect_fibres
                .iter()
                .any(|parent| parent.len() != 64)
            || !self
                .left_boundary_parent_fibres
                .is_subset(&self.parent_defect_fibres)
            || self
                .left_boundary_parent_fibres
                .iter()
                .any(|parent| parent.len() != 64)
            || self.left_boundary_occurrence_population
                < self.left_boundary_parent_fibres.len() as u64
            || self.routing_features.is_empty()
            || self
                .routing_features
                .iter()
                .any(|feature| feature.is_empty() || feature.chars().any(char::is_uppercase))
            || self.tokens.len() != 3
            || self.tokens.iter().any(String::is_empty)
            || self
                .tokens
                .iter()
                .filter(|token| token.chars().any(char::is_alphanumeric))
                .count()
                < 2
            || self.distinct_parent_fibres < 2
            || self.collapsed_occurrence_population < self.distinct_parent_fibres
            || !self.proper_subcontinuation
        {
            return Err(format!(
                "malformed recurring morphological generator {}",
                self.identity_sha256
            ));
        }
        Ok(())
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct MorphologicalGeneratorRest {
    pub schema: String,
    pub predecessor_product_sha256: String,
    pub generators: Vec<MorphologicalGenerator>,
    pub open_fibres: Vec<String>,
}

impl MorphologicalGeneratorRest {
    pub fn seal(
        predecessor_product_sha256: String,
        mut generators: Vec<MorphologicalGenerator>,
        open_fibres: Vec<String>,
    ) -> Result<Self, String> {
        generators.sort_by(|left, right| {
            (left.causal_ordinal, left.identity_sha256.as_str())
                .cmp(&(right.causal_ordinal, right.identity_sha256.as_str()))
        });
        let rest = Self {
            schema: MORPHOLOGICAL_GENERATOR_REST_SCHEMA.to_owned(),
            predecessor_product_sha256,
            generators,
            open_fibres,
        };
        rest.validate()?;
        Ok(rest)
    }

    pub fn read(bytes: &[u8]) -> Result<Self, String> {
        let rest: Self = serde_json::from_slice(bytes).map_err(|error| error.to_string())?;
        rest.validate()?;
        Ok(rest)
    }

    pub fn canonical_bytes(&self) -> Result<Vec<u8>, String> {
        self.validate()?;
        serde_json::to_vec(self).map_err(|error| error.to_string())
    }

    pub fn derived_generation_aperture(&self) -> usize {
        let distances = closing_distances(&self.generators);
        self.generators
            .iter()
            .filter_map(|generator| distances.get(&generator.tokens[..2]).copied())
            .max()
            .and_then(|distance| distance.checked_add(2))
            .unwrap_or(1)
    }

    /// Earliest proper closure in the maximal active receiver cover.
    ///
    /// This is not a caller-authored response length. Prompt and native-organ incidence determine
    /// each generator's contacted face; the largest incidence population establishes the receiver
    /// section; the earliest sentence that section can actually return supplies the horizon. The
    /// larger continuations remain in the reconstruction fibre rather than being enumerated into
    /// host memory before one complete answer can return.
    pub fn derived_generation_aperture_for(
        &self,
        prompt: &str,
        native_features: &BTreeSet<String>,
    ) -> usize {
        let mut active = lexical_tokens(prompt)
            .into_iter()
            .filter(|token| token.chars().all(char::is_alphanumeric))
            .map(|token| token.to_lowercase())
            .collect::<BTreeSet<_>>();
        active.extend(native_features.iter().cloned());
        self.restrict_to_active_receiver(&active, native_features)
            .map_or(1, |(restricted, _)| {
                restricted.derived_generation_aperture()
            })
    }

    /// Condense this rested ecology through one declared prompt/native receiver before remount.
    /// Every retained generator carries the largest active incidence population and reaches the
    /// earliest proper closure in that cover. Excluded generators remain named as one reopened
    /// reconstruction fibre; they are not declared false or deleted from the canonical rest.
    pub fn restrict_to_receiver(
        &self,
        prompt: &str,
        native_features: &BTreeSet<String>,
    ) -> Result<Self, String> {
        let mut active = lexical_tokens(prompt)
            .into_iter()
            .filter(|token| token.chars().all(char::is_alphanumeric))
            .map(|token| token.to_lowercase())
            .collect::<BTreeSet<_>>();
        active.extend(native_features.iter().cloned());
        self.restrict_to_active_receiver(&active, native_features)
            .map(|(restricted, _)| restricted)
    }

    pub fn restrict_to_receiver_with_contact(
        &self,
        prompt: &str,
        native_features: &BTreeSet<String>,
    ) -> Result<(Self, BTreeSet<String>), String> {
        let mut active = lexical_tokens(prompt)
            .into_iter()
            .filter(|token| token.chars().all(char::is_alphanumeric))
            .map(|token| token.to_lowercase())
            .collect::<BTreeSet<_>>();
        active.extend(native_features.iter().cloned());
        self.restrict_to_active_receiver(&active, native_features)
    }

    fn restrict_to_active_receiver(
        &self,
        active: &BTreeSet<String>,
        preferred: &BTreeSet<String>,
    ) -> Result<(Self, BTreeSet<String>), String> {
        let distances = closing_distances(&self.generators);
        let contacted = self
            .generators
            .iter()
            .map(|generator| {
                (
                    generator.routing_features.intersection(&active).count(),
                    generator,
                )
            })
            .filter(|(population, generator)| {
                *population > 0 && generator_closing_distance(generator, &distances).is_some()
            })
            .collect::<Vec<_>>();
        let maximum_cover = contacted
            .iter()
            .map(|(population, _)| *population)
            .max()
            .ok_or_else(|| "the receiver contacted no cultivated generator".to_owned())?;
        let boundary_founded = contacted.iter().any(|(population, generator)| {
            *population == maximum_cover && generator.left_boundary_parent_fibres.len() >= 2
        });
        let earliest_closure = contacted
            .iter()
            .filter(|(population, generator)| {
                *population == maximum_cover
                    && (!boundary_founded || generator.left_boundary_parent_fibres.len() >= 2)
            })
            .filter_map(|(_, generator)| generator_closing_distance(generator, &distances))
            .min()
            .ok_or_else(|| "the maximal receiver cover has no proper closure".to_owned())?;
        let seed = contacted
            .into_iter()
            .filter(|(population, generator)| {
                *population == maximum_cover
                    && (!boundary_founded || generator.left_boundary_parent_fibres.len() >= 2)
                    && generator_closing_distance(generator, &distances) == Some(earliest_closure)
            })
            .max_by_key(|(_, generator)| {
                (
                    generator.left_boundary_parent_fibres.len(),
                    generator.distinct_parent_fibres,
                    generator.collapsed_occurrence_population,
                    Reverse(generator.causal_ordinal),
                    Reverse(generator.identity_sha256.as_str()),
                )
            })
            .map(|(_, generator)| generator)
            .ok_or_else(|| "the maximal receiver cover has no founded seed".to_owned())?;
        let complete_contact = seed
            .routing_features
            .intersection(active)
            .cloned()
            .collect::<BTreeSet<_>>();
        let preferred_contact = complete_contact
            .intersection(preferred)
            .cloned()
            .collect::<BTreeSet<_>>();
        let separator_pool = if preferred_contact.is_empty() {
            &complete_contact
        } else {
            &preferred_contact
        };
        let separator = separator_pool
            .iter()
            .min_by_key(|feature| {
                (
                    self.generators
                        .iter()
                        .filter(|generator| generator.routing_features.contains(*feature))
                        .count(),
                    feature.as_str(),
                )
            })
            .ok_or_else(|| "the selected receiver section has no separating contact".to_owned())?
            .clone();
        let contact_features = BTreeSet::from([separator]);
        let mut retained = BTreeSet::new();
        let mut current = seed;
        loop {
            retained.insert(current.identity_sha256.clone());
            if is_sentence_boundary(&current.tokens[2]) {
                break;
            }
            let current_distance = generator_closing_distance(current, &distances)
                .ok_or_else(|| "the selected generator left its closing section".to_owned())?;
            let next_face = &current.tokens[1..];
            let next = self
                .generators
                .iter()
                .filter(|candidate| candidate.tokens[..2] == *next_face)
                .filter(|candidate| {
                    generator_closing_distance(candidate, &distances)
                        .and_then(|distance| distance.checked_add(1))
                        == Some(current_distance)
                })
                .max_by_key(|candidate| {
                    let shared_parents = candidate
                        .parent_defect_fibres
                        .intersection(&current.parent_defect_fibres)
                        .count();
                    let active_cover = candidate.routing_features.intersection(active).count();
                    let forward = candidate.causal_ordinal >= current.causal_ordinal;
                    let separation = candidate.causal_ordinal.abs_diff(current.causal_ordinal);
                    (
                        shared_parents,
                        active_cover,
                        forward,
                        Reverse(separation),
                        candidate.distinct_parent_fibres,
                        candidate.collapsed_occurrence_population,
                        Reverse(candidate.identity_sha256.as_str()),
                    )
                })
                .ok_or_else(|| "the selected generator has no closing successor".to_owned())?;
            current = next;
        }
        let generators = self
            .generators
            .iter()
            .filter(|generator| retained.contains(&generator.identity_sha256))
            .cloned()
            .collect::<Vec<_>>();
        let excluded = self.generators.len().saturating_sub(generators.len());
        let mut open_fibres = self.open_fibres.clone();
        if complete_contact.len() > contact_features.len() {
            open_fibres.push(format!(
                "{} co-contacting receiver features factor through the selected shortest separator and remain available for a wider inspection",
                complete_contact.len() - contact_features.len()
            ));
        }
        if excluded > 0 {
            open_fibres.push(format!(
                "{excluded} cultivated generators lie outside this receiver's maximal earliest-closure section and reopen when its receiver family widens"
            ));
        }
        let restricted = Self::seal(
            self.predecessor_product_sha256.clone(),
            generators,
            open_fibres,
        )?;
        Ok((restricted, contact_features))
    }

    pub fn mount_on_device(
        &self,
        contact_features: &BTreeSet<String>,
        conditioner: &mut CudaMorphologicalConditioner,
    ) -> Result<
        (
            MorphologicalLanguageEcology,
            MorphologicalConditionSemanticReceipt,
            MorphologicalConditionApparatusReceipt,
        ),
        MorphologicalLanguageError,
    > {
        if contact_features.is_empty() {
            return Err(MorphologicalLanguageError::MalformedFiber);
        }
        let passages = self
            .generators
            .iter()
            .map(|generator| {
                MorphologicalLanguagePassage::new(
                    generator.identity_sha256.clone(),
                    format!("native-generator/{}", generator.identity_sha256),
                    GENERATOR_RECEIVER,
                    render_tokens(generator.tokens.iter().map(String::as_str)),
                )
                .with_routing_features(contact_features.iter().cloned())
            })
            .collect::<Vec<_>>();
        let action =
            ActionCurrent::new(Cog::lit(1)).ok_or(MorphologicalLanguageError::CarrierExtent)?;
        MorphologicalLanguageEcology::condition_with_cuda(&passages, action, conditioner)
    }

    fn validate(&self) -> Result<(), String> {
        if self.schema != MORPHOLOGICAL_GENERATOR_REST_SCHEMA
            || self.predecessor_product_sha256.len() != 64
            || self.generators.is_empty()
        {
            return Err("malformed morphological generator rest boundary".to_owned());
        }
        let mut identities = BTreeSet::new();
        for generator in &self.generators {
            generator.validate()?;
            if !identities.insert(&generator.identity_sha256) {
                return Err("morphological generator rest repeats one identity".to_owned());
            }
        }
        if self.generators.windows(2).any(|pair| {
            (pair[0].causal_ordinal, pair[0].identity_sha256.as_str())
                > (pair[1].causal_ordinal, pair[1].identity_sha256.as_str())
        }) {
            return Err("morphological generator rest moved against causal order".to_owned());
        }
        Ok(())
    }
}

fn closing_distances(generators: &[MorphologicalGenerator]) -> BTreeMap<Vec<String>, usize> {
    let mut distances = BTreeMap::new();
    for generator in generators {
        if is_sentence_boundary(&generator.tokens[2]) {
            distances
                .entry(generator.tokens[..2].to_vec())
                .and_modify(|distance: &mut usize| *distance = (*distance).min(1))
                .or_insert(1);
        }
    }
    loop {
        let mut changed = false;
        for generator in generators {
            let Some(next) = distances.get(&generator.tokens[1..]).copied() else {
                continue;
            };
            let Some(candidate) = next.checked_add(1) else {
                continue;
            };
            match distances.get_mut(&generator.tokens[..2]) {
                Some(current) if candidate < *current => {
                    *current = candidate;
                    changed = true;
                }
                None => {
                    distances.insert(generator.tokens[..2].to_vec(), candidate);
                    changed = true;
                }
                _ => {}
            }
        }
        if !changed {
            break;
        }
    }
    distances
}

fn generator_closing_distance(
    generator: &MorphologicalGenerator,
    distances: &BTreeMap<Vec<String>, usize>,
) -> Option<usize> {
    let distance = if is_sentence_boundary(&generator.tokens[2]) {
        1
    } else {
        distances.get(&generator.tokens[1..])?.checked_add(1)?
    };
    (distances.get(&generator.tokens[..2]) == Some(&distance)).then_some(distance)
}

fn is_sentence_boundary(token: &str) -> bool {
    matches!(token, "." | "!" | "?")
}

fn generator_identity(
    causal_ordinal: u64,
    parent_defect_fibres: &BTreeSet<String>,
    left_boundary_parent_fibres: &BTreeSet<String>,
    left_boundary_occurrence_population: u64,
    features: &BTreeSet<String>,
    tokens: &[String],
) -> String {
    let mut digest = Sha256::new();
    digest.update(b"morphological-generator-native/v1");
    digest.update(causal_ordinal.to_le_bytes());
    for parent in parent_defect_fibres {
        digest.update((parent.len() as u64).to_le_bytes());
        digest.update(parent.as_bytes());
    }
    for parent in left_boundary_parent_fibres {
        digest.update((parent.len() as u64).to_le_bytes());
        digest.update(parent.as_bytes());
    }
    digest.update(left_boundary_occurrence_population.to_le_bytes());
    for feature in features {
        digest.update((feature.len() as u64).to_le_bytes());
        digest.update(feature.as_bytes());
    }
    for token in tokens {
        digest.update((token.len() as u64).to_le_bytes());
        digest.update(token.as_bytes());
    }
    hex(&digest.finalize())
}

fn parent_family_identity(parents: &BTreeSet<String>) -> String {
    let mut digest = Sha256::new();
    digest.update(b"morphological-generator-parent-family/v1");
    for parent in parents {
        digest.update((parent.len() as u64).to_le_bytes());
        digest.update(parent.as_bytes());
    }
    hex(&digest.finalize())
}

fn hex(bytes: &[u8]) -> String {
    const DIGITS: &[u8; 16] = b"0123456789abcdef";
    let mut rendered = String::with_capacity(bytes.len() * 2);
    for byte in bytes {
        rendered.push(DIGITS[(byte >> 4) as usize] as char);
        rendered.push(DIGITS[(byte & 15) as usize] as char);
    }
    rendered
}

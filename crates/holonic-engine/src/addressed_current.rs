//! Exact dynamic current as one addressed passage.
//!
//! A section is an exact weighted integral current on a founded incidence population. A passage
//! carries every `(source, generator)` occurrence to one ordered target section, retains both
//! boundary maps, and returns the complete reconstruction fibre. This is the apparatus-neutral
//! law enacted by a resident accelerator; buffer placement and synchronization are separate
//! testimony.

use std::collections::{BTreeMap, BTreeSet};

use num_bigint::BigUint;
use num_traits::Zero;
use serde::{Deserialize, Serialize};
use thiserror::Error;

/// One exact current section and the reconstruction-fibre mass carried by it.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct AddressedCurrentSection {
    /// Exact causal-state coordinate when the current crossed a state-bearing boundary chart.
    /// `None` means that this current's typed port carries no such coordinate; it is not state 0.
    pub boundary_state: Option<u32>,
    pub quadratic_weight: BigUint,
    pub factor_current: Vec<(u32, BigUint)>,
}

impl AddressedCurrentSection {
    fn validate(&self, factor_population: u32) -> Result<(), AddressedCurrentPassageError> {
        if self.quadratic_weight.is_zero()
            || self.factor_current.is_empty()
            || self
                .factor_current
                .windows(2)
                .any(|pair| pair[0].0 >= pair[1].0)
            || self
                .factor_current
                .iter()
                .any(|(factor, coefficient)| *factor >= factor_population || coefficient.is_zero())
        {
            return Err(AddressedCurrentPassageError::Section);
        }
        Ok(())
    }
}

/// One occurrence in the complete source-section × generator population.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct AddressedCurrentOccurrence {
    pub source_section: u32,
    pub generator: u32,
    pub target_section: u32,
}

/// One selected native higher-face restriction. `source_boundary_state` addresses the incidence
/// at which the restriction may meet a source section; `boundary_state` is its transported target
/// address. Cross-state source/slot pairs are the exact radical complement derived from these two
/// addressed populations and are not materialized as an ambient rectangular occurrence matrix.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct AddressedGeneratedPortSlot {
    pub port: u32,
    pub generator: u32,
    pub source_boundary_state: u32,
    pub boundary_state: u32,
    pub restriction: Vec<(u32, BigUint)>,
}

/// One occurrence in the complete source-section × selected generated-port-slot population.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct AddressedGeneratedPortCurrentOccurrence {
    pub source_section: u32,
    pub selected_slot: u32,
    /// `None` is an exact radical occurrence: the selected restriction annihilated this source
    /// section.  It remains in the reconstruction fibre but contributes no hot rank-one row.
    pub target_section: Option<u32>,
    /// Exact positive scale removed before the target projective current continued.  A radical
    /// occurrence carries zero.  The target quadratic weight receives this scale squared.
    pub removed_scale: BigUint,
}

/// Exact executable rank-one carrier for
/// `D_p T_g C T_g^T D_p = Σ_s w_s (D_p T_g x_s)(D_p T_g x_s)^T`.
///
/// The hot state is the condensed `target` family.  `slots` and `occurrences` retain both
/// boundary maps and the complete selected reconstruction fibre; unselected faces remain in the
/// encompassing receiver return rather than being relabelled as members of this passage.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct AddressedGeneratedPortCurrentPassage {
    pub schema: String,
    pub factor_population: u32,
    pub port_population: u32,
    pub generator_population: u32,
    pub source: Vec<AddressedCurrentSection>,
    pub target: Vec<AddressedCurrentSection>,
    pub generator_targets: Vec<u32>,
    pub slots: Vec<AddressedGeneratedPortSlot>,
    pub occurrences: Vec<AddressedGeneratedPortCurrentOccurrence>,
}

/// One local-current incidence retained by the target-site junction.  A radical occurrence is
/// preserved in the reconstruction fibre but contributes no current to the addressed target.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct AddressedGeneratedPortJunctionOccurrence {
    pub source_section: u32,
    pub selected_slot: u32,
    pub target_section: Option<u32>,
}

/// One exact HNN ecology step: all state-compatible local currents meet by linear addition at
/// their addressed target site before any reaction, projective observation, or quadratic face.
///
/// The occurrence population retains every boundary map.  The hot `target` population contains
/// exactly one section per reached target state; its unit quadratic weight is only the declared
/// resident observer face and does not participate in founding the successor current.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct AddressedGeneratedPortJunctionPassage {
    pub schema: String,
    pub factor_population: u32,
    pub port_population: u32,
    pub generator_population: u32,
    pub source: Vec<AddressedCurrentSection>,
    pub target: Vec<AddressedCurrentSection>,
    pub generator_targets: Vec<u32>,
    /// Complete input-conditioned current presented by the addressed exterior-return occurrence.
    /// `None` is the identity presentation used by the first ingress.  This current is distinct
    /// from the fixed internal generator action and from every exterior port rendering.
    pub presented_current: Option<Vec<(u32, BigUint)>>,
    pub slots: Vec<AddressedGeneratedPortSlot>,
    pub occurrences: Vec<AddressedGeneratedPortJunctionOccurrence>,
}

/// One exact current transport with both boundary maps and its complete reconstruction fibre.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct AddressedCurrentPassage {
    pub schema: String,
    pub factor_population: u32,
    pub generator_population: u32,
    pub source: Vec<AddressedCurrentSection>,
    pub target: Vec<AddressedCurrentSection>,
    /// `generator_targets[g * factor_population + source_factor]` is the oriented target factor.
    pub generator_targets: Vec<u32>,
    pub occurrences: Vec<AddressedCurrentOccurrence>,
}

impl AddressedCurrentPassage {
    /// Found one passage only after exact transport, literal-equality condensation, both boundary
    /// maps, target-weight conservation, and complete occurrence coverage have returned.
    pub fn found(
        factor_population: u32,
        generator_targets: Vec<u32>,
        source: Vec<AddressedCurrentSection>,
        target: Vec<AddressedCurrentSection>,
        occurrences: Vec<AddressedCurrentOccurrence>,
    ) -> Result<Self, AddressedCurrentPassageError> {
        let factor_extent = factor_population as usize;
        if factor_population == 0
            || source.is_empty()
            || target.is_empty()
            || source.len() > u32::MAX as usize
            || target.len() > u32::MAX as usize
            || generator_targets.is_empty()
            || generator_targets.len() % factor_extent != 0
            || generator_targets
                .iter()
                .any(|target| *target >= factor_population)
        {
            return Err(AddressedCurrentPassageError::Shape);
        }
        let generator_population = generator_targets.len() / factor_extent;
        if generator_population == 0 || generator_population > u32::MAX as usize {
            return Err(AddressedCurrentPassageError::Shape);
        }
        for section in source.iter().chain(&target) {
            section.validate(factor_population)?;
        }
        let expected_occurrences = source
            .len()
            .checked_mul(generator_population)
            .ok_or(AddressedCurrentPassageError::Shape)?;
        if occurrences.len() != expected_occurrences {
            return Err(AddressedCurrentPassageError::Boundary);
        }

        let mut seen_source_boundary = BTreeSet::new();
        let mut reached_targets = BTreeSet::new();
        let mut target_of_current = BTreeMap::<(Option<u32>, Vec<(u32, BigUint)>), u32>::new();
        let mut returned_weight = vec![BigUint::ZERO; target.len()];
        for occurrence in &occurrences {
            let source_section = source
                .get(occurrence.source_section as usize)
                .ok_or(AddressedCurrentPassageError::Boundary)?;
            if occurrence.generator as usize >= generator_population
                || occurrence.target_section as usize >= target.len()
                || !seen_source_boundary.insert((occurrence.source_section, occurrence.generator))
            {
                return Err(AddressedCurrentPassageError::Boundary);
            }
            let transported = transport_current(
                factor_population,
                &generator_targets,
                occurrence.generator,
                &source_section.factor_current,
            )?;
            let target_section = &target[occurrence.target_section as usize];
            if source_section.boundary_state != target_section.boundary_state
                || transported != target_section.factor_current
            {
                return Err(AddressedCurrentPassageError::Transport);
            }
            match target_of_current.insert(
                (source_section.boundary_state, transported),
                occurrence.target_section,
            ) {
                Some(existing) if existing != occurrence.target_section => {
                    return Err(AddressedCurrentPassageError::Condensation);
                }
                _ => {}
            }
            returned_weight[occurrence.target_section as usize] += &source_section.quadratic_weight;
            reached_targets.insert(occurrence.target_section);
        }
        if seen_source_boundary.len() != expected_occurrences
            || reached_targets.len() != target.len()
            || target_of_current.len() != target.len()
            || target
                .iter()
                .zip(returned_weight)
                .any(|(target, weight)| target.quadratic_weight != weight)
        {
            return Err(AddressedCurrentPassageError::Conservation);
        }

        Ok(Self {
            schema: "holonic-engine.addressed-dynamic-current-passage.v1".to_owned(),
            factor_population,
            generator_population: generator_population as u32,
            source,
            target,
            generator_targets,
            occurrences,
        })
    }

    pub fn reconstruction_fibre(
        &self,
        target_section: u32,
    ) -> impl Iterator<Item = &AddressedCurrentOccurrence> {
        self.occurrences
            .iter()
            .filter(move |occurrence| occurrence.target_section == target_section)
    }
}

impl AddressedGeneratedPortCurrentPassage {
    /// Derive one complete local-current ecology step from its rested transport/restriction
    /// morphology and contemporary addressed source state.
    ///
    /// This is the apparatus-neutral construction whose result a resident accelerator must
    /// reproduce.  Each state-compatible `(source section, selected slot)` occurrence is
    /// transported, restricted, reduced to its primitive positive projective ray, and then
    /// condensed only with a literally equal `(target state, ray)` occurrence.  The removed
    /// projective scale remains on the occurrence and contributes its square to the returned
    /// quadratic weight.  A restriction which annihilates a transported section remains an
    /// addressed radical occurrence with no target; it is never silently dropped.
    pub fn derive(
        factor_population: u32,
        port_population: u32,
        generator_targets: Vec<u32>,
        source: Vec<AddressedCurrentSection>,
        slots: Vec<AddressedGeneratedPortSlot>,
    ) -> Result<Self, AddressedCurrentPassageError> {
        let factor_extent = factor_population as usize;
        if factor_population == 0
            || port_population == 0
            || source.is_empty()
            || slots.is_empty()
            || source.len() > u32::MAX as usize
            || slots.len() > u32::MAX as usize
            || generator_targets.is_empty()
            || generator_targets.len() % factor_extent != 0
        {
            return Err(AddressedCurrentPassageError::Shape);
        }
        let generator_population = generator_targets.len() / factor_extent;
        if generator_population == 0 || generator_population > u32::MAX as usize {
            return Err(AddressedCurrentPassageError::Shape);
        }
        for section in &source {
            section.validate(factor_population)?;
            if section.boundary_state.is_none() {
                return Err(AddressedCurrentPassageError::Boundary);
            }
        }
        for slot in &slots {
            if slot.port >= port_population
                || slot.generator as usize >= generator_population
                || slot.restriction.is_empty()
                || slot
                    .restriction
                    .windows(2)
                    .any(|pair| pair[0].0 >= pair[1].0)
                || slot.restriction.iter().any(|(factor, coefficient)| {
                    *factor >= factor_population || coefficient.is_zero()
                })
            {
                return Err(AddressedCurrentPassageError::Section);
            }
        }

        let mut target = Vec::<AddressedCurrentSection>::new();
        let mut target_by_section = BTreeMap::<(Option<u32>, Vec<(u32, BigUint)>), u32>::new();
        let mut occurrences = Vec::<AddressedGeneratedPortCurrentOccurrence>::new();
        for (source_section, section) in source.iter().enumerate() {
            let source_boundary_state = section
                .boundary_state
                .ok_or(AddressedCurrentPassageError::Boundary)?;
            for (selected_slot, slot) in slots.iter().enumerate() {
                if slot.source_boundary_state != source_boundary_state {
                    continue;
                }
                let transported = transport_current(
                    factor_population,
                    &generator_targets,
                    slot.generator,
                    &section.factor_current,
                )?;
                let restricted = restrict_current(&transported, &slot.restriction);
                if restricted.is_empty() {
                    occurrences.push(AddressedGeneratedPortCurrentOccurrence {
                        source_section: source_section as u32,
                        selected_slot: selected_slot as u32,
                        target_section: None,
                        removed_scale: BigUint::ZERO,
                    });
                    continue;
                }

                let removed_scale = restricted
                    .iter()
                    .map(|(_, coefficient)| coefficient.clone())
                    .reduce(exact_biguint_gcd)
                    .filter(|scale| !scale.is_zero())
                    .ok_or(AddressedCurrentPassageError::Transport)?;
                let projective = restricted
                    .iter()
                    .map(|(factor, coefficient)| {
                        let quotient = coefficient / &removed_scale;
                        ((!quotient.is_zero() && &quotient * &removed_scale == *coefficient)
                            .then_some((*factor, quotient)))
                        .ok_or(AddressedCurrentPassageError::Transport)
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                let key = (Some(slot.boundary_state), projective.clone());
                let target_section = match target_by_section.get(&key).copied() {
                    Some(target_section) => target_section,
                    None => {
                        let target_section = u32::try_from(target.len())
                            .map_err(|_| AddressedCurrentPassageError::Shape)?;
                        target_by_section.insert(key, target_section);
                        target.push(AddressedCurrentSection {
                            boundary_state: Some(slot.boundary_state),
                            quadratic_weight: BigUint::ZERO,
                            factor_current: projective,
                        });
                        target_section
                    }
                };
                target[target_section as usize].quadratic_weight +=
                    &section.quadratic_weight * &removed_scale * &removed_scale;
                occurrences.push(AddressedGeneratedPortCurrentOccurrence {
                    source_section: source_section as u32,
                    selected_slot: selected_slot as u32,
                    target_section: Some(target_section),
                    removed_scale,
                });
            }
        }
        if occurrences.is_empty() {
            return Err(AddressedCurrentPassageError::Conservation);
        }
        Self::found(
            factor_population,
            port_population,
            generator_targets,
            source,
            target,
            slots,
            occurrences,
        )
    }

    /// Admit the selected addressed family only after every restricted transport, exact-equality
    /// quotient, boundary map, and quadratic weight has been reconstructed independently of the
    /// resident apparatus.
    pub fn found(
        factor_population: u32,
        port_population: u32,
        generator_targets: Vec<u32>,
        source: Vec<AddressedCurrentSection>,
        target: Vec<AddressedCurrentSection>,
        slots: Vec<AddressedGeneratedPortSlot>,
        occurrences: Vec<AddressedGeneratedPortCurrentOccurrence>,
    ) -> Result<Self, AddressedCurrentPassageError> {
        let factor_extent = factor_population as usize;
        if factor_population == 0
            || port_population == 0
            || source.is_empty()
            || slots.is_empty()
            || source.len() > u32::MAX as usize
            || target.len() > u32::MAX as usize
            || slots.len() > u32::MAX as usize
            || generator_targets.is_empty()
            || generator_targets.len() % factor_extent != 0
        {
            return Err(AddressedCurrentPassageError::Shape);
        }
        let generator_population = generator_targets.len() / factor_extent;
        if generator_population == 0 || generator_population > u32::MAX as usize {
            return Err(AddressedCurrentPassageError::Shape);
        }
        for section in source.iter().chain(&target) {
            section.validate(factor_population)?;
        }
        for slot in &slots {
            if slot.port >= port_population
                || slot.generator as usize >= generator_population
                || slot.restriction.is_empty()
                || slot
                    .restriction
                    .windows(2)
                    .any(|pair| pair[0].0 >= pair[1].0)
                || slot.restriction.iter().any(|(factor, coefficient)| {
                    *factor >= factor_population || coefficient.is_zero()
                })
            {
                return Err(AddressedCurrentPassageError::Section);
            }
        }
        let expected_occurrences = source
            .iter()
            .map(|section| {
                section
                    .boundary_state
                    .map(|state| {
                        slots
                            .iter()
                            .filter(|slot| slot.source_boundary_state == state)
                            .count()
                    })
                    .ok_or(AddressedCurrentPassageError::Boundary)
            })
            .try_fold(0_usize, |sum, extent| {
                sum.checked_add(extent?)
                    .ok_or(AddressedCurrentPassageError::Shape)
            })?;
        if occurrences.len() != expected_occurrences {
            return Err(AddressedCurrentPassageError::Boundary);
        }

        let mut seen_source_boundary = BTreeSet::new();
        let mut reached_targets = BTreeSet::new();
        let mut target_of_current = BTreeMap::<(Option<u32>, Vec<(u32, BigUint)>), u32>::new();
        let mut returned_weight = vec![BigUint::ZERO; target.len()];
        for occurrence in &occurrences {
            let source_section = source
                .get(occurrence.source_section as usize)
                .ok_or(AddressedCurrentPassageError::Boundary)?;
            let slot = slots
                .get(occurrence.selected_slot as usize)
                .ok_or(AddressedCurrentPassageError::Boundary)?;
            if source_section.boundary_state != Some(slot.source_boundary_state) {
                return Err(AddressedCurrentPassageError::Boundary);
            }
            if !seen_source_boundary.insert((occurrence.source_section, occurrence.selected_slot)) {
                return Err(AddressedCurrentPassageError::Boundary);
            }
            let transported = transport_current(
                factor_population,
                &generator_targets,
                slot.generator,
                &source_section.factor_current,
            )?;
            let restricted = restrict_current(&transported, &slot.restriction);
            if restricted.is_empty() {
                if occurrence.target_section.is_some() || !occurrence.removed_scale.is_zero() {
                    return Err(AddressedCurrentPassageError::Transport);
                }
                continue;
            }
            if occurrence.removed_scale.is_zero() {
                return Err(AddressedCurrentPassageError::Transport);
            }
            let projective = restricted
                .iter()
                .map(|(factor, coefficient)| {
                    let quotient = coefficient / &occurrence.removed_scale;
                    ((!quotient.is_zero() && &quotient * &occurrence.removed_scale == *coefficient)
                        .then_some((*factor, quotient)))
                    .ok_or(AddressedCurrentPassageError::Transport)
                })
                .collect::<Result<Vec<_>, _>>()?;
            let target_address = occurrence
                .target_section
                .ok_or(AddressedCurrentPassageError::Transport)?;
            let target_section = target
                .get(target_address as usize)
                .ok_or(AddressedCurrentPassageError::Boundary)?;
            if Some(slot.boundary_state) != target_section.boundary_state
                || projective != target_section.factor_current
            {
                return Err(AddressedCurrentPassageError::Transport);
            }
            match target_of_current.insert((Some(slot.boundary_state), projective), target_address)
            {
                Some(existing) if existing != target_address => {
                    return Err(AddressedCurrentPassageError::Condensation);
                }
                _ => {}
            }
            returned_weight[target_address as usize] += &source_section.quadratic_weight
                * &occurrence.removed_scale
                * &occurrence.removed_scale;
            reached_targets.insert(target_address);
        }
        if seen_source_boundary.len() != expected_occurrences
            || reached_targets.len() != target.len()
            || target_of_current.len() != target.len()
            || target
                .iter()
                .zip(returned_weight)
                .any(|(target, weight)| target.quadratic_weight != weight)
        {
            return Err(AddressedCurrentPassageError::Conservation);
        }

        Ok(Self {
            schema: "holonic-engine.addressed-generated-port-current-passage.v2".to_owned(),
            factor_population,
            port_population,
            generator_population: generator_population as u32,
            source,
            target,
            generator_targets,
            slots,
            occurrences,
        })
    }

    pub fn reconstruction_fibre(
        &self,
        target_section: u32,
    ) -> impl Iterator<Item = &AddressedGeneratedPortCurrentOccurrence> {
        self.occurrences
            .iter()
            .filter(move |occurrence| occurrence.target_section == Some(target_section))
    }

    /// Every addressed occurrence was annihilated by its local receiver restriction.  The empty
    /// target is the exact zero section of this selected ecology step, not an absent computation.
    pub fn receiver_radical(&self) -> bool {
        self.target.is_empty()
            && !self.occurrences.is_empty()
            && self.occurrences.iter().all(|occurrence| {
                occurrence.target_section.is_none() && occurrence.removed_scale.is_zero()
            })
    }
}

impl AddressedGeneratedPortJunctionPassage {
    /// Derive the apparatus-neutral target-site sum
    /// `x'_t = Σ_(s,p,g -> t) D_p T_g x_s`.
    pub fn derive(
        factor_population: u32,
        port_population: u32,
        generator_targets: Vec<u32>,
        source: Vec<AddressedCurrentSection>,
        slots: Vec<AddressedGeneratedPortSlot>,
    ) -> Result<Self, AddressedCurrentPassageError> {
        Self::derive_with_presented_current(
            factor_population,
            port_population,
            generator_targets,
            source,
            None,
            slots,
        )
    }

    /// Derive the same target-site junction after one complete returned occurrence conditions
    /// every local current through its native factor section.  The returned current is applied
    /// after fixed generator transport and boundary restriction; this is the apparatus-neutral
    /// `localCurrent morphology occurrence state target source` law.
    pub fn derive_with_presented_current(
        factor_population: u32,
        port_population: u32,
        generator_targets: Vec<u32>,
        source: Vec<AddressedCurrentSection>,
        presented_current: Option<Vec<(u32, BigUint)>>,
        slots: Vec<AddressedGeneratedPortSlot>,
    ) -> Result<Self, AddressedCurrentPassageError> {
        validate_generated_port_shape(
            factor_population,
            port_population,
            &generator_targets,
            &source,
            &slots,
        )?;
        validate_presented_current(factor_population, presented_current.as_deref())?;

        let mut current_by_state = BTreeMap::<u32, BTreeMap<u32, BigUint>>::new();
        let mut occurrence_states = Vec::<(u32, u32, Option<u32>)>::new();
        for (source_section, section) in source.iter().enumerate() {
            let source_state = section
                .boundary_state
                .ok_or(AddressedCurrentPassageError::Boundary)?;
            for (selected_slot, slot) in slots.iter().enumerate() {
                if slot.source_boundary_state != source_state {
                    continue;
                }
                let transported = transport_current(
                    factor_population,
                    &generator_targets,
                    slot.generator,
                    &section.factor_current,
                )?;
                let restricted = restrict_current(&transported, &slot.restriction);
                let restricted = presented_current
                    .as_deref()
                    .map_or(restricted.clone(), |presented| {
                        restrict_current(&restricted, presented)
                    });
                let target_state = (!restricted.is_empty()).then_some(slot.boundary_state);
                if let Some(target_state) = target_state {
                    let target = current_by_state.entry(target_state).or_default();
                    for (factor, coefficient) in restricted {
                        *target.entry(factor).or_default() += coefficient;
                    }
                }
                occurrence_states.push((source_section as u32, selected_slot as u32, target_state));
            }
        }
        if occurrence_states.is_empty() {
            return Err(AddressedCurrentPassageError::Conservation);
        }

        let mut target_by_state = BTreeMap::<u32, u32>::new();
        let mut target = Vec::with_capacity(current_by_state.len());
        for (state, current) in current_by_state {
            let target_section =
                u32::try_from(target.len()).map_err(|_| AddressedCurrentPassageError::Shape)?;
            target_by_state.insert(state, target_section);
            target.push(AddressedCurrentSection {
                boundary_state: Some(state),
                quadratic_weight: BigUint::from(1_u8),
                factor_current: current
                    .into_iter()
                    .filter(|(_, coefficient)| !coefficient.is_zero())
                    .collect(),
            });
        }
        let occurrences = occurrence_states
            .into_iter()
            .map(|(source_section, selected_slot, target_state)| {
                Ok(AddressedGeneratedPortJunctionOccurrence {
                    source_section,
                    selected_slot,
                    target_section: target_state
                        .map(|state| {
                            target_by_state
                                .get(&state)
                                .copied()
                                .ok_or(AddressedCurrentPassageError::Boundary)
                        })
                        .transpose()?,
                })
            })
            .collect::<Result<Vec<_>, AddressedCurrentPassageError>>()?;
        Self::found_with_presented_current(
            factor_population,
            port_population,
            generator_targets,
            source,
            target,
            presented_current,
            slots,
            occurrences,
        )
    }

    /// Admit a resident target-site junction only after independently reconstructing every local
    /// current and its exact addressed sum.
    pub fn found(
        factor_population: u32,
        port_population: u32,
        generator_targets: Vec<u32>,
        source: Vec<AddressedCurrentSection>,
        target: Vec<AddressedCurrentSection>,
        slots: Vec<AddressedGeneratedPortSlot>,
        occurrences: Vec<AddressedGeneratedPortJunctionOccurrence>,
    ) -> Result<Self, AddressedCurrentPassageError> {
        Self::found_with_presented_current(
            factor_population,
            port_population,
            generator_targets,
            source,
            target,
            None,
            slots,
            occurrences,
        )
    }

    pub fn found_with_presented_current(
        factor_population: u32,
        port_population: u32,
        generator_targets: Vec<u32>,
        source: Vec<AddressedCurrentSection>,
        target: Vec<AddressedCurrentSection>,
        presented_current: Option<Vec<(u32, BigUint)>>,
        slots: Vec<AddressedGeneratedPortSlot>,
        occurrences: Vec<AddressedGeneratedPortJunctionOccurrence>,
    ) -> Result<Self, AddressedCurrentPassageError> {
        validate_generated_port_shape(
            factor_population,
            port_population,
            &generator_targets,
            &source,
            &slots,
        )?;
        validate_presented_current(factor_population, presented_current.as_deref())?;
        for section in &target {
            section.validate(factor_population)?;
            if section.boundary_state.is_none() || section.quadratic_weight != BigUint::from(1_u8) {
                return Err(AddressedCurrentPassageError::Section);
            }
        }

        let expected_occurrences = expected_generated_port_occurrences(&source, &slots)?;
        if occurrences.len() != expected_occurrences {
            return Err(AddressedCurrentPassageError::Boundary);
        }
        let mut target_by_state = BTreeMap::<u32, u32>::new();
        for (target_section, section) in target.iter().enumerate() {
            let state = section
                .boundary_state
                .ok_or(AddressedCurrentPassageError::Boundary)?;
            if target_by_state
                .insert(state, target_section as u32)
                .is_some()
            {
                return Err(AddressedCurrentPassageError::Condensation);
            }
        }

        let mut seen = BTreeSet::new();
        let mut returned = vec![BTreeMap::<u32, BigUint>::new(); target.len()];
        let mut reached = BTreeSet::new();
        for occurrence in &occurrences {
            let section = source
                .get(occurrence.source_section as usize)
                .ok_or(AddressedCurrentPassageError::Boundary)?;
            let slot = slots
                .get(occurrence.selected_slot as usize)
                .ok_or(AddressedCurrentPassageError::Boundary)?;
            if section.boundary_state != Some(slot.source_boundary_state)
                || !seen.insert((occurrence.source_section, occurrence.selected_slot))
            {
                return Err(AddressedCurrentPassageError::Boundary);
            }
            let transported = transport_current(
                factor_population,
                &generator_targets,
                slot.generator,
                &section.factor_current,
            )?;
            let restricted = restrict_current(&transported, &slot.restriction);
            let restricted = presented_current
                .as_deref()
                .map_or(restricted.clone(), |presented| {
                    restrict_current(&restricted, presented)
                });
            if restricted.is_empty() {
                if occurrence.target_section.is_some() {
                    return Err(AddressedCurrentPassageError::Transport);
                }
                continue;
            }
            let target_section = occurrence
                .target_section
                .ok_or(AddressedCurrentPassageError::Transport)?;
            if target_by_state.get(&slot.boundary_state) != Some(&target_section) {
                return Err(AddressedCurrentPassageError::Transport);
            }
            let sum = returned
                .get_mut(target_section as usize)
                .ok_or(AddressedCurrentPassageError::Boundary)?;
            for (factor, coefficient) in restricted {
                *sum.entry(factor).or_default() += coefficient;
            }
            reached.insert(target_section);
        }
        if seen.len() != expected_occurrences || reached.len() != target.len() {
            return Err(AddressedCurrentPassageError::Conservation);
        }
        for (target_section, expected) in target.iter().zip(returned) {
            let expected = expected
                .into_iter()
                .filter(|(_, coefficient)| !coefficient.is_zero())
                .collect::<Vec<_>>();
            if target_section.factor_current != expected {
                return Err(AddressedCurrentPassageError::Conservation);
            }
        }

        Ok(Self {
            schema: "holonic-engine.addressed-generated-port-junction-passage.v2".to_owned(),
            factor_population,
            port_population,
            generator_population: (generator_targets.len() / factor_population as usize) as u32,
            source,
            target,
            generator_targets,
            presented_current,
            slots,
            occurrences,
        })
    }

    pub fn reconstruction_fibre(
        &self,
        target_section: u32,
    ) -> impl Iterator<Item = &AddressedGeneratedPortJunctionOccurrence> {
        self.occurrences
            .iter()
            .filter(move |occurrence| occurrence.target_section == Some(target_section))
    }

    pub fn receiver_radical(&self) -> bool {
        self.target.is_empty()
            && !self.occurrences.is_empty()
            && self
                .occurrences
                .iter()
                .all(|occurrence| occurrence.target_section.is_none())
    }
}

fn validate_presented_current(
    factor_population: u32,
    presented_current: Option<&[(u32, BigUint)]>,
) -> Result<(), AddressedCurrentPassageError> {
    let Some(current) = presented_current else {
        return Ok(());
    };
    if current.is_empty()
        || current.windows(2).any(|pair| pair[0].0 >= pair[1].0)
        || current
            .iter()
            .any(|(factor, coefficient)| *factor >= factor_population || coefficient.is_zero())
    {
        return Err(AddressedCurrentPassageError::Section);
    }
    Ok(())
}

fn validate_generated_port_shape(
    factor_population: u32,
    port_population: u32,
    generator_targets: &[u32],
    source: &[AddressedCurrentSection],
    slots: &[AddressedGeneratedPortSlot],
) -> Result<(), AddressedCurrentPassageError> {
    let factor_extent = factor_population as usize;
    if factor_population == 0
        || port_population == 0
        || source.is_empty()
        || slots.is_empty()
        || source.len() > u32::MAX as usize
        || slots.len() > u32::MAX as usize
        || generator_targets.is_empty()
        || generator_targets.len() % factor_extent != 0
    {
        return Err(AddressedCurrentPassageError::Shape);
    }
    let generator_population = generator_targets.len() / factor_extent;
    if generator_population == 0 || generator_population > u32::MAX as usize {
        return Err(AddressedCurrentPassageError::Shape);
    }
    for section in source {
        section.validate(factor_population)?;
        if section.boundary_state.is_none() {
            return Err(AddressedCurrentPassageError::Boundary);
        }
    }
    for slot in slots {
        if slot.port >= port_population
            || slot.generator as usize >= generator_population
            || slot.restriction.is_empty()
            || slot
                .restriction
                .windows(2)
                .any(|pair| pair[0].0 >= pair[1].0)
            || slot
                .restriction
                .iter()
                .any(|(factor, coefficient)| *factor >= factor_population || coefficient.is_zero())
        {
            return Err(AddressedCurrentPassageError::Section);
        }
    }
    Ok(())
}

fn expected_generated_port_occurrences(
    source: &[AddressedCurrentSection],
    slots: &[AddressedGeneratedPortSlot],
) -> Result<usize, AddressedCurrentPassageError> {
    source
        .iter()
        .map(|section| {
            section
                .boundary_state
                .map(|state| {
                    slots
                        .iter()
                        .filter(|slot| slot.source_boundary_state == state)
                        .count()
                })
                .ok_or(AddressedCurrentPassageError::Boundary)
        })
        .try_fold(0_usize, |sum, extent| {
            sum.checked_add(extent?)
                .ok_or(AddressedCurrentPassageError::Shape)
        })
}

fn transport_current(
    factor_population: u32,
    generator_targets: &[u32],
    generator: u32,
    source: &[(u32, BigUint)],
) -> Result<Vec<(u32, BigUint)>, AddressedCurrentPassageError> {
    let factor_extent = factor_population as usize;
    let generator_offset = (generator as usize)
        .checked_mul(factor_extent)
        .ok_or(AddressedCurrentPassageError::Shape)?;
    let generator = generator_targets
        .get(generator_offset..generator_offset + factor_extent)
        .ok_or(AddressedCurrentPassageError::Shape)?;
    let mut target = BTreeMap::<u32, BigUint>::new();
    for (factor, coefficient) in source {
        let target_factor = *generator
            .get(*factor as usize)
            .ok_or(AddressedCurrentPassageError::Shape)?;
        *target.entry(target_factor).or_default() += coefficient;
    }
    Ok(target.into_iter().collect())
}

fn restrict_current(
    transported: &[(u32, BigUint)],
    restriction: &[(u32, BigUint)],
) -> Vec<(u32, BigUint)> {
    let mut transported_at = 0_usize;
    let mut restriction_at = 0_usize;
    let mut returned = Vec::new();
    while transported_at < transported.len() && restriction_at < restriction.len() {
        let (transported_factor, transported_value) = &transported[transported_at];
        let (restriction_factor, restriction_value) = &restriction[restriction_at];
        match transported_factor.cmp(restriction_factor) {
            std::cmp::Ordering::Less => transported_at += 1,
            std::cmp::Ordering::Greater => restriction_at += 1,
            std::cmp::Ordering::Equal => {
                let value = transported_value * restriction_value;
                if !value.is_zero() {
                    returned.push((*transported_factor, value));
                }
                transported_at += 1;
                restriction_at += 1;
            }
        }
    }
    returned
}

fn exact_biguint_gcd(mut left: BigUint, mut right: BigUint) -> BigUint {
    while !right.is_zero() {
        let remainder = &left % &right;
        left = right;
        right = remainder;
    }
    left
}

#[derive(Clone, Debug, PartialEq, Eq, Error)]
pub enum AddressedCurrentPassageError {
    #[error("the addressed current passage has a malformed population or operator extent")]
    Shape,
    #[error("an addressed current section is empty, unordered, zero, or outside its incidence")]
    Section,
    #[error("the addressed current occurrence population lost one of its boundary maps")]
    Boundary,
    #[error("a returned current is not the exact transport of its addressed source")]
    Transport,
    #[error("literal-equality condensation produced duplicate target addresses")]
    Condensation,
    #[error("the addressed current target does not conserve its complete predecessor fibre")]
    Conservation,
}

#[cfg(test)]
mod tests {
    use super::*;

    fn section(weight: u32, current: &[(u32, u32)]) -> AddressedCurrentSection {
        AddressedCurrentSection {
            boundary_state: None,
            quadratic_weight: BigUint::from(weight),
            factor_current: current
                .iter()
                .map(|(factor, coefficient)| (*factor, BigUint::from(*coefficient)))
                .collect(),
        }
    }

    #[test]
    fn noninjective_transport_retains_the_complete_occurrence_fibre() {
        let passage = AddressedCurrentPassage::found(
            3,
            vec![0, 0, 1, 1, 2, 2],
            vec![section(2, &[(0, 1), (1, 2)]), section(5, &[(2, 3)])],
            vec![
                section(2, &[(0, 3)]),
                section(5, &[(1, 3)]),
                section(5, &[(2, 3)]),
                section(2, &[(1, 1), (2, 2)]),
            ],
            vec![
                AddressedCurrentOccurrence {
                    source_section: 0,
                    generator: 0,
                    target_section: 0,
                },
                AddressedCurrentOccurrence {
                    source_section: 0,
                    generator: 1,
                    target_section: 3,
                },
                AddressedCurrentOccurrence {
                    source_section: 1,
                    generator: 0,
                    target_section: 1,
                },
                AddressedCurrentOccurrence {
                    source_section: 1,
                    generator: 1,
                    target_section: 2,
                },
            ],
        )
        .expect("exact addressed passage");
        assert_eq!(passage.occurrences.len(), 4);
        assert_eq!(passage.reconstruction_fibre(0).count(), 1);
    }

    #[test]
    fn equal_transported_currents_cannot_be_split_across_two_targets() {
        let error = AddressedCurrentPassage::found(
            2,
            vec![0, 0, 0, 0],
            vec![section(1, &[(0, 1)]), section(1, &[(1, 1)])],
            vec![section(2, &[(0, 1)]), section(2, &[(0, 1)])],
            vec![
                AddressedCurrentOccurrence {
                    source_section: 0,
                    generator: 0,
                    target_section: 0,
                },
                AddressedCurrentOccurrence {
                    source_section: 0,
                    generator: 1,
                    target_section: 0,
                },
                AddressedCurrentOccurrence {
                    source_section: 1,
                    generator: 0,
                    target_section: 1,
                },
                AddressedCurrentOccurrence {
                    source_section: 1,
                    generator: 1,
                    target_section: 1,
                },
            ],
        )
        .expect_err("split literal current");
        assert_eq!(error, AddressedCurrentPassageError::Condensation);
    }

    #[test]
    fn equal_restricted_currents_at_distinct_boundary_states_remain_distinct_targets() {
        let source = vec![AddressedCurrentSection {
            boundary_state: Some(5),
            quadratic_weight: BigUint::from(3_u8),
            factor_current: vec![(0, BigUint::from(2_u8))],
        }];
        let restriction = vec![(0, BigUint::from(1_u8))];
        let passage = AddressedGeneratedPortCurrentPassage::found(
            2,
            2,
            vec![0, 1],
            source,
            vec![
                AddressedCurrentSection {
                    boundary_state: Some(5),
                    quadratic_weight: BigUint::from(3_u8),
                    factor_current: vec![(0, BigUint::from(2_u8))],
                },
                AddressedCurrentSection {
                    boundary_state: Some(6),
                    quadratic_weight: BigUint::from(3_u8),
                    factor_current: vec![(0, BigUint::from(2_u8))],
                },
            ],
            vec![
                AddressedGeneratedPortSlot {
                    port: 0,
                    generator: 0,
                    source_boundary_state: 5,
                    boundary_state: 5,
                    restriction: restriction.clone(),
                },
                AddressedGeneratedPortSlot {
                    port: 1,
                    generator: 0,
                    source_boundary_state: 5,
                    boundary_state: 6,
                    restriction,
                },
            ],
            vec![
                AddressedGeneratedPortCurrentOccurrence {
                    source_section: 0,
                    selected_slot: 0,
                    target_section: Some(0),
                    removed_scale: BigUint::from(1_u8),
                },
                AddressedGeneratedPortCurrentOccurrence {
                    source_section: 0,
                    selected_slot: 1,
                    target_section: Some(1),
                    removed_scale: BigUint::from(1_u8),
                },
            ],
        )
        .expect("state-addressed restricted current passage");

        assert_eq!(
            passage.target[0].factor_current,
            passage.target[1].factor_current
        );
        assert_ne!(
            passage.target[0].boundary_state,
            passage.target[1].boundary_state
        );
    }

    #[test]
    fn complete_generated_port_ecology_step_derives_reaction_and_radical_fibre() {
        let passage = AddressedGeneratedPortCurrentPassage::derive(
            3,
            2,
            vec![1, 2, 2],
            vec![
                AddressedCurrentSection {
                    boundary_state: Some(5),
                    quadratic_weight: BigUint::from(2_u8),
                    factor_current: vec![(0, BigUint::from(2_u8)), (1, BigUint::from(4_u8))],
                },
                AddressedCurrentSection {
                    boundary_state: Some(5),
                    quadratic_weight: BigUint::from(3_u8),
                    factor_current: vec![(0, BigUint::from(4_u8)), (1, BigUint::from(8_u8))],
                },
            ],
            vec![
                AddressedGeneratedPortSlot {
                    port: 0,
                    generator: 0,
                    source_boundary_state: 5,
                    boundary_state: 6,
                    restriction: vec![(1, BigUint::from(3_u8)), (2, BigUint::from(5_u8))],
                },
                AddressedGeneratedPortSlot {
                    port: 1,
                    generator: 0,
                    source_boundary_state: 5,
                    boundary_state: 7,
                    restriction: vec![(0, BigUint::from(1_u8))],
                },
            ],
        )
        .expect("complete apparatus-neutral ecology step");

        assert_eq!(passage.target.len(), 1);
        assert_eq!(passage.target[0].boundary_state, Some(6));
        assert_eq!(passage.target[0].quadratic_weight, BigUint::from(56_u8));
        assert_eq!(
            passage.target[0].factor_current,
            vec![(1, BigUint::from(3_u8)), (2, BigUint::from(10_u8))]
        );
        assert_eq!(passage.occurrences.len(), 4);
        assert_eq!(
            passage
                .occurrences
                .iter()
                .filter(|occurrence| occurrence.target_section == Some(0))
                .map(|occurrence| occurrence.removed_scale.clone())
                .collect::<Vec<_>>(),
            vec![BigUint::from(2_u8), BigUint::from(4_u8)]
        );
        assert_eq!(
            passage
                .occurrences
                .iter()
                .filter(|occurrence| occurrence.target_section.is_none())
                .count(),
            2
        );
        assert_eq!(passage.reconstruction_fibre(0).count(), 2);
    }

    #[test]
    fn complete_generated_port_ecology_step_retains_an_all_radical_successor() {
        let passage = AddressedGeneratedPortCurrentPassage::derive(
            2,
            1,
            vec![0, 1],
            vec![AddressedCurrentSection {
                boundary_state: Some(3),
                quadratic_weight: BigUint::from(7_u8),
                factor_current: vec![(0, BigUint::from(5_u8))],
            }],
            vec![AddressedGeneratedPortSlot {
                port: 0,
                generator: 0,
                source_boundary_state: 3,
                boundary_state: 4,
                restriction: vec![(1, BigUint::from(11_u8))],
            }],
        )
        .expect("the zero successor is a complete addressed return");

        assert!(passage.receiver_radical());
        assert!(passage.target.is_empty());
        assert_eq!(passage.occurrences.len(), 1);
    }

    #[test]
    fn target_site_junction_sums_local_currents_before_any_projective_receiver() {
        let passage = AddressedGeneratedPortJunctionPassage::derive(
            3,
            2,
            vec![1, 2, 2],
            vec![
                AddressedCurrentSection {
                    boundary_state: Some(5),
                    quadratic_weight: BigUint::from(17_u8),
                    factor_current: vec![(0, BigUint::from(2_u8)), (1, BigUint::from(4_u8))],
                },
                AddressedCurrentSection {
                    boundary_state: Some(5),
                    quadratic_weight: BigUint::from(23_u8),
                    factor_current: vec![(0, BigUint::from(4_u8)), (1, BigUint::from(8_u8))],
                },
            ],
            vec![
                AddressedGeneratedPortSlot {
                    port: 0,
                    generator: 0,
                    source_boundary_state: 5,
                    boundary_state: 6,
                    restriction: vec![(1, BigUint::from(3_u8)), (2, BigUint::from(5_u8))],
                },
                AddressedGeneratedPortSlot {
                    port: 1,
                    generator: 0,
                    source_boundary_state: 5,
                    boundary_state: 7,
                    restriction: vec![(0, BigUint::from(1_u8))],
                },
            ],
        )
        .expect("exact target-site junction");

        assert_eq!(passage.target.len(), 1);
        assert_eq!(passage.target[0].boundary_state, Some(6));
        assert_eq!(passage.target[0].quadratic_weight, BigUint::from(1_u8));
        assert_eq!(
            passage.target[0].factor_current,
            vec![(1, BigUint::from(18_u8)), (2, BigUint::from(60_u8))]
        );
        assert_eq!(passage.occurrences.len(), 4);
        assert_eq!(passage.reconstruction_fibre(0).count(), 2);
        assert_eq!(
            passage
                .occurrences
                .iter()
                .filter(|occurrence| occurrence.target_section.is_none())
                .count(),
            2
        );
    }

    #[test]
    fn returned_native_current_conditions_every_local_junction_current() {
        let presented_current = vec![(1, BigUint::from(7_u8)), (2, BigUint::from(11_u8))];
        let passage = AddressedGeneratedPortJunctionPassage::derive_with_presented_current(
            3,
            2,
            vec![1, 2, 2],
            vec![
                AddressedCurrentSection {
                    boundary_state: Some(5),
                    quadratic_weight: BigUint::from(17_u8),
                    factor_current: vec![(0, BigUint::from(2_u8)), (1, BigUint::from(4_u8))],
                },
                AddressedCurrentSection {
                    boundary_state: Some(5),
                    quadratic_weight: BigUint::from(23_u8),
                    factor_current: vec![(0, BigUint::from(4_u8)), (1, BigUint::from(8_u8))],
                },
            ],
            Some(presented_current.clone()),
            vec![
                AddressedGeneratedPortSlot {
                    port: 0,
                    generator: 0,
                    source_boundary_state: 5,
                    boundary_state: 6,
                    restriction: vec![(1, BigUint::from(3_u8)), (2, BigUint::from(5_u8))],
                },
                AddressedGeneratedPortSlot {
                    port: 1,
                    generator: 0,
                    source_boundary_state: 5,
                    boundary_state: 7,
                    restriction: vec![(0, BigUint::from(1_u8))],
                },
            ],
        )
        .expect("returned native current joins the exact local-current law");

        assert_eq!(passage.presented_current, Some(presented_current));
        assert_eq!(passage.target.len(), 1);
        assert_eq!(passage.target[0].boundary_state, Some(6));
        assert_eq!(
            passage.target[0].factor_current,
            vec![(1, BigUint::from(126_u16)), (2, BigUint::from(660_u16))]
        );
        assert_eq!(passage.reconstruction_fibre(0).count(), 2);
        assert_eq!(
            passage
                .occurrences
                .iter()
                .filter(|occurrence| occurrence.target_section.is_none())
                .count(),
            2
        );
    }
}

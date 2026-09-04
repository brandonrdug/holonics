//! M3 anti-vacuity: recover the finite swing action, then let lineage reopen a geometric quotient.

use std::collections::{BTreeMap, BTreeSet, VecDeque};

use holonic_engine::receiver_exact_compression::InputId;
use serde::Serialize;

use super::active_cover::StateAddress;

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct SwingRelation {
    pub presented_word: Vec<InputId>,
    pub normal_form: Vec<InputId>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct LineageSeparator {
    pub left_word: Vec<InputId>,
    pub right_word: Vec<InputId>,
    pub common_geometric_action: usize,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct SwingCalibration {
    pub schema: String,
    /// Derived from the number of M2 excitation environments, not chosen as a capacity.
    pub cyclic_chart_extent: usize,
    pub anchor_generators: Vec<InputId>,
    pub geometric_actions: usize,
    pub normal_forms: Vec<Vec<InputId>>,
    pub relations: Vec<SwingRelation>,
    pub every_generator_is_conjugated_negation: bool,
    pub every_generator_is_an_involution: bool,
    pub every_presented_word_factors_through_its_normal_form: bool,
    pub lineage_separator: LineageSeparator,
    pub first_noncommuting_words: (Vec<InputId>, Vec<InputId>, usize),
    pub exact_position_reads: u64,
}

pub fn calibrate(states: &[StateAddress]) -> Result<SwingCalibration, String> {
    let extent = states
        .iter()
        .map(|state| state.excitation_occurrence.as_str())
        .collect::<BTreeSet<_>>()
        .len();
    if extent <= 2 {
        return Err("the M2 environment population cannot exhibit a nontrivial swing".to_owned());
    }
    let anchors = vec![InputId(0), InputId(1)];
    let tables = anchors
        .iter()
        .map(|anchor| {
            (0..extent)
                .map(|position| swing(anchor.0 as usize, position, extent))
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>();
    let identity = (0..extent).collect::<Vec<_>>();
    let mut actions = vec![identity.clone()];
    let mut normal_forms = vec![Vec::<InputId>::new()];
    let mut action_id = BTreeMap::from([(identity, 0usize)]);
    let mut frontier = VecDeque::from([0usize]);
    let mut relations = Vec::new();
    let mut exact_position_reads = 0u64;
    while let Some(current) = frontier.pop_front() {
        for (generator_at, generator) in anchors.iter().enumerate() {
            let next = actions[current]
                .iter()
                .map(|position| {
                    exact_position_reads += 1;
                    tables[generator_at][*position]
                })
                .collect::<Vec<_>>();
            let mut word = normal_forms[current].clone();
            word.push(*generator);
            if let Some(existing) = action_id.get(&next).copied() {
                if word != normal_forms[existing] {
                    relations.push(SwingRelation {
                        presented_word: word,
                        normal_form: normal_forms[existing].clone(),
                    });
                }
            } else {
                let at = actions.len();
                action_id.insert(next.clone(), at);
                actions.push(next);
                normal_forms.push(word);
                frontier.push_back(at);
            }
        }
    }

    let every_generator_is_conjugated_negation = (0..extent).all(|anchor| {
        (0..extent).all(|position| {
            let displacement = sub(position, anchor, extent);
            swing(anchor, position, extent) == add(anchor, neg(displacement, extent), extent)
        })
    });
    let every_generator_is_an_involution = tables
        .iter()
        .all(|table| (0..extent).all(|position| table[table[position]] == position));
    let every_presented_word_factors_through_its_normal_form = relations.iter().all(|relation| {
        action_of(&relation.presented_word, &tables, extent)
            == action_of(&relation.normal_form, &tables, extent)
    });
    let reopened = relations
        .iter()
        .find(|relation| relation.presented_word != relation.normal_form)
        .ok_or_else(|| "the swing action returned no nontrivial word relation".to_owned())?;
    let common_geometric_action = *action_id
        .get(&action_of(&reopened.presented_word, &tables, extent))
        .ok_or_else(|| "a presented swing word left the recovered action".to_owned())?;
    let lineage_separator = LineageSeparator {
        left_word: reopened.presented_word.clone(),
        right_word: reopened.normal_form.clone(),
        common_geometric_action,
    };

    let left = vec![anchors[0], anchors[1]];
    let right = vec![anchors[1], anchors[0]];
    let left_action = action_of(&left, &tables, extent);
    let right_action = action_of(&right, &tables, extent);
    let separating_position = (0..extent)
        .find(|position| left_action[*position] != right_action[*position])
        .ok_or_else(|| "the two-anchor swing control unexpectedly commuted".to_owned())?;

    if !(every_generator_is_conjugated_negation
        && every_generator_is_an_involution
        && every_presented_word_factors_through_its_normal_form)
    {
        return Err("the swing anti-vacuity calibration failed its exact action laws".to_owned());
    }
    Ok(SwingCalibration {
        schema: "holonics.m3.swing-anti-vacuity.v1".to_owned(),
        cyclic_chart_extent: extent,
        anchor_generators: anchors,
        geometric_actions: actions.len(),
        normal_forms,
        relations,
        every_generator_is_conjugated_negation,
        every_generator_is_an_involution,
        every_presented_word_factors_through_its_normal_form,
        lineage_separator,
        first_noncommuting_words: (left, right, separating_position),
        exact_position_reads,
    })
}

fn swing(anchor: usize, position: usize, modulus: usize) -> usize {
    add(anchor, sub(anchor, position, modulus), modulus)
}

fn add(left: usize, right: usize, modulus: usize) -> usize {
    (left + right) % modulus
}

fn sub(left: usize, right: usize, modulus: usize) -> usize {
    (left + modulus - right) % modulus
}

fn neg(value: usize, modulus: usize) -> usize {
    (modulus - value) % modulus
}

fn action_of(word: &[InputId], tables: &[Vec<usize>], extent: usize) -> Vec<usize> {
    (0..extent)
        .map(|mut position| {
            for generator in word {
                position = tables[generator.0 as usize][position];
            }
            position
        })
        .collect()
}

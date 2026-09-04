//! Receiver-addressed operation/state transport substrate for M6.
//!
//! This is not the final total descent proof. It returns the least active source cover already
//! founded by the target's elaborated operation contacts, every before/after proof-state fibre,
//! shortest closure routes where they exist, reconvergence and exact source-face ablations. No
//! theorem/file/tactic label classifies a route and no host-authored case list enters the return.

use std::collections::{BTreeMap, BTreeSet, VecDeque};

use serde::Serialize;
use sha2::{Digest, Sha256};

use super::incidence::{IncidenceReturn, RecruitmentContact, TransitionOccurrence};

const CLOSED: &str = "holonics.m6/closed-proof-boundary";

#[derive(Clone, Debug, Serialize)]
pub struct RouteSubstrateReturn {
    pub schema: String,
    pub source_occurrence: String,
    pub receiver_question: ReceiverQuestion,
    pub active_operations: BTreeSet<String>,
    pub active_transition_occurrences: BTreeSet<String>,
    pub active_goal_occurrences: BTreeSet<String>,
    pub active_expression_faces: BTreeSet<String>,
    pub active_contacts: Vec<RecruitmentContact>,
    pub state_fibres: Vec<StateFibre>,
    pub shortest_closure_fibres: Vec<ShortestClosureFibre>,
    pub reconvergences: Vec<Reconvergence>,
    pub source_ablations: Vec<SourceAblation>,
    pub coverage: RouteCoverage,
    pub open_exterior: Vec<String>,
    pub truth_status: String,
}

#[derive(Clone, Debug, Serialize)]
pub struct ReceiverQuestion {
    pub target_operation: String,
    pub target_type_expression: String,
    pub target_defining_value_expression: Option<String>,
    pub target_seed_operations: BTreeSet<String>,
    pub selection_law: String,
}

#[derive(Clone, Debug, Serialize)]
pub struct StateFibre {
    pub occurrence: String,
    pub before_structural_word: Vec<String>,
    pub transition_occurrences: BTreeSet<String>,
    pub complete_after_structural_fibre: BTreeSet<Vec<String>>,
    pub parent_operations: BTreeSet<String>,
    pub source_paths_lineage: BTreeSet<String>,
}

#[derive(Clone, Debug, Serialize)]
pub struct ShortestClosureFibre {
    pub state_structural_face: String,
    pub distance_to_closed_boundary: usize,
    pub complete_next_state_fibre: BTreeSet<String>,
}

#[derive(Clone, Debug, Serialize)]
pub struct Reconvergence {
    pub state_structural_face: String,
    pub entering_transition_occurrences: BTreeSet<String>,
    pub entering_parent_operations: BTreeSet<String>,
}

#[derive(Clone, Debug, Serialize)]
pub struct SourceAblation {
    pub source_path_lineage: String,
    pub removed_transition_occurrences: BTreeSet<String>,
    pub removed_state_passages: BTreeSet<String>,
    pub reopened_before_fibres: BTreeSet<String>,
    pub deformed_before_fibres: BTreeSet<String>,
    pub unchanged_before_fibres: usize,
}

#[derive(Clone, Debug, Serialize)]
pub struct RouteCoverage {
    pub active_operations: usize,
    pub active_transitions: usize,
    pub assigned_transitions: usize,
    pub before_fibres: usize,
    pub plural_successor_fibres: usize,
    pub closed_passages: usize,
    pub reachable_state_faces: usize,
    pub open_state_faces: usize,
    pub reconvergences: usize,
    pub complete_at_returned_transition_grain: bool,
    pub total_descent_case_cover_established: bool,
}

pub fn derive(incidence: &IncidenceReturn) -> Result<RouteSubstrateReturn, String> {
    let operations = incidence
        .operations
        .iter()
        .map(|operation| (operation.occurrence.as_str(), operation))
        .collect::<BTreeMap<_, _>>();
    let target = operations
        .get(incidence.target_operation.as_str())
        .copied()
        .ok_or_else(|| "the target operation left the exact incidence".to_owned())?;
    let goal_structure = incidence
        .goals
        .iter()
        .map(|goal| (goal.occurrence.as_str(), goal.structural_face.as_str()))
        .collect::<BTreeMap<_, _>>();
    let active_transitions = incidence
        .transitions
        .iter()
        .filter(|transition| {
            transition
                .parent_operation
                .as_ref()
                .is_some_and(|parent| incidence.active_carrier_operations.contains(parent))
        })
        .collect::<Vec<_>>();
    if active_transitions.is_empty() {
        return Err(
            "the operation-derived active cover returned no proof-state transitions".to_owned(),
        );
    }

    let mut fibres = BTreeMap::<Vec<String>, FibreBuilder>::new();
    let mut active_transition_occurrences = BTreeSet::new();
    let mut active_goal_occurrences = BTreeSet::new();
    let mut active_expression_faces = BTreeSet::new();
    let mut active_sites = incidence.active_carrier_operations.clone();
    let mut closed_passages = 0usize;
    let mut adjacency = BTreeMap::<String, BTreeSet<String>>::new();
    let mut reverse = BTreeMap::<String, BTreeSet<String>>::new();
    let mut entering = BTreeMap::<String, BTreeSet<(String, String)>>::new();
    for transition in &active_transitions {
        active_transition_occurrences.insert(transition.occurrence.clone());
        active_sites.insert(transition.occurrence.clone());
        let before = structural_word(&transition.before_goals, &goal_structure)?;
        let after = structural_word(&transition.after_goals, &goal_structure)?;
        if after.is_empty() {
            closed_passages += 1;
        }
        let fibre = fibres.entry(before.clone()).or_default();
        fibre.transitions.insert(transition.occurrence.clone());
        fibre.after.insert(after.clone());
        fibre
            .source_paths
            .insert(transition.source_path_lineage.clone());
        if let Some(parent) = &transition.parent_operation {
            fibre.parents.insert(parent.clone());
        }
        for goal in transition
            .before_goals
            .iter()
            .chain(&transition.after_goals)
        {
            active_goal_occurrences.insert(goal.clone());
            active_sites.insert(goal.clone());
        }
        let from_states = if before.is_empty() {
            vec![root_face(transition)]
        } else {
            before.clone()
        };
        let to_states = if after.is_empty() {
            vec![CLOSED.to_owned()]
        } else {
            after.clone()
        };
        for from in &from_states {
            for to in &to_states {
                adjacency
                    .entry(from.clone())
                    .or_default()
                    .insert(to.clone());
                reverse.entry(to.clone()).or_default().insert(from.clone());
                entering.entry(to.clone()).or_default().insert((
                    transition.occurrence.clone(),
                    transition.parent_operation.clone().unwrap_or_default(),
                ));
            }
        }
    }
    for goal in incidence
        .goals
        .iter()
        .filter(|goal| active_goal_occurrences.contains(&goal.occurrence))
    {
        active_expression_faces.insert(goal.target_expression.clone());
        active_expression_faces.extend(goal.local_standing_expressions.iter().cloned());
    }
    active_sites.extend(active_expression_faces.iter().cloned());
    let active_contacts = incidence
        .recruitment_contacts
        .iter()
        .filter(|contact| {
            active_sites.contains(&contact.from) && active_sites.contains(&contact.to)
        })
        .cloned()
        .collect::<Vec<_>>();
    if active_contacts.is_empty() {
        return Err("the active operation/state cover returned no founded contacts".to_owned());
    }
    let state_fibres = fibres
        .iter()
        .map(|(before, builder)| StateFibre {
            occurrence: fibre_address(before, &builder.after),
            before_structural_word: before.clone(),
            transition_occurrences: builder.transitions.clone(),
            complete_after_structural_fibre: builder.after.clone(),
            parent_operations: builder.parents.clone(),
            source_paths_lineage: builder.source_paths.clone(),
        })
        .collect::<Vec<_>>();
    let shortest = shortest_closure(&adjacency, &reverse);
    let all_state_faces = adjacency
        .keys()
        .chain(adjacency.values().flatten())
        .filter(|face| face.as_str() != CLOSED)
        .cloned()
        .collect::<BTreeSet<_>>();
    let open_state_faces = all_state_faces
        .iter()
        .filter(|face| !shortest.contains_key(*face))
        .count();
    let reconvergences = entering
        .into_iter()
        .filter_map(|(state, entries)| {
            if state == CLOSED || entries.len() < 2 {
                return None;
            }
            Some(Reconvergence {
                state_structural_face: state,
                entering_transition_occurrences: entries
                    .iter()
                    .map(|entry| entry.0.clone())
                    .collect(),
                entering_parent_operations: entries
                    .iter()
                    .map(|entry| entry.1.clone())
                    .filter(|parent| !parent.is_empty())
                    .collect(),
            })
        })
        .collect::<Vec<_>>();
    let source_ablations = source_ablations(&active_transitions, &goal_structure, &fibres)?;
    let assigned_transitions = fibres
        .values()
        .map(|fibre| fibre.transitions.len())
        .sum::<usize>();
    let coverage = RouteCoverage {
        active_operations: incidence.active_carrier_operations.len(),
        active_transitions: active_transitions.len(),
        assigned_transitions,
        before_fibres: fibres.len(),
        plural_successor_fibres: fibres
            .values()
            .filter(|fibre| fibre.after.len() > 1)
            .count(),
        closed_passages,
        reachable_state_faces: shortest.len().saturating_sub(1),
        open_state_faces,
        reconvergences: reconvergences.len(),
        complete_at_returned_transition_grain: assigned_transitions == active_transitions.len(),
        total_descent_case_cover_established: false,
    };
    Ok(RouteSubstrateReturn {
        schema: "holonics.m6.receiver-addressed-operation-state-route.v2".to_owned(),
        source_occurrence: incidence.source_occurrence.clone(),
        receiver_question: ReceiverQuestion {
            target_operation: incidence.target_operation.clone(),
            target_type_expression: target.type_expression.clone(),
            target_defining_value_expression: target.defining_value_expression.clone(),
            target_seed_operations: incidence.target_seed_operations.clone(),
            selection_law: "the active carrier is the least operation-dependency closure returned by the target's founded contacts; state cells and successor fibres are induced by Lean's exact before/after goal return, never by syntax or tactic labels".to_owned(),
        },
        active_operations: incidence.active_carrier_operations.clone(),
        active_transition_occurrences,
        active_goal_occurrences,
        active_expression_faces,
        active_contacts,
        state_fibres,
        shortest_closure_fibres: shortest.into_values().filter(|face| face.state_structural_face != CLOSED).collect(),
        reconvergences,
        source_ablations,
        coverage,
        open_exterior: vec![
            "the returned transition complex is complete at S0's elaborated proof-state grain; it has not yet established the ten total descent receiver cases".to_owned(),
            "no independent theorem inhabitant has yet been emitted".to_owned(),
            "cultivation, held-out successor, native/Phoenix siblings, detached rest and product manifest remain open".to_owned(),
        ],
        truth_status: "established-bounded".to_owned(),
    })
}

#[derive(Default)]
struct FibreBuilder {
    transitions: BTreeSet<String>,
    after: BTreeSet<Vec<String>>,
    parents: BTreeSet<String>,
    source_paths: BTreeSet<String>,
}

fn structural_word(
    goals: &[String],
    structure: &BTreeMap<&str, &str>,
) -> Result<Vec<String>, String> {
    goals
        .iter()
        .map(|goal| {
            structure
                .get(goal.as_str())
                .map(|value| (*value).to_owned())
                .ok_or_else(|| format!("transition goal left the incidence: {goal}"))
        })
        .collect()
}

fn root_face(transition: &TransitionOccurrence) -> String {
    address(&[
        b"root",
        transition
            .parent_operation
            .as_deref()
            .unwrap_or("")
            .as_bytes(),
        transition.occurrence.as_bytes(),
    ])
}

fn shortest_closure(
    adjacency: &BTreeMap<String, BTreeSet<String>>,
    reverse: &BTreeMap<String, BTreeSet<String>>,
) -> BTreeMap<String, ShortestClosureFibre> {
    let mut distance = BTreeMap::from([(CLOSED.to_owned(), 0usize)]);
    let mut front = VecDeque::from([CLOSED.to_owned()]);
    while let Some(at) = front.pop_front() {
        let next = distance[&at] + 1;
        for predecessor in reverse.get(&at).into_iter().flatten() {
            if !distance.contains_key(predecessor) {
                distance.insert(predecessor.clone(), next);
                front.push_back(predecessor.clone());
            }
        }
    }
    distance
        .iter()
        .map(|(state, held)| {
            let complete_next_state_fibre = if *held == 0 {
                BTreeSet::new()
            } else {
                adjacency
                    .get(state)
                    .into_iter()
                    .flatten()
                    .filter(|next| distance.get(*next) == Some(&(held - 1)))
                    .cloned()
                    .collect()
            };
            (
                state.clone(),
                ShortestClosureFibre {
                    state_structural_face: state.clone(),
                    distance_to_closed_boundary: *held,
                    complete_next_state_fibre,
                },
            )
        })
        .collect()
}

fn source_ablations(
    transitions: &[&TransitionOccurrence],
    structure: &BTreeMap<&str, &str>,
    before: &BTreeMap<Vec<String>, FibreBuilder>,
) -> Result<Vec<SourceAblation>, String> {
    let paths = transitions
        .iter()
        .map(|transition| transition.source_path_lineage.clone())
        .collect::<BTreeSet<_>>();
    let mut returned = Vec::new();
    for path in paths {
        let removed = transitions
            .iter()
            .filter(|transition| transition.source_path_lineage == path)
            .map(|transition| transition.occurrence.clone())
            .collect::<BTreeSet<_>>();
        let mut after = BTreeMap::<Vec<String>, BTreeSet<Vec<String>>>::new();
        let mut removed_passages = BTreeSet::new();
        for transition in transitions
            .iter()
            .filter(|transition| transition.source_path_lineage != path)
        {
            let from = structural_word(&transition.before_goals, structure)?;
            let to = structural_word(&transition.after_goals, structure)?;
            after.entry(from).or_default().insert(to);
        }
        for transition in transitions
            .iter()
            .filter(|transition| transition.source_path_lineage == path)
        {
            let from = structural_word(&transition.before_goals, structure)?;
            let to = structural_word(&transition.after_goals, structure)?;
            removed_passages.insert(address(&[
                format!("{from:?}").as_bytes(),
                format!("{to:?}").as_bytes(),
                transition.occurrence.as_bytes(),
            ]));
        }
        let mut reopened = BTreeSet::new();
        let mut deformed = BTreeSet::new();
        let mut unchanged = 0usize;
        for (from, prior) in before {
            let key = fibre_address(from, &prior.after);
            match after.get(from) {
                None => {
                    reopened.insert(key);
                }
                Some(next) if next != &prior.after => {
                    deformed.insert(key);
                }
                Some(_) => unchanged += 1,
            }
        }
        returned.push(SourceAblation {
            source_path_lineage: path,
            removed_transition_occurrences: removed,
            removed_state_passages: removed_passages,
            reopened_before_fibres: reopened,
            deformed_before_fibres: deformed,
            unchanged_before_fibres: unchanged,
        });
    }
    Ok(returned)
}

fn fibre_address(before: &[String], after: &BTreeSet<Vec<String>>) -> String {
    address(&[
        format!("{before:?}").as_bytes(),
        format!("{after:?}").as_bytes(),
    ])
}

fn address(parts: &[&[u8]]) -> String {
    let mut hasher = Sha256::new();
    for part in parts {
        hasher.update((part.len() as u64).to_le_bytes());
        hasher.update(part);
    }
    hasher
        .finalize()
        .iter()
        .map(|octet| format!("{octet:02x}"))
        .collect()
}

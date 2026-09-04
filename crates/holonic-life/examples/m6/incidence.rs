//! The exact declaration/operation/state incidence returned from S0.
//!
//! The exterior Lean apparatus has already elaborated the addressed source and condensed repeated
//! expression standing. This owner joins those returned faces into one operation complex. Lean
//! names, paths, syntax and tactic labels remain attached realization testimony; founded contacts
//! use only addressed operations, transition occurrences and goal occurrences.

use std::collections::{BTreeMap, BTreeSet};

use holonic_structure::LocalSequence;
use life::returned_contact_cuda::{
    CudaReturnedContactExecutor, ReturnedContactCudaReceipt, ReturnedContactGroups,
    ReturnedContactRelation, ReturnedContactSparseFront,
};
use serde::Serialize;
use sha2::{Digest, Sha256};

use super::{
    causal::{ExpressionFace, MountedCausalReturn, TransportNode},
    source::MountedSource,
};

#[derive(Clone, Debug, Serialize)]
pub struct RecruitmentContact {
    pub occurrence: String,
    pub from: String,
    pub to: String,
    pub relation: String,
}

#[derive(Clone, Debug, Serialize)]
pub struct GoalOccurrence {
    pub occurrence: String,
    pub structural_face: String,
    pub source_path_lineage: String,
    pub parent_operation: Option<String>,
    pub target_expression: String,
    pub local_standing_expressions: Vec<String>,
    pub exterior_goal_face: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct TransitionOccurrence {
    pub occurrence: String,
    pub exterior_return_occurrence: String,
    pub source_path_lineage: String,
    pub parent_operation: Option<String>,
    pub before_goals: Vec<String>,
    pub after_goals: Vec<String>,
    pub source_span_exterior: (usize, usize),
    pub syntax_sha256_exterior: String,
    pub elaborator_exterior: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct TermOccurrence {
    pub occurrence: String,
    pub exterior_return_occurrence: String,
    pub source_path_lineage: String,
    pub parent_operation: Option<String>,
    pub expression: String,
    pub expected_type: Option<String>,
    pub source_span_exterior: (usize, usize),
    pub syntax_sha256_exterior: String,
    pub elaborator_exterior: String,
}

#[derive(Clone, Debug, Serialize)]
pub struct OperationOccurrence {
    pub occurrence: String,
    pub type_expression: String,
    pub defining_value_expression: Option<String>,
    pub source_module_lineage: String,
    pub declaration_exterior: String,
    pub kind_exterior: String,
    pub target_seed: bool,
    pub active_carrier: bool,
}

#[derive(Clone, Debug, Serialize)]
pub struct IncidenceWork {
    pub source_files: u64,
    pub expressions: u64,
    pub transport_nodes: u64,
    pub declaration_operations: u64,
    pub operation_contacts: u64,
    pub term_occurrences: u64,
    pub transition_occurrences: u64,
    pub goal_occurrences: u64,
    pub incidence_contacts: u64,
    pub active_carrier_operations: u64,
}

#[derive(Clone, Debug, Serialize)]
pub struct FoundedComplexFace {
    pub sites: usize,
    pub bonds: usize,
    pub ingress: usize,
    pub exposed: usize,
    pub faithful: bool,
    pub absent_contact_endpoints: Vec<String>,
}

#[derive(Clone, Debug, Serialize)]
pub struct IncidenceReturn {
    pub schema: String,
    pub source_occurrence: String,
    pub source_content_sha256: String,
    pub target_operation: String,
    pub target_seed_operations: BTreeSet<String>,
    pub active_carrier_operations: BTreeSet<String>,
    pub expressions: BTreeMap<String, ExpressionFace>,
    pub transport_nodes: BTreeMap<String, TransportNode>,
    pub operations: Vec<OperationOccurrence>,
    pub goals: Vec<GoalOccurrence>,
    pub transitions: Vec<TransitionOccurrence>,
    pub terms: Vec<TermOccurrence>,
    pub recruitment_contacts: Vec<RecruitmentContact>,
    pub incidence_work: IncidenceWork,
    pub founded_complex: FoundedComplexFace,
    pub exterior_faces_do_not_route: bool,
    pub truth_status: String,
}

#[derive(Debug, Serialize)]
pub struct ResidentJunctionReturn {
    pub schema: String,
    pub source_occurrence: String,
    pub semantic: ReturnedContactGroups,
    pub apparatus: ReturnedContactCudaReceipt,
    pub target_atlas: Vec<String>,
    pub occurrence_atlas: Vec<String>,
}

pub fn derive_causal(
    source: &MountedSource,
    causal: &MountedCausalReturn,
) -> Result<IncidenceReturn, String> {
    if source.manifest.occurrence != causal.manifest.source_occurrence
        || source.manifest.content_sha256 != causal.manifest.source_content_sha256
    {
        return Err(
            "the source occurrence and exterior causal return do not share lineage".to_owned(),
        );
    }
    let declarations = &causal.declarations;
    let mut expressions = declarations.expression_faces.clone();
    let mut transport_nodes = declarations.transport_nodes.clone();
    let mut operations = Vec::new();
    for operation in &declarations.declaration_operations {
        operations.push(OperationOccurrence {
            occurrence: operation.occurrence.clone(),
            type_expression: operation.type_face.clone(),
            defining_value_expression: operation.defining_value.clone(),
            source_module_lineage: operation.module_exterior.clone(),
            declaration_exterior: operation.declaration_exterior.clone(),
            kind_exterior: operation.kind_exterior.clone(),
            target_seed: declarations
                .target_seed_operations
                .contains(&operation.occurrence),
            active_carrier: declarations
                .carrier_operations
                .contains(&operation.occurrence),
        });
    }
    let mut contacts = declarations
        .operation_contacts
        .iter()
        .map(|contact| RecruitmentContact {
            occurrence: contact.occurrence.clone(),
            from: contact.from_operation.clone(),
            to: contact.to_operation.clone(),
            relation: "operation-reference".to_owned(),
        })
        .collect::<Vec<_>>();
    let mut goals_by_occurrence = BTreeMap::<String, GoalOccurrence>::new();
    let mut transitions = Vec::new();
    let mut terms = Vec::new();
    for returned in &causal.transitions {
        merge_expressions(&mut expressions, &returned.expression_faces)?;
        merge_transport_nodes(&mut transport_nodes, &returned.transport_nodes)?;
        for term in &returned.term_occurrences {
            let parent = term.parent_operation.as_deref().unwrap_or("");
            let occurrence = address(&[
                source.manifest.occurrence.as_bytes(),
                returned.source_path_exterior.as_bytes(),
                parent.as_bytes(),
                &term.start_byte.to_le_bytes(),
                &term.stop_byte.to_le_bytes(),
                term.syntax_sha256_exterior.as_bytes(),
                term.elaborator_exterior.as_bytes(),
                term.expression_face.as_bytes(),
                term.expected_type_face.as_deref().unwrap_or("").as_bytes(),
            ]);
            terms.push(TermOccurrence {
                occurrence: occurrence.clone(),
                exterior_return_occurrence: term.occurrence.clone(),
                source_path_lineage: returned.source_path_exterior.clone(),
                parent_operation: term.parent_operation.clone(),
                expression: term.expression_face.clone(),
                expected_type: term.expected_type_face.clone(),
                source_span_exterior: (term.start_byte, term.stop_byte),
                syntax_sha256_exterior: term.syntax_sha256_exterior.clone(),
                elaborator_exterior: term.elaborator_exterior.clone(),
            });
            if let Some(parent) = &term.parent_operation {
                contacts.push(contact(parent, &occurrence, "operation-term"));
            }
            contacts.push(contact(
                &occurrence,
                &term.expression_face,
                "term-expression",
            ));
            if let Some(expected) = &term.expected_type_face {
                contacts.push(contact(&occurrence, expected, "term-expected-type"));
            }
        }
        for transition in &returned.tactic_transitions {
            let parent = transition.parent_operation.as_deref().unwrap_or("");
            let goal_occurrence = |goal: &super::causal::GoalFace| {
                address(&[
                    source.manifest.occurrence.as_bytes(),
                    returned.source_path_exterior.as_bytes(),
                    parent.as_bytes(),
                    goal.occurrence.as_bytes(),
                ])
            };
            let before = transition
                .before
                .iter()
                .map(|goal| goal_occurrence(goal))
                .collect::<Vec<_>>();
            let after = transition
                .after
                .iter()
                .map(|goal| goal_occurrence(goal))
                .collect::<Vec<_>>();
            for goal in transition.before.iter().chain(&transition.after) {
                let occurrence = goal_occurrence(goal);
                let held = GoalOccurrence {
                    occurrence: occurrence.clone(),
                    structural_face: goal.structural_face.clone(),
                    source_path_lineage: returned.source_path_exterior.clone(),
                    parent_operation: transition.parent_operation.clone(),
                    target_expression: goal.target_face.clone(),
                    local_standing_expressions: goal
                        .local_standing
                        .iter()
                        .flat_map(|standing| {
                            std::iter::once(standing.type_face.clone())
                                .chain(standing.value_face.clone())
                        })
                        .collect(),
                    exterior_goal_face: goal.goal_occurrence_exterior.clone(),
                };
                if let Some(prior) = goals_by_occurrence.get(&held.occurrence) {
                    if prior.structural_face != held.structural_face
                        || prior.target_expression != held.target_expression
                        || prior.local_standing_expressions != held.local_standing_expressions
                    {
                        return Err(format!(
                            "one goal occurrence returned plural standing: {}",
                            held.occurrence
                        ));
                    }
                } else {
                    goals_by_occurrence.insert(held.occurrence.clone(), held);
                }
            }
            let before_word = before.join("|");
            let after_word = after.join("|");
            let occurrence = address(&[
                source.manifest.occurrence.as_bytes(),
                returned.source_path_exterior.as_bytes(),
                parent.as_bytes(),
                &transition.start_byte.to_le_bytes(),
                &transition.stop_byte.to_le_bytes(),
                transition.syntax_sha256_exterior.as_bytes(),
                transition.elaborator_exterior.as_bytes(),
                before_word.as_bytes(),
                after_word.as_bytes(),
            ]);
            if let Some(parent) = &transition.parent_operation {
                contacts.push(contact(parent, &occurrence, "operation-transition"));
            }
            for goal in &before {
                contacts.push(contact(goal, &occurrence, "before-transition"));
            }
            for goal in &after {
                contacts.push(contact(&occurrence, goal, "after-transition"));
            }
            transitions.push(TransitionOccurrence {
                occurrence,
                exterior_return_occurrence: transition.occurrence.clone(),
                source_path_lineage: returned.source_path_exterior.clone(),
                parent_operation: transition.parent_operation.clone(),
                before_goals: before,
                after_goals: after,
                source_span_exterior: (transition.start_byte, transition.stop_byte),
                syntax_sha256_exterior: transition.syntax_sha256_exterior.clone(),
                elaborator_exterior: transition.elaborator_exterior.clone(),
            });
        }
    }
    operations.sort_by(|left, right| left.occurrence.cmp(&right.occurrence));
    terms.sort_by(|left, right| left.occurrence.cmp(&right.occurrence));
    transitions.sort_by(|left, right| left.occurrence.cmp(&right.occurrence));
    refuse_divergent_duplicate_terms(&terms)?;
    refuse_divergent_duplicate_transitions(&transitions)?;
    terms.dedup_by(|left, right| left.occurrence == right.occurrence);
    transitions.dedup_by(|left, right| left.occurrence == right.occurrence);
    contacts.sort_by(|left, right| left.occurrence.cmp(&right.occurrence));
    contacts.dedup_by(|left, right| left.occurrence == right.occurrence);
    let goals = goals_by_occurrence.into_values().collect::<Vec<_>>();
    let sites = operations
        .iter()
        .map(|operation| operation.occurrence.clone())
        .chain(expressions.keys().cloned())
        .chain(transport_nodes.keys().cloned())
        .chain(terms.iter().map(|term| term.occurrence.clone()))
        .chain(
            transitions
                .iter()
                .map(|transition| transition.occurrence.clone()),
        )
        .chain(goals.iter().map(|goal| goal.occurrence.clone()))
        .collect::<BTreeSet<_>>();
    let absent_contact_endpoints = contacts
        .iter()
        .flat_map(|contact| [&contact.from, &contact.to])
        .filter(|endpoint| !sites.contains(*endpoint))
        .cloned()
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect::<Vec<_>>();
    if !absent_contact_endpoints.is_empty() {
        return Err(format!(
            "the exact incidence has absent endpoints: {absent_contact_endpoints:?}"
        ));
    }
    let ingress = contacts
        .iter()
        .map(|contact| contact.to.clone())
        .collect::<BTreeSet<_>>();
    let exposed = sites.iter().filter(|site| !ingress.contains(*site)).count();
    let incidence_work = IncidenceWork {
        source_files: u64::try_from(causal.transitions.len())
            .map_err(|_| "source file count".to_owned())?,
        expressions: u64::try_from(expressions.len()).map_err(|_| "expression count".to_owned())?,
        transport_nodes: u64::try_from(transport_nodes.len())
            .map_err(|_| "transport-node count".to_owned())?,
        declaration_operations: u64::try_from(operations.len())
            .map_err(|_| "operation count".to_owned())?,
        operation_contacts: u64::try_from(declarations.operation_contacts.len())
            .map_err(|_| "operation contact count".to_owned())?,
        term_occurrences: u64::try_from(terms.len()).map_err(|_| "term count".to_owned())?,
        transition_occurrences: u64::try_from(transitions.len())
            .map_err(|_| "transition count".to_owned())?,
        goal_occurrences: u64::try_from(goals.len()).map_err(|_| "goal count".to_owned())?,
        incidence_contacts: u64::try_from(contacts.len())
            .map_err(|_| "contact count".to_owned())?,
        active_carrier_operations: u64::try_from(declarations.carrier_operations.len())
            .map_err(|_| "carrier count".to_owned())?,
    };
    Ok(IncidenceReturn {
        schema: "holonics.m6.exact-operation-state-incidence.v3".to_owned(),
        source_occurrence: source.manifest.occurrence.clone(),
        source_content_sha256: source.manifest.content_sha256.clone(),
        target_operation: declarations.target_operation.clone(),
        target_seed_operations: declarations.target_seed_operations.clone(),
        active_carrier_operations: declarations.carrier_operations.clone(),
        expressions,
        transport_nodes,
        operations,
        goals,
        transitions,
        terms,
        recruitment_contacts: contacts,
        founded_complex: FoundedComplexFace {
            sites: sites.len(),
            bonds: incidence_work.incidence_contacts as usize,
            ingress: ingress.len(),
            exposed,
            faithful: true,
            absent_contact_endpoints,
        },
        incidence_work,
        exterior_faces_do_not_route: true,
        truth_status: "established-bounded".to_owned(),
    })
}

fn refuse_divergent_duplicate_terms(terms: &[TermOccurrence]) -> Result<(), String> {
    for pair in terms.windows(2) {
        if pair[0].occurrence == pair[1].occurrence && pair[0] != pair[1] {
            return Err(format!(
                "one term occurrence returned plural standing: {}",
                pair[0].occurrence
            ));
        }
    }
    Ok(())
}

fn refuse_divergent_duplicate_transitions(
    transitions: &[TransitionOccurrence],
) -> Result<(), String> {
    for pair in transitions.windows(2) {
        if pair[0].occurrence == pair[1].occurrence && pair[0] != pair[1] {
            return Err(format!(
                "one transition occurrence returned plural standing: {}",
                pair[0].occurrence
            ));
        }
    }
    Ok(())
}

fn merge_expressions(
    held: &mut BTreeMap<String, ExpressionFace>,
    entering: &BTreeMap<String, ExpressionFace>,
) -> Result<(), String> {
    for (occurrence, face) in entering {
        if let Some(prior) = held.get_mut(occurrence) {
            if prior.occurrence != face.occurrence
                || prior.structural_face != face.structural_face
                || prior.root_transport_node != face.root_transport_node
            {
                return Err(format!("expression occurrence reopened: {occurrence}"));
            }
            prior
                .lean_hashes_exterior
                .extend(face.lean_hashes_exterior.iter().cloned());
            prior
                .rendered_faces_exterior
                .extend(face.rendered_faces_exterior.iter().cloned());
        } else {
            held.insert(occurrence.clone(), face.clone());
        }
    }
    Ok(())
}

fn merge_transport_nodes(
    held: &mut BTreeMap<String, TransportNode>,
    entering: &BTreeMap<String, TransportNode>,
) -> Result<(), String> {
    for (occurrence, node) in entering {
        if let Some(prior) = held.get(occurrence) {
            if prior != node {
                return Err(format!("transport-node occurrence reopened: {occurrence}"));
            }
        } else {
            held.insert(occurrence.clone(), node.clone());
        }
    }
    Ok(())
}

fn contact(from: &str, to: &str, relation: &str) -> RecruitmentContact {
    RecruitmentContact {
        occurrence: address(&[from.as_bytes(), to.as_bytes(), relation.as_bytes()]),
        from: from.to_owned(),
        to: to.to_owned(),
        relation: relation.to_owned(),
    }
}

/// One continuing resident owner for the whole exact incidence and every later active cut.
pub struct ResidentJunctionOwner {
    card: CudaReturnedContactExecutor,
}

impl ResidentJunctionOwner {
    pub fn new() -> Result<Self, String> {
        let card = CudaReturnedContactExecutor::new(0)
            .map_err(|error| format!("mount resident junction owner: {error}"))?;
        Ok(Self { card })
    }

    pub fn enact(
        &mut self,
        source_occurrence: &str,
        contacts: &[RecruitmentContact],
    ) -> Result<ResidentJunctionReturn, String> {
        let mut vertices = BTreeSet::new();
        for contact in contacts {
            vertices.insert(contact.from.clone());
            vertices.insert(contact.to.clone());
        }
        let target_atlas = vertices.into_iter().collect::<Vec<_>>();
        let addresses = target_atlas
            .iter()
            .cloned()
            .enumerate()
            .map(|(at, occurrence)| (occurrence, at))
            .collect::<BTreeMap<_, _>>();
        let mut ordered = contacts.iter().collect::<Vec<_>>();
        ordered.sort_by(|left, right| {
            (addresses[&left.to], left.occurrence.as_str())
                .cmp(&(addresses[&right.to], right.occurrence.as_str()))
        });
        let occurrence_atlas = ordered
            .iter()
            .map(|contact| contact.occurrence.clone())
            .collect::<Vec<_>>();
        let mut rows = LocalSequence::with_capacity(ordered.len());
        for (at, contact) in ordered.into_iter().enumerate() {
            let target = u32::try_from(addresses[&contact.to])
                .map_err(|_| "resident target extent".to_owned())?;
            let occurrence = u32::try_from(at).map_err(|_| "resident contact extent".to_owned())?;
            let row = ReturnedContactRelation::new(target, occurrence, false, true)
                .ok_or_else(|| "resident junction relation refused".to_owned())?;
            rows.push(row);
        }
        let front = ReturnedContactSparseFront::new(addresses.len(), contacts.len(), rows)
            .map_err(|error| format!("found resident junction front: {error}"))?;
        let returned = self
            .card
            .enact_sparse(&front)
            .map_err(|error| format!("enact resident junction population: {error}"))?;
        Ok(ResidentJunctionReturn {
            schema: "holonics.m6.resident-junction-return.v2".to_owned(),
            source_occurrence: source_occurrence.to_owned(),
            semantic: returned.semantic,
            apparatus: returned.apparatus,
            target_atlas,
            occurrence_atlas,
        })
    }
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

use super::*;
use super::{codec::*, types::*};

pub(super) fn order_relation_path(
    selected: &BTreeSet<usize>,
    clauses: &[RelationalClause],
) -> Vec<usize> {
    let mut incoming = BTreeMap::<usize, usize>::new();
    let mut outgoing = BTreeMap::<usize, BTreeSet<usize>>::new();
    for at in selected {
        incoming.insert(*at, 0);
    }
    for left in selected {
        for right in selected {
            if left == right {
                continue;
            }
            let carries = if clauses[*left].passage == clauses[*right].passage {
                // A passage is already caused chronology. A repeated noun in its later clause
                // cannot reverse that occurrence simply because it also touches an earlier face.
                clauses[*left].identity < clauses[*right].identity
            } else {
                !shared_caused_entity_face(
                    &clause_output_face(&clauses[*left]),
                    &clauses[*left].relation,
                    &clauses[*right].subject.identity,
                )
                .is_empty()
            };
            if carries && outgoing.entry(*left).or_default().insert(*right) {
                *incoming.entry(*right).or_default() += 1;
            }
        }
    }
    let mut ready = incoming
        .iter()
        .filter_map(|(at, degree)| (*degree == 0).then_some(*at))
        .collect::<BTreeSet<_>>();
    let mut ordered = Vec::new();
    while let Some(at) = ready.iter().next().copied() {
        ready.remove(&at);
        ordered.push(at);
        if let Some(targets) = outgoing.get(&at) {
            for target in targets {
                if let Some(degree) = incoming.get_mut(target) {
                    *degree = degree.saturating_sub(1);
                    if *degree == 0 {
                        ready.insert(*target);
                    }
                }
            }
        }
    }
    if ordered.len() != selected.len() {
        for at in selected {
            if !ordered.contains(at) {
                ordered.push(*at);
            }
        }
    }
    ordered
}

pub(super) fn relational_join(
    left: &RelationalClause,
    right: &RelationalClause,
    conduct: RelationalChannelConduct,
    recurrence_population: BigUint,
) -> RelationalJoin {
    RelationalJoin {
        from_clause: left.identity.clone(),
        to_clause: right.identity.clone(),
        shared_entity_faces: clause_shared_entity_faces(left, right),
        shared_passage: (left.passage == right.passage).then(|| left.passage.clone()),
        conduct,
        recurrence_population,
    }
}

#[derive(Clone)]
pub(super) struct RelationalTransportEdge {
    pub(super) from: usize,
    pub(super) to: usize,
    pub(super) identity: String,
}

pub(super) fn transport_passage_identity(join: &RelationalJoin) -> String {
    let faces = join
        .shared_entity_faces
        .iter()
        .map(String::as_str)
        .collect::<Vec<_>>()
        .join("+");
    let passage = join.shared_passage.as_deref().unwrap_or("-");
    let conduct = match join.conduct {
        RelationalChannelConduct::Copresent => "copresent",
        RelationalChannelConduct::SourceContinuous => "source-continuous",
        RelationalChannelConduct::Caused => "caused",
        RelationalChannelConduct::Ride => "ride",
        RelationalChannelConduct::Open => "open",
    };
    format!(
        "{}=>{}[faces={faces};passage={passage};conduct={conduct};recurrence={}]",
        join.from_clause, join.to_clause, join.recurrence_population
    )
}

pub(super) fn transport_adjacency(
    clause_population: usize,
    edges: &[RelationalTransportEdge],
) -> Vec<Vec<(usize, usize)>> {
    let mut adjacency = vec![Vec::new(); clause_population];
    for (edge_at, edge) in edges.iter().enumerate() {
        adjacency[edge.from].push((edge.to, edge_at));
        adjacency[edge.to].push((edge.from, edge_at));
    }
    for neighborhood in &mut adjacency {
        neighborhood.sort();
    }
    adjacency
}

pub(super) fn transport_components(
    clauses: &[RelationalClause],
    adjacency: &[Vec<(usize, usize)>],
) -> Vec<BTreeSet<usize>> {
    let mut unseen = (0..clauses.len()).collect::<BTreeSet<_>>();
    let mut components = Vec::new();
    while let Some(root) = unseen.iter().next().copied() {
        let mut component = BTreeSet::from([root]);
        let mut frontier = LocalQueue::from_iter([root]);
        unseen.remove(&root);
        while let Some(at) = frontier.pop_front() {
            for (next, _) in &adjacency[at] {
                if unseen.remove(next) {
                    component.insert(*next);
                    frontier.push_back(*next);
                }
            }
        }
        components.push(component);
    }
    components
}

pub(super) fn transport_holonomy(
    clauses: &[RelationalClause],
    edges: &[RelationalTransportEdge],
) -> Vec<RelationalHolonomyGenerator> {
    let mut tree = vec![Vec::<(usize, usize)>::new(); clauses.len()];
    let mut generators = Vec::new();
    for (edge_at, edge) in edges.iter().enumerate() {
        if let Some(return_path) = tree_transport_path(edge.to, edge.from, &tree, edges) {
            let mut ordered_return = vec![RelationalHolonomyStep {
                passage: edge.identity.clone(),
                hand: RelationalTransportHand::Forward,
            }];
            ordered_return.extend(return_path);
            generators.push(RelationalHolonomyGenerator {
                chord: edge.identity.clone(),
                ordered_return,
            });
        } else {
            tree[edge.from].push((edge.to, edge_at));
            tree[edge.to].push((edge.from, edge_at));
        }
    }
    generators
}

pub(super) fn tree_transport_path(
    source: usize,
    target: usize,
    tree: &[Vec<(usize, usize)>],
    edges: &[RelationalTransportEdge],
) -> Option<Vec<RelationalHolonomyStep>> {
    let mut prior = BTreeMap::<usize, (usize, usize)>::new();
    let mut frontier = LocalQueue::from_iter([source]);
    let mut reached = BTreeSet::from([source]);
    while let Some(at) = frontier.pop_front() {
        if at == target {
            break;
        }
        for (next, edge_at) in &tree[at] {
            if reached.insert(*next) {
                prior.insert(*next, (at, *edge_at));
                frontier.push_back(*next);
            }
        }
    }
    if !reached.contains(&target) {
        return None;
    }
    let mut reversed = Vec::<(usize, usize, usize)>::new();
    let mut at = target;
    while at != source {
        let (previous, edge_at) = prior.get(&at).copied()?;
        reversed.push((previous, at, edge_at));
        at = previous;
    }
    reversed.reverse();
    Some(
        reversed
            .into_iter()
            .map(|(from, _, edge_at)| {
                let edge = &edges[edge_at];
                RelationalHolonomyStep {
                    passage: edge.identity.clone(),
                    hand: if edge.from == from {
                        RelationalTransportHand::Forward
                    } else {
                        RelationalTransportHand::Reverse
                    },
                }
            })
            .collect(),
    )
}

pub(super) fn realize_relation_fibers(
    clauses: &[RelationalClause],
    parse_fibers: &[RelationalParseFiber],
    inherited_surfaces: &[Vec<String>],
) -> Result<Vec<RelationalRealization>, RelationalLanguageError> {
    // Parse ambiguity is already an exact product of local fibers.  Enumerating that product is
    // neither additional knowledge nor a lawful prerequisite for an outward receiver.  Expose
    // the selected section and every one-fiber variation, while `factorized_parse_population`
    // retains the complete product cardinality on the thought current.
    let mut paths = vec![clauses.to_vec()];
    let mut path_identities = BTreeSet::from([clauses
        .iter()
        .map(|clause| clause.identity.clone())
        .collect::<Vec<_>>()]);
    for (clause_at, clause) in clauses.iter().enumerate() {
        let Some(fiber) = parse_fibers
            .iter()
            .find(|fiber| fiber.selected_clause == clause.identity)
        else {
            continue;
        };
        for alternative in &fiber.alternatives {
            if alternative.identity == clause.identity {
                continue;
            }
            let mut path = clauses.to_vec();
            path[clause_at] = alternative.clone();
            let identities = path
                .iter()
                .map(|member| member.identity.clone())
                .collect::<Vec<_>>();
            if path_identities.insert(identities) {
                paths.push(path);
            }
        }
    }
    let mut realizations = Vec::new();
    for path in paths {
        realizations.extend(realize_relation_path(&path, inherited_surfaces)?);
    }
    realizations.sort_by(|left, right| {
        left.clauses
            .iter()
            .map(|clause| clause.relation_clause.as_str())
            .cmp(
                right
                    .clauses
                    .iter()
                    .map(|clause| clause.relation_clause.as_str()),
            )
            .then_with(|| left.voice_dual.cmp(&right.voice_dual).reverse())
            .then_with(|| left.text.cmp(&right.text))
    });
    realizations.dedup_by(|left, right| {
        left.text == right.text
            && left
                .clauses
                .iter()
                .map(|clause| clause.relation_clause.as_str())
                .eq(right
                    .clauses
                    .iter()
                    .map(|clause| clause.relation_clause.as_str()))
    });
    Ok(realizations)
}

pub(super) fn parse_fiber_population(
    clauses: &[RelationalClause],
    parse_fibers: &[RelationalParseFiber],
) -> BigUint {
    clauses
        .iter()
        .fold(BigUint::from(1u8), |population, clause| {
            let local = parse_fibers
                .iter()
                .find(|fiber| fiber.selected_clause == clause.identity)
                .map_or(1usize, |fiber| fiber.alternatives.len().max(1));
            population * BigUint::from(local)
        })
}

pub(super) fn realize_relation_path(
    clauses: &[RelationalClause],
    inherited_surfaces: &[Vec<String>],
) -> Result<Vec<RelationalRealization>, RelationalLanguageError> {
    let dual = realize_clauses(clauses, inherited_surfaces, true)?;
    let semantic = realize_clauses(clauses, inherited_surfaces, false)?;
    let mut realizations = vec![dual];
    if realizations[0].text != semantic.text {
        realizations.push(semantic);
    }
    Ok(realizations)
}

pub(super) fn realize_clauses(
    clauses: &[RelationalClause],
    inherited_surfaces: &[Vec<String>],
    voice_dual: bool,
) -> Result<RelationalRealization, RelationalLanguageError> {
    let mut realized = Vec::new();
    for clause in clauses {
        let tokens = if voice_dual {
            dual_clause_tokens(clause)
        } else {
            semantic_clause_tokens(clause)
        };
        if tokens.is_empty() {
            return Err(RelationalLanguageError::MalformedClause);
        }
        let inherited_contiguous = inherited_surfaces.iter().any(|surface| {
            surface
                .windows(tokens.len())
                .any(|window| equal_folded(window, &tokens))
        });
        let text = sentence_surface(&tokens);
        realized.push(RelationalRealizationClause {
            relation_clause: clause.identity.clone(),
            text,
            sources: BTreeSet::from([clause.source.clone()]),
            passages: BTreeSet::from([clause.passage.clone()]),
            inherited_contiguous,
        });
    }
    let text = realized
        .iter()
        .map(|clause| clause.text.as_str())
        .collect::<Vec<_>>()
        .join(" ");
    let inherited_contiguous = inherited_surfaces.iter().any(|surface| {
        let tokens = word_tokens(&text);
        surface
            .windows(tokens.len())
            .any(|window| equal_folded(window, &tokens))
    });
    Ok(RelationalRealization {
        text,
        clauses: realized,
        voice_dual,
        inherited_contiguous,
    })
}

pub(super) fn dual_clause_tokens(clause: &RelationalClause) -> Vec<String> {
    match clause.witnessed_voice {
        RelationalClauseVoice::Active => passive_tokens(clause),
        RelationalClauseVoice::Passive => active_tokens(clause),
        RelationalClauseVoice::Copular => definition_reverse_tokens(clause),
    }
}

pub(super) fn semantic_clause_tokens(clause: &RelationalClause) -> Vec<String> {
    match clause.witnessed_voice {
        RelationalClauseVoice::Active | RelationalClauseVoice::Passive => active_tokens(clause),
        RelationalClauseVoice::Copular => {
            let mut tokens = clause.subject.surface.clone();
            if let Some(modality) = &clause.modality {
                tokens.push(modality.clone());
                tokens.push("be".to_owned());
            } else {
                tokens.push(if entity_is_plural(&clause.subject) {
                    "are".to_owned()
                } else {
                    "is".to_owned()
                });
            }
            tokens.extend(clause.object.surface.iter().cloned());
            capitalize_first(tokens)
        }
    }
}

pub(super) fn active_tokens(clause: &RelationalClause) -> Vec<String> {
    let mut tokens = clause.subject.surface.clone();
    if let Some(modality) = &clause.modality {
        tokens.push(modality.clone());
        tokens.push(clause.relation.clone());
    } else {
        tokens.push(present_relation(
            &clause.relation,
            entity_is_plural(&clause.subject),
        ));
    }
    tokens.extend(clause.object.surface.iter().cloned());
    capitalize_first(tokens)
}

pub(super) fn passive_tokens(clause: &RelationalClause) -> Vec<String> {
    let mut tokens = clause.object.surface.clone();
    if let Some(modality) = &clause.modality {
        tokens.push(modality.clone());
        tokens.push("be".to_owned());
    } else {
        tokens.push(if entity_is_plural(&clause.object) {
            "are".to_owned()
        } else {
            "is".to_owned()
        });
    }
    tokens.push(past_participle(&clause.relation));
    tokens.push("by".to_owned());
    tokens.extend(objective_entity_surface(&clause.subject));
    capitalize_first(tokens)
}

pub(super) fn definition_reverse_tokens(clause: &RelationalClause) -> Vec<String> {
    let mut tokens = clause.object.surface.clone();
    if let Some(modality) = &clause.modality {
        tokens.push(modality.clone());
        tokens.push("define".to_owned());
    } else {
        tokens.push("defines".to_owned());
    }
    tokens.extend(clause.subject.surface.iter().cloned());
    capitalize_first(tokens)
}

pub(super) fn objective_entity_surface(entity: &RelationalEntity) -> Vec<String> {
    entity
        .surface
        .iter()
        .map(|word| match word.as_str() {
            "i" => "me".to_owned(),
            "we" => "us".to_owned(),
            "he" => "him".to_owned(),
            "she" => "her".to_owned(),
            "they" => "them".to_owned(),
            _ => word.clone(),
        })
        .collect()
}

pub(super) fn clause_reaches(clause: &RelationalClause, region: &BTreeSet<String>) -> bool {
    // One requested entity region must be received by one side of the relation. Combining one
    // token from the subject with another from the object manufactures a face which neither
    // receiver actually carries (for example, `language` in an owned type plus `episode` in its
    // owner). Cross-clause motion remains available through `relation_joins`; it cannot rewrite
    // an entity boundary merely to close a question.
    region.is_subset(&clause.subject.identity) || region.is_subset(&clause.object.identity)
}

pub(super) fn clause_shared_entity_faces(
    left: &RelationalClause,
    right: &RelationalClause,
) -> BTreeSet<String> {
    let mut shared = BTreeSet::new();
    let left_faces = [&left.subject.identity, &left.object.identity];
    let right_faces = [&right.subject.identity, &right.object.identity];
    for left_face in left_faces {
        for right_face in right_faces {
            shared.extend(shared_entity_face(left_face, right_face));
        }
    }
    let left_output = clause_output_face(left);
    let right_output = clause_output_face(right);
    for right_face in right_faces {
        shared.extend(shared_caused_entity_face(
            &left_output,
            &left.relation,
            right_face,
        ));
    }
    for left_face in left_faces {
        shared.extend(shared_caused_entity_face(
            &right_output,
            &right.relation,
            left_face,
        ));
    }
    shared
}

/// The enacted relation is itself a phase of its patient. `current` and `advanced current` are not
/// joined by the generic noun alone; the first clause emits the latter as a caused face.
pub(super) fn clause_output_face(clause: &RelationalClause) -> BTreeSet<String> {
    let mut output = clause.object.identity.clone();
    output.insert(clause.relation.clone());
    output
}

/// Two entities meet only when one complete received face is carried by the other. A coincident
/// adjective such as `relational` is not itself an edge between otherwise different bodies.
pub(super) fn shared_entity_face(
    left: &BTreeSet<String>,
    right: &BTreeSet<String>,
) -> BTreeSet<String> {
    if left == right {
        left.clone()
    } else {
        BTreeSet::new()
    }
}

pub(super) fn shared_caused_entity_face(
    output: &BTreeSet<String>,
    relation: &str,
    received: &BTreeSet<String>,
) -> BTreeSet<String> {
    let shared = if output == received {
        output.clone()
    } else if received.is_subset(output) && received.contains(relation) {
        received.clone()
    } else if output.is_subset(received) && output.contains(relation) {
        output.clone()
    } else {
        BTreeSet::new()
    };
    if shared.len() == 1 && shared.contains(relation) {
        BTreeSet::new()
    } else {
        shared
    }
}

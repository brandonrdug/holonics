use super::transport::{clause_output_face, clause_shared_entity_faces};
use super::types::*;
use super::*;

pub(super) fn receive_deictic_antecedents(
    selected: &mut BTreeSet<usize>,
    clauses: &[RelationalClause],
) {
    loop {
        let mut founded = ExactSet::<usize>::new();
        for at in selected.iter().copied() {
            let clause = &clauses[at];
            let deictic = clause.subject.surface.iter().any(|word| {
                matches!(
                    word.as_str(),
                    "this" | "that" | "these" | "those" | "it" | "its"
                )
            });
            if !deictic {
                continue;
            }
            if let Some(prior) = clauses
                .iter()
                .enumerate()
                .filter(|(prior_at, prior)| {
                    *prior_at != at
                        && prior.passage == clause.passage
                        && prior.identity < clause.identity
                })
                .max_by(|(_, left), (_, right)| left.identity.cmp(&right.identity))
                .map(|(prior_at, _)| prior_at)
            {
                if !selected.contains(&prior) {
                    founded.insert(prior);
                }
            }
        }
        if founded.is_empty() {
            break;
        }
        selected.extend(founded);
    }
}

pub(super) fn split_coordinated_clause_words(
    passage: &MorphologicalLanguagePassage,
    words: &[String],
) -> Result<Vec<Vec<String>>, RelationalLanguageError> {
    let lower = words
        .iter()
        .map(|word| word.to_lowercase())
        .collect::<Vec<_>>();
    for at in 1..words.len().saturating_sub(1) {
        if lower[at] != "and" {
            continue;
        }
        let left = words[..at].to_vec();
        let right = words[at + 1..].to_vec();
        let left_clause = parse_clause("coordination-left".to_owned(), passage, &left)?;
        let mut right_clause = parse_clause("coordination-right".to_owned(), passage, &right)?;
        let mut carried_right = right.clone();
        if right_clause.is_none() && left_clause.is_some() {
            if let Some(prefix) = coordinated_subject_prefix(&left) {
                carried_right = prefix;
                carried_right.extend(right.iter().cloned());
                right_clause = parse_clause(
                    "coordination-right-carried".to_owned(),
                    passage,
                    &carried_right,
                )?;
            }
        }
        if left_clause.is_some() && right_clause.is_some() {
            let mut clauses = split_coordinated_clause_words(passage, &left)?;
            clauses.extend(split_coordinated_clause_words(passage, &carried_right)?);
            return Ok(clauses);
        }
    }
    Ok(vec![words.to_vec()])
}

/// Coordinate ellipsis carries the already witnessed subject and modal into a later bare
/// predicate: `we could grow X and condition Y` is two clauses, not one object whose interior
/// happens to contain `and condition`.
pub(super) fn coordinated_subject_prefix(words: &[String]) -> Option<Vec<String>> {
    let lower = words
        .iter()
        .map(|word| word.to_lowercase())
        .collect::<Vec<_>>();
    if let Some(modal_at) = lower.iter().position(|word| is_modal(word)) {
        return (modal_at > 0).then(|| words[..=modal_at].to_vec());
    }
    let predicate_at = lower
        .iter()
        .enumerate()
        .skip(1)
        .find(|(at, word)| *at + 1 < lower.len() && is_likely_finite_relation(word))
        .map(|(at, _)| at)?;
    (predicate_at > 0).then(|| words[..predicate_at].to_vec())
}

pub(super) fn parse_fiber(
    identity: String,
    passage: &MorphologicalLanguagePassage,
    words: &[String],
    selected: RelationalClause,
) -> Result<RelationalParseFiber, RelationalLanguageError> {
    let mut alternatives = vec![selected.clone()];
    if selected.witnessed_voice == RelationalClauseVoice::Passive {
        let lower = words
            .iter()
            .map(|word| word.to_lowercase())
            .collect::<Vec<_>>();
        if let Some(be_at) = lower.iter().position(|word| is_be(word)) {
            if be_at > 0 && be_at + 1 < words.len() {
                let subject = entity(&words[..be_at]);
                let object = entity(&words[be_at + 1..]);
                if !subject.identity.is_empty() && !object.identity.is_empty() {
                    alternatives.push(RelationalClause {
                        identity: format!("{identity}::alternative::copular"),
                        passage: passage.identity.clone(),
                        source: passage.source.clone(),
                        receiver: passage.receiver,
                        source_order: selected.source_order,
                        source_order_declared: selected.source_order_declared,
                        source_local_step: selected.source_local_step,
                        subject,
                        relation: "be".to_owned(),
                        modality: selected.modality.clone(),
                        object,
                        witnessed_voice: RelationalClauseVoice::Copular,
                        witnessed_surface: sentence_surface(words),
                    });
                }
            }
        }
    }
    alternatives.sort_by(|left, right| left.identity.cmp(&right.identity));
    alternatives.dedup_by(|left, right| {
        left.subject == right.subject
            && left.relation == right.relation
            && left.modality == right.modality
            && left.object == right.object
            && left.witnessed_voice == right.witnessed_voice
    });
    let selected_clause = selected.identity;
    // Keep the inherited traversal first even when its lexical identity sorts after an alternate.
    if let Some(at) = alternatives
        .iter()
        .position(|alternative| alternative.identity == selected_clause)
    {
        alternatives.swap(0, at);
    }
    Ok(RelationalParseFiber {
        identity,
        selected_clause,
        alternatives,
    })
}

pub(super) fn parse_clause(
    identity: String,
    passage: &MorphologicalLanguagePassage,
    words: &[String],
) -> Result<Option<RelationalClause>, RelationalLanguageError> {
    if words.len() < 3 {
        return Ok(None);
    }
    let lower = words
        .iter()
        .map(|word| word.to_lowercase())
        .collect::<Vec<_>>();
    if let Some(be_at) = lower.iter().position(|word| is_be(word)) {
        if be_at > 0 && be_at + 1 < words.len() {
            let modality = lower
                .get(be_at.saturating_sub(1))
                .filter(|word| is_modal(word))
                .cloned();
            let subject_end = if modality.is_some() { be_at - 1 } else { be_at };
            let relation_at = be_at + 1;
            if is_participle(&lower[relation_at]) {
                if let Some(preposition_at) =
                    (relation_at + 1..lower.len()).find(|at| is_relational_preposition(&lower[*at]))
                {
                    if preposition_at + 1 < words.len() {
                        let passive_subject = entity(&words[..subject_end]);
                        let passive_agent = entity(&words[preposition_at + 1..]);
                        if !passive_subject.identity.is_empty()
                            && !passive_agent.identity.is_empty()
                        {
                            return Ok(Some(RelationalClause {
                                identity,
                                passage: passage.identity.clone(),
                                source: passage.source.clone(),
                                receiver: passage.receiver,
                                source_order: passage.source_order,
                                source_order_declared: passage.source_order_declared,
                                source_local_step: 0,
                                subject: passive_agent,
                                relation: verb_lemma(&lower[relation_at]),
                                modality: modality.clone(),
                                object: passive_subject,
                                witnessed_voice: RelationalClauseVoice::Passive,
                                witnessed_surface: sentence_surface(words),
                            }));
                        }
                    }
                }
            }
            let subject = entity(&words[..subject_end]);
            let object = entity(&words[be_at + 1..]);
            if !subject.identity.is_empty() && !object.identity.is_empty() {
                return Ok(Some(RelationalClause {
                    identity,
                    passage: passage.identity.clone(),
                    source: passage.source.clone(),
                    receiver: passage.receiver,
                    source_order: passage.source_order,
                    source_order_declared: passage.source_order_declared,
                    source_local_step: 0,
                    subject,
                    relation: "be".to_owned(),
                    modality,
                    object,
                    witnessed_voice: RelationalClauseVoice::Copular,
                    witnessed_surface: sentence_surface(words),
                }));
            }
        }
    }

    let predicate_at = lower
        .iter()
        .enumerate()
        .find_map(|(at, word)| {
            is_modal(word)
                .then(|| at.checked_add(1).filter(|next| *next < lower.len()))
                .flatten()
        })
        .or_else(|| {
            // An attributive participle ("returned token") may itself be a known relation, but
            // it does not own the clause's finite current. Prefer an unambiguously finite form.
            lower
                .iter()
                .enumerate()
                .skip(1)
                .filter(|(at, _)| *at + 1 < lower.len())
                .find(|(_, word)| is_likely_finite_relation(word) && !is_participle(word))
                .map(|(at, _)| at)
        })
        .or_else(|| {
            lower
                .iter()
                .enumerate()
                .skip(1)
                .filter(|(at, _)| *at + 1 < lower.len())
                .find(|(_, word)| is_likely_finite_relation(word))
                .map(|(at, _)| at)
        });
    let Some(predicate_at) = predicate_at else {
        return Ok(None);
    };
    let subject_end = if predicate_at > 0 && is_modal(&lower[predicate_at - 1]) {
        predicate_at - 1
    } else {
        predicate_at
    };
    if subject_end == 0 || predicate_at + 1 >= words.len() {
        return Ok(None);
    }
    let subject = entity(&words[..subject_end]);
    let object = entity(&words[predicate_at + 1..]);
    if subject.identity.is_empty() || object.identity.is_empty() {
        return Ok(None);
    }
    Ok(Some(RelationalClause {
        identity,
        passage: passage.identity.clone(),
        source: passage.source.clone(),
        receiver: passage.receiver,
        source_order: passage.source_order,
        source_order_declared: passage.source_order_declared,
        source_local_step: 0,
        subject,
        relation: verb_lemma(&lower[predicate_at]),
        modality: predicate_at
            .checked_sub(1)
            .and_then(|at| is_modal(&lower[at]).then(|| lower[at].clone())),
        object,
        witnessed_voice: RelationalClauseVoice::Active,
        witnessed_surface: sentence_surface(words),
    }))
}

pub(super) fn question_entity_regions(
    question: &str,
    predicate_lexicon: &LocalSet<String>,
) -> Vec<BTreeSet<String>> {
    let words = word_tokens(question);
    let lower = words
        .iter()
        .map(|word| word.to_lowercase())
        .collect::<Vec<_>>();
    if lower.is_empty() {
        return Vec::new();
    }
    if let Some(split_at) = (1..lower.len().saturating_sub(1)).find(|at| {
        lower[*at] == "and"
            && matches!(
                lower[*at + 1].as_str(),
                "what" | "who" | "which" | "how" | "why"
            )
    }) {
        let mut regions = question_entity_regions(&words[..split_at].join(" "), predicate_lexicon);
        regions.extend(question_entity_regions(
            &words[split_at + 1..].join(" "),
            predicate_lexicon,
        ));
        regions.sort();
        regions.dedup();
        if !regions.is_empty() {
            return regions;
        }
    }
    if let Some(be_at) = lower.iter().position(|word| is_be(word)) {
        if lower[..be_at]
            .iter()
            .any(|word| matches!(word.as_str(), "what" | "who" | "which"))
            && be_at + 1 < words.len()
        {
            let region = entity_identity(&words[be_at + 1..]);
            return (!region.is_empty()).then_some(region).into_iter().collect();
        }
    }
    let auxiliary_at = lower.iter().position(|word| is_auxiliary(word));
    let Some(auxiliary_at) = auxiliary_at else {
        if matches!(lower[0].as_str(), "what" | "who" | "which") {
            let predicate_at = (1..lower.len()).find(|at| {
                let lemma = verb_lemma(&lower[*at]);
                !is_participle(&lower[*at])
                    && (predicate_lexicon.contains(&lemma)
                        || inherited_predicate_lexicon().contains(&lemma))
            });
            if let Some(predicate_at) = predicate_at {
                let object_start = predicate_at + 1;
                if let Some(preposition_at) =
                    (object_start..lower.len()).find(|at| is_relational_preposition(&lower[*at]))
                {
                    let mut regions = Vec::new();
                    let direct = entity_identity(&words[object_start..preposition_at]);
                    if !direct.is_empty() {
                        regions.push(direct);
                    }
                    let relative = entity_identity(&words[preposition_at + 1..]);
                    if !relative.is_empty() {
                        regions.push(relative);
                    }
                    if !regions.is_empty() {
                        regions.sort();
                        regions.dedup();
                        return regions;
                    }
                } else {
                    let region = entity_identity(&words[object_start..]);
                    if !region.is_empty() {
                        return vec![region];
                    }
                }
            }
        }
        let region = entity_identity(&words);
        return (!region.is_empty()).then_some(region).into_iter().collect();
    };
    let is_predicate = |at: usize| {
        let lemma = verb_lemma(&lower[at]);
        predicate_lexicon.contains(&lemma) || inherited_predicate_lexicon().contains(&lemma)
    };
    let predicate_at = (auxiliary_at + 1..lower.len())
        .find(|at| is_predicate(*at) && !is_participle(&lower[*at]))
        .or_else(|| (auxiliary_at + 1..lower.len()).find(|at| is_predicate(*at)));
    let Some(outer_predicate_at) = predicate_at else {
        let region = entity_identity(&words[auxiliary_at + 1..]);
        return (!region.is_empty()).then_some(region).into_iter().collect();
    };
    // In a causative question, the outer relation opens a nested relational body: “How does X
    // make A change B?” asks for A/change/B. Treating X/make/the-complete-remainder as one scalar
    // region would make the routing context an impossible answer obligation.
    let nested_predicate_at = matches!(
        verb_lemma(&lower[outer_predicate_at]).as_str(),
        "allow" | "cause" | "have" | "let" | "make"
    )
    .then(|| {
        (outer_predicate_at + 1..lower.len())
            .find(|at| is_predicate(*at) && !is_participle(&lower[*at]))
    })
    .flatten();
    let (subject_start, predicate_at) = nested_predicate_at
        .map_or((auxiliary_at + 1, outer_predicate_at), |nested| {
            (outer_predicate_at + 1, nested)
        });
    let mut regions = Vec::new();
    let subject = entity_identity(&words[subject_start..predicate_at]);
    if !subject.is_empty() {
        regions.push(subject);
    }
    let object_start = predicate_at + 1;
    if object_start < words.len() {
        let relative_at = (object_start..lower.len()).find(|at| {
            is_participle(&lower[*at])
                && lower
                    .get(*at + 1)
                    .is_some_and(|next| is_relational_preposition(next))
        });
        if let Some(relative_at) = relative_at {
            let direct = entity_identity(&words[object_start..relative_at]);
            if !direct.is_empty() {
                regions.push(direct);
            }
            let relative_start = relative_at + 2;
            if relative_start < words.len() {
                let relative = entity_identity(&words[relative_start..]);
                if !relative.is_empty() {
                    regions.push(relative);
                }
            }
        } else {
            let object = entity_identity(&words[object_start..]);
            if !object.is_empty() {
                regions.push(object);
            }
        }
    }
    regions.sort();
    regions.dedup();
    regions
}

/// Relations explicitly requested by a direct `what/who/which` clause constrain its endpoint
/// testimony. `how` and `why` remain causal-path questions: their intermediate path need not bear
/// the outer framing verb as a copied label.
pub(super) fn question_requested_relations(
    question: &str,
    predicate_lexicon: &LocalSet<String>,
) -> BTreeSet<String> {
    let words = word_tokens(question);
    let lower = words
        .iter()
        .map(|word| word.to_lowercase())
        .collect::<Vec<_>>();
    if lower.is_empty() {
        return BTreeSet::new();
    }
    if let Some(split_at) = (1..lower.len().saturating_sub(1)).find(|at| {
        lower[*at] == "and"
            && matches!(
                lower[*at + 1].as_str(),
                "what" | "who" | "which" | "how" | "why"
            )
    }) {
        let mut relations =
            question_requested_relations(&words[..split_at].join(" "), predicate_lexicon);
        relations.extend(question_requested_relations(
            &words[split_at + 1..].join(" "),
            predicate_lexicon,
        ));
        return relations;
    }
    if !matches!(lower[0].as_str(), "what" | "who" | "which") {
        return BTreeSet::new();
    }
    let start = lower
        .iter()
        .position(|word| is_auxiliary(word))
        .map_or(1, |at| at.saturating_add(1));
    (start..lower.len())
        .find_map(|at| {
            let relation = verb_lemma(&lower[at]);
            (predicate_lexicon.contains(&relation)
                || inherited_predicate_lexicon().contains(&relation))
            .then_some(relation)
        })
        .into_iter()
        .collect()
}

/// Expose the inherited question transducer's plural receiver regions before any source passage
/// has returned.  A world membrane can use these regions as simultaneous leaders; it does not
/// need to collapse the visible question into one opaque search string.
pub fn relational_question_regions(question: &str) -> Vec<BTreeSet<String>> {
    question_entity_regions(question, &inherited_predicate_lexicon())
}

/// Form the simultaneous higher- and lower-grain receiver frontier for open deliberation.
///
/// There is no authored token count here. Every constituent of every nominal region remains an
/// exact local obligation, while the complete regions remain contextual leaders. A one-member
/// face is shared by both charts and is emitted only once.
pub fn relational_deliberation_frontier(question: &str) -> RelationalQuestionFrontier {
    let coarse = relational_question_regions(question);
    let mut leaders = BTreeSet::<BTreeSet<String>>::new();
    let mut required = BTreeSet::<BTreeSet<String>>::new();
    for region in coarse {
        if region.is_empty() {
            continue;
        }
        leaders.insert(region.clone());
        for face in region {
            let local = BTreeSet::from([face]);
            leaders.insert(local.clone());
            if !local.iter().all(|face| is_deliberative_phase_face(face)) {
                required.insert(local);
            }
        }
    }
    RelationalQuestionFrontier {
        leader_regions: leaders.into_iter().collect(),
        required_regions: required.into_iter().collect(),
    }
}

/// Contextual operators remain available to the world membrane as leader phase, but they are not
/// independent entities whose pairwise return can block a question forever.
pub(super) fn is_deliberative_phase_face(face: &str) -> bool {
    matches!(
        face,
        "i" | "me"
            | "my"
            | "mine"
            | "we"
            | "us"
            | "our"
            | "ours"
            | "you"
            | "your"
            | "yours"
            | "he"
            | "him"
            | "his"
            | "she"
            | "her"
            | "hers"
            | "they"
            | "them"
            | "their"
            | "theirs"
            | "most"
            | "important"
    )
}

/// Parse one delivered occurrence completely before any part of it changes standing. The
/// proposal is then committed once in the caller's supplied chronology; malformed syntax cannot
/// leave a passage identity ahead of a partial clause body.
pub(super) fn propose_relational_passage(
    passage: &MorphologicalLanguagePassage,
) -> Result<RelationalPassageProposal, RelationalLanguageError> {
    let mut surfaces = LocalSequence::new();
    let mut clauses = LocalSequence::new();
    let mut parse_fibers = LocalSequence::new();
    let mut predicates = LocalSet::new();
    for (sentence_at, sentence) in sentence_word_tokens(&passage.text).into_iter().enumerate() {
        if sentence.is_empty() {
            continue;
        }
        surfaces.push(sentence.clone());
        let copresent = split_coordinated_clause_words(passage, &sentence)?;
        for (clause_at, clause_words) in copresent.into_iter().enumerate() {
            let identity = format!("{}::relation::{sentence_at}:{clause_at}", passage.identity);
            if let Some(mut clause) = parse_clause(identity.clone(), passage, &clause_words)? {
                clause.source_local_step = u64::try_from(clauses.len())
                    .map_err(|_| RelationalLanguageError::CarrierExtent)?;
                predicates.insert(clause.relation.clone());
                let fiber = parse_fiber(identity, passage, &clause_words, clause.clone())?;
                for alternative in &fiber.alternatives {
                    predicates.insert(alternative.relation.clone());
                }
                clauses.push(clause);
                parse_fibers.push(fiber);
            }
        }
    }
    Ok(RelationalPassageProposal {
        surfaces,
        clauses,
        parse_fibers,
        predicates,
    })
}

pub(super) fn extend_relation_incidence(
    clauses: &[RelationalClause],
    adjacency: &mut LocalSequence<LocalSet<usize>>,
    face_incidence: &mut LocalRelations<String, LocalSet<usize>>,
    entity_incidence: &mut LocalRelations<BTreeSet<String>, LocalSet<usize>>,
    output_incidence: &mut LocalRelations<BTreeSet<String>, LocalSet<usize>>,
    relation_incidence: &mut LocalRelations<String, LocalSet<usize>>,
    passage_incidence: &mut LocalRelations<String, LocalSet<usize>>,
    junction_phases: &mut LocalRelations<(usize, usize), RelationalJunctionPhase>,
    first_new_clause: usize,
) -> LocalSequence<RelationalJunctionCandidate> {
    debug_assert_eq!(adjacency.len(), first_new_clause);
    adjacency.resize_with(clauses.len(), LocalSet::new);
    let mut candidates_out = LocalSequence::new();
    for right in first_new_clause..clauses.len() {
        let clause = &clauses[right];
        let received_faces = [&clause.subject.identity, &clause.object.identity];
        let output_face = clause_output_face(clause);
        // One passage is one co-present higher cell, not a request to materialize the complete
        // graph on its clause faces. Its chronological seam contributes only the immediately
        // preceding clause to structural standing. The complete co-present clause population
        // remains available through `passage_incidence` and is restricted as an observation-local
        // hyperedge by source-occurrence sections and caused relation joins.
        let passage_predecessor = passage_incidence
            .get(&clause.passage)
            .and_then(|carriers| carriers.iter().last().copied());
        let mut candidates = passage_predecessor.into_iter().collect::<LocalSet<_>>();
        for face in received_faces {
            if let Some(carriers) = entity_incidence.get(face) {
                candidates.extend(carriers.iter().copied());
            }
            if let Some(carriers) = output_incidence.get(face) {
                candidates.extend(carriers.iter().copied());
            }
            for constituent in face {
                if let Some(carriers) = relation_incidence.get(constituent) {
                    candidates.extend(carriers.iter().copied());
                }
            }
        }
        if let Some(carriers) = entity_incidence.get(&output_face) {
            candidates.extend(carriers.iter().copied());
        }
        if let Some(carriers) = face_incidence.get(&clause.relation) {
            candidates.extend(carriers.iter().copied());
        }
        for left in candidates {
            if left >= right {
                continue;
            }
            let shared_contact = !clause_shared_entity_faces(&clauses[left], clause).is_empty();
            if passage_predecessor != Some(left) && !shared_contact {
                continue;
            }
            adjacency[left].insert(right);
            adjacency[right].insert(left);
            let phase = relational_junction_phase(&clauses[left], clause);
            junction_phases.insert((left, right), phase.clone());
            candidates_out.push(RelationalJunctionCandidate { left, right, phase });
        }
        for face in received_faces {
            insert_local_incidence(entity_incidence, face.clone(), right);
            for constituent in face {
                insert_local_incidence(face_incidence, constituent.clone(), right);
            }
        }
        insert_local_incidence(output_incidence, output_face, right);
        insert_local_incidence(relation_incidence, clause.relation.clone(), right);
        insert_local_incidence(passage_incidence, clause.passage.clone(), right);
    }
    candidates_out
}

pub(super) fn insert_local_incidence<K: Ord>(
    incidence: &mut LocalRelations<K, LocalSet<usize>>,
    key: K,
    member: usize,
) {
    if let Some(carriers) = incidence.get_mut(&key) {
        carriers.insert(member);
    } else {
        incidence.insert(key, LocalSet::from([member]));
    }
}

pub(super) fn ordered_clause_pair(left: usize, right: usize) -> (usize, usize) {
    if left <= right {
        (left, right)
    } else {
        (right, left)
    }
}

pub(super) fn empty_relational_association() -> Result<ResonanceEcology, RelationalLanguageError> {
    let standing =
        SparseStandingSurface::empty_rank(8).map_err(|_| RelationalLanguageError::CarrierExtent)?;
    Ok(ResonanceEcology::new(LiveCurrentMachine::new(standing)))
}

pub(super) fn relational_junction_candidate_occurrence(
    candidate: &RelationalJunctionCandidate,
    clauses: &[RelationalClause],
    order: u64,
) -> Result<ResonanceOccurrence, RelationalLanguageError> {
    let left = clauses
        .get(candidate.left)
        .ok_or(RelationalLanguageError::CarrierExtent)?;
    let right = clauses
        .get(candidate.right)
        .ok_or(RelationalLanguageError::CarrierExtent)?;
    let mut identity = encode_relational_junction_phase(&candidate.phase)?;
    identity.push(3);
    encode_string(&mut identity, &left.identity)?;
    encode_string(&mut identity, &right.identity)?;
    identity.extend_from_slice(&order.to_le_bytes());
    relational_junction_occurrence_with_identity(&candidate.phase, &identity, order)
}

pub(super) fn relational_junction_occurrence_with_identity(
    phase: &RelationalJunctionPhase,
    identity: &[u8],
    order: u64,
) -> Result<ResonanceOccurrence, RelationalLanguageError> {
    let phase_bytes = encode_relational_junction_phase(phase)?;
    let mut opposed_phase_bytes = phase_bytes.clone();
    opposed_phase_bytes.push(1);
    let mut return_phase_bytes = phase_bytes;
    return_phase_bytes.push(2);
    let opposed = ResonanceGerm::new(
        fiber_from_bytes(RELATIONAL_JUNCTION_SCHEMA, &opposed_phase_bytes),
        RelationAtom::new(Cog::lit(1)).ok_or(RelationalLanguageError::CarrierExtent)?,
    );
    let returned = ResonanceGerm::new(
        fiber_from_bytes(RELATIONAL_JUNCTION_SCHEMA, &return_phase_bytes),
        RelationAtom::new(Cog::lit(2)).ok_or(RelationalLanguageError::CarrierExtent)?,
    );
    let required_return = returned.identity().clone();
    Ok(ResonanceOccurrence::informant(
        fiber_from_bytes(RELATIONAL_JUNCTION_OCCURRENCE_SCHEMA, identity),
        order,
        vec![opposed, returned],
    )?
    .with_required_germ_ports(LocalSet::from([required_return]))?)
}

#[cfg(test)]
pub(super) fn relational_junction_witness_occurrence(
    phase: &RelationalJunctionPhase,
    witness: &str,
    order: u64,
) -> Result<ResonanceOccurrence, RelationalLanguageError> {
    relational_junction_occurrence_with_identity(phase, witness.as_bytes(), order)
}

pub(super) fn clause_site(at: usize) -> Result<ReceiverCurrentSiteId, RelationalLanguageError> {
    Ok(ReceiverCurrentSiteId(
        u64::try_from(at).map_err(|_| RelationalLanguageError::CarrierExtent)?,
    ))
}

pub(super) fn relational_clause_morphology(
    clause: &RelationalClause,
) -> RelationalClauseMorphology {
    RelationalClauseMorphology {
        subject: clause.subject.identity.clone(),
        relation: clause.relation.clone(),
        modality: clause.modality.clone(),
        object: clause.object.identity.clone(),
        voice: clause.witnessed_voice,
    }
}

pub(super) fn encode_relational_junction_phase(
    phase: &RelationalJunctionPhase,
) -> Result<Vec<u8>, RelationalLanguageError> {
    let mut bytes = Vec::new();
    encode_string_set(&mut bytes, &phase.shared_entity_faces)?;
    for endpoint in &phase.endpoints {
        encode_string(&mut bytes, &endpoint.relation)?;
        match &endpoint.modality {
            Some(modality) => {
                bytes.push(1);
                encode_string(&mut bytes, modality)?;
            }
            None => bytes.push(0),
        }
        encode_extent(&mut bytes, endpoint.roles.len())?;
        for role in &endpoint.roles {
            bytes.push(match role {
                RelationalJunctionRole::Subject => 1,
                RelationalJunctionRole::Object => 2,
                RelationalJunctionRole::CausedOutput => 3,
            });
        }
    }
    Ok(bytes)
}

pub(super) fn encode_string_set(
    bytes: &mut Vec<u8>,
    values: &BTreeSet<String>,
) -> Result<(), RelationalLanguageError> {
    encode_extent(bytes, values.len())?;
    for value in values {
        encode_string(bytes, value)?;
    }
    Ok(())
}

pub(super) fn encode_string(
    bytes: &mut Vec<u8>,
    value: &str,
) -> Result<(), RelationalLanguageError> {
    encode_extent(bytes, value.len())?;
    bytes.extend_from_slice(value.as_bytes());
    Ok(())
}

pub(super) fn encode_extent(
    bytes: &mut Vec<u8>,
    extent: usize,
) -> Result<(), RelationalLanguageError> {
    let extent = u64::try_from(extent).map_err(|_| RelationalLanguageError::CarrierExtent)?;
    bytes.extend_from_slice(&extent.to_le_bytes());
    Ok(())
}

pub(super) fn relational_junction_phase(
    left: &RelationalClause,
    right: &RelationalClause,
) -> RelationalJunctionPhase {
    let shared_entity_faces = clause_shared_entity_faces(left, right);
    let mut endpoints = [
        relational_junction_endpoint(left, &shared_entity_faces),
        relational_junction_endpoint(right, &shared_entity_faces),
    ];
    if endpoints[1] < endpoints[0] {
        endpoints.swap(0, 1);
    }
    RelationalJunctionPhase {
        shared_entity_faces,
        endpoints,
    }
}

pub(super) fn relational_junction_endpoint(
    clause: &RelationalClause,
    shared: &BTreeSet<String>,
) -> RelationalJunctionEndpoint {
    let mut roles = BTreeSet::new();
    if !shared.is_empty() && shared.is_subset(&clause.subject.identity) {
        roles.insert(RelationalJunctionRole::Subject);
    }
    if !shared.is_empty() && shared.is_subset(&clause.object.identity) {
        roles.insert(RelationalJunctionRole::Object);
    }
    if shared.contains(&clause.relation) && shared.is_subset(&clause_output_face(clause)) {
        roles.insert(RelationalJunctionRole::CausedOutput);
    }
    RelationalJunctionEndpoint {
        relation: clause.relation.clone(),
        modality: clause.modality.clone(),
        roles,
    }
}

pub(super) fn inherited_channel_conduct(
    left: &RelationalClause,
    right: &RelationalClause,
) -> Option<RelationalChannelConduct> {
    if left.passage == right.passage {
        Some(RelationalChannelConduct::Copresent)
    } else if clauses_have_exact_caused_contact(left, right) {
        Some(RelationalChannelConduct::Caused)
    } else {
        None
    }
}

/// Exact oriented object-to-subject incidence is a declared composable relation, analogous to a
/// typed output entering a typed input. Broader shared vocabulary remains only a Swing candidate.
pub(super) fn clauses_have_exact_caused_contact(
    left: &RelationalClause,
    right: &RelationalClause,
) -> bool {
    (!left.object.identity.is_empty() && left.object.identity == right.subject.identity)
        || (!right.object.identity.is_empty() && right.object.identity == left.subject.identity)
}

pub(super) fn entity(words: &[String]) -> RelationalEntity {
    RelationalEntity {
        surface: words
            .iter()
            .enumerate()
            .map(|(at, word)| {
                let interior_uppercase = word.chars().skip(1).any(char::is_uppercase);
                let numeric_symbol = word.chars().any(|character| character.is_ascii_digit());
                let internal_title = at > 0 && word.chars().next().is_some_and(char::is_uppercase);
                if interior_uppercase || numeric_symbol || internal_title {
                    word.clone()
                } else {
                    word.to_lowercase()
                }
            })
            .collect(),
        identity: entity_identity(words),
    }
}

pub(super) fn entity_identity(words: &[String]) -> BTreeSet<String> {
    words
        .iter()
        .map(|word| word.to_lowercase())
        .filter(|word| !is_entity_operator(word))
        .map(|word| nominal_lemma(&word))
        .filter(|word| !word.is_empty())
        .collect()
}

pub(super) fn entity_is_plural(entity: &RelationalEntity) -> bool {
    // A finite content clause is one proposition at the outer receiver even when its interior
    // subject is plural: "that currents close" therefore *is* verified.
    if entity
        .surface
        .first()
        .is_some_and(|word| matches!(word.as_str(), "that" | "what" | "whether"))
    {
        return false;
    }
    entity
        .surface
        .iter()
        .rev()
        .find(|word| !is_entity_operator(word))
        .is_some_and(|word| {
            matches!(word.as_str(), "we" | "they")
                || (word.ends_with('s')
                    && !word.ends_with("ss")
                    && !matches!(word.as_str(), "this" | "is"))
        })
}

pub(super) fn sentence_word_tokens(text: &str) -> Vec<Vec<String>> {
    let mut sentences = Vec::new();
    let mut current = Vec::new();
    for token in lexical_tokens(text) {
        if token.chars().any(char::is_alphanumeric)
            && !matches!(token.to_lowercase().as_str(), "while" | "whereas")
        {
            current.push(token);
        } else if (matches!(token.as_str(), "." | "!" | "?" | ";" | ":")
            || matches!(token.to_lowercase().as_str(), "while" | "whereas"))
            && !current.is_empty()
        {
            sentences.push(std::mem::take(&mut current));
        }
    }
    if !current.is_empty() {
        sentences.push(current);
    }
    sentences
}

pub(super) fn word_tokens(text: &str) -> Vec<String> {
    lexical_tokens(text)
        .into_iter()
        .filter(|token| token.chars().any(char::is_alphanumeric))
        .collect()
}

pub(super) fn sentence_surface(words: &[String]) -> String {
    let words = capitalize_first(words.to_vec());
    let mut text = words.join(" ");
    if !text.ends_with(['.', '!', '?']) {
        text.push('.');
    }
    text
}

pub(super) fn capitalize_first(mut words: Vec<String>) -> Vec<String> {
    if let Some(first) = words.first_mut() {
        if let Some(character) = first.chars().next() {
            let uppercase = character.to_uppercase().collect::<String>();
            first.replace_range(0..character.len_utf8(), &uppercase);
        }
    }
    words
}

pub(super) fn equal_folded(left: &[String], right: &[String]) -> bool {
    left.iter()
        .zip(right)
        .all(|(left, right)| left.eq_ignore_ascii_case(right))
}

pub(super) fn verb_lemma(word: &str) -> String {
    match word {
        "is" | "are" | "was" | "were" | "been" | "being" => "be".to_owned(),
        "has" | "had" => "have".to_owned(),
        "does" | "did" => "do".to_owned(),
        "uses" => "use".to_owned(),
        "made" => "make".to_owned(),
        "built" => "build".to_owned(),
        "written" | "wrote" => "write".to_owned(),
        _ if word.ends_with("ies") && word.len() > 3 => {
            format!("{}y", &word[..word.len() - 3])
        }
        _ if word.ends_with("ied") && word.len() > 3 => {
            format!("{}y", &word[..word.len() - 3])
        }
        _ if word.ends_with("ed") && word.len() > 3 => {
            let root = &word[..word.len() - 2];
            if root.ends_with('c') || root.ends_with('v') || root.ends_with('s') {
                format!("{root}e")
            } else {
                root.to_owned()
            }
        }
        _ if word.ends_with("es") && word.len() > 3 => {
            let root = &word[..word.len() - 2];
            if root.ends_with(['s', 'x', 'z']) || root.ends_with("ch") || root.ends_with("sh") {
                root.to_owned()
            } else {
                word[..word.len() - 1].to_owned()
            }
        }
        _ if word.ends_with('s') && word.len() > 2 && !word.ends_with("ss") => {
            word[..word.len() - 1].to_owned()
        }
        _ => word.to_owned(),
    }
}

pub(super) fn nominal_lemma(word: &str) -> String {
    match word {
        "returned" => "return".to_owned(),
        "advanced" => "advance".to_owned(),
        "formed" => "form".to_owned(),
        "used" => "use".to_owned(),
        _ if word.ends_with("'s") && word.len() > 2 => word[..word.len() - 2].to_owned(),
        _ if word.ends_with("sis") => word.to_owned(),
        _ if word.ends_with("ies") && word.len() > 3 => {
            format!("{}y", &word[..word.len() - 3])
        }
        _ if word.ends_with('s') && word.len() > 3 && !word.ends_with("ss") => {
            word[..word.len() - 1].to_owned()
        }
        _ => word.to_owned(),
    }
}

pub(super) fn present_relation(relation: &str, plural: bool) -> String {
    if plural {
        return relation.to_owned();
    }
    match relation {
        "be" => "is".to_owned(),
        "have" => "has".to_owned(),
        "do" => "does".to_owned(),
        _ if relation.ends_with('y')
            && relation
                .chars()
                .rev()
                .nth(1)
                .is_some_and(|prior| !matches!(prior, 'a' | 'e' | 'i' | 'o' | 'u')) =>
        {
            format!("{}ies", &relation[..relation.len() - 1])
        }
        _ if relation.ends_with(['s', 'x', 'z'])
            || relation.ends_with("ch")
            || relation.ends_with("sh") =>
        {
            format!("{relation}es")
        }
        _ => format!("{relation}s"),
    }
}

pub(super) fn past_participle(relation: &str) -> String {
    match relation {
        "be" => "been".to_owned(),
        "begin" => "begun".to_owned(),
        "choose" => "chosen".to_owned(),
        "come" => "come".to_owned(),
        "do" => "done".to_owned(),
        "find" => "found".to_owned(),
        "give" => "given".to_owned(),
        "go" => "gone".to_owned(),
        "grow" => "grown".to_owned(),
        "have" => "had".to_owned(),
        "know" => "known".to_owned(),
        "lead" => "led".to_owned(),
        "make" => "made".to_owned(),
        "read" => "read".to_owned(),
        "run" => "run".to_owned(),
        "see" => "seen".to_owned(),
        "show" => "shown".to_owned(),
        "speak" => "spoken".to_owned(),
        "take" => "taken".to_owned(),
        "teach" => "taught".to_owned(),
        "think" => "thought".to_owned(),
        "build" => "built".to_owned(),
        "write" => "written".to_owned(),
        "carry" => "carried".to_owned(),
        "up" => "upped".to_owned(),
        _ if relation.ends_with('e') => format!("{relation}d"),
        _ if relation.ends_with('y') => format!("{}ied", &relation[..relation.len() - 1]),
        _ => format!("{relation}ed"),
    }
}

pub(super) fn is_likely_finite_relation(word: &str) -> bool {
    inherited_predicate_lexicon().contains(&verb_lemma(word))
        || word.ends_with("ates")
        || word.ends_with("ifies")
        || word.ends_with("izes")
}

pub(super) fn is_participle(word: &str) -> bool {
    word.ends_with("ed")
        || word.ends_with("en")
        || matches!(word, "made" | "built" | "written" | "known" | "shown")
}

pub(super) fn is_be(word: &str) -> bool {
    matches!(
        word,
        "is" | "are" | "was" | "were" | "be" | "been" | "being"
    )
}

pub(super) fn is_modal(word: &str) -> bool {
    matches!(
        word,
        "can" | "could" | "may" | "might" | "must" | "shall" | "should" | "will" | "would"
    )
}

pub(super) fn is_auxiliary(word: &str) -> bool {
    is_be(word) || is_modal(word) || matches!(word, "do" | "does" | "did" | "have" | "has" | "had")
}

pub(super) fn is_relational_preposition(word: &str) -> bool {
    matches!(
        word,
        "by" | "from" | "through" | "with" | "into" | "over" | "as" | "to"
    )
}

pub(super) fn is_entity_operator(word: &str) -> bool {
    matches!(
        word,
        "a" | "an"
            | "the"
            | "this"
            | "that"
            | "these"
            | "those"
            | "one"
            | "it"
            | "its"
            | "itself"
            | "themselves"
            | "what"
            | "which"
            | "who"
            | "whom"
            | "whose"
            | "how"
            | "why"
            | "when"
            | "where"
            | "and"
            | "or"
            | "but"
            | "by"
            | "from"
            | "through"
            | "with"
            | "into"
            | "over"
            | "as"
            | "to"
            | "of"
            | "for"
            | "in"
            | "on"
            | "at"
            | "does"
            | "do"
            | "did"
            | "is"
            | "are"
            | "was"
            | "were"
            | "be"
            | "not"
            | "can"
            | "could"
            | "may"
            | "might"
            | "must"
            | "shall"
            | "should"
            | "will"
            | "would"
    )
}

pub(super) fn inherited_predicate_lexicon() -> LocalSet<String> {
    [
        "advance",
        "affect",
        "allow",
        "become",
        "build",
        "carry",
        "cause",
        "change",
        "check",
        "close",
        "condition",
        "construct",
        "define",
        "derive",
        "emit",
        "falsify",
        "form",
        "found",
        "generate",
        "have",
        "invoke",
        "make",
        "mean",
        "open",
        "own",
        "predict",
        "preserve",
        "provide",
        "receive",
        "reconstruct",
        "relate",
        "contradict",
        "connect",
        "remain",
        "require",
        "restrict",
        "retain",
        "return",
        "transform",
        "use",
    ]
    .into_iter()
    .map(str::to_owned)
    .collect()
}

use super::*;

pub(super) fn declaration_proof_face(returned: &LeanKernelReturn) -> LeanDeclarationProofFace {
    LeanDeclarationProofFace {
        proof_sha256: sha256(returned.candidate.proof.as_bytes()),
        source_sha256: returned.source_sha256.clone(),
        motions: LocalSequence::from_slice(&returned.candidate.motions),
        declaration_lineage: LocalSequence::from_iter(
            returned.candidate.declaration_lineage.iter().cloned(),
        ),
    }
}

pub(super) fn proof_family_matches_paths(
    proofs: &LocalSequence<LeanDeclarationProofFace>,
    paths: &LocalSequence<LeanReturnedProofPath>,
) -> bool {
    proofs.len() == paths.len()
        && proofs.iter().zip(paths).all(|(proof, path)| {
            proof.proof_sha256 == path.proof_sha256
                && proof.source_sha256 == path.source_sha256
                && proof.motions == path.motions
                && proof.declaration_lineage == path.declaration_lineage
        })
}

pub(super) fn merge_kernel_admitted_organ(
    family: &mut LeanDeclarationOrgan,
    member: LeanDeclarationOrgan,
) -> Result<(), LeanMathematicsError> {
    if family.source != member.source
        || family.name != member.name
        || family.binders != member.binders
        || family.statement_identifiers != member.statement_identifiers
        || family.result_constructors != member.result_constructors
    {
        return Err(LeanMathematicsError::Parse(
            "kernel-admitted paths did not return one common theorem face".to_owned(),
        ));
    }
    family.tactic_species.extend(member.tactic_species);
    family
        .referenced_declarations
        .extend(member.referenced_declarations);
    Ok(())
}

/// Reify the plural proof family as one theorem declaration. Each independently kernel-admitted
/// path is elaborated as a proof of the common theorem result. Proof irrelevance then glues their
/// co-present sections; candidate chronology is retained for lineage but never used as a score.
pub(super) fn family_composite_declaration(
    problem: &LeanProofProblem,
    returns: &LeanKernelReturnFamily,
) -> Result<String, LeanMathematicsError> {
    let result_at =
        first_top_level_colon(&problem.theorem_header).ok_or(LeanMathematicsError::EmptyProblem)?;
    let result = problem.theorem_header[result_at + 1..].trim();
    if result.is_empty() {
        return Err(LeanMathematicsError::EmptyProblem);
    }
    let mut declaration = format!("{} := by", problem.theorem_header);
    let mut admitted = 0usize;
    for returned in returns.kernel_admitted() {
        declaration.push_str(&format!(
            "\n  have family_path_{admitted} : {result} := {}",
            returned.candidate.proof.replace('\n', "\n  ")
        ));
        admitted = admitted
            .checked_add(1)
            .ok_or(LeanMathematicsError::CarrierExtent)?;
    }
    if admitted == 0 {
        return Err(LeanMathematicsError::NoKernelAdmittedProof);
    }
    declaration.push_str(&format!(
        "\n  have family_fold_0 : {result} := family_path_0"
    ));
    for at in 1..admitted {
        let prior = at - 1;
        declaration.push_str(&format!(
            "\n  have family_glue_{at} : family_path_0 = family_path_{at} := Subsingleton.elim _ _\n  have family_fold_{at} : {result} := Eq.ndrec (motive := fun _ => {result}) family_fold_{prior} family_glue_{at}"
        ));
    }
    declaration.push_str(&format!("\n  exact family_fold_{}", admitted - 1));
    Ok(declaration)
}

pub(super) fn returned_proof_path(returned: &LeanKernelReturn) -> LeanReturnedProofPath {
    let mut declaration_lineage = LocalSequence::new();
    for declaration in &returned.candidate.declaration_lineage {
        declaration_lineage.push(Arc::clone(declaration));
    }
    LeanReturnedProofPath {
        candidate_ordinal: returned.candidate.ordinal,
        proof_sha256: sha256(returned.candidate.proof.as_bytes()),
        source_sha256: returned.source_sha256.to_owned(),
        diagnostic_sha256: returned.diagnostic_sha256.to_owned(),
        motions: LocalSequence::from_slice(&returned.candidate.motions),
        declaration_lineage,
    }
}

pub(super) fn insert_declaration_incidence(
    incidence: &mut LocalRelations<String, LocalSet<String>>,
    identifier: String,
    declaration: String,
) {
    if let Some(declarations) = incidence.get_mut(&identifier) {
        declarations.insert(declaration);
    } else {
        incidence.insert(identifier, LocalSet::from([declaration]));
    }
}

pub(super) fn proof_round(
    ordinal: u64,
    cause: &str,
    returns: &LeanKernelReturnFamily,
) -> Result<LeanProofRoundReceipt, LeanMathematicsError> {
    let kernel_admitted = returns.kernel_admitted_extent();
    Ok(LeanProofRoundReceipt {
        ordinal,
        cause: cause.to_owned(),
        candidate_ordinals: returns
            .members()
            .iter()
            .map(|returned| returned.candidate.ordinal)
            .collect(),
        kernel_admitted: u64::try_from(kernel_admitted)
            .map_err(|_| LeanMathematicsError::CarrierExtent)?,
        obstructed: u64::try_from(returns.members().len().saturating_sub(kernel_admitted))
            .map_err(|_| LeanMathematicsError::CarrierExtent)?,
    })
}

#[derive(Clone, Debug)]
pub(super) struct ParsedDeclaration {
    pub(super) organ: LeanDeclarationOrgan,
    pub(super) proof: String,
}

/// The section variables a declaration actually takes, by Lean's rule: a variable is included when
/// the declaration mentions it, and mentioning one drags in whatever its own type mentions.
///
/// Two conditions the oracle taught this function, each by disagreeing with it:
///
/// - **A mention can be a projection.** `#l.toFinset = l.dedup.length` mentions `l`, and the
///   identifier scan returns the dotted token; taking the head segment as well is what lets the
///   variable be seen at all. Without it `List.card_toFinset` came back with an empty domain where
///   Lean prints one argument.
/// - **A declaration's own binder shadows a section variable of the same name.**
///   `theorem Multiset.dedup_card_eq_card_iff_nodup {m : Multiset α}` re-binds `m` *implicitly*
///   under a `variable (m : Multiset α)`, so `m` is not a positional argument at all; admitting the
///   section's explicit `m` beside it claimed an argument Lean does not take.
fn admitted_context(
    context: &[LeanBinderChart],
    header: &str,
    shadowed: &BTreeSet<String>,
) -> Vec<LeanBinderChart> {
    let mut wanted: BTreeSet<String> = BTreeSet::new();
    for identifier in lean_identifiers(header) {
        if let Some((head, _)) = identifier.split_once('.') {
            wanted.insert(head.to_owned());
        }
        wanted.insert(identifier);
    }
    // Close over the admitted binders' own types until nothing new is dragged in.
    loop {
        let mut grew = false;
        for binder in context {
            if binder.name.is_empty() || !wanted.contains(&binder.name) {
                continue;
            }
            for identifier in lean_identifiers(&binder.type_text) {
                if let Some((head, _)) = identifier.split_once('.') {
                    if wanted.insert(head.to_owned()) {
                        grew = true;
                    }
                }
                if wanted.insert(identifier) {
                    grew = true;
                }
            }
        }
        if !grew {
            break;
        }
    }
    context
        .iter()
        .filter(|binder| {
            !binder.name.is_empty()
                && wanted.contains(&binder.name)
                && !shadowed.contains(&binder.name)
        })
        .cloned()
        .collect()
}

pub(super) fn parse_declarations(
    document: &LeanSourceDocument,
) -> Result<Vec<ParsedDeclaration>, LeanMathematicsError> {
    let lines = document.text.lines().collect::<Vec<_>>();
    let mut context = Vec::<LeanBinderChart>::new();
    let mut declarations = Vec::new();
    let mut cursor = 0usize;
    while cursor < lines.len() {
        let trimmed = lines[cursor].trim();
        if trimmed.starts_with("variable ") {
            merge_binders(&mut context, parse_binder_charts(trimmed));
            cursor += 1;
            continue;
        }
        if !(trimmed.starts_with("theorem ") || trimmed.starts_with("lemma ")) {
            cursor += 1;
            continue;
        }
        let start = cursor;
        cursor += 1;
        while cursor < lines.len() {
            let line = lines[cursor];
            let next = line.trim_start();
            // **A top-level `variable` ends a declaration's chunk.** The scan ran only to the next
            // `theorem`/`lemma`, so every `variable` line appearing after the first declaration was
            // swallowed into the preceding chunk and never reached the branch that merges it — and
            // interleaving `variable` with declarations is mathlib's ordinary style. Measured
            // against Lean itself: `variable [DecidableEq α] (m : Multiset α) (l : List α)` inside
            // `section ToMultiset` contributed nothing, so `List.card_toFinset` came back with an
            // empty parameter domain where the oracle prints one argument.
            if line.len() == next.len()
                && (next.starts_with("theorem ")
                    || next.starts_with("lemma ")
                    || next.starts_with("variable "))
            {
                break;
            }
            cursor += 1;
        }
        let chunk = lines[start..cursor].join("\n");
        let Some(split) = chunk.find(":=") else {
            continue;
        };
        let header = chunk[..split].trim();
        let proof = chunk[split + 2..].trim().to_owned();
        let name = declaration_name(header).ok_or_else(|| {
            LeanMathematicsError::Parse(format!(
                "{}:{} has no declaration identity",
                document.path,
                start + 1
            ))
        })?;
        // **A section variable enters a declaration's domain only if the declaration mentions it.**
        // That is Lean's own rule, and without it every declaration under a `variable` block would
        // claim every variable in scope as a parameter. The mention is closed over the types of the
        // binders already admitted, because `(m : Multiset α)` drags `α` in with it.
        let own = parse_binder_charts(header);
        let shadowed: BTreeSet<String> = own
            .iter()
            .filter(|binder| !binder.name.is_empty())
            .map(|binder| binder.name.clone())
            .collect();
        let mut binders = admitted_context(&context, header, &shadowed);
        merge_binders(&mut binders, own);
        let binder_names = binders
            .iter()
            .map(|binder| binder.name.clone())
            .collect::<BTreeSet<_>>();
        let statement_identifiers = lean_identifiers(header)
            .difference(&binder_names)
            .filter(|identifier| !lean_keyword(identifier) && *identifier != &name)
            .cloned()
            .collect();
        let tactic_species = proof
            .lines()
            .filter_map(tactic_species)
            .collect::<BTreeSet<_>>();
        let result_constructors = result_constructors(header);
        let conclusion_relation = principal_relation(header);
        declarations.push(ParsedDeclaration {
            organ: LeanDeclarationOrgan {
                source: document.path.clone(),
                name,
                binders,
                statement_identifiers,
                tactic_species,
                referenced_declarations: BTreeSet::new(),
                result_constructors,
                conclusion_relation,
            },
            proof,
        });
    }
    Ok(declarations)
}

pub(super) fn declaration_name(header: &str) -> Option<String> {
    let rest = header
        .strip_prefix("theorem ")
        .or_else(|| header.strip_prefix("lemma "))?;
    let name = rest
        .split(|character: char| character.is_whitespace() || matches!(character, '(' | '{' | ':'))
        .next()?;
    (!name.is_empty()).then(|| name.to_owned())
}

pub(super) fn declaration_identity(organ: &LeanDeclarationOrgan) -> String {
    format!("{}#{}", organ.source, organ.name)
}

pub(super) fn parse_binder_charts(text: &str) -> Vec<LeanBinderChart> {
    // Only the declaration prefix can introduce declaration binders. Parenthesized terms after
    // the top-level result colon (for example `(∑ n : Old, demand n)`) are expressions, not
    // binder charts. Treating their locally bound indices as theorem arguments corrupts later
    // application transport.
    let binder_extent = first_top_level_colon(text).unwrap_or(text.len());
    let text = &text[..binder_extent];
    let characters = text.char_indices().collect::<Vec<_>>();
    let mut binders = Vec::new();
    let mut cursor = 0usize;
    while cursor < characters.len() {
        let (byte, character) = characters[cursor];
        let (close, kind) = match character {
            '(' => (')', LeanBinderKind::Explicit),
            '{' => ('}', LeanBinderKind::Implicit),
            '[' => (']', LeanBinderKind::Instance),
            '⦃' => ('⦄', LeanBinderKind::StrictImplicit),
            _ => {
                cursor += 1;
                continue;
            }
        };
        let explicit = kind.is_positional();
        let start = byte + character.len_utf8();
        let mut depth = 1usize;
        let mut end = None;
        cursor += 1;
        while cursor < characters.len() {
            let (at, local) = characters[cursor];
            if local == character {
                depth += 1;
            } else if local == close {
                depth -= 1;
                if depth == 0 {
                    end = Some(at);
                    break;
                }
            }
            cursor += 1;
        }
        let Some(end) = end else {
            break;
        };
        let content = &text[start..end];
        // **The type is kept.** It was bound to `_` here, and it is `H.0362`'s `D`.
        // An instance binder is commonly written with no name at all -- `[Fintype α]` -- in which
        // case the whole content is the type and Lean synthesises the name; it is retained as an
        // anonymous binder rather than dropped, because it still occupies a position in the
        // declaration's domain.
        let (names, type_text) = match content.split_once(':') {
            Some((names, written)) => (
                names,
                written.split_whitespace().collect::<Vec<_>>().join(" "),
            ),
            None => ("", content.split_whitespace().collect::<Vec<_>>().join(" ")),
        };
        if !type_text.is_empty() && names.split_whitespace().next().is_none() {
            binders.push(LeanBinderChart {
                name: String::new(),
                explicit,
                kind,
                type_text: type_text.clone(),
            });
        }
        {
            for name in names.split_whitespace() {
                let name = name.trim_matches(|character: char| !is_identifier_character(character));
                if valid_binder_name(name) {
                    binders.push(LeanBinderChart {
                        name: name.to_owned(),
                        explicit,
                        kind,
                        type_text: type_text.clone(),
                    });
                }
            }
        }
        cursor += 1;
    }
    binders
}

pub(super) fn first_top_level_colon(text: &str) -> Option<usize> {
    let mut round = 0usize;
    let mut curly = 0usize;
    let mut square = 0usize;
    for (byte, character) in text.char_indices() {
        match character {
            '(' => round = round.saturating_add(1),
            ')' => round = round.saturating_sub(1),
            '{' => curly = curly.saturating_add(1),
            '}' => curly = curly.saturating_sub(1),
            '[' => square = square.saturating_add(1),
            ']' => square = square.saturating_sub(1),
            ':' if round == 0 && curly == 0 && square == 0 => return Some(byte),
            _ => {}
        }
    }
    None
}

/// The relation symbols this reader recognises at depth zero in a conclusion.
///
/// The list is **the material's**, not a taxonomy: these are the symbols mathlib's own declarations
/// put in that position, and one that never occurs costs nothing. What the list may not do is decide
/// admissibility — that is [`principal_relation`]'s single-relation condition, and a conclusion the
/// scan cannot resolve returns `None` and is counted rather than defaulted.
const CONCLUSION_RELATIONS: [&str; 12] =
    ["↔", "≠", "≤", "≥", "⊆", "∈", "∣", "∧", "∨", "=", "<", ">"];

/// The **principal relation** of a declaration's conclusion, if the material exposes exactly one.
///
/// Two cuts before the scan, and both are structural rather than authored:
///
/// 1. the conclusion is the text after the first top-level `:`;
/// 2. `→` is right-associative and binds loosest, so the text after the **last** top-level arrow is
///    what the declaration actually concludes — everything before it is a hypothesis.
///
/// Then a conclusion carrying exactly one distinct depth-zero relation returns it. One carrying
/// none, or several, returns `None`: **the reader does not guess a principal connective it cannot
/// see.** That population is large and is meant to be reported, not absorbed — measured over
/// mathlib, fewer than half of all declarations expose exactly one.
pub(super) fn principal_relation(header: &str) -> Option<String> {
    let colon = first_top_level_colon(header)?;
    let conclusion = &header[colon + 1..];
    let conclusion = match last_top_level_arrow(conclusion) {
        Some(at) => &conclusion[at..],
        None => conclusion,
    };
    let mut found: BTreeSet<String> = BTreeSet::new();
    let bytes = conclusion.as_bytes();
    let mut depth = 0i64;
    for (byte, character) in conclusion.char_indices() {
        match character {
            '(' | '{' | '[' | '⟨' => depth += 1,
            ')' | '}' | ']' | '⟩' => depth -= 1,
            _ => {}
        }
        if depth != 0 {
            continue;
        }
        // `:=` is not a relation, and neither is the `=` inside `≠` — which is one character here.
        if character == '='
            && byte > 0
            && matches!(bytes.get(byte - 1), Some(b':' | b'=' | b'<' | b'>' | b'!'))
        {
            continue;
        }
        if character == '=' && matches!(bytes.get(byte + 1), Some(b'=' | b'>')) {
            continue;
        }
        for relation in CONCLUSION_RELATIONS {
            if conclusion[byte..].starts_with(relation) {
                found.insert(relation.to_owned());
                break;
            }
        }
    }
    (found.len() == 1).then(|| found.into_iter().next().expect("exactly one"))
}

/// The byte offset just past the last top-level `→` or `->`.
fn last_top_level_arrow(text: &str) -> Option<usize> {
    let mut depth = 0i64;
    let mut last = None;
    for (byte, character) in text.char_indices() {
        match character {
            '(' | '{' | '[' | '⟨' => depth += 1,
            ')' | '}' | ']' | '⟩' => depth -= 1,
            _ => {}
        }
        if depth != 0 {
            continue;
        }
        if character == '→' {
            last = Some(byte + character.len_utf8());
        } else if character == '-' && text[byte..].starts_with("->") {
            last = Some(byte + 2);
        }
    }
    last
}

pub(super) fn result_constructors(header: &str) -> BTreeSet<LeanResultConstructor> {
    let Some(colon) = first_top_level_colon(header) else {
        return BTreeSet::new();
    };
    let result = &header[colon + 1..];
    let mut round = 0usize;
    let mut curly = 0usize;
    let mut square = 0usize;
    let mut constructors = BTreeSet::new();
    for character in result.chars() {
        match character {
            '(' => round = round.saturating_add(1),
            ')' => round = round.saturating_sub(1),
            '{' => curly = curly.saturating_add(1),
            '}' => curly = curly.saturating_sub(1),
            '[' => square = square.saturating_add(1),
            ']' => square = square.saturating_sub(1),
            '∧' if round == 0 && curly == 0 && square == 0 => {
                constructors.insert(LeanResultConstructor::Conjunction);
            }
            _ => {}
        }
    }
    constructors
}

pub(super) fn merge_binders(target: &mut Vec<LeanBinderChart>, source: Vec<LeanBinderChart>) {
    for binder in source {
        if let Some(existing) = target.iter_mut().find(|prior| prior.name == binder.name) {
            existing.explicit |= binder.explicit;
        } else {
            target.push(binder);
        }
    }
}

/// An application built **in the recruited declaration's own frame**.
///
/// [`declaration_application`] walks the organ's explicit binders, keeps those whose *name* the
/// target also binds, and **silently drops the rest** — so an organ carrying one binder the target
/// does not name is applied with its remaining arguments in the wrong positions, and an organ
/// sharing no name at all is applied bare. It works only where corpus and goal happen to share a
/// `variable` block, and it is a string intersection standing in for a chart transition.
///
/// This walks the same binders and emits `_` where the goal supplies no name, so the arity and the
/// order are the organ's own and Lean infers what the goal cannot supply.
pub(super) fn declaration_application_in_frame(
    organ: &LeanDeclarationOrgan,
    target_names: &BTreeSet<String>,
) -> String {
    let arguments = organ
        .binders
        .iter()
        .filter(|binder| binder.kind.is_positional())
        .map(|binder| {
            if !binder.name.is_empty() && target_names.contains(&binder.name) {
                binder.name.clone()
            } else {
                "_".to_owned()
            }
        })
        .collect::<Vec<_>>();
    if arguments.is_empty() {
        return organ.name.clone();
    }
    format!("{} {}", organ.name, arguments.join(" "))
}

pub(super) fn declaration_application(
    organ: &LeanDeclarationOrgan,
    target_names: &BTreeSet<String>,
) -> String {
    let arguments = organ
        .binders
        .iter()
        .filter(|binder| binder.explicit && target_names.contains(&binder.name))
        .map(|binder| binder.name.as_str())
        .collect::<Vec<_>>();
    if arguments.is_empty() {
        organ.name.clone()
    } else {
        format!("{} {}", organ.name, arguments.join(" "))
    }
}

/// The in-frame application for the contrapose family: positional in the organ's own domain, with
/// the contraposed hypothesis put in the **first position the goal cannot supply**.
///
/// The untyped twin replaces a single unmatched binder and drops every other unmatched one, so the
/// application is short and misaligned. This one is the reason the recognition arm exists: with `rw`
/// gated and the other two applications built in frame, **every surviving structural refusal came
/// from this family** — ten of them, each an `Application type mismatch` on an organ whose domain is
/// ten and which was being handed five arguments. The component read wrong was not `(D, v)`; it was
/// a third emission site that still built in the goal's frame.
pub(super) fn declaration_application_in_frame_with_substitute(
    organ: &LeanDeclarationOrgan,
    target_names: &BTreeSet<String>,
    substitute: &str,
) -> String {
    let mut used_substitute = false;
    let arguments = organ
        .binders
        .iter()
        .filter(|binder| binder.kind.is_positional())
        .map(|binder| {
            if !binder.name.is_empty() && target_names.contains(&binder.name) {
                return binder.name.clone();
            }
            if !used_substitute {
                used_substitute = true;
                return substitute.to_owned();
            }
            "_".to_owned()
        })
        .collect::<Vec<_>>();
    if arguments.is_empty() {
        return organ.name.clone();
    }
    format!("{} {}", organ.name, arguments.join(" "))
}

pub(super) fn declaration_application_with_substitute(
    organ: &LeanDeclarationOrgan,
    target_names: &BTreeSet<String>,
    substitute: &str,
) -> String {
    let unmatched = organ
        .binders
        .iter()
        .filter(|binder| binder.explicit && !target_names.contains(&binder.name))
        .count();
    let arguments = organ
        .binders
        .iter()
        .filter(|binder| binder.explicit)
        .filter_map(|binder| {
            if target_names.contains(&binder.name) {
                Some(binder.name.as_str())
            } else if unmatched == 1 {
                Some(substitute)
            } else {
                None
            }
        })
        .collect::<Vec<_>>();
    if arguments.is_empty() {
        organ.name.clone()
    } else {
        format!("{} {}", organ.name, arguments.join(" "))
    }
}

pub(super) fn push_candidate(
    candidates: &mut Vec<LeanProofCandidate>,
    proof: String,
    motions: Vec<LeanProofMotion>,
    declaration_lineage: LocalSet<Arc<str>>,
) -> Result<(), LeanMathematicsError> {
    if candidates.iter().any(|candidate| candidate.proof == proof) {
        return Ok(());
    }
    let ordinal =
        u64::try_from(candidates.len()).map_err(|_| LeanMathematicsError::CarrierExtent)?;
    candidates.push(LeanProofCandidate {
        ordinal,
        proof,
        motions,
        declaration_lineage,
    });
    Ok(())
}

pub(super) fn tactic_species(line: &str) -> Option<String> {
    let line = line.trim().trim_start_matches('·').trim();
    let first = line
        .split(|character: char| character.is_whitespace() || character == '[')
        .find(|word| !word.is_empty())?;
    const TACTICS: &[&str] = &[
        "aesop",
        "apply",
        "assumption",
        "calc",
        "constructor",
        "exact",
        "field_simp",
        "have",
        "linarith",
        "nlinarith",
        "omega",
        "refine",
        "rintro",
        "ring",
        "rw",
        "simpa",
        "simp",
    ];
    TACTICS.contains(&first).then(|| first.to_owned())
}

pub(super) fn lean_identifiers(text: &str) -> BTreeSet<String> {
    let mut identifiers = BTreeSet::new();
    let mut current = String::new();
    for character in text.chars() {
        if is_identifier_character(character) {
            current.push(character);
        } else if !current.is_empty() {
            if valid_identifier(&current) {
                identifiers.insert(std::mem::take(&mut current));
            } else {
                current.clear();
            }
        }
    }
    if valid_identifier(&current) {
        identifiers.insert(current);
    }
    identifiers
}

pub(super) fn is_identifier_character(character: char) -> bool {
    character.is_alphanumeric()
        || matches!(character, '_' | '\'' | '.' | '₀'..='₉' | 'α'..='ω' | 'Α'..='Ω')
}

pub(super) fn valid_identifier(identifier: &str) -> bool {
    !identifier.is_empty()
        && identifier
            .chars()
            .any(|character| character.is_alphabetic() || character == '_')
}

pub(super) fn valid_binder_name(identifier: &str) -> bool {
    valid_identifier(identifier)
        && !matches!(identifier, "fun" | "forall" | "Prop" | "Type" | "Type*")
}

pub(super) fn lean_keyword(identifier: &str) -> bool {
    matches!(
        identifier,
        "theorem"
            | "lemma"
            | "by"
            | "if"
            | "then"
            | "else"
            | "let"
            | "in"
            | "forall"
            | "Prop"
            | "Type"
            | "Type*"
            | "Nat"
            | "Real"
    )
}

pub(super) fn safe_identity(identity: &str) -> String {
    identity
        .chars()
        .map(|character| {
            if character.is_ascii_alphanumeric() || character == '-' {
                character
            } else {
                '_'
            }
        })
        .collect()
}

pub(super) fn sha256(bytes: &[u8]) -> String {
    let mut digest = Sha256::new();
    digest.update(bytes);
    let digest = digest.finalize();
    let alphabet = b"0123456789abcdef";
    let mut face = String::with_capacity(digest.len() * 2);
    for byte in digest {
        face.push(char::from(alphabet[usize::from(byte >> 4)]));
        face.push(char::from(alphabet[usize::from(byte & 0x0f)]));
    }
    face
}

pub(super) fn io_error(error: std::io::Error) -> LeanMathematicsError {
    LeanMathematicsError::Io(error.to_string())
}

pub fn collect_lean_documents(
    root: &Path,
) -> Result<Vec<LeanSourceDocument>, LeanMathematicsError> {
    fn visit(
        root: &Path,
        path: &Path,
        documents: &mut Vec<LeanSourceDocument>,
    ) -> Result<(), LeanMathematicsError> {
        let mut entries = fs::read_dir(path)
            .map_err(io_error)?
            .collect::<Result<Vec<_>, _>>()
            .map_err(io_error)?;
        entries.sort_by_key(|entry| entry.path());
        for entry in entries {
            let path = entry.path();
            if path.is_dir() {
                if path.file_name().is_some_and(|name| {
                    matches!(
                        name.to_string_lossy().as_ref(),
                        ".git" | ".claude" | ".lake" | "target" | "runs"
                    )
                }) {
                    continue;
                }
                visit(root, &path, documents)?;
            } else if path
                .extension()
                .is_some_and(|extension| extension == "lean")
            {
                let relative = path.strip_prefix(root).unwrap_or(path.as_path());
                let text = fs::read_to_string(&path).map_err(io_error)?;
                documents.push(LeanSourceDocument::new(relative.to_string_lossy(), text));
            }
        }
        Ok(())
    }

    let mut documents = Vec::new();
    visit(root, root, &mut documents)?;
    Ok(documents)
}

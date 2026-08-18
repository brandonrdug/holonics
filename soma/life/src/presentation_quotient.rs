//! **The presentation's division: the answer is the quotient and the remainder is exhibited.**
//!
//! An emission conducts a plurality and utters one surface. `agentic_language` already names that
//! correctly — *"This is an explicit presentation quotient. It does not delete alternative
//! currents"* — and retains the alternatives beside the answer. But the alternatives carried no
//! distinguishing word, no witness receiver, and no block relation to what was uttered, so the
//! remainder was **kept without the division being taken**, and a remainder without a division is a
//! second undivided pile.
//!
//! This module takes it. The emitted population is read as prefixes over the emitted alphabet, the
//! declared receiver family is four **codec faces of the material the emission itself produced**,
//! and `receiver_exact_compression::compress` returns the causal-state construction over them. Each
//! retained alternative then comes back either as *indistinguishable from the answer under this
//! family* or as *separated, by this word, seen by this receiver*.
//!
//! **Nothing here ranks, scores, or crowns.** Which candidate is uttered is the caller's
//! declaration; this module says what the utterance cost by exhibiting the population it stood in
//! for.
//!
//! **On the receiver family being authored.** `CLAUDE.md`'s rule is that a returned partition may
//! not be the preimage of a field the driver authored, and the check is: *which declared input, if
//! varied across two members of one returned block, would move them apart?* Every receiver here is
//! a face of the emission's own return — the terminal token, the matched horizon that token was
//! exposed at, the sources that attested it, and whether the prefix is a contiguous window of some
//! inherited passage. None is a label the caller attached to a candidate, and varying the material
//! moves all four.

use std::collections::{BTreeMap, BTreeSet};

use holonic_engine::receiver_exact_compression::{
    compress, InputId, ItemId, Observation, ObservedSystem, ReceiverId,
};
use sha2::{Digest, Sha256};

/// One candidate the emission conducted, as the emission returned it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PresentedCandidate {
    pub identity: String,
    pub tokens: Vec<String>,
    /// The matched horizon each token was exposed at, positionally. May be shorter than `tokens`
    /// when an emission does not carry one; the missing positions read as absent rather than zero.
    pub matched_horizons: Vec<u32>,
    /// The sources that attested each token, positionally.
    pub sources: Vec<BTreeSet<String>>,
}

impl PresentedCandidate {
    pub fn new(identity: impl Into<String>, tokens: Vec<String>) -> Self {
        Self {
            identity: identity.into(),
            tokens,
            matched_horizons: Vec::new(),
            sources: Vec::new(),
        }
    }
}

/// The material the emission drew on, for the one receiver that needs it.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct PresentationMaterial {
    /// Each inherited passage as its own token sequence.
    pub inherited_surfaces: Vec<Vec<String>>,
}

impl PresentationMaterial {
    /// **The window test.** A token sequence is a contiguous span of the material exactly when some
    /// inherited surface contains it as a window. Its complement is what an emission composed.
    ///
    /// Scope, and it travels with every figure read off this: the test runs against the surfaces
    /// supplied here. It certifies *not a span of this material*. It does not certify *absent from
    /// a corpus that was not supplied*.
    /// **Can this material answer the span question at all?** An empty surface population cannot:
    /// it returns `false` for everything, which reads as *composed* and is a statement about the
    /// receiver rather than about the candidate.
    pub fn can_answer(&self) -> bool {
        !self.inherited_surfaces.is_empty()
    }

    pub fn is_contiguous_span(&self, tokens: &[String]) -> bool {
        if tokens.is_empty() {
            return true;
        }
        self.inherited_surfaces.iter().any(|surface| {
            surface.len() >= tokens.len()
                && surface.windows(tokens.len()).any(|window| window == tokens)
        })
    }
}

/// **The same window test, precomputed up to a declared length.**
///
/// [`PresentationMaterial::is_contiguous_span`] rescans every surface for every query, which is the
/// reference reading and is `O(material)` per call. This is the same predicate as a set of windows,
/// built once. It is not an approximation and it is held to the reference by
/// `the_span_index_agrees_with_the_reference_scan`.
///
/// `is_contiguous_span` returns `None` above the declared length rather than a wrong answer, so a
/// caller that outruns the index must fall back to the reference rather than receive a silent miss.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SpanIndex {
    windows: BTreeSet<Vec<String>>,
    longest: usize,
}

impl SpanIndex {
    pub fn is_contiguous_span(&self, tokens: &[String]) -> Option<bool> {
        if tokens.is_empty() {
            return Some(true);
        }
        if tokens.len() > self.longest {
            return None;
        }
        Some(self.windows.contains(tokens))
    }

    pub const fn longest(&self) -> usize {
        self.longest
    }

    pub fn population(&self) -> usize {
        self.windows.len()
    }
}

impl PresentationMaterial {
    /// Every window of the material up to `longest`, as a set.
    pub fn span_index(&self, longest: usize) -> SpanIndex {
        let mut windows = BTreeSet::new();
        for surface in &self.inherited_surfaces {
            for extent in 1..=longest {
                if surface.len() < extent {
                    break;
                }
                for window in surface.windows(extent) {
                    windows.insert(window.to_vec());
                }
            }
        }
        SpanIndex { windows, longest }
    }
}

/// One retained alternative, related to the uttered answer by the word that separates them.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SeparatedAlternative {
    pub identity: String,
    /// The shortest word after which a declared receiver sees a difference. Empty means a receiver
    /// already separated them with no history at all — the one-shot reading was enough.
    pub distinguishing_word: Vec<String>,
    /// Which receiver saw it, and what the two returned.
    pub witness: Option<(PresentationReceiver, u64, u64)>,
    /// Separated because one continues where the other stops. A terminus is a distinction.
    pub separated_by_terminus: bool,
}

/// The declared receiver family: four codec faces of the emission's own return.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum PresentationReceiver {
    /// The identity of the prefix's last emitted token.
    TerminalToken,
    /// The matched horizon that token was exposed at.
    TerminalHorizon,
    /// The set of sources that attested it.
    TerminalSources,
    /// Whether the prefix is a contiguous window of some inherited surface.
    InheritedSpan,
}

impl PresentationReceiver {
    pub const ALL: [Self; 4] = [
        Self::TerminalToken,
        Self::TerminalHorizon,
        Self::TerminalSources,
        Self::InheritedSpan,
    ];

    /// **The family with the identity face withheld.**
    ///
    /// `TerminalToken` returns the candidate's own last token, so it separates every distinct
    /// candidate by construction and any family containing it has the identity map as its quotient.
    /// It is a lawful face — a receiver may genuinely read the token — but a division taken under it
    /// answers *how many distinct candidates are there*, which the caller already knew. These three
    /// are the faces that can actually collapse.
    pub const COLLAPSING: [Self; 3] = [
        Self::TerminalHorizon,
        Self::TerminalSources,
        Self::InheritedSpan,
    ];
}

/// **The division: one uttered answer, and a typed remainder.**
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PresentationDivision {
    pub answer: String,
    /// The rendered token sequence of the answer.
    pub answer_tokens: Vec<String>,
    /// `false` when the answer is not a contiguous window of any inherited surface: the emission
    /// composed rather than copied. Carries the scope stated on [`PresentationMaterial`].
    pub answer_is_inherited_span: bool,
    pub one_shot_blocks: usize,
    pub conduct_blocks: usize,
    pub rounds: usize,
    /// Alternatives in the answer's own conduct block: no word in this family separates them from
    /// what was uttered. **They are within tolerance for this receiver family**, which is the
    /// collapsed-pair relation and not a numerical threshold.
    pub indistinguishable: Vec<String>,
    /// Alternatives a word does separate, each carrying the word.
    pub separated: Vec<SeparatedAlternative>,
    /// Every pair the one-shot reading merged and conduct separated, over the whole prefix
    /// population — the compression's own exact loss.
    pub collapsed_population: usize,
    /// How far back the reading had to look. `None` is a genuine zero.
    pub memory_order: Option<usize>,
    /// Candidates whose complete token sequence is not a window of any inherited surface.
    pub composed_candidates: Vec<String>,
    pub inherited_candidates: Vec<String>,
}

#[derive(Debug, PartialEq, Eq)]
pub enum PresentationError {
    EmptyPopulation,
    AnswerNotPresented(String),
    /// A division under no receivers is not a division. Refused rather than defaulted, because a
    /// defaulted family is a family the caller did not declare.
    EmptyReceiverFamily,
    CarrierExtent,
}

/// The prefix system the compression runs on.
///
/// **`family` is declared, not assumed.** It was `PresentationReceiver::ALL` until 2026-08-18, and
/// on real material that made the division vacuous: `TerminalToken` is the item's own identity, so
/// a family containing it separates every candidate by construction and the quotient is the
/// identity map. Measured on 501 conducted candidates — one-shot 443 blocks, conduct 429, a
/// compression of 501 into 429. **A receiver family carrying an identity face cannot collapse
/// anything**, which is `CLAUDE.md`'s convicted shape — a check whose material cannot vary the
/// property under test — wearing a green, plural, rigorous-looking result.
struct PrefixSystem {
    prefixes: Vec<Vec<String>>,
    index: BTreeMap<Vec<String>, usize>,
    alphabet: Vec<String>,
    family: Vec<PresentationReceiver>,
    horizon_at: BTreeMap<Vec<String>, u32>,
    sources_at: BTreeMap<Vec<String>, BTreeSet<String>>,
    spans: BTreeMap<Vec<String>, bool>,
}

fn digest(bytes: &[u8]) -> u64 {
    let carried = Sha256::digest(bytes);
    let mut word = [0u8; 8];
    word.copy_from_slice(&carried[..8]);
    u64::from_le_bytes(word)
}

impl ObservedSystem for PrefixSystem {
    fn items(&self) -> Vec<ItemId> {
        (0..self.prefixes.len())
            .map(|index| ItemId(index as u64))
            .collect()
    }

    fn receivers(&self) -> Vec<ReceiverId> {
        (0..self.family.len())
            .map(|index| ReceiverId(index as u64))
            .collect()
    }

    fn inputs(&self) -> Vec<InputId> {
        (0..self.alphabet.len())
            .map(|index| InputId(index as u64))
            .collect()
    }

    fn observation(&self, item: ItemId, receiver: ReceiverId) -> Observation {
        let Some(prefix) = self.prefixes.get(item.0 as usize) else {
            return Observation(0);
        };
        let Some(face) = self.family.get(receiver.0 as usize).copied() else {
            return Observation(0);
        };
        Observation(self.face(prefix, face))
    }

    fn successor(&self, item: ItemId, input: InputId) -> Option<ItemId> {
        let prefix = self.prefixes.get(item.0 as usize)?;
        let token = self.alphabet.get(input.0 as usize)?;
        let mut extended = prefix.clone();
        extended.push(token.clone());
        self.index
            .get(&extended)
            .map(|index| ItemId(*index as u64))
    }
}

impl PrefixSystem {
    fn face(&self, prefix: &[String], receiver: PresentationReceiver) -> u64 {
        let owned = prefix.to_vec();
        match receiver {
            PresentationReceiver::TerminalToken => match prefix.last() {
                None => 0,
                Some(token) => digest(token.as_bytes()),
            },
            PresentationReceiver::TerminalHorizon => self
                .horizon_at
                .get(&owned)
                .map_or(0, |horizon| u64::from(*horizon).wrapping_add(1)),
            PresentationReceiver::TerminalSources => match self.sources_at.get(&owned) {
                None => 0,
                Some(sources) => digest(
                    sources
                        .iter()
                        .map(String::as_str)
                        .collect::<Vec<_>>()
                        .join("\u{1}")
                        .as_bytes(),
                ),
            },
            PresentationReceiver::InheritedSpan => {
                u64::from(self.spans.get(&owned).copied().unwrap_or(true))
            }
        }
    }
}

/// Build the prefix system every division in this module runs on.
///
/// Shared by [`divide`] and [`divide_junction`] so the two readings cannot drift: a junction
/// divided one way and audited another would be two partitions of one population.
fn prefix_system(
    candidates: &[PresentedCandidate],
    material: &PresentationMaterial,
    family: &[PresentationReceiver],
) -> Result<PrefixSystem, PresentationError> {
    if family.is_empty() {
        return Err(PresentationError::EmptyReceiverFamily);
    }
    let mut prefixes: BTreeSet<Vec<String>> = BTreeSet::new();
    let mut alphabet: BTreeSet<String> = BTreeSet::new();
    let mut horizon_at: BTreeMap<Vec<String>, u32> = BTreeMap::new();
    let mut sources_at: BTreeMap<Vec<String>, BTreeSet<String>> = BTreeMap::new();
    prefixes.insert(Vec::new());
    for candidate in candidates {
        for (position, token) in candidate.tokens.iter().enumerate() {
            alphabet.insert(token.clone());
            let prefix: Vec<String> = candidate.tokens[..=position].to_vec();
            prefixes.insert(prefix.clone());
            // **Two candidates may share a prefix and have reached it differently.** First-wins
            // would make the face depend on iteration order, which is a partition authored by the
            // loop rather than read off the material. The declared readings: the horizon is the
            // GREATEST any candidate reached that prefix at, and the sources are the UNION —
            // plural lineage retained, exactly as the emission carries it.
            if let Some(horizon) = candidate.matched_horizons.get(position) {
                let slot = horizon_at.entry(prefix.clone()).or_insert(*horizon);
                *slot = (*slot).max(*horizon);
            }
            if let Some(sources) = candidate.sources.get(position) {
                sources_at
                    .entry(prefix)
                    .or_default()
                    .extend(sources.iter().cloned());
            }
        }
    }
    let prefixes: Vec<Vec<String>> = prefixes.into_iter().collect();
    let index: BTreeMap<Vec<String>, usize> = prefixes
        .iter()
        .enumerate()
        .map(|(position, prefix)| (prefix.clone(), position))
        .collect();
    let alphabet: Vec<String> = alphabet.into_iter().collect();
    let spans: BTreeMap<Vec<String>, bool> = prefixes
        .iter()
        .map(|prefix| (prefix.clone(), material.is_contiguous_span(prefix)))
        .collect();

    Ok(PrefixSystem {
        prefixes,
        index,
        alphabet,
        family: family.to_vec(),
        horizon_at,
        sources_at,
        spans,
    })
}

/// **Take the presentation's division against a caller-declared utterance.**
///
/// `answer` names which candidate was uttered; every other candidate is the remainder. The answer
/// is a declaration by the caller, not a ranking performed here.
///
/// **This is an AUDIT, not the production path.** It answers *what did that utterance cost*, which
/// is a real question and the one this module was built for — but it presupposes an utterance
/// somebody else chose. [`divide_junction`] is the production path: it takes no answer, because the
/// answer is the block.
pub fn divide(
    candidates: &[PresentedCandidate],
    answer: &str,
    material: &PresentationMaterial,
) -> Result<PresentationDivision, PresentationError> {
    if candidates.is_empty() {
        return Err(PresentationError::EmptyPopulation);
    }
    let uttered = candidates
        .iter()
        .find(|candidate| candidate.identity == answer)
        .ok_or_else(|| PresentationError::AnswerNotPresented(answer.to_owned()))?;
    let system = prefix_system(candidates, material, &PresentationReceiver::ALL)?;
    let compression = compress(&system);

    let item_of = |tokens: &[String]| -> Option<ItemId> {
        system
            .index
            .get(&tokens.to_vec())
            .map(|position| ItemId(*position as u64))
    };
    let word_of = |word: &[InputId]| -> Vec<String> {
        word.iter()
            .filter_map(|input| system.alphabet.get(input.0 as usize).cloned())
            .collect()
    };
    let receiver_of = |receiver: ReceiverId| -> PresentationReceiver {
        PresentationReceiver::ALL
            .get(receiver.0 as usize)
            .copied()
            .unwrap_or(PresentationReceiver::TerminalToken)
    };

    let answer_item = item_of(&uttered.tokens).ok_or(PresentationError::CarrierExtent)?;
    let answer_block = compression.conduct.block_of(answer_item);

    let mut indistinguishable = Vec::new();
    let mut separated = Vec::new();
    for candidate in candidates {
        if candidate.identity == uttered.identity {
            continue;
        }
        let Some(item) = item_of(&candidate.tokens) else {
            continue;
        };
        if compression.conduct.block_of(item) == answer_block {
            indistinguishable.push(candidate.identity.clone());
            continue;
        }
        let pair = compression.collapsed.iter().find(|collapsed| {
            (collapsed.left == answer_item && collapsed.right == item)
                || (collapsed.left == item && collapsed.right == answer_item)
        });
        let (distinguishing_word, witness, separated_by_terminus) = match pair {
            Some(collapsed) => (
                word_of(&collapsed.distinguishing_word),
                collapsed.witness.map(|(receiver, left, right)| {
                    (receiver_of(receiver), left.0, right.0)
                }),
                collapsed.separated_by_terminus,
            ),
            // Different conduct blocks with no collapsed pair means the one-shot reading already
            // separated them: some receiver differs on the empty word.
            None => {
                let witness = PresentationReceiver::ALL.iter().find_map(|face| {
                    let left = system.face(&uttered.tokens, *face);
                    let right = system.face(&candidate.tokens, *face);
                    (left != right).then_some((*face, left, right))
                });
                (Vec::new(), witness, false)
            }
        };
        separated.push(SeparatedAlternative {
            identity: candidate.identity.clone(),
            distinguishing_word,
            witness,
            separated_by_terminus,
        });
    }

    let mut composed_candidates = Vec::new();
    let mut inherited_candidates = Vec::new();
    for candidate in candidates {
        if material.is_contiguous_span(&candidate.tokens) {
            inherited_candidates.push(candidate.identity.clone());
        } else {
            composed_candidates.push(candidate.identity.clone());
        }
    }

    Ok(PresentationDivision {
        answer: uttered.identity.clone(),
        answer_tokens: uttered.tokens.clone(),
        answer_is_inherited_span: material.is_contiguous_span(&uttered.tokens),
        one_shot_blocks: compression.one_shot.len(),
        conduct_blocks: compression.conduct.len(),
        rounds: compression.rounds,
        indistinguishable,
        separated,
        collapsed_population: compression.collapsed.len(),
        memory_order: compression.memory_order(),
        composed_candidates,
        inherited_candidates,
    })
}

/// **★ ONE RESPONSE — a block of the junction's own quotient, never a pick from it.**
///
/// Every candidate in `members` is indistinguishable from every other under the declared receiver
/// family: no word in the family separates them. That is *tolerance* in this corpus's exact sense —
/// the collapsed-pair relation, not a numerical threshold — so the block **is** the response and
/// naming one member as the answer would be reintroducing the governor.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ResponseBlock {
    /// Every candidate identity the block holds, canonically ordered.
    pub members: Vec<String>,
    /// The block's rendered surfaces. Two members with the same surface are one surface here.
    pub surfaces: Vec<String>,
    /// `Some(true)` when every member's token sequence is a contiguous window of some inherited
    /// surface — the block copied; `Some(false)` when at least one member composed.
    ///
    /// **`None` when the material cannot answer.** An empty [`PresentationMaterial`] makes
    /// `is_contiguous_span` return `false` for everything, so a resumed process with no corpus
    /// reported every block as *composed* — which is a fact about the receiver, not about the
    /// block. Measured 2026-08-18 across a process seam: identical candidates read *wholly
    /// inherited* on the near side and *composed* on the far side. That is the absolute-frame
    /// defect on this module's own return, and `None` is the repair: a blind receiver says nothing
    /// rather than saying no.
    pub wholly_inherited: Option<bool>,
}

/// **The question the machine asks when its own quotient is plural.**
///
/// It is not composed and it is not a template: it is the **shortest word that separates two
/// blocks** — the exact input after which some declared receiver sees the two apart. Asking it is
/// the cheapest thing that would collapse the fiber to one block, which is what a clarifying
/// question *is*.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SeparatingQuestion {
    pub left_block: usize,
    pub right_block: usize,
    /// The word itself, in the emitted alphabet. Empty means the one-shot reading already separated
    /// them, so no continuation is needed — a declared face already tells them apart.
    pub word: Vec<String>,
    /// The receiver that sees the difference, and what the two sides returned to it.
    pub witness: Option<(PresentationReceiver, u64, u64)>,
    pub separated_by_terminus: bool,
}

/// **★ THE JUNCTION'S DIVISION — the production reading, with no answer declared.**
///
/// The whole conducted population enters; the quotient's blocks come back. **Nothing is chosen,
/// ranked, capped, or crowned**, and the count of blocks is a property of the material against the
/// declared receiver family rather than an aperture.
///
/// Read it as the three-part return this corpus already specifies for an emission:
///
/// - **the block** — [`Self::blocks`], each one a response the family cannot see inside;
/// - **the remainder** — [`Self::collapsed_population`] and the words in [`Self::questions`], which
///   is what the division cost, exhibited rather than counted;
/// - **the load** — [`Self::one_shot_blocks`] against [`Self::conduct_blocks`], the spread before
///   and after successor conduct refined it.
///
/// **A plural return is not a failure.** One block is a determinate response; many blocks means the
/// prompt did not determine the continuation for this receiver family, and [`Self::questions`]
/// carries what would. That is where a clarifying question comes from in this machine — it falls
/// out of the quotient being plural and is never bolted on.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct JunctionDivision {
    /// The receiver family this division was taken under. **A block count without its family is a
    /// receiver coordinate presented as a property of the material.**
    pub family: Vec<PresentationReceiver>,
    pub candidate_population: usize,
    pub one_shot_blocks: usize,
    pub conduct_blocks: usize,
    pub rounds: usize,
    /// The response blocks, canonically ordered. **This is the return.**
    pub blocks: Vec<ResponseBlock>,
    /// What the machine would ask to collapse the fiber, one per separated block pair that the
    /// compression exhibited a word for.
    pub questions: Vec<SeparatingQuestion>,
    /// Every pair the one-shot reading merged and successor conduct separated — the compression's
    /// own exact loss over the whole prefix population.
    pub collapsed_population: usize,
    /// How far back the reading had to look. `None` is a genuine zero, not a missing measurement.
    pub memory_order: Option<usize>,
}

impl JunctionDivision {
    /// **Did the junction determine a response?** True when the quotient has exactly one block.
    ///
    /// This is a reading of the return, not a gate on it: a plural division is returned whole
    /// either way.
    pub fn is_determinate(&self) -> bool {
        self.conduct_blocks == 1
    }

    /// How much the division compressed: candidates in, blocks out. Returned as the **pair**,
    /// undivided, because a ratio reported as one number has crossed a horizon it may not cross.
    pub const fn compression(&self) -> (usize, usize) {
        (self.candidate_population, self.conduct_blocks)
    }
}

/// **Divide the junction under a DECLARED receiver family.** No answer is passed, because the
/// answer is the block.
///
/// **The family must be declared and it decides everything.** Handing this
/// [`PresentationReceiver::ALL`] includes `TerminalToken`, which is the candidate's own identity,
/// so every candidate lands in its own block and the division returns the population it was given.
/// [`PresentationReceiver::COLLAPSING`] is the family with that identity face withheld, and the
/// difference between the two block counts is exactly what the identity face was carrying.
pub fn divide_junction(
    candidates: &[PresentedCandidate],
    material: &PresentationMaterial,
    family: &[PresentationReceiver],
) -> Result<JunctionDivision, PresentationError> {
    if candidates.is_empty() {
        return Err(PresentationError::EmptyPopulation);
    }
    let system = prefix_system(candidates, material, family)?;
    let compression = compress(&system);

    let word_of = |word: &[InputId]| -> Vec<String> {
        word.iter()
            .filter_map(|input| system.alphabet.get(input.0 as usize).cloned())
            .collect()
    };
    let receiver_of = |receiver: ReceiverId| -> PresentationReceiver {
        family
            .get(receiver.0 as usize)
            .copied()
            .unwrap_or(PresentationReceiver::TerminalToken)
    };

    // Each candidate's COMPLETE token sequence is the item that stands for it. Prefixes shorter
    // than a whole candidate are in the system because conduct is read over them, but a response is
    // a whole emission and only whole emissions are members of a block.
    let mut block_members: BTreeMap<usize, BTreeSet<String>> = BTreeMap::new();
    let mut block_surfaces: BTreeMap<usize, BTreeSet<String>> = BTreeMap::new();
    let mut block_inherited: BTreeMap<usize, bool> = BTreeMap::new();
    let material_can_answer = material.can_answer();
    let mut block_of_candidate: BTreeMap<String, usize> = BTreeMap::new();
    for candidate in candidates {
        let Some(position) = system.index.get(&candidate.tokens) else {
            continue;
        };
        let block = compression.conduct.block_of(ItemId(*position as u64));
        let Some(block) = block else { continue };
        block_members
            .entry(block)
            .or_default()
            .insert(candidate.identity.clone());
        block_surfaces
            .entry(block)
            .or_default()
            .insert(candidate.tokens.join(" "));
        let inherited = material.is_contiguous_span(&candidate.tokens);
        let slot = block_inherited.entry(block).or_insert(true);
        *slot = *slot && inherited;
        block_of_candidate.insert(candidate.identity.clone(), block);
    }

    let ordered: Vec<usize> = block_members.keys().copied().collect();
    // One representative per response block: the canonically first whole candidate in it, with the
    // token sequence that reaches it. Canonical so the representative is read off the material and
    // not off iteration order.
    let representatives: Vec<(ItemId, Vec<String>)> = ordered
        .iter()
        .filter_map(|block| {
            let identity = block_members[block].iter().next()?;
            let candidate = candidates
                .iter()
                .find(|candidate| &candidate.identity == identity)?;
            let position = system.index.get(&candidate.tokens)?;
            Some((ItemId(*position as u64), candidate.tokens.clone()))
        })
        .collect();
    let blocks: Vec<ResponseBlock> = ordered
        .iter()
        .map(|block| ResponseBlock {
            members: block_members[block].iter().cloned().collect(),
            surfaces: block_surfaces[block].iter().cloned().collect(),
            wholly_inherited: material_can_answer.then(|| block_inherited[block]),
        })
        .collect();

    // ---- THE QUESTIONS ----
    //
    // **Asked between RESPONSE BLOCKS, not between collapsed pairs.** An earlier form of this read
    // the collapsed population directly and mapped each pair's two sides to response blocks; that
    // silently dropped every pair whose members were shorter prefixes rather than whole emissions,
    // and on real material it returned **zero questions against 59,040 collapsed pairs.** A
    // question is a property of the two blocks, so it is taken between them.
    //
    // Each block contributes one representative — the item whose whole token sequence sits in it,
    // taken canonically so the choice is not an ordering artefact. The word comes from the
    // collapsed population when conduct separated the two, and from the one-shot faces when a
    // declared receiver already told them apart on the empty word.
    let collapsed_index: BTreeMap<(ItemId, ItemId), &_> = compression
        .collapsed
        .iter()
        .map(|pair| {
            let key = if pair.left <= pair.right {
                (pair.left, pair.right)
            } else {
                (pair.right, pair.left)
            };
            (key, pair)
        })
        .collect();
    let mut questions = Vec::new();
    for left_at in 0..representatives.len() {
        for right_at in (left_at + 1)..representatives.len() {
            let (left, left_tokens) = &representatives[left_at];
            let (right, right_tokens) = &representatives[right_at];
            let key = if left <= right {
                (*left, *right)
            } else {
                (*right, *left)
            };
            match collapsed_index.get(&key) {
                Some(pair) => questions.push(SeparatingQuestion {
                    left_block: left_at,
                    right_block: right_at,
                    word: word_of(&pair.distinguishing_word),
                    witness: pair
                        .witness
                        .map(|(receiver, one, two)| (receiver_of(receiver), one.0, two.0)),
                    separated_by_terminus: pair.separated_by_terminus,
                }),
                // No collapsed pair means the one-shot reading already separated them: some
                // declared receiver differs on the EMPTY word, so nothing needs to be asked to see
                // it and the word is empty by construction rather than by omission.
                None => {
                    let witness = family.iter().find_map(|face| {
                        let one = system.face(left_tokens, *face);
                        let two = system.face(right_tokens, *face);
                        (one != two).then_some((*face, one, two))
                    });
                    questions.push(SeparatingQuestion {
                        left_block: left_at,
                        right_block: right_at,
                        word: Vec::new(),
                        witness,
                        separated_by_terminus: false,
                    });
                }
            }
        }
    }

    Ok(JunctionDivision {
        family: family.to_vec(),
        candidate_population: candidates.len(),
        one_shot_blocks: compression.one_shot.len(),
        conduct_blocks: blocks.len(),
        rounds: compression.rounds,
        blocks,
        questions,
        collapsed_population: compression.collapsed.len(),
        memory_order: compression.memory_order(),
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn tokens(text: &str) -> Vec<String> {
        text.split_whitespace().map(ToOwned::to_owned).collect()
    }

    fn material() -> PresentationMaterial {
        PresentationMaterial {
            inherited_surfaces: vec![
                tokens("the receiver returns the arc onward"),
                tokens("the current returns the residual"),
            ],
        }
    }

    fn population() -> Vec<PresentedCandidate> {
        vec![
            // a contiguous span of the first surface
            PresentedCandidate::new("inherited", tokens("the receiver returns the arc")),
            // the same prefix, a different terminal token: separated by one receiver at once
            PresentedCandidate::new("crossed", tokens("the receiver returns the residual")),
            // a composition: no surface contains it as a window
            PresentedCandidate::new("composed", tokens("the receiver returns the residual onward")),
        ]
    }

    /// The remainder comes back with the word that separates it, not as a count.
    #[test]
    fn every_separated_alternative_carries_its_word_or_its_witness() {
        let division = divide(&population(), "inherited", &material()).unwrap();
        assert_eq!(division.answer, "inherited");
        assert_eq!(
            division.indistinguishable.len() + division.separated.len(),
            population().len() - 1
        );
        for alternative in &division.separated {
            assert!(
                !alternative.distinguishing_word.is_empty() || alternative.witness.is_some(),
                "an alternative separated by nothing at all: {alternative:?}"
            );
        }
    }

    /// **The window test, and its complement.** A candidate that is a span of the material is
    /// named as one; a candidate that is not is named as composed.
    #[test]
    fn the_window_test_separates_the_span_from_the_composition() {
        let division = divide(&population(), "inherited", &material()).unwrap();
        assert!(division.answer_is_inherited_span);
        assert!(division.inherited_candidates.contains(&"inherited".to_owned()));
        assert!(division.composed_candidates.contains(&"composed".to_owned()));
        // And uttering the composition instead flips the answer's own face without moving the
        // population it stood in for.
        let composed = divide(&population(), "composed", &material()).unwrap();
        assert!(!composed.answer_is_inherited_span);
        assert_eq!(composed.conduct_blocks, division.conduct_blocks);
        assert_eq!(composed.collapsed_population, division.collapsed_population);
    }

    /// The division is over the prefix population, so the blocks are the causal states of the
    /// emission and the rounds are how far back the reading had to look.
    #[test]
    fn the_division_returns_a_partition_and_its_exact_loss() {
        let division = divide(&population(), "inherited", &material()).unwrap();
        assert!(division.conduct_blocks >= division.one_shot_blocks);
        assert!(division.rounds >= 1);
        // `None` is a genuine zero: the one-shot reading was already exact.
        if division.collapsed_population == 0 {
            assert_eq!(division.memory_order, None);
        } else {
            assert!(division.memory_order.is_some());
        }
    }

    /// Two frames on one predicate. The index is a precomputation, not an approximation, and a
    /// disagreement anywhere would be a defect rather than a tolerance.
    #[test]
    fn the_span_index_agrees_with_the_reference_scan() {
        let material = material();
        let index = material.span_index(4);
        assert!(index.population() > 0);
        let probes = [
            tokens("the receiver returns"),
            tokens("the receiver returns the arc"),
            tokens("receiver returns the residual"),
            tokens("the current returns the residual"),
            tokens("nothing like this occurs"),
            tokens("arc"),
            Vec::new(),
        ];
        for probe in &probes {
            match index.is_contiguous_span(probe) {
                Some(carried) => assert_eq!(
                    carried,
                    material.is_contiguous_span(probe),
                    "the two frames disagree on {probe:?}"
                ),
                None => assert!(
                    probe.len() > index.longest(),
                    "the index refused a probe inside its declared length: {probe:?}"
                ),
            }
        }
    }

    /// An answer that was never presented is refused rather than invented.
    #[test]
    fn an_unpresented_answer_is_refused() {
        assert_eq!(
            divide(&population(), "never-emitted", &material()),
            Err(PresentationError::AnswerNotPresented("never-emitted".into()))
        );
        assert_eq!(
            divide(&[], "anything", &material()),
            Err(PresentationError::EmptyPopulation)
        );
    }

    /// **The receiver family is not a label the caller attached.** Varying the material moves the
    /// inherited-span face, which moves the partition — the authored-partition check, run.
    #[test]
    fn varying_the_material_moves_the_partition() {
        let narrow = material();
        let mut wide = material();
        // One more surface, which makes `crossed` a span of the material without touching the
        // emitted population at all.
        wide.inherited_surfaces
            .push(tokens("the receiver returns the residual"));
        let narrow_division = divide(&population(), "inherited", &narrow).unwrap();
        let wide_division = divide(&population(), "inherited", &wide).unwrap();
        assert_ne!(
            narrow_division.inherited_candidates,
            wide_division.inherited_candidates,
            "a receiver family blind to the material would return the same partition on both"
        );
        assert!(narrow_division.composed_candidates.contains(&"crossed".to_owned()));
        assert!(wide_division.inherited_candidates.contains(&"crossed".to_owned()));
        // On this population the block COUNTS do not move, because the other three receivers
        // already separate the same prefixes. That is a real return about this material rather
        // than a failure, and the arm below is the one that isolates the span face.
        assert_eq!(
            (narrow_division.one_shot_blocks, narrow_division.conduct_blocks),
            (wide_division.one_shot_blocks, wide_division.conduct_blocks)
        );
    }

    /// **The span face isolated.** Two candidates ending on the same token, with no horizon and no
    /// sources, agree on the other three receivers exactly. Whether the material contains them as
    /// windows is then the only thing that can separate them — and it does, which is the check
    /// that this receiver is load-bearing rather than decorative.
    #[test]
    fn the_span_face_alone_separates_two_otherwise_identical_candidates() {
        let population = vec![
            PresentedCandidate::new("left", tokens("alpha beta")),
            PresentedCandidate::new("right", tokens("gamma beta")),
        ];
        let separating = PresentationMaterial {
            inherited_surfaces: vec![tokens("alpha beta gamma")],
        };
        let blind = PresentationMaterial {
            inherited_surfaces: vec![tokens("alpha beta gamma"), tokens("gamma beta")],
        };
        let separated = divide(&population, "left", &separating).unwrap();
        let merged = divide(&population, "left", &blind).unwrap();
        assert_eq!(separated.indistinguishable, Vec::<String>::new());
        assert_eq!(separated.separated.len(), 1);
        assert_eq!(
            separated.separated[0].witness.map(|(face, _, _)| face),
            Some(PresentationReceiver::InheritedSpan),
            "the span face is the witness"
        );
        assert_eq!(merged.indistinguishable, vec!["right".to_owned()]);
        assert!(merged.separated.is_empty());
        assert!(
            merged.one_shot_blocks < separated.one_shot_blocks,
            "the blind material must merge what the separating material tells apart"
        );
    }
}

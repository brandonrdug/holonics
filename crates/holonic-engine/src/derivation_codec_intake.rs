//! A foreign codec, recovered from its own declared statistics, entering the conditioning path by
//! the seam the body's own material enters by.
//!
//! ## The receiver question
//!
//! *Can a conditioner the body did not author be recovered from provided statistics alone, condition
//! the body through the same seam its own reading uses, and can the body then say which readings it
//! can tell apart from its own and which it cannot — naming the material that separates them?*
//!
//! ## What recovery is here, and what it is not
//!
//! Brandon, correcting a prior misreading of this organ:
//!
//! > *"I think you are potentially misinterpretting it and expecting the machine to reverse engineer
//! > black boxes without the necessary parameters provided. It's like Fourier Analysis... we need the
//! > machine to be able to derive correlations and relationships from provided statistics as
//! > parameters."*
//!
//! and, on whose codec it is:
//!
//! > *"'pure' and 'impure' are still the same thing, just different by perspectives. 'Someone else's
//! > architecture' is still 'codec directly', there is no codec that exists without cause, there is no
//! > thing that has nature that cannot be attributed to a cause. They distill & diffuse into
//! > equivalent discrete algorithmic classes."*
//!
//! So nothing below queries an oracle for its parameters. The foreign conditioner **declares its
//! statistics**: over an exhausted query family it returns, for every word, the segmentation it makes
//! — and the token-length profile of that segmentation is the provided statistic, exactly as a
//! sampled waveform is the provided statistic a spectrum is recovered from. [`recover`] derives the
//! relations those statistics imply; this module wires them onto the conditioning path.
//!
//! ## The four slots `CLAUDE.md` §4 asks for
//!
//! ```text
//!   source geometry    real linguistic material, presented as its maximal runs over a declared
//!                      alphabet
//!   receiver map       the foreign conditioner's declared statistics: the token-length profile it
//!                      returns over the exhausted query family
//!   transport          symbol succession through a run
//!   returned residual  the symbol pairs the statistics hold apart, each with the shortest context
//!                      that does it; the symbols the conditioner emits nothing for; the symbols the
//!                      declared alphabet does not carry; and the identifier positions two founded
//!                      morphologies read differently, each with the shortest word of material that
//!                      separates them
//! ```
//!
//! ## The relations, which are the return
//!
//! A [`RecoveredRelations`] carries three relations over the declared symbols, none of them a count:
//!
//! ```text
//!   the symbol quotient    which symbols the statistics never separate
//!   the separation         each separated pair with the SHORTEST context that separates it
//!   the adjacency          Join / Cut per ordered class pair -- which classes agglutinate
//! ```
//!
//! The second is the relation in Brandon's sense: a *correlation derived from provided statistics*,
//! carrying the material that produced it. [`RecoveredRelations::agglutinating`] hands back the
//! `Join` sub-relation, which is the one a segmentation is made of.
//!
//! ## The seam, and why entry by it is the whole point
//!
//! [`FoundedMorphology::from_founded_words`] is declared in `conditioned_derivation` as *"the seam a
//! foreign conditioner enters by — a foreign conditioner hands over its founded words each with its
//! own lineage rendered as text, and everything below runs unchanged."* That is the entry
//! [`intake`] uses and the only one. A recovered codec segments real material; the tokens are the
//! founded words; the recovery's own account of why each word was cut is the lineage. Nothing
//! downstream is told that a conditioner was foreign, and nothing downstream reads the lineage:
//! `FoundedStem`'s own declaration says *"the only field any conduct path reads is the stem text."*
//!
//! ## The two cases this module is built to exhibit
//!
//! - **The body cannot tell one recovered conditioner from its own reading.** A foreign codec whose
//!   statistics say *letters agglutinate, separators are dropped and break* is recovered from
//!   testimony alone, and the words it founds on real material are the words [`expose`] founds,
//!   in order, whole by whole. The founded morphologies then agree on **everything any conduct path
//!   reads** and differ only in `foreign_lineage`, which no conduct path reads.
//! - **The body tells another apart, and names the word.** A character-level conditioner over the
//!   same alphabet founds a different committed population, and [`distinguish`] returns the
//!   identifier positions the two readings split differently — each with the shortest word of
//!   material after which the coarser reading finally sees the difference, and the founded stem by
//!   which the finer reading saw it at once.
//!
//! **The order of those two matters and is a rule, not a preference.** `CLAUDE.md` §8: a gauge whose
//! group acts trivially on the declared material is not a gauge. The distinction instrument is shown
//! returning a non-empty population *before* its empty return is read as agreement, and
//! [`MorphologyDistinction::indistinguishable`] is therefore never evidence on its own.
//!
//! ## The declared refusals, and why an empty return is not one of them
//!
//! `CLAUDE.md` §8 again: a law that returns zero proves nothing about itself. A conditioner whose
//! declared statistics separate no two symbols has supplied no relation, and this module refuses it
//! **by type** — [`IntakeRefusal::NoRelationRecovered`] — rather than handing back an empty
//! morphology that a caller would have to notice was empty. The same holds for material that carries
//! no declared symbol and for a population that never recurs across two wholes.
//!
//! ## What this module does not own
//!
//! It does not own [`recover`], [`compress`], `MorphemicIncidence`, or `FoundedMorphology` — it calls
//! all four. It does not own a second segmentation law: every token comes from
//! [`RecoveredCodec::segment`], so the lineage and the founded words are read through one runner. It
//! does not own file access; a caller presents named wholes of text.

use std::collections::{BTreeMap, BTreeSet};

use serde::{Deserialize, Serialize};
use thiserror::Error;

use crate::codec_recovery::{
    Boundary, Emission, Obstruction, OpaqueSymbolCodec, RecoveredCodec, RecoveryApertures,
    RecoveryError, RecoveryWork, Symbol, SymbolAlphabet, SymbolSeparation, recover,
};
use crate::conditioned_derivation::{
    ConditionedDerivationRefusal, FoundedMorphology, MorphemicIncidence, StemFiring,
};
use crate::receiver_exact_compression::{ItemId, ReceiverExactCompression, compress};

/// The name an intake writes onto itself, so a return read back from octets can be checked against
/// what produced it rather than assumed.
pub const INTAKE_SCHEMA: &str = "holonic-engine.derivation-codec-intake.v1";

/// The name a distinction writes onto itself.
pub const DISTINCTION_SCHEMA: &str = "holonic-engine.morphology-distinction.v1";

// -------------------------------------------------------------------------------------------------
// Presentation: real material, read through a declared alphabet
// -------------------------------------------------------------------------------------------------

/// One whole of real material, presented to a foreign conditioner through a declared alphabet.
///
/// A conditioner is asked about the symbols it was declared over and no others, so material is
/// presented as its **maximal runs over the declared alphabet**. A symbol the alphabet does not carry
/// is a declared boundary of presentation and is retained by name in [`Self::undeclared`] rather than
/// projected onto a representative the conditioner never testified about.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct PresentedWhole {
    pub whole: String,
    /// The maximal runs of declared symbols, in reading order.
    pub runs: Vec<String>,
    /// Symbols this whole carries that the declared alphabet does not, **named**.
    pub undeclared: BTreeSet<char>,
}

/// Read one whole of real material into the runs a declared alphabet admits.
///
/// **The declared exterior codec, stated once and applied identically to every conditioner under
/// test.** Text is case-folded down by the ASCII rule, which is [`expose`](crate::conditioned_derivation::expose)'s
/// own single orthographic rule and is forced by the same material: a deposited identifier is written
/// `exactCarrier` while prose writes `carrier`, so a case-sensitive presentation could found no
/// shared stem. The fold tells a conditioner nothing about its own classes; it is the same fold for
/// all of them, which is what keeps a comparison between two conditioners uncontaminated by it.
pub fn present(whole: &str, text: &str, alphabet: &BTreeSet<char>) -> PresentedWhole {
    let mut runs = Vec::new();
    let mut undeclared = BTreeSet::new();
    let mut open = String::new();
    for symbol in text.chars() {
        let folded = symbol.to_ascii_lowercase();
        if alphabet.contains(&folded) {
            open.push(folded);
        } else {
            undeclared.insert(folded);
            if !open.is_empty() {
                runs.push(std::mem::take(&mut open));
            }
        }
    }
    if !open.is_empty() {
        runs.push(open);
    }
    PresentedWhole {
        whole: whole.to_owned(),
        runs,
        undeclared,
    }
}

// -------------------------------------------------------------------------------------------------
// The relations the declared statistics imply
// -------------------------------------------------------------------------------------------------

/// One entry of the adjacency relation: whether a token break falls between two symbol classes.
///
/// Written with each class's **representative** — its least member — because a class is named by its
/// members and not by an index into a table.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct ClassAdjacency {
    pub left: Symbol,
    pub right: Symbol,
    pub boundary: Boundary,
}

/// The relations a foreign conditioner's declared statistics imply.
///
/// Every member is an exhibited artifact. There is no rate, no score, no ranking, and no magnitude
/// anywhere in it; [`Self::work`] carries the exact counts the recovery paid, which is a cost stated
/// rather than a quantity that decides anything.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct RecoveredRelations {
    pub schema: String,
    /// The declared symbols, in canonical order.
    pub alphabet: Vec<Symbol>,
    /// The longest word the conditioner was asked about. The family was **exhausted**, not sampled.
    pub radius: usize,
    /// The symbol quotient: which symbols the statistics never separate.
    pub classes: Vec<BTreeSet<Symbol>>,
    /// Per class representative, whether a symbol of that class enters the token it is read into.
    pub emission: Vec<(Symbol, Emission)>,
    /// **The relation.** Each separated pair with the shortest context that separates it and both
    /// returns at it.
    pub separations: Vec<SymbolSeparation>,
    /// The adjacency relation over class representatives, every ordered pair.
    pub adjacency: Vec<ClassAdjacency>,
    /// Adjacency entries no input of any length decides. A freedom, reported rather than hidden.
    pub gauge_freedom: Vec<(Symbol, Symbol)>,
    pub work: RecoveryWork,
}

impl RecoveredRelations {
    /// The `Join` sub-relation — the pairs of classes that agglutinate. This is what a segmentation
    /// is made of; the `Cut` entries are its complement and both are carried in [`Self::adjacency`].
    pub fn agglutinating(&self) -> Vec<&ClassAdjacency> {
        self.adjacency
            .iter()
            .filter(|entry| entry.boundary == Boundary::Join)
            .collect()
    }

    /// The shortest context that placed two symbols apart, or `None` when the statistics hold them
    /// together.
    pub fn separating_context(&self, left: Symbol, right: Symbol) -> Option<&SymbolSeparation> {
        self.separations.iter().find(|separation| {
            (separation.left, separation.right) == (left, right)
                || (separation.left, separation.right) == (right, left)
        })
    }

    /// The class a symbol fell in, written as that class's representative.
    pub fn representative_of(&self, symbol: Symbol) -> Option<Symbol> {
        self.classes
            .iter()
            .find(|block| block.contains(&symbol))
            .and_then(|block| block.iter().next().copied())
    }

    /// The classes the conditioner emits no character for. Material it drops, named.
    pub fn dropped(&self) -> BTreeSet<Symbol> {
        self.emission
            .iter()
            .filter(|(_, emission)| *emission == Emission::Drop)
            .filter_map(|(representative, _)| {
                self.classes
                    .iter()
                    .find(|block| block.contains(representative))
                    .cloned()
            })
            .flatten()
            .collect()
    }
}

// -------------------------------------------------------------------------------------------------
// The intake
// -------------------------------------------------------------------------------------------------

/// One founded word as it was handed across the seam: the word, the wholes that witnessed it, and
/// what the foreign conditioner says founded it.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct FoundedWordLineage {
    pub word: String,
    pub wholes: Vec<String>,
    /// The conditioner's own account, rendered as text. Carried across the seam and **never parsed**
    /// by anything downstream.
    pub lineage: Vec<String>,
}

/// What the material carried that no founded word does. Retained as the obstruction it is.
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct RetainedObstruction {
    /// Declared symbols the recovered conditioner emits no character for.
    pub dropped: BTreeSet<Symbol>,
    /// Per whole, the symbols the declared alphabet does not carry, named.
    pub undeclared: BTreeMap<String, BTreeSet<char>>,
}

/// A foreign conditioner recovered from its declared statistics and carried onto the conditioning
/// path.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CodecIntake {
    pub schema: String,
    /// What this conditioner is called. Provenance; nothing reads it.
    pub conditioner: String,
    pub relations: RecoveredRelations,
    /// The recovered structure. It runs on material no query ever visited.
    pub codec: RecoveredCodec,
    /// **The morphology, founded through the seam.** Indistinguishable in kind from one the body's
    /// own exposure founds.
    pub morphology: FoundedMorphology,
    /// Every word handed across the seam, in the order the material first exhibited it.
    pub founded: Vec<FoundedWordLineage>,
    pub retained: RetainedObstruction,
}

/// Why an intake was refused. Each variant carries the material that produced it.
#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum IntakeRefusal {
    /// The recovery halted. The conditioner's statistics are outside the declared shape, or the
    /// declared family was too small to choose between the codecs it retained.
    #[error("the recovery returned {} obstruction(s) rather than a codec", .obstructions.len())]
    RecoveryObstructed { obstructions: Vec<Obstruction> },
    /// **The declared refusal.** The conditioner's statistics separate no two declared symbols, so
    /// no relation was recovered and there is nothing to condition on. Refused by type rather than
    /// returned as an empty morphology.
    #[error(
        "the declared statistics separate no two symbols; the quotient is one class {classes:?}"
    )]
    NoRelationRecovered { classes: Vec<BTreeSet<Symbol>> },
    /// The recovered conditioner founded no word at all on the presented material.
    #[error("no founded word on any of the presented wholes: {wholes:?}")]
    NoFoundedWord { wholes: Vec<String> },
    /// Words were founded and none of them recurred across two distinct wholes, so the morphology
    /// commits nothing and no stem reaches the derivation path.
    #[error("{} founded word(s) and none recurred across two distinct wholes", .founded.len())]
    NoCommittedStem { founded: Vec<String> },
    #[error(transparent)]
    Recovery(#[from] RecoveryError),
    #[error(transparent)]
    Conditioned(#[from] ConditionedDerivationRefusal),
}

/// Recover a foreign conditioner from its declared statistics and condition on real material with it.
///
/// `alphabet` and `radius` declare the query family, which is exhausted rather than sampled, so
/// every relation returned is a statement about the whole family. `apertures` is what the **caller's
/// host** can hold; it is passed through to [`recover`] and is not this organ's to pick. `material`
/// is named wholes of real text; it is presented through [`present`] and segmented by the recovered
/// structure, and the tokens enter [`FoundedMorphology::from_founded_words`] — the one seam.
///
/// ## Cost
///
/// The recovery pays one call to the conditioner per family word — `sum(|A|^L for L in 1..=radius)`
/// — and that figure is returned in [`RecoveredRelations::work`] rather than optimised away. The
/// conditioning then pays one [`RecoveredCodec::segment`] per presented run, which is linear in the
/// material.
pub fn intake(
    conditioner: &str,
    target: &OpaqueSymbolCodec,
    alphabet: &SymbolAlphabet,
    radius: usize,
    apertures: RecoveryApertures,
    material: &[(String, String)],
) -> Result<CodecIntake, IntakeRefusal> {
    // The declared alphabet arrives as a `SymbolAlphabet`; the recovery is asked about its symbols
    // in declaration order. Text material still enters through `present`, which is the exterior
    // codec, and is translated into these symbols at the segmentation below.
    let symbols = alphabet.symbols();
    let recovery = recover(target, &symbols, radius, apertures)?;
    if !recovery.obstructions.is_empty() {
        return Err(IntakeRefusal::RecoveryObstructed {
            obstructions: recovery.obstructions,
        });
    }
    // A recovery with no obstruction carries a codec; the two are tied by `CodecRecovery`'s own
    // invariant, and reading the option rather than asserting it keeps that tie checkable.
    let codec = recovery
        .codec
        .clone()
        .ok_or_else(|| IntakeRefusal::RecoveryObstructed {
            obstructions: Vec::new(),
        })?;

    if recovery.separations.is_empty() {
        return Err(IntakeRefusal::NoRelationRecovered {
            classes: recovery.classes,
        });
    }

    let count = codec.classes.len();
    let representative: Vec<Symbol> = codec
        .classes
        .iter()
        .map(|block| {
            block
                .iter()
                .next()
                .copied()
                .expect("a recovered class is never empty")
        })
        .collect();
    let relations = RecoveredRelations {
        schema: INTAKE_SCHEMA.to_owned(),
        alphabet: recovery.alphabet.clone(),
        radius: recovery.radius,
        classes: recovery.classes.clone(),
        emission: representative
            .iter()
            .copied()
            .zip(codec.emission.iter().copied())
            .collect(),
        separations: recovery.separations.clone(),
        adjacency: {
            let mut adjacency = Vec::with_capacity(count * count);
            for left in 0..count {
                for right in 0..count {
                    adjacency.push(ClassAdjacency {
                        left: representative[left],
                        right: representative[right],
                        boundary: codec.boundary[left][right],
                    });
                }
            }
            adjacency
        },
        gauge_freedom: recovery
            .gauge_freedom
            .iter()
            .map(|(left, right)| {
                (
                    representative[left.0 as usize],
                    representative[right.0 as usize],
                )
            })
            .collect(),
        work: recovery.work,
    };

    let declared: BTreeSet<Symbol> = recovery.alphabet.iter().copied().collect();
    // **The exterior text codec's chart.** `present` reads text and this organ's material is text,
    // so the declared symbols are looked up by their identities. A symbol whose identity is not a
    // single character cannot be reached by `present` at all — it is not projected onto one that
    // can, it simply never appears in a run, which is the same discipline `present` already applies
    // to an undeclared character.
    let declared_text: BTreeSet<char> = declared
        .iter()
        .filter_map(|symbol| {
            let identity = alphabet.identity(*symbol)?;
            let mut characters = identity.chars();
            match (characters.next(), characters.next()) {
                (Some(single), None) => Some(single),
                _ => None,
            }
        })
        .collect();
    let mut order: BTreeMap<Vec<Symbol>, usize> = BTreeMap::new();
    let mut founded: Vec<FoundedWordLineage> = Vec::new();
    let mut retained = RetainedObstruction {
        dropped: relations.dropped(),
        undeclared: BTreeMap::new(),
    };
    for (whole, text) in material {
        let presented = present(whole, text, &declared_text);
        if !presented.undeclared.is_empty() {
            retained
                .undeclared
                .insert(whole.clone(), presented.undeclared);
        }
        for run in &presented.runs {
            // Text into symbols, at the one seam where the exterior codec meets the recovered one.
            let word: Vec<Symbol> = run
                .chars()
                .filter_map(|character| alphabet.symbol_of(character.to_string().as_str()))
                .collect();
            for token in codec.segment(&word)? {
                match order.get(&token).copied() {
                    Some(slot) => {
                        // The `last()` guard is the cost law, not a nicety: material arrives whole
                        // by whole, so after a word's first occurrence in a whole the last witness
                        // is that whole, and the linear `contains` scan runs at most once per
                        // (word, whole) rather than once per occurrence.
                        let carried: &mut FoundedWordLineage = &mut founded[slot];
                        if carried.wholes.last() != Some(whole) && !carried.wholes.contains(whole) {
                            carried.wholes.push(whole.clone());
                        }
                    }
                    None => {
                        let lineage = account_for(&token, &codec, &relations, alphabet);
                        let spelled = alphabet.render(&token);
                        order.insert(token.clone(), founded.len());
                        founded.push(FoundedWordLineage {
                            word: spelled,
                            wholes: vec![whole.clone()],
                            lineage,
                        });
                    }
                }
            }
        }
    }

    if founded.is_empty() {
        return Err(IntakeRefusal::NoFoundedWord {
            wholes: material.iter().map(|(whole, _)| whole.clone()).collect(),
        });
    }

    let morphology = FoundedMorphology::from_founded_words(founded.iter().map(|entry| {
        (
            entry.word.clone(),
            entry.wholes.clone(),
            entry.lineage.clone(),
        )
    }));
    if morphology.committed().is_empty() {
        return Err(IntakeRefusal::NoCommittedStem {
            founded: founded.into_iter().map(|entry| entry.word).collect(),
        });
    }

    Ok(CodecIntake {
        schema: INTAKE_SCHEMA.to_owned(),
        conditioner: conditioner.to_owned(),
        relations,
        codec,
        morphology,
        founded,
        retained,
    })
}

/// The foreign conditioner's own account of why one word was cut out of the material.
///
/// Every entry is a fact read off the recovered structure and the recovered relations. Nothing here
/// is parsed downstream — `from_founded_words` carries the lineage and `FoundedStem` declares that
/// the only field any conduct path reads is the stem text — so this is provenance in the exact sense
/// `CLAUDE.md` §9 asks for and never a channel.
fn account_for(
    word: &[Symbol],
    codec: &RecoveredCodec,
    relations: &RecoveredRelations,
    alphabet: &SymbolAlphabet,
) -> Vec<String> {
    let mut lineage = Vec::new();
    let classes: Vec<Symbol> = word
        .iter()
        .filter_map(|symbol| relations.representative_of(*symbol))
        .collect();
    lineage.push(format!("recovered classes {}", alphabet.render(&classes)));
    let mut adjacencies: BTreeSet<(Symbol, Symbol)> = BTreeSet::new();
    for pair in classes.windows(2) {
        adjacencies.insert((pair[0], pair[1]));
    }
    for (left, right) in &adjacencies {
        if let Some(boundary) = codec.boundary_between(*left, *right) {
            lineage.push(format!(
                "boundary({},{}) = {}",
                alphabet.identity(*left).unwrap_or("?"),
                alphabet.identity(*right).unwrap_or("?"),
                match boundary {
                    Boundary::Join => "Join",
                    Boundary::Cut => "Cut",
                }
            ));
        }
    }
    let mut distinct: BTreeSet<Symbol> = classes.iter().copied().collect();
    distinct.extend(relations.dropped().iter().take(1));
    let members: Vec<Symbol> = distinct.into_iter().collect();
    for (index, left) in members.iter().enumerate() {
        for right in &members[index + 1..] {
            if let Some(separation) = relations.separating_context(*left, *right) {
                lineage.push(format!(
                    "class {:?} apart from {:?} by context {:?}^{:?}",
                    alphabet.identity(*left).unwrap_or("?"),
                    alphabet.identity(*right).unwrap_or("?"),
                    alphabet.render(&separation.prefix),
                    alphabet.render(&separation.suffix)
                ));
            }
        }
    }
    lineage
}

// -------------------------------------------------------------------------------------------------
// The distinction: can the body tell two conditioners apart, and by what word
// -------------------------------------------------------------------------------------------------

/// One pair of identifier positions two founded morphologies read differently.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct PositionDistinction {
    pub left: String,
    pub right: String,
    /// The shortest word of material after which the reading that **merged** them finally separates
    /// them under its own successor conduct. `None` when no word of any length ever does — that
    /// reading is permanently blind to the difference, which is a stronger statement than a long
    /// word and is reported as its own species rather than as a missing value.
    pub distinguishing_word: Option<String>,
    /// The founded stem by which the reading that **separated** them saw it at once, or `None` when
    /// the difference is a terminus rather than a stem.
    pub witness_stem: Option<String>,
}

/// Whether the body's reading of one item population can tell two founded morphologies apart, and by
/// what material.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct MorphologyDistinction {
    pub schema: String,
    pub left: String,
    pub right: String,
    /// Committed stems only the left morphology founded **that fire on this material**, with the
    /// positions they fire at. A stem neither reading can exercise here is not part of the
    /// difference and is not reported as one.
    pub only_left_reaching: Vec<StemFiring>,
    pub only_right_reaching: Vec<StemFiring>,
    /// Positions the left reading merges and the right reading separates at once.
    pub right_separates: Vec<PositionDistinction>,
    /// Positions the right reading merges and the left reading separates at once.
    pub left_separates: Vec<PositionDistinction>,
}

impl MorphologyDistinction {
    /// The body's reading cannot tell these two morphologies apart on this material.
    ///
    /// **This is never evidence on its own.** `CLAUDE.md` §8: a gauge whose group acts trivially is
    /// not a gauge, so a caller must first exhibit this instrument returning a non-empty population
    /// on the same material and the same item population.
    pub fn indistinguishable(&self) -> bool {
        self.right_separates.is_empty() && self.left_separates.is_empty()
    }

    /// Every distinguishing word this distinction exhibited, in canonical order, deduplicated.
    /// Positions no word separates contribute nothing here and are carried in the populations above.
    pub fn distinguishing_words(&self) -> BTreeSet<&str> {
        self.right_separates
            .iter()
            .chain(self.left_separates.iter())
            .filter_map(|distinction| distinction.distinguishing_word.as_deref())
            .collect()
    }

    /// Every founded stem by which some difference was seen at once, in canonical order.
    pub fn witness_stems(&self) -> BTreeSet<&str> {
        self.right_separates
            .iter()
            .chain(self.left_separates.iter())
            .filter_map(|distinction| distinction.witness_stem.as_deref())
            .collect()
    }
}

/// Read one identifier population under two founded morphologies and return what separates them.
///
/// The two readings are the same items and the same transport; they differ only in which founded
/// stems are receivers. So a difference between them is a difference the **conditioning** made, and
/// it is exhibited as `receiver_exact_compression` exhibits every difference: the pair, the shortest
/// word of material that separates it, and the receiver that sees it.
pub fn distinguish(
    identifiers: &BTreeSet<String>,
    left: (&str, &FoundedMorphology),
    right: (&str, &FoundedMorphology),
) -> Result<MorphologyDistinction, IntakeRefusal> {
    let (left_name, left_morphology) = left;
    let (right_name, right_morphology) = right;
    let left_system = MorphemicIncidence::over(identifiers, left_morphology)?;
    let right_system = MorphemicIncidence::over(identifiers, right_morphology)?;
    let left_reading = compress(&left_system);
    let right_reading = compress(&right_system);
    let left_merged = left_reading.one_shot.identified_pairs();
    let right_merged = right_reading.one_shot.identified_pairs();

    let left_committed: BTreeSet<&str> = left_morphology.committed_stems().into_iter().collect();
    let right_committed: BTreeSet<&str> = right_morphology.committed_stems().into_iter().collect();

    Ok(MorphologyDistinction {
        schema: DISTINCTION_SCHEMA.to_owned(),
        left: left_name.to_owned(),
        right: right_name.to_owned(),
        only_left_reaching: left_system
            .firing()
            .into_iter()
            .filter(|firing| !right_committed.contains(firing.stem.as_str()))
            .collect(),
        only_right_reaching: right_system
            .firing()
            .into_iter()
            .filter(|firing| !left_committed.contains(firing.stem.as_str()))
            .collect(),
        right_separates: account_separations(
            &left_merged,
            &right_merged,
            &left_reading,
            &left_system,
            &right_system,
        ),
        left_separates: account_separations(
            &right_merged,
            &left_merged,
            &right_reading,
            &right_system,
            &left_system,
        ),
    })
}

/// The pairs `merged_by` holds together that `separated_by` splits, each with the merging reading's
/// own shortest distinguishing word and the splitting reading's witnessing stem.
fn account_separations(
    merged_by: &BTreeSet<(ItemId, ItemId)>,
    separated_by: &BTreeSet<(ItemId, ItemId)>,
    merging_reading: &ReceiverExactCompression,
    merging_system: &MorphemicIncidence,
    separating_system: &MorphemicIncidence,
) -> Vec<PositionDistinction> {
    merged_by
        .difference(separated_by)
        .map(|(left, right)| PositionDistinction {
            left: merging_system.render_position(*left),
            right: merging_system.render_position(*right),
            distinguishing_word: merging_reading
                .collapsed
                .iter()
                .find(|pair| (pair.left, pair.right) == (*left, *right))
                .map(|pair| merging_system.render_word(&pair.distinguishing_word)),
            witness_stem: separating_system
                .separating_stem(*left, *right)
                .map(str::to_owned),
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::codec_recovery::conform;
    use crate::conditioned_derivation::{
        ConditionedBody, DerivationQuery, StemStanding, derive, expose,
    };

    /// **What this test body declares as its host capacity.** The apertures moved out of
    /// `codec_recovery` on 2026-08-09 (`canon/THE_AUTHORED_LEVEL.md` §5.2); a fixture is a caller
    /// and declares its own. The values reproduce the excised constants so these fixtures' returns
    /// are unchanged by the move.
    const TEST_APERTURES: RecoveryApertures = RecoveryApertures {
        family_words: 65_536,
        free_entries: 12,
    };

    // ---------------------------------------------------------------------------------------------
    // Material. Two wholes of prose, so a word can recur across distinct sources, plus a deposit
    // whose recruited identifiers carry the morphemes the prose founds.
    // ---------------------------------------------------------------------------------------------

    const FIRST: &str = "The exact carrier of a chart is the carry it will not drop. \
         A formal carrier is a chart; an exact chart is a carrier. \
         Soma is the kernel and the witness is the kernel's own.";

    const SECOND: &str = "An exact carry is a carrier of the chart it came from. \
         The kernel is formal; the witness is exact. \
         A carrier is a chart and a chart is a carry.";

    fn corpus() -> Vec<(String, String)> {
        vec![
            ("first".to_owned(), FIRST.to_owned()),
            ("second".to_owned(), SECOND.to_owned()),
        ]
    }

    /// Three deposited routes reaching **one** statement by different recruitments. A production
    /// needs a route that reaches the query and an identifier that route does not recruit, so a
    /// single-route deposit could never exhibit one and would make the control below vacuous.
    fn deposit() -> Vec<(String, String)> {
        ["exact_chart_carry", "formal_carry", "kernelWitness"]
            .into_iter()
            .enumerate()
            .map(|(ordinal, recruits)| {
                (
                    format!("deposit-{ordinal}"),
                    format!(
                        "namespace Soma\n\
                         theorem carrier_transport_{ordinal} (P : Prop) (h : P) : exactCarrier P := by\n\
                         \x20 have bridged := {recruits}\n\
                         end Soma\n"
                    ),
                )
            })
            .collect()
    }

    /// The declared alphabet: the twenty-six ASCII letters and three separators the material really
    /// carries. Twenty-nine symbols at radius three is `29 + 841 + 24389` family words, inside the
    /// declared aperture.
    fn declared_characters() -> Vec<char> {
        let mut declared: Vec<char> = ('a'..='z').collect();
        declared.extend([' ', '.', '_']);
        declared
    }

    /// The declared alphabet, as symbols. The fixtures speak text; `intake` speaks symbols, and this
    /// is the one translation between them.
    fn alphabet() -> SymbolAlphabet {
        SymbolAlphabet::from_chars(&declared_characters())
            .expect("the fixture alphabet carries no repeat")
    }

    /// A text-speaking conditioner, presented through the declared alphabet.
    fn text_codec(law: impl Fn(&str) -> Vec<String> + 'static) -> OpaqueSymbolCodec {
        OpaqueSymbolCodec::over_text(&alphabet(), law)
    }

    /// A word written over the declared alphabet.
    fn word(spelling: &str) -> Vec<Symbol> {
        alphabet()
            .spell(spelling)
            .expect("fixture spellings are declared")
    }

    /// A segmentation, read back as spellings.
    fn spelled(segmentation: &[Vec<Symbol>]) -> Vec<String> {
        let declared = alphabet();
        segmentation
            .iter()
            .map(|token| declared.render(token))
            .collect()
    }

    fn sym(character: char) -> Symbol {
        alphabet()
            .symbol_of(character.to_string().as_str())
            .expect("every fixture character is declared")
    }

    /// A class, read back as characters so an assertion says what the quotient is.
    fn spell_class(block: &BTreeSet<Symbol>) -> BTreeSet<char> {
        let declared = alphabet();
        block
            .iter()
            .filter_map(|member| declared.identity(*member)?.chars().next())
            .collect()
    }

    fn is_separator(symbol: char) -> bool {
        matches!(symbol, ' ' | '.' | '_')
    }

    // ---------------------------------------------------------------------------------------------
    // The foreign conditioners. Each is an opaque law: the recovery holds a boxed `Fn` and the only
    // admitted contact is calling it, so nothing below is read out of these definitions.
    // ---------------------------------------------------------------------------------------------

    /// *Letters agglutinate; separators are dropped and break.* The conditioner whose reading of
    /// real material coincides with the body's own.
    fn word_runs() -> OpaqueSymbolCodec {
        text_codec(|input: &str| {
            let mut tokens = Vec::new();
            let mut current = String::new();
            for symbol in input.chars() {
                if is_separator(symbol) {
                    if !current.is_empty() {
                        tokens.push(std::mem::take(&mut current));
                    }
                } else {
                    current.push(symbol);
                }
            }
            if !current.is_empty() {
                tokens.push(current);
            }
            tokens
        })
    }

    /// *Every letter is its own token; separators are dropped.* A character-level conditioner: the
    /// same symbol quotient and the same emission as [`word_runs`], differing in exactly one
    /// adjacency entry, which is what makes the two comparable as codecs.
    fn characters() -> OpaqueSymbolCodec {
        text_codec(|input: &str| {
            input
                .chars()
                .filter(|symbol| !is_separator(*symbol))
                .map(|symbol| symbol.to_string())
                .collect()
        })
    }

    /// *A consonant run opens a token and carries the vowels after it; a vowel followed by a
    /// consonant breaks.* A syllabic conditioner, three classes with one dropped.
    fn syllables() -> OpaqueSymbolCodec {
        text_codec(|input: &str| {
            let vowel = |symbol: char| matches!(symbol, 'a' | 'e' | 'i' | 'o' | 'u');
            let mut tokens = Vec::new();
            let mut current = String::new();
            let mut previous: Option<char> = None;
            for symbol in input.chars() {
                let cut = match previous {
                    None => true,
                    Some(before) => {
                        is_separator(before)
                            || is_separator(symbol)
                            || (vowel(before) && !vowel(symbol))
                    }
                };
                if cut && !current.is_empty() {
                    tokens.push(std::mem::take(&mut current));
                }
                if !is_separator(symbol) {
                    current.push(symbol);
                }
                previous = Some(symbol);
            }
            if !current.is_empty() {
                tokens.push(current);
            }
            tokens
        })
    }

    /// *Everything is one token.* A conditioner whose declared statistics separate no two symbols.
    fn one_class() -> OpaqueSymbolCodec {
        text_codec(|input: &str| {
            if input.is_empty() {
                Vec::new()
            } else {
                vec![input.to_owned()]
            }
        })
    }

    /// A conditioner whose boundary decision is about the token's own length rather than about the
    /// adjacent pair of classes. Outside the declared shape, and refused as such.
    fn capped() -> OpaqueSymbolCodec {
        text_codec(|input: &str| {
            let mut tokens = Vec::new();
            let mut current = String::new();
            for symbol in input.chars() {
                if current.chars().count() == 3 {
                    tokens.push(std::mem::take(&mut current));
                }
                current.push(symbol);
            }
            if !current.is_empty() {
                tokens.push(current);
            }
            tokens
        })
    }

    fn native() -> FoundedMorphology {
        FoundedMorphology::condition(&[expose("first", FIRST), expose("second", SECOND)])
    }

    fn identifiers() -> BTreeSet<String> {
        ConditionedBody::mount(deposit())
            .expect("the deposit declares a theorem")
            .recruited_population()
    }

    // ---------------------------------------------------------------------------------------------
    // The relations, and the declared control on them
    // ---------------------------------------------------------------------------------------------

    /// Non-zero relations on statistics that carry them, each with the shortest context that
    /// produced it — and the contexts really are the shortest, which is what distinguishes a
    /// recovered relation from a working one.
    #[test]
    fn the_declared_statistics_return_relations_with_the_shortest_context_that_produced_each() {
        let carried = intake(
            "word-runs",
            &word_runs(),
            &alphabet(),
            3,
            TEST_APERTURES,
            &corpus(),
        )
        .expect("the conditioner is recoverable and founds a committed population");
        let relations = &carried.relations;

        assert_eq!(relations.classes.len(), 2, "{:?}", relations.classes);
        // **Asserted by membership, not by position.** The canonical class order is "by each class's
        // least member", and until the alphabet was rotated off `char` on 2026-08-13 that made it
        // ASCII collation -- the separator class came first because a space is 0x20. A `Symbol` is an
        // ordinal into a *declared* alphabet, so least member now means earliest declared, which is
        // the caller's statement rather than the encoding's. The classes are unchanged; only their
        // order is, and an index into a canonical order should never have been load-bearing.
        let spelled: Vec<BTreeSet<char>> = relations.classes.iter().map(spell_class).collect();
        assert!(
            spelled.contains(&BTreeSet::from([' ', '.', '_'])),
            "{spelled:?}"
        );
        assert!(
            spelled.contains(&('a'..='z').collect::<BTreeSet<char>>()),
            "{spelled:?}"
        );
        let emission: BTreeSet<(char, Emission)> = relations
            .emission
            .iter()
            .map(|(symbol, emission)| {
                (
                    alphabet()
                        .identity(*symbol)
                        .and_then(|identity| identity.chars().next())
                        .unwrap_or('?'),
                    *emission,
                )
            })
            .collect();
        assert_eq!(
            emission,
            BTreeSet::from([(' ', Emission::Drop), ('a', Emission::Emit)])
        );

        // The relation is non-empty and every entry carries its material.
        assert!(!relations.separations.is_empty());
        for separation in &relations.separations {
            assert_ne!(separation.left_return, separation.right_return);
            assert_ne!(
                relations.representative_of(separation.left),
                relations.representative_of(separation.right)
            );
        }

        // A dropped symbol against an emitted one is visible in the bare hole, so the shortest
        // context that separates them has length one.
        let separation = relations
            .separating_context(sym(' '), sym('a'))
            .expect("a dropped symbol and an emitted one are separated");
        assert_eq!(separation.context_length(), 1);
        assert_eq!(
            (
                alphabet().render(&separation.prefix).as_str(),
                alphabet().render(&separation.suffix).as_str()
            ),
            ("", "")
        );

        // The agglutination relation, read off the structure rather than out of the fixture.
        assert_eq!(
            relations.agglutinating(),
            vec![&ClassAdjacency {
                left: sym('a'),
                right: sym('a'),
                boundary: Boundary::Join
            }]
        );
        assert_eq!(
            carried
                .retained
                .dropped
                .iter()
                .filter_map(|s| alphabet().identity(*s)?.chars().next())
                .collect::<BTreeSet<char>>(),
            BTreeSet::from([' ', '.', '_'])
        );
    }

    /// **The declared control's refusal side.** Statistics that separate nothing supply no relation,
    /// and the intake says so by type rather than handing back an empty morphology.
    #[test]
    fn statistics_that_separate_no_two_symbols_are_refused_by_type_and_not_returned_empty() {
        let refusal = intake(
            "one-class",
            &one_class(),
            &alphabet(),
            3,
            TEST_APERTURES,
            &corpus(),
        )
        .expect_err("a conditioner that separates nothing supplies no relation");
        let IntakeRefusal::NoRelationRecovered { classes } = refusal else {
            panic!("expected NoRelationRecovered, got {refusal:?}");
        };
        assert_eq!(classes.len(), 1, "{classes:?}");
        assert_eq!(classes[0].len(), alphabet().len());
    }

    /// Material carrying no declared symbol founds no word, and that is a typed refusal naming the
    /// wholes rather than an empty return.
    #[test]
    fn material_carrying_no_declared_symbol_is_refused_by_type() {
        let numerals = vec![
            ("digits".to_owned(), "0123 4567 89".to_owned()),
            ("more-digits".to_owned(), "9876 5432 10".to_owned()),
        ];
        let refusal = intake(
            "word-runs",
            &word_runs(),
            &alphabet(),
            3,
            TEST_APERTURES,
            &numerals,
        )
        .expect_err("no declared letter appears in the material");
        let IntakeRefusal::NoFoundedWord { wholes } = refusal else {
            panic!("expected NoFoundedWord, got {refusal:?}");
        };
        assert_eq!(wholes, vec!["digits".to_owned(), "more-digits".to_owned()]);
    }

    /// A population no second whole witnessed commits nothing, and the intake refuses by type rather
    /// than returning a morphology whose committed population is silently empty.
    #[test]
    fn a_population_that_never_recurs_across_two_wholes_is_refused_by_type() {
        let single = vec![("only".to_owned(), FIRST.to_owned())];
        let refusal = intake(
            "word-runs",
            &word_runs(),
            &alphabet(),
            3,
            TEST_APERTURES,
            &single,
        )
        .expect_err("one whole cannot witness a recurrence across distinct wholes");
        let IntakeRefusal::NoCommittedStem { founded } = refusal else {
            panic!("expected NoCommittedStem, got {refusal:?}");
        };
        assert!(founded.contains(&"carrier".to_owned()), "{founded:?}");
    }

    /// A conditioner outside the declared shape is refused with the recovery's own obstruction
    /// carried, not approximated by the nearest structure that fits.
    #[test]
    fn a_conditioner_outside_the_declared_shape_carries_the_recovery_obstruction_forward() {
        let refusal = intake(
            "capped",
            &capped(),
            &SymbolAlphabet::from_chars(&['a', 'b']).expect("declared"),
            4,
            TEST_APERTURES,
            &corpus(),
        )
        .expect_err("a token-length cap is not an adjacency law");
        let IntakeRefusal::RecoveryObstructed { obstructions } = refusal else {
            panic!("expected RecoveryObstructed, got {refusal:?}");
        };
        assert!(
            matches!(
                obstructions.first(),
                Some(Obstruction::NoConformingTable { .. })
            ),
            "{obstructions:?}"
        );
    }

    // ---------------------------------------------------------------------------------------------
    // The seam: what the recovered conditioner founds
    // ---------------------------------------------------------------------------------------------

    /// **The identity claim.** A conditioner recovered from black-box testimony alone founds, on real
    /// prose, exactly the words the body's own reading founds — in order, whole by whole.
    #[test]
    fn the_recovered_conditioner_founds_exactly_the_words_the_bodys_own_reading_founds() {
        let carried = intake(
            "word-runs",
            &word_runs(),
            &alphabet(),
            3,
            TEST_APERTURES,
            &corpus(),
        )
        .expect("the conditioner is recoverable");
        let spelled = alphabet();
        let declared: BTreeSet<char> = carried
            .relations
            .alphabet
            .iter()
            .filter_map(|symbol| spelled.identity(*symbol)?.chars().next())
            .collect();

        for (whole, text) in corpus() {
            let native_words = expose(&whole, &text).words;
            let presented = present(&whole, &text, &declared);
            let recovered: Vec<String> = presented
                .runs
                .iter()
                .flat_map(|run| {
                    let word = spelled.spell(run).expect("a presented run is declared");
                    carried
                        .codec
                        .segment(&word)
                        .expect("declared symbols only")
                        .into_iter()
                        .map(|token| spelled.render(&token))
                        .collect::<Vec<_>>()
                })
                .collect();
            assert_eq!(
                recovered, native_words,
                "the recovered reading of {whole} departs from the native one"
            );
            assert!(
                native_words.len() > 20,
                "the material must be able to show a departure: {} words",
                native_words.len()
            );
        }

        // A different conditioner over the same alphabet does depart, so the agreement above is a
        // property of this conditioner and not of the comparison.
        let other = intake(
            "characters",
            &characters(),
            &alphabet(),
            3,
            TEST_APERTURES,
            &corpus(),
        )
        .expect("the conditioner is recoverable");
        let presented = present("first", FIRST, &declared);
        let spelled = alphabet();
        let split: Vec<String> = presented
            .runs
            .iter()
            .flat_map(|run| {
                let word = spelled.spell(run).expect("a presented run is declared");
                other
                    .codec
                    .segment(&word)
                    .expect("declared symbols only")
                    .into_iter()
                    .map(|token| spelled.render(&token))
                    .collect::<Vec<_>>()
            })
            .collect();
        assert_ne!(split, expose("first", FIRST).words);
    }

    /// The morphology founded through the seam agrees with the natively conditioned one on
    /// **everything any conduct path reads**, and differs exactly in the field none reads.
    #[test]
    fn the_carried_morphology_differs_from_the_native_one_only_in_the_lineage_nothing_reads() {
        let carried = intake(
            "word-runs",
            &word_runs(),
            &alphabet(),
            3,
            TEST_APERTURES,
            &corpus(),
        )
        .expect("the conditioner is recoverable")
        .morphology;
        let native = native();

        assert_eq!(
            carried.founded().len(),
            native.founded().len(),
            "the founded populations must have the same members"
        );
        for (recovered, own) in carried.founded().iter().zip(native.founded().iter()) {
            assert_eq!(recovered.stem, own.stem);
            assert_eq!(recovered.id, own.id);
            assert_eq!(recovered.parent, own.parent);
            assert_eq!(recovered.wholes, own.wholes);
            assert_eq!(recovered.standing(), own.standing());
        }
        assert_eq!(carried.committed_stems(), native.committed_stems());
        assert!(!carried.committed_stems().is_empty());

        // The one difference, and it is the one no conduct path reads.
        assert!(
            native
                .founded()
                .iter()
                .all(|stem| stem.foreign_lineage.is_empty()),
            "the native reading founds no foreign lineage"
        );
        let accounted = carried
            .founded()
            .iter()
            .find(|stem| stem.stem == "carrier")
            .expect("the corpus founds `carrier`");
        assert!(
            accounted
                .foreign_lineage
                .iter()
                .any(|entry| entry == "recovered classes aaaaaaa"),
            "{:?}",
            accounted.foreign_lineage
        );
        assert!(
            accounted
                .foreign_lineage
                .iter()
                .any(|entry| entry == "boundary(a,a) = Join"),
            "{:?}",
            accounted.foreign_lineage
        );
        assert!(
            accounted.foreign_lineage.iter().any(|entry| {
                // Two things the rotation changed, both honest. The pair is written in class
                // order, which is now declaration order rather than ASCII collation, so either
                // hand may come first. And a symbol is named by its IDENTITY, which is a string
                // and renders with double quotes -- a `char` rendered `'a'` and could never have
                // named a multi-character symbol at all.
                entry == r#"class " " apart from "a" by context ""^"""#
                    || entry == r#"class "a" apart from " " by context ""^"""#
            }),
            "{:?}",
            accounted.foreign_lineage
        );
        assert_ne!(
            carried, native,
            "the lineage is carried and is a difference"
        );
    }

    // ---------------------------------------------------------------------------------------------
    // The gauge, and the order in which its two returns may be read
    // ---------------------------------------------------------------------------------------------

    /// **The gauge acts.** Before any agreement is read as evidence, the instrument is shown
    /// returning a non-empty population on the same material and the same item population — with the
    /// shortest word of material that separates each pair, and the founded stem that saw it.
    #[test]
    fn the_body_tells_a_character_conditioner_from_its_own_reading_and_names_the_word() {
        let population = identifiers();
        let carried = intake(
            "characters",
            &characters(),
            &alphabet(),
            3,
            TEST_APERTURES,
            &corpus(),
        )
        .expect("the conditioner is recoverable");
        let native = native();

        let distinction = distinguish(
            &population,
            ("native", &native),
            ("characters", &carried.morphology),
        )
        .expect("the identifiers are ASCII");

        assert!(
            !distinction.indistinguishable(),
            "the gauge must act before agreement elsewhere may be read as evidence"
        );
        assert!(
            !distinction.witness_stems().is_empty(),
            "every separation must name the founded stem that saw it"
        );
        // Every exhibited pair carries either the word that separates it or the proof that none does.
        for exhibited in distinction
            .right_separates
            .iter()
            .chain(distinction.left_separates.iter())
        {
            assert_ne!(exhibited.left, exhibited.right);
            assert!(
                exhibited.witness_stem.is_some() || exhibited.distinguishing_word.is_some(),
                "{exhibited:?} exhibits neither a witness nor a word"
            );
        }
        // The two conditioners really do found different committed populations that reach this
        // material, so the difference is caused by the conditioning and not by the item population.
        assert!(
            !distinction.only_left_reaching.is_empty(),
            "the native reading founds stems the character reading does not"
        );
    }

    /// A syllabic conditioner — a wholly different architecture, three classes with one dropped — is
    /// also told apart, so the instrument is not reporting one accident.
    #[test]
    fn the_body_tells_a_syllabic_conditioner_apart_as_well() {
        let population = identifiers();
        let carried = intake(
            "syllables",
            &syllables(),
            &alphabet(),
            3,
            TEST_APERTURES,
            &corpus(),
        )
        .expect("the conditioner is recoverable");
        assert_eq!(
            carried.relations.classes.len(),
            3,
            "{:?}",
            carried.relations.classes
        );
        assert_eq!(
            carried
                .relations
                .classes
                .iter()
                .map(spell_class)
                .find(|block| block.contains(&'a'))
                .expect("the class carrying a vowel is recovered"),
            BTreeSet::from(['a', 'e', 'i', 'o', 'u']),
            "the vowel class is recovered from testimony, never declared"
        );

        // **The adjacency relation is ORDERED, and this is the material that can show it.** The
        // word-runs conditioner's only `Join` is a class with itself, so its table is symmetric and
        // a transposed report of it is invisible; here a consonant carries the vowel after it while
        // a vowel breaks before a consonant, so the transpose is a different relation. The reported
        // relation is then checked against the runner that segments with it, not only against
        // itself. Without these four assertions transposing the reported adjacency survived the
        // whole suite.
        let boundary = |left: char, right: char| {
            carried
                .relations
                .adjacency
                .iter()
                .find(|entry| (entry.left, entry.right) == (sym(left), sym(right)))
                .map(|entry| entry.boundary)
        };
        assert_eq!(boundary('b', 'a'), Some(Boundary::Join));
        assert_eq!(boundary('a', 'b'), Some(Boundary::Cut));
        for entry in &carried.relations.adjacency {
            assert_eq!(
                Some(entry.boundary),
                carried.codec.boundary_between(entry.left, entry.right),
                "the reported relation departs from the structure that segments with it"
            );
        }
        assert_eq!(
            carried
                .codec
                .segment(&alphabet().spell("carrier").expect("declared"))
                .unwrap()
                .iter()
                .map(|token| alphabet().render(token))
                .collect::<Vec<_>>(),
            vec!["ca".to_owned(), "rrie".to_owned(), "r".to_owned()],
            "the ordered relation is what makes this segmentation, not its transpose"
        );

        let distinction = distinguish(
            &population,
            ("native", &native()),
            ("syllables", &carried.morphology),
        )
        .expect("the identifiers are ASCII");
        assert!(!distinction.indistinguishable());
        assert!(!distinction.witness_stems().is_empty());
    }

    /// **The agreement, read only after the gauge has been shown to act.** The body's reading of the
    /// deposited identifiers cannot tell the recovered word-runs conditioner from its own.
    #[test]
    fn the_body_cannot_tell_the_recovered_word_runs_conditioner_from_its_own_reading() {
        let population = identifiers();
        let native = native();

        // The gauge acts on this exact material and this exact item population.
        let acting = distinguish(
            &population,
            ("native", &native),
            (
                "characters",
                &intake(
                    "characters",
                    &characters(),
                    &alphabet(),
                    3,
                    TEST_APERTURES,
                    &corpus(),
                )
                .expect("recoverable")
                .morphology,
            ),
        )
        .expect("the identifiers are ASCII");
        assert!(
            !acting.indistinguishable(),
            "a gauge whose group acts trivially is not a gauge"
        );

        // Only now is the empty return admissible as evidence.
        let carried = intake(
            "word-runs",
            &word_runs(),
            &alphabet(),
            3,
            TEST_APERTURES,
            &corpus(),
        )
        .expect("recoverable");
        let agreement = distinguish(
            &population,
            ("native", &native),
            ("word-runs", &carried.morphology),
        )
        .expect("the identifiers are ASCII");
        assert!(
            agreement.indistinguishable(),
            "right {:?} left {:?}",
            agreement.right_separates,
            agreement.left_separates
        );
        assert!(agreement.only_left_reaching.is_empty());
        assert!(agreement.only_right_reaching.is_empty());
    }

    /// **The instrument is a reading, not a set difference.** Two morphologies whose committed
    /// populations differ by a named member are indistinguishable when that member reaches nothing,
    /// and distinguishable when it does — so an empty return is a statement about what the material
    /// exercises rather than about which words were founded.
    ///
    /// This is what keeps [`the_body_cannot_tell_the_recovered_word_runs_conditioner_from_its_own_reading`]
    /// from resting on a tautology. That test's two morphologies commit the *same* stems, so its
    /// empty return could not have come out otherwise; the measurement there is upstream, in the
    /// words the recovered conditioner cut out of the material. Here the populations really differ
    /// and the instrument still decides, both ways, by removing structure.
    #[test]
    fn the_distinction_answers_to_a_structural_removal_and_not_to_a_population_difference() {
        let population = identifiers();
        let native = native();
        let reaching: BTreeSet<String> = MorphemicIncidence::over(&population, &native)
            .expect("the identifiers are ASCII")
            .firing()
            .into_iter()
            .map(|firing| firing.stem)
            .collect();
        assert!(
            !reaching.is_empty(),
            "no committed stem reaches this material"
        );

        // A committed stem the material never exercises. Removing it is a real difference in the
        // founded population and no difference at all in the reading.
        let unreached = native
            .committed_stems()
            .into_iter()
            .find(|stem| !reaching.contains(*stem))
            .expect("some committed stem reaches nothing here")
            .to_owned();
        let without = native
            .without_stem(&unreached)
            .expect("the stem was founded");
        assert_ne!(without.committed_stems(), native.committed_stems());
        let quiet = distinguish(
            &population,
            ("native", &native),
            ("native-less-a-stem-that-reaches-nothing", &without),
        )
        .expect("the identifiers are ASCII");
        assert!(
            quiet.indistinguishable(),
            "removing {unreached:?} moved the reading: {:?} {:?}",
            quiet.right_separates,
            quiet.left_separates
        );
        assert_eq!(
            quiet.only_left_reaching,
            vec![],
            "a stem that reaches nothing must not be reported as reaching something"
        );

        // And a stem the material does exercise, taken in canonical order rather than chosen: the
        // first whose removal moves the reading, with the word that shows it.
        let moved = reaching
            .iter()
            .find_map(|stem| {
                let without = native.without_stem(stem)?;
                let distinction = distinguish(
                    &population,
                    ("native", &native),
                    ("native-less-a-reaching-stem", &without),
                )
                .ok()?;
                (!distinction.indistinguishable()).then_some((stem.clone(), distinction))
            })
            .expect("removing some reaching stem moves the reading");
        let (stem, distinction) = moved;
        assert!(
            !distinction.only_left_reaching.is_empty(),
            "removing {stem:?} must remove a stem that reached this material"
        );
        assert!(
            !distinction.witness_stems().is_empty()
                || !distinction.distinguishing_words().is_empty(),
            "removing {stem:?} moved the reading without exhibiting what shows it"
        );
    }

    /// The two conditioners are distinct **as codecs**, exactly and over all inputs, and the input
    /// that separates them is named. Without this the agreement above could be two names for one
    /// object.
    #[test]
    fn the_two_conditioners_are_separated_as_codecs_by_a_named_input() {
        let runs = intake(
            "word-runs",
            &word_runs(),
            &alphabet(),
            3,
            TEST_APERTURES,
            &corpus(),
        )
        .expect("recoverable");
        let chars = intake(
            "characters",
            &characters(),
            &alphabet(),
            3,
            TEST_APERTURES,
            &corpus(),
        )
        .expect("recoverable");

        assert_eq!(runs.codec.classes, chars.codec.classes);
        assert_eq!(runs.codec.emission, chars.codec.emission);
        let separating = runs
            .codec
            .shortest_separating_input(&chars.codec)
            .expect("the two codecs share their classes and emission")
            .expect("some input separates them");
        assert_eq!(separating.len(), 2, "returned {separating:?}");
        assert_ne!(
            runs.codec.segment(&separating).unwrap(),
            chars.codec.segment(&separating).unwrap()
        );
        assert_eq!(
            spelled(&runs.codec.segment(&word("aa")).unwrap()),
            vec!["aa".to_owned()]
        );
        assert_eq!(
            spelled(&chars.codec.segment(&word("aa")).unwrap()),
            vec!["a".to_owned(), "a".to_owned()]
        );
    }

    // ---------------------------------------------------------------------------------------------
    // The production: the seam really is the causal path
    // ---------------------------------------------------------------------------------------------

    /// A morphology carried across the seam drives the derivation the natively conditioned one
    /// drives, and a different conditioner drives a different one. The reading is not the only thing
    /// the conditioning reaches.
    #[test]
    fn a_carried_morphology_drives_the_production_the_native_one_drives() {
        let mut body = ConditionedBody::mount(deposit()).expect("the deposit declares a theorem");
        let query = DerivationQuery::reaching(
            body.standing_statements()
                .iter()
                .next()
                .expect("the deposit reached a statement"),
        );

        // Unconditioned: no stem can bridge two identifiers, so nothing is produced.
        assert!(body.derive(&query).expect("ASCII identifiers").is_empty());

        body.carry_morphology(
            intake(
                "word-runs",
                &word_runs(),
                &alphabet(),
                3,
                TEST_APERTURES,
                &corpus(),
            )
            .expect("recoverable")
            .morphology,
        );
        let carried: Vec<String> = body
            .derive(&query)
            .expect("ASCII identifiers")
            .into_iter()
            .map(|passage| passage.name)
            .collect();
        assert!(
            !carried.is_empty(),
            "the carried morphology produces nothing"
        );

        let own: Vec<String> = derive(&body.standing_derivations(), &native(), &query)
            .expect("ASCII identifiers")
            .into_iter()
            .map(|passage| passage.name)
            .collect();
        assert_eq!(carried, own, "the seam must not change the production");

        body.carry_morphology(
            intake(
                "characters",
                &characters(),
                &alphabet(),
                3,
                TEST_APERTURES,
                &corpus(),
            )
            .expect("recoverable")
            .morphology,
        );
        let elsewhere: Vec<String> = body
            .derive(&query)
            .expect("ASCII identifiers")
            .into_iter()
            .map(|passage| passage.name)
            .collect();
        assert!(!elsewhere.is_empty());
        assert_ne!(
            elsewhere, own,
            "a different conditioner must reach a different production"
        );
    }

    // ---------------------------------------------------------------------------------------------
    // Presentation, cost, and determinism
    // ---------------------------------------------------------------------------------------------

    /// The presentation names what the declared alphabet cannot carry, per whole, and never projects
    /// it onto a symbol the conditioner never testified about.
    #[test]
    fn the_presentation_names_the_symbols_the_alphabet_does_not_carry() {
        let declared: BTreeSet<char> = declared_characters().into_iter().collect();
        let presented = present("mixed", "carry 42, chart; \u{3bb} exact", &declared);
        assert_eq!(
            presented.undeclared,
            BTreeSet::from(['4', '2', ',', ';', '\u{3bb}'])
        );
        assert_eq!(
            presented.runs,
            vec![
                "carry ".to_owned(),
                " chart".to_owned(),
                " ".to_owned(),
                " exact".to_owned(),
            ]
        );

        let carried = intake(
            "word-runs",
            &word_runs(),
            &alphabet(),
            3,
            TEST_APERTURES,
            &corpus(),
        )
        .expect("recoverable");
        assert!(
            carried
                .retained
                .undeclared
                .get("first")
                .expect("the prose carries an apostrophe and a semicolon")
                .contains(&'\''),
            "{:?}",
            carried.retained.undeclared
        );
    }

    /// The recovered structure runs on real material longer than anything the family reached, and
    /// agrees with the opaque conditioner there. The relations are a structure, not retained
    /// testimony.
    #[test]
    fn the_recovered_structure_conforms_with_the_conditioner_on_held_out_real_runs() {
        let carried = intake(
            "word-runs",
            &word_runs(),
            &alphabet(),
            3,
            TEST_APERTURES,
            &corpus(),
        )
        .expect("recoverable");
        let spelled = alphabet();
        let declared: BTreeSet<char> = carried
            .relations
            .alphabet
            .iter()
            .filter_map(|symbol| spelled.identity(*symbol)?.chars().next())
            .collect();
        let presented = present("second", SECOND, &declared);
        let held_out: Vec<&str> = presented
            .runs
            .iter()
            .map(String::as_str)
            .filter(|run| run.chars().count() > carried.relations.radius)
            .collect();
        assert!(!held_out.is_empty());
        // The held-out material must be able to vary the property under test: a population that
        // returned one token per run would conform under almost any adjacency table.
        let widest = held_out
            .iter()
            .map(|run| {
                carried
                    .codec
                    .segment(&word(run))
                    .expect("declared symbols only")
                    .len()
            })
            .max()
            .expect("the population is not empty");
        assert!(
            widest >= 12,
            "the held-out material returns at most {widest} tokens"
        );

        let held_out_words: Vec<Vec<Symbol>> = held_out.iter().map(|run| word(run)).collect();
        let conformance = conform(&carried.codec, &word_runs(), &held_out_words);
        assert!(
            conformance.is_exact(),
            "disagreements {:?} refusals {:?}",
            conformance.disagreements,
            conformance.refusals
        );
        assert_eq!(conformance.examined, held_out.len() as u64);
    }

    /// The cost is stated rather than optimised away, and a committed stem really is one that two
    /// distinct wholes witnessed.
    #[test]
    fn the_intake_states_its_cost_and_commits_only_what_recurred_across_wholes() {
        let carried = intake(
            "word-runs",
            &word_runs(),
            &alphabet(),
            3,
            TEST_APERTURES,
            &corpus(),
        )
        .expect("recoverable");
        assert_eq!(
            carried.relations.work.declared_family_words,
            29 + 29 * 29 + 29 * 29 * 29
        );
        assert_eq!(
            carried.relations.work.target_calls,
            carried.relations.work.declared_family_words
        );
        assert!(carried.relations.work.contexts_examined > 0);

        for stem in carried.morphology.founded() {
            assert_eq!(
                stem.standing() == StemStanding::Committed,
                stem.wholes.len() >= 2,
                "{stem:?}"
            );
        }
        let committed = carried.morphology.committed_stems();
        assert!(committed.contains(&"carrier"), "{committed:?}");
        assert!(
            !committed.contains(&"drop"),
            "`drop` appears in one whole only"
        );
    }

    /// The same declaration returns the same intake. Nothing here is ordered by an iteration
    /// accident.
    #[test]
    fn the_intake_is_deterministic() {
        let first = intake(
            "word-runs",
            &word_runs(),
            &alphabet(),
            3,
            TEST_APERTURES,
            &corpus(),
        )
        .expect("ok");
        let second = intake(
            "word-runs",
            &word_runs(),
            &alphabet(),
            3,
            TEST_APERTURES,
            &corpus(),
        )
        .expect("ok");
        assert_eq!(first, second);

        let population = identifiers();
        let one = distinguish(
            &population,
            ("native", &native()),
            ("word-runs", &first.morphology),
        )
        .expect("ASCII");
        let two = distinguish(
            &population,
            ("native", &native()),
            ("word-runs", &second.morphology),
        )
        .expect("ASCII");
        assert_eq!(one, two);
    }
}

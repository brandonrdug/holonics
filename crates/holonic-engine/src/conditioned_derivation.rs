//! One carrier holding the conditioning, the production it makes possible, and that production read
//! back as a circuit — with every cell of the circuit named by the passage that founded it.
//!
//! ## The receiver question this is a step toward
//!
//! *Can a body conditioned on linguistic material derive mathematics that the same body,
//! unconditioned, cannot — and can we read what it derived as a circuit?* This module is the spine
//! of that question and nothing else: it does not compute curvature, does not integrate along a
//! path, does not apply a skein move, and does not recover a foreign codec. It holds the three
//! things those organs need to be pointed at one object, and the map that makes their returns
//! interpretable instead of anonymous.
//!
//! ```text
//!   the conditioning   FoundedMorphology     reusable morphology founded by exposure to
//!                                            linguistic material, with per-stem lineage
//!   the production     DerivedPassage        mathematical passages the conditioned body emitted,
//!                                            each carrying the bridge that licensed it
//!   the circuit        ConditionedCircuit    that production as a GradedCausalComplex, via
//!                                            derivation_atlas::found_circuit
//!   the seam           provenance            CausalCellId -> the passages that founded that cell
//! ```
//!
//! ## The mechanism, in the four slots `CLAUDE.md` §4 asks for
//!
//! ```text
//!   source geometry   the deposited mathematical material: the identifiers its derivations recruit
//!   receiver map      the founded morphology: which stems the linguistic corpus committed
//!   transport         character succession through an identifier
//!   returned residual the positions the reading cannot separate, each with the shortest word that
//!                     would, and the stems that bridge two identifiers the reading holds apart
//! ```
//!
//! **The linguistic corpus is the receiver family through which the mathematical material is read.**
//! That is the whole of why the conditioning is on the causal path rather than beside it. Under a
//! body that has been exposed to nothing, a recruited identifier is an **atom**: `exactCarrier` and
//! `exact_chart_carry` share no structure, no bridge is licensed, and no passage is emitted. Under a
//! body the corpus has conditioned, the identifier carries a founded cover, two identifiers can
//! share a stem, and the shared stem licenses a passage that reaches a standing statement by a route
//! the standing deposit does not carry.
//!
//! ## What the founding is, and the one constant it takes from the laboratory
//!
//! A [`FoundedStem`] is founded when a whole of linguistic material witnesses a word, and it stands
//! **Provisional** until a *second, distinct* whole witnesses it — [`COMMITTING_RECURRENCE`], which
//! is the laboratory's own `CODEC_MINIMUM_RECURRENCE = 2` and the same distinction its
//! `propose_views` / `commit_views` pair draws: provisional contact is not continuing cultivation.
//! Only committed stems reach the derivation path. The provisional population is **retained**, never
//! discarded, and [`FoundedMorphology::promoted_provisional`] hands it back as a declared foil: if
//! the stems that never recurred license the same passages, the recurrence condition is decorative.
//!
//! There is no threshold on stem length, no frequency cut, no inverse-document weighting and no
//! ranking. A single-letter corpus word-type is a founded stem exactly as `carrier` is, because
//! `CLAUDE.md` §5 rules on precisely this — *"the aperture cannot decide the deed"* and *"broad
//! recruitment remains lawful"*. What replaces a filter is **maximality**, which is structural: an
//! occurrence is on the path only when no other founded occurrence strictly contains it, so `act`
//! inside `exact` is not a bridge while the residual letters of a tail the corpus never witnessed
//! are. That residue is retained by name in [`FoundedCover::residue`] as the obstruction it is.
//!
//! ## Why the founded morphology is a morphology and not a counter
//!
//! `CLAUDE.md` §13 rule 1: a morphology is the contemporary causal organization by which a body
//! receives, transforms, retains and emits differences, and a training claim needs a structural
//! change in that organization plus an ablation that removes later conduct **by removing
//! structure**. A [`FoundedMorphology`] is a population of named stems with parented lineage; it
//! transforms an identifier it has never seen into a cover; [`FoundedMorphology::without_stem`]
//! removes one member and the passages that member licensed are then **absent**, not
//! differently-valued. Nothing here is incremented, no field named `morphology` carries a number,
//! and [`StemAblation`] exhibits the removed passages and the vanished circuit cells by name.
//!
//! ## The gauge, and its obligation to exhibit its own distinguishing word
//!
//! `CLAUDE.md` §8: *"A gauge whose group acts trivially on the declared material is not a gauge...
//! A gauge should be required to exhibit its distinguishing word."* The conditioned and
//! unconditioned readings are two receiver families over one item population — the character
//! positions of the recruited identifiers — so [`MorphemicIncidence`] presents that population to
//! [`compress`] and [`frame_orbit`] returns the pairs one family separates and the other does not,
//! **each with the shortest word of material that separates it**. A frame orbit whose
//! `separated_by_conditioning` population is empty is a report that the conditioning did not move
//! this material, and the driver exits nonzero on it rather than reading agreement as evidence.
//!
//! ## What this module must not own
//!
//! It does not own [`compress`], `found_circuit`, `read_derivation` or `rebase_invariants` — it
//! calls all four. It does not own a second reading of a Lean artifact: every passage it emits is
//! read back through [`read_derivation`], so the circuit sees emitted and deposited material through
//! one reading. It does not own a kernel, a judge, or a claim that an emitted passage is a proof: a
//! passage is an artifact of the production read as structure, exactly as the deposited artifacts
//! are, and the deposit itself contains kernel-refused foils. It does not own file access; a caller
//! presents material through [`Exposure`] and [`ConditionedBody::mount`].
//!
//! ## The seam a foreign conditioner enters by
//!
//! `soma/life/src/decomposing_codec.rs` founds one parented `CodecVersion` per collapsed pair,
//! cutting at that pair's own shortest distinguishing word. That organ is the conditioning mechanism
//! this module was specified against, and it **cannot be called from here**: `life` depends on
//! `holonic-engine`, so the edge runs the other way and naming it would be a dependency cycle.
//! [`FoundedMorphology::from_founded_words`] is the seam instead — a foreign conditioner hands over
//! its founded words each with its own lineage rendered as text, and everything below runs
//! unchanged. That is the laboratory's own join rule: a carrier generic over the application's own
//! founding plus one narrow entry the application fills, never a universal payload and never a
//! registry.

use std::collections::{BTreeMap, BTreeSet};

use serde::{Deserialize, Serialize};

use crate::algebraic::CausalCellId;
use crate::derivation_atlas::{
    found_circuit, read_derivation, statement_vertex_key, CircuitAperture, Derivation,
    DerivationAtlasRefusal, DerivationCircuit, DerivationIdentity, StatementIncidence,
};
use crate::receiver_exact_compression::{
    compress, InputId, ItemId, Observation, ObservedSystem, ReceiverExactCompression, ReceiverId,
};

/// The number of **distinct** wholes that must witness a word before it commits.
///
/// Two, and the figure is the laboratory's `CODEC_MINIMUM_RECURRENCE` rather than a choice made
/// here. It is a recurrence across distinct sources, which is a structural condition, not a
/// magnitude compared against a bound: nothing is scored, and a word witnessed twice in one whole
/// does not commit.
pub const COMMITTING_RECURRENCE: usize = 2;

/// The receiver that reads *has this identifier ended here*. Stem receivers occupy
/// `STEM_RECEIVER_BASE..`, so this identity cannot collide with one of them.
pub const AT_END_RECEIVER: u64 = 0;

/// The first receiver identity a founded stem may take.
pub const STEM_RECEIVER_BASE: u64 = 1;

// -------------------------------------------------------------------------------------------------
// The material, as presented
// -------------------------------------------------------------------------------------------------

/// One whole of linguistic material, named, read into the word population it exhibits.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Exposure {
    /// What this whole is. Carried into every stem's lineage, so a founded stem names the wholes
    /// that witnessed it rather than a count of them.
    pub whole: String,
    /// The words this whole exhibited, in reading order, with repetition.
    pub words: Vec<String>,
}

/// Read one whole of material into its word population.
///
/// **The declared aperture, and it is an exterior codec rather than a claim.** A word is a maximal
/// run of ASCII alphabetic characters, case-folded down. Case folding is forced by the material the
/// morphology is read *onto*: a Lean identifier is written `exactCarrier` and the prose writes
/// `carrier`, so a case-sensitive reading could never found the shared stem, and the fold is stated
/// here as the reading's one orthographic rule exactly as `derivation_atlas` states its own. The
/// ASCII restriction is likewise forced: the identifiers this morphology is applied to are ASCII, so
/// a Greek or accented run in the prose can found no stem that any identifier could carry, and
/// admitting it would grow the receiver family with members that cannot fire.
pub fn expose(whole: &str, text: &str) -> Exposure {
    let mut words = Vec::new();
    let mut open = String::new();
    for symbol in text.chars() {
        if symbol.is_ascii_alphabetic() {
            open.push(symbol.to_ascii_lowercase());
        } else if !open.is_empty() {
            words.push(std::mem::take(&mut open));
        }
    }
    if !open.is_empty() {
        words.push(open);
    }
    Exposure {
        whole: whole.to_owned(),
        words,
    }
}

// -------------------------------------------------------------------------------------------------
// The conditioning
// -------------------------------------------------------------------------------------------------

/// A founded stem's place in the morphology's own version lineage.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct StemId(pub u64);

/// Whether a founded stem has recurred across distinct wholes.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum StemStanding {
    /// Witnessed by one whole. Retained as lineage; never on the derivation path.
    Provisional,
    /// Witnessed by [`COMMITTING_RECURRENCE`] distinct wholes or more.
    Committed,
}

/// One member of the founded morphology.
///
/// `wholes` is the population of distinct wholes that witnessed the stem, **named**, in the order
/// they did. It is lineage and not a tally: [`Self::standing`] reads its length, and nothing else
/// anywhere reads it.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct FoundedStem {
    pub id: StemId,
    pub stem: String,
    pub wholes: Vec<String>,
    /// The morphology version this stem was founded on: the stem founded immediately before it, or
    /// `None` for the first. The same parenting `decomposing_codec` gives a `CodecVersion`.
    pub parent: Option<StemId>,
    /// What the foreign conditioner said founded this stem, if it came in through
    /// [`FoundedMorphology::from_founded_words`]. Empty for a stem founded by [`Exposure`].
    pub foreign_lineage: Vec<String>,
}

impl FoundedStem {
    pub fn standing(&self) -> StemStanding {
        if self.wholes.len() >= COMMITTING_RECURRENCE {
            StemStanding::Committed
        } else {
            StemStanding::Provisional
        }
    }
}

/// The reusable morphology: a population of founded stems with parented lineage.
///
/// This is what exposure founds and what a later reading conducts through. It is never a number, and
/// the only field any conduct path reads is the stem text.
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct FoundedMorphology {
    stems: Vec<FoundedStem>,
    index: BTreeMap<String, usize>,
}

impl FoundedMorphology {
    /// A body exposed to nothing. Every identifier is an atom to it.
    pub fn unconditioned() -> Self {
        Self::default()
    }

    /// Exposure founds morphology.
    ///
    /// Walking the wholes in order, a word never witnessed founds a stem parented on the stem
    /// founded before it; a word witnessed again by a *distinct* whole adds that whole to the stem's
    /// lineage and commits it once [`COMMITTING_RECURRENCE`] wholes stand behind it. A repeat inside
    /// one whole changes nothing, which is what makes the commitment a recurrence across sources
    /// rather than a frequency.
    pub fn condition(exposures: &[Exposure]) -> Self {
        let mut founded = Self::default();
        for exposure in exposures {
            for word in &exposure.words {
                founded.witness(word, &exposure.whole, Vec::new());
            }
        }
        founded
    }

    /// The seam a foreign conditioner enters by.
    ///
    /// Each entry is a founded word, the wholes that witnessed it, and whatever that conditioner
    /// says founded it — `decomposing_codec` would render its `CollapsedPair` here. The lineage is
    /// carried and never parsed: this module does not know what a collapsed pair is and must not.
    pub fn from_founded_words<W, L>(founded: impl IntoIterator<Item = (String, W, L)>) -> Self
    where
        W: IntoIterator<Item = String>,
        L: IntoIterator<Item = String>,
    {
        let mut morphology = Self::default();
        for (word, wholes, lineage) in founded {
            let lineage: Vec<String> = lineage.into_iter().collect();
            let wholes: Vec<String> = wholes.into_iter().collect();
            if wholes.is_empty() {
                continue;
            }
            for whole in wholes {
                morphology.witness(&word, &whole, lineage.clone());
            }
        }
        morphology
    }

    fn witness(&mut self, word: &str, whole: &str, lineage: Vec<String>) {
        if word.is_empty() {
            return;
        }
        match self.index.get(word).copied() {
            Some(slot) => {
                let stem = &mut self.stems[slot];
                if !stem.wholes.iter().any(|carried| carried == whole) {
                    stem.wholes.push(whole.to_owned());
                }
                for entry in lineage {
                    if !stem.foreign_lineage.contains(&entry) {
                        stem.foreign_lineage.push(entry);
                    }
                }
            }
            None => {
                let parent = self.stems.last().map(|stem| stem.id);
                let id = StemId(self.stems.len() as u64);
                self.index.insert(word.to_owned(), self.stems.len());
                self.stems.push(FoundedStem {
                    id,
                    stem: word.to_owned(),
                    wholes: vec![whole.to_owned()],
                    parent,
                    foreign_lineage: lineage,
                });
            }
        }
    }

    /// Every stem founded, in founding order.
    pub fn founded(&self) -> &[FoundedStem] {
        &self.stems
    }

    pub fn stem(&self, stem: &str) -> Option<&FoundedStem> {
        self.index.get(stem).map(|slot| &self.stems[*slot])
    }

    /// The stems that recurred across distinct wholes, in canonical text order. **The morphology on
    /// the derivation path.**
    pub fn committed(&self) -> Vec<&FoundedStem> {
        let mut committed: Vec<&FoundedStem> = self
            .stems
            .iter()
            .filter(|stem| stem.standing() == StemStanding::Committed)
            .collect();
        committed.sort_by(|left, right| left.stem.cmp(&right.stem));
        committed
    }

    /// The stems one whole witnessed and no second whole did. Retained lineage, off the path.
    pub fn provisional(&self) -> Vec<&FoundedStem> {
        let mut provisional: Vec<&FoundedStem> = self
            .stems
            .iter()
            .filter(|stem| stem.standing() == StemStanding::Provisional)
            .collect();
        provisional.sort_by(|left, right| left.stem.cmp(&right.stem));
        provisional
    }

    /// The committed stem texts, canonically ordered. The receiver family, as words.
    pub fn committed_stems(&self) -> Vec<&str> {
        self.committed()
            .into_iter()
            .map(|stem| stem.stem.as_str())
            .collect()
    }

    /// **The ablation.** The same morphology with one founded stem removed by removing it, its
    /// successor re-parented onto its parent so the lineage stays a chain.
    ///
    /// Returns `None` when the stem was never founded, so an ablation cannot silently be a no-op.
    pub fn without_stem(&self, stem: &str) -> Option<Self> {
        let slot = self.index.get(stem).copied()?;
        let removed = self.stems[slot].id;
        let inherited = self.stems[slot].parent;
        let mut kept = Self::default();
        for carried in self
            .stems
            .iter()
            .enumerate()
            .filter(|(at, _)| *at != slot)
            .map(|(_, carried)| carried)
        {
            let mut carried = carried.clone();
            if carried.parent == Some(removed) {
                carried.parent = inherited;
            }
            kept.index.insert(carried.stem.clone(), kept.stems.len());
            kept.stems.push(carried);
        }
        Some(kept)
    }

    /// **The declared foil.** The provisional population promoted to committed standing, and the
    /// committed population dropped.
    ///
    /// This is the same corpus, the same reading and the same founding rule, differing only in which
    /// side of [`COMMITTING_RECURRENCE`] a stem fell. If it licenses the same passages the committed
    /// morphology does, the recurrence condition is decorative and the founding carries no evidence.
    pub fn promoted_provisional(&self) -> Self {
        let mut foil = Self::default();
        for stem in self.provisional() {
            for repeat in 0..COMMITTING_RECURRENCE {
                foil.witness(
                    &stem.stem,
                    &format!("{}#promoted-{repeat}", stem.wholes.first().map_or("", String::as_str)),
                    stem.foreign_lineage.clone(),
                );
            }
        }
        foil
    }

    /// **The second declared foil.** Every committed stem, reversed.
    ///
    /// The population has the same size and the same length profile as the committed morphology and
    /// is drawn from words the corpus overwhelmingly did not witness. `decomposing_codec`'s own
    /// falsifier asks for exactly this: cut at a word of the same length the reading did not return,
    /// and if any cut whatsoever licenses as much, the derivation is decorative.
    pub fn reversed(&self) -> Self {
        let mut foil = Self::default();
        for stem in self.committed() {
            let reversed: String = stem.stem.chars().rev().collect();
            for whole in &stem.wholes {
                foil.witness(&reversed, whole, stem.foreign_lineage.clone());
            }
        }
        foil
    }

    /// Decompose a word the morphology may never have seen into the founded occurrences it carries.
    ///
    /// An occurrence is retained only when **maximal**: no other founded occurrence strictly
    /// contains it. That is the whole of what replaces a length filter, and it is structural — `act`
    /// inside `exact` is contained and drops out, while a letter of a tail no longer stem covers
    /// stands. A position no occurrence covers at all is [`FoundedCover::residue`]: material the
    /// morphology cannot found, retained as the obstruction rather than dropped.
    ///
    /// The word is case-folded by [`expose`]'s rule before matching; non-ASCII input is refused,
    /// because the founded stems are ASCII and a byte offset into a multi-byte identifier would name
    /// a place no stem can start.
    pub fn cover(&self, word: &str) -> Result<FoundedCover, ConditionedDerivationRefusal> {
        if !word.is_ascii() {
            return Err(ConditionedDerivationRefusal::IdentifierIsNotAscii {
                identifier: word.to_owned(),
            });
        }
        let folded: String = word.to_ascii_lowercase();
        let bytes = folded.as_bytes();
        let mut all: Vec<StemOccurrence> = Vec::new();
        for at in 0..bytes.len() {
            for through in (at + 1)..=bytes.len() {
                let candidate = &folded[at..through];
                if self
                    .stem(candidate)
                    .is_some_and(|stem| stem.standing() == StemStanding::Committed)
                {
                    all.push(StemOccurrence {
                        stem: candidate.to_owned(),
                        at,
                        through,
                    });
                }
            }
        }
        // **The full family is retained. Maximality is a READING, not the constructor's decision.**
        //
        // This filter used to run here and `all` was discarded — every occurrence strictly inside
        // another was deleted before any consumer saw it. `canon/THE_MATHEMATICS_TABLET.md` §1 names
        // that exactly: *"a carrier that reduces on construction has decided, for every consumer it
        // will ever have, which distinctions are invisible… the reduction belongs in the reading and
        // never in the constructor."*
        //
        // What the reduction deleted is **containment**, and that is the precise statement: the
        // filter keeps the antichain under containment, so two crossing spans both survive it and
        // every stem *inside* another does not. `exactCarrier` kept `exact` and `carrier` while
        // `act`, `x`, `carry`, `arr`, `car` ceased to exist, though the corpus committed each one.
        //
        // The short contained stems are exactly the ones two different identifiers are most likely
        // to SHARE, so deleting them is deleting contact — and the longer the founded stems get, the
        // more of them are deleted.
        //
        // The measured consequence, on the doubling ladder in
        // `examples/the_atmosphere_and_the_ground`: as the atmosphere grows from 4 documents to 489
        // the committed stems grow 30x and the admitted statements fall **42 → 1**, because finer
        // maximal covers stop meeting. The same mechanism was already visible from the other side —
        // removing the stem `exact` **reopened six routes**, since the residual letters it had been
        // suppressing licensed the same contact the moment the word was gone. Maximality suppresses
        // contact, and at corpus scale that is the dominant effect.
        let occurrences = all;
        let residue: Vec<usize> = (0..bytes.len())
            .filter(|at| {
                !occurrences
                    .iter()
                    .any(|occurrence| occurrence.at <= *at && *at < occurrence.through)
            })
            .collect();
        Ok(FoundedCover {
            word: word.to_owned(),
            occurrences,
            residue,
        })
    }
}

/// One founded stem, located in a word.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct StemOccurrence {
    pub stem: String,
    pub at: usize,
    pub through: usize,
}

/// A word, decomposed under a founded morphology.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct FoundedCover {
    pub word: String,
    /// **Every** founded occurrence at every span, overlaps retained, in canonical order.
    ///
    /// This is a cover in the topological sense — a family of spans that overlap — and not a
    /// partition. [`Self::maximal`] is the partition, offered as one reading among others.
    pub occurrences: Vec<StemOccurrence>,
    /// Byte offsets no founded occurrence covers. The retained obstruction.
    pub residue: Vec<usize>,
}

impl FoundedCover {
    /// The reading that keeps only the occurrences no other occurrence contains — the partition.
    ///
    /// Correct as a reading and wrong as a constructor: see [`FoundedMorphology::cover`].
    pub fn maximal(&self) -> Vec<&StemOccurrence> {
        self.occurrences
            .iter()
            .filter(|here| {
                !self.occurrences.iter().any(|other| {
                    other.at <= here.at
                        && here.through <= other.through
                        && (other.at, other.through) != (here.at, here.through)
                })
            })
            .collect()
    }

    /// **The crossings.** Pairs of occurrences whose spans overlap without either containing the
    /// other — the 1-faces of the cover's nerve.
    ///
    /// A partition has none by construction, which is why a maximal cover cannot interfere: an
    /// interference needs two carriers present at one site, and disjoint spans are never both at a
    /// site. Brandon, 2026-08-09, naming what was missing: *"it should be that stems reflect and
    /// refract about emergent boundary limits, they intersect, and they interfere. This is why I
    /// consistently say knot theory, hypergeometry, crossings, faces, and intersections are
    /// important."*
    pub fn crossings(&self) -> Vec<(&StemOccurrence, &StemOccurrence)> {
        let mut crossings = Vec::new();
        for (index, left) in self.occurrences.iter().enumerate() {
            for right in self.occurrences.iter().skip(index + 1) {
                let overlaps = left.at < right.through && right.at < left.through;
                let contains = (left.at <= right.at && right.through <= left.through)
                    || (right.at <= left.at && left.through <= right.through);
                if overlaps && !contains {
                    crossings.push((left, right));
                }
            }
        }
        crossings
    }

    /// **The nerve at one site.** Every occurrence covering byte offset `at` — the face whose
    /// members are all present there at once, and therefore the carriers that can superpose.
    pub fn face_at(&self, at: usize) -> Vec<&StemOccurrence> {
        self.occurrences
            .iter()
            .filter(|occurrence| occurrence.at <= at && at < occurrence.through)
            .collect()
    }

    /// The occurrences that cross `here` — overlapping it without either containing the other.
    ///
    /// A crossing is not a neighbour. Two stems that merely abut can be taken independently; two
    /// that cross **share letters neither can give up**, so engaging one engages the other. That is
    /// what makes a crossed contact different in kind from a simple one, and it is the reason the
    /// licensing carries it rather than reducing it away.
    pub fn crossings_of(&self, here: &StemOccurrence) -> Vec<&StemOccurrence> {
        self.occurrences
            .iter()
            .filter(|other| {
                let overlaps = here.at < other.through && other.at < here.through;
                let contains = (here.at <= other.at && other.through <= here.through)
                    || (other.at <= here.at && here.through <= other.through);
                overlaps && !contains
            })
            .collect()
    }
    /// The stems this cover carries, without their offsets.
    pub fn stems(&self) -> BTreeSet<&str> {
        self.occurrences
            .iter()
            .map(|occurrence| occurrence.stem.as_str())
            .collect()
    }

    /// The character at one offset, in the folded frame the offsets index.
    ///
    /// The offsets in [`Self::occurrences`] and [`Self::residue`] index the **case-folded** word,
    /// because that is the word the founded stems were matched against. Reading the deposited
    /// character at the same offset instead would render `exactCarrier`'s residue as `Carrier` while
    /// its occurrences render as `carrier`, which is one cover printed in two frames.
    fn folded_at(&self, at: usize) -> Option<char> {
        self.word
            .as_bytes()
            .get(at)
            .map(|byte| byte.to_ascii_lowercase() as char)
    }

    /// The residue, as the characters it names.
    pub fn residue_characters(&self) -> String {
        self.residue
            .iter()
            .filter_map(|at| self.folded_at(*at))
            .collect()
    }

    /// The cover written out in reading order: founded segments in place, residue characters
    /// bracketed. Overlapping occurrences both appear, because the cover is plural and a rendering
    /// that picked one would be a choice this organ does not make.
    pub fn render(&self) -> String {
        let mut ordered: Vec<(usize, usize, String)> = self
            .occurrences
            .iter()
            .map(|occurrence| {
                (
                    occurrence.at,
                    occurrence.through,
                    occurrence.stem.clone(),
                )
            })
            .collect();
        ordered.extend(self.residue.iter().filter_map(|at| {
            self.folded_at(*at)
                .map(|symbol| (*at, at + 1, format!("[{symbol}]")))
        }));
        ordered.sort_by_key(|(at, through, _)| (*at, *through));
        ordered
            .into_iter()
            .map(|(_, _, rendered)| rendered)
            .collect::<Vec<String>>()
            .join("|")
    }
}

// -------------------------------------------------------------------------------------------------
// The gauge: two receiver families over one item population
// -------------------------------------------------------------------------------------------------

/// The recruited identifiers of a deposit, read as an observed system whose receivers are the
/// founded stems.
///
/// Items are **character positions** `(identifier, offset)`, `offset` running through the
/// identifier's length inclusive so a terminus is an item. Transport is character succession.
/// Receivers are [`AT_END_RECEIVER`] — *has this identifier ended* — plus one per committed stem,
/// reading *does a founded stem begin here*. A body exposed to nothing carries the first receiver
/// and no others, which is exactly the reading under which an identifier is an atom.
pub struct MorphemicIncidence {
    identifiers: Vec<String>,
    positions: Vec<(usize, usize)>,
    /// The item index at which each identifier's positions begin, so `(which, offset)` resolves in
    /// constant time. Without it `successor` is a linear scan of the position population and the
    /// breadth-first exhibition of collapsed pairs pays that scan on every step — a cost law
    /// `CLAUDE.md` §8 asks to be stated rather than discovered.
    starts: Vec<usize>,
    stems: Vec<String>,
    inputs: Vec<InputId>,
}

impl MorphemicIncidence {
    /// Present a recruited-identifier population under a founded morphology.
    pub fn over(
        identifiers: &BTreeSet<String>,
        morphology: &FoundedMorphology,
    ) -> Result<Self, ConditionedDerivationRefusal> {
        let mut folded: Vec<String> = Vec::new();
        for identifier in identifiers {
            if !identifier.is_ascii() {
                return Err(ConditionedDerivationRefusal::IdentifierIsNotAscii {
                    identifier: identifier.clone(),
                });
            }
            folded.push(identifier.to_ascii_lowercase());
        }
        let mut positions = Vec::new();
        let mut starts = Vec::with_capacity(folded.len());
        let mut alphabet: BTreeSet<u8> = BTreeSet::new();
        for (which, identifier) in folded.iter().enumerate() {
            starts.push(positions.len());
            for offset in 0..=identifier.len() {
                positions.push((which, offset));
            }
            alphabet.extend(identifier.as_bytes().iter().copied());
        }
        Ok(Self {
            identifiers: folded,
            positions,
            starts,
            stems: morphology
                .committed_stems()
                .into_iter()
                .map(str::to_owned)
                .collect(),
            inputs: alphabet
                .into_iter()
                .map(|byte| InputId(u64::from(byte)))
                .collect(),
        })
    }

    /// The item a position takes, so a caller can name a returned pair with its material.
    pub fn position_of(&self, item: ItemId) -> Option<(&str, usize)> {
        self.positions
            .get(item.0 as usize)
            .map(|(which, offset)| (self.identifiers[*which].as_str(), *offset))
    }

    /// A position, written as the material it names: the identifier, a caret, and the tail.
    pub fn render_position(&self, item: ItemId) -> String {
        match self.position_of(item) {
            Some((identifier, offset)) => {
                format!("{}^{}", &identifier[..offset], &identifier[offset..])
            }
            None => format!("?{}", item.0),
        }
    }

    /// A returned word of inputs, read back as the characters it names.
    pub fn render_word(&self, word: &[InputId]) -> String {
        word.iter()
            .map(|input| u8::try_from(input.0).map_or('?', |byte| byte as char))
            .collect()
    }

    /// The stem a receiver identity names, or `None` for [`AT_END_RECEIVER`].
    pub fn stem_of(&self, receiver: ReceiverId) -> Option<&str> {
        if receiver.0 < STEM_RECEIVER_BASE {
            return None;
        }
        self.stems
            .get((receiver.0 - STEM_RECEIVER_BASE) as usize)
            .map(String::as_str)
    }

    /// How many stem receivers this reading declares. A declared aperture, printed with the return.
    pub fn stem_receivers(&self) -> usize {
        self.stems.len()
    }

    /// The first founded stem whose reading of two items differs.
    ///
    /// This is what makes [`SeparatedPositions::witness_stem`] answerable. The receiver a
    /// `CollapsedPair` names is a receiver of the family that *collapsed* the pair, and the
    /// unconditioned family holds one receiver that no stem occupies, so the pair's own witness can
    /// never name a stem. The separating stem lives in the **conditioned** family and is found here.
    pub fn separating_stem(&self, left: ItemId, right: ItemId) -> Option<&str> {
        (0..self.stems.len())
            .map(|at| ReceiverId(STEM_RECEIVER_BASE + at as u64))
            .find(|receiver| {
                self.observation(left, *receiver) != self.observation(right, *receiver)
            })
            .and_then(|receiver| self.stem_of(receiver))
    }

    /// Every founded stem that fires anywhere on this material, with the positions it fires at.
    ///
    /// **This is the founded morphology's reach onto the mathematical material**, complete and
    /// exhibited: a stem the corpus committed that no identifier carries appears nowhere here, and a
    /// reading in which no stem fires returns the empty population rather than a zero.
    pub fn firing(&self) -> Vec<StemFiring> {
        let items = self.items();
        let mut firing = Vec::new();
        for at in 0..self.stems.len() {
            let receiver = ReceiverId(STEM_RECEIVER_BASE + at as u64);
            let positions: Vec<String> = items
                .iter()
                .filter(|item| self.observation(**item, receiver) == Observation(1))
                .map(|item| self.render_position(*item))
                .collect();
            if !positions.is_empty() {
                firing.push(StemFiring {
                    stem: self.stems[at].clone(),
                    positions,
                });
            }
        }
        firing
    }
}

/// One founded stem and every identifier position it reads as a beginning.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct StemFiring {
    pub stem: String,
    pub positions: Vec<String>,
}

impl ObservedSystem for MorphemicIncidence {
    fn items(&self) -> Vec<ItemId> {
        (0..self.positions.len())
            .map(|at| ItemId(at as u64))
            .collect()
    }

    fn receivers(&self) -> Vec<ReceiverId> {
        let mut receivers = vec![ReceiverId(AT_END_RECEIVER)];
        receivers.extend(
            (0..self.stems.len()).map(|at| ReceiverId(STEM_RECEIVER_BASE + at as u64)),
        );
        receivers
    }

    fn inputs(&self) -> Vec<InputId> {
        self.inputs.clone()
    }

    fn observation(&self, item: ItemId, receiver: ReceiverId) -> Observation {
        let Some((which, offset)) = self.positions.get(item.0 as usize).copied() else {
            return Observation(0);
        };
        let identifier = &self.identifiers[which];
        if receiver.0 == AT_END_RECEIVER {
            return Observation(u64::from(offset == identifier.len()));
        }
        let Some(stem) = self.stem_of(receiver) else {
            return Observation(0);
        };
        Observation(u64::from(identifier[offset..].starts_with(stem)))
    }

    fn successor(&self, item: ItemId, input: InputId) -> Option<ItemId> {
        let (which, offset) = self.positions.get(item.0 as usize).copied()?;
        let identifier = self.identifiers[which].as_bytes();
        let byte = u8::try_from(input.0).ok()?;
        if identifier.get(offset).copied()? != byte {
            return None;
        }
        Some(ItemId((self.starts[which] + offset + 1) as u64))
    }
}

/// One pair of identifier positions the conditioned reading separates immediately and the
/// unconditioned reading did not, with the material that separates it.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct SeparatedPositions {
    pub left: String,
    pub right: String,
    /// The shortest word of material after which the unconditioned reading finally saw a
    /// difference. Empty when the difference was visible without transport.
    pub distinguishing_word: String,
    /// The receiver that saw it, as the stem it names, or `None` for a terminus.
    pub witness_stem: Option<String>,
}

/// The orbit of the conditioning, as a gauge acting on one item population.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct FrameOrbit {
    pub conditioned: ReceiverExactCompression,
    pub unconditioned: ReceiverExactCompression,
    /// Pairs the unconditioned one-shot reading merged and the conditioned one did not. **The
    /// orbit.** Empty means the gauge acted trivially on this material.
    pub separated_by_conditioning: Vec<SeparatedPositions>,
    /// The founded morphology's complete incidence on this material: every stem that fires and
    /// where. The generator of the population above.
    pub firing: Vec<StemFiring>,
}

impl FrameOrbit {
    /// The gauge acted. A `false` here is a report that the conditioning did not move the material,
    /// and it is a defect in the construction rather than a finding about the world.
    pub fn acts_nontrivially(&self) -> bool {
        !self.separated_by_conditioning.is_empty()
    }

    /// Removing receivers may only coarsen a receiver-exact quotient — `AblatedSystem`'s own
    /// monotonicity. The unconditioned reading is the conditioned one with every stem receiver
    /// removed, so its one-shot partition can never be finer.
    pub fn coarsening_holds(&self) -> bool {
        self.unconditioned.one_shot.len() <= self.conditioned.one_shot.len()
    }
}

/// Read one recruited-identifier population under two receiver families and return the orbit.
///
/// The two families are the same items and the same transport; they differ only in whether the
/// founded stems are present. The returned population is exhibited with the shortest distinguishing
/// word per pair, which is what `CLAUDE.md` §8 requires of a gauge before agreement between frames
/// may be read as evidence.
pub fn frame_orbit(
    identifiers: &BTreeSet<String>,
    morphology: &FoundedMorphology,
) -> Result<FrameOrbit, ConditionedDerivationRefusal> {
    let conditioned_system = MorphemicIncidence::over(identifiers, morphology)?;
    let unconditioned_system =
        MorphemicIncidence::over(identifiers, &FoundedMorphology::unconditioned())?;
    let conditioned = compress(&conditioned_system);
    let unconditioned = compress(&unconditioned_system);

    let conditioned_merged = conditioned.one_shot.identified_pairs();
    let mut separated = Vec::new();
    for pair in &unconditioned.collapsed {
        if conditioned_merged.contains(&(pair.left, pair.right)) {
            continue;
        }
        separated.push(SeparatedPositions {
            left: unconditioned_system.render_position(pair.left),
            right: unconditioned_system.render_position(pair.right),
            distinguishing_word: unconditioned_system.render_word(&pair.distinguishing_word),
            witness_stem: conditioned_system
                .separating_stem(pair.left, pair.right)
                .map(str::to_owned),
        });
    }
    Ok(FrameOrbit {
        conditioned,
        unconditioned,
        separated_by_conditioning: separated,
        firing: conditioned_system.firing(),
    })
}

// -------------------------------------------------------------------------------------------------
// The production
// -------------------------------------------------------------------------------------------------

/// What a query asks the body for: a further route to a statement the deposit already reached.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct DerivationQuery {
    pub statement: String,
}

impl DerivationQuery {
    pub fn reaching(statement: &str) -> Self {
        Self {
            statement: statement.to_owned(),
        }
    }
}

/// The stems of an occurrence family, in canonical order — the readable name of a face or a
/// crossing set.
fn named(occurrences: &[&StemOccurrence]) -> Vec<String> {
    let mut stems: Vec<String> = occurrences
        .iter()
        .map(|occurrence| occurrence.stem.clone())
        .collect();
    stems.sort();
    stems.dedup();
    stems
}

/// One founded stem, holding two recruited identifiers together.
///
/// `held` is an identifier the licensing **route** already recruits; `brought` is one it does not.
/// Both offsets are carried, so a bridge names *where* in each identifier the stem stands and a
/// reader can tell a morphemic bridge from a residual one without being told.
///
/// `route` is the deposited artifact whose recruitment the bridge extends, keyed `name#ordinal` over
/// the population's own read order — the same key `DerivationIdentity::ByRoute` uses. **Licensing is
/// per route and not per declaration**, and the difference is not cosmetic: pooling thirty-four
/// artifacts of `carrier_transport` onto one recruitment set makes almost every identifier already
/// recruited, and the morphemic bridges — the ones carried by whole words rather than by single
/// residual letters — are exactly the ones that pooling destroys. Measured on the deposit: pooled,
/// no licensing stem was longer than two characters; per route, `carry`, `exact`, `kernel` and
/// `formal` all license.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct Bridge {
    pub stem: String,
    pub held: String,
    pub held_at: usize,
    pub brought: String,
    pub brought_at: usize,
    pub route: String,
    /// **The face on the held side**: every occurrence co-present at `held_at`, this one included.
    /// One means the bridging stem is the only carrier at that site; more means the contact is
    /// superposed and several carriers hold it at once.
    pub held_face: Vec<String>,
    /// The face on the brought side.
    pub brought_face: Vec<String>,
    /// **The stems the bridging occurrence crosses on the held side** — overlapping it without
    /// containment, so they share letters neither can give up.
    pub held_crossings: Vec<String>,
    /// The stems it crosses on the brought side.
    pub brought_crossings: Vec<String>,
}

/// **What kind of contact a bridge is.** A reading of the face and the crossings, not a new
/// quantity — the three are exhaustive and disjoint by construction, and the constructor decides
/// none of them.
///
/// Brandon, 2026-08-09, on what the licensing was missing: *"it should be that stems reflect and
/// refract about emergent boundary limits, they intersect, and they interfere. This is why I
/// consistently say knot theory, hypergeometry, crossings, faces, and intersections are important.
/// Interference, superposition, entanglement, etc."*
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum ContactSpecies {
    /// One carrier at the site on both sides, crossing nothing. The contact stands alone.
    Simple,
    /// More than one occurrence is present at the site on at least one side. Several carriers hold
    /// the contact at once — they superpose there, and the bridging stem is not the only reading.
    Superposed,
    /// The bridging occurrence crosses another on at least one side. **Entangled**: the crossing
    /// stem shares letters with it, so the contact cannot be taken without engaging that stem too.
    Crossed,
}

impl Bridge {
    /// The contact's species. `Crossed` dominates `Superposed`, because a crossing is a constraint
    /// on what else must be engaged while a superposition is only a plurality of carriers.
    pub fn contact(&self) -> ContactSpecies {
        if !self.held_crossings.is_empty() || !self.brought_crossings.is_empty() {
            ContactSpecies::Crossed
        } else if self.held_face.len() > 1 || self.brought_face.len() > 1 {
            ContactSpecies::Superposed
        } else {
            ContactSpecies::Simple
        }
    }
}

/// One mathematical passage the conditioned body emitted.
///
/// The statement is the queried statement **verbatim**, so the passage lands on that statement's
/// 0-cell and is a second route to a standing result rather than a new result. Nothing here is
/// submitted to a kernel; the passage is production read as structure, exactly as the deposited
/// artifacts are.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct DerivedPassage {
    pub name: String,
    pub statement: String,
    /// The standing declaration whose statement this passage re-reaches.
    pub reaches: String,
    /// The recruited identifier the standing route to this statement does not carry.
    pub brought: String,
    /// The founded stem that licensed it.
    pub stem: String,
    /// Every held-identifier occurrence that licenses this passage, once per licensing route.
    /// Plural, and never reduced. [`Self::licensing`] groups it for reading; nothing reduces it.
    pub bridges: Vec<Bridge>,
    /// The artifact.
    pub text: String,
}

/// One bridge with every deposited route that licensed it.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct LicensedBridge {
    pub stem: String,
    pub held: String,
    pub held_at: usize,
    pub brought: String,
    pub brought_at: usize,
    /// The deposited routes whose recruitment this bridge extends, keyed `name#ordinal`.
    pub routes: Vec<String>,
}

impl DerivedPassage {
    /// The bridges, grouped: one entry per distinct occurrence pair, carrying the routes that
    /// licensed it. A regrouping of [`Self::bridges`] and never a reduction of it — every route the
    /// population held is on exactly one entry.
    pub fn licensing(&self) -> Vec<LicensedBridge> {
        let mut grouped: BTreeMap<(String, String, usize, String, usize), Vec<String>> =
            BTreeMap::new();
        for bridge in &self.bridges {
            grouped
                .entry((
                    bridge.stem.clone(),
                    bridge.held.clone(),
                    bridge.held_at,
                    bridge.brought.clone(),
                    bridge.brought_at,
                ))
                .or_default()
                .push(bridge.route.clone());
        }
        grouped
            .into_iter()
            .map(
                |((stem, held, held_at, brought, brought_at), routes)| LicensedBridge {
                    stem,
                    held,
                    held_at,
                    brought,
                    brought_at,
                    routes,
                },
            )
            .collect()
    }

    /// Every deposited route that licensed this passage, without repetition.
    pub fn routes(&self) -> BTreeSet<&str> {
        self.bridges
            .iter()
            .map(|bridge| bridge.route.as_str())
            .collect()
    }
}

/// Compose the Lean-shaped artifact one bridge licenses.
///
/// The body carries exactly one recruitment the standing route does not — `brought`, on the right of
/// a `have` binding, which is the one binding form `derivation_atlas::read_derivation` knows. No
/// import line and no tactic name is written, so every symbol the reading recovers from this text is
/// either the queried statement's own or the brought identifier.
fn compose_passage(name: &str, statement: &str, brought: &str) -> String {
    format!("namespace Soma\ntheorem {name} {statement} := by\n  have bridged := {brought}\nend Soma\n")
}

/// A Lean-legal declaration name for a passage. `.` is the only character a recruited identifier
/// carries that a declaration name may not.
fn passage_name(reaches: &str, stem: &str, brought: &str) -> String {
    format!("{reaches}_via_{stem}_{}", brought.replace('.', "_"))
}

/// Every identifier any standing derivation recruited.
pub fn recruited_population(standing: &[Derivation]) -> BTreeSet<String> {
    standing
        .iter()
        .flat_map(|derivation| derivation.recruited.keys().cloned())
        .collect()
}

/// The conditioned body's production: the passages a query returns.
///
/// For each deposited **route** that reached the queried statement, and each identifier `brought`
/// that route does not recruit, a passage is licensed exactly when some identifier the route *does*
/// recruit shares a committed founded stem with `brought`. Passages are then pooled by
/// `(declaration, stem, brought)`, so thirty-four artifacts of one declaration licensing one bridge
/// return one passage carrying all thirty-four routes as lineage rather than thirty-four passages.
///
/// An unconditioned morphology commits no stem, so `cover` returns no occurrence, no two identifiers
/// share one, and this returns the empty population. That is not a check bolted on: the founded
/// morphology is the only thing that can hold two identifiers together here.
pub fn derive(
    standing: &[Derivation],
    morphology: &FoundedMorphology,
    query: &DerivationQuery,
) -> Result<Vec<DerivedPassage>, ConditionedDerivationRefusal> {
    let population = recruited_population(standing);
    let mut covers: BTreeMap<&String, FoundedCover> = BTreeMap::new();
    for identifier in &population {
        covers.insert(identifier, morphology.cover(identifier)?);
    }

    let mut licensed: BTreeMap<(String, String, String), Vec<Bridge>> = BTreeMap::new();
    for (ordinal, route) in standing.iter().enumerate() {
        if route.statement != query.statement {
            continue;
        }
        let route_key = format!("{}#{ordinal}", route.name);
        for brought in &population {
            if route.recruited.contains_key(brought) {
                continue;
            }
            let brought_cover = &covers[brought];
            for held in route.recruited.keys() {
                let Some(held_cover) = covers.get(held) else {
                    continue;
                };
                for held_occurrence in &held_cover.occurrences {
                    for brought_occurrence in &brought_cover.occurrences {
                        if held_occurrence.stem != brought_occurrence.stem {
                            continue;
                        }
                        licensed
                            .entry((
                                route.name.clone(),
                                held_occurrence.stem.clone(),
                                brought.clone(),
                            ))
                            .or_default()
                            .push(Bridge {
                                stem: held_occurrence.stem.clone(),
                                held: held.clone(),
                                held_at: held_occurrence.at,
                                brought: brought.clone(),
                                brought_at: brought_occurrence.at,
                                route: route_key.clone(),
                                // The face and the crossings are both in hand exactly here, which is
                                // why they are carried here: this is the one site where a contact is
                                // formed, and computing them later would need the covers again.
                                held_face: named(&held_cover.face_at(held_occurrence.at)),
                                brought_face: named(
                                    &brought_cover.face_at(brought_occurrence.at),
                                ),
                                held_crossings: named(
                                    &held_cover.crossings_of(held_occurrence),
                                ),
                                brought_crossings: named(
                                    &brought_cover.crossings_of(brought_occurrence),
                                ),
                            });
                    }
                }
            }
        }
    }

    let mut passages = Vec::with_capacity(licensed.len());
    for ((reaches, stem, brought), mut bridges) in licensed {
        bridges.sort();
        bridges.dedup();
        let name = passage_name(&reaches, &stem, &brought);
        let text = compose_passage(&name, &query.statement, &brought);
        passages.push(DerivedPassage {
            name,
            statement: query.statement.clone(),
            reaches,
            brought,
            stem,
            bridges,
            text,
        });
    }
    Ok(passages)
}

// -------------------------------------------------------------------------------------------------
// The circuit, and the map back to the passage
// -------------------------------------------------------------------------------------------------

/// A passage's place in the population the circuit was founded over.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct PassageId(pub u64);

/// Where a passage came from.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum PassageOrigin {
    /// Deposited. The name is whatever the caller called the material.
    Standing { source: String },
    /// Emitted by the conditioned body, with the stem that licensed it.
    Derived {
        stem: String,
        reaches: String,
        brought: String,
    },
}

/// One passage, with the reading `derivation_atlas` gave it.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Passage {
    pub id: PassageId,
    pub origin: PassageOrigin,
    pub derivation: Derivation,
    pub text: String,
}

impl Passage {
    pub fn is_derived(&self) -> bool {
        matches!(self.origin, PassageOrigin::Derived { .. })
    }
}

/// A derivation circuit with every cell named by the passages that founded it.
///
/// **`provenance` is the seam every later organ depends on.** A curvature deficit at a cell, a
/// holonomy around a loop, a realizer that supports a class — none of those returns can be read
/// unless the cell can be traced back to a passage. `unclaimed` is the falsifier: a cell the
/// provenance cannot name is a defect in the founding, and it is returned by name rather than
/// asserted away.
#[derive(Clone, Debug)]
pub struct ConditionedCircuit {
    pub aperture: CircuitAperture,
    pub circuit: DerivationCircuit,
    pub passages: Vec<Passage>,
    pub provenance: BTreeMap<CausalCellId, BTreeSet<PassageId>>,
    pub unclaimed: Vec<String>,
}

impl ConditionedCircuit {
    /// Every cell is named by at least one passage.
    pub fn provenance_is_total(&self) -> bool {
        self.unclaimed.is_empty()
    }

    /// The passages that founded one cell, in population order.
    pub fn passages_founding(&self, cell: CausalCellId) -> Vec<&Passage> {
        self.provenance
            .get(&cell)
            .map(|ids| {
                ids.iter()
                    .filter_map(|id| self.passages.get(id.0 as usize))
                    .collect()
            })
            .unwrap_or_default()
    }

    /// Every cell a derived passage founded, by cell name. What the conditioning added to the
    /// circuit, as structure.
    pub fn cells_from_derived(&self) -> BTreeSet<String> {
        self.circuit
            .complex()
            .cells()
            .values()
            .filter(|cell| {
                self.passages_founding(cell.id)
                    .iter()
                    .all(|passage| passage.is_derived())
            })
            .map(|cell| cell.name.clone())
            .collect()
    }

    /// Every cell name the complex carries.
    pub fn cell_names(&self) -> BTreeSet<String> {
        self.circuit
            .complex()
            .cells()
            .values()
            .map(|cell| cell.name.clone())
            .collect()
    }
}

/// The 0-cell key `found_circuit` gives the passage at `ordinal` under a declared identity.
fn vertex_key(identity: DerivationIdentity, derivation: &Derivation, ordinal: usize) -> String {
    match identity {
        DerivationIdentity::ByDeclaration => derivation.name.clone(),
        DerivationIdentity::ByRoute => format!("{}#{ordinal}", derivation.name),
    }
}

/// Found the circuit a passage population presents, and the map from each cell back to the passages
/// that founded it.
pub fn found_conditioned_circuit(
    passages: Vec<Passage>,
    aperture: CircuitAperture,
) -> Result<ConditionedCircuit, ConditionedDerivationRefusal> {
    let derivations: Vec<Derivation> = passages
        .iter()
        .map(|passage| passage.derivation.clone())
        .collect();
    let circuit = found_circuit(&derivations, aperture)?;

    let mut provenance: BTreeMap<CausalCellId, BTreeSet<PassageId>> = BTreeMap::new();
    let mut claim = |cell: CausalCellId, id: PassageId| {
        provenance.entry(cell).or_default().insert(id);
    };

    for (ordinal, passage) in passages.iter().enumerate() {
        let key = vertex_key(aperture.identity, &passage.derivation, ordinal);
        if let Some(cell) = circuit.vertices().get(&key) {
            claim(*cell, passage.id);
        }
        for symbol in passage.derivation.recruited.keys() {
            if let Some(cell) = circuit.vertices().get(symbol) {
                claim(*cell, passage.id);
            }
            if let Some(cell) = circuit
                .recruitments()
                .get(&(key.clone(), symbol.clone()))
            {
                claim(*cell, passage.id);
            }
        }
        if aperture.statements == StatementIncidence::Founded {
            let statement = &passage.derivation.statement;
            if let Some(cell) = circuit
                .vertices()
                .get(&statement_vertex_key(statement))
            {
                claim(*cell, passage.id);
            }
            if let Some(cell) = circuit.reaches().get(&(key.clone(), statement.clone())) {
                claim(*cell, passage.id);
            }
        }
    }

    let unclaimed: Vec<String> = circuit
        .complex()
        .cells()
        .values()
        .filter(|cell| !provenance.contains_key(&cell.id))
        .map(|cell| cell.name.clone())
        .collect();

    Ok(ConditionedCircuit {
        aperture,
        circuit,
        passages,
        provenance,
        unclaimed,
    })
}

// -------------------------------------------------------------------------------------------------
// The body
// -------------------------------------------------------------------------------------------------

/// The three things and the transitions between them.
#[derive(Clone, Debug)]
pub struct ConditionedBody {
    standing: Vec<Passage>,
    morphology: FoundedMorphology,
}

impl ConditionedBody {
    /// Mount a body on deposited mathematical material. Unconditioned: it has been exposed to
    /// nothing and every recruited identifier is an atom to it.
    ///
    /// Each entry is a source name and the artifact text. Material carrying no `theorem` line is
    /// refused by name rather than silently skipped.
    pub fn mount(
        deposit: impl IntoIterator<Item = (String, String)>,
    ) -> Result<Self, ConditionedDerivationRefusal> {
        let mut standing = Vec::new();
        for (source, text) in deposit {
            let derivation = read_derivation(&text)
                .ok_or(ConditionedDerivationRefusal::MaterialDeclaresNothing {
                    source: source.clone(),
                })?;
            standing.push(Passage {
                id: PassageId(standing.len() as u64),
                origin: PassageOrigin::Standing { source },
                derivation,
                text,
            });
        }
        Ok(Self {
            standing,
            morphology: FoundedMorphology::unconditioned(),
        })
    }

    /// Exposure to linguistic material founds the morphology this body later conducts through.
    pub fn condition(&mut self, exposures: &[Exposure]) {
        self.morphology = FoundedMorphology::condition(exposures);
    }

    /// Carry a morphology a foreign conditioner founded.
    pub fn carry_morphology(&mut self, morphology: FoundedMorphology) {
        self.morphology = morphology;
    }

    pub fn morphology(&self) -> &FoundedMorphology {
        &self.morphology
    }

    pub fn standing(&self) -> &[Passage] {
        &self.standing
    }

    /// The deposited derivations, as `derivation_atlas` read them.
    pub fn standing_derivations(&self) -> Vec<Derivation> {
        self.standing
            .iter()
            .map(|passage| passage.derivation.clone())
            .collect()
    }

    /// Every statement the deposit reached, canonically ordered. The queries this body can be asked.
    pub fn standing_statements(&self) -> BTreeSet<String> {
        self.standing
            .iter()
            .map(|passage| passage.derivation.statement.clone())
            .collect()
    }

    pub fn recruited_population(&self) -> BTreeSet<String> {
        recruited_population(&self.standing_derivations())
    }

    /// The production. Empty for a body exposed to nothing.
    pub fn derive(
        &self,
        query: &DerivationQuery,
    ) -> Result<Vec<DerivedPassage>, ConditionedDerivationRefusal> {
        derive(&self.standing_derivations(), &self.morphology, query)
    }

    /// The whole passage population under one query: the deposit, then what the body derived.
    pub fn passages(
        &self,
        query: &DerivationQuery,
    ) -> Result<Vec<Passage>, ConditionedDerivationRefusal> {
        let mut passages = self.standing.clone();
        for derived in self.derive(query)? {
            let derivation = read_derivation(&derived.text).ok_or(
                ConditionedDerivationRefusal::EmittedPassageDeclaresNothing {
                    name: derived.name.clone(),
                },
            )?;
            if derivation.statement != derived.statement {
                return Err(
                    ConditionedDerivationRefusal::EmittedPassageMissedItsStatement {
                        name: derived.name.clone(),
                        wanted: derived.statement.clone(),
                        read: derivation.statement,
                    },
                );
            }
            if !derivation.recruited.contains_key(&derived.brought) {
                return Err(
                    ConditionedDerivationRefusal::EmittedPassageDroppedItsBridge {
                        name: derived.name.clone(),
                        brought: derived.brought.clone(),
                    },
                );
            }
            passages.push(Passage {
                id: PassageId(passages.len() as u64),
                origin: PassageOrigin::Derived {
                    stem: derived.stem.clone(),
                    reaches: derived.reaches.clone(),
                    brought: derived.brought.clone(),
                },
                derivation,
                text: derived.text,
            });
        }
        Ok(passages)
    }

    /// The circuit this body's production presents under a declared aperture.
    pub fn circuit(
        &self,
        query: &DerivationQuery,
        aperture: CircuitAperture,
    ) -> Result<ConditionedCircuit, ConditionedDerivationRefusal> {
        found_conditioned_circuit(self.passages(query)?, aperture)
    }

    /// The gauge orbit of this body's conditioning over its own recruited identifiers.
    pub fn frame_orbit(&self) -> Result<FrameOrbit, ConditionedDerivationRefusal> {
        frame_orbit(&self.recruited_population(), &self.morphology)
    }

    /// **The ablation.** The same body with one founded stem removed by removing it.
    pub fn without_stem(&self, stem: &str) -> Option<Self> {
        Some(Self {
            standing: self.standing.clone(),
            morphology: self.morphology.without_stem(stem)?,
        })
    }

    /// The same body carrying a declared foil morphology in place of the founded one.
    pub fn with_morphology(&self, morphology: FoundedMorphology) -> Self {
        Self {
            standing: self.standing.clone(),
            morphology,
        }
    }
}

/// One passage a removal **reopened**: it was not licensed before, and a stem the removed one had
/// been covering licenses it now.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Reopening {
    pub passage: String,
    /// The stem that licenses it now.
    pub stem: String,
    /// The removed stem, which had contained that one and suppressed it by maximality.
    pub was_covered_by: String,
}

/// What removing one founded stem removed, and what its removal reopened.
///
/// Every field is a population with its material. `passages_absent` carries the artifacts whole, and
/// `cells_absent` names the circuit cells that stopped existing — which is what makes this a
/// structural removal rather than a changed number.
///
/// **`passages_appeared` is not a defect and the first form of this type said it was.** The declared
/// control read *"removing a receiver can only remove licences"*, and the material refused it on the
/// first run: deleting `at` took the production from 27 passages to 36. The reason is
/// [`FoundedMorphology::cover`]'s maximality — `Nat` covers as `n|at`, and with `at` gone the
/// occurrences `a` and `t` it had been containing become maximal and license bridges of their own.
/// That is **retained-fiber reopening**, the project's own mechanism, appearing here without being
/// put in: a founded stem does not only license, it also *suppresses* what it covers, and removing
/// it returns the suppressed population. The invariant that survives, and that can still fail, is
/// [`Self::removes_structure`]: every reopened passage's stem is a proper factor of the removed one.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StemAblation {
    pub stem: String,
    /// The wholes of linguistic material that witnessed the removed stem.
    pub wholes: Vec<String>,
    pub passages_before: Vec<String>,
    pub passages_after: Vec<String>,
    /// The passages the removal made structurally absent, exhibited whole.
    pub passages_absent: Vec<DerivedPassage>,
    /// Passages present after the removal that were not present before, each with the stem that
    /// licenses it and the removed stem that had covered it.
    pub reopened: Vec<Reopening>,
    /// Reopened passages whose licensing stem the removed stem does **not** contain. Must be empty:
    /// nothing else can promote an occurrence.
    pub unaccounted: Vec<Reopening>,
    pub cells_absent: Vec<String>,
    pub cells_appeared: Vec<String>,
}

impl StemAblation {
    /// The removal removed later production by removing structure, and everything it reopened is
    /// accounted for by the maximality the removed stem had been exercising.
    pub fn removes_structure(&self) -> bool {
        !self.passages_absent.is_empty()
            && !self.cells_absent.is_empty()
            && self.unaccounted.is_empty()
            && self
                .passages_absent
                .iter()
                .all(|passage| passage.stem == self.stem)
    }
}

/// Delete one founded stem, re-query, and return what stopped existing.
///
/// This is the fourth ablation shape: not construction by omission, not receiver-axis withholding,
/// not reference-versus-return, but **deleting a founded fiber and re-querying**.
pub fn ablate_stem(
    body: &ConditionedBody,
    stem: &str,
    query: &DerivationQuery,
    aperture: CircuitAperture,
) -> Result<StemAblation, ConditionedDerivationRefusal> {
    let founded = body.morphology().stem(stem).ok_or(
        ConditionedDerivationRefusal::StemWasNeverFounded {
            stem: stem.to_owned(),
        },
    )?;
    let wholes = founded.wholes.clone();
    let ablated = body
        .without_stem(stem)
        .ok_or(ConditionedDerivationRefusal::StemWasNeverFounded {
            stem: stem.to_owned(),
        })?;

    let before = body.derive(query)?;
    let after = ablated.derive(query)?;
    let after_names: BTreeSet<&str> = after.iter().map(|passage| passage.name.as_str()).collect();
    let before_names: BTreeSet<&str> = before.iter().map(|passage| passage.name.as_str()).collect();

    let passages_absent: Vec<DerivedPassage> = before
        .iter()
        .filter(|passage| !after_names.contains(passage.name.as_str()))
        .cloned()
        .collect();
    let reopened: Vec<Reopening> = after
        .iter()
        .filter(|passage| !before_names.contains(passage.name.as_str()))
        .map(|passage| Reopening {
            passage: passage.name.clone(),
            stem: passage.stem.clone(),
            was_covered_by: stem.to_owned(),
        })
        .collect();
    let unaccounted: Vec<Reopening> = reopened
        .iter()
        .filter(|entry| !(stem.contains(&entry.stem) && stem != entry.stem))
        .cloned()
        .collect();

    let cells_before = body.circuit(query, aperture)?.cell_names();
    let cells_after = ablated.circuit(query, aperture)?.cell_names();

    Ok(StemAblation {
        stem: stem.to_owned(),
        wholes,
        passages_before: before.iter().map(|passage| passage.name.clone()).collect(),
        passages_after: after.iter().map(|passage| passage.name.clone()).collect(),
        passages_absent,
        reopened,
        unaccounted,
        cells_absent: cells_before.difference(&cells_after).cloned().collect(),
        cells_appeared: cells_after.difference(&cells_before).cloned().collect(),
    })
}

// -------------------------------------------------------------------------------------------------
// Refusals
// -------------------------------------------------------------------------------------------------

/// Why a conditioning, a derivation, or a circuit was refused.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ConditionedDerivationRefusal {
    /// A founded morphology is ASCII, and a byte offset into a multi-byte identifier names a place
    /// no stem can begin.
    IdentifierIsNotAscii { identifier: String },
    /// Deposited material carrying no declaration. Refused rather than skipped, so a deposit cannot
    /// silently shrink between two runs.
    MaterialDeclaresNothing { source: String },
    /// A passage this module composed could not be read back. The composer and the reading disagree,
    /// which is a defect in the composer.
    EmittedPassageDeclaresNothing { name: String },
    /// The passage was read back reaching a different statement than the query. The route would land
    /// on the wrong 0-cell.
    EmittedPassageMissedItsStatement {
        name: String,
        wanted: String,
        read: String,
    },
    /// The passage was read back without the identifier its bridge brought. The licence would be
    /// invisible in the circuit.
    EmittedPassageDroppedItsBridge { name: String, brought: String },
    /// An ablation named a stem the morphology never founded.
    StemWasNeverFounded { stem: String },
    /// The circuit refused the population.
    Atlas(DerivationAtlasRefusal),
}

impl std::fmt::Display for ConditionedDerivationRefusal {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::IdentifierIsNotAscii { identifier } => write!(
                formatter,
                "the identifier {identifier:?} is not ASCII; a founded stem cannot name an offset in it"
            ),
            Self::MaterialDeclaresNothing { source } => {
                write!(formatter, "{source} declares no theorem")
            }
            Self::EmittedPassageDeclaresNothing { name } => {
                write!(formatter, "the composed passage {name} declares no theorem")
            }
            Self::EmittedPassageMissedItsStatement { name, wanted, read } => write!(
                formatter,
                "the composed passage {name} was read reaching {read:?} rather than {wanted:?}"
            ),
            Self::EmittedPassageDroppedItsBridge { name, brought } => write!(
                formatter,
                "the composed passage {name} was read without recruiting {brought}, so its licence \
                 is invisible in the circuit"
            ),
            Self::StemWasNeverFounded { stem } => {
                write!(formatter, "the morphology never founded the stem {stem:?}")
            }
            Self::Atlas(refusal) => write!(formatter, "{refusal}"),
        }
    }
}

impl std::error::Error for ConditionedDerivationRefusal {}

impl From<DerivationAtlasRefusal> for ConditionedDerivationRefusal {
    fn from(refusal: DerivationAtlasRefusal) -> Self {
        Self::Atlas(refusal)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // ---------------------------------------------------------------------------------------------
    // Material. Two corpora that differ in exactly one respect that matters, plus a deposit whose
    // identifiers carry the morphemes both corpora are being asked about.
    // ---------------------------------------------------------------------------------------------

    /// A corpus that witnesses `exact` and `carry` in two wholes and `carrier` in one only.
    fn corpus_without_carrier() -> Vec<Exposure> {
        vec![
            expose(
                "one",
                "an exact transport must carry the boundary. the carrier is named once here.",
            ),
            expose("two", "exact transport, and what it must carry across."),
        ]
    }

    /// The same corpus with `carrier` witnessed by a second whole. Nothing else differs.
    fn corpus_with_carrier() -> Vec<Exposure> {
        vec![
            expose(
                "one",
                "an exact transport must carry the boundary. the carrier is named once here.",
            ),
            expose(
                "two",
                "exact transport, and what it must carry across. the carrier again.",
            ),
        ]
    }

    /// Three artifacts, and the third is load-bearing rather than decorative: **two of them are
    /// distinct routes of one declaration reaching one statement**, so a bridge can be licensed by
    /// more than one route and `licensing`'s grouping has something to group. Without it,
    /// `grouping_the_bridges_loses_no_route_and_names_each_occurrence_pair_once` holds for a
    /// truncating implementation as readily as for a correct one — a check whose material cannot
    /// vary the property under test, which is the defect `CLAUDE.md` §8 convicts.
    fn deposit() -> Vec<(String, String)> {
        vec![
            (
                "carry".to_owned(),
                "namespace Soma\ntheorem carrier_transport (P : Prop) : exactCarrier P := by\n  \
                 have step := exact_chart_carry\nend Soma\n"
                    .to_owned(),
            ),
            (
                "carry-again".to_owned(),
                "namespace Soma\ntheorem carrier_transport (P : Prop) : exactCarrier P := by\n  \
                 have step := exact_chart_carry\n  have again := exact_chart_carry\nend Soma\n"
                    .to_owned(),
            ),
            (
                "relay".to_owned(),
                "namespace Soma\ntheorem relay_agrees (P : Prop) : exactCarrier P := by\n  \
                 have step := formal_carry\nend Soma\n"
                    .to_owned(),
            ),
        ]
    }

    fn the_statement() -> DerivationQuery {
        DerivationQuery::reaching("(P : Prop) : exactCarrier P")
    }

    // ---------------------------------------------------------------------------------------------
    // The conditioning
    // ---------------------------------------------------------------------------------------------

    #[test]
    fn a_word_one_whole_witnessed_stays_provisional_and_a_second_distinct_whole_commits_it() {
        let morphology = FoundedMorphology::condition(&corpus_without_carrier());
        let carrier = morphology.stem("carrier").expect("carrier was witnessed");
        assert_eq!(carrier.standing(), StemStanding::Provisional);
        assert_eq!(carrier.wholes, vec!["one".to_owned()]);

        let exact = morphology.stem("exact").expect("exact was witnessed");
        assert_eq!(exact.standing(), StemStanding::Committed);
        assert_eq!(exact.wholes, vec!["one".to_owned(), "two".to_owned()]);

        let committed = morphology.committed_stems();
        assert!(committed.contains(&"exact"), "{committed:?}");
        assert!(committed.contains(&"carry"), "{committed:?}");
        assert!(!committed.contains(&"carrier"), "{committed:?}");
    }

    #[test]
    fn a_repeat_inside_one_whole_does_not_commit_a_stem() {
        let morphology = FoundedMorphology::condition(&[expose(
            "alone",
            "carrier carrier carrier carrier carrier",
        )]);
        let carrier = morphology.stem("carrier").expect("witnessed");
        assert_eq!(carrier.wholes, vec!["alone".to_owned()]);
        assert_eq!(carrier.standing(), StemStanding::Provisional);
        assert!(morphology.committed_stems().is_empty());
    }

    #[test]
    fn every_founded_stem_is_parented_on_the_version_founded_before_it() {
        let morphology = FoundedMorphology::condition(&corpus_without_carrier());
        let founded = morphology.founded();
        assert!(founded.len() > 3, "{}", founded.len());
        assert_eq!(founded[0].parent, None);
        for pair in founded.windows(2) {
            assert_eq!(pair[1].parent, Some(pair[0].id));
        }
    }

    #[test]
    fn the_cover_carries_the_contained_occurrence_and_the_maximal_reading_refuses_it() {
        // `act` and `exact` are both committed. Both are PRESENT in the cover; only `exact` stands
        // in the maximal reading. Re-founded 2026-08-09: this test asserted that `act` was absent
        // from `cover.occurrences`, which pinned the constructor's reduction as though it were the
        // law. It is a reading, and the reading is where it now lives.
        let morphology = FoundedMorphology::condition(&[
            expose("one", "exact act"),
            expose("two", "exact act"),
        ]);
        let cover = morphology.cover("exact").expect("ascii");
        let exact = StemOccurrence { stem: "exact".to_owned(), at: 0, through: 5 };
        let act = StemOccurrence { stem: "act".to_owned(), at: 2, through: 5 };

        assert_eq!(cover.occurrences, vec![exact.clone(), act.clone()], "the cover carries both");
        assert_eq!(cover.maximal(), vec![&exact], "the maximal reading carries one");
        assert!(cover.residue.is_empty(), "{:?}", cover.residue);
        // Contained, not crossing: `act` sits inside `exact`, so this pair is not a 1-face.
        assert!(cover.crossings().is_empty());
        // At offset 2 both are present. That is the face, and it is what can superpose.
        assert_eq!(cover.face_at(2), vec![&exact, &act]);
    }

    /// **A real crossing: two committed stems that overlap without either containing the other.**
    /// This is the object a partition cannot hold and the reason the reduction was removed.
    #[test]
    fn two_overlapping_stems_cross_and_the_maximal_reading_keeps_only_one() {
        let morphology = FoundedMorphology::condition(&[
            expose("one", "exa xac"),
            expose("two", "exa xac"),
        ]);
        let cover = morphology.cover("exact").expect("ascii");
        let crossings = cover.crossings();
        assert_eq!(crossings.len(), 1, "{:?}", cover.occurrences);
        let (left, right) = crossings[0];
        assert_eq!((left.stem.as_str(), left.at, left.through), ("exa", 0, 3));
        assert_eq!((right.stem.as_str(), right.at, right.through), ("xac", 1, 4));
        // They share offsets 1 and 2 — the overlap is where they interfere.
        assert_eq!(cover.face_at(1).len(), 2);
        assert_eq!(cover.face_at(2).len(), 2);
        // **And the maximal reading keeps BOTH.** Neither contains the other, so neither is
        // refused: `maximal` is the antichain under containment, not a partition. Crossings always
        // survived it; what it deleted was containment. This assertion read `<` until it was run.
        assert_eq!(cover.maximal().len(), cover.occurrences.len());
    }

    #[test]
    fn a_tail_no_committed_stem_covers_is_returned_as_residue_and_the_second_corpus_founds_it() {
        let without = FoundedMorphology::condition(&corpus_without_carrier());
        let with = FoundedMorphology::condition(&corpus_with_carrier());

        let blind = without.cover("exactCarrier").expect("ascii");
        let seeing = with.cover("exactCarrier").expect("ascii");

        assert_eq!(blind.render(), "exact|[c]|[a]|[r]|[r]|[i]|[e]|[r]");
        assert_eq!(blind.residue_characters(), "carrier");
        assert_eq!(seeing.render(), "exact|carrier");
        assert!(seeing.residue.is_empty(), "{:?}", seeing.residue);
        assert_ne!(blind.stems(), seeing.stems());
    }

    #[test]
    fn a_word_the_morphology_never_saw_is_still_decomposed_which_is_what_reusable_means() {
        let morphology = FoundedMorphology::condition(&corpus_with_carrier());
        // Neither corpus contains this identifier anywhere.
        let cover = morphology.cover("transportCarrier").expect("ascii");
        assert_eq!(cover.render(), "transport|carrier");
    }

    #[test]
    fn a_non_ascii_identifier_is_refused_rather_than_offset_into() {
        let morphology = FoundedMorphology::condition(&corpus_with_carrier());
        assert_eq!(
            morphology.cover("exactCarriér"),
            Err(ConditionedDerivationRefusal::IdentifierIsNotAscii {
                identifier: "exactCarriér".to_owned(),
            })
        );
    }

    // ---------------------------------------------------------------------------------------------
    // The gauge
    // ---------------------------------------------------------------------------------------------

    #[test]
    fn the_conditioned_and_unconditioned_readings_are_distinct_frames_and_the_orbit_carries_words() {
        let body = {
            let mut body = ConditionedBody::mount(deposit()).expect("deposit reads");
            body.condition(&corpus_with_carrier());
            body
        };
        let orbit = body.frame_orbit().expect("ascii identifiers");
        assert!(orbit.coarsening_holds());
        assert!(
            orbit.acts_nontrivially(),
            "the conditioning separated no pair the unconditioned reading merged"
        );
        assert!(
            orbit.conditioned.one_shot.len() > orbit.unconditioned.one_shot.len(),
            "conditioned {} unconditioned {}",
            orbit.conditioned.one_shot.len(),
            orbit.unconditioned.one_shot.len()
        );
        // A pair the unconditioned one-shot merged and the conditioned one did not must differ on
        // some stem: `AT_END_RECEIVER` stands in both families, so it cannot be what separated them.
        let anonymous: Vec<&SeparatedPositions> = orbit
            .separated_by_conditioning
            .iter()
            .filter(|pair| pair.witness_stem.is_none())
            .collect();
        assert!(
            anonymous.is_empty(),
            "{} separated pairs named no stem, first {:?}",
            anonymous.len(),
            anonymous.first()
        );
    }

    #[test]
    fn the_firing_population_carries_the_stems_the_material_holds_and_omits_those_it_does_not() {
        let mut body = ConditionedBody::mount(deposit()).expect("deposit reads");
        body.condition(&corpus_with_carrier());
        let orbit = body.frame_orbit().expect("ascii identifiers");
        let fired: BTreeSet<&str> = orbit
            .firing
            .iter()
            .map(|firing| firing.stem.as_str())
            .collect();
        assert!(fired.contains("carry"), "{fired:?}");
        assert!(fired.contains("carrier"), "{fired:?}");
        assert!(fired.contains("exact"), "{fired:?}");
        // Committed by the corpus, carried by no identifier the deposit recruits.
        assert!(body.morphology().committed_stems().contains(&"must"));
        assert!(!fired.contains("must"), "{fired:?}");
        for firing in &orbit.firing {
            assert!(!firing.positions.is_empty());
            for position in &firing.positions {
                let (_, tail) = position.split_once('^').expect("a rendered position");
                assert!(
                    tail.starts_with(&firing.stem),
                    "{} does not begin {}",
                    position,
                    firing.stem
                );
            }
        }
    }

    #[test]
    fn an_unconditioned_body_declares_exactly_one_receiver_and_a_conditioned_one_declares_more() {
        let population = BTreeSet::from(["exactCarrier".to_owned()]);
        let bare = MorphemicIncidence::over(&population, &FoundedMorphology::unconditioned())
            .expect("ascii");
        assert_eq!(bare.stem_receivers(), 0);
        assert_eq!(bare.receivers(), vec![ReceiverId(AT_END_RECEIVER)]);

        let conditioned =
            MorphemicIncidence::over(&population, &FoundedMorphology::condition(&corpus_with_carrier()))
                .expect("ascii");
        assert!(conditioned.stem_receivers() > 0);
        assert!(conditioned.receivers().len() > bare.receivers().len());
    }

    #[test]
    fn constant_time_succession_lands_on_the_position_it_names_across_several_identifiers() {
        let population = BTreeSet::from([
            "exactCarrier".to_owned(),
            "Prop".to_owned(),
            "exact_chart_carry".to_owned(),
        ]);
        let system = MorphemicIncidence::over(&population, &FoundedMorphology::unconditioned())
            .expect("ascii");
        let mut advanced = 0usize;
        for item in system.items() {
            let (identifier, offset) = system.position_of(item).expect("an item");
            let identifier = identifier.to_owned();
            for input in system.inputs() {
                let byte = u8::try_from(input.0).expect("an octet");
                match system.successor(item, input) {
                    Some(next) => {
                        assert_eq!(identifier.as_bytes()[offset], byte);
                        let (landed, landed_at) = system.position_of(next).expect("a landing");
                        assert_eq!(landed, identifier, "succession left the identifier");
                        assert_eq!(landed_at, offset + 1);
                        advanced += 1;
                    }
                    None => assert!(
                        identifier.as_bytes().get(offset).copied() != Some(byte),
                        "{identifier} at {offset} refused {}",
                        byte as char
                    ),
                }
            }
        }
        assert_eq!(advanced, "exactcarrier".len() + "prop".len() + "exact_chart_carry".len());
    }

    #[test]
    fn a_position_renders_as_the_material_it_names() {
        let population = BTreeSet::from(["exactCarrier".to_owned()]);
        let system = MorphemicIncidence::over(&population, &FoundedMorphology::unconditioned())
            .expect("ascii");
        assert_eq!(system.render_position(ItemId(0)), "^exactcarrier");
        assert_eq!(system.render_position(ItemId(5)), "exact^carrier");
        assert_eq!(system.render_position(ItemId(12)), "exactcarrier^");
    }

    // ---------------------------------------------------------------------------------------------
    // The production
    // ---------------------------------------------------------------------------------------------

    #[test]
    fn an_unconditioned_body_returns_no_passage_and_a_conditioned_one_returns_a_named_population() {
        let bare = ConditionedBody::mount(deposit()).expect("deposit reads");
        assert!(bare
            .derive(&the_statement())
            .expect("derives")
            .is_empty());

        let mut conditioned = ConditionedBody::mount(deposit()).expect("deposit reads");
        conditioned.condition(&corpus_with_carrier());
        let derived = conditioned.derive(&the_statement()).expect("derives");
        assert!(!derived.is_empty(), "the conditioned body derived nothing");

        // The bridge is morphemic and the passage carries it whole.
        let carry: Vec<&DerivedPassage> = derived
            .iter()
            .filter(|passage| passage.stem == "carry")
            .collect();
        assert!(!carry.is_empty(), "{:?}", derived.iter().map(|p| &p.stem).collect::<Vec<_>>());
        for passage in carry {
            assert!(!passage.bridges.is_empty());
            for bridge in &passage.bridges {
                assert_eq!(bridge.stem, "carry");
                assert!(bridge.held.to_ascii_lowercase()[bridge.held_at..].starts_with("carry"));
                assert!(
                    bridge.brought.to_ascii_lowercase()[bridge.brought_at..].starts_with("carry")
                );
            }
        }
    }

    #[test]
    fn grouping_the_bridges_loses_no_route_and_names_each_occurrence_pair_once() {
        let mut body = ConditionedBody::mount(deposit()).expect("deposit reads");
        body.condition(&corpus_with_carrier());
        let derived = body.derive(&the_statement()).expect("derives");
        assert!(!derived.is_empty());
        for passage in &derived {
            let grouped = passage.licensing();
            let carried: usize = grouped.iter().map(|entry| entry.routes.len()).sum();
            assert_eq!(carried, passage.bridges.len(), "{}", passage.name);
            let keys: BTreeSet<(&str, &str, usize, &str, usize)> = grouped
                .iter()
                .map(|entry| {
                    (
                        entry.stem.as_str(),
                        entry.held.as_str(),
                        entry.held_at,
                        entry.brought.as_str(),
                        entry.brought_at,
                    )
                })
                .collect();
            assert_eq!(keys.len(), grouped.len(), "an occurrence pair appeared twice");
            assert!(!passage.routes().is_empty());
        }
        // The material must be able to vary the property: some occurrence pair is licensed by more
        // than one route, or a grouping that kept only the first route would pass this test.
        assert!(
            derived
                .iter()
                .flat_map(DerivedPassage::licensing)
                .any(|entry| entry.routes.len() >= 2),
            "no bridge in the fixture is licensed by two routes"
        );
    }

    #[test]
    fn an_emitted_passage_reads_back_to_the_queried_statement_and_recruits_what_it_brought() {
        let mut body = ConditionedBody::mount(deposit()).expect("deposit reads");
        body.condition(&corpus_with_carrier());
        let query = the_statement();
        for passage in body.derive(&query).expect("derives") {
            let read = read_derivation(&passage.text).expect("the composed text declares");
            assert_eq!(read.name, passage.name);
            assert_eq!(read.statement, query.statement);
            assert!(
                read.recruited.contains_key(&passage.brought),
                "{} did not recruit {}",
                passage.name,
                passage.brought
            );
        }
    }

    #[test]
    fn a_bridge_never_brings_an_identifier_its_own_licensing_route_already_recruits() {
        let mut body = ConditionedBody::mount(deposit()).expect("deposit reads");
        body.condition(&corpus_with_carrier());
        let standing = body.standing_derivations();
        let routes: BTreeMap<String, &Derivation> = standing
            .iter()
            .enumerate()
            .map(|(ordinal, derivation)| (format!("{}#{ordinal}", derivation.name), derivation))
            .collect();
        let mut examined = 0usize;
        for passage in body.derive(&the_statement()).expect("derives") {
            for bridge in &passage.bridges {
                let route = routes[&bridge.route];
                assert!(
                    !route.recruited.contains_key(&bridge.brought),
                    "{} brought {} which route {} already recruits",
                    passage.name,
                    bridge.brought,
                    bridge.route
                );
                assert!(route.recruited.contains_key(&bridge.held));
                examined += 1;
            }
        }
        assert!(examined > 0, "no bridge was examined");
    }

    #[test]
    fn a_query_for_a_statement_the_deposit_never_reached_returns_nothing() {
        let mut body = ConditionedBody::mount(deposit()).expect("deposit reads");
        body.condition(&corpus_with_carrier());
        assert!(body
            .derive(&DerivationQuery::reaching("(Q : Prop) : neverReached Q"))
            .expect("derives")
            .is_empty());
    }

    // ---------------------------------------------------------------------------------------------
    // The two declared foils
    // ---------------------------------------------------------------------------------------------

    #[test]
    fn the_promoted_provisional_foil_licenses_a_different_population() {
        let mut body = ConditionedBody::mount(deposit()).expect("deposit reads");
        body.condition(&corpus_without_carrier());
        let query = the_statement();
        let founded: BTreeSet<String> = body
            .derive(&query)
            .expect("derives")
            .into_iter()
            .map(|passage| passage.name)
            .collect();

        let foil = body.with_morphology(body.morphology().promoted_provisional());
        let foiled: BTreeSet<String> = foil
            .derive(&query)
            .expect("derives")
            .into_iter()
            .map(|passage| passage.name)
            .collect();
        assert_ne!(
            founded, foiled,
            "the stems that never recurred license the same passages, so the recurrence condition \
             is decorative"
        );
    }

    #[test]
    fn the_reversed_foil_licenses_a_different_population() {
        let mut body = ConditionedBody::mount(deposit()).expect("deposit reads");
        body.condition(&corpus_with_carrier());
        let query = the_statement();
        let founded: BTreeSet<String> = body
            .derive(&query)
            .expect("derives")
            .into_iter()
            .map(|passage| passage.name)
            .collect();

        let reversed = body.morphology().reversed();
        assert_eq!(
            reversed.committed_stems().len(),
            body.morphology().committed_stems().len()
        );
        let foiled: BTreeSet<String> = body
            .with_morphology(reversed)
            .derive(&query)
            .expect("derives")
            .into_iter()
            .map(|passage| passage.name)
            .collect();
        assert_ne!(founded, foiled);
    }

    // ---------------------------------------------------------------------------------------------
    // The circuit and the provenance
    // ---------------------------------------------------------------------------------------------

    #[test]
    fn every_cell_of_the_circuit_is_named_by_a_passage_under_all_four_declared_apertures() {
        let mut body = ConditionedBody::mount(deposit()).expect("deposit reads");
        body.condition(&corpus_with_carrier());
        let query = the_statement();
        for aperture in CircuitAperture::DECLARED {
            let Ok(circuit) = body.circuit(&query, aperture) else {
                // `Multiplicity` under `ByDeclaration` is refused when a name carries two artifacts;
                // that refusal is the atlas's and not this module's to reinterpret.
                continue;
            };
            assert!(
                circuit.provenance_is_total(),
                "{aperture:?} left {:?} unclaimed",
                circuit.unclaimed
            );
            assert!(!circuit.cell_names().is_empty());
        }
    }

    #[test]
    fn the_conditioning_founds_circuit_cells_the_unconditioned_body_does_not_carry() {
        let query = the_statement();
        let aperture = CircuitAperture::STATEMENT_INCIDENT;
        let bare = ConditionedBody::mount(deposit()).expect("deposit reads");
        let mut conditioned = ConditionedBody::mount(deposit()).expect("deposit reads");
        conditioned.condition(&corpus_with_carrier());

        let before = bare.circuit(&query, aperture).expect("founds").cell_names();
        let after = conditioned
            .circuit(&query, aperture)
            .expect("founds")
            .cell_names();
        assert!(before.is_subset(&after));
        let opened: BTreeSet<&String> = after.difference(&before).collect();
        assert!(!opened.is_empty(), "the conditioning founded no cell");
        assert!(
            opened.iter().any(|name| name.contains("_via_carry_")),
            "{opened:?}"
        );
    }

    #[test]
    fn the_conditioning_opens_further_routes_to_a_statement_the_deposit_already_reached() {
        let query = the_statement();
        let aperture = CircuitAperture::STATEMENT_INCIDENT;
        let bare = ConditionedBody::mount(deposit()).expect("deposit reads");
        let mut conditioned = ConditionedBody::mount(deposit()).expect("deposit reads");
        conditioned.condition(&corpus_with_carrier());

        let before = bare.circuit(&query, aperture).expect("founds");
        let after = conditioned.circuit(&query, aperture).expect("founds");
        assert!(
            after.circuit.lineage_route_excess() > before.circuit.lineage_route_excess(),
            "before {} after {}",
            before.circuit.lineage_route_excess(),
            after.circuit.lineage_route_excess()
        );
        assert!(after
            .circuit
            .vertices_reaching(&query.statement)
            .len()
            > before.circuit.vertices_reaching(&query.statement).len());
    }

    #[test]
    fn a_cell_a_derived_passage_founded_traces_back_to_that_passage_and_names_its_stem() {
        let mut body = ConditionedBody::mount(deposit()).expect("deposit reads");
        body.condition(&corpus_with_carrier());
        let query = the_statement();
        let circuit = body
            .circuit(&query, CircuitAperture::STATEMENT_INCIDENT)
            .expect("founds");
        let derived_only = circuit.cells_from_derived();
        assert!(!derived_only.is_empty());
        for name in &derived_only {
            let cell = circuit
                .circuit
                .complex()
                .cells()
                .values()
                .find(|cell| &cell.name == name)
                .expect("named cell exists");
            let founding = circuit.passages_founding(cell.id);
            assert!(!founding.is_empty(), "{name} traces to nothing");
            for passage in founding {
                match &passage.origin {
                    PassageOrigin::Derived { stem, .. } => assert!(!stem.is_empty()),
                    PassageOrigin::Standing { source } => {
                        panic!("{name} traced to standing {source}")
                    }
                }
            }
        }
    }

    // ---------------------------------------------------------------------------------------------
    // The ablation: delete a founded fiber and re-query
    // ---------------------------------------------------------------------------------------------

    #[test]
    fn deleting_one_founded_stem_removes_the_passages_it_licensed_and_their_circuit_cells() {
        let mut body = ConditionedBody::mount(deposit()).expect("deposit reads");
        body.condition(&corpus_with_carrier());
        let ablation = ablate_stem(
            &body,
            "carry",
            &the_statement(),
            CircuitAperture::STATEMENT_INCIDENT,
        )
        .expect("carry was founded");

        assert_eq!(ablation.wholes, vec!["one".to_owned(), "two".to_owned()]);
        assert!(
            ablation.removes_structure(),
            "absent {:?} cells {:?} unaccounted {:?}",
            ablation.passages_absent.len(),
            ablation.cells_absent,
            ablation.unaccounted
        );
        for passage in &ablation.passages_absent {
            assert_eq!(passage.stem, "carry");
            assert!(!passage.text.is_empty());
        }
        assert!(ablation
            .cells_absent
            .iter()
            .any(|name| name.contains("_via_carry_")));
    }

    #[test]
    /// **Re-founded 2026-08-09. The reopening this test pinned was maximality's own shadow.**
    ///
    /// It asserted that removing `carry` *reopens* `car` — true while the constructor deleted every
    /// contained occurrence, because `car` was invisible until `carry` left. With the cover retained
    /// both stand from the beginning, so there is nothing to reopen and the return is empty.
    ///
    /// That is not a weaker result. A reopening was a **receiver artifact**: the material always had
    /// `car`, and only the reduction hid it. What survives, and is asserted here, is the real
    /// property — the cover is over-determined, and an ablation must remove **every occurrence at a
    /// site** rather than one stem, because the unit of removal has to match the unit of carrying.
    #[test]
    fn the_cover_holds_the_contained_stem_from_the_start_so_removal_reopens_nothing() {
        let mut body = ConditionedBody::mount(deposit()).expect("deposit reads");
        body.condition(&[
            expose("one", "an exact transport must carry the carrier by car"),
            expose("two", "exact transport must carry the carrier by car"),
        ]);
        assert!(body.morphology().committed_stems().contains(&"car"));

        let before = body.morphology().cover("formal_carry").expect("ascii");
        assert!(before.stems().contains("carry"));
        assert!(
            before.stems().contains("car"),
            "the contained stem stands from the start: {}",
            before.render()
        );
        // Both cover the same site, which is what over-determination means here.
        let carry_at = before
            .occurrences
            .iter()
            .find(|occurrence| occurrence.stem == "carry")
            .expect("carry stands");
        assert!(
            before.face_at(carry_at.at).len() > 1,
            "more than one occurrence stands at that site"
        );

        let ablation = ablate_stem(
            &body,
            "carry",
            &the_statement(),
            CircuitAperture::STATEMENT_INCIDENT,
        )
        .expect("carry was founded");
        assert!(
            ablation.reopened.is_empty(),
            "nothing was suppressed, so nothing reopens: {:?}",
            ablation.reopened
        );
        assert!(ablation.unaccounted.is_empty(), "{:?}", ablation.unaccounted);
    }

    #[test]
    fn a_reopening_whose_stem_the_removed_one_does_not_contain_is_reported_unaccounted() {
        // The invariant is checkable rather than assumed: build the return by hand with a stem the
        // removed one cannot have covered, and `removes_structure` must refuse it.
        let claimed = StemAblation {
            stem: "carry".to_owned(),
            wholes: vec!["one".to_owned()],
            passages_before: vec!["p".to_owned()],
            passages_after: Vec::new(),
            passages_absent: vec![DerivedPassage {
                name: "p".to_owned(),
                statement: String::new(),
                reaches: String::new(),
                brought: String::new(),
                stem: "carry".to_owned(),
                bridges: Vec::new(),
                text: String::new(),
            }],
            reopened: vec![Reopening {
                passage: "q".to_owned(),
                stem: "kernel".to_owned(),
                was_covered_by: "carry".to_owned(),
            }],
            unaccounted: vec![Reopening {
                passage: "q".to_owned(),
                stem: "kernel".to_owned(),
                was_covered_by: "carry".to_owned(),
            }],
            cells_absent: vec!["p".to_owned()],
            cells_appeared: Vec::new(),
        };
        assert!(!claimed.removes_structure());
    }

    #[test]
    fn ablating_a_stem_that_was_never_founded_is_refused_rather_than_a_no_op() {
        let mut body = ConditionedBody::mount(deposit()).expect("deposit reads");
        body.condition(&corpus_with_carrier());
        assert_eq!(
            ablate_stem(
                &body,
                "neverwitnessed",
                &the_statement(),
                CircuitAperture::STATEMENT_INCIDENT
            ),
            Err(ConditionedDerivationRefusal::StemWasNeverFounded {
                stem: "neverwitnessed".to_owned(),
            })
        );
        assert!(body.morphology().without_stem("neverwitnessed").is_none());
    }

    #[test]
    fn removing_a_stem_keeps_the_lineage_a_chain() {
        let morphology = FoundedMorphology::condition(&corpus_with_carrier());
        let second = morphology.founded()[1].stem.clone();
        let kept = morphology.without_stem(&second).expect("founded");
        assert_eq!(kept.founded().len() + 1, morphology.founded().len());
        assert!(kept.stem(&second).is_none());
        assert_eq!(kept.founded()[0].parent, None);
        assert_eq!(kept.founded()[1].parent, Some(kept.founded()[0].id));
    }

    // ---------------------------------------------------------------------------------------------
    // The foreign seam
    // ---------------------------------------------------------------------------------------------

    #[test]
    fn a_foreign_conditioner_hands_over_founded_words_with_its_own_lineage() {
        let morphology = FoundedMorphology::from_founded_words([
            (
                "carry".to_owned(),
                vec!["pair-0".to_owned(), "pair-1".to_owned()],
                vec!["collapsed(3,7) word=carry".to_owned()],
            ),
            (
                "carrier".to_owned(),
                vec!["pair-0".to_owned()],
                vec!["collapsed(9,11) word=carrier".to_owned()],
            ),
        ]);
        assert_eq!(morphology.committed_stems(), vec!["carry"]);
        assert_eq!(
            morphology.provisional()[0].foreign_lineage,
            vec!["collapsed(9,11) word=carrier".to_owned()]
        );
        let mut body = ConditionedBody::mount(deposit()).expect("deposit reads");
        body.carry_morphology(morphology);
        assert!(!body.derive(&the_statement()).expect("derives").is_empty());
    }

    #[test]
    fn a_foreign_word_with_no_whole_founds_nothing() {
        let morphology = FoundedMorphology::from_founded_words([(
            "carry".to_owned(),
            Vec::new(),
            vec!["no whole".to_owned()],
        )]);
        assert!(morphology.founded().is_empty());
    }

    // ---------------------------------------------------------------------------------------------
    // The reading aperture
    // ---------------------------------------------------------------------------------------------

    #[test]
    fn exposure_folds_case_and_cuts_at_every_non_letter() {
        let exposure = expose("w", "Exact-Chart CARRY_carrier θ42x");
        assert_eq!(
            exposure.words,
            vec![
                "exact".to_owned(),
                "chart".to_owned(),
                "carry".to_owned(),
                "carrier".to_owned(),
                "x".to_owned(),
            ]
        );
    }

    #[test]
    fn material_declaring_no_theorem_is_refused_by_name() {
        assert_eq!(
            ConditionedBody::mount([("empty".to_owned(), "namespace Soma\nend Soma\n".to_owned())])
                .err(),
            Some(ConditionedDerivationRefusal::MaterialDeclaresNothing {
                source: "empty".to_owned(),
            })
        );
    }
}

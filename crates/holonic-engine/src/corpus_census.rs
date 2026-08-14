//! The lived construction `Π`: what a declared corpus actually wrote, counted and never gated.
//!
//! ## The question this exists to measure
//!
//! Brandon, on why a corpus founds invariants nobody authored:
//!
//! > *"if in the English we use about mathematics, there are certain words that are used
//! > invariantly to refer to a discrete kind of object… If the words are not necessarily hard-coded
//! > as invariants, but the machine experiences them as invariants associated with particular
//! > meanings, then perhaps its language comprehension would implicitly curve around those **iron
//! > recurrences (density)**… The density and invariants it founds are not ours to necessarily
//! > author, they are happenstance of our own writing."*
//!
//! The precedent is `canon/THE_DIALECT.md`: 8,935 messages measured, `holon` 1141, `current` 696,
//! and `FOUND`/`RIDE`/`OPEN` as capitalised primitives **zero**. Nobody authored that reading; it
//! fell out of density.
//!
//! ## Frequency is `Π`, and `Π` is not allowed to gate
//!
//! `reference/holobrochos-a07ff376/src/soma/FORMULA.md:2459`, ratified, and `CLAUDE.md` §13 rule 2:
//! a distribution has four faces — `Π` the lived construction, `Q` the declared quotient,
//! `q_current` the transported testimony, and `G_authored`, the only contaminant. **This module is
//! `Π` and nothing else.** It counts what occurred, per surface form, per whole, per stratum, and it
//! returns every count. Nothing here selects, ranks, thresholds, prunes, or smooths. The one place a
//! count becomes a *quotient* is [`CorpusCensus::density_reading`], which hands the census to
//! `surprisal::read_population` as an embodied standing — `p(t) = N(t) / Σ N` — and receives back a
//! ℚ-linear form over prime axes rather than a number.
//!
//! `CLAUDE.md` §13 rule 2's operative test is jurisdiction, not vocabulary: **a scalar that measures
//! is lawful, a scalar that governs is not.** Every scalar below measures.
//!
//! ## The declared bounds, stated once and named where they bite
//!
//! - **The corpus is the caller's.** [`CorpusCensus::read_declared`] takes the strata — their
//!   roots, their extensions, their labels — and the [`LexicalSpecies`] they are read under. The
//!   organ holds no corpus. [`DECLARED_STRATA`] is *this repository's* four strata, and it is a
//!   declaration three callers outside this module name and pass; nothing here reads it except the
//!   one line of [`CorpusCensus::read`] that exists to keep those callers compiling.
//!
//!   It was not always so. Until 2026-08-09 `read` joined its root with four `&'static str` paths
//!   compiled into this file, `admit` was private, and **every corpus that was not this repository
//!   returned `EmptyStratum`** — a caller's declaration living inside the organ, which is the
//!   species `canon/THE_AUTHORED_LEVEL.md` convicts.
//! - **The stream** is every token: word runs *and* markup runs. Whitespace separates and is not a
//!   token. Under [`LexicalSpecies::LeanSource`] comment text is not in the stream at all and is
//!   returned whole by [`CorpusCensus::comment_bound`].
//! - **The measured population** is the **word** surfaces. Markup surfaces stay in the stream — a
//!   receiver standing next to a `#` must be able to see it — but are not themselves measured.
//!   [`CorpusCensus::markup_bound`] returns exactly what that bound excluded, by count and by
//!   distinct form, so the exclusion is named rather than silent.
//! - **Surfaces are case-sensitive.** `set`, `Set` and `SET` are three surfaces. Folding them would
//!   pre-decide the question the separation reading is asked to answer.
//!
//! ## No absolute frame
//!
//! `CLAUDE.md` §0's second lesson: ten C++ card adapters folded the filesystem path into their rest
//! integrity. The corpus root is a **locator**, supplied by the caller, and it is never folded into
//! any returned reading — every whole is named by its path *relative to the declared root*, so two
//! checkouts at different absolute paths return bit-identical censuses.

use std::collections::BTreeMap;
use std::fs;
use std::path::{Path, PathBuf};

use num_bigint::BigUint;
use serde::{Deserialize, Serialize};

use crate::surprisal::{Support, SurprisalError, read_population};

/// **A frame index into the caller's declared corpus**, in `CLAUDE.md` §0's fourth-lesson sense: an
/// invariant is only visible across two of them.
///
/// The index is all this type carries. What the frame *is* — its label, its root, its extension —
/// is the caller's declaration and is read back off the census through
/// [`CorpusCensus::stratum_label`], never off this type.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct Stratum(pub u8);

#[allow(non_upper_case_globals)]
impl Stratum {
    /// The four frames [`DECLARED_STRATA`] declares. Named here because three callers outside this
    /// module name them by these words; they are that declaration's labels and not this type's.
    pub const Papers: Stratum = Stratum(0);
    pub const Canon: Stratum = Stratum(1);
    pub const Records: Stratum = Stratum(2);
    pub const Seed: Stratum = Stratum(3);

    /// The frame index.
    pub fn index(self) -> usize {
        self.0 as usize
    }

    /// The label [`DECLARED_STRATA`] gave this index. A corpus that is not this repository names
    /// its own frames through [`StratumDeclaration::label`] and reads them back through
    /// [`CorpusCensus::stratum_label`]; this is provenance for the four that predate the
    /// declaration being the caller's.
    pub fn name(self) -> &'static str {
        ["papers", "canon", "records", "seed"]
            .get(self.index())
            .copied()
            .unwrap_or("frame")
    }

    fn bit(self) -> u64 {
        1u64 << self.0
    }
}

/// **Which lexical species a corpus is read under.** A caller's declaration, because the answer is
/// a property of the material and not of this organ.
///
/// The two are each exact on their own material and the wrong one returns a plausible census
/// instead of an error. Measured 2026-08-09 over 3,198,664 octets of Lean — 223 wholes across four
/// declared areas of mathlib, by `examples/the_census_is_pointed_at_a_foreign_corpus.rs` — the two
/// species read the same bytes as:
///
/// ```text
///                              prose      lean-source
///   markup share               46.2%            42.6%
///   `.` occurrences (rank)  32204 (#3)     369 (#163)
///   `₁` standing alone           1773                0
///   bare subscripts              4512               18
///   qualified word surfaces         0             8986
///   comment population         0 / 0   143344 / 6279
/// ```
///
/// Under `Prose` the `.` is the **third most recurrent surface in the corpus**, which is another
/// way of saying no qualified name such as `Nat.succ` survives tokenization at all, and `₁` stands
/// alone 1,773 times because the word rule is `[A-Za-z0-9_]` on **bytes**.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum LexicalSpecies {
    /// Maximal runs of `[A-Za-z0-9_]` are word tokens; maximal runs of any other non-whitespace
    /// character are markup; whitespace separates and produces nothing. Every non-ASCII character
    /// is markup. This is prose about mathematics, which is the corpus [`DECLARED_STRATA`] names.
    Prose,
    /// Lean's own lexical law, and the three clauses are the three ways `Prose` shatters source:
    ///
    /// - **comment-aware.** `--` to end of line and nested `/- … -/`, `/--`, `/-!` included. Comment
    ///   text is not admitted to the stream and is returned whole by
    ///   [`CorpusCensus::comment_bound`] — never silently dropped.
    /// - **`.`-joining.** A `.` *between* two identifier runs continues the run, so `Nat.succ` and
    ///   `Mathlib.Tactic.Ring` are one surface each. A `.` that is not between two such runs stays
    ///   markup, so `(f x).1` splits — a declared bound, not an accident.
    /// - **unicode-continuing.** An identifier begins with an alphabetic character or `_` and
    ///   continues through anything alphanumeric plus `_ ' ! ?`. `₁` is `Nd`/`No` and therefore
    ///   alphanumeric, so `h₁` is one surface; `α` is `Ll` and is a word; `≤`, `→`, `∀` are `Sm`
    ///   and are markup.
    ///
    /// **Declared bound: string literals are not tracked**, so a `--` inside one opens a comment.
    /// It is the bound [`crate::lean_development`] declares for the same reason.
    LeanSource,
}

/// Where one stratum's wholes live, relative to the declared corpus root, and what the caller calls
/// it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct StratumDeclaration {
    pub stratum: Stratum,
    /// The caller's name for this frame. Printed; never folded into a reading.
    pub label: &'static str,
    pub relative_root: &'static str,
    pub extension: &'static str,
    pub recursive: bool,
}

/// **This repository's own corpus, as a caller declares it.** Four strata, whole files, no
/// sampling.
///
/// Nothing in this module reads it except the single line of [`CorpusCensus::read`] that passes it
/// on. It is here rather than in the three drivers that name it because those drivers —
/// `examples/the_iron_tokens_carry_the_field.rs`,
/// `examples/the_token_holds_an_axis_while_its_windows_vary.rs`, and `token_invariance`'s own test
/// fixtures — import it by this path.
pub const DECLARED_STRATA: [StratumDeclaration; 4] = [
    StratumDeclaration {
        stratum: Stratum::Papers,
        label: "papers",
        relative_root: "papers/source/mathematics",
        extension: "typ",
        recursive: true,
    },
    StratumDeclaration {
        stratum: Stratum::Canon,
        label: "canon",
        relative_root: "canon",
        extension: "md",
        recursive: false,
    },
    StratumDeclaration {
        stratum: Stratum::Records,
        label: "records",
        relative_root: "research/records",
        extension: "md",
        recursive: false,
    },
    StratumDeclaration {
        stratum: Stratum::Seed,
        label: "seed",
        relative_root: "reference/pureholonics-seed",
        extension: "md",
        recursive: true,
    },
];

/// An interned surface form. Case-sensitive, by declaration.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct SurfaceId(pub u32);

/// The orthographic kind of a surface. A declared quotient of the vocabulary — six values, and the
/// coarsest thing a receiver can say about *what kind of object* is standing at a position.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum Kind {
    /// A word run with no uppercase letter and at least one lowercase letter.
    Lower,
    /// A word run whose first character is uppercase and which carries no further uppercase.
    Capitalised,
    /// A word run with uppercase letters and no lowercase letters. A single uppercase letter is
    /// AllCaps by this rule and not `Capitalised`; the boundary is declared here rather than left
    /// to a reader's intuition, because `A` is a real and common surface in this corpus.
    AllCaps,
    /// A word run with internal case changes that is neither of the above.
    Mixed,
    /// A word run of ASCII digits only.
    Numeral,
    /// A run of non-word, non-whitespace characters.
    Markup,
}

impl Kind {
    pub fn name(self) -> &'static str {
        match self {
            Kind::Lower => "lower",
            Kind::Capitalised => "Capital",
            Kind::AllCaps => "ALLCAPS",
            Kind::Mixed => "Mixed",
            Kind::Numeral => "numeral",
            Kind::Markup => "markup",
        }
    }

    pub fn is_word(self) -> bool {
        self != Kind::Markup
    }

    fn observation(self) -> u64 {
        self as u64
    }
}

/// The declared length bands. Exact integer boundaries, stated here and nowhere else.
pub const WEIGHT_BANDS: [(usize, usize, &str); 5] = [
    (1, 1, "1"),
    (2, 3, "2-3"),
    (4, 6, "4-6"),
    (7, 10, "7-10"),
    (11, usize::MAX, "11+"),
];

/// The length band of a surface of `length` characters.
pub fn weight_band(length: usize) -> u64 {
    for (index, (low, high, _)) in WEIGHT_BANDS.iter().enumerate() {
        if length >= *low && length <= *high {
            return index as u64;
        }
    }
    (WEIGHT_BANDS.len() - 1) as u64
}

pub fn weight_band_name(band: u64) -> &'static str {
    WEIGHT_BANDS
        .get(band as usize)
        .map(|(_, _, name)| *name)
        .unwrap_or("?")
}

/// The **density band** of an occurrence count: `floor(log2 n)`, computed as a bit length.
///
/// Exact integer arithmetic on a `u64` — no logarithm is evaluated and no float is constructed.
/// `0 -> 0`, `1 -> 0`, `2..3 -> 1`, `4..7 -> 2`, and so on. This is the one receiver axis that is
/// **derived from `Π` itself** rather than from orthography, which is the point: Brandon's question
/// is whether comprehension curves around *iron recurrences (density)*, so density must be
/// something a receiver can see, not only something a reader tabulates.
pub fn density_band(occurrences: u64) -> u64 {
    if occurrences <= 1 {
        return 0;
    }
    (u64::BITS - occurrences.leading_zeros() - 1) as u64
}

/// One whole: a file, its stratum, its name relative to the declared root, and its token stream.
#[derive(Clone, Debug)]
pub struct WholeRecord {
    pub stratum: Stratum,
    pub relative_path: String,
    pub stream: Vec<SurfaceId>,
}

/// What the markup bound excluded, named rather than dropped.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MarkupBound {
    pub markup_occurrences: BigUint,
    pub distinct_markup_surfaces: usize,
    /// The most-recurrent markup surfaces, exhibited so the bound is inspectable.
    pub exhibited: Vec<(String, BigUint)>,
}

/// What the comment clause took out of the stream, named rather than dropped.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CommentBound {
    pub comment_occurrences: BigUint,
    pub distinct_comment_surfaces: usize,
    /// The most-recurrent surfaces occurring inside comment text.
    pub exhibited: Vec<(String, BigUint)>,
}

/// One token's density reading. Occurrences, reach across wholes and strata, and the exact
/// symbolic surprisal of its embodied probability.
#[derive(Clone, Debug)]
pub struct DensityRow {
    pub surface: SurfaceId,
    pub occurrences: BigUint,
    pub distinct_wholes: u32,
    pub strata: Vec<Stratum>,
    /// `S(p) = -log2(N(t) / ΣN)` as a ℚ-linear form over prime axes. Never evaluated.
    pub surprisal: Support,
}

/// The corpus, counted.
#[derive(Clone, Debug)]
pub struct CorpusCensus {
    root: PathBuf,
    species: LexicalSpecies,
    labels: Vec<String>,
    surfaces: Vec<String>,
    kinds: Vec<Kind>,
    interner: BTreeMap<String, SurfaceId>,
    wholes: Vec<WholeRecord>,
    counts: Vec<u64>,
    distinct_wholes: Vec<u32>,
    strata_mask: Vec<u64>,
    last_whole: Vec<i64>,
    sites: Vec<Vec<(u32, u32)>>,
    word_occurrences: u64,
    markup_occurrences: u64,
    comment_counts: BTreeMap<String, u64>,
    comment_occurrences: u64,
}

impl CorpusCensus {
    /// This repository's own four strata, read as prose.
    ///
    /// **One line, and it is the whole of what this organ knows about any corpus.**
    /// [`DECLARED_STRATA`] is a caller's declaration that happens to be published beside the organ;
    /// `token_invariance`'s fixtures and two field drivers name it by this path, which is why the
    /// convenience survives. New callers declare their own and use [`Self::read_declared`].
    pub fn read(root: &Path) -> Result<Self, CensusError> {
        Self::read_declared(root, &DECLARED_STRATA, LexicalSpecies::Prose)
    }

    /// Read a **caller-declared** corpus rooted at `root`. Every file under every declared stratum
    /// root with the declared extension is read whole, under the declared species.
    pub fn read_declared(
        root: &Path,
        strata: &[StratumDeclaration],
        species: LexicalSpecies,
    ) -> Result<Self, CensusError> {
        let mut census = Self::declaring(strata, species)?;
        census.root = root.to_path_buf();
        for declaration in strata {
            let stratum_root = root.join(declaration.relative_root);
            let mut paths = Vec::new();
            collect(
                &stratum_root,
                declaration.extension,
                declaration.recursive,
                &mut paths,
            )?;
            paths.sort();
            if paths.is_empty() {
                return Err(CensusError::EmptyStratum {
                    stratum: declaration.stratum,
                    root: declaration.relative_root,
                });
            }
            for path in paths {
                let text = fs::read_to_string(&path).map_err(|error| {
                    CensusError::Unreadable(path.display().to_string(), error.to_string())
                })?;
                let relative = path
                    .strip_prefix(root)
                    .unwrap_or(&path)
                    .display()
                    .to_string();
                census.admit(declaration.stratum, relative, &text);
            }
        }
        Ok(census)
    }

    /// An empty census over a caller-declared frame population, with **no filesystem root at all**.
    ///
    /// The wholes are then handed in by [`Self::admit_whole`]. `CLAUDE.md` §0's second lesson is
    /// that a lineage may carry no absolute frame; a corpus that never touches a path cannot carry
    /// one even by accident.
    pub fn declaring(
        strata: &[StratumDeclaration],
        species: LexicalSpecies,
    ) -> Result<Self, CensusError> {
        if strata.is_empty() {
            return Err(CensusError::NoStrataDeclared);
        }
        let mut labels: Vec<String> = Vec::new();
        for declaration in strata {
            let index = declaration.stratum.index();
            if index >= u64::BITS as usize {
                return Err(CensusError::FrameBeyondCarrier {
                    index,
                    frames: u64::BITS as usize,
                });
            }
            if labels.len() <= index {
                labels.resize(index + 1, String::new());
            }
            if !labels[index].is_empty() {
                return Err(CensusError::FrameDeclaredTwice {
                    index,
                    held: labels[index].clone(),
                    offered: declaration.label.to_owned(),
                });
            }
            labels[index] = declaration.label.to_owned();
        }
        Ok(Self {
            root: PathBuf::new(),
            species,
            labels,
            surfaces: Vec::new(),
            kinds: Vec::new(),
            interner: BTreeMap::new(),
            wholes: Vec::new(),
            counts: Vec::new(),
            distinct_wholes: Vec::new(),
            strata_mask: Vec::new(),
            last_whole: Vec::new(),
            sites: Vec::new(),
            word_occurrences: 0,
            markup_occurrences: 0,
            comment_counts: BTreeMap::new(),
            comment_occurrences: 0,
        })
    }

    /// Admit one whole the caller supplies directly. The counterpart of [`Self::declaring`], and
    /// the reason a corpus need not be a directory tree at all.
    pub fn admit_whole(&mut self, stratum: Stratum, name: String, text: &str) {
        self.admit(stratum, name, text);
    }

    fn admit(&mut self, stratum: Stratum, relative_path: String, text: &str) {
        let whole_index = self.wholes.len() as u32;
        let mut stream = Vec::new();
        for token in tokenize_as(text, self.species) {
            if token.commentary {
                let slot = self
                    .comment_counts
                    .entry(token.text.to_owned())
                    .or_insert(0);
                *slot += 1;
                self.comment_occurrences += 1;
                continue;
            }
            let id = self.intern(token.text);
            let slot = id.0 as usize;
            self.counts[slot] += 1;
            if self.last_whole[slot] != whole_index as i64 {
                self.last_whole[slot] = whole_index as i64;
                self.distinct_wholes[slot] += 1;
            }
            self.strata_mask[slot] |= stratum.bit();
            if self.kinds[slot].is_word() {
                self.word_occurrences += 1;
                self.sites[slot].push((whole_index, stream.len() as u32));
            } else {
                self.markup_occurrences += 1;
            }
            stream.push(id);
        }
        self.wholes.push(WholeRecord {
            stratum,
            relative_path,
            stream,
        });
    }

    fn intern(&mut self, surface: &str) -> SurfaceId {
        if let Some(id) = self.interner.get(surface) {
            return *id;
        }
        let id = SurfaceId(self.surfaces.len() as u32);
        self.surfaces.push(surface.to_owned());
        self.kinds.push(classify_as(surface, self.species));
        self.counts.push(0);
        self.distinct_wholes.push(0);
        self.strata_mask.push(0);
        self.last_whole.push(-1);
        self.sites.push(Vec::new());
        self.interner.insert(surface.to_owned(), id);
        id
    }

    pub fn root(&self) -> &Path {
        &self.root
    }

    /// The species this corpus was declared to be read under.
    pub fn species(&self) -> LexicalSpecies {
        self.species
    }

    /// The caller's label for one declared frame.
    pub fn stratum_label(&self, stratum: Stratum) -> &str {
        self.labels
            .get(stratum.index())
            .map(String::as_str)
            .unwrap_or("")
    }

    /// Every frame the caller declared, in index order.
    pub fn declared_strata(&self) -> Vec<Stratum> {
        (0..self.labels.len())
            .filter(|index| !self.labels[*index].is_empty())
            .map(|index| Stratum(index as u8))
            .collect()
    }

    pub fn wholes(&self) -> &[WholeRecord] {
        &self.wholes
    }

    pub fn surface(&self, id: SurfaceId) -> &str {
        &self.surfaces[id.0 as usize]
    }

    pub fn kind(&self, id: SurfaceId) -> Kind {
        self.kinds[id.0 as usize]
    }

    pub fn occurrences(&self, id: SurfaceId) -> u64 {
        self.counts[id.0 as usize]
    }

    pub fn distinct_wholes(&self, id: SurfaceId) -> u32 {
        self.distinct_wholes[id.0 as usize]
    }

    pub fn strata(&self, id: SurfaceId) -> Vec<Stratum> {
        self.declared_strata()
            .into_iter()
            .filter(|stratum| self.strata_mask[id.0 as usize] & stratum.bit() != 0)
            .collect()
    }

    /// Every recorded occurrence of a word surface, as `(whole, position)`. Corpus order.
    pub fn sites(&self, id: SurfaceId) -> &[(u32, u32)] {
        &self.sites[id.0 as usize]
    }

    pub fn lookup(&self, surface: &str) -> Option<SurfaceId> {
        self.interner.get(surface).copied()
    }

    /// Every surface, word and markup alike.
    pub fn all_surfaces(&self) -> impl Iterator<Item = SurfaceId> + '_ {
        (0..self.surfaces.len() as u32).map(SurfaceId)
    }

    /// The **measured population**: the word surfaces, in surface order.
    pub fn word_surfaces(&self) -> Vec<SurfaceId> {
        self.all_surfaces()
            .filter(|id| self.kind(*id).is_word())
            .collect()
    }

    pub fn word_occurrences(&self) -> u64 {
        self.word_occurrences
    }

    pub fn total_occurrences(&self) -> u64 {
        self.word_occurrences + self.markup_occurrences
    }

    /// What the comment clause of [`LexicalSpecies::LeanSource`] took out of the stream, by count
    /// and by exhibited form.
    ///
    /// Under [`LexicalSpecies::Prose`] there is no comment clause and this population is empty:
    /// comment prose is in the stream, indistinguishable from what the source actually named.
    pub fn comment_bound(&self, exhibit: usize) -> CommentBound {
        let mut population: Vec<(u64, &str)> = self
            .comment_counts
            .iter()
            .map(|(surface, count)| (*count, surface.as_str()))
            .collect();
        population.sort_by(|left, right| right.0.cmp(&left.0).then(left.1.cmp(right.1)));
        CommentBound {
            comment_occurrences: BigUint::from(self.comment_occurrences),
            distinct_comment_surfaces: population.len(),
            exhibited: population
                .iter()
                .take(exhibit)
                .map(|(count, surface)| ((*surface).to_owned(), BigUint::from(*count)))
                .collect(),
        }
    }

    /// What the measured-population bound excluded, by count and by exhibited form.
    pub fn markup_bound(&self, exhibit: usize) -> MarkupBound {
        let mut markup: Vec<(u64, SurfaceId)> = self
            .all_surfaces()
            .filter(|id| !self.kind(*id).is_word())
            .map(|id| (self.occurrences(id), id))
            .collect();
        markup.sort_by(|left, right| right.0.cmp(&left.0).then(left.1.cmp(&right.1)));
        MarkupBound {
            markup_occurrences: BigUint::from(self.markup_occurrences),
            distinct_markup_surfaces: markup.len(),
            exhibited: markup
                .iter()
                .take(exhibit)
                .map(|(count, id)| (self.surface(*id).to_owned(), BigUint::from(*count)))
                .collect(),
        }
    }

    /// The embodied standing over the measured population: `event -> N(event)`.
    ///
    /// This is `Π` handed to `surprisal` as a standing. The quotient `p = N/ΣN` is taken there.
    pub fn word_population(&self) -> BTreeMap<u64, BigUint> {
        self.word_surfaces()
            .into_iter()
            .map(|id| (id.0 as u64, BigUint::from(self.occurrences(id))))
            .collect()
    }

    /// The same standing restricted to one stratum — the second frame.
    pub fn stratum_population(&self, stratum: Stratum) -> BTreeMap<u64, BigUint> {
        let mut population: BTreeMap<u64, BigUint> = BTreeMap::new();
        for whole in &self.wholes {
            if whole.stratum != stratum {
                continue;
            }
            for surface in &whole.stream {
                if self.kind(*surface).is_word() {
                    *population
                        .entry(surface.0 as u64)
                        .or_insert_with(BigUint::default) += BigUint::from(1u32);
                }
            }
        }
        population
    }

    /// The density reading: occurrences, reach, and the exact symbolic surprisal, for **every**
    /// member of the measured population. Nothing is selected and nothing is omitted.
    pub fn density_reading(&self) -> Result<BTreeMap<SurfaceId, DensityRow>, SurprisalError> {
        let population = self.word_population();
        let read = read_population(&population, &population)?;
        let mut rows = BTreeMap::new();
        for id in self.word_surfaces() {
            let support = read
                .get(&(id.0 as u64))
                .cloned()
                .unwrap_or(Support::Unsupported);
            rows.insert(
                id,
                DensityRow {
                    surface: id,
                    occurrences: BigUint::from(self.occurrences(id)),
                    distinct_wholes: self.distinct_wholes(id),
                    strata: self.strata(id),
                    surprisal: support,
                },
            );
        }
        Ok(rows)
    }

    /// The receiver signature of the surface standing at one position: `(kind, weight, density)`.
    ///
    /// This is what every receiver in the declared family factors through, and the three coordinates
    /// are read by three separate receivers so that each one's contribution is separately ablatable.
    pub fn signature(&self, id: SurfaceId) -> (u64, u64, u64) {
        (
            self.kind(id).observation(),
            weight_band(self.surface(id).chars().count()),
            density_band(self.occurrences(id)),
        )
    }
}

/// One lexed token and whether it stood inside comment text.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Lexed<'a> {
    pub text: &'a str,
    /// True only under [`LexicalSpecies::LeanSource`], and only inside a `--` or `/- … -/` run.
    pub commentary: bool,
}

/// The tokenizer of [`LexicalSpecies::Prose`]: maximal runs of `[A-Za-z0-9_]` are word tokens,
/// maximal runs of any other non-whitespace characters are markup tokens, whitespace separates and
/// produces nothing. Nothing is ever commentary.
pub fn tokenize(text: &str) -> Vec<&str> {
    let bytes = text.as_bytes();
    let mut tokens = Vec::new();
    let mut index = 0usize;
    while index < bytes.len() {
        let byte = bytes[index];
        if (byte as char).is_ascii_whitespace() {
            index += 1;
            continue;
        }
        let word = is_word_byte(byte);
        let start = index;
        while index < bytes.len() {
            let next = bytes[index];
            if (next as char).is_ascii_whitespace() || is_word_byte(next) != word {
                break;
            }
            index += 1;
        }
        // A multi-byte character's continuation bytes are neither whitespace nor word bytes, so a
        // non-ASCII run stays inside one markup token and the slice stays on a character boundary.
        tokens.push(&text[start..index]);
    }
    tokens
}

/// The declared tokenizer of one species.
pub fn tokenize_as(text: &str, species: LexicalSpecies) -> Vec<Lexed<'_>> {
    match species {
        LexicalSpecies::Prose => tokenize(text)
            .into_iter()
            .map(|text| Lexed {
                text,
                commentary: false,
            })
            .collect(),
        LexicalSpecies::LeanSource => tokenize_lean(text),
    }
}

fn is_word_byte(byte: u8) -> bool {
    byte.is_ascii_alphanumeric() || byte == b'_'
}

/// A subscript or superscript modifier: `₀-₉`, the letter-like subscripts `ₐ-ₜ` and `ᵢ-ᵪ`, and
/// superscript `ⁿ`. These **continue** an identifier and never open one.
///
/// Lean's own `isLetterLike` admits them as identifier heads, and the reading declares the narrower
/// rule deliberately: mathlib writes `→ₗ[R]`, `≃ₐ`, `∑ᵢ`, where the modifier belongs to the
/// notation on its left. Admitting it as a head sheds a spurious one-character word off every such
/// arrow — measured at 511 for `ₖ` and 461 for `ₘ` before this clause existed.
fn is_subscript_modifier(character: char) -> bool {
    ('\u{2080}'..='\u{209C}').contains(&character)
        || ('\u{1D62}'..='\u{1D6A}').contains(&character)
        || character == '\u{207F}'
}

/// An identifier's first character.
fn is_lean_identifier_start(character: char) -> bool {
    (character.is_alphabetic() || character == '_') && !is_subscript_modifier(character)
}

/// An identifier's continuation, by Lean's rule. `is_alphanumeric` is `Alphabetic | Nd | Nl | No`,
/// which is why the subscript `₁` (`No`) continues an identifier and `≤` (`Sm`) does not.
fn is_lean_identifier_rest(character: char) -> bool {
    character.is_alphanumeric()
        || character == '_'
        || character == '\''
        || character == '!'
        || character == '?'
}

/// A run this species opens a token on: an identifier head, or an ASCII digit for a literal.
fn opens_a_lean_word(character: char) -> bool {
    is_lean_identifier_start(character) || character.is_ascii_digit()
}

fn opens_a_comment(bytes: &[u8], at: usize) -> bool {
    matches!(
        (bytes.get(at), bytes.get(at + 1)),
        (Some(b'-'), Some(b'-')) | (Some(b'/'), Some(b'-'))
    )
}

/// The tokenizer of [`LexicalSpecies::LeanSource`]. The three clauses are documented on the species.
fn tokenize_lean(text: &str) -> Vec<Lexed<'_>> {
    let bytes = text.as_bytes();
    let mut tokens = Vec::new();
    let mut index = 0usize;
    while index < bytes.len() {
        if bytes[index] == b'-' && bytes.get(index + 1) == Some(&b'-') {
            let end = text[index..]
                .find('\n')
                .map(|at| index + at)
                .unwrap_or(bytes.len());
            lex_lean_run(&text[index..end], true, &mut tokens);
            index = end;
            continue;
        }
        if bytes[index] == b'/' && bytes.get(index + 1) == Some(&b'-') {
            let start = index;
            let mut depth = 0usize;
            let mut scan = index;
            while scan < bytes.len() {
                if bytes[scan] == b'/' && bytes.get(scan + 1) == Some(&b'-') {
                    depth += 1;
                    scan += 2;
                    continue;
                }
                if bytes[scan] == b'-' && bytes.get(scan + 1) == Some(&b'/') {
                    depth -= 1;
                    scan += 2;
                    if depth == 0 {
                        break;
                    }
                    continue;
                }
                scan += 1;
            }
            // An unterminated block runs to the end of the whole; the text said so and the reading
            // does not repair it.
            let end = scan.min(bytes.len());
            lex_lean_run(&text[start..end], true, &mut tokens);
            index = end;
            continue;
        }

        let character = text[index..].chars().next().expect("index is a boundary");
        if character.is_whitespace() {
            index += character.len_utf8();
            continue;
        }
        if opens_a_lean_word(character) {
            let start = index;
            index = lean_word_end(text, index);
            tokens.push(Lexed {
                text: &text[start..index],
                commentary: false,
            });
            continue;
        }
        let start = index;
        while index < bytes.len() {
            if opens_a_comment(bytes, index) {
                break;
            }
            let next = text[index..].chars().next().expect("index is a boundary");
            if next.is_whitespace() || opens_a_lean_word(next) {
                break;
            }
            index += next.len_utf8();
        }
        tokens.push(Lexed {
            text: &text[start..index],
            commentary: false,
        });
    }
    tokens
}

/// Split one already-delimited run — code or comment — with no comment detection of its own.
fn lex_lean_run<'a>(run: &'a str, commentary: bool, into: &mut Vec<Lexed<'a>>) {
    let bytes = run.as_bytes();
    let mut index = 0usize;
    while index < bytes.len() {
        let character = run[index..].chars().next().expect("index is a boundary");
        if character.is_whitespace() {
            index += character.len_utf8();
            continue;
        }
        let start = index;
        if opens_a_lean_word(character) {
            index = lean_word_end(run, index);
        } else {
            while index < bytes.len() {
                let next = run[index..].chars().next().expect("index is a boundary");
                if next.is_whitespace() || opens_a_lean_word(next) {
                    break;
                }
                index += next.len_utf8();
            }
        }
        into.push(Lexed {
            text: &run[start..index],
            commentary,
        });
    }
}

/// The byte index one past the identifier or literal beginning at `start`, `.`-joins included.
fn lean_word_end(text: &str, start: usize) -> usize {
    let mut index = start + text[start..].chars().next().map_or(0, char::len_utf8);
    loop {
        while let Some(character) = text[index..].chars().next() {
            if !is_lean_identifier_rest(character) {
                break;
            }
            index += character.len_utf8();
        }
        // A `.` continues the run only **between** two identifier runs, so `Nat.succ` is one
        // surface and the `.1` of `(f x).1` is not.
        if text[index..].starts_with('.') {
            if let Some(next) = text[index + 1..].chars().next() {
                if is_lean_identifier_rest(next) {
                    index += 1;
                    continue;
                }
            }
        }
        return index;
    }
}

/// The declared orthographic classification under [`LexicalSpecies::Prose`].
pub fn classify(surface: &str) -> Kind {
    if !surface.bytes().all(is_word_byte) {
        return Kind::Markup;
    }
    let mut upper = 0usize;
    let mut lower = 0usize;
    let mut digit = 0usize;
    for byte in surface.bytes() {
        if byte.is_ascii_uppercase() {
            upper += 1;
        } else if byte.is_ascii_lowercase() {
            lower += 1;
        } else if byte.is_ascii_digit() {
            digit += 1;
        }
    }
    if upper == 0 && lower == 0 && digit > 0 {
        return Kind::Numeral;
    }
    if upper == 0 {
        return Kind::Lower;
    }
    if lower == 0 {
        return Kind::AllCaps;
    }
    let first_upper = surface
        .bytes()
        .next()
        .is_some_and(|b| b.is_ascii_uppercase());
    if first_upper && upper == 1 {
        Kind::Capitalised
    } else {
        Kind::Mixed
    }
}

/// The declared orthographic classification of one species.
pub fn classify_as(surface: &str, species: LexicalSpecies) -> Kind {
    match species {
        LexicalSpecies::Prose => classify(surface),
        LexicalSpecies::LeanSource => classify_lean(surface),
    }
}

fn classify_lean(surface: &str) -> Kind {
    let Some(first) = surface.chars().next() else {
        return Kind::Markup;
    };
    if !opens_a_lean_word(first) {
        return Kind::Markup;
    }
    if !surface
        .chars()
        .all(|character| is_lean_identifier_rest(character) || character == '.')
    {
        return Kind::Markup;
    }
    let mut upper = 0usize;
    let mut lower = 0usize;
    let mut digit = 0usize;
    for character in surface.chars() {
        if character.is_uppercase() {
            upper += 1;
        } else if character.is_lowercase() {
            lower += 1;
        } else if character.is_numeric() {
            digit += 1;
        }
    }
    if upper == 0 && lower == 0 && digit > 0 {
        return Kind::Numeral;
    }
    if upper == 0 {
        return Kind::Lower;
    }
    if lower == 0 {
        return Kind::AllCaps;
    }
    if first.is_uppercase() && upper == 1 {
        Kind::Capitalised
    } else {
        Kind::Mixed
    }
}

fn collect(
    directory: &Path,
    extension: &str,
    recursive: bool,
    into: &mut Vec<PathBuf>,
) -> Result<(), CensusError> {
    let entries = fs::read_dir(directory).map_err(|error| {
        CensusError::Unreadable(directory.display().to_string(), error.to_string())
    })?;
    for entry in entries {
        let entry = entry.map_err(|error| {
            CensusError::Unreadable(directory.display().to_string(), error.to_string())
        })?;
        let path = entry.path();
        if path.is_dir() {
            if recursive {
                collect(&path, extension, recursive, into)?;
            }
        } else if path.extension().and_then(|value| value.to_str()) == Some(extension) {
            into.push(path);
        }
    }
    Ok(())
}

#[derive(Clone, Debug, PartialEq, Eq, thiserror::Error)]
pub enum CensusError {
    #[error("the declared corpus root {0} could not be read: {1}")]
    Unreadable(String, String),
    #[error("the declared stratum {stratum:?} at {root} holds no wholes")]
    EmptyStratum {
        stratum: Stratum,
        root: &'static str,
    },
    /// A corpus of no frames. `CLAUDE.md` §0's fourth lesson is that an invariant is only visible
    /// across two of them; zero is not a corpus at all.
    #[error("no stratum was declared: a corpus is the caller's declaration and this one is empty")]
    NoStrataDeclared,
    /// Two declarations claiming one frame index would have merged silently into one mask bit.
    #[error("frame {index} is declared twice: {held} and {offered}")]
    FrameDeclaredTwice {
        index: usize,
        held: String,
        offered: String,
    },
    /// The reach mask is one `u64` per surface, so the carrier holds `u64::BITS` frames. An ABI
    /// fact of the mask, reported with the width it came from rather than as a bare number.
    #[error("frame {index} is past the {frames} the reach mask carries")]
    FrameBeyondCarrier { index: usize, frames: usize },
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_tokenizer_splits_word_runs_from_markup_runs_and_drops_whitespace() {
        assert_eq!(
            tokenize("arxiv.org/abs/2607.01 **holon**"),
            vec![
                "arxiv", ".", "org", "/", "abs", "/", "2607", ".", "01", "**", "holon", "**"
            ]
        );
        assert_eq!(tokenize("   \n\t "), Vec::<&str>::new());
    }

    /// A non-ASCII run stays inside one markup token and the slice stays on a character boundary.
    #[test]
    fn a_non_ascii_run_does_not_split_a_character() {
        let tokens = tokenize("α → β and x");
        assert_eq!(tokens, vec!["α", "→", "β", "and", "x"]);
    }

    #[test]
    fn the_orthographic_classes_are_disjoint_and_exhaustive_on_the_declared_alphabet() {
        assert_eq!(classify("holon"), Kind::Lower);
        assert_eq!(classify("Holon"), Kind::Capitalised);
        // The declared boundary case: no lowercase letter means AllCaps, including a single letter.
        assert_eq!(classify("A"), Kind::AllCaps);
        assert_eq!(classify("FOUND"), Kind::AllCaps);
        assert_eq!(classify("THE_QUOTE_NETWORK"), Kind::AllCaps);
        assert_eq!(classify("arXiv"), Kind::Mixed);
        assert_eq!(classify("2026"), Kind::Numeral);
        assert_eq!(classify("x1"), Kind::Lower);
        assert_eq!(classify("07T17"), Kind::AllCaps);
        assert_eq!(classify("**"), Kind::Markup);
        assert_eq!(classify("α"), Kind::Markup);
    }

    /// The density band is `floor(log2 n)` computed with integers only. No logarithm is evaluated
    /// anywhere and the boundaries are exact powers of two.
    #[test]
    fn the_density_band_is_a_bit_length_and_its_boundaries_are_exact_powers_of_two() {
        assert_eq!(density_band(0), 0);
        assert_eq!(density_band(1), 0);
        assert_eq!(density_band(2), 1);
        assert_eq!(density_band(3), 1);
        assert_eq!(density_band(4), 2);
        assert_eq!(density_band(7), 2);
        assert_eq!(density_band(8), 3);
        for exponent in 1..40u32 {
            let boundary = 1u64 << exponent;
            assert_eq!(density_band(boundary - 1), (exponent - 1) as u64);
            assert_eq!(density_band(boundary), exponent as u64);
        }
    }

    // ------------------------------------------------------------------ the declared species

    /// One line of real Lean, carrying every clause at once: a qualified name, a subscripted
    /// binder, a doc comment, and unicode notation.
    const LEAN_LINE: &str = "/-- The bound. -/\ntheorem IsGLB.between (h₁ : a ≤ b) : Nat.succ 0 ≤ b := by\n  simp [Nat.succ_le_of_lt] -- close it\n";

    #[test]
    fn the_prose_species_is_the_historical_tokenizer_bit_for_bit() {
        let carried: Vec<&str> = tokenize_as(LEAN_LINE, LexicalSpecies::Prose)
            .into_iter()
            .map(|token| token.text)
            .collect();
        assert_eq!(carried, tokenize(LEAN_LINE));
        assert!(
            tokenize_as(LEAN_LINE, LexicalSpecies::Prose)
                .iter()
                .all(|token| !token.commentary),
            "prose has no comment clause"
        );
    }

    /// The three clauses, each shown to come apart from the prose reading on the same bytes.
    #[test]
    fn the_lean_species_joins_a_qualified_name_keeps_a_subscript_and_lifts_the_comment() {
        let prose = tokenize(LEAN_LINE);
        let lean = tokenize_as(LEAN_LINE, LexicalSpecies::LeanSource);
        let code: Vec<&str> = lean
            .iter()
            .filter(|token| !token.commentary)
            .map(|token| token.text)
            .collect();

        // `.`-joining. Prose shatters `Nat.succ_le_of_lt` into three surfaces and a dot.
        assert!(prose.contains(&"Nat") && prose.contains(&"."), "{prose:?}");
        assert!(!prose.contains(&"Nat.succ_le_of_lt"), "{prose:?}");
        assert!(code.contains(&"Nat.succ_le_of_lt"), "{code:?}");
        assert!(code.contains(&"IsGLB.between"), "{code:?}");

        // unicode continuation. `₁` is `No`, so it is alphanumeric and continues `h`.
        assert!(prose.contains(&"h") && prose.contains(&"₁"), "{prose:?}");
        assert!(code.contains(&"h₁"), "{code:?}");
        assert!(!code.contains(&"₁"), "{code:?}");

        // comment awareness. `--`, `/--`, `-/` and the English between them leave the stream.
        assert!(
            prose.contains(&"The") && prose.contains(&"close"),
            "{prose:?}"
        );
        assert!(
            !code.contains(&"The") && !code.contains(&"close"),
            "{code:?}"
        );
        let commentary: Vec<&str> = lean
            .iter()
            .filter(|token| token.commentary)
            .map(|token| token.text)
            .collect();
        assert!(commentary.contains(&"The"), "{commentary:?}");
        assert!(commentary.contains(&"close"), "{commentary:?}");
        assert!(commentary.contains(&"/--"), "{commentary:?}");

        // `≤` is `Sm` and stays markup under both.
        assert_eq!(classify_as("≤", LexicalSpecies::LeanSource), Kind::Markup);
        assert_eq!(classify_as("h₁", LexicalSpecies::LeanSource), Kind::Lower);
        assert_eq!(
            classify_as("Nat.succ_le_of_lt", LexicalSpecies::LeanSource),
            Kind::Capitalised
        );
        // `α` is `Ll`: a Lean type variable is a word, and under prose it is markup.
        assert_eq!(classify_as("α", LexicalSpecies::LeanSource), Kind::Lower);
        assert_eq!(classify_as("α", LexicalSpecies::Prose), Kind::Markup);
    }

    /// A subscript continues an identifier and never opens one, so mathlib's `→ₗ[R]` keeps its
    /// modifier instead of shedding a one-character word.
    #[test]
    fn a_subscript_continues_an_identifier_and_never_opens_one() {
        let carried: Vec<&str> = tokenize_as("f →ₗ[R] g and μₖ", LexicalSpecies::LeanSource)
            .into_iter()
            .map(|token| token.text)
            .collect();
        assert_eq!(carried, vec!["f", "→ₗ[", "R", "]", "g", "and", "μₖ"]);
        assert_eq!(classify_as("→ₗ[", LexicalSpecies::LeanSource), Kind::Markup);
        assert_eq!(classify_as("μₖ", LexicalSpecies::LeanSource), Kind::Lower);
    }

    /// A `.` that is not between two identifier runs stays markup. The declared bound, pinned so it
    /// cannot drift into a silent join.
    #[test]
    fn a_dot_joins_only_between_two_identifier_runs() {
        let carried: Vec<&str> = tokenize_as("(f x).1 ‹a› Nat.succ", LexicalSpecies::LeanSource)
            .into_iter()
            .map(|token| token.text)
            .collect();
        assert_eq!(
            carried,
            vec!["(", "f", "x", ").", "1", "‹", "a", "›", "Nat.succ"]
        );
    }

    /// A nested `/- /- … -/ -/` closes at its own depth and not at the first `-/`.
    #[test]
    fn a_nested_block_comment_closes_at_its_own_depth() {
        let carried = tokenize_as(
            "/- outer /- inner -/ still -/ code",
            LexicalSpecies::LeanSource,
        );
        let code: Vec<&str> = carried
            .iter()
            .filter(|token| !token.commentary)
            .map(|token| token.text)
            .collect();
        assert_eq!(code, vec!["code"]);
        assert!(
            carried
                .iter()
                .any(|token| token.text == "still" && token.commentary)
        );
    }

    // ------------------------------------------------------------------ the caller's corpus

    fn lean_wholes() -> CorpusCensus {
        let declaration = [StratumDeclaration {
            stratum: Stratum(0),
            label: "development",
            relative_root: "",
            extension: "lean",
            recursive: false,
        }];
        let mut census =
            CorpusCensus::declaring(&declaration, LexicalSpecies::LeanSource).expect("declared");
        census.admit_whole(Stratum(0), "one.lean".to_owned(), LEAN_LINE);
        census
    }

    #[test]
    fn a_caller_declared_corpus_needs_no_filesystem_root_and_no_stratum_of_this_repository() {
        let census = lean_wholes();
        assert_eq!(census.root(), Path::new(""));
        assert_eq!(census.stratum_label(Stratum(0)), "development");
        assert_eq!(census.declared_strata(), vec![Stratum(0)]);
        assert!(census.lookup("Nat.succ_le_of_lt").is_some());
        assert!(census.lookup("h₁").is_some());
        // The comment population is out of the stream and returned whole.
        assert!(census.lookup("close").is_none());
        let bound = census.comment_bound(64);
        assert!(bound.comment_occurrences > BigUint::from(0u32));
        assert!(
            bound
                .exhibited
                .iter()
                .any(|(surface, _)| surface == "close")
        );
    }

    #[test]
    fn an_empty_declaration_and_a_repeated_frame_are_refused_by_name() {
        assert_eq!(
            CorpusCensus::declaring(&[], LexicalSpecies::Prose).unwrap_err(),
            CensusError::NoStrataDeclared
        );
        let twice = [
            StratumDeclaration {
                stratum: Stratum(0),
                label: "left",
                relative_root: "a",
                extension: "md",
                recursive: false,
            },
            StratumDeclaration {
                stratum: Stratum(0),
                label: "right",
                relative_root: "b",
                extension: "md",
                recursive: false,
            },
        ];
        assert_eq!(
            CorpusCensus::declaring(&twice, LexicalSpecies::Prose).unwrap_err(),
            CensusError::FrameDeclaredTwice {
                index: 0,
                held: "left".to_owned(),
                offered: "right".to_owned(),
            }
        );
    }

    /// The repair, measured on a filesystem: a corpus declaring **none** of this repository's four
    /// roots is censused. Before the strata became the caller's, this returned `EmptyStratum`
    /// whatever the material was.
    #[test]
    fn a_corpus_that_is_not_this_repository_is_read_from_the_callers_own_declaration() {
        let root = std::env::temp_dir().join("holonic-corpus-census-foreign");
        let _ = fs::remove_dir_all(&root);
        fs::create_dir_all(root.join("left")).unwrap();
        fs::create_dir_all(root.join("right/nested")).unwrap();
        fs::write(root.join("left/one.lean"), LEAN_LINE).unwrap();
        fs::write(
            root.join("right/nested/two.lean"),
            "theorem Nat.other (h₂ : b) : b := h₂\n",
        )
        .unwrap();

        let declaration = [
            StratumDeclaration {
                stratum: Stratum(0),
                label: "left",
                relative_root: "left",
                extension: "lean",
                recursive: false,
            },
            StratumDeclaration {
                stratum: Stratum(1),
                label: "right",
                relative_root: "right",
                extension: "lean",
                recursive: true,
            },
        ];
        let census = CorpusCensus::read_declared(&root, &declaration, LexicalSpecies::LeanSource)
            .expect("a caller-declared corpus is read");
        assert_eq!(census.wholes().len(), 2);
        assert_eq!(census.stratum_label(Stratum(1)), "right");
        let joined = census.lookup("Nat.succ_le_of_lt").expect("qualified name");
        assert_eq!(census.strata(joined), vec![Stratum(0)]);
        let subscripted = census.lookup("h₂").expect("subscripted binder");
        assert_eq!(census.strata(subscripted), vec![Stratum(1)]);

        // And the control that names what was broken: the same root under this repository's own
        // declaration holds no wholes at all, which is the error every foreign corpus used to get.
        assert!(matches!(
            CorpusCensus::read(&root),
            Err(CensusError::Unreadable(..)) | Err(CensusError::EmptyStratum { .. })
        ));
        let _ = fs::remove_dir_all(&root);
    }

    #[test]
    fn the_weight_bands_partition_every_length() {
        let mut seen = vec![0usize; WEIGHT_BANDS.len()];
        for length in 1..200usize {
            seen[weight_band(length) as usize] += 1;
        }
        assert!(
            seen.iter().all(|count| *count > 0),
            "every band is reachable: {seen:?}"
        );
        assert_eq!(weight_band(1), 0);
        assert_eq!(weight_band(3), 1);
        assert_eq!(weight_band(6), 2);
        assert_eq!(weight_band(10), 3);
        assert_eq!(weight_band(11), 4);
    }
}

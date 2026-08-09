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
//! - **The corpus** is four strata, declared in [`DECLARED_STRATA`]: the mathematics paper sources,
//!   the canon, the research records, and the pure-holonics seed. Every file under those roots with
//!   the declared extension is read whole. Nothing is sampled.
//! - **The stream** is every token: word runs *and* markup runs. Whitespace separates and is not a
//!   token.
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

/// One declared source family. A frame, in `CLAUDE.md` §0's fourth-lesson sense: an invariant is
/// only visible across two of them.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum Stratum {
    Papers,
    Canon,
    Records,
    Seed,
}

impl Stratum {
    pub const ALL: [Stratum; 4] = [
        Stratum::Papers,
        Stratum::Canon,
        Stratum::Records,
        Stratum::Seed,
    ];

    pub fn name(self) -> &'static str {
        match self {
            Stratum::Papers => "papers",
            Stratum::Canon => "canon",
            Stratum::Records => "records",
            Stratum::Seed => "seed",
        }
    }

    fn bit(self) -> u8 {
        match self {
            Stratum::Papers => 1,
            Stratum::Canon => 2,
            Stratum::Records => 4,
            Stratum::Seed => 8,
        }
    }
}

/// Where one stratum's wholes live, relative to the declared corpus root.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct StratumDeclaration {
    pub stratum: Stratum,
    pub relative_root: &'static str,
    pub extension: &'static str,
    pub recursive: bool,
}

/// The declared corpus. Four strata, whole files, no sampling.
pub const DECLARED_STRATA: [StratumDeclaration; 4] = [
    StratumDeclaration {
        stratum: Stratum::Papers,
        relative_root: "papers/source/mathematics",
        extension: "typ",
        recursive: true,
    },
    StratumDeclaration {
        stratum: Stratum::Canon,
        relative_root: "canon",
        extension: "md",
        recursive: false,
    },
    StratumDeclaration {
        stratum: Stratum::Records,
        relative_root: "research/records",
        extension: "md",
        recursive: false,
    },
    StratumDeclaration {
        stratum: Stratum::Seed,
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
    surfaces: Vec<String>,
    kinds: Vec<Kind>,
    interner: BTreeMap<String, SurfaceId>,
    wholes: Vec<WholeRecord>,
    counts: Vec<u64>,
    distinct_wholes: Vec<u32>,
    strata_mask: Vec<u8>,
    last_whole: Vec<i64>,
    sites: Vec<Vec<(u32, u32)>>,
    word_occurrences: u64,
    markup_occurrences: u64,
}

impl CorpusCensus {
    /// Read the declared corpus rooted at `root`. Every file under every declared stratum root with
    /// the declared extension is read whole.
    pub fn read(root: &Path) -> Result<Self, CensusError> {
        let mut census = Self {
            root: root.to_path_buf(),
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
        };
        for declaration in DECLARED_STRATA {
            let stratum_root = root.join(declaration.relative_root);
            let mut paths = Vec::new();
            collect(&stratum_root, declaration.extension, declaration.recursive, &mut paths)?;
            paths.sort();
            if paths.is_empty() {
                return Err(CensusError::EmptyStratum {
                    stratum: declaration.stratum,
                    root: declaration.relative_root,
                });
            }
            for path in paths {
                let text = fs::read_to_string(&path)
                    .map_err(|error| CensusError::Unreadable(path.display().to_string(), error.to_string()))?;
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

    fn admit(&mut self, stratum: Stratum, relative_path: String, text: &str) {
        let whole_index = self.wholes.len() as u32;
        let mut stream = Vec::new();
        for surface in tokenize(text) {
            let id = self.intern(surface);
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
        self.kinds.push(classify(surface));
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
        Stratum::ALL
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
                    *population.entry(surface.0 as u64).or_insert_with(BigUint::default) +=
                        BigUint::from(1u32);
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

/// The declared tokenizer: maximal runs of `[A-Za-z0-9_]` are word tokens, maximal runs of any other
/// non-whitespace characters are markup tokens, whitespace separates and produces nothing.
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

fn is_word_byte(byte: u8) -> bool {
    byte.is_ascii_alphanumeric() || byte == b'_'
}

/// The declared orthographic classification.
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
    let first_upper = surface.bytes().next().is_some_and(|b| b.is_ascii_uppercase());
    if first_upper && upper == 1 {
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
        let entry =
            entry.map_err(|error| CensusError::Unreadable(directory.display().to_string(), error.to_string()))?;
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
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_tokenizer_splits_word_runs_from_markup_runs_and_drops_whitespace() {
        assert_eq!(
            tokenize("arxiv.org/abs/2607.01 **holon**"),
            vec!["arxiv", ".", "org", "/", "abs", "/", "2607", ".", "01", "**", "holon", "**"]
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

    #[test]
    fn the_weight_bands_partition_every_length() {
        let mut seen = vec![0usize; WEIGHT_BANDS.len()];
        for length in 1..200usize {
            seen[weight_band(length) as usize] += 1;
        }
        assert!(seen.iter().all(|count| *count > 0), "every band is reachable: {seen:?}");
        assert_eq!(weight_band(1), 0);
        assert_eq!(weight_band(3), 1);
        assert_eq!(weight_band(6), 2);
        assert_eq!(weight_band(10), 3);
        assert_eq!(weight_band(11), 4);
    }
}

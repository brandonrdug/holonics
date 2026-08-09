//! The parcel: a receiver carried by the transport, retaining what it traversed.
//!
//! Every organ in this engine is **Eulerian** — it carries a field over sites and asks what the
//! field does. Nothing is **Lagrangian**: nothing rides the transport and reports the ordered word
//! it passed through. `analytic_field.rs:1177` says so in its own comment, and `kelvin.rs` carries a
//! material loop with no parcels to be made of.
//!
//! This module is that missing half. It is graded by **agreeing with an organ that already exists**,
//! not by returning something new.
//!
//! ## A parcel is not a new kind of object
//!
//! Brandon, 2026-08-09: *"the receiver does not necessarily refer to an actively founding set of
//! leader arcs, it can refer to a previously founded region's perspectives."* So a parcel is a
//! **receiver that moves with the flow**, and a previously founded region's perspective is a parcel
//! at rest. What a parcel carries is a **site** and a **retained ordered word** — the sequence of
//! letters it spelled. That word is the first-person side of the machine, against the field's set
//! side.
//!
//! ## The grade: the boundary-integral identity, exact at every horizon
//!
//! `research/records/2026-08-09_THE_INTERIOR_IS_AN_INTEGRAL_OVER_ITS_BOUNDARY_AND_THE_KERNEL_IS_BUILT_BY_REFLECTION.md`
//! §4 states the Eulerian object: on a finite weighted complex with the sites split into boundary
//! `∂` and interior `I`, the rows of `−M_II⁻¹ M_I∂` are the hitting distributions of the walk.
//! `diffusion.rs:474` computes `M_II⁻¹` (`interior_inverse`) exactly over `Rat`, and refuses at
//! `:499` when the inverse residual is not identically zero.
//!
//! A parcel cohort released at interior site `x` and advanced `k` passages returns the finite part
//! of exactly that object, plus its own frontier. Write `lower_k[x][b]` for the mass absorbed at
//! boundary site `b` within `k` passages and `open_k[x][v]` for the mass still riding at interior
//! site `v`. Then, with `E = −M_II⁻¹ M_I∂`:
//!
//! ```text
//!    E[x][b]   ==   lower_k[x][b]  +  SUM over interior v of  open_k[x][v] * E[v][b]
//! ```
//!
//! and this is **exact at every `k`**, with no tolerance, no limit and no float, because
//! `lower_k = SUM_{n<k} P_II^n P_I∂` and `open_k = P_II^k` and `E = SUM_{n>=0} P_II^n P_I∂`. The
//! parcel supplies the finite part of the boundary integral; the Eulerian organ supplies the tail at
//! the frontier; **the two must sum to the Eulerian whole.** That is the record's title one level in,
//! and it is what [`boundary_integral_reading`] returns and what a driver asserts entry by entry.
//!
//! It also yields the enclosure `lower_k[x][b] <= E[x][b] <= lower_k[x][b] + open_mass_k[x]` with an
//! **exact rational remainder** — the shape `CLAUDE.md` §11 demands — and the remainder is
//! `open_mass_k`, exhibited rather than bounded.
//!
//! ### What is NOT claimed
//!
//! **Exact equality of `lower_k` with `E` in finite `k` is unattainable** on any complex whose
//! interior carries a cycle, and `diffusion.rs` couples every branch in both directions
//! (`:464-467`), so a single interior–interior branch is already a cycle. What is exact in finite
//! `k` is the identity above, which glues the parcel's finite part to the Eulerian tail. An organ
//! that resummed the tail by itself would be performing the same elimination `diffusion.rs` already
//! performs, and would not be a second route.
//!
//! No comparison against `kelvin.rs`'s circulation is built here.
//!
//! ## Killing is not optional, and it is why the rows do not sum to one
//!
//! `diffusion.rs`'s operator is **not** the bare Laplacian. `:458` puts each node's `capacity` on the
//! diagonal before `:463-467` add `interval * conductance`, and `:65-67` refuses a non-positive
//! capacity outright. So the operator is `M = C + tau*L` with `C` strictly positive, the walk it
//! generates is **killed** at interior sites, and the rows of `−M_II⁻¹ M_I∂` sum to strictly less
//! than one. A parcel therefore needs a third question of its field — [`CarriedField::dissipation`],
//! the exact weight at which conduct ceases at a site without reaching the boundary. For
//! `diffusion.rs` that weight **is** the capacity. This makes the cross-check strictly harder to pass
//! by accident: a row forced to sum to one carries a free constraint, and these do not.
//!
//! ## The cohort is factorized by shared prefix, and the width is caller-declared
//!
//! `research/records/2026-08-01_THE_HARDWARE_IS_A_RECEIVER_COVER_THE_CARD_MUST_CARRY_THE_CURRENT.md`,
//! ratified: *"Shared structure is factorized; if the remaining exact terminal width exceeds declared
//! host/card capacity, the event returns a resource obstruction while preserving standing."*
//!
//! A parcel at a site with several admissible passages **forks and retains both** — plurality is the
//! return and a continuation fiber is not a number (`CLAUDE.md` §13 rule 2). Nothing is sampled,
//! selected, or weighted-and-chosen. The cohort is held as a [`WordTrie`]: words sharing a prefix are
//! one entry until they separate, and a riding parcel is keyed by `(trie node, site)` rather than by
//! its passage history. **Two passages spelling the same letter merge, and their masses add** — which
//! is the parcel form of the same factorization `token_invariance.rs` performs on windows. Where the
//! exact frontier width exceeds the caller's declared width, [`ParcelCohort::advanced`] returns
//! [`ParcelError::TerminalWidthExceeded`] naming the width the material required. It never returns a
//! prefix and never truncates; the cohort it was called on is untouched.
//!
//! The letter is what a **receiver** can see of a passage. Where every passage carries its own letter
//! the distinct-word population equals the path population; where several passages share a letter it
//! does not, and the driver measures both.

use std::collections::BTreeMap;

use num_bigint::BigUint;
use num_traits::{One, Signed, Zero};
use relational_geometry::Rat;
use serde::{Deserialize, Serialize};
use thiserror::Error;

use crate::diffusion::{DiffusionBoundaryTransferCertificate, DiffusionComplex};
use crate::{CurrentBranchId, CurrentNodeId};

/// A site the parcel can occupy. The caller declares the correspondence with its own field.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct ParcelSite(pub u64);

/// One admissible passage, named. Distinct from its letter: two passages may spell one letter.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct PassageId(pub u64);

/// What a receiver sees of a passage. The retained word is a word in these.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct Letter(pub u64);

/// One admissible passage out of a site, with its exact weight.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Passage {
    pub passage: PassageId,
    pub letter: Letter,
    pub target: ParcelSite,
    /// Exact, nonnegative. It is a **measurement** of the field, never a governor: nothing here
    /// compares two weights to choose one, and every admissible passage is retained.
    pub weight: Rat,
}

/// The Eulerian side, supplied by the caller.
///
/// A field is asked three questions and answers them exactly. It is never asked which passage to
/// take.
pub trait CarriedField {
    /// Every admissible passage out of `site`, with its exact weight. Order is irrelevant: the
    /// cohort is a map and nothing reads position.
    fn passages_from(&self, site: ParcelSite) -> Vec<Passage>;

    /// The boundary. A parcel that steps into an absorbing site lands there and stops.
    fn is_absorbing(&self, site: ParcelSite) -> bool;

    /// The exact weight at which conduct **ceases** at this site without reaching the boundary.
    ///
    /// Zero for a bare Laplacian, in which case every parcel eventually lands. For `diffusion.rs`
    /// this is the node's `capacity`, which `:65` requires to be strictly positive — see the module
    /// header. It is a weight in the same currency as a passage weight and shares the same
    /// denominator.
    fn dissipation(&self, site: ParcelSite) -> Rat {
        let _ = site;
        Rat::zero()
    }
}

/// Mass and path population of one cohort entry.
///
/// `mass` is the exact rational share of the released unit; `paths` is how many distinct
/// **passage** sequences that share collapsed into this one **letter** word. Where every passage
/// carries its own letter the two populations agree; the gap between them is the factorization.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ParcelMass {
    pub mass: Rat,
    pub paths: BigUint,
}

impl ParcelMass {
    pub fn unit() -> Self {
        Self {
            mass: Rat::one(),
            paths: BigUint::one(),
        }
    }

    fn empty() -> Self {
        Self {
            mass: Rat::zero(),
            paths: BigUint::zero(),
        }
    }

    fn absorb(&mut self, other: &Self) {
        self.mass += &other.mass;
        self.paths += &other.paths;
    }
}

/// The retained words of a whole cohort, factorized by shared prefix.
///
/// Node `0` is the release, carrying the empty word. Its size is the number of **distinct prefixes**
/// the cohort ever spelled, which is `O(distinct words)` rather than `O(paths)`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct WordTrie {
    parents: Vec<Option<(usize, Letter)>>,
    children: Vec<BTreeMap<Letter, usize>>,
    depths: Vec<usize>,
}

impl Default for WordTrie {
    fn default() -> Self {
        Self::new()
    }
}

impl WordTrie {
    pub fn new() -> Self {
        Self {
            parents: vec![None],
            children: vec![BTreeMap::new()],
            depths: vec![0],
        }
    }

    /// The node reached by appending `letter` to `node`, founding it when it is new.
    fn descend(&mut self, node: usize, letter: Letter) -> usize {
        if let Some(existing) = self.children[node].get(&letter) {
            return *existing;
        }
        let founded = self.parents.len();
        self.parents.push(Some((node, letter)));
        self.children.push(BTreeMap::new());
        self.depths.push(self.depths[node] + 1);
        self.children[node].insert(letter, founded);
        founded
    }

    /// How many distinct prefixes this trie holds, the release included.
    pub fn nodes(&self) -> usize {
        self.parents.len()
    }

    pub fn depth(&self, node: usize) -> usize {
        self.depths[node]
    }

    /// The retained word at `node`, in traversal order.
    pub fn word(&self, node: usize) -> Vec<Letter> {
        let mut reversed = Vec::with_capacity(self.depths[node]);
        let mut cursor = node;
        while let Some((parent, letter)) = self.parents[cursor] {
            reversed.push(letter);
            cursor = parent;
        }
        reversed.reverse();
        reversed
    }

    /// The first index at which two retained words differ — the interchange obstruction.
    pub fn separating_word(&self, first: usize, second: usize) -> WordSeparation {
        separating_word(&self.word(first), &self.word(second))
    }
}

/// What separates two retained words, or that nothing does.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum WordSeparation {
    /// The same word. Two parcels here are one receiver's perspective, whatever passages they took.
    Identical,
    /// One word is a proper prefix of the other. It carries no separating index: the shorter parcel
    /// has not yet been anywhere the longer one has not.
    Prefix { shared: usize, longer: usize },
    /// The first index at which the two words differ, with the letter each spelled there.
    Separated {
        index: usize,
        first: Letter,
        second: Letter,
    },
}

/// The shortest separating word of two retained words, as an index and the two letters at it.
pub fn separating_word(first: &[Letter], second: &[Letter]) -> WordSeparation {
    for (index, (left, right)) in first.iter().zip(second.iter()).enumerate() {
        if left != right {
            return WordSeparation::Separated {
                index,
                first: *left,
                second: *right,
            };
        }
    }
    if first.len() == second.len() {
        WordSeparation::Identical
    } else {
        WordSeparation::Prefix {
            shared: first.len().min(second.len()),
            longer: first.len().max(second.len()),
        }
    }
}

/// Whether a word is a repetition of a shorter one. `w` is primitive when it is not `u^m`, `m >= 2`.
pub fn is_primitive(word: &[Letter]) -> bool {
    let extent = word.len();
    if extent == 0 {
        return false;
    }
    for period in 1..extent {
        if extent % period != 0 {
            continue;
        }
        if (period..extent).all(|index| word[index] == word[index - period]) {
            return false;
        }
    }
    true
}

/// A parcel that returned to the site it was released from, by the word it took to get back.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ClosedWord {
    pub word: Vec<Letter>,
    /// The exact share of the released unit that returned by this word.
    pub returned: ParcelMass,
    /// False when the word is a repetition of a shorter closed word.
    pub primitive: bool,
}

/// A frontier the caller's declared width cannot hold.
///
/// Standing is preserved: the cohort this was raised from is untouched and every figure it carries
/// remains exact. What is refused is only the request to materialize the next frontier, and the
/// refusal names the width the material required.
#[derive(Clone, Debug, PartialEq, Eq, Error)]
pub enum ParcelError {
    #[error("the field returned a negative weight on passage {passage:?} out of site {site:?}")]
    NegativeWeight { site: ParcelSite, passage: PassageId },
    #[error("the field returned a negative dissipation at site {site:?}")]
    NegativeDissipation { site: ParcelSite },
    #[error(
        "advancing the cohort requires a frontier of width {required}, past the declared width \
         {declared}"
    )]
    TerminalWidthExceeded { required: BigUint, declared: u64 },
}

/// A cohort of parcels released at one site, each carrying the ordered word it spelled.
///
/// Every population is keyed by `(trie node, site)`: the word says what a receiver saw, the site
/// says where the parcel is, and two parcels agreeing on both are one entry with their masses added.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ParcelCohort {
    release: ParcelSite,
    steps: usize,
    trie: WordTrie,
    riding: BTreeMap<(usize, ParcelSite), ParcelMass>,
    landed: BTreeMap<(usize, ParcelSite), ParcelMass>,
    dissipated: BTreeMap<(usize, ParcelSite), ParcelMass>,
    stalled: BTreeMap<(usize, ParcelSite), ParcelMass>,
    closed: Vec<ClosedWord>,
}

fn merge(
    population: &mut BTreeMap<(usize, ParcelSite), ParcelMass>,
    key: (usize, ParcelSite),
    value: ParcelMass,
) {
    population
        .entry(key)
        .or_insert_with(ParcelMass::empty)
        .absorb(&value);
}

fn total_mass(population: &BTreeMap<(usize, ParcelSite), ParcelMass>) -> Rat {
    population
        .values()
        .fold(Rat::zero(), |sum, entry| sum + &entry.mass)
}

fn mass_by_site(population: &BTreeMap<(usize, ParcelSite), ParcelMass>) -> BTreeMap<ParcelSite, Rat> {
    let mut folded = BTreeMap::new();
    for ((_, site), entry) in population {
        let slot = folded.entry(*site).or_insert_with(Rat::zero);
        *slot += &entry.mass;
    }
    folded
}

impl ParcelCohort {
    /// Release one unit of parcel at `site`, carrying the empty word.
    pub fn release<F: CarriedField>(field: &F, site: ParcelSite) -> Self {
        let mut riding = BTreeMap::new();
        let mut landed = BTreeMap::new();
        if field.is_absorbing(site) {
            landed.insert((0usize, site), ParcelMass::unit());
        } else {
            riding.insert((0usize, site), ParcelMass::unit());
        }
        Self {
            release: site,
            steps: 0,
            trie: WordTrie::new(),
            riding,
            landed,
            dissipated: BTreeMap::new(),
            stalled: BTreeMap::new(),
            closed: Vec::new(),
        }
    }

    /// Advance every riding parcel one passage, forking at every admissible passage.
    ///
    /// The cohort this is called on is left intact, so a refused frontier costs the caller nothing
    /// it had.
    pub fn advanced<F: CarriedField>(
        &self,
        field: &F,
        declared_width: u64,
    ) -> Result<Self, ParcelError> {
        let mut trie = self.trie.clone();
        let mut riding: BTreeMap<(usize, ParcelSite), ParcelMass> = BTreeMap::new();
        let mut landed = self.landed.clone();
        let mut dissipated = self.dissipated.clone();
        let mut stalled = self.stalled.clone();

        for ((node, site), carried) in &self.riding {
            let passages = field.passages_from(*site);
            let dissipation = field.dissipation(*site);
            if dissipation.is_negative() {
                return Err(ParcelError::NegativeDissipation { site: *site });
            }
            let mut total = dissipation.clone();
            for passage in &passages {
                if passage.weight.is_negative() {
                    return Err(ParcelError::NegativeWeight {
                        site: *site,
                        passage: passage.passage,
                    });
                }
                total += &passage.weight;
            }
            if total.is_zero() {
                merge(&mut stalled, (*node, *site), carried.clone());
                continue;
            }
            if dissipation.is_positive() {
                let share = (&carried.mass * &dissipation) / &total;
                merge(
                    &mut dissipated,
                    (*node, *site),
                    ParcelMass {
                        mass: share,
                        paths: carried.paths.clone(),
                    },
                );
            }
            for passage in &passages {
                if passage.weight.is_zero() {
                    continue;
                }
                let child = trie.descend(*node, passage.letter);
                let moved = ParcelMass {
                    mass: (&carried.mass * &passage.weight) / &total,
                    paths: carried.paths.clone(),
                };
                if field.is_absorbing(passage.target) {
                    merge(&mut landed, (child, passage.target), moved);
                } else {
                    merge(&mut riding, (child, passage.target), moved);
                }
            }
        }

        let width = riding.len();
        if width as u128 > u128::from(declared_width) {
            return Err(ParcelError::TerminalWidthExceeded {
                required: BigUint::from(width),
                declared: declared_width,
            });
        }

        let mut closed = self.closed.clone();
        for ((node, site), carried) in &riding {
            if *site != self.release {
                continue;
            }
            let word = trie.word(*node);
            let primitive = is_primitive(&word);
            closed.push(ClosedWord {
                word,
                returned: carried.clone(),
                primitive,
            });
        }

        Ok(Self {
            release: self.release,
            steps: self.steps + 1,
            trie,
            riding,
            landed,
            dissipated,
            stalled,
            closed,
        })
    }

    /// Release at `site` and advance `horizon` passages.
    pub fn advanced_to<F: CarriedField>(
        field: &F,
        site: ParcelSite,
        horizon: usize,
        declared_width: u64,
    ) -> Result<Self, ParcelError> {
        let mut cohort = Self::release(field, site);
        for _ in 0..horizon {
            cohort = cohort.advanced(field, declared_width)?;
        }
        Ok(cohort)
    }

    pub fn release_site(&self) -> ParcelSite {
        self.release
    }

    pub fn steps(&self) -> usize {
        self.steps
    }

    pub fn trie(&self) -> &WordTrie {
        &self.trie
    }

    pub fn riding(&self) -> &BTreeMap<(usize, ParcelSite), ParcelMass> {
        &self.riding
    }

    pub fn landed(&self) -> &BTreeMap<(usize, ParcelSite), ParcelMass> {
        &self.landed
    }

    pub fn dissipated(&self) -> &BTreeMap<(usize, ParcelSite), ParcelMass> {
        &self.dissipated
    }

    /// Parcels at a site the field admits no passage out of and declares no dissipation at.
    pub fn stalled(&self) -> &BTreeMap<(usize, ParcelSite), ParcelMass> {
        &self.stalled
    }

    /// The width of the current frontier — the exact number of distinct `(word, site)` states.
    pub fn frontier_width(&self) -> usize {
        self.riding.len()
    }

    /// The exact retained remainder: mass still riding, having neither landed nor dissipated.
    pub fn open_mass(&self) -> Rat {
        total_mass(&self.riding)
    }

    pub fn landed_mass(&self) -> Rat {
        total_mass(&self.landed)
    }

    pub fn dissipated_mass(&self) -> Rat {
        total_mass(&self.dissipated)
    }

    pub fn stalled_mass(&self) -> Rat {
        total_mass(&self.stalled)
    }

    /// The finite part of the boundary integral: mass absorbed at each boundary site so far.
    pub fn exit_lower(&self) -> BTreeMap<ParcelSite, Rat> {
        mass_by_site(&self.landed)
    }

    /// Where the frontier is, by site — the weights the Eulerian tail is read against.
    pub fn open_at(&self) -> BTreeMap<ParcelSite, Rat> {
        mass_by_site(&self.riding)
    }

    /// Every landed parcel as `(retained word, boundary site, mass, paths)`, in trie order.
    ///
    /// This is the artifact. A count of landings is a supporting receipt and never a substitute.
    pub fn landed_words(&self) -> Vec<(Vec<Letter>, ParcelSite, ParcelMass)> {
        self.landed
            .iter()
            .map(|((node, site), carried)| (self.trie.word(*node), *site, carried.clone()))
            .collect()
    }

    /// Every riding parcel as `(retained word, site, mass, paths)`, in trie order.
    pub fn riding_words(&self) -> Vec<(Vec<Letter>, ParcelSite, ParcelMass)> {
        self.riding
            .iter()
            .map(|((node, site), carried)| (self.trie.word(*node), *site, carried.clone()))
            .collect()
    }

    /// How many distinct **letter** words the cohort has spelled, landed and riding together.
    pub fn distinct_words(&self) -> usize {
        let mut nodes = self
            .landed
            .keys()
            .chain(self.riding.keys())
            .chain(self.dissipated.keys())
            .chain(self.stalled.keys())
            .map(|(node, _)| *node)
            .collect::<Vec<_>>();
        nodes.sort_unstable();
        nodes.dedup();
        nodes.len()
    }

    /// How many distinct **passage** sequences those words stand for.
    ///
    /// Equal to [`distinct_words`](Self::distinct_words) exactly when no two passages share a letter.
    /// The ratio is the factorization.
    pub fn path_population(&self) -> BigUint {
        self.landed
            .values()
            .chain(self.riding.values())
            .chain(self.dissipated.values())
            .chain(self.stalled.values())
            .fold(BigUint::zero(), |sum, entry| sum + &entry.paths)
    }

    /// Every closed word recorded so far: parcels that came back to the release site.
    pub fn closed_words(&self) -> &[ClosedWord] {
        &self.closed
    }

    /// Closed words that are not repetitions of a shorter closed word.
    pub fn primitive_closed_words(&self) -> Vec<&ClosedWord> {
        self.closed.iter().filter(|word| word.primitive).collect()
    }

    /// Primitive closed words counted by length, index zero being length one.
    ///
    /// **Comparable in shape** to `relational_geometry::IharaSignature::primitive_oriented_cycles`,
    /// which is indexed the same way. It is **not** the same population and is not asserted equal to
    /// it: Ihara counts primitive cycles modulo the cyclic choice of starting dart and admits no
    /// backtracking, while a closed word here is **rooted** at the release site and a parcel may
    /// retrace the passage it just took. The two quotients that separate them are named here rather
    /// than applied.
    pub fn primitive_closed_word_census(&self) -> Vec<BigUint> {
        let mut census: Vec<BigUint> = Vec::new();
        for word in self.closed.iter().filter(|word| word.primitive) {
            let index = word.word.len() - 1;
            while census.len() <= index {
                census.push(BigUint::zero());
            }
            census[index] += BigUint::one();
        }
        census
    }
}

/// One boundary site's two routes, side by side.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct BoundaryIntegralTerm {
    pub boundary: ParcelSite,
    /// The Lagrangian finite part: mass this cohort actually delivered to `boundary`.
    pub parcel_lower: Rat,
    /// The Eulerian tail read at the frontier: `SUM_v open[v] * E[v][boundary]`.
    pub frontier_tail: Rat,
    /// `parcel_lower + frontier_tail`.
    pub glued: Rat,
    /// `E[release][boundary]`, straight from the Eulerian organ.
    pub eulerian: Rat,
    /// `eulerian - glued`. Zero is the claim.
    pub residual: Rat,
}

/// The two routes glued at the frontier, at one horizon, for one release site.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct BoundaryIntegralReading {
    pub release: ParcelSite,
    pub steps: usize,
    pub open_mass: Rat,
    pub dissipated_mass: Rat,
    pub stalled_mass: Rat,
    pub terms: Vec<BoundaryIntegralTerm>,
    /// Frontier or release sites the supplied Eulerian atlas has no row for. A reading that names
    /// one is not evidence: the tail could not be read and the identity was not tested.
    pub missing_rows: Vec<ParcelSite>,
}

impl BoundaryIntegralReading {
    /// The identity holds exactly, every row was available, and nothing stalled.
    pub fn exact(&self) -> bool {
        self.missing_rows.is_empty()
            && self.stalled_mass.is_zero()
            && self.terms.iter().all(|term| term.residual.is_zero())
    }

    /// The weaker reading the identity implies: `lower <= E <= lower + open_mass`, entry by entry.
    ///
    /// It is **strictly weaker**, and measurably so: a perturbation smaller than the retained
    /// remainder passes here and is refused by [`exact`](Self::exact). The driver exhibits the
    /// horizon at which the enclosure first narrows past a declared perturbation. Stalled mass is
    /// refused rather than widened into: mass that can never land makes `lower + open_mass` not an
    /// upper enclosure at all.
    pub fn contained(&self) -> bool {
        self.missing_rows.is_empty()
            && self.stalled_mass.is_zero()
            && self.terms.iter().all(|term| {
                term.eulerian >= term.parcel_lower
                    && term.eulerian <= &term.parcel_lower + &self.open_mass
            })
    }

    /// The exact rational width of the enclosure. It is the retained remainder, not a bound on it.
    pub fn enclosure_width(&self) -> &Rat {
        &self.open_mass
    }
}

/// Glue the cohort's finite part to the Eulerian tail and return both routes entry by entry.
///
/// `eulerian` is an atlas of interior rows: `eulerian[v][b]` is the Eulerian organ's answer for a
/// parcel released at `v` landing at `b`. [`harmonic_measure`] builds it from `diffusion.rs`'s own
/// certificate.
pub fn boundary_integral_reading(
    cohort: &ParcelCohort,
    boundary: &[ParcelSite],
    eulerian: &BTreeMap<ParcelSite, BTreeMap<ParcelSite, Rat>>,
) -> BoundaryIntegralReading {
    let open_at = cohort.open_at();
    let lower = cohort.exit_lower();
    let mut missing_rows = Vec::new();
    if !eulerian.contains_key(&cohort.release_site()) {
        missing_rows.push(cohort.release_site());
    }
    for site in open_at.keys() {
        if !eulerian.contains_key(site) {
            missing_rows.push(*site);
        }
    }
    missing_rows.sort_unstable();
    missing_rows.dedup();

    let released_row = eulerian.get(&cohort.release_site());
    let terms = boundary
        .iter()
        .map(|site| {
            let parcel_lower = lower.get(site).cloned().unwrap_or_else(Rat::zero);
            let frontier_tail = open_at.iter().fold(Rat::zero(), |sum, (frontier, mass)| {
                let reached = eulerian
                    .get(frontier)
                    .and_then(|row| row.get(site))
                    .cloned()
                    .unwrap_or_else(Rat::zero);
                sum + mass * reached
            });
            let glued = &parcel_lower + &frontier_tail;
            let eulerian_value = released_row
                .and_then(|row| row.get(site))
                .cloned()
                .unwrap_or_else(Rat::zero);
            let residual = &eulerian_value - &glued;
            BoundaryIntegralTerm {
                boundary: *site,
                parcel_lower,
                frontier_tail,
                glued,
                eulerian: eulerian_value,
                residual,
            }
        })
        .collect();

    BoundaryIntegralReading {
        release: cohort.release_site(),
        steps: cohort.steps(),
        open_mass: cohort.open_mass(),
        dissipated_mass: cohort.dissipated_mass(),
        stalled_mass: cohort.stalled_mass(),
        terms,
        missing_rows,
    }
}

/// `−M_II⁻¹ M_I∂`, read straight off `diffusion.rs`'s own certificate.
///
/// `interior_inverse` is `diffusion.rs:474`; `M_I∂` is sliced from the assembled `operator`
/// (`:456-468`) at the certificate's declared interior and boundary. Row `x` is the Eulerian answer
/// for a parcel released at `x`. Nothing here re-derives the inverse: the load-bearing computation is
/// the one the diffusion organ already certified at `:493-500`.
pub fn harmonic_measure(
    certificate: &DiffusionBoundaryTransferCertificate,
) -> BTreeMap<ParcelSite, BTreeMap<ParcelSite, Rat>> {
    let ordinals = certificate
        .node_order
        .iter()
        .enumerate()
        .map(|(ordinal, node)| (*node, ordinal))
        .collect::<BTreeMap<_, _>>();
    let interior_ordinals = certificate
        .interior
        .iter()
        .map(|node| ordinals[node])
        .collect::<Vec<_>>();
    let boundary_ordinals = certificate
        .boundary
        .iter()
        .map(|node| ordinals[node])
        .collect::<Vec<_>>();

    certificate
        .interior
        .iter()
        .enumerate()
        .map(|(row, node)| {
            let entries = certificate
                .boundary
                .iter()
                .enumerate()
                .map(|(column, target)| {
                    let value = interior_ordinals
                        .iter()
                        .enumerate()
                        .fold(Rat::zero(), |sum, (index, interior)| {
                            let coupling =
                                &certificate.operator[*interior][boundary_ordinals[column]];
                            sum + &certificate.interior_inverse[row][index] * coupling
                        });
                    (ParcelSite(target.0), -value)
                })
                .collect::<BTreeMap<_, _>>();
            (ParcelSite(node.0), entries)
        })
        .collect()
}

/// The field `diffusion.rs` declares, read as something a parcel can ride.
///
/// The passage weight out of a node is `interval * conductance` — exactly the off-diagonal coupling
/// `diffusion.rs:463-467` assembles — and the dissipation is the node's `capacity`, exactly the
/// diagonal term `:458` places before the couplings. So the total weight at a site is the operator's
/// diagonal entry `M_vv`, and the parcel's fork shares are `M_vw / M_vv`. Nothing is renormalized and
/// nothing is authored.
#[derive(Clone, Debug)]
pub struct DiffusionCarriedField {
    interval: Rat,
    capacities: BTreeMap<ParcelSite, Rat>,
    absorbing: Vec<ParcelSite>,
    outgoing: BTreeMap<ParcelSite, Vec<Passage>>,
}

impl DiffusionCarriedField {
    /// Every branch spells its own letter, so distinct words and paths agree.
    pub fn new(
        complex: &DiffusionComplex,
        interval: Rat,
        boundary: impl IntoIterator<Item = CurrentNodeId>,
    ) -> Self {
        Self::with_declared_letters(complex, interval, boundary, &BTreeMap::new())
    }

    /// The caller declares what a receiver sees of each branch. Branches absent from `letters` spell
    /// their own branch identifier; branches sharing a letter **merge** in the retained word.
    pub fn with_declared_letters(
        complex: &DiffusionComplex,
        interval: Rat,
        boundary: impl IntoIterator<Item = CurrentNodeId>,
        letters: &BTreeMap<CurrentBranchId, Letter>,
    ) -> Self {
        let capacities = complex
            .nodes()
            .values()
            .map(|node| (ParcelSite(node.node.0), node.capacity.clone()))
            .collect();
        let mut absorbing = boundary
            .into_iter()
            .map(|node| ParcelSite(node.0))
            .collect::<Vec<_>>();
        absorbing.sort_unstable();
        absorbing.dedup();

        let mut outgoing: BTreeMap<ParcelSite, Vec<Passage>> = BTreeMap::new();
        for branch in complex.branches().values() {
            let letter = letters
                .get(&branch.branch)
                .copied()
                .unwrap_or(Letter(branch.branch.0));
            let weight = &interval * &branch.conductance;
            for (from, to) in [
                (branch.source, branch.target),
                (branch.target, branch.source),
            ] {
                outgoing
                    .entry(ParcelSite(from.0))
                    .or_default()
                    .push(Passage {
                        passage: PassageId(branch.branch.0),
                        letter,
                        target: ParcelSite(to.0),
                        weight: weight.clone(),
                    });
            }
        }

        Self {
            interval,
            capacities,
            absorbing,
            outgoing,
        }
    }

    pub fn interval(&self) -> &Rat {
        &self.interval
    }

    pub fn interior(&self) -> Vec<ParcelSite> {
        self.capacities
            .keys()
            .copied()
            .filter(|site| !self.absorbing.contains(site))
            .collect()
    }

    pub fn boundary(&self) -> &[ParcelSite] {
        &self.absorbing
    }
}

impl CarriedField for DiffusionCarriedField {
    fn passages_from(&self, site: ParcelSite) -> Vec<Passage> {
        self.outgoing.get(&site).cloned().unwrap_or_default()
    }

    fn is_absorbing(&self, site: ParcelSite) -> bool {
        self.absorbing.contains(&site)
    }

    fn dissipation(&self, site: ParcelSite) -> Rat {
        self.capacities
            .get(&site)
            .cloned()
            .unwrap_or_else(Rat::zero)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::diffusion::{
        DiffusionBranch, DiffusionComplex, DiffusionEvent, DiffusionNode, ExactDiffusionLaw,
    };
    use num_bigint::BigInt;

    fn rational(numerator: i64, denominator: i64) -> Rat {
        Rat::new(BigInt::from(numerator), BigInt::from(denominator))
    }

    fn integer(value: i64) -> Rat {
        Rat::from_integer(BigInt::from(value))
    }

    /// Three interior sites, two boundary sites, every conductance different.
    ///
    /// `kelvin.rs`'s falsifier records that equal capacities collapse two transports that unequal
    /// ones separate, so nothing here is equal to anything else.
    fn declared_complex() -> DiffusionComplex {
        DiffusionComplex::new(
            [
                DiffusionNode {
                    node: CurrentNodeId(1),
                    capacity: rational(1, 5),
                },
                DiffusionNode {
                    node: CurrentNodeId(2),
                    capacity: rational(1, 7),
                },
                DiffusionNode {
                    node: CurrentNodeId(3),
                    capacity: rational(1, 3),
                },
                DiffusionNode {
                    node: CurrentNodeId(10),
                    capacity: integer(2),
                },
                DiffusionNode {
                    node: CurrentNodeId(11),
                    capacity: integer(3),
                },
            ],
            [
                DiffusionBranch {
                    branch: CurrentBranchId(1),
                    source: CurrentNodeId(1),
                    target: CurrentNodeId(2),
                    conductance: integer(3),
                },
                DiffusionBranch {
                    branch: CurrentBranchId(2),
                    source: CurrentNodeId(2),
                    target: CurrentNodeId(3),
                    conductance: rational(5, 2),
                },
                DiffusionBranch {
                    branch: CurrentBranchId(3),
                    source: CurrentNodeId(1),
                    target: CurrentNodeId(3),
                    conductance: rational(7, 3),
                },
                DiffusionBranch {
                    branch: CurrentBranchId(4),
                    source: CurrentNodeId(1),
                    target: CurrentNodeId(10),
                    conductance: rational(1, 2),
                },
                DiffusionBranch {
                    branch: CurrentBranchId(5),
                    source: CurrentNodeId(3),
                    target: CurrentNodeId(11),
                    conductance: integer(4),
                },
                DiffusionBranch {
                    branch: CurrentBranchId(6),
                    source: CurrentNodeId(2),
                    target: CurrentNodeId(11),
                    conductance: rational(1, 4),
                },
                DiffusionBranch {
                    branch: CurrentBranchId(7),
                    source: CurrentNodeId(2),
                    target: CurrentNodeId(10),
                    conductance: rational(6, 5),
                },
            ],
        )
        .expect("the declared diffusion complex is well formed")
    }

    fn declared_certificate(
        complex: &DiffusionComplex,
        interval: Rat,
    ) -> DiffusionBoundaryTransferCertificate {
        let law = ExactDiffusionLaw::with_boundary(
            complex.clone(),
            [CurrentNodeId(10), CurrentNodeId(11)],
        )
        .expect("the diffusion law admits the declared boundary");
        let standing = law
            .initial_standing(
                complex
                    .nodes()
                    .keys()
                    .map(|node| (*node, Rat::zero()))
                    .collect(),
            )
            .expect("the standing populates every node");
        let (_, receipt) = law
            .enact(
                &standing,
                &DiffusionEvent {
                    interval,
                    source: BTreeMap::new(),
                },
            )
            .expect("the declared event completes");
        receipt.transfer.certificate
    }

    #[test]
    fn the_parcel_route_and_the_eulerian_route_glue_exactly_at_every_horizon() {
        let complex = declared_complex();
        let interval = integer(1);
        let certificate = declared_certificate(&complex, interval.clone());
        let eulerian = harmonic_measure(&certificate);
        let field = DiffusionCarriedField::new(
            &complex,
            interval,
            [CurrentNodeId(10), CurrentNodeId(11)],
        );
        let boundary = field.boundary().to_vec();

        for release in field.interior() {
            let mut cohort = ParcelCohort::release(&field, release);
            let mut previous_open: Option<Rat> = None;
            for _ in 0..=6 {
                let reading = boundary_integral_reading(&cohort, &boundary, &eulerian);
                assert!(
                    reading.exact(),
                    "the boundary-integral identity failed at {release:?} after {} steps: {:?}",
                    reading.steps,
                    reading.terms
                );
                assert!(reading.contained());
                if let Some(previous) = previous_open {
                    assert!(
                        reading.open_mass < previous,
                        "the retained remainder did not shrink at {release:?}"
                    );
                }
                previous_open = Some(reading.open_mass.clone());
                cohort = cohort
                    .advanced(&field, u64::from(u16::MAX))
                    .expect("the declared width holds this frontier");
            }
        }
    }

    /// The control's orbit. The identity is asserted against an Eulerian atlas built from a complex
    /// whose branch 5 carries a different conductance; every residual must move off zero.
    #[test]
    fn the_identity_fails_when_the_two_routes_read_different_conductances() {
        let complex = declared_complex();
        let interval = integer(1);
        let mut moved_branches = complex.branches().values().cloned().collect::<Vec<_>>();
        for branch in &mut moved_branches {
            if branch.branch == CurrentBranchId(5) {
                branch.conductance = rational(9, 2);
            }
        }
        let moved = DiffusionComplex::new(complex.nodes().values().cloned(), moved_branches)
            .expect("the moved complex is well formed");
        let eulerian = harmonic_measure(&declared_certificate(&moved, interval.clone()));
        let field = DiffusionCarriedField::new(
            &complex,
            interval,
            [CurrentNodeId(10), CurrentNodeId(11)],
        );
        let boundary = field.boundary().to_vec();
        let cohort = ParcelCohort::advanced_to(
            &field,
            ParcelSite(1),
            4,
            u64::from(u16::MAX),
        )
        .expect("the declared width holds this frontier");
        let reading = boundary_integral_reading(&cohort, &boundary, &eulerian);
        assert!(!reading.exact());
        assert!(reading.terms.iter().all(|term| !term.residual.is_zero()));
    }

    /// Merging two passages onto one letter changes the retained words and changes nothing else.
    #[test]
    fn a_shared_letter_merges_the_word_and_conserves_the_mass() {
        let complex = declared_complex();
        let interval = integer(1);
        let certificate = declared_certificate(&complex, interval.clone());
        let eulerian = harmonic_measure(&certificate);
        let boundary = [ParcelSite(10), ParcelSite(11)];

        let separate = DiffusionCarriedField::new(
            &complex,
            interval.clone(),
            [CurrentNodeId(10), CurrentNodeId(11)],
        );
        let merged = DiffusionCarriedField::with_declared_letters(
            &complex,
            interval,
            [CurrentNodeId(10), CurrentNodeId(11)],
            &BTreeMap::from([
                (CurrentBranchId(1), Letter(100)),
                (CurrentBranchId(2), Letter(100)),
                (CurrentBranchId(3), Letter(100)),
            ]),
        );

        let width = u64::from(u16::MAX);
        let separate_cohort = ParcelCohort::advanced_to(&separate, ParcelSite(1), 5, width)
            .expect("the declared width holds the separate frontier");
        let merged_cohort = ParcelCohort::advanced_to(&merged, ParcelSite(1), 5, width)
            .expect("the declared width holds the merged frontier");

        assert_eq!(separate_cohort.exit_lower(), merged_cohort.exit_lower());
        assert_eq!(separate_cohort.open_mass(), merged_cohort.open_mass());
        assert_eq!(
            separate_cohort.path_population(),
            merged_cohort.path_population()
        );
        assert!(merged_cohort.distinct_words() < separate_cohort.distinct_words());
        assert!(boundary_integral_reading(&merged_cohort, &boundary, &eulerian).exact());
    }

    #[test]
    fn an_oversized_frontier_is_refused_by_name_and_the_cohort_survives() {
        let complex = declared_complex();
        let interval = integer(1);
        let field = DiffusionCarriedField::new(
            &complex,
            interval,
            [CurrentNodeId(10), CurrentNodeId(11)],
        );
        let cohort = ParcelCohort::advanced_to(&field, ParcelSite(1), 3, u64::from(u16::MAX))
            .expect("the declared width holds this frontier");
        let standing = cohort.clone();
        let required = BigUint::from(cohort.advanced(&field, u64::MAX).unwrap().frontier_width());
        match cohort.advanced(&field, 1) {
            Err(ParcelError::TerminalWidthExceeded { required: named, declared }) => {
                assert_eq!(named, required);
                assert_eq!(declared, 1);
            }
            other => panic!("the oversized frontier was not refused by name: {other:?}"),
        }
        assert_eq!(cohort, standing);
    }

    #[test]
    fn the_separating_word_is_the_first_index_at_which_two_parcels_differ() {
        assert_eq!(
            separating_word(&[Letter(1), Letter(4)], &[Letter(1), Letter(4)]),
            WordSeparation::Identical
        );
        assert_eq!(
            separating_word(&[Letter(1)], &[Letter(1), Letter(4)]),
            WordSeparation::Prefix {
                shared: 1,
                longer: 2
            }
        );
        assert_eq!(
            separating_word(&[Letter(1), Letter(4)], &[Letter(1), Letter(7)]),
            WordSeparation::Separated {
                index: 1,
                first: Letter(4),
                second: Letter(7)
            }
        );
    }

    #[test]
    fn a_repeated_word_is_not_primitive_and_the_census_is_indexed_from_length_one() {
        assert!(is_primitive(&[Letter(1)]));
        assert!(is_primitive(&[Letter(1), Letter(3)]));
        assert!(!is_primitive(&[Letter(1), Letter(1)]));
        assert!(!is_primitive(&[Letter(1), Letter(3), Letter(1), Letter(3)]));
        assert!(is_primitive(&[Letter(1), Letter(3), Letter(1)]));
        assert!(!is_primitive(&[]));

        let complex = declared_complex();
        let field = DiffusionCarriedField::new(
            &complex,
            integer(1),
            [CurrentNodeId(10), CurrentNodeId(11)],
        );
        let cohort = ParcelCohort::advanced_to(&field, ParcelSite(1), 4, u64::from(u16::MAX))
            .expect("the declared width holds this frontier");
        let census = cohort.primitive_closed_word_census();
        // Site 1 has no self-branch, so no closed word has length one.
        assert!(census.is_empty() || census[0].is_zero());
        assert!(
            cohort
                .primitive_closed_words()
                .iter()
                .all(|word| word.word.len() >= 2)
        );
        assert!(!cohort.primitive_closed_words().is_empty());
    }

    #[test]
    fn a_dissipation_free_field_lands_every_parcel_and_the_rows_sum_to_one() {
        struct Chain;
        impl CarriedField for Chain {
            fn passages_from(&self, site: ParcelSite) -> Vec<Passage> {
                match site.0 {
                    1 => vec![
                        Passage {
                            passage: PassageId(1),
                            letter: Letter(1),
                            target: ParcelSite(10),
                            weight: integer(1),
                        },
                        Passage {
                            passage: PassageId(2),
                            letter: Letter(2),
                            target: ParcelSite(11),
                            weight: integer(3),
                        },
                    ],
                    _ => Vec::new(),
                }
            }
            fn is_absorbing(&self, site: ParcelSite) -> bool {
                site.0 >= 10
            }
        }

        let cohort = ParcelCohort::advanced_to(&Chain, ParcelSite(1), 1, 8).unwrap();
        assert_eq!(cohort.open_mass(), Rat::zero());
        assert_eq!(cohort.dissipated_mass(), Rat::zero());
        assert_eq!(cohort.landed_mass(), Rat::one());
        assert_eq!(
            cohort.exit_lower(),
            BTreeMap::from([
                (ParcelSite(10), rational(1, 4)),
                (ParcelSite(11), rational(3, 4))
            ])
        );
    }

    #[test]
    fn a_site_with_no_passage_and_no_dissipation_stalls_rather_than_vanishing() {
        struct DeadEnd;
        impl CarriedField for DeadEnd {
            fn passages_from(&self, site: ParcelSite) -> Vec<Passage> {
                match site.0 {
                    1 => vec![Passage {
                        passage: PassageId(1),
                        letter: Letter(1),
                        target: ParcelSite(2),
                        weight: integer(1),
                    }],
                    _ => Vec::new(),
                }
            }
            fn is_absorbing(&self, _site: ParcelSite) -> bool {
                false
            }
        }

        let cohort = ParcelCohort::advanced_to(&DeadEnd, ParcelSite(1), 2, 8).unwrap();
        assert_eq!(cohort.stalled_mass(), Rat::one());
        assert_eq!(cohort.open_mass(), Rat::zero());
        assert_eq!(
            cohort.stalled().keys().map(|(_, site)| *site).collect::<Vec<_>>(),
            vec![ParcelSite(2)]
        );
        let reading = boundary_integral_reading(&cohort, &[], &BTreeMap::new());
        assert!(!reading.exact());
    }
}

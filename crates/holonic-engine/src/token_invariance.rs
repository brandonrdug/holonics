//! Which tokens a corpus treats as invariant objects, and what that costs — the separation half.
//!
//! ## The two readings, and why neither alone is the answer
//!
//! `corpus_census` returns the **density** reading: `Π`, the lived construction, counted and never
//! gated. This module returns the **separation** reading, and the governing point is that they are
//! the magnitude and the phase of one thing.
//!
//! An amplitude is complex; a probability is its squared modulus. **A probability keeps the
//! magnitude and deletes the phase** — the same deletion a float performs on the tail
//! (`canon/THE_MATHEMATICS_TABLET.md` §1) and a bare sign performs on the turn (`CLAUDE.md` §2b), at
//! a fourth carrier. Two routes to one result add as amplitudes, not as counts, so **a frequency
//! census cannot tell two routes that reinforce from two that cancel.** A token occurring 4,712
//! times is not thereby an invariant object: it may be one object seen 4,712 times, or a dozen
//! objects sharing a spelling.
//!
//! So: **an iron token is DENSE *and* UNSEPARATED, and neither reading alone decides it.**
//!
//! ## What "unseparated" means here, exactly
//!
//! An occurrence is a **position** in a whole's token stream. Conduct is a step **left** or
//! **right** along that stream, bounded by a declared **horizon**. A declared family of receivers
//! reads the surface standing at whatever position conduct has reached. Then
//! `receiver_exact_compression::compress` is Moore's partition refinement over exactly that system,
//! and its returns mean:
//!
//! - `one_shot` — what the family sees at the occurrence itself. Every occurrence of one surface
//!   reads identically here, by construction, so the roots begin in **one block**. The reading has
//!   no head start.
//! - `conduct` — the Nerode congruence: two occurrences survive together only if no word of steps
//!   within the horizon reaches a position where any receiver sees a difference.
//! - `collapsed` — the exact loss, **exhibited**: every pair the one-shot reading held together and
//!   conduct separates, each carrying the **shortest word** that separates it and the receiver that
//!   finally sees it. That word is the token's fuzziness, shown rather than scored.
//!
//! A surface whose whole occurrence population survives in one conduct block at the declared horizon
//! is **iron at that horizon**: the corpus never once used it in a context this family can tell
//! apart. A surface that shatters is **fuzzy**, and the shortest words say where and how near.
//!
//! ## The declared receiver family, and why it is three
//!
//! [`ReceiverAxis`] declares three receivers, each reading one coordinate of
//! `CorpusCensus::signature`:
//!
//! | axis | what it sees |
//! |---|---|
//! | `Kind` | the orthographic kind of the surface at the position — six values |
//! | `Weight` | its length band — five values |
//! | `Density` | its **density band**, `floor(log2 N)` on the corpus census — exact bit length |
//!
//! `Density` is the axis Brandon's question actually asks for: comprehension curving around *iron
//! recurrences (density)* requires density to be something a **receiver can see**, not only
//! something a reader tabulates. It is derived from `Π` and it measures; it selects nothing, and
//! [`axis_witnesses`] proves the family's orbit is non-trivial by exhibiting, for each axis, a pair
//! of surfaces that axis separates and the other two do not.
//!
//! ## The separation population is FACTORIZED, and that is why no aperture bounds this reading
//!
//! Until 2026-08-09 this module carried two authored levels — `WINDOW_APERTURE = 64` capping how
//! many distinct windows reached the compression organ, and `SEPARATION_EXHIBIT = 512` capping how
//! many separations the reading carried. Both were **silent truncations**: the return was a prefix
//! and a count, and a caller could not tell a complete answer from a cut one. Both are gone, and
//! neither was replaced by a larger number.
//!
//! What replaced them is the observation that the population **factorizes exactly**, so the
//! quadratic object never has to be materialized to be returned:
//!
//! 1. **Conduct words are pure runs.** `successor` moves one slot, and a mixed word such as `LR`
//!    returns to the root, which the organ's breadth-first search has already seen and never
//!    enqueues. So the admitted words are `L^k` and `R^k` for `k <= horizon`, explored in the order
//!    `L, R, LL, RR, LLL, RRR, …`.
//! 2. **A [`Window`] is therefore an ordered word, not a set.** It is written in exactly that
//!    order — offset `-1`, `+1`, `-2`, `+2`, … — so *lexicographic order on windows is the organ's
//!    own refinement order*, and the first index at which two windows differ **is** the round at
//!    which Moore's algorithm separates them.
//! 3. **Two occurrences separate exactly when their windows differ**, and the shortest separating
//!    word is read straight off that first differing index: `L` when it is even, `R` when it is
//!    odd, at depth `index / 2 + 1`.
//! 4. So the whole separation population is carried by the window classes **in sorted order**
//!    together with the length of the prefix each shares with its predecessor — the standard
//!    longest-common-prefix array. That is `O(d · horizon)` for `d` distinct windows, against
//!    `C(d, 2)` pairs, and every pair is recoverable from it exactly.
//!
//! Measured on the declared corpus by `examples/the_iron_tokens_carry_the_field` on 2026-08-09, at
//! horizon 2: `"the"` had **30,507** distinct windows and `C(30507, 2) = 465,323,271` separated
//! pairs, held by 30,507 classes and 30,506 shared-prefix lengths. **That figure moves**, because
//! the declared corpus is this repository and it is written to; re-take it rather than carrying it.
//! What does not move is the shape: the old aperture presented 64 of those windows and reported
//! `conduct_blocks = 64` — a number produced by the level rather than by the corpus.
//!
//! ## Where a declared capacity still binds, and what it returns
//!
//! Materializing pairs is the one operation whose cost is genuinely quadratic. It is not performed
//! by the reading; a caller asks for it, declares the capacity it has, and
//! [`SeparationComplex::exhibit`] either returns the population **whole** or returns
//! [`ExhibitionObstructed`] naming the width the material required. It never returns a prefix.
//!
//! `research/records/2026-08-01_THE_HARDWARE_IS_A_RECEIVER_COVER_THE_CARD_MUST_CARRY_THE_CURRENT.md`,
//! ratified, is the law this follows: *"An exact antichain can have genuine large width. That width
//! is an unresolved alternative fiber, not permission to exhaust memory or truncate silently. Shared
//! structure is factorized; if the remaining exact terminal width exceeds declared host/card
//! capacity, the event returns a resource obstruction while preserving standing."* The standing
//! preserved here is the complex itself: an obstructed exhibition costs the caller nothing it had.
//!
//! ## Two independent implementations of one partition
//!
//! `CLAUDE.md` §8: where an independent implementation exists, state both. The factorization
//! computed here and the Nerode refinement computed by `receiver_exact_compression` are two
//! implementations of the same partition, and [`cross_check`] runs the second against the first
//! **pair for pair** — word, witness, and terminus — on any surface whose pair population fits a
//! declared capacity. It is asserted, not assumed.

use std::collections::{BTreeMap, BTreeSet};

use num_bigint::BigUint;

use crate::corpus_census::{CorpusCensus, Kind, SurfaceId, weight_band_name};
use crate::receiver_exact_compression::{
    AblatedSystem, InputId, ItemId, Observation, ObservedSystem, ReceiverId, compress,
};

/// One declared receiver. Each reads exactly one coordinate of the census signature, so each is
/// separately ablatable and each one's contribution is separately measurable.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ReceiverAxis {
    Kind,
    Weight,
    Density,
}

impl ReceiverAxis {
    pub const DECLARED: [ReceiverAxis; 3] =
        [ReceiverAxis::Kind, ReceiverAxis::Weight, ReceiverAxis::Density];

    pub fn id(self) -> ReceiverId {
        ReceiverId(match self {
            ReceiverAxis::Kind => 0,
            ReceiverAxis::Weight => 1,
            ReceiverAxis::Density => 2,
        })
    }

    pub fn from_id(id: ReceiverId) -> Option<Self> {
        match id.0 {
            0 => Some(ReceiverAxis::Kind),
            1 => Some(ReceiverAxis::Weight),
            2 => Some(ReceiverAxis::Density),
            _ => None,
        }
    }

    pub fn name(self) -> &'static str {
        match self {
            ReceiverAxis::Kind => "kind",
            ReceiverAxis::Weight => "weight",
            ReceiverAxis::Density => "density",
        }
    }

    /// What this axis reads out of a census signature.
    pub fn read(self, signature: (u64, u64, u64)) -> u64 {
        match self {
            ReceiverAxis::Kind => signature.0,
            ReceiverAxis::Weight => signature.1,
            ReceiverAxis::Density => signature.2,
        }
    }

    /// What this axis returned, rendered as the class it names rather than as a bare integer.
    pub fn render(self, reading: u64) -> String {
        match self {
            ReceiverAxis::Kind => [
                "lower", "Capital", "ALLCAPS", "Mixed", "numeral", "markup",
            ]
            .get(reading as usize)
            .map(|name| (*name).to_owned())
            .unwrap_or_else(|| format!("kind:{reading}")),
            ReceiverAxis::Weight => format!("len {}", weight_band_name(reading)),
            ReceiverAxis::Density => format!("2^{reading}"),
        }
    }
}

/// A step of conduct. `Left` is `InputId(0)` and `Right` is `InputId(1)`, and the compression organ
/// walks inputs in that order — so at equal depth a difference on the **left** is the word returned.
/// A declared tie-break, stated rather than incidental.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Step {
    Left,
    Right,
}

impl Step {
    pub fn input(self) -> InputId {
        InputId(match self {
            Step::Left => 0,
            Step::Right => 1,
        })
    }

    pub fn from_input(input: InputId) -> Option<Self> {
        match input.0 {
            0 => Some(Step::Left),
            1 => Some(Step::Right),
            _ => None,
        }
    }

    pub fn offset(self) -> i64 {
        match self {
            Step::Left => -1,
            Step::Right => 1,
        }
    }
}

/// The complete information a word of length at most `horizon` can reach from one occurrence,
/// written **in the order the organ's breadth-first search reaches it**: offset `-1`, `+1`, `-2`,
/// `+2`, …, with `None` where the whole ends.
///
/// The order is the content. Lexicographic comparison of two windows is Moore refinement of the two
/// occurrences they belong to, and the first differing index is the round at which they separate.
pub type Window = Vec<Option<(u64, u64, u64)>>;

/// The `(side, depth)` a window index names. Index `2(k-1)` is `L^k`; index `2(k-1)+1` is `R^k`.
pub fn step_at(index: usize) -> (Step, usize) {
    (
        if index % 2 == 0 { Step::Left } else { Step::Right },
        index / 2 + 1,
    )
}

/// The signed stream offset a window index names.
pub fn offset_at(index: usize) -> i64 {
    let (side, depth) = step_at(index);
    side.offset() * depth as i64
}

/// The window of the occurrence at `position` in `whole`.
pub fn window(census: &CorpusCensus, whole: u32, position: u32, horizon: usize) -> Window {
    let stream = &census.wholes()[whole as usize].stream;
    let mut reading = Vec::with_capacity(2 * horizon);
    for index in 0..2 * horizon {
        let site = position as i64 + offset_at(index);
        if site < 0 || site >= stream.len() as i64 {
            reading.push(None);
        } else {
            reading.push(Some(census.signature(stream[site as usize])));
        }
    }
    reading
}

/// The window of one occurrence under a family with one axis removed. The ablated reading is the
/// same word with one coordinate deleted, so ablation is a projection of the factorization and
/// needs no separate refinement.
fn ablated_window(
    census: &CorpusCensus,
    whole: u32,
    position: u32,
    horizon: usize,
    without: ReceiverAxis,
) -> Vec<Option<(u64, u64)>> {
    window(census, whole, position, horizon)
        .into_iter()
        .map(|reading| {
            reading.map(|signature| {
                let kept: Vec<u64> = ReceiverAxis::DECLARED
                    .into_iter()
                    .filter(|axis| *axis != without)
                    .map(|axis| axis.read(signature))
                    .collect();
                (kept[0], kept[1])
            })
        })
        .collect()
}

// -------------------------------------------------------------------------------------------------
// The factorized separation population
// -------------------------------------------------------------------------------------------------

/// One distinct window, with **every** occurrence that reads it.
///
/// The occurrences inside a class are indistinguishable to the declared family within the horizon —
/// no admitted word separates them — so collapsing them is an exact quotient rather than a sample.
/// The multiplicity is retained, which is what lets the complex report the separated population
/// over the whole occurrence set and not merely over representatives.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct WindowClass {
    pub window: Window,
    pub sites: Vec<(u32, u32)>,
}

impl WindowClass {
    pub fn occurrences(&self) -> usize {
        self.sites.len()
    }
}

/// The whole separation population of one surface at one horizon, factorized.
///
/// `classes` is in lexicographic window order, which is the organ's refinement order.
/// `shared_prefix[i]` is the length of the longest common prefix of `classes[i]` and
/// `classes[i + 1]` — the standard longest-common-prefix array of the sorted population. The first
/// index at which classes `i < j` differ is `min(shared_prefix[i..j])`, and that index carries the
/// shortest separating word, its offset, and the receiver that sees it.
///
/// This is `O(d · horizon)` and holds `C(d, 2)` pairs exactly. Nothing is truncated and nothing is
/// summarised: [`SeparationComplex::separation_between`] returns any one of them.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SeparationComplex {
    pub surface: SurfaceId,
    pub horizon: usize,
    pub classes: Vec<WindowClass>,
    pub shared_prefix: Vec<usize>,
}

/// A materialization the caller's declared capacity cannot hold.
///
/// Standing is preserved: the [`SeparationComplex`] is intact and every figure it carries remains
/// exact. What is refused is only the caller's request to write the quadratic population out, and
/// the refusal names the width the material required so the caller can declare it or ask a
/// narrower question.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExhibitionObstructed {
    pub surface: SurfaceId,
    pub horizon: usize,
    pub declared_capacity: u64,
    pub required: BigUint,
}

impl std::fmt::Display for ExhibitionObstructed {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            formatter,
            "exhibiting the separation population of surface {} at horizon {} requires width {}, \
             past the declared capacity {}",
            self.surface.0, self.horizon, self.required, self.declared_capacity
        )
    }
}

impl std::error::Error for ExhibitionObstructed {}

impl SeparationComplex {
    /// Build the complex from the surface's whole occurrence population. No aperture participates.
    pub fn read(census: &CorpusCensus, surface: SurfaceId, horizon: usize) -> Self {
        let mut grouped: BTreeMap<Window, Vec<(u32, u32)>> = BTreeMap::new();
        for (whole, position) in census.sites(surface) {
            grouped
                .entry(window(census, *whole, *position, horizon))
                .or_default()
                .push((*whole, *position));
        }
        // `BTreeMap` already yields lexicographic window order, which is refinement order.
        let classes: Vec<WindowClass> = grouped
            .into_iter()
            .map(|(window, sites)| WindowClass { window, sites })
            .collect();
        let shared_prefix = classes
            .windows(2)
            .map(|pair| {
                pair[0]
                    .window
                    .iter()
                    .zip(pair[1].window.iter())
                    .take_while(|(left, right)| left == right)
                    .count()
            })
            .collect();
        Self {
            surface,
            horizon,
            classes,
            shared_prefix,
        }
    }

    pub fn distinct_windows(&self) -> usize {
        self.classes.len()
    }

    pub fn occurrences(&self) -> BigUint {
        self.classes
            .iter()
            .map(|class| BigUint::from(class.occurrences()))
            .sum()
    }

    /// `C(d, 2)` — every pair of distinct window classes separates, exactly.
    pub fn separated_class_pairs(&self) -> BigUint {
        choose_two(&BigUint::from(self.classes.len()))
    }

    /// The separated pairs over the **whole occurrence population**: `C(N,2)` minus the pairs inside
    /// a class, which no admitted word separates.
    pub fn separated_occurrence_pairs(&self) -> BigUint {
        let inside: BigUint = self
            .classes
            .iter()
            .map(|class| choose_two(&BigUint::from(class.occurrences())))
            .sum();
        choose_two(&self.occurrences()) - inside
    }

    /// The first index at which classes `left < right` differ. `None` when they are the same class.
    pub fn first_difference(&self, left: usize, right: usize) -> Option<usize> {
        let (low, high) = if left <= right {
            (left, right)
        } else {
            (right, left)
        };
        if low == high {
            return None;
        }
        self.shared_prefix[low..high].iter().min().copied()
    }

    /// The shallowest separation in the population — the round at which this surface first
    /// shatters. `None` for a surface with one window class.
    pub fn first_depth(&self) -> Option<usize> {
        self.shared_prefix
            .iter()
            .min()
            .map(|index| step_at(*index).1)
    }

    /// One named pair's separation, materialized exactly.
    pub fn separation_between(
        &self,
        census: &CorpusCensus,
        left: usize,
        right: usize,
    ) -> Option<Separation> {
        let index = self.first_difference(left, right)?;
        Some(self.materialize(census, left, right, index))
    }

    /// The separation that separates soonest, with the lowest class pair as the declared tie-break.
    /// A complete answer to a narrower question — never a prefix of the population.
    pub fn shortest_separation(&self, census: &CorpusCensus) -> Option<Separation> {
        let (position, _) = self
            .shared_prefix
            .iter()
            .enumerate()
            .min_by_key(|(position, index)| (**index, *position))?;
        self.separation_between(census, position, position + 1)
    }

    /// The whole separation population, or a typed obstruction naming the width it required.
    ///
    /// **Never a prefix.** A truncation returns a cut population and a count, and the caller cannot
    /// tell it from a complete one; an obstruction returns no population, the reason, and the width,
    /// and the caller can. `codec_recovery::Obstruction::GaugeApertureExceeded` is the same shape.
    pub fn exhibit(
        &self,
        census: &CorpusCensus,
        declared_capacity: u64,
    ) -> Result<Vec<Separation>, ExhibitionObstructed> {
        let required = self.separated_class_pairs();
        if required > BigUint::from(declared_capacity) {
            return Err(ExhibitionObstructed {
                surface: self.surface,
                horizon: self.horizon,
                declared_capacity,
                required,
            });
        }
        let mut separations = Vec::new();
        for left in 0..self.classes.len() {
            for right in left + 1..self.classes.len() {
                let index = self
                    .first_difference(left, right)
                    .expect("distinct classes differ");
                separations.push(self.materialize(census, left, right, index));
            }
        }
        Ok(separations)
    }

    /// Every separation of one named class against the rest, complete. A *stated* sub-population
    /// rather than an anonymous prefix, so a caller who cannot hold `C(d,2)` can still receive a
    /// whole answer to a smaller question.
    pub fn exhibit_class(
        &self,
        census: &CorpusCensus,
        class: usize,
        declared_capacity: u64,
    ) -> Result<Vec<Separation>, ExhibitionObstructed> {
        let required = BigUint::from(self.classes.len().saturating_sub(1));
        if required > BigUint::from(declared_capacity) {
            return Err(ExhibitionObstructed {
                surface: self.surface,
                horizon: self.horizon,
                declared_capacity,
                required,
            });
        }
        Ok((0..self.classes.len())
            .filter(|other| *other != class)
            .filter_map(|other| self.separation_between(census, class.min(other), class.max(other)))
            .collect())
    }

    fn materialize(
        &self,
        census: &CorpusCensus,
        left: usize,
        right: usize,
        index: usize,
    ) -> Separation {
        let (side, depth) = step_at(index);
        let offset = offset_at(index);
        let left_reading = self.classes[left].window[index];
        let right_reading = self.classes[right].window[index];
        let left_site = self.classes[left].sites[0];
        let right_site = self.classes[right].sites[0];
        let landing = |site: (u32, u32), reading: Option<(u64, u64, u64)>| -> Option<SurfaceId> {
            reading?;
            let stream = &census.wholes()[site.0 as usize].stream;
            let position = site.1 as i64 + offset;
            if position < 0 || position >= stream.len() as i64 {
                None
            } else {
                Some(stream[position as usize])
            }
        };
        let (axis, readings) = match (left_reading, right_reading) {
            (Some(left_signature), Some(right_signature)) => {
                let axis = ReceiverAxis::DECLARED
                    .into_iter()
                    .find(|axis| axis.read(left_signature) != axis.read(right_signature))
                    .expect("distinct signatures differ on some declared axis");
                (
                    Some(axis),
                    Some((axis.read(left_signature), axis.read(right_signature))),
                )
            }
            _ => (None, None),
        };
        Separation {
            left_class: left,
            right_class: right,
            left_site,
            right_site,
            left_occurrences: BigUint::from(self.classes[left].occurrences()),
            right_occurrences: BigUint::from(self.classes[right].occurrences()),
            word: vec![side; depth],
            offset,
            left_surface: landing(left_site, left_reading),
            right_surface: landing(right_site, right_reading),
            axis,
            readings,
            by_terminus: left_reading.is_none() != right_reading.is_none(),
        }
    }
}

fn choose_two(population: &BigUint) -> BigUint {
    if population < &BigUint::from(2u32) {
        return BigUint::from(0u32);
    }
    population.clone() * (population.clone() - BigUint::from(1u32)) / BigUint::from(2u32)
}

/// One exhibited separation: two window classes the one-shot reading held together, the shortest
/// word that separates them, and what was seen there.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Separation {
    pub left_class: usize,
    pub right_class: usize,
    /// A representative occurrence of each class. Every occurrence in a class reads identically, so
    /// which one is named changes nothing the receivers can see.
    pub left_site: (u32, u32),
    pub right_site: (u32, u32),
    /// How many occurrences stand behind each side. The class pair stands for
    /// `left_occurrences * right_occurrences` separated occurrence pairs.
    pub left_occurrences: BigUint,
    pub right_occurrences: BigUint,
    pub word: Vec<Step>,
    pub offset: i64,
    pub left_surface: Option<SurfaceId>,
    pub right_surface: Option<SurfaceId>,
    pub axis: Option<ReceiverAxis>,
    pub readings: Option<(u64, u64)>,
    /// The word separates them because one occurrence runs out of whole and the other does not.
    pub by_terminus: bool,
}

impl Separation {
    /// How many occurrence pairs this class pair stands for, exactly.
    pub fn occurrence_pairs(&self) -> BigUint {
        self.left_occurrences.clone() * self.right_occurrences.clone()
    }

    /// The separation, exhibited as text: the word, where it landed, and what each side found.
    pub fn exhibit(&self, census: &CorpusCensus) -> String {
        let word = if self.word.is_empty() {
            "<empty>".to_owned()
        } else {
            self.word
                .iter()
                .map(|step| match step {
                    Step::Left => "L",
                    Step::Right => "R",
                })
                .collect::<Vec<_>>()
                .join("")
        };
        let render = |surface: Option<SurfaceId>| match surface {
            Some(id) => format!("{:?}", census.surface(id)),
            None => "<end of whole>".to_owned(),
        };
        match (self.axis, self.readings) {
            (Some(axis), Some((left, right))) => format!(
                "word {word} (offset {:+}) -> {} vs {}, receiver `{}` returned {} vs {}",
                self.offset,
                render(self.left_surface),
                render(self.right_surface),
                axis.name(),
                axis.render(left),
                axis.render(right),
            ),
            _ => format!(
                "word {word} (offset {:+}) -> {} vs {}, separated by TERMINUS (no receiver saw a \
                 difference; one occurrence ran out of whole)",
                self.offset,
                render(self.left_surface),
                render(self.right_surface),
            ),
        }
    }
}

// -------------------------------------------------------------------------------------------------
// The reading
// -------------------------------------------------------------------------------------------------

/// What the separation reading returns for one surface.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Verdict {
    /// One conduct block. The corpus never used this surface in a context the family can tell apart.
    Iron,
    /// More than one conduct block, with the shortest separating word at depth `first_depth`.
    Separated { first_depth: usize },
}

impl Verdict {
    pub fn is_iron(self) -> bool {
        matches!(self, Verdict::Iron)
    }
}

/// One surface's separation reading at one declared horizon.
///
/// Every figure here is taken over the **whole** occurrence population. No level bounds it.
#[derive(Clone, Debug)]
pub struct SeparationReading {
    pub surface: SurfaceId,
    pub horizon: usize,
    pub occurrences: BigUint,
    /// The true number of distinct radius-`horizon` windows, over **every** occurrence.
    pub distinct_windows: usize,
    pub verdict: Verdict,
    pub complex: SeparationComplex,
}

impl SeparationReading {
    /// `C(N,2)` — the number of occurrence pairs the verdict ranged over, exact.
    ///
    /// **`CLAUDE.md` §8's tautology rule, made a number the reading carries.** A receipt that could
    /// not have come out otherwise carries no evidence, and a surface occurring **once** is
    /// unseparated by arithmetic rather than by the corpus's usage: there is no pair for conduct to
    /// separate. This is the exact count of the non-separations an iron verdict actually survived,
    /// and it is `0` exactly where the verdict is vacuous.
    pub fn survived_pairs(&self) -> BigUint {
        choose_two(&self.occurrences)
    }

    /// An iron verdict on a surface with fewer than two occurrences. True iron, vacuously.
    pub fn vacuously_iron(&self) -> bool {
        self.verdict.is_iron() && self.occurrences < BigUint::from(2u32)
    }

    /// An iron verdict that at least one occurrence pair could have refuted and did not.
    pub fn witnessed_iron(&self) -> bool {
        self.verdict.is_iron() && !self.vacuously_iron()
    }

    /// The shortest separating word length, or `None` for an iron surface.
    pub fn first_depth(&self) -> Option<usize> {
        match self.verdict {
            Verdict::Separated { first_depth } => Some(first_depth),
            _ => None,
        }
    }

    /// The exact separated-pair population over the whole occurrence set.
    pub fn separated_occurrence_pairs(&self) -> BigUint {
        self.complex.separated_occurrence_pairs()
    }

    /// The shortest separating word this surface carries, materialized.
    pub fn shortest_separation(&self, census: &CorpusCensus) -> Option<Separation> {
        self.complex.shortest_separation(census)
    }

    /// The whole separation population, or the typed obstruction naming what it required.
    pub fn exhibit(
        &self,
        census: &CorpusCensus,
        declared_capacity: u64,
    ) -> Result<Vec<Separation>, ExhibitionObstructed> {
        self.complex.exhibit(census, declared_capacity)
    }
}

/// Read one surface's occurrence population at one declared horizon.
pub fn separation_reading(
    census: &CorpusCensus,
    surface: SurfaceId,
    horizon: usize,
) -> SeparationReading {
    let complex = SeparationComplex::read(census, surface, horizon);
    let distinct_windows = complex.distinct_windows();
    let verdict = match complex.first_depth() {
        None => Verdict::Iron,
        Some(first_depth) => Verdict::Separated { first_depth },
    };
    SeparationReading {
        surface,
        horizon,
        occurrences: BigUint::from(census.occurrences(surface)),
        distinct_windows,
        verdict,
        complex,
    }
}

/// The whole measured population, read at one horizon. Every word surface appears.
pub fn sweep(census: &CorpusCensus, horizon: usize) -> BTreeMap<SurfaceId, SeparationReading> {
    census
        .word_surfaces()
        .into_iter()
        .map(|surface| (surface, separation_reading(census, surface, horizon)))
        .collect()
}

/// The iron population at one horizon: every surface whose whole occurrence population survives in
/// one conduct block.
///
/// Read over the **whole** occurrence population of every surface. Until 2026-08-09 this ran on the
/// first 64 distinct windows of each surface, which is what `canon/THE_CONTAMINANT_PROTOCOL.md`
/// §2.5 convicted; the aperture is gone and no subsample participates.
pub fn iron_at(sweep: &BTreeMap<SurfaceId, SeparationReading>) -> BTreeSet<SurfaceId> {
    sweep
        .iter()
        .filter(|(_, reading)| reading.verdict.is_iron())
        .map(|(surface, _)| *surface)
        .collect()
}

/// The iron population **that could have been refuted**: iron surfaces with at least one occurrence
/// pair. `CLAUDE.md` §8 — a receipt that could not have come out otherwise carries no evidence, and
/// a surface occurring once is unseparated by arithmetic. The complement is not dropped: it is
/// [`iron_at`] minus this, and both are returned.
pub fn witnessed_iron_at(sweep: &BTreeMap<SurfaceId, SeparationReading>) -> BTreeSet<SurfaceId> {
    sweep
        .iter()
        .filter(|(_, reading)| reading.witnessed_iron())
        .map(|(surface, _)| *surface)
        .collect()
}

// -------------------------------------------------------------------------------------------------
// The second implementation, and the cross-check between them
// -------------------------------------------------------------------------------------------------

/// One surface's occurrence population, presented as a system the compression organ can refine.
///
/// This is the **second** implementation of the partition the factorization computes. It exists to
/// be disagreed with: [`cross_check`] runs both and compares pair for pair.
pub struct OccurrenceSystem<'a> {
    census: &'a CorpusCensus,
    roots: Vec<(u32, u32)>,
    horizon: usize,
    axes: Vec<ReceiverAxis>,
}

impl<'a> OccurrenceSystem<'a> {
    pub fn new(census: &'a CorpusCensus, roots: Vec<(u32, u32)>, horizon: usize) -> Self {
        Self {
            census,
            roots,
            horizon,
            axes: ReceiverAxis::DECLARED.to_vec(),
        }
    }

    fn stride(&self) -> u64 {
        (2 * self.horizon + 1) as u64
    }

    pub fn root_item(&self, root: usize) -> ItemId {
        ItemId(root as u64 * self.stride() + self.horizon as u64)
    }

    /// `(whole, position)` for an item, or `None` when the offset falls outside the whole.
    pub fn site(&self, item: ItemId) -> Option<(u32, u32)> {
        let root = (item.0 / self.stride()) as usize;
        let offset = (item.0 % self.stride()) as i64 - self.horizon as i64;
        let (whole, position) = *self.roots.get(root)?;
        let index = position as i64 + offset;
        let stream = &self.census.wholes()[whole as usize].stream;
        if index < 0 || index >= stream.len() as i64 {
            None
        } else {
            Some((whole, index as u32))
        }
    }

    pub fn surface_at(&self, item: ItemId) -> Option<SurfaceId> {
        let (whole, position) = self.site(item)?;
        Some(self.census.wholes()[whole as usize].stream[position as usize])
    }

    /// The signed offset a word of steps lands on. Words returned by the organ are pure runs — a
    /// mixed word revisits a pair already seen and is never enqueued — but this sums the steps
    /// rather than assuming it.
    pub fn word_offset(word: &[InputId]) -> i64 {
        word.iter()
            .filter_map(|input| Step::from_input(*input))
            .map(Step::offset)
            .sum()
    }
}

impl ObservedSystem for OccurrenceSystem<'_> {
    fn items(&self) -> Vec<ItemId> {
        let mut items = Vec::with_capacity(self.roots.len() * (2 * self.horizon + 1));
        for root in 0..self.roots.len() {
            for slot in 0..self.stride() {
                let item = ItemId(root as u64 * self.stride() + slot);
                if self.site(item).is_some() {
                    items.push(item);
                }
            }
        }
        items
    }

    fn receivers(&self) -> Vec<ReceiverId> {
        self.axes.iter().map(|axis| axis.id()).collect()
    }

    fn inputs(&self) -> Vec<InputId> {
        vec![Step::Left.input(), Step::Right.input()]
    }

    fn observation(&self, item: ItemId, receiver: ReceiverId) -> Observation {
        let Some(surface) = self.surface_at(item) else {
            // Unreachable for a declared item; a missing site is a terminus, never an observation.
            return Observation(u64::MAX);
        };
        let signature = self.census.signature(surface);
        Observation(match ReceiverAxis::from_id(receiver) {
            Some(axis) => axis.read(signature),
            None => u64::MAX,
        })
    }

    fn successor(&self, item: ItemId, input: InputId) -> Option<ItemId> {
        let step = Step::from_input(input)?;
        let root = item.0 / self.stride();
        let slot = (item.0 % self.stride()) as i64;
        let next_slot = slot + step.offset();
        if next_slot < 0 || next_slot >= self.stride() as i64 {
            return None;
        }
        let next = ItemId(root * self.stride() + next_slot as u64);
        self.site(next).map(|_| next)
    }
}

/// What running both implementations returned.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CrossCheck {
    pub surface: SurfaceId,
    pub horizon: usize,
    /// Distinct windows, from the factorization.
    pub classes: usize,
    /// Conduct blocks among the presented roots, from `receiver_exact_compression`.
    pub conduct_blocks: usize,
    pub one_shot_blocks: usize,
    pub refinement_rounds: usize,
    /// Pairs the factorization returned; equal to the organ's collapsed population when they agree.
    pub factorized_pairs: usize,
    pub organ_pairs: usize,
    /// Pairs where the two implementations disagree on the word, the witness, or the terminus.
    pub disagreements: Vec<(usize, usize)>,
}

impl CrossCheck {
    /// The two implementations agree on the partition **and** on every pair's separating word.
    pub fn agrees(&self) -> bool {
        self.classes == self.conduct_blocks
            && self.factorized_pairs == self.organ_pairs
            && self.disagreements.is_empty()
    }
}

/// Run `receiver_exact_compression` over the same surface and compare pair for pair.
///
/// The organ's cost is quadratic in the presented population, so the caller declares the capacity it
/// has; past it this refuses with the width the material required rather than running a subsample.
pub fn cross_check(
    census: &CorpusCensus,
    surface: SurfaceId,
    horizon: usize,
    declared_capacity: u64,
) -> Result<CrossCheck, ExhibitionObstructed> {
    let complex = SeparationComplex::read(census, surface, horizon);
    let required = complex.separated_class_pairs();
    if required > BigUint::from(declared_capacity) {
        return Err(ExhibitionObstructed {
            surface,
            horizon,
            declared_capacity,
            required,
        });
    }
    let roots: Vec<(u32, u32)> = complex
        .classes
        .iter()
        .map(|class| class.sites[0])
        .collect();
    let presented = roots.len();
    let system = OccurrenceSystem::new(census, roots, horizon);
    let compression = compress(&system);
    let root_items: BTreeMap<ItemId, usize> = (0..presented)
        .map(|root| (system.root_item(root), root))
        .collect();

    let block_count = |blocks: &[BTreeSet<ItemId>]| {
        blocks
            .iter()
            .filter(|block| block.iter().any(|item| root_items.contains_key(item)))
            .count()
    };

    let mut organ_pairs = 0usize;
    let mut disagreements = Vec::new();
    for pair in &compression.collapsed {
        let (Some(left), Some(right)) = (
            root_items.get(&pair.left).copied(),
            root_items.get(&pair.right).copied(),
        ) else {
            continue;
        };
        organ_pairs += 1;
        let index = complex
            .first_difference(left, right)
            .expect("distinct classes differ");
        let mine = complex.materialize(census, left.min(right), left.max(right), index);
        let organ_word: Vec<Step> = pair
            .distinguishing_word
            .iter()
            .filter_map(|input| Step::from_input(*input))
            .collect();
        let organ_axis = pair
            .witness
            .and_then(|(receiver, _, _)| ReceiverAxis::from_id(receiver));
        if organ_word != mine.word
            || organ_axis != mine.axis
            || pair.separated_by_terminus != mine.by_terminus
        {
            disagreements.push((left.min(right), left.max(right)));
        }
    }

    Ok(CrossCheck {
        surface,
        horizon,
        classes: complex.classes.len(),
        conduct_blocks: block_count(&compression.conduct.blocks),
        one_shot_blocks: block_count(&compression.one_shot.blocks),
        refinement_rounds: compression.rounds,
        factorized_pairs: required
            .try_into()
            .expect("bounded by the declared capacity"),
        organ_pairs,
        disagreements,
    })
}

// -------------------------------------------------------------------------------------------------
// The declared family's orbit, and its ablation
// -------------------------------------------------------------------------------------------------

/// A pair of surfaces one axis separates and the other two do not. The orbit assertion: a family
/// whose members all agree has not been shown to be a family.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct AxisWitness {
    pub axis: ReceiverAxis,
    pub left: SurfaceId,
    pub right: SurfaceId,
    pub left_reading: u64,
    pub right_reading: u64,
}

/// For each declared axis, find a witness pair from the corpus's own vocabulary.
pub fn axis_witnesses(census: &CorpusCensus) -> BTreeMap<ReceiverAxis, AxisWitness> {
    let surfaces = census.word_surfaces();
    let mut witnesses = BTreeMap::new();
    for axis in ReceiverAxis::DECLARED {
        let mut buckets: BTreeMap<(u64, u64), (u64, SurfaceId)> = BTreeMap::new();
        for surface in &surfaces {
            let (kind, weight, density) = census.signature(*surface);
            let (held, varying) = match axis {
                ReceiverAxis::Kind => ((weight, density), kind),
                ReceiverAxis::Weight => ((kind, density), weight),
                ReceiverAxis::Density => ((kind, weight), density),
            };
            match buckets.get(&held) {
                Some((seen, other)) if *seen != varying => {
                    witnesses.insert(
                        axis,
                        AxisWitness {
                            axis,
                            left: *other,
                            right: *surface,
                            left_reading: *seen,
                            right_reading: varying,
                        },
                    );
                    break;
                }
                Some(_) => {}
                None => {
                    buckets.insert(held, (varying, *surface));
                }
            }
        }
    }
    witnesses
}

/// What one axis's removal costs a surface's reading. H.0016's transformations clause guarantees
/// removal can only **coarsen**.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct AblationReading {
    pub axis: ReceiverAxis,
    pub blocks_with: usize,
    pub blocks_without: usize,
}

impl AblationReading {
    pub fn contributed(self) -> bool {
        self.blocks_without < self.blocks_with
    }
}

/// Ablate each declared axis in turn on one surface's whole occurrence population.
///
/// Exact and unbounded: an ablated family reads the same window word with one coordinate deleted, so
/// the ablated partition is a **projection** of the factorization and is counted directly. The
/// compression organ's own `AblatedSystem` is the second implementation and
/// [`cross_check_ablation`] runs it against this one.
pub fn ablation_profile(
    census: &CorpusCensus,
    surface: SurfaceId,
    horizon: usize,
) -> Vec<AblationReading> {
    let sites = census.sites(surface);
    let with = sites
        .iter()
        .map(|(whole, position)| window(census, *whole, *position, horizon))
        .collect::<BTreeSet<_>>()
        .len();
    ReceiverAxis::DECLARED
        .into_iter()
        .map(|axis| AblationReading {
            axis,
            blocks_with: with,
            blocks_without: sites
                .iter()
                .map(|(whole, position)| {
                    ablated_window(census, *whole, *position, horizon, axis)
                })
                .collect::<BTreeSet<_>>()
                .len(),
        })
        .collect()
}

/// The compression organ's own `AblatedSystem`, run against [`ablation_profile`] on one surface.
///
/// Quadratic in the presented population, so the caller declares its capacity and this refuses past
/// it with the width the material required.
pub fn cross_check_ablation(
    census: &CorpusCensus,
    surface: SurfaceId,
    horizon: usize,
    declared_capacity: u64,
) -> Result<Vec<AblationReading>, ExhibitionObstructed> {
    let complex = SeparationComplex::read(census, surface, horizon);
    let required = complex.separated_class_pairs();
    if required > BigUint::from(declared_capacity) {
        return Err(ExhibitionObstructed {
            surface,
            horizon,
            declared_capacity,
            required,
        });
    }
    let roots: Vec<(u32, u32)> = complex.classes.iter().map(|class| class.sites[0]).collect();
    let presented = roots.len();
    let system = OccurrenceSystem::new(census, roots, horizon);
    let root_items: BTreeSet<ItemId> = (0..presented).map(|root| system.root_item(root)).collect();
    let block_count = |blocks: &[BTreeSet<ItemId>]| {
        blocks
            .iter()
            .filter(|block| block.iter().any(|item| root_items.contains(item)))
            .count()
    };
    let with = block_count(&compress(&system).conduct.blocks);
    Ok(ReceiverAxis::DECLARED
        .into_iter()
        .map(|axis| {
            let ablated = AblatedSystem {
                inner: &system,
                without: axis.id(),
            };
            AblationReading {
                axis,
                blocks_with: with,
                blocks_without: block_count(&compress(&ablated).conduct.blocks),
            }
        })
        .collect())
}

// -------------------------------------------------------------------------------------------------
// The warping
// -------------------------------------------------------------------------------------------------

/// One row of the warping: what a surface recruits and what recruits it, relative to one iron axis.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Recruitment {
    /// The iron surface occurs **after** this one, within the declared radius.
    pub recruits: BigUint,
    /// The iron surface occurs **before** this one, within the declared radius.
    pub recruited_by: BigUint,
}

impl Recruitment {
    pub fn total(&self) -> BigUint {
        self.recruits.clone() + self.recruited_by.clone()
    }
}

/// The warping: an incidence complex, not a table. A non-iron surface's position **is** which iron
/// surfaces it recruits and which recruit it.
#[derive(Clone, Debug)]
pub struct WarpingIncidence {
    pub radius: usize,
    pub iron: Vec<SurfaceId>,
    pub entries: BTreeMap<(SurfaceId, SurfaceId), Recruitment>,
    /// Rows whose surface is itself iron — the iron field's own incidence, kept separate so the
    /// warping of the non-iron population is readable on its own.
    pub iron_rows: usize,
}

impl WarpingIncidence {
    /// One surface's row, ordered by total incidence descending then by surface — a **presentation**
    /// of a returned complex, never a ranking that decides anything.
    pub fn row(&self, surface: SurfaceId) -> Vec<(SurfaceId, Recruitment)> {
        let mut row: Vec<(SurfaceId, Recruitment)> = self
            .entries
            .range((surface, SurfaceId(0))..=(surface, SurfaceId(u32::MAX)))
            .map(|((_, iron), recruitment)| (*iron, recruitment.clone()))
            .collect();
        row.sort_by(|left, right| {
            right
                .1
                .total()
                .cmp(&left.1.total())
                .then(left.0.cmp(&right.0))
        });
        row
    }

    pub fn nonzero(&self) -> usize {
        self.entries.len()
    }

    /// How many distinct iron axes this surface touches — the width of its warping, reported.
    pub fn support_width(&self, surface: SurfaceId) -> usize {
        self.entries
            .range((surface, SurfaceId(0))..=(surface, SurfaceId(u32::MAX)))
            .count()
    }
}

/// Build the warping incidence over the whole corpus in one pass.
pub fn warping_incidence(
    census: &CorpusCensus,
    iron: &BTreeSet<SurfaceId>,
    radius: usize,
) -> WarpingIncidence {
    let mut is_iron = vec![false; census.all_surfaces().count()];
    for surface in iron {
        is_iron[surface.0 as usize] = true;
    }
    let mut counts: BTreeMap<(SurfaceId, SurfaceId), (u64, u64)> = BTreeMap::new();
    for whole in census.wholes() {
        let stream = &whole.stream;
        for (position, surface) in stream.iter().enumerate() {
            if census.kind(*surface) == Kind::Markup {
                continue;
            }
            let low = position.saturating_sub(radius);
            let high = (position + radius).min(stream.len().saturating_sub(1));
            for neighbour in low..=high {
                if neighbour == position {
                    continue;
                }
                let other = stream[neighbour];
                if !is_iron[other.0 as usize] {
                    continue;
                }
                let entry = counts.entry((*surface, other)).or_insert((0, 0));
                if neighbour > position {
                    entry.0 += 1;
                } else {
                    entry.1 += 1;
                }
            }
        }
    }
    let iron_rows = counts
        .keys()
        .map(|(row, _)| *row)
        .collect::<BTreeSet<_>>()
        .into_iter()
        .filter(|row| is_iron[row.0 as usize])
        .count();
    WarpingIncidence {
        radius,
        iron: iron.iter().copied().collect(),
        entries: counts
            .into_iter()
            .map(|(key, (after, before))| {
                (
                    key,
                    Recruitment {
                        recruits: BigUint::from(after),
                        recruited_by: BigUint::from(before),
                    },
                )
            })
            .collect(),
        iron_rows,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs;

    /// The declared capacity these fixtures run under. A test is a caller and declares its own.
    const TEST_CAPACITY: u64 = 4_096;

    fn scratch(name: &str) -> std::path::PathBuf {
        let root = std::env::temp_dir().join(format!("holonic-token-invariance-{name}"));
        let _ = fs::remove_dir_all(&root);
        for declaration in crate::corpus_census::DECLARED_STRATA {
            fs::create_dir_all(root.join(declaration.relative_root)).unwrap();
        }
        root
    }

    fn write(root: &std::path::Path, relative: &str, text: &str) {
        let path = root.join(relative);
        fs::create_dir_all(path.parent().unwrap()).unwrap();
        fs::write(path, text).unwrap();
    }

    /// A corpus built so both verdicts are forced and neither can be an accident.
    ///
    /// `arxiv` occurs three times and **always** inside `pad ref arxiv . org pad`, so out to
    /// horizon two it has exactly one window. `set` occurs four times across three strata with four
    /// different neighbourhoods, and it is the **denser** of the two. The two readings must come
    /// apart on this material or the conjunction is doing no work.
    ///
    /// The second line of the papers whole exists to give [`axis_witnesses`] something to find:
    /// `abc`/`Abc` differ on `kind` alone, `ref`/`arxiv` on `weight` alone, `pad`/`ref` on
    /// `density` alone.
    fn declared_corpus(name: &str) -> std::path::PathBuf {
        let root = scratch(name);
        write(
            &root,
            "papers/source/mathematics/a.typ",
            "pad pad ref arxiv . org pad pad ref arxiv . org pad pad ref arxiv . org pad pad\n\
             abc Abc abcde xyz xyz\n",
        );
        write(&root, "canon/a.md", "the set of points\n");
        write(&root, "research/records/a.md", "a set with members\n");
        write(&root, "reference/pureholonics-seed/a.md", "set members here and set again\n");
        root
    }

    #[test]
    fn a_surface_used_in_one_construction_is_iron_and_one_used_in_many_is_not() {
        let root = declared_corpus("verdicts");
        let census = CorpusCensus::read(&root).unwrap();

        let arxiv = census.lookup("arxiv").expect("the fixture writes it");
        let set = census.lookup("set").expect("the fixture writes it");

        let iron = separation_reading(&census, arxiv, 1);
        assert_eq!(iron.distinct_windows, 1, "one construction, one window");
        assert_eq!(iron.verdict, Verdict::Iron);
        assert_eq!(
            iron.exhibit(&census, TEST_CAPACITY).expect("within capacity"),
            Vec::new(),
            "an iron surface has no separations at all"
        );

        let fuzzy = separation_reading(&census, set, 1);
        assert!(fuzzy.distinct_windows > 1, "several constructions, several windows");
        assert!(matches!(fuzzy.verdict, Verdict::Separated { .. }));
        let separations = fuzzy.exhibit(&census, TEST_CAPACITY).expect("within capacity");
        assert_eq!(
            BigUint::from(separations.len()),
            fuzzy.complex.separated_class_pairs(),
            "the exhibition is the WHOLE population or it is an obstruction"
        );
        assert!(
            separations.iter().all(|separation| !separation.word.is_empty()),
            "an empty word is the one-shot reading, which held every occurrence together"
        );

        // Density and separation come apart: `set` is the denser of the two AND the separable one.
        assert!(census.occurrences(set) > census.occurrences(arxiv));

        let _ = fs::remove_dir_all(&root);
    }

    /// The iron population can only shrink as the horizon grows: a longer word separates more.
    #[test]
    fn iron_is_monotone_decreasing_in_the_horizon() {
        let root = declared_corpus("monotone");
        let census = CorpusCensus::read(&root).unwrap();
        let near = iron_at(&sweep(&census, 1));
        let far = iron_at(&sweep(&census, 2));
        assert!(
            far.is_subset(&near),
            "iron at horizon 2 must be contained in iron at horizon 1; \
             near={near:?} far={far:?}"
        );
        assert!(!near.is_empty(), "the fixture founds at least one iron surface");
        let _ = fs::remove_dir_all(&root);
    }

    /// The factorization and the organ's Nerode refinement are two implementations of one partition,
    /// checked **pair for pair** over every surface at both declared horizons.
    #[test]
    fn the_factorization_and_the_nerode_refinement_agree_pair_for_pair() {
        let root = declared_corpus("parity");
        let census = CorpusCensus::read(&root).unwrap();
        let mut checked = 0usize;
        for horizon in [1usize, 2] {
            for surface in census.word_surfaces() {
                let check = cross_check(&census, surface, horizon, TEST_CAPACITY)
                    .expect("the fixture is inside the declared capacity");
                assert!(
                    check.agrees(),
                    "horizon {horizon}, {:?}: {check:?}",
                    census.surface(surface)
                );
                checked += 1;
            }
        }
        assert!(checked > 0, "the cross-check must run on something");
        let _ = fs::remove_dir_all(&root);
    }

    /// The cross-check has a non-trivial orbit: it is comparing populations that are not empty, so a
    /// disagreement is a thing the material could have produced.
    #[test]
    fn the_cross_check_ranges_over_a_non_empty_pair_population() {
        let root = declared_corpus("orbit-of-the-check");
        let census = CorpusCensus::read(&root).unwrap();
        let set = census.lookup("set").unwrap();
        let check = cross_check(&census, set, 1, TEST_CAPACITY).expect("within capacity");
        assert!(
            check.organ_pairs > 0 && check.factorized_pairs > 0,
            "a cross-check over zero pairs cannot fail and is not evidence: {check:?}"
        );
        assert_eq!(check.factorized_pairs, check.organ_pairs);
        let _ = fs::remove_dir_all(&root);
    }

    /// The declared family's orbit is non-trivial: each axis separates a pair the other two do not.
    #[test]
    fn each_declared_axis_separates_a_pair_the_others_do_not() {
        let root = declared_corpus("orbit");
        let census = CorpusCensus::read(&root).unwrap();
        let witnesses = axis_witnesses(&census);
        for axis in ReceiverAxis::DECLARED {
            let witness = witnesses
                .get(&axis)
                .unwrap_or_else(|| panic!("axis {} found no witness", axis.name()));
            let left = census.signature(witness.left);
            let right = census.signature(witness.right);
            let differing: Vec<ReceiverAxis> = ReceiverAxis::DECLARED
                .into_iter()
                .filter(|other| other.read(left) != other.read(right))
                .collect();
            assert_eq!(
                differing,
                vec![axis],
                "{} must be the ONLY axis separating {:?} from {:?}",
                axis.name(),
                census.surface(witness.left),
                census.surface(witness.right)
            );
        }
        let _ = fs::remove_dir_all(&root);
    }

    /// Removing a receiver may only coarsen — H.0016's transformations clause, on real material —
    /// and the projection and the organ's own `AblatedSystem` return the same numbers.
    #[test]
    fn ablating_an_axis_never_refines_the_reading_and_both_routes_agree() {
        let root = declared_corpus("ablation");
        let census = CorpusCensus::read(&root).unwrap();
        let set = census.lookup("set").unwrap();
        let projected = ablation_profile(&census, set, 1);
        let organ = cross_check_ablation(&census, set, 1, TEST_CAPACITY).expect("within capacity");
        assert_eq!(projected.len(), 3);
        assert_eq!(
            projected, organ,
            "the projection and `AblatedSystem` are two implementations of one ablation"
        );
        for reading in &projected {
            assert!(
                reading.blocks_without <= reading.blocks_with,
                "{} ablated REFINED {} -> {}",
                reading.axis.name(),
                reading.blocks_with,
                reading.blocks_without
            );
        }
        let _ = fs::remove_dir_all(&root);
    }

    /// The warping is an incidence a non-iron surface actually carries, with both arms distinct.
    #[test]
    fn the_warping_carries_both_arms_and_they_are_not_the_same_number() {
        let root = declared_corpus("warping");
        let census = CorpusCensus::read(&root).unwrap();
        let iron = iron_at(&sweep(&census, 1));
        let incidence = warping_incidence(&census, &iron, 2);
        assert!(incidence.nonzero() > 0, "the iron field must warp something");

        let org = census.lookup("org").expect("the fixture writes it");
        assert!(iron.contains(&org), "`org` only ever follows `arxiv .`");
        let pad = census.lookup("pad").expect("the fixture writes it");
        assert!(!iron.contains(&pad), "`pad` stands in many places and is not iron");
        let row = incidence.row(pad);
        assert!(!row.is_empty(), "`pad` sits within two steps of `org`");
        let recruitment = &row.iter().find(|(id, _)| *id == org).expect("`org` is in reach").1;
        assert_ne!(
            recruitment.recruits, recruitment.recruited_by,
            "the two arms are directions, not one number counted twice"
        );
        let _ = fs::remove_dir_all(&root);
    }

    /// An iron verdict on one occurrence could not have come out otherwise, and the reading says so
    /// with an exact count rather than a hedge. `CLAUDE.md` §8's tautology rule.
    #[test]
    fn an_iron_verdict_carries_the_exact_number_of_non_separations_it_survived() {
        let root = declared_corpus("tautology");
        let census = CorpusCensus::read(&root).unwrap();
        let reading = sweep(&census, 2);

        let arxiv = census.lookup("arxiv").unwrap();
        let witnessed = &reading[&arxiv];
        assert!(witnessed.witnessed_iron());
        assert!(!witnessed.vacuously_iron());
        assert_eq!(
            witnessed.survived_pairs(),
            BigUint::from(3u32),
            "three occurrences is C(3,2) = 3 pairwise non-separations"
        );

        let abcde = census.lookup("abcde").unwrap();
        let vacuous = &reading[&abcde];
        assert!(vacuous.verdict.is_iron());
        assert!(vacuous.vacuously_iron(), "one occurrence has no pair to separate");
        assert_eq!(vacuous.survived_pairs(), BigUint::from(0u32));

        let iron = iron_at(&reading);
        let witnessed_only = witnessed_iron_at(&reading);
        assert!(witnessed_only.is_subset(&iron));
        assert!(
            witnessed_only.len() < iron.len(),
            "the fixture carries both shapes or this split proves nothing"
        );
        let _ = fs::remove_dir_all(&root);
    }

    /// The separated population over the whole occurrence set is exact and is **not** `C(N,2)`:
    /// occurrences sharing a window are held together, and the difference is the factorization.
    #[test]
    fn the_separated_occurrence_population_excludes_the_pairs_inside_a_window_class() {
        let root = declared_corpus("occurrence-pairs");
        let census = CorpusCensus::read(&root).unwrap();
        let arxiv = census.lookup("arxiv").unwrap();
        let reading = separation_reading(&census, arxiv, 1);
        assert_eq!(reading.survived_pairs(), BigUint::from(3u32));
        assert_eq!(
            reading.separated_occurrence_pairs(),
            BigUint::from(0u32),
            "three occurrences in one window class separate into nothing"
        );

        let set = census.lookup("set").unwrap();
        let fuzzy = separation_reading(&census, set, 1);
        let exhibited = fuzzy.exhibit(&census, TEST_CAPACITY).expect("within capacity");
        let from_pairs: BigUint = exhibited
            .iter()
            .map(|separation| separation.occurrence_pairs())
            .sum();
        assert_eq!(
            from_pairs,
            fuzzy.separated_occurrence_pairs(),
            "the class-pair multiplicities must sum to the occurrence-pair population"
        );
        let _ = fs::remove_dir_all(&root);
    }

    /// A capacity the material exceeds returns a typed obstruction naming the required width, and
    /// **no separations at all** — never a prefix a caller could mistake for the whole.
    #[test]
    fn an_exceeded_capacity_returns_an_obstruction_and_never_a_prefix() {
        let root = declared_corpus("obstruction");
        let census = CorpusCensus::read(&root).unwrap();
        let set = census.lookup("set").unwrap();
        let reading = separation_reading(&census, set, 1);
        let required = reading.complex.separated_class_pairs();
        assert!(required > BigUint::from(1u32), "the fixture must exceed a capacity of one");

        let obstruction = reading
            .exhibit(&census, 1)
            .expect_err("a capacity of one cannot hold this population");
        assert_eq!(obstruction.declared_capacity, 1);
        assert_eq!(obstruction.required, required);
        assert_eq!(obstruction.surface, set);

        // The standing is preserved: the complex still answers everything that is not the
        // materialization, and a larger declaration returns the population whole.
        assert!(reading.shortest_separation(&census).is_some());
        assert_eq!(
            BigUint::from(reading.exhibit(&census, TEST_CAPACITY).expect("fits").len()),
            required
        );
        let _ = fs::remove_dir_all(&root);
    }

    /// The window is an ordered word whose lexicographic order is the organ's refinement order, and
    /// the index arithmetic that reads a word off it is exact.
    #[test]
    fn a_window_index_names_the_word_the_organ_would_have_walked() {
        assert_eq!(step_at(0), (Step::Left, 1));
        assert_eq!(step_at(1), (Step::Right, 1));
        assert_eq!(step_at(2), (Step::Left, 2));
        assert_eq!(step_at(3), (Step::Right, 2));
        assert_eq!(offset_at(0), -1);
        assert_eq!(offset_at(1), 1);
        assert_eq!(offset_at(2), -2);
        assert_eq!(offset_at(3), 2);
    }

    /// A separation resolved by a terminus rather than by a receiver is returned as such, on
    /// material that forces one: the papers whole opens on `pad`, so that occurrence has no left
    /// neighbour while every other `pad` does.
    #[test]
    fn a_terminus_is_a_distinction_and_is_named_as_one() {
        let root = declared_corpus("terminus");
        let census = CorpusCensus::read(&root).unwrap();
        let pad = census.lookup("pad").unwrap();
        let reading = separation_reading(&census, pad, 1);
        let separations = reading.exhibit(&census, TEST_CAPACITY).expect("within capacity");
        assert!(
            separations.iter().any(|separation| separation.by_terminus),
            "the opening `pad` has no left neighbour and every other one does: {separations:?}"
        );
        let check = cross_check(&census, pad, 1, TEST_CAPACITY).expect("within capacity");
        assert!(check.agrees(), "the organ must agree about the terminus too: {check:?}");
        let _ = fs::remove_dir_all(&root);
    }
}

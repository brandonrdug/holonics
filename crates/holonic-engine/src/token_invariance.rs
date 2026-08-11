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
//! ## The declared receiver family: three that read a spelling and one that does not
//!
//! [`ReceiverAxis`] declares four receivers, each reading one coordinate of a [`Reading`]:
//!
//! | axis | what it sees | reads the neighbour's |
//! |---|---|---|
//! | `Kind` | the orthographic kind of the surface at the position — six values | **spelling** |
//! | `Weight` | its length band — five values | **spelling** |
//! | `Density` | its **density band**, `floor(log2 N)` on the corpus census | **spelling** (a count of it) |
//! | `Conduct` | its [`ConductSignature`] — the orthographic axes the corpus holds constant around it everywhere else, and whether it ever runs out of whole | **conduct** |
//!
//! `Density` is the axis Brandon's question first asks for: comprehension curving around *iron
//! recurrences (density)* requires density to be something a **receiver can see**, not only
//! something a reader tabulates. It is derived from `Π` and it measures; it selects nothing.
//!
//! **`Conduct` exists because the first three are one species and could not answer the question.**
//! Measured 2026-08-09 on the declared corpus at horizon 2, before this axis: `tensor`, `vector`,
//! `lemma`, `group`, `field`, `holon`, `receiver` and `exact` were **all** `Varying` — no declared
//! family held any of them — and the 1,269 surfaces that did collapse were URL components, DOI
//! fragments and timestamps. The reason was not a missing faculty. `tensor` fails to collapse
//! because it stands next to markup in one sentence and a word in the next, and `Kind` separates
//! `markup` from `lower`. **That is typography, not meaning.**
//!
//! So the fourth axis reads, of the surface standing at the position, *what the corpus did with that
//! surface everywhere else*: the block of the down-set lattice its own occurrence population lands
//! in under `receiver_exact_compression`'s Nerode partition. Two surfaces with nothing orthographic
//! in common can share the reading, and two spelled alike can differ — which is exactly what
//! `Kind`, `Weight` and `Density` cannot do.
//!
//! **The axis is DECLARED, not founded by `founded_receiver::found_to_exhaustion`, and the
//! difference is measured rather than asserted.** That organ's two species — `ContinuationAperture`
//! and `ConductReach` — both read the *system's own successor relation*, and a surface population
//! has none, so run on one it reaches `FoundingPressure::Congestion` and then refuses
//! `FoundingRefusal::FoundedNothing`. `examples/the_axis_reads_what_the_neighbour_does` drives that
//! refusal. What the conduct axis is, in that organ's vocabulary, is a **third species**: the
//! pressure is congestion — the orthographic panel routing the whole vocabulary through one
//! distinction — and the engineering answer is another pathway rather than a finer version of the
//! same one. [`surface_residue`] measures its residue and its capacity under that module's own law.
//!
//! [`axis_witnesses`] proves the family's orbit is non-trivial by exhibiting, for each axis, a pair
//! of surfaces that axis separates and the other three do not.
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
//!
//! ## The other pole, and why it cannot be stated at the full family
//!
//! Iron is `distinct_windows == 1`, and on the real corpus the witnessed iron population is
//! dominated by **formulaic** surfaces — a citation fragment, a timestamp, a domain name. That is
//! the reading working correctly and it is not the object Brandon named. His object is `tensor` and
//! `vector`: *"Regardless of the arbitrary use cases of the words, they generally point to similar
//! objects."* A surface that points to one object **through** varied use is the **opposite** pole —
//! many distinct windows that nonetheless land in one conduct block.
//!
//! **That statement is empty at the full declared family, and the reason is a theorem of this
//! module rather than a property of any corpus.** Two occurrences separate exactly when their
//! windows differ (the factorization above), so the conduct-block count of a surface's occurrence
//! population **is** its distinct-window count — which is what [`cross_check`] asserts when it
//! requires `classes == conduct_blocks`. So `windows > 1 && blocks == 1` is unsatisfiable, for every
//! surface, at every horizon, on every material. A deeper horizon only separates more. **The
//! collapse cannot come from refining; it can only come from coarsening the receiver family.**
//!
//! So the verdict beside iron names the family at which the collapse happens, and the family is read
//! off the material rather than chosen:
//!
//! > A surface is **conduct-invariant** when the full declared family separates its occurrences —
//! > `distinct_windows > 1`, so it is genuinely used variously — while some **nonempty** declared
//! > sub-family holds them in **one conduct block**.
//!
//! The collapsing families form a **down-set with a single maximal element**, so the verdict is not
//! a search over the sixteen sub-families. Removing a receiver may only coarsen (H.0016's
//! transformations clause), so `F` collapses the population exactly when
//!
//! ```text
//!   F ⊆ constant_axes(s)     and     the TERMINUS pattern does not vary
//! ```
//!
//! where `constant_axes(s)` is the set of declared axes whose reading agrees across every occurrence
//! at every offset. The second clause is separate because **a terminus is family-invariant**:
//! deleting a receiver never merges `<end of whole>` with a reading, so a surface whose occurrences
//! disagree about whether an offset exists at all is separated under *every* family including the
//! empty one. [`ConductInvariance`] returns both, and `constant_axes` **is** the maximal collapsing
//! family.
//!
//! Three properties make the verdict falsifiable rather than a relabelling:
//!
//! 1. **It is disjoint from iron by construction** — it requires `windows > 1` and iron is
//!    `windows == 1` — so the measured population partitions three ways with nothing double-counted.
//! 2. **It cannot be vacuous.** `windows > 1` forces at least two occurrences, so
//!    [`ConductInvariance::separations_withstood`] — the exact count of occurrence pairs the **full**
//!    family separates and the collapsing family does not — is nonzero on every surface the verdict
//!    admits. Iron's non-vacuity had to be added as a separate clause; here it is forced.
//! 3. **The collapsing family is a PROPER nonempty subset.** All three axes constant with a constant
//!    terminus pattern means the windows are identical, which is iron. So a conduct-invariant surface
//!    exhibits, by name, both the axes its material holds and the axes its material varies.
//!
//! And it costs nothing quadratic: [`SeparationComplex::conduct_invariance`] reads the sorted window
//! classes once, `O(d · horizon)`, and never materializes a pair. A surface whose exhibition is
//! obstructed still receives a verdict — the route does not go through the quadratic population at
//! all.
//!
//! **The two costs are different objects and conflating them was a real error.** The reading is
//! `O(d · horizon)` — the volume of the causal diamond the window enumerates. The *exhibition* is
//! `C(d, 2)` — the pair product, which is a presentation and not a transport. A caller's declared
//! capacity guards only the second; it bounds a `Vec` this organ writes out, never the work it does.
//! An earlier form of this paragraph called that capacity *"the aperture law"*, which promoted an
//! output-buffer guard to a law and then reasoned from the promotion. See this file's
//! *"The horizon, read off the material"* section for what actually bounds a receiver.

use std::collections::{BTreeMap, BTreeSet};

use num_bigint::BigUint;

use crate::corpus_census::{CorpusCensus, Kind, SurfaceId, weight_band_name};
use crate::hardware_cover::{ChartId, CoverDecomposition, FrontCell, HardwareCover};
use crate::receiver_exact_compression::{
    AblatedSystem, InputId, ItemId, Observation, ObservedSystem, ReceiverId, compress,
};

/// One declared receiver. Each reads exactly one coordinate of a [`Reading`], so each is separately
/// ablatable and each one's contribution is separately measurable.
///
/// **Three of the four are orthographic and one is not.** `Kind`, `Weight` and `Density` read the
/// surface standing at the position — its case class, its length band, its corpus count. `Conduct`
/// reads what the corpus **does** with that surface, and the difference is the whole content of this
/// enum; see the module header.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ReceiverAxis {
    Kind,
    Weight,
    Density,
    Conduct,
}

impl ReceiverAxis {
    pub const DECLARED: [ReceiverAxis; 4] = [
        ReceiverAxis::Kind,
        ReceiverAxis::Weight,
        ReceiverAxis::Density,
        ReceiverAxis::Conduct,
    ];

    /// The three axes that read the neighbour's **spelling**. The declared panel before the conduct
    /// axis entered, kept nameable so every reading can be taken at both panels on one material.
    pub const ORTHOGRAPHIC: [ReceiverAxis; 3] =
        [ReceiverAxis::Kind, ReceiverAxis::Weight, ReceiverAxis::Density];

    pub fn id(self) -> ReceiverId {
        ReceiverId(self.index() as u64)
    }

    pub fn from_id(id: ReceiverId) -> Option<Self> {
        Self::DECLARED.get(id.0 as usize).copied()
    }

    /// This axis's position in [`ReceiverAxis::DECLARED`], which is both the coordinate it reads out
    /// of a [`Reading`] and the bit [`ReceiverFamily`] uses for it.
    pub fn index(self) -> usize {
        match self {
            ReceiverAxis::Kind => 0,
            ReceiverAxis::Weight => 1,
            ReceiverAxis::Density => 2,
            ReceiverAxis::Conduct => 3,
        }
    }

    pub fn name(self) -> &'static str {
        match self {
            ReceiverAxis::Kind => "kind",
            ReceiverAxis::Weight => "weight",
            ReceiverAxis::Density => "density",
            ReceiverAxis::Conduct => "conduct",
        }
    }

    /// Whether this axis reads how the neighbour is **written**. `Conduct` is the one that does not.
    pub fn is_orthographic(self) -> bool {
        self != ReceiverAxis::Conduct
    }

    /// What this axis reads out of one position's reading.
    pub fn read(self, reading: Reading) -> u64 {
        reading[self.index()]
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
            ReceiverAxis::Conduct => ConductSignature::decode(reading).to_string(),
        }
    }
}

/// A declared sub-family of [`ReceiverAxis::DECLARED`], as a bitmask over `ReceiverAxis::index`.
///
/// The lattice of sub-families is where conduct-invariance is stated, because at the full family the
/// conduct-block count and the distinct-window count are the same number and "many windows, one
/// block" is unsatisfiable. Removing a receiver may only coarsen — H.0016's transformations clause —
/// so the families that collapse a given surface are **downward closed**, and naming the maximal one
/// names all of them.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub struct ReceiverFamily(pub u8);

impl ReceiverFamily {
    /// No receiver at all. It collapses every reading a receiver could make and would certify a
    /// verdict that could not have come out otherwise, so no verdict is stated at it — but it is
    /// **not** vacuous as a system: a terminus is still a distinction, which is exactly why the
    /// terminus clause is separate.
    pub const EMPTY: ReceiverFamily = ReceiverFamily(0);
    /// All four declared axes — the family every other reading in this module runs at.
    pub const FULL: ReceiverFamily = ReceiverFamily(0b1111);
    /// The three axes that read the neighbour's spelling. The panel this module declared before the
    /// conduct axis, and the family every "before" figure is taken at.
    pub const ORTHOGRAPHIC: ReceiverFamily = ReceiverFamily(0b111);

    pub fn of(axes: impl IntoIterator<Item = ReceiverAxis>) -> Self {
        ReceiverFamily(axes.into_iter().fold(0u8, |bits, axis| bits | (1 << axis.index())))
    }

    pub fn contains(self, axis: ReceiverAxis) -> bool {
        self.0 & (1 << axis.index()) != 0
    }

    pub fn with(self, axis: ReceiverAxis) -> Self {
        ReceiverFamily(self.0 | (1 << axis.index()))
    }

    pub fn without(self, axis: ReceiverAxis) -> Self {
        ReceiverFamily(self.0 & !(1 << axis.index()))
    }

    pub fn axes(self) -> Vec<ReceiverAxis> {
        ReceiverAxis::DECLARED
            .into_iter()
            .filter(|axis| self.contains(*axis))
            .collect()
    }

    pub fn len(self) -> usize {
        self.0.count_ones() as usize
    }

    pub fn is_empty(self) -> bool {
        self.0 == 0
    }

    /// The axes this family does **not** read. For a conduct-invariant surface this is exactly the
    /// set of axes its material varies, so the verdict exhibits both halves.
    pub fn complement(self) -> Self {
        ReceiverFamily(Self::FULL.0 & !self.0)
    }

    pub fn is_subset_of(self, other: Self) -> bool {
        self.0 & other.0 == self.0
    }

    /// Every sub-family of this one, coarsest first.
    pub fn subsets(self) -> Vec<Self> {
        let mut subsets: Vec<Self> = (0..=Self::FULL.0)
            .map(ReceiverFamily)
            .filter(|candidate| candidate.is_subset_of(self))
            .collect();
        subsets.sort_by_key(|family| (family.len(), family.0));
        subsets
    }
}

impl std::fmt::Display for ReceiverFamily {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.is_empty() {
            return write!(formatter, "{{}}");
        }
        write!(
            formatter,
            "{{{}}}",
            self.axes()
                .into_iter()
                .map(ReceiverAxis::name)
                .collect::<Vec<_>>()
                .join(",")
        )
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

/// What the declared family reads at one position, one coordinate per axis in
/// [`ReceiverAxis::DECLARED`] order.
pub type Reading = [u64; 4];

/// The complete information a word of length at most `horizon` can reach from one occurrence,
/// written **in the order the organ's breadth-first search reaches it**: offset `-1`, `+1`, `-2`,
/// `+2`, …, with `None` where the whole ends.
///
/// The order is the content. Lexicographic comparison of two windows is Moore refinement of the two
/// occurrences they belong to, and the first differing index is the round at which they separate.
pub type Window = Vec<Option<Reading>>;

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

// -------------------------------------------------------------------------------------------------
// The conduct axis: what the corpus DOES with a surface, not how the surface is written
// -------------------------------------------------------------------------------------------------

/// **One surface's conduct signature**: the axes its own whole occurrence population holds constant
/// under the orthographic panel, and whether that population ever runs out of whole.
///
/// This is exactly the pair [`ConductInvariance`] returns — `constant_axes` and `terminus_varies` —
/// taken at the orthographic panel, which is the **block of the down-set lattice** the surface's
/// occurrences land in under `receiver_exact_compression`'s Nerode partition. It is a property of
/// the surface's *usage across the whole corpus*, so two surfaces with nothing orthographic in
/// common can share it and two spelled alike can differ.
///
/// **A surface with one window is iron, and iron is `holds = ORTHOGRAPHIC, terminus = false`** —
/// nothing varied, so nothing is in the varying set. The two statements are the same statement:
/// if all three axes and the terminus pattern agree at every offset, every window is the same word.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub struct ConductSignature {
    /// The orthographic axes this surface's material holds constant at every offset.
    pub holds: ReceiverFamily,
    /// Two of its occurrences disagree about whether some offset exists at all.
    pub terminus_varies: bool,
}

impl ConductSignature {
    /// The exact token a receiver returns. **Derived, never authored**: the collapsing family's own
    /// bitmask shifted by the one bit the terminus needs, so the token *is* the lattice point.
    pub fn encode(self) -> u64 {
        (u64::from(self.holds.0) << 1) | u64::from(self.terminus_varies)
    }

    pub fn decode(token: u64) -> Self {
        Self {
            holds: ReceiverFamily((token >> 1) as u8 & ReceiverFamily::ORTHOGRAPHIC.0),
            terminus_varies: token & 1 == 1,
        }
    }

    /// The surface's material never distinguished anything the orthographic panel reads, which is
    /// [`ConductVerdict::Iron`] at that panel.
    pub fn is_iron(self) -> bool {
        self.holds == ReceiverFamily::ORTHOGRAPHIC && !self.terminus_varies
    }
}

impl std::fmt::Display for ConductSignature {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            formatter,
            "holds {}{}",
            self.holds,
            if self.terminus_varies { " +terminus" } else { "" }
        )
    }
}

/// **The founded conduct axis, as a reading per surface.**
///
/// The three declared axes read the neighbour's spelling. This one reads the neighbour's
/// [`ConductSignature`] — what the corpus did with it everywhere else — so it is the only coordinate
/// in a [`Reading`] that is not a function of the surface's characters.
///
/// **It is founded over EVERY surface, markup included.** `CorpusCensus::sites` records word
/// surfaces only, because the *measured population* is the words; but a receiver standing next to a
/// `#` must still read something, and returning a declared outside-value for markup would make the
/// axis orthographic again at exactly the place the reading is supposed to bite. So the atlas walks
/// the streams itself and gives markup a conduct signature on the same terms as a word.
///
/// **The founding horizon is the caller's**, never this organ's, and it need not be the horizon a
/// later reading runs at — the two are different declarations and both are carried.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ConductAtlas {
    founding_horizon: usize,
    /// One token per `SurfaceId`, indexed by `SurfaceId.0`.
    tokens: Vec<u64>,
}

impl ConductAtlas {
    /// Found the atlas over the whole corpus at a declared horizon.
    ///
    /// One pass to collect every surface's occurrences, then one pass per surface comparing every
    /// occurrence's orthographic window against the first. `O(total tokens · horizon)`; no pair is
    /// materialized and no aperture participates.
    pub fn found(census: &CorpusCensus, founding_horizon: usize) -> Self {
        let population = census.all_surfaces().count();
        let mut sites: Vec<Vec<(u32, u32)>> = vec![Vec::new(); population];
        for (whole, record) in census.wholes().iter().enumerate() {
            for (position, surface) in record.stream.iter().enumerate() {
                sites[surface.0 as usize].push((whole as u32, position as u32));
            }
        }
        let tokens = sites
            .iter()
            .map(|occurrences| {
                orthographic_signature(census, occurrences, founding_horizon).encode()
            })
            .collect();
        Self {
            founding_horizon,
            tokens,
        }
    }

    /// The atlas **before** founding: one token for every surface.
    ///
    /// A constant axis separates nothing, so its residue is empty and — by `founded_receiver`'s
    /// capacity law — it takes the minimum capacity and dilates maximally. It is the null the orbit
    /// is measured against, and it is what the declared panel amounted to before the axis existed.
    pub fn unfounded(census: &CorpusCensus, founding_horizon: usize) -> Self {
        Self {
            founding_horizon,
            tokens: vec![0; census.all_surfaces().count()],
        }
    }

    /// An atlas carrying tokens a caller supplies. The route every declared null takes: the tokens
    /// are the caller's, the reading machinery is unchanged, and the two are therefore comparable on
    /// one material.
    pub fn declaring(founding_horizon: usize, tokens: Vec<u64>) -> Self {
        Self {
            founding_horizon,
            tokens,
        }
    }

    pub fn founding_horizon(&self) -> usize {
        self.founding_horizon
    }

    /// The token this axis returns for a surface. A surface outside the atlas reads `0`, which is
    /// the same token [`Self::unfounded`] gives everything — never a sentinel a caller could mistake
    /// for a founded reading.
    pub fn token(&self, surface: SurfaceId) -> u64 {
        self.tokens.get(surface.0 as usize).copied().unwrap_or(0)
    }

    pub fn signature(&self, surface: SurfaceId) -> ConductSignature {
        ConductSignature::decode(self.token(surface))
    }

    pub fn tokens(&self) -> &[u64] {
        &self.tokens
    }

    /// How many surfaces carry each token. **The orbit of the axis itself**: an atlas returning one
    /// token has founded nothing, and one returning a distinct token per surface has founded an
    /// identity map. Both are reported rather than assumed away.
    pub fn population(&self) -> BTreeMap<u64, usize> {
        let mut population: BTreeMap<u64, usize> = BTreeMap::new();
        for token in &self.tokens {
            *population.entry(*token).or_default() += 1;
        }
        population
    }

    /// **The atlas with the terminus bit of every reading ablated.**
    ///
    /// A [`ConductSignature`] carries two things: which orthographic distinctions the corpus never
    /// made around the surface, and whether the surface ever stood within the horizon of a **whole's
    /// edge**. The second is a property of *document length and placement* rather than of how the
    /// surface is used, so it is the one coordinate of this axis that is arguably the same species
    /// as the typography the axis exists to get past.
    ///
    /// Ablating it is a measurement, not a repair: the ablated axis is strictly coarser, so it
    /// collapses more, and a coarser axis approaches the constant one whose ceiling is meaningless.
    /// Both numbers have to be read together, which is why this returns an atlas rather than
    /// replacing one.
    pub fn without_terminus(&self) -> Self {
        Self {
            founding_horizon: self.founding_horizon,
            tokens: self.tokens.iter().map(|token| token & !1).collect(),
        }
    }

    /// Every surface whose reading satisfies a caller's predicate, complete and in surface order.
    /// A **stated** sub-population, never a prefix: the caller names the class and receives all of
    /// it.
    pub fn surfaces_reading(&self, admits: impl Fn(ConductSignature) -> bool) -> Vec<SurfaceId> {
        self.tokens
            .iter()
            .enumerate()
            .filter(|(_, token)| admits(ConductSignature::decode(**token)))
            .map(|(place, _)| SurfaceId(place as u32))
            .collect()
    }

    /// The atlas with its tokens **permuted across surfaces** by a caller-declared permutation.
    ///
    /// The multiset of readings is preserved exactly, so the axis is *equally coarse* and carries no
    /// relation whatever to the material. This is the sharpest available null: any collapse that
    /// survives it is a consequence of the axis's coarseness and not of what it read.
    pub fn permuted(&self, permutation: &[usize]) -> Self {
        Self {
            founding_horizon: self.founding_horizon,
            tokens: (0..self.tokens.len())
                .map(|place| {
                    permutation
                        .get(place)
                        .and_then(|from| self.tokens.get(*from))
                        .copied()
                        .unwrap_or(0)
                })
                .collect(),
        }
    }
}

/// The orthographic conduct signature of one surface's occurrence population.
///
/// The same comparison [`SeparationComplex::conduct_invariance`] performs, taken at
/// [`ReceiverFamily::ORTHOGRAPHIC`] and over raw occurrences rather than window classes. It has to
/// be stated separately and prior, because the conduct axis is what the founded reading adds and a
/// coordinate cannot be an input to its own founding.
///
/// Comparing every occurrence against the **first** is not weaker than comparing every pair: at one
/// offset an axis returns one value per occurrence, so all-equal-to-the-first is all-equal.
fn orthographic_signature(
    census: &CorpusCensus,
    occurrences: &[(u32, u32)],
    horizon: usize,
) -> ConductSignature {
    let mut varying = ReceiverFamily::EMPTY;
    let mut terminus_varies = false;
    let Some((first_whole, first_position)) = occurrences.first().copied() else {
        return ConductSignature {
            holds: ReceiverFamily::ORTHOGRAPHIC,
            terminus_varies: false,
        };
    };
    let reference: Vec<Option<(u64, u64, u64)>> =
        orthographic_window(census, first_whole, first_position, horizon);
    for (whole, position) in &occurrences[1..] {
        let other = orthographic_window(census, *whole, *position, horizon);
        for (left, right) in reference.iter().zip(other.iter()) {
            match (left, right) {
                (Some(left), Some(right)) => {
                    for axis in ReceiverAxis::ORTHOGRAPHIC {
                        let coordinate = match axis {
                            ReceiverAxis::Kind => (left.0, right.0),
                            ReceiverAxis::Weight => (left.1, right.1),
                            _ => (left.2, right.2),
                        };
                        if coordinate.0 != coordinate.1 {
                            varying = varying.with(axis);
                        }
                    }
                }
                (None, None) => {}
                _ => terminus_varies = true,
            }
        }
    }
    ConductSignature {
        holds: ReceiverFamily(ReceiverFamily::ORTHOGRAPHIC.0 & !varying.0),
        terminus_varies,
    }
}

/// One occurrence's window under the orthographic panel alone. The founding reading.
fn orthographic_window(
    census: &CorpusCensus,
    whole: u32,
    position: u32,
    horizon: usize,
) -> Vec<Option<(u64, u64, u64)>> {
    let stream = &census.wholes()[whole as usize].stream;
    (0..2 * horizon)
        .map(|index| {
            let site = position as i64 + offset_at(index);
            if site < 0 || site >= stream.len() as i64 {
                None
            } else {
                Some(census.signature(stream[site as usize]))
            }
        })
        .collect()
}

/// What the declared family reads off one surface: three orthographic coordinates and the founded
/// conduct token.
pub fn reading(census: &CorpusCensus, atlas: &ConductAtlas, surface: SurfaceId) -> Reading {
    let (kind, weight, density) = census.signature(surface);
    [kind, weight, density, atlas.token(surface)]
}

/// The window of the occurrence at `position` in `whole`.
pub fn window(
    census: &CorpusCensus,
    atlas: &ConductAtlas,
    whole: u32,
    position: u32,
    horizon: usize,
) -> Window {
    let stream = &census.wholes()[whole as usize].stream;
    let mut window = Vec::with_capacity(2 * horizon);
    for index in 0..2 * horizon {
        let site = position as i64 + offset_at(index);
        if site < 0 || site >= stream.len() as i64 {
            window.push(None);
        } else {
            window.push(Some(reading(census, atlas, stream[site as usize])));
        }
    }
    window
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

// -------------------------------------------------------------------------------------------------
// The charts of the separation object, and the atlas that covers the widest one
// -------------------------------------------------------------------------------------------------
//
// **A capacity is not a quantity this organ has any business holding.** Until 2026-08-10 both
// drivers carried `const DECLARED_CAPACITY: u64 = 8_192` and refused any surface whose separation
// population exceeded it. Brandon, on that number: *"it's a magic capacity you can't justify… there
// are hypergeometric higher dimensional causal reasons for capacity demands to grow and change in
// varying charts and local manifold regions, this is group structures."*
//
// He is right, and the arithmetic says so exactly. The classes are **orbits**: the occurrence
// population quotiented by what the declared receiver family can distinguish inside the cone, so
// `d = |X/G|`. What the capacity bounded was
//
// ```text
//    C(d,2)  =  rank Λ²(ℚ^{X/G})  =  edges of K_d  =  the 2-faces of the simplex on the orbits
// ```
//
// — one graded piece of the Boolean lattice `Σ_k C(d,k) = 2^d`, which is `H.0150`'s crossing depth
// with inclusion–exclusion's `(−1)^{k−1}` as its Möbius function. And `C(d,k)` at fixed `k` is a
// **hypergeometric term** in `d` in the strict sense — `C(d,2)/C(d−1,2) = d/(d−2)` is a rational
// function of the index — with `Σ_k C(d,k)x^k = (1+x)^d` the degenerate `₂F₁`.
//
// `d` moves for two independent reasons, both group data: coarsening the receiver family merges
// orbits, and deepening the cone refines the partition. So `d` is a **fibre dimension that varies
// over the base**, and a single constant is a constant section of a bundle that has none. Measured
// on the declared corpus: `"the"` carries 37,530 classes — `C(d,2) = 704,231,685` — while a rare
// surface carries 2, where it is 1. Eight orders of magnitude, one law.
//
// # The charts, and why the refusal was a wall in front of an atlas
//
// The reading lives on the **orbit** chart, `d` points. The exhibition lives on the **pair** chart,
// `C(d,2)` points. Those are two charts of one object and the transition multiplies dimension by
// `(d−1)/2`. A capacity was a caller trying to bound the *local degree of a chart transition* with
// a scalar, which cannot be done: the degree is local and varies over the base.
//
// [`SeparationComplex::exhibit_class`] has always returned the **star** of one class — `d−1`
// separations, transition degree **1**. `K_d` is covered by `d` such stars, each pair lying in
// exactly two, `d(d−1)/2 = C(d,2)`. Group-theoretically that is the point-stabilizer decomposition
// of the pair space, and it is an atlas rather than an approximation. So a caller who cannot hold
// the pair chart does not lose anything: it reads the same object through [`pair_atlas`], `d`
// charts of degree one. **That is a rebase — `H.0104`, invertible, remainder zero — not a loss.**

/// Which chart of one surface's separation object a caller is reading in.
///
/// The caller names the chart; the demand follows from `d` by the transition degree and is
/// **computed**, never declared.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum SeparationChart {
    /// The orbit chart: the classes themselves, `d` points. Degree 1 over the reading.
    Orbit,
    /// The star of one class: `d − 1` separations. Degree 1. `d` of these cover [`Pair`].
    ///
    /// [`Pair`]: SeparationChart::Pair
    Star(usize),
    /// The pair chart: every separation, `C(d,2)` points, degree `(d−1)/2` over the orbit chart.
    Pair,
}

/// What a chart costs to materialize, in the material's own terms. Exact, no metric, no number
/// authored anywhere.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ChartDemand {
    pub chart: SeparationChart,
    /// `d` — the orbit count this receiver family produces at this horizon.
    pub classes: BigUint,
    /// Points in this chart.
    pub extent: BigUint,
    /// The transition degree over the orbit chart, as an exact ratio `numerator / denominator`.
    /// `Orbit` and `Star` are `1/1`; `Pair` is `(d−1)/2`.
    pub degree: (BigUint, BigUint),
}

impl ChartDemand {
    /// True when this chart's extent is no larger than the orbit chart's own — the charts of degree
    /// one. Reading through these never materializes a population wider than the reading itself.
    pub fn is_degree_one(&self) -> bool {
        self.degree.0 <= self.degree.1
    }
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
    pub fn read(
        census: &CorpusCensus,
        atlas: &ConductAtlas,
        surface: SurfaceId,
        horizon: usize,
    ) -> Self {
        let mut grouped: BTreeMap<Window, Vec<(u32, u32)>> = BTreeMap::new();
        for (whole, position) in census.sites(surface) {
            grouped
                .entry(window(census, atlas, *whole, *position, horizon))
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

    /// The conduct-block count of this surface's occurrence population under a declared sub-family.
    ///
    /// Exactly the number of distinct windows once each reading is projected onto `family`, which is
    /// the same theorem the full family runs on: two occurrences separate iff their (projected)
    /// windows differ. `family_blocks(ReceiverFamily::FULL)` is [`Self::distinct_windows`], and
    /// [`cross_check_family`] runs `receiver_exact_compression` against this.
    ///
    /// `O(d · horizon)`. No pair is materialized, so the aperture law does not bind here.
    pub fn family_blocks(&self, family: ReceiverFamily) -> usize {
        self.classes
            .iter()
            .map(|class| project(&class.window, family))
            .collect::<BTreeSet<_>>()
            .len()
    }

    /// The other pole, read off the sorted classes in one pass.
    ///
    /// Returns the axes the material holds constant, whether the terminus pattern varies, and the
    /// verdict the two decide. `O(d · horizon · 3)`, and never a pair.
    pub fn conduct_invariance(&self, occurrences: BigUint) -> ConductInvariance {
        let mut terminus_varies = false;
        let mut varying = ReceiverFamily::EMPTY;
        if let Some(reference) = self.classes.first() {
            for class in &self.classes[1..] {
                for (left, right) in reference.window.iter().zip(class.window.iter()) {
                    match (left, right) {
                        (Some(left), Some(right)) => {
                            for axis in ReceiverAxis::DECLARED {
                                if axis.read(*left) != axis.read(*right) {
                                    varying = varying.with(axis);
                                }
                            }
                        }
                        (None, None) => {}
                        // One occurrence ran out of whole and the other did not. No receiver is
                        // involved, so no ablation can merge them.
                        _ => terminus_varies = true,
                    }
                }
            }
        }
        let constant_axes = varying.complement();
        let windows = self.classes.len();
        let verdict = if windows <= 1 {
            ConductVerdict::Iron
        } else if terminus_varies || constant_axes.is_empty() {
            ConductVerdict::Varying {
                windows,
                terminus_varies,
            }
        } else {
            ConductVerdict::ConductInvariant {
                windows,
                collapsing: constant_axes,
            }
        };
        ConductInvariance {
            surface: self.surface,
            horizon: self.horizon,
            occurrences,
            windows,
            terminus_varies,
            constant_axes,
            separations_withstood: self.separated_occurrence_pairs(),
            verdict,
        }
    }

    /// **The shallowest separation a declared sub-family still makes.**
    ///
    /// [`Self::shortest_separation`] answers at the full family, so on a four-axis panel it names
    /// whichever axis comes first in [`ReceiverAxis::DECLARED`] — which is never `Conduct` when an
    /// orthographic axis also differs. That is the wrong artifact for a family that does *not*
    /// collapse a population: the question there is what **that family** still sees.
    ///
    /// Same factorization, same cost. The projected windows are sorted, the shared-prefix array is
    /// taken over them, and its minimum is the round at which the family first separates — so this
    /// is `O(d · horizon · log d)` and materializes no pair. `None` when the family collapses the
    /// population, which is exactly [`ConductInvariance::collapses`] returning true.
    pub fn shallowest_within(&self, family: ReceiverFamily) -> Option<FamilySeparation> {
        let mut projected: Vec<Vec<Option<Vec<u64>>>> = self
            .classes
            .iter()
            .map(|class| project(&class.window, family))
            .collect();
        projected.sort();
        projected.dedup();
        if projected.len() < 2 {
            return None;
        }
        let (index, left, right) = projected
            .windows(2)
            .map(|pair| {
                let shared = pair[0]
                    .iter()
                    .zip(pair[1].iter())
                    .take_while(|(left, right)| left == right)
                    .count();
                (shared, &pair[0], &pair[1])
            })
            .min_by_key(|(shared, ..)| *shared)?;
        let (side, depth) = step_at(index);
        let axes = family.axes();
        let (axis, readings, by_terminus) = match (&left[index], &right[index]) {
            (Some(left), Some(right)) => {
                let place = left
                    .iter()
                    .zip(right.iter())
                    .position(|(left, right)| left != right)?;
                (
                    axes.get(place).copied(),
                    Some((left[place], right[place])),
                    false,
                )
            }
            _ => (None, None, true),
        };
        Some(FamilySeparation {
            family,
            blocks: projected.len(),
            word: vec![side; depth],
            offset: offset_at(index),
            axis,
            readings,
            by_terminus,
        })
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

    /// **The demand of one chart, computed from `d` and the transition degree.**
    ///
    /// Nothing is materialized. A caller asks what a chart costs before it asks for the chart, and
    /// the answer is arithmetic on the orbit count rather than a number anyone chose.
    pub fn demand(&self, chart: SeparationChart) -> ChartDemand {
        let d = BigUint::from(self.classes.len());
        let one = BigUint::from(1u32);
        let two = BigUint::from(2u32);
        let (extent, degree) = match chart {
            SeparationChart::Orbit => (d.clone(), (one.clone(), one.clone())),
            SeparationChart::Star(_) => (
                d.clone() - d.clone().min(one.clone()),
                (one.clone(), one.clone()),
            ),
            // `(d−1)/2` exactly, as a ratio: the pair chart's extent over the orbit chart's.
            SeparationChart::Pair => (
                choose_two(&d),
                (d.clone() - d.clone().min(one.clone()), two),
            ),
        };
        ChartDemand {
            chart,
            classes: d,
            extent,
            degree,
        }
    }

    /// **The star atlas covering the pair chart.** `d` charts, each of transition degree one.
    ///
    /// Every separation lies in exactly two of them, so folding the atlas visits each pair twice and
    /// nothing is lost or invented. This is the point-stabilizer decomposition of the pair space,
    /// and it is what a caller reads when the pair chart is wider than it can hold — a chart change,
    /// not a truncation.
    pub fn pair_atlas(&self) -> Vec<SeparationChart> {
        (0..self.classes.len()).map(SeparationChart::Star).collect()
    }

    /// Read this surface's separations **in a named chart**.
    ///
    /// There is no capacity. `Orbit` returns nothing — the classes are the reading itself and carry
    /// no separations. `Star(i)` returns that class against every other, `d − 1`. `Pair` returns
    /// every separation, and a caller asking for it has declared that it can hold `C(d,2)`; if it
    /// cannot, [`pair_atlas`] covers the same object at degree one.
    ///
    /// [`pair_atlas`]: SeparationComplex::pair_atlas
    pub fn exhibit_in(&self, census: &CorpusCensus, chart: SeparationChart) -> Vec<Separation> {
        match chart {
            SeparationChart::Orbit => Vec::new(),
            SeparationChart::Star(class) => {
                if class >= self.classes.len() {
                    return Vec::new();
                }
                (0..self.classes.len())
                    .filter(|other| *other != class)
                    .filter_map(|other| {
                        self.separation_between(census, class.min(other), class.max(other))
                    })
                    .collect()
            }
            SeparationChart::Pair => {
                let mut separations = Vec::new();
                for left in 0..self.classes.len() {
                    for right in left + 1..self.classes.len() {
                        let index = self
                            .first_difference(left, right)
                            .expect("distinct classes differ");
                        separations.push(self.materialize(census, left, right, index));
                    }
                }
                separations
            }
        }
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
        let landing = |site: (u32, u32), reading: Option<Reading>| -> Option<SurfaceId> {
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

/// A window read by a declared sub-family. A terminus projects to `None` under **every** family,
/// including the empty one — that is the sense in which a terminus is not a receiver's to delete.
fn project(window: &Window, family: ReceiverFamily) -> Vec<Option<Vec<u64>>> {
    window
        .iter()
        .map(|reading| {
            reading.map(|signature| {
                family
                    .axes()
                    .into_iter()
                    .map(|axis| axis.read(signature))
                    .collect()
            })
        })
        .collect()
}

fn choose_two(population: &BigUint) -> BigUint {
    if population < &BigUint::from(2u32) {
        return BigUint::from(0u32);
    }
    population.clone() * (population.clone() - BigUint::from(1u32)) / BigUint::from(2u32)
}

/// The shallowest separation one declared sub-family still makes over a surface's occurrences.
///
/// The artifact for a family that does **not** collapse the population: it names what that family
/// still sees, rather than what the full panel sees, which on a four-axis reading is almost always a
/// different axis.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FamilySeparation {
    pub family: ReceiverFamily,
    /// How many blocks the family leaves. Two or more, or there is no separation to name.
    pub blocks: usize,
    pub word: Vec<Step>,
    pub offset: i64,
    /// The member of `family` that sees it. `None` for a terminus, which is no receiver's.
    pub axis: Option<ReceiverAxis>,
    pub readings: Option<(u64, u64)>,
    pub by_terminus: bool,
}

impl FamilySeparation {
    /// The separation, exhibited as text.
    pub fn exhibit(&self) -> String {
        let word: String = self
            .word
            .iter()
            .map(|step| match step {
                Step::Left => "L",
                Step::Right => "R",
            })
            .collect();
        match (self.axis, self.readings) {
            (Some(axis), Some((left, right))) => format!(
                "{} blocks; word {word} (offset {:+}) -> receiver `{}` returned {} vs {}",
                self.blocks,
                self.offset,
                axis.name(),
                axis.render(left),
                axis.render(right),
            ),
            _ => format!(
                "{} blocks; word {word} (offset {:+}) -> separated by TERMINUS, which no ablation \
                 can merge",
                self.blocks, self.offset,
            ),
        }
    }
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

/// What the **coarser** reading returns for one surface — the verdict that sits beside iron.
///
/// [`Verdict`] is the reading at the full declared family, and it stays exactly what it was:
/// `Iron` or `Separated`. Conduct-invariance is *not* a third case of it, because it is not a
/// finding at that family — at the full family it is unsatisfiable, by the theorem in this module's
/// header. It is a reading at a **coarser declared family**, so it is a separate verdict, computed
/// from the same [`SeparationComplex`] in the same sweep and directly comparable on the same
/// material.
///
/// `Iron` appears in both, and it is the same surfaces both times: [`ConductVerdict::Iron`] and
/// [`Verdict::Iron`] are both `distinct_windows == 1`. That is asserted, not assumed.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ConductVerdict {
    /// One window under the full family. The same population [`Verdict::Iron`] returns.
    Iron,
    /// Many windows under the full family, and **one conduct block** under `collapsing` — the
    /// maximal declared family this surface's own material holds constant.
    ///
    /// `collapsing` is always a **nonempty proper** subset of [`ReceiverFamily::FULL`]: nonempty
    /// because the verdict requires it, proper because a surface constant on all three axes with a
    /// constant terminus pattern has one window and is iron.
    ConductInvariant {
        windows: usize,
        collapsing: ReceiverFamily,
    },
    /// Many windows, and no nonempty declared family holds them in one block. `terminus_varies`
    /// names the stronger case: the occurrences disagree about whether an offset exists at all, so
    /// even the empty family separates them and no ablation could ever merge them.
    Varying {
        windows: usize,
        terminus_varies: bool,
    },
}

impl ConductVerdict {
    pub fn is_iron(self) -> bool {
        matches!(self, ConductVerdict::Iron)
    }

    pub fn is_conduct_invariant(self) -> bool {
        matches!(self, ConductVerdict::ConductInvariant { .. })
    }

    /// The maximal family that holds this surface's occurrences in one block, when one exists.
    pub fn collapsing(self) -> Option<ReceiverFamily> {
        match self {
            ConductVerdict::Iron => Some(ReceiverFamily::FULL),
            ConductVerdict::ConductInvariant { collapsing, .. } => Some(collapsing),
            ConductVerdict::Varying { .. } => None,
        }
    }
}

/// One surface's conduct-invariance reading at one declared horizon.
///
/// Read off the sorted window classes in one pass. No pair is materialized, so a surface whose
/// [`SeparationComplex::exhibit`] is obstructed still receives this verdict whole.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ConductInvariance {
    pub surface: SurfaceId,
    pub horizon: usize,
    pub occurrences: BigUint,
    /// Distinct windows under the **full** family. Also its conduct-block count there.
    pub windows: usize,
    /// Two occurrences disagree about whether some offset exists at all. Family-invariant: no
    /// ablation merges a terminus with a reading, so this alone refuses every collapsing family.
    pub terminus_varies: bool,
    /// The axes whose reading agrees across every occurrence at every offset. The collapsing
    /// families are exactly this family's subsets — provided the terminus pattern does not vary —
    /// so this is the unique **maximal** one.
    pub constant_axes: ReceiverFamily,
    /// The exact number of occurrence pairs the **full** family separates and the collapsing family
    /// holds together. This is what a conduct-invariant verdict withstood, and it is the same
    /// instrument [`SeparationReading::survived_pairs`] is for iron: `CLAUDE.md` §8's tautology
    /// rule, made a number the reading carries.
    ///
    /// It is nonzero on every surface [`ConductVerdict::ConductInvariant`] admits, because
    /// `windows > 1` forces at least one separated pair. **The verdict cannot be vacuous.**
    pub separations_withstood: BigUint,
    pub verdict: ConductVerdict,
}

impl ConductInvariance {
    /// Does this declared family hold the surface's whole occurrence population in one block?
    ///
    /// `F` collapses iff `F ⊆ constant_axes` **and** the terminus pattern does not vary. The two
    /// clauses are separate because a terminus is not a receiver's to delete.
    pub fn collapses(&self, family: ReceiverFamily) -> bool {
        !self.terminus_varies && family.is_subset_of(self.constant_axes)
    }

    /// Every declared family that holds this surface in one block, coarsest first. Empty when the
    /// terminus pattern varies — not even the empty family collapses it then.
    pub fn collapsing_families(&self) -> Vec<ReceiverFamily> {
        if self.terminus_varies {
            Vec::new()
        } else {
            self.constant_axes.subsets()
        }
    }

    /// The axes this surface's material varies. For a conduct-invariant surface this is nonempty,
    /// and together with `constant_axes` it is the whole declared family.
    pub fn varying_axes(&self) -> ReceiverFamily {
        self.constant_axes.complement()
    }

    /// An iron verdict on fewer than two occurrences: true by arithmetic rather than by usage.
    /// Conduct-invariance has no such case, which is the point of stating it this way.
    pub fn vacuous(&self) -> bool {
        self.verdict.is_iron() && self.occurrences < BigUint::from(2u32)
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

    /// Read this surface's separations in a named chart. No capacity participates.
    pub fn exhibit_in(&self, census: &CorpusCensus, chart: SeparationChart) -> Vec<Separation> {
        self.complex.exhibit_in(census, chart)
    }

    /// What a chart costs here, computed from this surface's own orbit count.
    pub fn demand(&self, chart: SeparationChart) -> ChartDemand {
        self.complex.demand(chart)
    }

    /// The star atlas covering this surface's pair chart.
    pub fn pair_atlas(&self) -> Vec<SeparationChart> {
        self.complex.pair_atlas()
    }

    /// The **second** verdict, from the **same** reading: conduct-invariance at the coarser declared
    /// families. `O(d · horizon)` off the classes already built, so one [`sweep`] returns both and
    /// they are comparable on the same material by construction.
    pub fn conduct_invariance(&self) -> ConductInvariance {
        self.complex.conduct_invariance(self.occurrences.clone())
    }

    /// The conduct-block count under a declared sub-family. `family_blocks(FULL)` is
    /// `distinct_windows`.
    pub fn family_blocks(&self, family: ReceiverFamily) -> usize {
        self.complex.family_blocks(family)
    }

    /// The shallowest separation a declared sub-family still makes — what **that** family sees,
    /// rather than what the full panel sees. `None` exactly when the family collapses.
    pub fn shallowest_within(&self, family: ReceiverFamily) -> Option<FamilySeparation> {
        self.complex.shallowest_within(family)
    }
}

/// Read one surface's occurrence population at one declared horizon.
pub fn separation_reading(
    census: &CorpusCensus,
    atlas: &ConductAtlas,
    surface: SurfaceId,
    horizon: usize,
) -> SeparationReading {
    let complex = SeparationComplex::read(census, atlas, surface, horizon);
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
pub fn sweep(
    census: &CorpusCensus,
    atlas: &ConductAtlas,
    horizon: usize,
) -> BTreeMap<SurfaceId, SeparationReading> {
    sweep_over(census, atlas, horizon, &HardwareCover::host_only())
}

/// **The sweep, covered across the charts a caller declares.**
///
/// Every surface's reading is independent of every other — they share the census and the atlas
/// immutably and touch disjoint occurrence sets — so the population of surfaces IS a front, and
/// `hardware_cover` decomposes it. Until 2026-08-10 this was a serial `map`, which is why driving
/// it pinned one host core while every other lane and the card stood idle: `CLAUDE.md` §9 names
/// that state a defect to diagnose, not a mystery to narrate.
///
/// **The cover places, and the placement is proved.** Each surface is a cell of the front whose
/// extent is its own occurrence count; the cover sends it to the coarsest chart whose grain that
/// extent fills, and `independence` checks that every cell reaches exactly one chart before any
/// work is issued. A barrier is returned as a serial sweep rather than worked around.
///
/// **The device chart is placed and not yet enacted, and that is stated rather than hidden.**
/// `token_invariance` reaches no executor and no kernel — a window partition is a sort plus a
/// longest-common-prefix scan, which is GPU-shaped, and building that kernel is its own
/// construction. Cells placed on a device chart are read on the host today, and
/// [`SweepCover::device_cells`] reports how many, so the gap is a number rather than an impression.
pub fn sweep_over(
    census: &CorpusCensus,
    atlas: &ConductAtlas,
    horizon: usize,
    cover: &HardwareCover,
) -> BTreeMap<SurfaceId, SeparationReading> {
    sweep_covered(census, atlas, horizon, cover).readings
}

/// A covered sweep, with what the cover did to it.
pub struct SweepCover {
    pub readings: BTreeMap<SurfaceId, SeparationReading>,
    /// Cells the cover placed on a device chart. Read on the host today; the count is the debt.
    pub device_cells: usize,
    /// Lanes the host section was spread over.
    pub host_lanes: usize,
}

/// The covered sweep, returning the placement beside the readings.
pub fn sweep_covered(
    census: &CorpusCensus,
    atlas: &ConductAtlas,
    horizon: usize,
    cover: &HardwareCover,
) -> SweepCover {
    let surfaces = census.word_surfaces();
    let front: Vec<FrontCell> = surfaces
        .iter()
        .enumerate()
        .map(|(index, surface)| FrontCell {
            index,
            extent: census.sites(*surface).len() as u64,
        })
        .collect();
    let decomposition = CoverDecomposition::of(cover, &front, "separation_reading");
    let device_cells = decomposition
        .sections
        .iter()
        .filter(|section| matches!(section.chart, ChartId::Device(_)))
        .map(|section| section.cells.len())
        .sum();
    // **The caller's declared width, unclamped.** This read `.max(1)`, which silently rewrote a
    // declaration of zero host lanes into one. The only value it changed was `0`, and `0` and `1`
    // take the same branch below, so it was an authored floor with no orbit sitting on top of a
    // caller-declared level — the worse of the two, because it overrode a declaration.
    let lanes = cover.host().lanes as usize;

    // Independence is checked before any work is issued. A barrier is not worked around: the sweep
    // falls back to one lane, which is always licensed. A width of zero -- no declared lanes, or no
    // surfaces to spread over -- lands on the same single section, because there is nothing to
    // spread.
    let licensed = decomposition.independence(&front).is_ok();
    let effective_lanes = if licensed { lanes.min(surfaces.len()) } else { 1 };

    let readings = if effective_lanes <= 1 {
        surfaces
            .iter()
            .map(|surface| (*surface, separation_reading(census, atlas, *surface, horizon)))
            .collect()
    } else {
        // Cover the surfaces by EXTENT, not by count: a surface with a million occurrences and one
        // with two are not one unit each.
        let mut by_extent: Vec<&FrontCell> = front.iter().collect();
        by_extent.sort_by_key(|cell| (std::cmp::Reverse(cell.extent), cell.index));
        let mut sections: Vec<Vec<usize>> = vec![Vec::new(); effective_lanes];
        let mut carried = vec![0u128; effective_lanes];
        for cell in by_extent {
            let lane = carried
                .iter()
                .enumerate()
                .min_by_key(|(lane, load)| (**load, *lane))
                .map(|(lane, _)| lane)
                .unwrap_or(0);
            sections[lane].push(cell.index);
            carried[lane] += u128::from(cell.extent);
        }
        std::thread::scope(|scope| {
            let handles: Vec<_> = sections
                .into_iter()
                .map(|section| {
                    let surfaces = &surfaces;
                    scope.spawn(move || {
                        section
                            .into_iter()
                            .map(|at| {
                                let surface = surfaces[at];
                                (
                                    surface,
                                    separation_reading(census, atlas, surface, horizon),
                                )
                            })
                            .collect::<Vec<_>>()
                    })
                })
                .collect();
            handles
                .into_iter()
                .flat_map(|handle| match handle.join() {
                    Ok(section) => section,
                    Err(payload) => std::panic::resume_unwind(payload),
                })
                .collect()
        })
    };

    SweepCover {
        readings,
        device_cells,
        host_lanes: effective_lanes,
    }
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

/// The conduct-invariance reading of every surface in a sweep. The **same** sweep the iron reading
/// runs on, so the two verdicts are never taken over different material.
pub fn conduct_invariance_at(
    sweep: &BTreeMap<SurfaceId, SeparationReading>,
) -> BTreeMap<SurfaceId, ConductInvariance> {
    sweep
        .iter()
        .map(|(surface, reading)| (*surface, reading.conduct_invariance()))
        .collect()
}

/// The measured population, split by verdict. Three blocks, disjoint by construction, and iron is
/// split again into the part a pair could have refuted and the part arithmetic decided.
///
/// A verdict that does not partition its population is a taxonomy, not a reading:
/// [`InvariancePartition::is_a_partition`] is checked on real material by every driver.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct InvariancePartition {
    /// `windows == 1` on fewer than two occurrences. Iron by arithmetic.
    pub vacuously_iron: BTreeSet<SurfaceId>,
    /// `windows == 1` with at least one occurrence pair that could have refuted it.
    pub witnessed_iron: BTreeSet<SurfaceId>,
    /// `windows > 1` and some nonempty declared family holds the occurrences in one block.
    pub conduct_invariant: BTreeSet<SurfaceId>,
    /// `windows > 1` and no nonempty declared family holds them.
    pub varying: BTreeSet<SurfaceId>,
}

impl InvariancePartition {
    pub fn iron(&self) -> usize {
        self.vacuously_iron.len() + self.witnessed_iron.len()
    }

    pub fn total(&self) -> usize {
        self.iron() + self.conduct_invariant.len() + self.varying.len()
    }

    /// The blocks are pairwise disjoint and cover the measured population.
    pub fn is_a_partition(&self, measured: usize) -> bool {
        let union: BTreeSet<SurfaceId> = self
            .vacuously_iron
            .iter()
            .chain(self.witnessed_iron.iter())
            .chain(self.conduct_invariant.iter())
            .chain(self.varying.iter())
            .copied()
            .collect();
        union.len() == self.total() && self.total() == measured
    }
}

/// Split a sweep by verdict.
pub fn invariance_partition(
    sweep: &BTreeMap<SurfaceId, SeparationReading>,
) -> InvariancePartition {
    let mut partition = InvariancePartition::default();
    for (surface, reading) in sweep {
        match reading.conduct_invariance().verdict {
            ConductVerdict::Iron => {
                if reading.vacuously_iron() {
                    partition.vacuously_iron.insert(*surface);
                } else {
                    partition.witnessed_iron.insert(*surface);
                }
            }
            ConductVerdict::ConductInvariant { .. } => {
                partition.conduct_invariant.insert(*surface);
            }
            ConductVerdict::Varying { .. } => {
                partition.varying.insert(*surface);
            }
        }
    }
    partition
}

/// The conduct-invariant population indexed by the family that collapses it. The **orbit** of the
/// verdict: a family that never appears has not been shown to do anything on this material.
pub fn collapsing_family_population(
    sweep: &BTreeMap<SurfaceId, SeparationReading>,
) -> BTreeMap<ReceiverFamily, BTreeSet<SurfaceId>> {
    let mut population: BTreeMap<ReceiverFamily, BTreeSet<SurfaceId>> = BTreeMap::new();
    for (surface, reading) in sweep {
        if let ConductVerdict::ConductInvariant { collapsing, .. } =
            reading.conduct_invariance().verdict
        {
            population.entry(collapsing).or_default().insert(*surface);
        }
    }
    population
}

// -------------------------------------------------------------------------------------------------
// The horizon, read off the material
// -------------------------------------------------------------------------------------------------
//
// **A horizon is not a level and must never be authored.** Brandon, 2026-08-10, on the constant this
// section removes: *"'horizon' shouldn't be a constant either if it is."* Everything below derives
// it, and the derivation is exact.
//
// # The window is a causal diamond, and the horizon is its radius
//
// [`step_at`] writes index `2(k−1)` as `L^k` and `2(k−1)+1` as `R^k`, so a window enumerates the
// occurrence's neighbourhood **shell by shell** — `−1, +1, −2, +2, …` — in order of `|offset|`.
// That is a discrete causal diamond around the occurrence: the two sides are the two sheets, the
// shell index is proper distance along the stream, and `None` is where the whole ends, which is the
// material's own boundary rather than padding.
//
// Two consequences, both used below:
//
// - the window at horizon `h` is a **prefix** of the window at `h+1`, so the partition at `h+1`
//   refines the partition at `h` — *"a deeper horizon only separates more"*, this module's own
//   statement, now load-bearing rather than decorative;
// - the first index at which two windows differ is the **shell at which the two occurrences
//   separate**, which is what the shared-prefix array already reports.
//
// # Why the derivation terminates, and it is a theorem about the material
//
// An occurrence at position `p` of a whole of length `L` reads shells while `k ≤ max(p, L−1−p)` and
// `(None, None)` forever after, so a surface's own occurrences fix its ceiling exactly and no deeper
// horizon can refine anything. That bound is **read off the material this surface occupies**; nobody
// declares it. The corpus-wide `max stream length` is the ceiling of those ceilings and remains a
// real reading about the corpus — it is simply not any one surface's cost.
//
// Within `[0, bound]` the class count is monotone non-decreasing, because refinement can only
// split. And a refinement with the same number of blocks **is** the same partition. So
//
// ```text
//   saturation horizon  =  the least h with  classes(h) == classes(bound)
// ```
//
// is exactly the least horizon whose partition is already final, and monotonicity makes it binary
// searchable in `O(log bound)` partition builds instead of `bound` of them.
//
// # What this is in the ontology
//
// The saturation horizon is where the receiver's causal past stops carrying difference: extending
// the cone past it changes nothing this receiver can distinguish. It is the material's own null
// boundary for that receiver — `Q(v) = 0`, the vacuous difference — and it is a **relation between
// a receiver and its material**, never a property either one has alone.

/// The material's own ceiling on any horizon: no window reaches past the longest whole.
///
/// Read off the census. A horizon above this refines nothing, because every window already carries
/// its occurrence's whole entire and every further shell is `None` on both sides.
pub fn material_horizon_bound(census: &CorpusCensus) -> usize {
    census
        .wholes()
        .iter()
        .map(|whole| whole.stream.len())
        .max()
        .unwrap_or(0)
}

/// **One surface's own ceiling, exactly**, from its own occurrences and nothing else.
///
/// An occurrence at position `p` of a whole of length `L` reads `at(−k)` while `k ≤ p` and `at(+k)`
/// while `k ≤ L−1−p`, so past `max(p, L−1−p)` its shell is `(None, None)` forever. A surface can
/// therefore separate nothing past the maximum of that over its **own** sites, and that maximum is
/// read off the material the same way [`material_horizon_bound`] is — only from the part of the
/// material this surface actually occupies.
///
/// **This replaced [`material_horizon_bound`] as the propagation's ceiling.** Using the longest
/// whole in the *whole census* as every surface's ceiling makes one unrelated long document lengthen
/// the loop of every surface that never saturates, for identical material: a corpus-global
/// coordinate deciding a surface-local cost, which is the absolute-frame defect at the level of a
/// cost law. The corpus-wide figure remains a real reading — it is the ceiling of the ceilings — and
/// is still what a caller reports about the corpus.
pub fn surface_horizon_bound(census: &CorpusCensus, surface: SurfaceId) -> usize {
    let wholes = census.wholes();
    census
        .sites(surface)
        .iter()
        .map(|(whole, position)| {
            let length = wholes[*whole as usize].stream.len();
            let left = *position as usize;
            let right = length.saturating_sub(1).saturating_sub(left);
            left.max(right)
        })
        .max()
        .unwrap_or(0)
}

/// **A refinement that stalled and then resumed, with the witness that proves it.**
///
/// This is the object that makes "a quiet shell is not saturation" checkable rather than asserted.
/// It names three things an early-halting loop gets wrong, and every one of them is read off the
/// propagation rather than declared:
///
/// - `quiet_shell` — the depth at which the unsound loop stops;
/// - `resumed_at` — a **strictly later** depth that did split, so the stop was premature;
/// - `separated` — two occurrences that `resumed_at` pulled apart and `quiet_shell` left merged.
///
/// The last is the distinguishing word. A count of quiet shells says a stall happened; this says
/// *which two occurrences an early halt would have failed to tell apart*, which is the same shape
/// `receiver_exact_compression` returns for a collapsed pair.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Resumption {
    /// The quiet shell — it split nothing, and an early-halting loop returns it as the horizon.
    pub quiet_shell: usize,
    /// The later shell that split. Strictly greater than `quiet_shell`.
    pub resumed_at: usize,
    /// Classes entering `resumed_at`, which is what the quiet shell left standing.
    pub classes_before: usize,
    /// Classes leaving `resumed_at`. Strictly greater than `classes_before`; the difference is what
    /// halting at `quiet_shell` would have lost.
    pub classes_after: usize,
    /// The two occurrences — `(whole, position)` each — that `resumed_at` first separated. Neither
    /// is distinguishable from the other at `quiet_shell`.
    pub separated: ((u32, u32), (u32, u32)),
}

/// One surface's horizon, derived rather than declared.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SaturationHorizon {
    pub surface: SurfaceId,
    /// The least horizon whose partition is already final.
    ///
    /// **`0` is a reading, not a floor.** It says *no shell ever split*: this surface's occurrences
    /// were never separated by the cone at any radius the material admits, either because there is
    /// at most one of them or because they are indistinguishable to this receiver at every depth.
    /// The field carried `last_split.max(1)` until 2026-08-11, which reported a radius of one for a
    /// surface whose least final radius is zero — an authored floor, invisible to
    /// `tools/authored_levels.py` because it is not a `const`, and shielded from its own unit test
    /// by an `if horizon > 1` guard that excluded exactly the case the floor decided.
    pub horizon: usize,
    /// **This surface's own ceiling**, from [`surface_horizon_bound`] — the furthest shell any of
    /// its own occurrences can still read before both sides are off the end of their whole.
    ///
    /// Not [`material_horizon_bound`], which is the corpus's ceiling and was used here until
    /// 2026-08-11. That made one unrelated long document lengthen every non-saturating surface's
    /// propagation for material that had not changed.
    pub bound: usize,
    /// The final class count — what the receiver can distinguish at all, at any depth.
    pub classes: usize,
    /// The class count at horizon 1, so the orbit of the level this replaces is visible.
    pub classes_at_one: usize,
    /// The class count immediately **before** the last split — the partition at `horizon − 1`,
    /// carried out of the propagation, which passes through that state anyway.
    ///
    /// It is **not** evidence that the horizon is least, and was described as that proof until
    /// 2026-08-11. It is written only on a shell that split, and a shell that split leaves strictly
    /// more classes than it found, so `classes_before < classes` cannot come out false. What it
    /// carries is the *amount* the last shell separated, which does vary with the material. See
    /// [`is_least`].
    ///
    /// [`is_least`]: SaturationHorizon::is_least
    pub classes_before: usize,
    /// Shells actually propagated. Stops at this surface's own ceiling or when every class is a
    /// singleton.
    pub shells: usize,
    /// **Interior quiet shells: the evidence that stopping at the first quiet shell is unsound.**
    ///
    /// A shell is *interior quiet* when it split nothing **and** a later shell did split. That is
    /// the exact population an early-halting loop would have mistaken for saturation, and it is
    /// non-zero precisely on material where the sound loop and the unsound one disagree. Trailing
    /// quiet shells — the ones after the last split, which every propagation that reaches the
    /// ceiling walks — are deliberately **not** counted: they are not evidence of anything, because
    /// halting on them returns the right answer.
    pub interior_quiet_shells: usize,
    /// The **first resumption, with its witness**: the quiet shell, the later shell that split, and
    /// the two occurrences that shell pulled apart.
    ///
    /// `CLAUDE.md` §8: *a gauge should be required to exhibit its distinguishing word.* This is it —
    /// the point at which the sound and the unsound derivation part company on this surface, named
    /// rather than counted. `None` exactly when [`interior_quiet_shells`] is zero.
    ///
    /// [`interior_quiet_shells`]: SaturationHorizon::interior_quiet_shells
    pub first_resumption: Option<Resumption>,
    /// **How the propagation terminated, and only one of the two is a proof.**
    ///
    /// `true` — every class became a singleton, so no deeper shell can split anything and the
    /// horizon is final as a theorem. `false` — this surface's own ceiling was reached with classes
    /// still plural, so those occurrences are indistinguishable to this receiver at any depth.
    /// Reporting which is the difference between a checked claim and an assumed one.
    ///
    /// It is read off the returned partition. It was a flag set on one of the loop's two exits until
    /// 2026-08-11, which reported `false` for a surface whose last pair separated exactly at its
    /// ceiling — the theorem, filed as the assumption.
    pub exhausted: bool,
    /// **The cost, exactly**: occurrences still carrying difference, summed over the shells that
    /// were propagated. This is the volume of the cone that was still live — not the cone's volume,
    /// and not a wall-clock reading. `CLAUDE.md` §8: a cost is measured in work, never in elapsed
    /// time.
    ///
    /// It is the propagation's *whole* cost as of 2026-08-11 and was not before: singletons used to
    /// be drained and re-pushed every shell, so the real per-shell work was `Θ(classes)` while this
    /// field reported `Θ(active)`. Retiring a singleton into a count the moment it appears made the
    /// two the same quantity. The number is exact and machine-independent; it reproduces bit for bit
    /// on any host.
    pub active_total: usize,
}

impl SaturationHorizon {
    /// True when horizon 1 — the level this derivation replaces — already saw everything.
    pub fn one_was_enough(&self) -> bool {
        self.classes_at_one == self.classes
    }

    /// The distinctions a horizon of 1 could not reach.
    pub fn unreached_at_one(&self) -> usize {
        self.classes - self.classes_at_one
    }

    /// True when one shell shallower was still refining — the returned horizon is **least**.
    ///
    /// **This cannot return `false`, and that is a `definition`-grade receipt rather than a
    /// control.** `classes_before` is written only on a shell that split, and a shell that split
    /// leaves strictly more classes than it found; no later shell splits, so the final count is that
    /// one. `classes_before < classes` is therefore a theorem about the loop, not a measurement of
    /// the material, and `CLAUDE.md` §8 says a receipt that could not have come out otherwise
    /// carries no evidence. Leastness **is** graded, independently, by
    /// `the_horizon_is_read_off_the_material_not_declared`, which rebuilds the partition one shell
    /// shallower through [`SeparationComplex::read`] and compares — a route that can fail.
    pub fn is_least(&self) -> bool {
        self.horizon == 0 || self.classes_before < self.classes
    }

    /// True when the propagation crossed a shell that split nothing and then split again later.
    ///
    /// **This replaced `walked_past`, which could not fail.** That method returned
    /// `shells > horizon`, which is false on every propagation that exhausts to singletons — the
    /// last shell walked *is* the last shell that split — so it read `false` on the very fixture
    /// built to exhibit a stall. It measured no interior quiet shell at all; it measured whether the
    /// loop reached the ceiling with the horizon strictly inside it, which is a restatement of
    /// `!exhausted` on all but the boundary case `horizon == bound`.
    pub fn stalled(&self) -> bool {
        self.interior_quiet_shells > 0
    }
}

/// What one shell contributes: the two readings at `±k` from a site, or `None` past the whole.
fn shell(
    census: &CorpusCensus,
    atlas: &ConductAtlas,
    whole: u32,
    position: u32,
    depth: usize,
) -> (Option<Reading>, Option<Reading>) {
    let stream = &census.wholes()[whole as usize].stream;
    let at = |offset: i64| {
        let site = position as i64 + offset;
        if site < 0 || site >= stream.len() as i64 {
            None
        } else {
            Some(reading(census, atlas, stream[site as usize]))
        }
    };
    (at(-(depth as i64)), at(depth as i64))
}

/// Derive one surface's horizon by **propagating** the cone one shell at a time.
///
/// # This replaced a binary search, and the reason is the whole point
///
/// The first implementation binary-searched `[1, bound]` for the least horizon whose class count
/// matched the count at `bound`. It was correct and it was catastrophic: probing at the ceiling
/// materializes a window of `2 · bound` readings **per occurrence**, so one probe costs
/// `occurrences · 2 · bound · 32` octets. Run against this repository's own corpus it reached
/// **19.6 GB resident on one core in 6m39s with no output** and was halted — the unbounded causal
/// past, produced by the driver written to explain it.
///
/// **A cone is not binary-searched. It propagates.** Light does not sample its way to a horizon; it
/// advances one shell at a time and stops where the difference dies. So the partition is held and
/// refined shell by shell, and only classes that are **still non-singleton** are ever carried — a
/// singleton can never split again, so it is retired into a count the moment it appears and is never
/// looked at again. The work is therefore
///
/// ```text
///   Σ_k  (occurrences still carrying difference at shell k)
/// ```
///
/// which is the volume of the cone *that is still carrying difference*, not the volume of the cone.
/// Memory is `O(occurrences)`; no window is ever materialized.
///
/// **That statement was false until 2026-08-11 and the repair is the retirement.** The loop used to
/// `drain` the whole class vector every shell and push each singleton straight back, so per-shell
/// work was `Θ(classes)` — and `classes` grows toward `occurrences` as the partition sharpens, which
/// is the opposite of the shrinking front the doc claimed. Singletons are now retired into
/// `settled`, and the only vector walked is the still-plural one.
///
/// # The ceiling is this surface's own, not the corpus's
///
/// An occurrence at position `p` of a whole of length `L` can reach `p` shells to the left and
/// `L−1−p` to the right before both sides are off the end, so it contributes exactly
/// `max(p, L−1−p)` reachable shells and nothing past that shell can ever separate anything. The
/// surface's ceiling is the maximum of that over its **own** sites — [`surface_horizon_bound`] —
/// and it is read off the material the same way the corpus-wide ceiling is, only from the part of
/// the material this surface actually occupies.
///
/// # Why stopping is a theorem and not a heuristic
///
/// A shell that splits nothing does **not** prove saturation: refinement can stall for one shell
/// and resume — `Z A B C D E` against `W A B C D E`, read at `C`, agree at shells 1 and 2 and
/// differ at 3. So the loop does not stop on a quiet shell. It stops when **every class is a
/// singleton**, which is sound because a singleton cannot split at any depth, or at this surface's
/// own ceiling, past which every shell is `None` on both sides. The returned horizon is the **last
/// shell that actually split a class** — the least radius whose partition is already final — and it
/// is `0` when no shell ever split.
pub fn saturation_horizon(
    census: &CorpusCensus,
    atlas: &ConductAtlas,
    surface: SurfaceId,
) -> SaturationHorizon {
    let sites = census.sites(surface);
    let bound = surface_horizon_bound(census, surface);

    // The partition at shell 0: one class holding every occurrence. A class of one is already
    // settled -- it can never split again -- so it is retired to a count rather than carried.
    let mut plural = vec![sites.to_vec()];
    let mut settled = 0usize;
    if sites.len() <= 1 {
        plural.clear();
        settled = 1;
    }
    let mut last_split = 0usize;
    let mut classes_at_one = 1usize;
    let mut classes_before = 1usize;
    let mut shells = 0usize;
    let mut active_total = 0usize;
    let mut interior_quiet_shells = 0usize;
    let mut first_resumption: Option<Resumption> = None;
    // Quiet shells since the last split. They become INTERIOR the moment a later shell splits, and
    // stay uncounted otherwise, because a trailing quiet shell is not evidence of anything.
    let mut quiet_run = 0usize;
    let mut first_quiet_in_run: Option<usize> = None;

    for depth in 1..=bound {
        // Only a non-singleton class can split, and only those are carried. This is what keeps the
        // work on the front rather than on the whole partition.
        let active: usize = plural.iter().map(Vec::len).sum();
        if active == 0 {
            break;
        }
        let before = settled + plural.len();
        shells += 1;
        active_total += active;

        let mut refined: Vec<Vec<(u32, u32)>> = Vec::with_capacity(plural.len());
        let mut split = false;
        // The first pair this shell actually pulls apart. Retained, not counted: a resumption's
        // witness is two occurrences that an early halt would have left merged, and naming them
        // costs one comparison per splitting class.
        let mut separated: Option<((u32, u32), (u32, u32))> = None;
        for class in plural.drain(..) {
            let mut grouped: BTreeMap<(Option<Reading>, Option<Reading>), Vec<(u32, u32)>> =
                BTreeMap::new();
            for (whole, position) in class {
                grouped
                    .entry(shell(census, atlas, whole, position, depth))
                    .or_default()
                    .push((whole, position));
            }
            if grouped.len() > 1 {
                split = true;
                if separated.is_none() {
                    let mut groups = grouped.values();
                    if let (Some(left), Some(right)) = (groups.next(), groups.next()) {
                        if let (Some(one), Some(other)) = (left.first(), right.first()) {
                            separated = Some((*one, *other));
                        }
                    }
                }
            }
            for group in grouped.into_values() {
                if group.len() == 1 {
                    settled += 1;
                } else {
                    refined.push(group);
                }
            }
        }
        plural = refined;
        if split {
            last_split = depth;
            classes_before = before;
            interior_quiet_shells += quiet_run;
            if first_resumption.is_none() {
                if let (Some(quiet_shell), Some(separated)) = (first_quiet_in_run, separated) {
                    first_resumption = Some(Resumption {
                        quiet_shell,
                        resumed_at: depth,
                        classes_before: before,
                        classes_after: settled + plural.len(),
                        separated,
                    });
                }
            }
            quiet_run = 0;
            first_quiet_in_run = None;
        } else {
            quiet_run += 1;
            if first_quiet_in_run.is_none() {
                first_quiet_in_run = Some(depth);
            }
        }
        if depth == 1 {
            classes_at_one = settled + plural.len();
        }
    }

    SaturationHorizon {
        surface,
        horizon: last_split,
        bound,
        classes: settled + plural.len(),
        classes_at_one,
        classes_before,
        shells,
        // **Read off the partition, not off which exit the loop took.** This was a flag set only on
        // the `active == 0` branch, so a surface that separated its last pair exactly AT its ceiling
        // fell out of the loop with every class a singleton and reported `exhausted == false` — a
        // proof reported as an assumption. It never fired while the ceiling was the corpus's,
        // because there was always another shell to observe the empty front in; tightening the
        // ceiling to the surface's own made it reachable, and the stall fixture hit it immediately.
        exhausted: plural.is_empty(),
        active_total,
        interior_quiet_shells,
        first_resumption,
    }
}

/// Every word surface's derived horizon. No level participates anywhere in this call.
pub fn saturation_horizons(
    census: &CorpusCensus,
    atlas: &ConductAtlas,
) -> BTreeMap<SurfaceId, SaturationHorizon> {
    census
        .word_surfaces()
        .into_iter()
        .map(|surface| (surface, saturation_horizon(census, atlas, surface)))
        .collect()
}

/// The horizon at which **every** surface in the corpus has saturated: the corpus's own reading
/// horizon, and the honest replacement for a declared one.
///
/// Returned with the population that forced it, because a single number over a corpus is a summary
/// and this organ does not deal in summaries: the forcing surfaces are what a caller should look at
/// before deciding that one horizon serves the whole material.
pub fn corpus_horizon(
    horizons: &BTreeMap<SurfaceId, SaturationHorizon>,
) -> (usize, BTreeSet<SurfaceId>) {
    // `0` on an empty population, because no surface forced anything. A `1` here would be the same
    // authored floor the per-surface horizon carried until 2026-08-11.
    let deepest = horizons
        .values()
        .map(|reading| reading.horizon)
        .max()
        .unwrap_or(0);
    let forcing = horizons
        .iter()
        .filter(|(_, reading)| reading.horizon == deepest)
        .map(|(surface, _)| *surface)
        .collect();
    (deepest, forcing)
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
    atlas: &'a ConductAtlas,
    roots: Vec<(u32, u32)>,
    horizon: usize,
    axes: Vec<ReceiverAxis>,
}

impl<'a> OccurrenceSystem<'a> {
    pub fn new(
        census: &'a CorpusCensus,
        atlas: &'a ConductAtlas,
        roots: Vec<(u32, u32)>,
        horizon: usize,
    ) -> Self {
        Self::restricted(census, atlas, roots, horizon, ReceiverFamily::FULL)
    }

    /// The same population presented to a **declared sub-family** of receivers. Everything else —
    /// items, inputs, successors, termini — is untouched, so the only thing that moved is the
    /// family, which is what makes the block count attributable to it.
    ///
    /// `receivers()` returns nothing at [`ReceiverFamily::EMPTY`], and the organ still separates by
    /// terminus there. That is not a degenerate case; it is the terminus clause, driven.
    pub fn restricted(
        census: &'a CorpusCensus,
        atlas: &'a ConductAtlas,
        roots: Vec<(u32, u32)>,
        horizon: usize,
        family: ReceiverFamily,
    ) -> Self {
        Self {
            census,
            atlas,
            roots,
            horizon,
            axes: family.axes(),
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
        let reading = reading(self.census, self.atlas, surface);
        Observation(match ReceiverAxis::from_id(receiver) {
            Some(axis) => axis.read(reading),
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
    atlas: &ConductAtlas,
    surface: SurfaceId,
    horizon: usize,
    declared_capacity: u64,
) -> Result<CrossCheck, ExhibitionObstructed> {
    let complex = SeparationComplex::read(census, atlas, surface, horizon);
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
    let system = OccurrenceSystem::new(census, atlas, roots, horizon);
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

/// What running both implementations of a **sub-family's** block count returned.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FamilyCrossCheck {
    pub surface: SurfaceId,
    pub horizon: usize,
    pub family: ReceiverFamily,
    /// From the projection of the factorized window classes.
    pub projected_blocks: usize,
    /// From `receiver_exact_compression::compress` on the same population with only `family`
    /// declared as receivers.
    pub organ_blocks: usize,
    /// What the reading claimed: that `family` holds the whole population in one block.
    pub collapses_claimed: bool,
}

impl FamilyCrossCheck {
    pub fn agrees(&self) -> bool {
        self.projected_blocks == self.organ_blocks
            && self.collapses_claimed == (self.organ_blocks <= 1)
    }
}

/// Run `receiver_exact_compression` at a declared sub-family and compare its conduct-block count
/// against the projection of the factorization, and against what [`ConductInvariance`] claimed.
///
/// The organ is quadratic in the presented population, so the caller declares its capacity and this
/// refuses past it with the width the material required — the same law [`cross_check`] follows. The
/// verdict itself never needs this route; it is the independent implementation that grades it.
pub fn cross_check_family(
    census: &CorpusCensus,
    atlas: &ConductAtlas,
    surface: SurfaceId,
    horizon: usize,
    family: ReceiverFamily,
    declared_capacity: u64,
) -> Result<FamilyCrossCheck, ExhibitionObstructed> {
    let complex = SeparationComplex::read(census, atlas, surface, horizon);
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
    let system = OccurrenceSystem::restricted(census, atlas, roots, horizon, family);
    let root_items: BTreeSet<ItemId> = (0..presented).map(|root| system.root_item(root)).collect();
    let organ_blocks = compress(&system)
        .conduct
        .blocks
        .iter()
        .filter(|block| block.iter().any(|item| root_items.contains(item)))
        .count();
    let reading = complex.conduct_invariance(BigUint::from(census.occurrences(surface)));
    Ok(FamilyCrossCheck {
        surface,
        horizon,
        family,
        projected_blocks: complex.family_blocks(family),
        organ_blocks,
        collapses_claimed: reading.collapses(family),
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
pub fn axis_witnesses(
    census: &CorpusCensus,
    atlas: &ConductAtlas,
) -> BTreeMap<ReceiverAxis, AxisWitness> {
    let surfaces = census.word_surfaces();
    let mut witnesses = BTreeMap::new();
    for axis in ReceiverAxis::DECLARED {
        let mut buckets: BTreeMap<Vec<u64>, (u64, SurfaceId)> = BTreeMap::new();
        for surface in &surfaces {
            let signature = reading(census, atlas, *surface);
            let held: Vec<u64> = ReceiverAxis::DECLARED
                .into_iter()
                .filter(|other| *other != axis)
                .map(|other| other.read(signature))
                .collect();
            let varying = axis.read(signature);
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

/// **One axis's residue against a declared family, over the SURFACE population** — and the same
/// question asked the other way round, which is the arm an added axis can never answer.
///
/// `founded_receiver`'s definition, verbatim: `Res(r) = ( ⋂_{s≠r} ≡_s ) ∖ ≡_r`, the pairs every
/// other receiver identifies and this one separates. An axis with empty residue is **redundant**,
/// and by that module's capacity law it takes capacity `residue + 1`, so a redundant axis is not
/// deleted — it becomes the most congested route.
///
/// The second arm exists because adding a receiver may only **refine** (H.0016's transformations
/// clause), so an axis joining a panel can only ever separate. Whether it can *hold together* what
/// the panel splits is a question about the axis **alone**, and it is the one that decides whether a
/// coarser reading exists at all.
///
/// Both arms are exact and neither materializes a pair: the population is grouped and the count is
/// `Σ C(n,2)` over the groups.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SurfaceResidue {
    pub axis: ReceiverAxis,
    pub against: ReceiverFamily,
    pub population: usize,
    /// Pairs of surfaces `against` identifies.
    pub identified_by_against: BigUint,
    /// Of those, the pairs this axis **separates**. `founded_receiver`'s `Res(r)`.
    pub residue: BigUint,
    /// A pair witnessing the residue, exhibited rather than counted.
    pub residue_witness: Option<(SurfaceId, SurfaceId)>,
    /// Pairs of surfaces this axis alone identifies.
    pub identified_by_axis: BigUint,
    /// Of those, the pairs `against` **separates** — what a reading at this axis alone can hold
    /// together and the declared panel cannot.
    pub carried_alone: BigUint,
    /// A pair witnessing that arm.
    pub carried_witness: Option<(SurfaceId, SurfaceId)>,
}

impl SurfaceResidue {
    /// `founded_receiver`'s capacity law, applied: `capacity := |Res(r)| + 1`. The `+ 1` is forced
    /// because `set_site_capacity` refuses zero, so an empty residue takes the minimum and dilates
    /// maximally rather than being removed by a chooser.
    pub fn capacity(&self) -> BigUint {
        self.residue.clone() + BigUint::from(1u32)
    }

    /// The axis is redundant in the family: removing it leaves the partition unmoved.
    pub fn is_redundant(&self) -> bool {
        self.residue == BigUint::from(0u32)
    }
}

/// Compute one axis's two-armed residue against a declared family over the whole surface population.
pub fn surface_residue(
    census: &CorpusCensus,
    atlas: &ConductAtlas,
    axis: ReceiverAxis,
    against: ReceiverFamily,
) -> SurfaceResidue {
    let surfaces = census.word_surfaces();
    let mut by_against: BTreeMap<Vec<u64>, Vec<SurfaceId>> = BTreeMap::new();
    let mut by_axis: BTreeMap<u64, Vec<SurfaceId>> = BTreeMap::new();
    for surface in &surfaces {
        let signature = reading(census, atlas, *surface);
        let key: Vec<u64> = against
            .axes()
            .into_iter()
            .map(|member| member.read(signature))
            .collect();
        by_against.entry(key).or_default().push(*surface);
        by_axis
            .entry(axis.read(signature))
            .or_default()
            .push(*surface);
    }

    // Both arms are the same shape: a coarse grouping, refined by the other reading, and the
    // difference of the two pair counts is what the refinement broke apart.
    let split = |groups: &BTreeMap<Vec<u64>, Vec<SurfaceId>>,
                 refine: &dyn Fn(SurfaceId) -> Vec<u64>|
     -> (BigUint, BigUint, Option<(SurfaceId, SurfaceId)>) {
        let mut coarse = BigUint::from(0u32);
        let mut broken = BigUint::from(0u32);
        let mut witness = None;
        for members in groups.values() {
            coarse += choose_two(&BigUint::from(members.len()));
            let mut refined: BTreeMap<Vec<u64>, Vec<SurfaceId>> = BTreeMap::new();
            for member in members {
                refined.entry(refine(*member)).or_default().push(*member);
            }
            let inside: BigUint = refined
                .values()
                .map(|block| choose_two(&BigUint::from(block.len())))
                .sum();
            let here = choose_two(&BigUint::from(members.len())) - inside;
            if here > BigUint::from(0u32) && witness.is_none() && refined.len() > 1 {
                let mut blocks = refined.values();
                let left = blocks.next().and_then(|block| block.first()).copied();
                let right = blocks.next().and_then(|block| block.first()).copied();
                if let (Some(left), Some(right)) = (left, right) {
                    witness = Some((left, right));
                }
            }
            broken += here;
        }
        (coarse, broken, witness)
    };

    let (identified_by_against, residue, residue_witness) = split(&by_against, &|surface| {
        vec![axis.read(reading(census, atlas, surface))]
    });
    let by_axis_keyed: BTreeMap<Vec<u64>, Vec<SurfaceId>> = by_axis
        .into_iter()
        .map(|(token, members)| (vec![token], members))
        .collect();
    let (identified_by_axis, carried_alone, carried_witness) = split(&by_axis_keyed, &|surface| {
        let signature = reading(census, atlas, surface);
        against
            .axes()
            .into_iter()
            .map(|member| member.read(signature))
            .collect()
    });

    SurfaceResidue {
        axis,
        against,
        population: surfaces.len(),
        identified_by_against,
        residue,
        residue_witness,
        identified_by_axis,
        carried_alone,
        carried_witness,
    }
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
    atlas: &ConductAtlas,
    surface: SurfaceId,
    horizon: usize,
) -> Vec<AblationReading> {
    let windows: Vec<Window> = census
        .sites(surface)
        .iter()
        .map(|(whole, position)| window(census, atlas, *whole, *position, horizon))
        .collect();
    let with = windows.iter().collect::<BTreeSet<_>>().len();
    ReceiverAxis::DECLARED
        .into_iter()
        .map(|axis| AblationReading {
            axis,
            blocks_with: with,
            blocks_without: windows
                .iter()
                .map(|window| project(window, ReceiverFamily::FULL.without(axis)))
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
    atlas: &ConductAtlas,
    surface: SurfaceId,
    horizon: usize,
    declared_capacity: u64,
) -> Result<Vec<AblationReading>, ExhibitionObstructed> {
    let complex = SeparationComplex::read(census, atlas, surface, horizon);
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
    let system = OccurrenceSystem::new(census, atlas, roots, horizon);
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

    /// The horizon these fixtures found the conduct atlas at. A caller's declaration, and
    /// deliberately not the horizon every reading below runs at — the two are separate.
    const TEST_FOUNDING_HORIZON: usize = 1;

    fn atlas(census: &CorpusCensus) -> ConductAtlas {
        ConductAtlas::found(census, TEST_FOUNDING_HORIZON)
    }

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
        let atlas = atlas(&census);

        let arxiv = census.lookup("arxiv").expect("the fixture writes it");
        let set = census.lookup("set").expect("the fixture writes it");

        let iron = separation_reading(&census, &atlas, arxiv, 1);
        assert_eq!(iron.distinct_windows, 1, "one construction, one window");
        assert_eq!(iron.verdict, Verdict::Iron);
        assert_eq!(
            iron.exhibit(&census, TEST_CAPACITY).expect("within capacity"),
            Vec::new(),
            "an iron surface has no separations at all"
        );

        let fuzzy = separation_reading(&census, &atlas, set, 1);
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
        let atlas = atlas(&census);
        let near = iron_at(&sweep(&census, &atlas, 1));
        let far = iron_at(&sweep(&census, &atlas, 2));
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
        let atlas = atlas(&census);
        let mut checked = 0usize;
        for horizon in [1usize, 2] {
            for surface in census.word_surfaces() {
                let check = cross_check(&census, &atlas, surface, horizon, TEST_CAPACITY)
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
        let atlas = atlas(&census);
        let set = census.lookup("set").unwrap();
        let check = cross_check(&census, &atlas, set, 1, TEST_CAPACITY).expect("within capacity");
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
        let atlas = atlas(&census);
        let witnesses = axis_witnesses(&census, &atlas);
        for axis in ReceiverAxis::DECLARED {
            let witness = witnesses
                .get(&axis)
                .unwrap_or_else(|| panic!("axis {} found no witness", axis.name()));
            let left = reading(&census, &atlas, witness.left);
            let right = reading(&census, &atlas, witness.right);
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
        let atlas = atlas(&census);
        let set = census.lookup("set").unwrap();
        let projected = ablation_profile(&census, &atlas, set, 1);
        let organ = cross_check_ablation(&census, &atlas, set, 1, TEST_CAPACITY).expect("within capacity");
        assert_eq!(projected.len(), ReceiverAxis::DECLARED.len());
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
        let atlas = atlas(&census);
        let iron = iron_at(&sweep(&census, &atlas, 1));
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
        let atlas = atlas(&census);
        let reading = sweep(&census, &atlas, 2);

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
        let atlas = atlas(&census);
        let arxiv = census.lookup("arxiv").unwrap();
        let reading = separation_reading(&census, &atlas, arxiv, 1);
        assert_eq!(reading.survived_pairs(), BigUint::from(3u32));
        assert_eq!(
            reading.separated_occurrence_pairs(),
            BigUint::from(0u32),
            "three occurrences in one window class separate into nothing"
        );

        let set = census.lookup("set").unwrap();
        let fuzzy = separation_reading(&census, &atlas, set, 1);
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
        let atlas = atlas(&census);
        let set = census.lookup("set").unwrap();
        let reading = separation_reading(&census, &atlas, set, 1);
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

    // ---------------------------------------------------------------------------------------------
    // The other pole
    // ---------------------------------------------------------------------------------------------

    /// A corpus built so that **every arm** of [`ConductVerdict`] is forced by material rather than
    /// by an argument, and so that each declared axis is both held and varied somewhere.
    ///
    /// - `arxiv` — two occurrences, one window. **Iron**, witnessed.
    /// - `bee`  — `aa bee cc` and `dddd bee eeee`. Neighbours are all lowercase and all singletons,
    ///   so `kind` and `density` are held while the length band moves: **conduct-invariant at
    ///   `{kind,density}`**.
    /// - `pp`   — `Kk pp ll` and `tt pp Nn`. Neighbours are all two characters and all singletons,
    ///   so `weight` and `density` are held while the orthographic kind moves: **conduct-invariant
    ///   at `{weight,density}`**. Between them the two surfaces hold and vary each axis.
    /// - `ww`   — neighbours differ in kind, in length band, and in density band: **varying**, with
    ///   no collapsing family at all.
    /// - `qq`   — opens its whole once and stands mid-stream once: **varying by TERMINUS**, which no
    ///   ablation can repair.
    fn conduct_corpus(name: &str) -> std::path::PathBuf {
        let root = scratch(name);
        write(
            &root,
            "papers/source/mathematics/a.typ",
            "zz aa bee cc zz\n\
             zz dddd bee eeee zz\n\
             pad ref arxiv . org pad ref arxiv . org pad\n",
        );
        write(&root, "canon/a.md", "qq mm nn rr qq ss\n");
        write(
            &root,
            "research/records/a.md",
            "alpha ww Beta zz ww 12345 gamma ww ee\n",
        );
        write(&root, "reference/pureholonics-seed/a.md", "Kk pp ll tt pp Nn\n");
        root
    }

    /// The verdict the module exists for, on material that forces it: many windows, and one conduct
    /// block under the family the surface's own material holds constant.
    #[test]
    fn a_variously_used_surface_collapses_at_the_family_its_material_holds() {
        let root = conduct_corpus("collapse");
        let census = CorpusCensus::read(&root).unwrap();
        let atlas = atlas(&census);

        let bee = census.lookup("bee").expect("the fixture writes it");
        let reading = separation_reading(&census, &atlas, bee, 1);
        let invariance = reading.conduct_invariance();

        assert_eq!(reading.distinct_windows, 2, "`bee` stands in two constructions");
        assert!(matches!(reading.verdict, Verdict::Separated { .. }), "not iron");
        // `aa`/`dddd` and `cc`/`eeee` are all lowercase singletons standing in one construction
        // each, so `kind`, `density` and `conduct` all agree across the two occurrences and only
        // the length band moves.
        assert_eq!(
            invariance.verdict,
            ConductVerdict::ConductInvariant {
                windows: 2,
                collapsing: ReceiverFamily::of([
                    ReceiverAxis::Kind,
                    ReceiverAxis::Density,
                    ReceiverAxis::Conduct
                ]),
            },
        );
        assert_eq!(
            invariance.varying_axes(),
            ReceiverFamily::of([ReceiverAxis::Weight]),
            "the length band is the one thing that moved"
        );
        // The claim, checked against the projection rather than restated.
        assert_eq!(reading.family_blocks(ReceiverFamily::FULL), 2);
        assert_eq!(reading.family_blocks(invariance.constant_axes), 1);

        // Non-vacuity: the verdict withstood real separations, and the count is exact.
        assert_eq!(invariance.separations_withstood, BigUint::from(1u32));
        assert!(!invariance.vacuous());

        // The second surface holds the complementary pair of axes, so between the two every
        // declared axis is both held and varied on this material.
        let pp = census.lookup("pp").expect("the fixture writes it");
        let other = separation_reading(&census, &atlas, pp, 1).conduct_invariance();
        assert_eq!(
            other.verdict,
            ConductVerdict::ConductInvariant {
                windows: 2,
                collapsing: ReceiverFamily::of([
                    ReceiverAxis::Weight,
                    ReceiverAxis::Density,
                    ReceiverAxis::Conduct
                ]),
            },
        );
        let _ = fs::remove_dir_all(&root);
    }

    /// A terminus is family-invariant. No ablation merges `<end of whole>` with a reading, so a
    /// surface whose occurrences disagree about whether an offset exists is separated even by the
    /// empty family — the one case where `constant_axes` is not the whole story.
    #[test]
    fn a_terminus_refuses_every_family_including_the_empty_one() {
        let root = conduct_corpus("terminus-family");
        let census = CorpusCensus::read(&root).unwrap();
        let atlas = atlas(&census);
        let qq = census.lookup("qq").expect("the fixture writes it");
        let reading = separation_reading(&census, &atlas, qq, 1);
        let invariance = reading.conduct_invariance();

        assert!(invariance.terminus_varies, "`qq` opens its whole exactly once");
        assert_eq!(
            invariance.verdict,
            ConductVerdict::Varying {
                windows: 2,
                terminus_varies: true
            }
        );
        assert!(
            invariance.collapsing_families().is_empty(),
            "not even the empty family collapses a varying terminus"
        );
        assert_eq!(
            reading.family_blocks(ReceiverFamily::EMPTY),
            2,
            "with no receiver at all the terminus still separates the two occurrences"
        );
        let _ = fs::remove_dir_all(&root);
    }

    /// A surface whose material moves every declared axis collapses nowhere. Without this the
    /// verdict would be admitting everything that is not iron.
    #[test]
    fn a_surface_that_moves_every_axis_collapses_at_no_family() {
        let root = conduct_corpus("varying");
        let census = CorpusCensus::read(&root).unwrap();
        let atlas = atlas(&census);
        let ww = census.lookup("ww").expect("the fixture writes it");
        let invariance = separation_reading(&census, &atlas, ww, 1).conduct_invariance();
        assert!(!invariance.terminus_varies);
        assert_eq!(invariance.constant_axes, ReceiverFamily::EMPTY);
        assert!(matches!(
            invariance.verdict,
            ConductVerdict::Varying {
                terminus_varies: false,
                ..
            }
        ));
        let _ = fs::remove_dir_all(&root);
    }

    /// The down-set theorem the verdict rests on, checked against the projection for **every** one
    /// of the eight declared families on **every** surface at both horizons.
    ///
    /// `F` collapses iff `F ⊆ constant_axes` and the terminus pattern does not vary. If that were
    /// wrong, naming one maximal family would be naming the wrong set, and the verdict would be a
    /// search result presented as a theorem.
    #[test]
    fn the_collapsing_families_are_exactly_the_subsets_of_the_constant_axes() {
        let root = conduct_corpus("downset");
        let census = CorpusCensus::read(&root).unwrap();
        let atlas = atlas(&census);
        let mut collapsing_seen = 0usize;
        let mut refusing_seen = 0usize;
        for horizon in [1usize, 2] {
            for surface in census.word_surfaces() {
                let reading = separation_reading(&census, &atlas, surface, horizon);
                let invariance = reading.conduct_invariance();
                for family in ReceiverFamily::FULL.subsets() {
                    let projected = reading.family_blocks(family) == 1;
                    assert_eq!(
                        invariance.collapses(family),
                        projected,
                        "horizon {horizon}, {:?}, family {family}: the down-set law said {} and \
                         the projection said {projected} ({invariance:?})",
                        census.surface(surface),
                        invariance.collapses(family),
                    );
                    if projected {
                        collapsing_seen += 1;
                    } else {
                        refusing_seen += 1;
                    }
                }
            }
        }
        assert!(
            collapsing_seen > 0 && refusing_seen > 0,
            "a law that only ever collapses, or only ever refuses, proves nothing about itself: \
             {collapsing_seen} collapsed, {refusing_seen} refused"
        );
        let _ = fs::remove_dir_all(&root);
    }

    /// The projection and `receiver_exact_compression` are two implementations of the sub-family
    /// block count, and they must agree at **every** family — including the empty one, where the
    /// organ has no receiver and separates by terminus alone.
    #[test]
    fn the_projection_and_the_organ_agree_at_every_declared_sub_family() {
        let root = conduct_corpus("family-parity");
        let census = CorpusCensus::read(&root).unwrap();
        let atlas = atlas(&census);
        let mut checked = 0usize;
        let mut collapsed = 0usize;
        for horizon in [1usize, 2] {
            for surface in census.word_surfaces() {
                for family in ReceiverFamily::FULL.subsets() {
                    let check = cross_check_family(&census, &atlas, surface, horizon, family, TEST_CAPACITY)
                        .expect("the fixture is inside the declared capacity");
                    assert!(
                        check.agrees(),
                        "horizon {horizon}, {:?}: {check:?}",
                        census.surface(surface)
                    );
                    checked += 1;
                    if check.organ_blocks == 1 {
                        collapsed += 1;
                    }
                }
            }
        }
        assert!(checked > 0);
        assert!(
            collapsed > 0,
            "the organ must actually collapse something or the parity is over one outcome"
        );
        let _ = fs::remove_dir_all(&root);
    }

    /// The two verdicts partition the measured population, they agree exactly on iron, and the
    /// conduct-invariant block is disjoint from it by construction.
    #[test]
    fn the_two_verdicts_partition_the_measured_population_and_agree_on_iron() {
        let root = conduct_corpus("partition");
        let census = CorpusCensus::read(&root).unwrap();
        let atlas = atlas(&census);
        let reading = sweep(&census, &atlas, 1);
        let partition = invariance_partition(&reading);

        assert!(
            partition.is_a_partition(census.word_surfaces().len()),
            "the blocks must be disjoint and cover the measured population: {partition:?}"
        );

        // `ConductVerdict::Iron` and `Verdict::Iron` are the same population, not two readings that
        // happen to look alike.
        let iron: BTreeSet<SurfaceId> = iron_at(&reading);
        let conduct_iron: BTreeSet<SurfaceId> = partition
            .vacuously_iron
            .union(&partition.witnessed_iron)
            .copied()
            .collect();
        assert_eq!(iron, conduct_iron);
        assert!(iron.is_disjoint(&partition.conduct_invariant));

        // Every arm is exercised by the fixture, so the partition is not a taxonomy with empty
        // cells presented as a result.
        assert!(!partition.witnessed_iron.is_empty());
        assert!(!partition.vacuously_iron.is_empty());
        assert!(!partition.conduct_invariant.is_empty());
        assert!(!partition.varying.is_empty());
        let _ = fs::remove_dir_all(&root);
    }

    /// Two structural guarantees the verdict is stated to carry, checked over the whole sweep:
    /// a conduct-invariant surface's collapsing family is **nonempty and proper**, and its
    /// `separations_withstood` is **nonzero**. Neither can be arranged by a corpus.
    #[test]
    fn a_conduct_invariant_verdict_is_never_vacuous_and_never_the_whole_family() {
        let root = conduct_corpus("nonvacuous");
        let census = CorpusCensus::read(&root).unwrap();
        let atlas = atlas(&census);
        let mut admitted = 0usize;
        for horizon in [1usize, 2] {
            for (_, reading) in sweep(&census, &atlas, horizon) {
                let invariance = reading.conduct_invariance();
                let ConductVerdict::ConductInvariant { collapsing, windows } = invariance.verdict
                else {
                    continue;
                };
                admitted += 1;
                assert!(!collapsing.is_empty());
                assert!(
                    collapsing != ReceiverFamily::FULL,
                    "all three axes constant with a constant terminus is ONE window, which is iron"
                );
                assert!(windows > 1);
                assert!(reading.occurrences >= BigUint::from(2u32));
                assert!(
                    invariance.separations_withstood > BigUint::from(0u32),
                    "many windows forces a separated pair; a zero here would be a vacuous verdict"
                );
            }
        }
        assert!(admitted > 0, "the fixture must admit the verdict somewhere");
        let _ = fs::remove_dir_all(&root);
    }

    /// The verdict is computed by a route that never materializes a pair, so a surface whose
    /// exhibition the declared capacity refuses still receives it whole. This is the aperture law
    /// held rather than widened.
    #[test]
    fn a_verdict_is_returned_where_the_exhibition_is_obstructed() {
        let root = conduct_corpus("aperture");
        let census = CorpusCensus::read(&root).unwrap();
        let atlas = atlas(&census);
        let bee = census.lookup("bee").unwrap();
        let reading = separation_reading(&census, &atlas, bee, 1);
        reading
            .exhibit(&census, 0)
            .expect_err("a capacity of zero cannot hold this population");
        assert!(
            reading.conduct_invariance().verdict.is_conduct_invariant(),
            "the verdict does not go through the population the aperture bounds"
        );
        let _ = fs::remove_dir_all(&root);
    }

    /// `ablation_profile` removes one axis; `family_blocks` reads the complement. They are two
    /// spellings of one number and must agree.
    #[test]
    fn removing_one_axis_and_reading_its_complement_are_the_same_count() {
        let root = conduct_corpus("ablation-parity");
        let census = CorpusCensus::read(&root).unwrap();
        let atlas = atlas(&census);
        for surface in census.word_surfaces() {
            let complex = SeparationComplex::read(&census, &atlas, surface, 1);
            for reading in ablation_profile(&census, &atlas, surface, 1) {
                assert_eq!(
                    reading.blocks_with,
                    complex.family_blocks(ReceiverFamily::FULL)
                );
                assert_eq!(
                    reading.blocks_without,
                    complex.family_blocks(ReceiverFamily::FULL.without(reading.axis)),
                    "{:?} without {}",
                    census.surface(surface),
                    reading.axis.name()
                );
            }
        }
        let _ = fs::remove_dir_all(&root);
    }

    /// A separation resolved by a terminus rather than by a receiver is returned as such, on
    /// material that forces one: the papers whole opens on `pad`, so that occurrence has no left
    /// neighbour while every other `pad` does.
    #[test]
    fn a_terminus_is_a_distinction_and_is_named_as_one() {
        let root = declared_corpus("terminus");
        let census = CorpusCensus::read(&root).unwrap();
        let atlas = atlas(&census);
        let pad = census.lookup("pad").unwrap();
        let reading = separation_reading(&census, &atlas, pad, 1);
        let separations = reading.exhibit(&census, TEST_CAPACITY).expect("within capacity");
        assert!(
            separations.iter().any(|separation| separation.by_terminus),
            "the opening `pad` has no left neighbour and every other one does: {separations:?}"
        );
        let check = cross_check(&census, &atlas, pad, 1, TEST_CAPACITY).expect("within capacity");
        assert!(check.agrees(), "the organ must agree about the terminus too: {check:?}");
        let _ = fs::remove_dir_all(&root);
    }

    // ---------------------------------------------------------------------------------------------
    // The fourth axis
    // ---------------------------------------------------------------------------------------------

    #[test]
    fn a_conduct_signature_round_trips_through_the_token_a_receiver_returns() {
        for holds in ReceiverFamily::ORTHOGRAPHIC.subsets() {
            for terminus_varies in [false, true] {
                let signature = ConductSignature {
                    holds,
                    terminus_varies,
                };
                assert_eq!(ConductSignature::decode(signature.encode()), signature);
            }
        }
        // The token IS the lattice point, so iron — nothing varied — is the top of the down-set
        // with no terminus, and nothing else is.
        assert!(
            ConductSignature {
                holds: ReceiverFamily::ORTHOGRAPHIC,
                terminus_varies: false
            }
            .is_iron()
        );
        assert!(
            !ConductSignature {
                holds: ReceiverFamily::ORTHOGRAPHIC,
                terminus_varies: true
            }
            .is_iron()
        );
    }

    /// The atlas's own founding routine and the module's [`ConductInvariance`] are two
    /// implementations of one reading, and they must agree on **every** surface.
    ///
    /// Run against the *unfounded* atlas, so the conduct coordinate is constant and the reading is
    /// genuinely at the orthographic panel — which is the panel the founding is defined over. If
    /// these disagreed, the axis would be reading something other than what it claims.
    #[test]
    fn the_founded_signature_is_the_orthographic_reading_computed_independently() {
        let root = declared_corpus("founding-parity");
        let census = CorpusCensus::read(&root).unwrap();
        let flat = ConductAtlas::unfounded(&census, TEST_FOUNDING_HORIZON);
        let founded = ConductAtlas::found(&census, TEST_FOUNDING_HORIZON);
        let mut checked = 0usize;
        let mut varied = BTreeSet::new();
        for surface in census.word_surfaces() {
            let complex =
                SeparationComplex::read(&census, &flat, surface, TEST_FOUNDING_HORIZON);
            let reading = complex.conduct_invariance(BigUint::from(census.occurrences(surface)));
            let signature = founded.signature(surface);
            assert_eq!(
                ReceiverFamily(reading.constant_axes.0 & ReceiverFamily::ORTHOGRAPHIC.0),
                signature.holds,
                "{:?}: the atlas and the invariance reading disagree about what is held",
                census.surface(surface)
            );
            assert_eq!(
                reading.terminus_varies,
                signature.terminus_varies,
                "{:?}: the two disagree about the terminus",
                census.surface(surface)
            );
            varied.insert(signature);
            checked += 1;
        }
        assert!(checked > 0);
        assert!(
            varied.len() > 1,
            "a parity check over one signature value could not have come out otherwise: {varied:?}"
        );
        let _ = fs::remove_dir_all(&root);
    }

    /// The residue law, both arms, on real declared material.
    ///
    /// `founded_receiver`: `Res(r) = ( ⋂_{s≠r} ≡_s ) ∖ ≡_r`, and an axis whose residue is empty is
    /// redundant. The unfounded atlas is exactly that axis and must measure as one; the founded
    /// atlas must not. And the second arm — pairs the axis alone identifies that the orthographic
    /// panel separates — is the one an added receiver can never produce, because adding a receiver
    /// may only refine.
    #[test]
    fn the_conduct_axis_has_a_non_empty_residue_and_an_unfounded_one_is_redundant() {
        let root = declared_corpus("residue");
        let census = CorpusCensus::read(&root).unwrap();
        let founded = ConductAtlas::found(&census, TEST_FOUNDING_HORIZON);
        let flat = ConductAtlas::unfounded(&census, TEST_FOUNDING_HORIZON);

        let live = surface_residue(
            &census,
            &founded,
            ReceiverAxis::Conduct,
            ReceiverFamily::ORTHOGRAPHIC,
        );
        assert!(
            live.residue > BigUint::from(0u32),
            "the axis separates a pair the orthographic panel identifies: {live:?}"
        );
        assert!(
            live.carried_alone > BigUint::from(0u32),
            "the axis holds together a pair the orthographic panel separates: {live:?}"
        );
        assert!(live.residue_witness.is_some() && live.carried_witness.is_some());
        assert!(!live.is_redundant());
        assert_eq!(live.capacity(), live.residue.clone() + BigUint::from(1u32));

        // The witnesses are what they claim: one pair agrees orthographically and differs in
        // conduct, the other differs orthographically and agrees in conduct.
        let (left, right) = live.residue_witness.expect("a residue witness");
        assert_eq!(
            census.signature(left),
            census.signature(right),
            "a residue witness must agree on every orthographic coordinate"
        );
        assert_ne!(founded.token(left), founded.token(right));
        let (left, right) = live.carried_witness.expect("a carried witness");
        assert_ne!(census.signature(left), census.signature(right));
        assert_eq!(founded.token(left), founded.token(right));

        let null = surface_residue(
            &census,
            &flat,
            ReceiverAxis::Conduct,
            ReceiverFamily::ORTHOGRAPHIC,
        );
        assert!(
            null.is_redundant(),
            "a constant axis separates nothing and its residue is empty: {null:?}"
        );
        assert_eq!(null.capacity(), BigUint::from(1u32), "the minimum, forced");
        let _ = fs::remove_dir_all(&root);
    }

    /// A permutation of the atlas keeps the multiset of readings exactly and destroys the relation
    /// to the material. It is the null every collapse has to survive.
    #[test]
    fn a_permuted_atlas_keeps_the_coarseness_and_loses_the_material() {
        let root = declared_corpus("permuted");
        let census = CorpusCensus::read(&root).unwrap();
        let founded = ConductAtlas::found(&census, TEST_FOUNDING_HORIZON);
        let population = founded.tokens().len();
        let reversed: Vec<usize> = (0..population).rev().collect();
        let permuted = founded.permuted(&reversed);
        assert_eq!(
            permuted.population(),
            founded.population(),
            "the multiset of readings must be preserved exactly, or the null is a weaker axis"
        );
        assert_ne!(
            permuted.tokens(),
            founded.tokens(),
            "the fixture must actually move a reading, or the null could not fail"
        );
        let _ = fs::remove_dir_all(&root);
    }

    /// The shallowest separation a sub-family still makes agrees with that family's block count on
    /// every surface and every family, and the witness it names is **inside** the family.
    ///
    /// Without the last clause the reading would be the full panel's answer wearing a family's name,
    /// which is exactly the defect it was written to remove.
    #[test]
    fn a_sub_familys_own_shallowest_separation_names_a_receiver_inside_that_family() {
        let root = conduct_corpus("shallowest");
        let census = CorpusCensus::read(&root).unwrap();
        let atlas = atlas(&census);
        let mut separated = 0usize;
        let mut collapsed = 0usize;
        let mut by_terminus = 0usize;
        for horizon in [1usize, 2] {
            for (_, row) in sweep(&census, &atlas, horizon) {
                for family in ReceiverFamily::FULL.subsets() {
                    let blocks = row.family_blocks(family);
                    match row.shallowest_within(family) {
                        None => {
                            assert_eq!(blocks, 1, "no separation named where {family} leaves {blocks}");
                            collapsed += 1;
                        }
                        Some(separation) => {
                            assert!(blocks > 1);
                            assert_eq!(separation.blocks, blocks);
                            assert!(!separation.word.is_empty());
                            match separation.axis {
                                Some(axis) => assert!(
                                    family.contains(axis),
                                    "{family} named {} which is not in it",
                                    axis.name()
                                ),
                                None => {
                                    assert!(separation.by_terminus);
                                    by_terminus += 1;
                                }
                            }
                            separated += 1;
                        }
                    }
                }
            }
        }
        assert!(
            separated > 0 && collapsed > 0 && by_terminus > 0,
            "both outcomes and the terminus arm must occur or this proves nothing about itself: \
             {separated} separated, {collapsed} collapsed, {by_terminus} by terminus"
        );
        let _ = fs::remove_dir_all(&root);
    }

    /// **The object the axis exists for, on material that forces it.**
    ///
    /// `alpha` stands in three constructions. Its neighbours differ on **every** orthographic axis —
    /// `one` against `LONGWORD` against `gg` moves case class, length band and density band — so no
    /// nonempty orthographic family holds its occurrences together. But all six neighbours were used
    /// by this corpus in exactly one construction each, so all six carry the **same** conduct
    /// signature, and the conduct axis alone holds all three occurrences in one block.
    ///
    /// That is the collapse the three declared axes could not make: an added receiver may only
    /// refine, so the coarsening arm is only reachable by an axis that reads something else.
    fn typography_corpus(name: &str) -> std::path::PathBuf {
        let root = scratch(name);
        write(
            &root,
            "papers/source/mathematics/a.typ",
            "zero one alpha two three\n",
        );
        write(&root, "canon/a.md", "zero LONGWORD alpha four five\n");
        write(&root, "research/records/a.md", "pp gg alpha six hh\n");
        write(&root, "reference/pureholonics-seed/a.md", "pp gg alpha six hh\n");
        root
    }

    /// **The star atlas covers the pair chart exactly: a rebase, remainder zero.**
    ///
    /// Every separation lies in exactly two stars, so the atlas visits each pair twice and the
    /// deduplicated union is the pair chart on the nose. If this ever failed, reading through the
    /// atlas would be a truncation and the capacity it replaces would have been load-bearing.
    #[test]
    fn the_star_atlas_covers_the_pair_chart_with_no_remainder() {
        let root = declared_corpus("star-atlas");
        let census = CorpusCensus::read(&root).unwrap();
        let atlas = atlas(&census);
        let mut covered_any = false;
        for surface in census.word_surfaces() {
            let complex = SeparationComplex::read(&census, &atlas, surface, 1);
            let d = complex.distinct_windows();
            if d < 2 {
                continue;
            }
            covered_any = true;

            let pairs = complex.exhibit_in(&census, SeparationChart::Pair);
            let key = |s: &Separation| (s.offset, s.word.clone(), s.left_surface, s.right_surface);

            let mut from_atlas: Vec<_> = complex
                .pair_atlas()
                .into_iter()
                .flat_map(|chart| complex.exhibit_in(&census, chart))
                .collect();
            // Each pair is reached from both of its endpoints. That double cover is the atlas's
            // overlap, and it is exactly two everywhere.
            assert_eq!(
                from_atlas.len(),
                2 * pairs.len(),
                "every pair lies in exactly two stars: {surface:?}"
            );

            // Compared as MULTISETS, not deduplicated. Two distinct class pairs can separate on the
            // same word at the same offset, so a rendered key is not an identity — collapsing on
            // one is how a covering check quietly becomes weaker than the thing it checks.
            let mut expected: Vec<_> = pairs.iter().cloned().chain(pairs.iter().cloned()).collect();
            expected.sort_by_key(key);
            from_atlas.sort_by_key(key);
            assert_eq!(
                from_atlas.len(),
                expected.len(),
                "the atlas is the pair chart twice over"
            );
            for (through_atlas, direct) in from_atlas.iter().zip(&expected) {
                assert_eq!(key(through_atlas), key(direct), "no pair invented or lost");
            }
        }
        assert!(covered_any, "the fixture must carry a separated surface");
        let _ = fs::remove_dir_all(&root);
    }

    /// **The demand is computed from the orbit count, and the pair chart's degree grows with it.**
    ///
    /// This is what the excised constant could not be: a quantity that varies over the base. A
    /// single number is a constant section of a bundle whose fibre dimension is not constant.
    #[test]
    fn the_chart_demand_is_hypergeometric_in_the_orbit_count() {
        let root = declared_corpus("chart-demand");
        let census = CorpusCensus::read(&root).unwrap();
        let atlas = atlas(&census);
        let mut degrees = BTreeSet::new();
        let mut widths = BTreeSet::new();
        for surface in census.word_surfaces() {
            let complex = SeparationComplex::read(&census, &atlas, surface, 1);
            let d = complex.distinct_windows();
            let orbit = complex.demand(SeparationChart::Orbit);
            let star = complex.demand(SeparationChart::Star(0));
            let pair = complex.demand(SeparationChart::Pair);

            assert_eq!(orbit.extent, BigUint::from(d));
            assert_eq!(star.extent, BigUint::from(d.saturating_sub(1)));
            assert_eq!(pair.extent, choose_two(&BigUint::from(d)));
            // The two charts of degree one, and the one that is not.
            assert!(orbit.is_degree_one() && star.is_degree_one());
            assert_eq!(pair.degree.1, BigUint::from(2u32));
            assert_eq!(pair.degree.0, BigUint::from(d.saturating_sub(1)));
            // `extent = classes × degree` exactly: the transition is a dimension multiplier.
            assert_eq!(
                pair.extent.clone() * BigUint::from(2u32),
                orbit.extent.clone() * pair.degree.0.clone(),
                "the pair chart is the orbit chart times (d−1)/2"
            );
            degrees.insert(pair.degree.0.clone());
            widths.insert(pair.extent.clone());
        }
        assert!(
            degrees.len() > 1 && widths.len() > 1,
            "the demand must VARY over the base, or a constant could have served: \
             {degrees:?} {widths:?}"
        );
        let _ = fs::remove_dir_all(&root);
    }

    /// **This organ's key, driven through the SHARED law, equals this organ's own refinement.**
    ///
    /// The point of the factoring: `saturation_horizon` and `quotient_on_host` are not two
    /// implementations to be kept in step — the second is the law and the first supplies a key to
    /// it. This proves they agree on real material, which is what makes replacing the fused path
    /// with the shared one safe for every other organ that adopts it.
    #[test]
    fn the_shell_key_through_the_shared_quotient_equals_this_organs_own_refinement() {
        use crate::cuda_refine::{ReadingIdentities, quotient_on_host};
        let root = declared_corpus("shared-quotient");
        let census = CorpusCensus::read(&root).unwrap();
        let atlas = atlas(&census);
        let identities = ReadingIdentities::of(&census, &atlas);
        let bound = material_horizon_bound(&census);
        let mut exercised = 0usize;
        for surface in census.word_surfaces() {
            let sites = census.sites(surface);
            if sites.len() < 2 {
                continue;
            }
            exercised += 1;
            // Walk the shared law shell by shell, exactly as the organ does.
            let mut classes = vec![1u32; sites.len()];
            let mut carried = 1usize;
            for depth in 1..=bound {
                if carried == sites.len() {
                    break;
                }
                let keys = shell_keys_of(&census, &identities.per_surface, surface, depth);
                let step = quotient_on_host(&classes, &keys);
                classes = step.cell_class;
                carried = step.classes;
            }
            // The organ's own reading of the same material.
            let mine = SeparationComplex::read(&census, &atlas, surface, bound);
            assert_eq!(
                carried,
                mine.distinct_windows(),
                "class count for {surface:?} through the shared law"
            );
            // And the same equivalence, not the same numbering.
            let mut where_mine: BTreeMap<(u32, u32), usize> = BTreeMap::new();
            for (at, class) in mine.classes.iter().enumerate() {
                for site in &class.sites {
                    where_mine.insert(*site, at);
                }
            }
            let mut forward: BTreeMap<u32, usize> = BTreeMap::new();
            for (at, site) in sites.iter().enumerate() {
                let ours = where_mine[site];
                assert_eq!(
                    *forward.entry(classes[at]).or_insert(ours),
                    ours,
                    "the shared law and the organ must induce one equivalence"
                );
            }
        }
        assert!(exercised > 0, "the fixture must carry a separable surface");
        let _ = fs::remove_dir_all(&root);
    }

    /// **The covered sweep equals the serial one, cell for cell.** Lanes are a realization
    /// coordinate; if they could move a reading they would be chronology.
    #[test]
    fn the_covered_sweep_equals_the_serial_sweep_and_the_cover_actually_spreads() {
        let root = declared_corpus("covered-sweep");
        let census = CorpusCensus::read(&root).unwrap();
        let atlas = atlas(&census);

        let serial = sweep_covered(&census, &atlas, 1, &HardwareCover::of_charts(vec![
            crate::hardware_cover::Chart::Host(crate::hardware_cover::HostDeclaration { lanes: 1 }),
        ]));
        let wide = sweep_covered(&census, &atlas, 1, &HardwareCover::of_charts(vec![
            crate::hardware_cover::Chart::Host(crate::hardware_cover::HostDeclaration { lanes: 8 }),
        ]));

        assert_eq!(serial.host_lanes, 1);
        assert!(
            wide.host_lanes > 1,
            "eight declared lanes over {} surfaces must spread",
            census.word_surfaces().len()
        );
        // `SeparationReading` carries no `PartialEq`, so the comparison is made on every part a
        // reading returns: the surface set, the verdict, the window count, and the complex itself.
        let compare = |left: &BTreeMap<SurfaceId, SeparationReading>,
                       right: &BTreeMap<SurfaceId, SeparationReading>,
                       why: &str| {
            assert_eq!(
                left.keys().collect::<Vec<_>>(),
                right.keys().collect::<Vec<_>>(),
                "{why}: surface population"
            );
            for (surface, one) in left {
                let other = &right[surface];
                assert_eq!(one.verdict, other.verdict, "{why}: verdict at {surface:?}");
                assert_eq!(
                    one.distinct_windows, other.distinct_windows,
                    "{why}: windows at {surface:?}"
                );
                assert_eq!(one.occurrences, other.occurrences, "{why}: occurrences");
                assert_eq!(one.complex, other.complex, "{why}: complex at {surface:?}");
            }
        };
        compare(
            &serial.readings,
            &wide.readings,
            "a lane is a realization coordinate and may not move a reading",
        );
        compare(&sweep(&census, &atlas, 1), &serial.readings, "the default entry point");
        let _ = fs::remove_dir_all(&root);
    }

    /// The horizon is read off the material, and the reading is monotone as the theorem requires.
    ///
    /// `arxiv` sits inside `pad ref arxiv . org pad` every time, so it saturates at its own class
    /// count immediately; `set` occurs in four different neighbourhoods. The two must not derive the
    /// same horizon, or the derivation is returning a property of the corpus rather than of the
    /// receiver-material relation.
    #[test]
    fn the_horizon_is_read_off_the_material_not_declared() {
        let root = declared_corpus("saturation-horizon");
        let census = CorpusCensus::read(&root).unwrap();
        let atlas = atlas(&census);
        let corpus_bound = material_horizon_bound(&census);
        assert!(corpus_bound > 1, "the fixture must admit more than one shell");
        let mut floored = 0usize;

        for surface in census.word_surfaces() {
            let derived = saturation_horizon(&census, &atlas, surface);
            let bound = surface_horizon_bound(&census, surface);
            assert_eq!(derived.bound, bound, "the ceiling is this surface's own");
            assert!(
                bound <= corpus_bound,
                "a surface's own ceiling cannot exceed the corpus's: {bound} > {corpus_bound}"
            );
            assert!(derived.horizon <= bound);

            // Monotone refinement, which is what makes the derivation valid. This is the
            // property the derivation RESTS on, so it is checked rather than assumed.
            let mut previous = 0usize;
            for horizon in 1..=corpus_bound {
                let classes =
                    SeparationComplex::read(&census, &atlas, surface, horizon).distinct_windows();
                assert!(
                    classes >= previous,
                    "a deeper horizon may only separate more: {surface:?} at {horizon}"
                );
                previous = classes;
            }
            assert_eq!(previous, derived.classes, "the ceiling count is final");
            // The surface's OWN ceiling is already final: nothing past it can separate, because
            // every shell out there reads `(None, None)` on every one of its occurrences.
            assert_eq!(
                SeparationComplex::read(&census, &atlas, surface, bound).distinct_windows(),
                derived.classes,
                "this surface's own ceiling is already final; the corpus's adds nothing"
            );

            // The derived level is the LEAST one that is final -- both halves.
            assert_eq!(
                SeparationComplex::read(&census, &atlas, surface, derived.horizon)
                    .distinct_windows(),
                derived.classes,
                "the derived horizon is already final"
            );
            // **No `horizon > 1` guard.** That guard excluded exactly the case the removed
            // `.max(1)` decided. At horizon 1 the shallower reading is at horizon 0, which is the
            // one-class partition, so the check is real there rather than skipped; and horizon 0
            // is the surface saying no shell ever separated anything, which is checkable directly.
            if derived.horizon == 0 {
                floored += 1;
                assert_eq!(
                    derived.classes, 1,
                    "horizon 0 means no shell split, so there is exactly one class: {derived:?}"
                );
                assert_eq!(derived.classes_before, 1);
            } else {
                assert!(
                    SeparationComplex::read(&census, &atlas, surface, derived.horizon - 1)
                        .distinct_windows()
                        < derived.classes,
                    "one shell shallower must still be refining, or the level is not least"
                );
            }

            // The cone must never be propagated further than this surface's material admits, and
            // the live population must be bounded by the shells walked times the occurrences.
            assert!(derived.shells <= bound, "{} shells past {bound}", derived.shells);
            assert!(
                derived.active_total <= derived.shells * census.sites(surface).len(),
                "the live population cannot exceed shells x occurrences"
            );
        }

        // The orbit of the excised floor, on the declared fixture: the branch above must be
        // reached, or the fixture cannot grade the repair and this test is bookkeeping.
        assert!(
            floored > 0,
            "no surface of this fixture reports horizon 0, so the removed `.max(1)` moved nothing \
             here and the excision is ungraded"
        );
    }

    /// **Refinement stalls, and a loop that stopped at the first quiet shell would be wrong.**
    ///
    /// **The premise this test was written under is withdrawn 2026-08-11.** It read: *"The declared
    /// corpus cannot grade this: measured 2026-08-10 over 29,533 real surfaces, zero ever had a
    /// quiet shell before their last split."* That zero came from `walked_past()`, which returned
    /// `shells > horizon` — false on every propagation that exhausts to singletons, since the last
    /// shell walked is the last shell that split. It measured no quiet shell at all. Re-measured
    /// with `interior_quiet_shells`, the declared corpus carries **5,008 stalling surfaces and
    /// 27,668 interior quiet shells**, so a loop halting on the first quiet shell returns the wrong
    /// horizon on real material and not merely on a fixture.
    ///
    /// The control is kept, and it is now the stronger half rather than the only one: it exhibits
    /// the **witness** — the exact shell the unsound loop halts at — against a second, independently
    /// written loop, on material small enough to read.
    ///
    /// Three wholes, all carrying `c`:
    ///
    /// ```text
    ///     A     k a c b k          shell 1 = (a,b)   shell 2 = (k,k)     shell 3 = (-,-)
    ///     B     k z c b k          shell 1 = (z,b)
    ///     C   m k a c b k m        shell 1 = (a,b)   shell 2 = (k,k)     shell 3 = (m,m)
    /// ```
    ///
    /// Shell 1 splits `B` off. **Shell 2 splits nothing** — `A` and `C` still agree and `B` is
    /// already a singleton. Shell 3 splits `A` from `C`. A loop halting on the quiet shell returns
    /// horizon 1 and two classes; the correct answer is horizon 3 and three classes.
    ///
    /// **The assertion this test used to make could not fail, and that was the whole defect.** It
    /// read `assert!(derived.walked_past() || derived.exhausted)`. `walked_past` was
    /// `shells > horizon`, which is `false` on every propagation that exhausts — the last shell
    /// walked is the last shell that split — so on this fixture, built expressly to carry a stall,
    /// it returned `false` and the disjunct was carried entirely by `exhausted`, which is `true`
    /// here by construction. The quantity asserted below is `interior_quiet_shells`, which counts
    /// the shells that split nothing **and were followed by one that did**, and it is non-zero
    /// exactly on material where the sound and the unsound loop disagree.
    #[test]
    fn refinement_stalls_and_the_horizon_is_not_the_first_quiet_shell() {
        // Every declared stratum must be non-empty; the three carrying `c` are the fixture and the
        // fourth is filler that never writes the surface.
        let root = scratch("stalled-refinement");
        write(&root, "papers/source/mathematics/a.typ", "k a c b k\n");
        write(&root, "canon/a.md", "k z c b k\n");
        write(&root, "research/records/a.md", "m k a c b k m\n");
        write(&root, "reference/pureholonics-seed/a.md", "filler only\n");
        let census = CorpusCensus::read(&root).unwrap();
        let atlas = atlas(&census);
        let surface = census.lookup("c").expect("the fixture writes it");

        let derived = saturation_horizon(&census, &atlas, surface);
        assert_eq!(derived.horizon, 3, "the last split is at shell three: {derived:?}");
        assert_eq!(derived.classes, 3, "all three occurrences separate");
        assert_eq!(derived.classes_at_one, 2, "shell one splits B off and nothing else");

        // **The stall itself, with its witness, and no disjunction anywhere.** Shell 2 split nothing
        // and shell 3 split, so exactly one shell is interior quiet; the resumption names shell 2,
        // shell 3, and the two occurrences shell 3 pulled apart. Every one of these is `0`/`None` on
        // material that never stalls, which is what makes them assertions and not restatements.
        assert_eq!(
            derived.interior_quiet_shells, 1,
            "shell two split nothing and shell three split: {derived:?}"
        );
        let resumption = derived.first_resumption.expect("the fixture stalls and resumes");
        assert_eq!(resumption.quiet_shell, 2, "the unsound loop halts at shell two");
        assert_eq!(resumption.resumed_at, 3, "shell three is the resumption");
        assert!(resumption.quiet_shell < resumption.resumed_at);
        assert_eq!(resumption.classes_before, 2, "A and C are still one class at shell two");
        assert_eq!(resumption.classes_after, 3, "shell three separates them");

        // The witness itself: two occurrences of `c` that shell 3 pulled apart. Read them back out
        // of the corpus and confirm they agree at shell 2 and differ at shell 3 -- the exact
        // property "a quiet shell is not saturation" asserts, checked on the named pair.
        let (one, other) = resumption.separated;
        assert_ne!(one, other);
        assert_eq!(
            shell(&census, &atlas, one.0, one.1, resumption.quiet_shell),
            shell(&census, &atlas, other.0, other.1, resumption.quiet_shell),
            "the witnesses must be INDISTINGUISHABLE at the quiet shell, or it was not quiet"
        );
        assert_ne!(
            shell(&census, &atlas, one.0, one.1, resumption.resumed_at),
            shell(&census, &atlas, other.0, other.1, resumption.resumed_at),
            "the witnesses must SEPARATE at the resumption, or it did not resume"
        );

        assert!(derived.stalled());
        assert!(derived.exhausted, "the stall does not prevent exhaustion");

        // The unsound loop, written out, so the difference is exhibited rather than asserted: stop
        // at the first shell that splits nothing and it answers 1 where the truth is 3.
        let mut classes: Vec<Vec<(u32, u32)>> = vec![census.sites(surface).to_vec()];
        let mut halted_at = 0usize;
        for depth in 1..=derived.bound {
            let mut refined: Vec<Vec<(u32, u32)>> = Vec::new();
            let mut split = false;
            for class in classes.drain(..) {
                let mut grouped: BTreeMap<_, Vec<(u32, u32)>> = BTreeMap::new();
                for (whole, position) in class {
                    grouped
                        .entry(shell(&census, &atlas, whole, position, depth))
                        .or_default()
                        .push((whole, position));
                }
                if grouped.len() > 1 {
                    split = true;
                }
                refined.extend(grouped.into_values());
            }
            classes = refined;
            if !split {
                halted_at = depth - 1;
                break;
            }
        }
        assert_eq!(halted_at, 1, "the unsound loop halts on the quiet shell");
        assert_ne!(
            halted_at, derived.horizon,
            "if these agree the fixture does not separate the two loops"
        );
        // The retained witness and the independently written unsound loop must name the SAME shell:
        // the loop halts one shell before the first interior quiet one, by its own `depth - 1`.
        assert_eq!(
            halted_at + 1,
            resumption.quiet_shell,
            "the witness must be the shell the second implementation actually stopped at"
        );

        // **The negative arm, on the same material.** A quantity that were non-zero everywhere
        // would grade nothing, so the fixture is required to carry a surface that never stalls.
        let mut stalling = 0usize;
        let mut still = 0usize;
        for surface in census.word_surfaces() {
            let reading = saturation_horizon(&census, &atlas, surface);
            if reading.stalled() {
                stalling += 1;
            } else {
                still += 1;
            }
            assert_eq!(
                reading.stalled(),
                reading.first_resumption.is_some(),
                "the count and its witness must agree at {surface:?}: {reading:?}"
            );
            if let Some(resumption) = reading.first_resumption {
                assert!(resumption.quiet_shell < resumption.resumed_at);
                assert!(resumption.classes_before < resumption.classes_after);
                assert!(resumption.resumed_at <= reading.horizon);
            }
        }
        assert!(
            stalling > 0 && still > 0,
            "the fixture must separate stalling from non-stalling surfaces: \
             {stalling} stall, {still} do not"
        );
        let _ = fs::remove_dir_all(&root);
    }

    /// **The surface's ceiling is its own, and one unrelated long whole may not lengthen it.**
    ///
    /// `CLAUDE.md` §8 — *when the declared material cannot exercise a law, add a declared control
    /// that does.* The declared corpus cannot grade this repair: every one of its 29,587 surfaces
    /// exhausts to singletons long before any ceiling, so the ceiling never binds and the cost is
    /// identical either way. This fixture builds the case where it does bind — two byte-identical
    /// wholes, whose two occurrences of `c` are indistinguishable to this receiver at **every**
    /// depth, so the propagation runs to the ceiling and the ceiling is the entire cost.
    ///
    /// The frame is then moved, which is the only way an invariant is visible: an unrelated long
    /// whole is added that never writes `c`. Under the corpus-wide ceiling the identical material
    /// costs strictly more; under the surface's own ceiling it costs the same.
    #[test]
    fn one_unrelated_long_whole_may_not_lengthen_another_surfaces_cone() {
        let mut long = String::new();
        for n in 0..400 {
            long.push_str(&format!("w{n} "));
        }

        let build = |name: &str, filler: &str| {
            let root = scratch(name);
            // Two byte-identical wholes: `c` sits at the same place in both, so no shell ever
            // separates the two occurrences and the propagation cannot exhaust.
            write(&root, "papers/source/mathematics/a.typ", "k a c b k\n");
            write(&root, "canon/a.md", "k a c b k\n");
            write(&root, "research/records/a.md", filler);
            write(&root, "reference/pureholonics-seed/a.md", "filler only\n");
            root
        };

        let near = build("surface-local-ceiling-near", "q r s\n");
        let far = build("surface-local-ceiling-far", &format!("{long}\n"));

        let read_one = |root: &std::path::Path| {
            let census = CorpusCensus::read(root).unwrap();
            let atlas = atlas(&census);
            let surface = census.lookup("c").expect("the fixture writes it");
            (
                material_horizon_bound(&census),
                saturation_horizon(&census, &atlas, surface),
            )
        };
        let (near_corpus_bound, near_reading) = read_one(&near);
        let (far_corpus_bound, far_reading) = read_one(&far);

        // The frame genuinely moved: the corpus ceiling is far larger in the second reading.
        assert!(
            far_corpus_bound > near_corpus_bound,
            "the added whole must move the corpus ceiling, or this control grades nothing: \
             {near_corpus_bound} -> {far_corpus_bound}"
        );
        // The law binds here: neither reading exhausts, so the ceiling IS the cost.
        assert!(!near_reading.exhausted && !far_reading.exhausted);
        assert_eq!(near_reading.horizon, 0, "the two occurrences never separate");
        assert_eq!(near_reading.classes, 1);

        // And the invariant: the surface's own ceiling, its shells, and its exact work do not move.
        assert_eq!(near_reading.bound, far_reading.bound);
        assert_eq!(near_reading.shells, far_reading.shells);
        assert_eq!(near_reading.active_total, far_reading.active_total);
        assert_eq!(near_reading.classes, far_reading.classes);

        // What the corpus-wide ceiling would have cost on the SAME material, stated as the number
        // the repair removed rather than as an impression.
        let under_corpus_ceiling = far_corpus_bound * census_sites(&far, "c");
        assert!(
            under_corpus_ceiling > far_reading.active_total * 8,
            "the control must exhibit a wide gap or it is not grading a cost law: \
             {under_corpus_ceiling} against {}",
            far_reading.active_total
        );

        let _ = fs::remove_dir_all(&near);
        let _ = fs::remove_dir_all(&far);
    }

    /// The occurrence count of one surface in a corpus at `root`. Used by the ceiling control to
    /// state what the corpus-wide ceiling would have cost.
    fn census_sites(root: &std::path::Path, word: &str) -> usize {
        let census = CorpusCensus::read(root).unwrap();
        let surface = census.lookup(word).expect("the fixture writes it");
        census.sites(surface).len()
    }

    /// The derivation has a non-trivial orbit: the material must disagree with the authored `1`
    /// somewhere, or replacing the constant changed nothing and the excision is bookkeeping.
    #[test]
    fn the_derived_horizon_moves_against_the_level_it_replaces() {
        let root = declared_corpus("horizon-orbit");
        let census = CorpusCensus::read(&root).unwrap();
        let atlas = atlas(&census);
        let horizons = saturation_horizons(&census, &atlas);
        assert!(!horizons.is_empty());

        let moved: Vec<_> = horizons.values().filter(|r| !r.one_was_enough()).collect();
        assert!(
            !moved.is_empty(),
            "no surface needs more than one shell, so this fixture cannot grade the excision"
        );
        for reading in &moved {
            assert!(reading.horizon > 1);
            assert!(reading.unreached_at_one() > 0);
        }

        // Surfaces genuinely differ in reach: one horizon over the corpus is a summary, and the
        // organ returns the population that forced it rather than the number alone.
        let (deepest, forcing) = corpus_horizon(&horizons);
        assert!(deepest > 1);
        assert!(!forcing.is_empty());
        assert!(
            forcing.len() < horizons.len(),
            "if every surface forces the corpus horizon the reading carries no information"
        );
        let _ = fs::remove_dir_all(&root);
    }

    #[test]
    fn the_conduct_axis_holds_together_what_typography_splits() {
        let root = typography_corpus("typography");
        let census = CorpusCensus::read(&root).unwrap();
        let atlas = ConductAtlas::found(&census, 1);
        let alpha = census.lookup("alpha").expect("the fixture writes it");
        let reading = separation_reading(&census, &atlas, alpha, 1);
        let invariance = reading.conduct_invariance();

        assert_eq!(reading.distinct_windows, 3, "three constructions");
        assert_eq!(
            invariance.verdict,
            ConductVerdict::ConductInvariant {
                windows: 3,
                collapsing: ReceiverFamily::of([ReceiverAxis::Conduct]),
            },
            "the conduct axis alone holds the population"
        );

        // The control: NO nonempty orthographic family collapses it, so the collapse is the fourth
        // axis's and could not have come from the three.
        for family in ReceiverFamily::ORTHOGRAPHIC.subsets() {
            if family.is_empty() {
                continue;
            }
            assert!(
                reading.family_blocks(family) > 1,
                "the orthographic family {family} must NOT collapse `alpha`, or the fixture proves \
                 nothing about the fourth axis"
            );
        }
        assert_eq!(reading.family_blocks(ReceiverFamily::of([ReceiverAxis::Conduct])), 1);
        assert!(invariance.separations_withstood > BigUint::from(0u32));

        // The six neighbours read alike under conduct and differ under the panel that failed.
        let neighbours = ["one", "LONGWORD", "gg", "two", "four", "six"];
        let tokens: BTreeSet<u64> = neighbours
            .iter()
            .map(|name| atlas.token(census.lookup(name).expect("written")))
            .collect();
        assert_eq!(tokens.len(), 1, "all six were used in one construction each");
        let signatures: BTreeSet<(u64, u64, u64)> = neighbours
            .iter()
            .map(|name| census.signature(census.lookup(name).expect("written")))
            .collect();
        assert!(
            signatures.len() > 1,
            "the neighbours must differ orthographically or nothing was held together"
        );

        // **The distinguishing word.** Move ONE surface's conduct token and the collapse goes; the
        // verdict is a consequence of what the axis read and not of the axis existing.
        let long = census.lookup("LONGWORD").expect("written");
        let mut moved: Vec<u64> = atlas.tokens().to_vec();
        moved[long.0 as usize] += 1;
        let counterfactual = ConductAtlas::declaring(atlas.founding_horizon(), moved);
        let after = separation_reading(&census, &counterfactual, alpha, 1);
        assert_eq!(
            after.family_blocks(ReceiverFamily::of([ReceiverAxis::Conduct])),
            2,
            "one moved reading must break the collapse"
        );
        assert!(!after.conduct_invariance().verdict.is_conduct_invariant());

        // And the independent implementation grades the claim at every declared sub-family.
        for family in ReceiverFamily::FULL.subsets() {
            let check = cross_check_family(&census, &atlas, alpha, 1, family, TEST_CAPACITY)
                .expect("the fixture is inside the declared capacity");
            assert!(check.agrees(), "family {family}: {check:?}");
        }
        let _ = fs::remove_dir_all(&root);
    }
}

// -------------------------------------------------------------------------------------------------
// The separation refinement, expressed in the SHARED quotient
// -------------------------------------------------------------------------------------------------
//
// **This organ has no device path of its own, and that is the point.** `saturation_horizon`'s
// refinement is a quotient by an exact key, which is one law with two charts —
// `cuda_refine::{quotient_on_host, CudaRefineExecutor::quotient_on_device}`. What belongs to this
// organ is the KEY: what an occurrence carries at causal shell `k`. Everything after that is shared
// with every other organ that has a front.
//
// Brandon, 2026-08-10, on the alternative: *"why the fuck do you think you have a choice about
// 'paths'… why is this not ontologically integrated -> encapsulation and factored in the codebase."*
// A device path per organ is the cabinet-of-organs failure one level down.

/// **This organ's material: the exact key an occurrence carries at causal shell `depth`.**
///
/// Two occurrences agree at this shell exactly when they agree at `−depth` and at `+depth`, so the
/// key is the pair of reading identities, packed. `identity_of` supplies a dense identity per
/// surface; identity `0` is the terminus and no reading may take it.
pub fn shell_key(
    census: &CorpusCensus,
    identity_of: &[u32],
    whole: u32,
    position: u32,
    depth: usize,
) -> u64 {
    let stream = &census.wholes()[whole as usize].stream;
    let at = |offset: i64| -> u32 {
        let site = position as i64 + offset;
        if site < 0 || site >= stream.len() as i64 {
            0
        } else {
            identity_of
                .get(stream[site as usize].0 as usize)
                .copied()
                .unwrap_or(0)
        }
    };
    (u64::from(at(-(depth as i64))) << 32) | u64::from(at(depth as i64))
}

/// One surface's shell keys, in the census's own site order — what a chart is handed.
pub fn shell_keys_of(
    census: &CorpusCensus,
    identity_of: &[u32],
    surface: SurfaceId,
    depth: usize,
) -> Vec<u64> {
    census
        .sites(surface)
        .iter()
        .map(|(whole, position)| shell_key(census, identity_of, *whole, *position, depth))
        .collect()
}

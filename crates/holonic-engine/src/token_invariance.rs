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
//! ## The two apertures, and the one bound
//!
//! The **horizon** is a receiver coordinate, not a knob: every reading carries the horizon it was
//! taken at, and [`iron_at`] is monotone — iron at horizon `h+1` is contained in iron at horizon
//! `h`, because a longer word can only separate more. The driver takes both declared horizons and
//! asserts the containment.
//!
//! The one bound is [`WINDOW_APERTURE`]: at most that many *distinct* radius-`h` windows are
//! presented to the compression organ per surface, in corpus order, and
//! [`SeparationReading::windows_withheld`] names the residual. **The bound provably cannot
//! manufacture an iron verdict**, because a surface is iron exactly when it has one distinct window,
//! and one window is never withheld. It bounds only how many separating words are exhibited.
//!
//! ## Two independent implementations of one partition
//!
//! `CLAUDE.md` §8: where an independent implementation exists, state both. The distinct-window
//! census computed here and the Nerode refinement computed by `receiver_exact_compression` are two
//! implementations of the same partition — the window is the complete information a word of length
//! at most `h` can reach — and [`SeparationReading::parity`] is their agreement. It is asserted, not
//! assumed.

use std::collections::{BTreeMap, BTreeSet};

use num_bigint::BigUint;

use crate::corpus_census::{CorpusCensus, Kind, SurfaceId, weight_band_name};
use crate::receiver_exact_compression::{
    AblatedSystem, CollapsedPair, InputId, ItemId, ObservedSystem, Observation, ReceiverId, compress,
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

/// The declared window aperture: at most this many distinct windows per surface reach the
/// compression organ. See the module header — it cannot manufacture an iron verdict.
pub const WINDOW_APERTURE: usize = 64;

/// The declared cap on separations retained per surface. The organ computes every one; this bounds
/// what the reading carries so a whole-corpus sweep fits in memory.
/// [`SeparationReading::separations_found`] always reports the true total.
pub const SEPARATION_EXHIBIT: usize = 512;

/// The complete information a word of length at most `horizon` can reach from one occurrence:
/// the receiver signature at every offset in `-horizon..=horizon` except `0`, with `None` where the
/// whole ends.
pub type Window = Vec<Option<(u64, u64, u64)>>;

/// The window of the occurrence at `position` in `whole`.
pub fn window(census: &CorpusCensus, whole: u32, position: u32, horizon: usize) -> Window {
    let stream = &census.wholes()[whole as usize].stream;
    let mut reading = Vec::with_capacity(2 * horizon);
    for offset in -(horizon as i64)..=(horizon as i64) {
        if offset == 0 {
            continue;
        }
        let index = position as i64 + offset;
        if index < 0 || index >= stream.len() as i64 {
            reading.push(None);
        } else {
            reading.push(Some(census.signature(stream[index as usize])));
        }
    }
    reading
}

/// One surface's occurrence population, presented as a system the compression organ can refine.
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
        let (kind, weight, density) = self.census.signature(surface);
        Observation(match ReceiverAxis::from_id(receiver) {
            Some(ReceiverAxis::Kind) => kind,
            Some(ReceiverAxis::Weight) => weight,
            Some(ReceiverAxis::Density) => density,
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

/// One exhibited separation: two occurrences the one-shot reading held together, the shortest word
/// that separates them, and what was seen there.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Separation {
    pub left_site: (u32, u32),
    pub right_site: (u32, u32),
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

/// What the separation reading returns for one surface.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Verdict {
    /// One conduct block. The corpus never used this surface in a context the family can tell apart.
    Iron,
    /// More than one conduct block, with the shortest separating word at depth `first_depth`.
    Separated { first_depth: usize },
    /// The presented population did not separate but the aperture withheld windows. **Unreachable by
    /// construction** — retained as a typed refusal rather than as an assumption.
    ApertureOpen,
}

impl Verdict {
    pub fn is_iron(self) -> bool {
        matches!(self, Verdict::Iron)
    }
}

/// One surface's separation reading at one declared horizon.
#[derive(Clone, Debug)]
pub struct SeparationReading {
    pub surface: SurfaceId,
    pub horizon: usize,
    pub occurrences: BigUint,
    /// The true number of distinct radius-`horizon` windows, over **every** occurrence.
    pub distinct_windows: usize,
    pub windows_presented: usize,
    /// The named residual of the declared aperture.
    pub windows_withheld: usize,
    pub one_shot_blocks: usize,
    pub conduct_blocks: usize,
    pub refinement_rounds: usize,
    pub verdict: Verdict,
    /// Every separation the organ found among the presented roots, up to [`SEPARATION_EXHIBIT`].
    pub separations: Vec<Separation>,
    pub separations_found: usize,
    /// How many separated pairs the organ resolved by a terminus rather than by a receiver.
    pub terminus_separations: usize,
}

impl SeparationReading {
    /// The two independent implementations agree: the distinct-window census over the presented
    /// roots is the Nerode refinement the organ computed.
    pub fn parity(&self) -> bool {
        self.conduct_blocks == self.windows_presented
    }

    /// `C(N,2)` — the number of occurrence pairs the verdict ranged over, exact.
    ///
    /// **`CLAUDE.md` §8's tautology rule, made a number the reading carries.** A receipt that could
    /// not have come out otherwise carries no evidence, and a surface occurring **once** is
    /// unseparated by arithmetic rather than by the corpus's usage: there is no pair for conduct to
    /// separate. This is the exact count of the non-separations an iron verdict actually survived,
    /// and it is `0` exactly where the verdict is vacuous.
    pub fn survived_pairs(&self) -> BigUint {
        let occurrences = self.occurrences.clone();
        if occurrences < BigUint::from(2u32) {
            return BigUint::from(0u32);
        }
        let one = BigUint::from(1u32);
        occurrences.clone() * (occurrences - &one) / BigUint::from(2u32)
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
}

/// Read one surface's occurrence population at one declared horizon.
pub fn separation_reading(
    census: &CorpusCensus,
    surface: SurfaceId,
    horizon: usize,
) -> SeparationReading {
    let sites = census.sites(surface);
    let mut seen: BTreeMap<Window, ()> = BTreeMap::new();
    let mut roots: Vec<(u32, u32)> = Vec::new();
    let mut distinct = 0usize;
    for (whole, position) in sites {
        let reading = window(census, *whole, *position, horizon);
        if seen.insert(reading, ()).is_none() {
            distinct += 1;
            if roots.len() < WINDOW_APERTURE {
                roots.push((*whole, *position));
            }
        }
    }

    let presented = roots.len();
    let system = OccurrenceSystem::new(census, roots, horizon);
    let compression = compress(&system);

    let root_items: BTreeSet<ItemId> = (0..presented).map(|root| system.root_item(root)).collect();
    let one_shot_blocks = block_count(&compression.one_shot.blocks, &root_items);
    let conduct_blocks = block_count(&compression.conduct.blocks, &root_items);

    let mut separations = Vec::new();
    let mut found = 0usize;
    let mut terminus = 0usize;
    let mut first_depth: Option<usize> = None;
    for pair in &compression.collapsed {
        if !root_items.contains(&pair.left) || !root_items.contains(&pair.right) {
            continue;
        }
        found += 1;
        if pair.separated_by_terminus {
            terminus += 1;
        }
        let depth = pair.distinguishing_word.len();
        first_depth = Some(match first_depth {
            Some(current) => current.min(depth),
            None => depth,
        });
        if separations.len() < SEPARATION_EXHIBIT {
            separations.push(translate(&system, pair));
        }
    }

    let verdict = if conduct_blocks <= 1 {
        if presented < distinct {
            Verdict::ApertureOpen
        } else {
            Verdict::Iron
        }
    } else {
        Verdict::Separated {
            first_depth: first_depth.unwrap_or(0),
        }
    };

    SeparationReading {
        surface,
        horizon,
        occurrences: BigUint::from(census.occurrences(surface)),
        distinct_windows: distinct,
        windows_presented: presented,
        windows_withheld: distinct.saturating_sub(presented),
        one_shot_blocks,
        conduct_blocks,
        refinement_rounds: compression.rounds,
        verdict,
        separations,
        separations_found: found,
        terminus_separations: terminus,
    }
}

fn block_count(blocks: &[BTreeSet<ItemId>], roots: &BTreeSet<ItemId>) -> usize {
    blocks
        .iter()
        .filter(|block| block.iter().any(|item| roots.contains(item)))
        .count()
}

fn translate(system: &OccurrenceSystem<'_>, pair: &CollapsedPair) -> Separation {
    let word: Vec<Step> = pair
        .distinguishing_word
        .iter()
        .filter_map(|input| Step::from_input(*input))
        .collect();
    let offset = OccurrenceSystem::word_offset(&pair.distinguishing_word);
    let landing = |item: ItemId| -> Option<SurfaceId> {
        let mut current = item;
        for input in &pair.distinguishing_word {
            current = system.successor(current, *input)?;
        }
        system.surface_at(current)
    };
    let left_surface = landing(pair.left);
    let right_surface = landing(pair.right);
    let (axis, readings) = match pair.witness {
        Some((receiver, left, right)) => (ReceiverAxis::from_id(receiver), Some((left.0, right.0))),
        None => (None, None),
    };
    Separation {
        left_site: system.site(pair.left).unwrap_or((u32::MAX, u32::MAX)),
        right_site: system.site(pair.right).unwrap_or((u32::MAX, u32::MAX)),
        word,
        offset,
        left_surface,
        right_surface,
        axis,
        readings,
        by_terminus: pair.separated_by_terminus,
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

/// What one axis's removal costs a surface's reading. `AblatedSystem` is the organ's own ablation,
/// and H.0016's transformations clause guarantees removal can only **coarsen**.
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

/// Ablate each declared axis in turn on one surface's presented population.
pub fn ablation_profile(
    census: &CorpusCensus,
    surface: SurfaceId,
    horizon: usize,
) -> Vec<AblationReading> {
    let sites = census.sites(surface);
    let mut seen: BTreeSet<Window> = BTreeSet::new();
    let mut roots: Vec<(u32, u32)> = Vec::new();
    for (whole, position) in sites {
        let reading = window(census, *whole, *position, horizon);
        if seen.insert(reading) && roots.len() < WINDOW_APERTURE {
            roots.push((*whole, *position));
        }
    }
    let presented = roots.len();
    let system = OccurrenceSystem::new(census, roots, horizon);
    let root_items: BTreeSet<ItemId> = (0..presented).map(|root| system.root_item(root)).collect();
    let full = compress(&system);
    let with = block_count(&full.conduct.blocks, &root_items);
    ReceiverAxis::DECLARED
        .into_iter()
        .map(|axis| {
            let ablated = AblatedSystem {
                inner: &system,
                without: axis.id(),
            };
            let reduced = compress(&ablated);
            AblationReading {
                axis,
                blocks_with: with,
                blocks_without: block_count(&reduced.conduct.blocks, &root_items),
            }
        })
        .collect()
}

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
        assert_eq!(iron.conduct_blocks, 1);
        assert_eq!(iron.verdict, Verdict::Iron);
        assert!(iron.parity(), "the window census and the Nerode refinement must agree");

        let fuzzy = separation_reading(&census, set, 1);
        assert!(fuzzy.distinct_windows > 1, "several constructions, several windows");
        assert!(matches!(fuzzy.verdict, Verdict::Separated { .. }));
        assert!(fuzzy.parity());
        assert!(
            fuzzy.separations_found > 0,
            "a separated surface must exhibit at least one separating word"
        );
        assert!(
            fuzzy.separations.iter().all(|separation| !separation.word.is_empty()),
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

    /// The window census and the organ's Nerode refinement are two implementations of one
    /// partition, over **every** surface at both declared horizons.
    #[test]
    fn the_window_census_and_the_nerode_refinement_agree_on_every_surface() {
        let root = declared_corpus("parity");
        let census = CorpusCensus::read(&root).unwrap();
        for horizon in [1usize, 2] {
            for (surface, reading) in sweep(&census, horizon) {
                assert!(
                    reading.parity(),
                    "horizon {horizon}, {:?}: {} presented windows vs {} conduct blocks",
                    census.surface(surface),
                    reading.windows_presented,
                    reading.conduct_blocks
                );
            }
        }
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
                .filter(|other| match other {
                    ReceiverAxis::Kind => left.0 != right.0,
                    ReceiverAxis::Weight => left.1 != right.1,
                    ReceiverAxis::Density => left.2 != right.2,
                })
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

    /// Removing a receiver may only coarsen — H.0016's transformations clause, on real material.
    #[test]
    fn ablating_an_axis_never_refines_the_reading() {
        let root = declared_corpus("ablation");
        let census = CorpusCensus::read(&root).unwrap();
        let set = census.lookup("set").unwrap();
        let profile = ablation_profile(&census, set, 1);
        assert_eq!(profile.len(), 3);
        for reading in &profile {
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

    /// The declared aperture cannot manufacture an iron verdict: a surface is iron exactly when it
    /// has one distinct window, and one window is never withheld.
    #[test]
    fn the_declared_aperture_cannot_manufacture_an_iron_verdict() {
        let root = declared_corpus("aperture");
        let census = CorpusCensus::read(&root).unwrap();
        for horizon in [1usize, 2] {
            for reading in sweep(&census, horizon).values() {
                if reading.verdict.is_iron() {
                    assert_eq!(reading.distinct_windows, 1);
                    assert_eq!(reading.windows_withheld, 0);
                }
                assert_ne!(
                    reading.verdict,
                    Verdict::ApertureOpen,
                    "the aperture-open arm is unreachable by construction"
                );
            }
        }
        let _ = fs::remove_dir_all(&root);
    }
}

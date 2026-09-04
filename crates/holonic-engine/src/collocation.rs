//! Coherence is collocation over time: two things relate iff presented together, within one source.
//!
//! ## The law this organ owns
//!
//! `archive/reference/holobrochos-a07ff376/src/soma/FORMULA.md:298`, ratified and until now with no
//! implementation anywhere in either tree:
//!
//! > *"ONE law: **coherence is collocation over time** — two things relate iff presented together,
//! > across time. **Faces grow from collocation**; mass folds the topology; currents path the
//! > geodesics and are transformed at the dense regions; **the regions are emergent, never
//! > designed**."*
//!
//! and `:615`, *"coherence is collocation at EVERY grain"*, and `:1278`'s **referent law** —
//! *"association only through a REAL cross-sense invariant of ONE SOURCE (the referent law — random
//! pairing is the null-bind)"*.
//!
//! ## What is built, in the law's own words
//!
//! ```text
//!   presented together   a REGION: one aperture of one SOURCE, carrying a set of items
//!   faces grow           the simplicial complex whose faces are exactly the co-presented subsets
//!   the regions          the FACETS and the CLOSED SETS -- derived, never declared
//!   over time            an item's EXTENT: the regions that presented it, by name
//!   two things relate    a FORCED PASSAGE a => b: every region presenting `a` presented `b`
//!   random pairing       the NULL-BIND: the same items, the same counts, the pairing destroyed
//! ```
//!
//! A face is not asserted and not looked up. `ext(A)` is the regions carrying all of `A`; `int(X)`
//! is the items every region of `X` carries; a face of the complex is a set that some region
//! carried, and the **closure** `A'' = int(ext(A))` is what presenting `A` forces. The closure
//! operator's fixed points are the closed sets, and they are the emergent regions: nothing here
//! declares a cluster, a region count, or a membership.
//!
//! ## The atom is not empty
//!
//! [`crate::name_elaboration`] walks **recruitment** and an atom recruits nothing, so its
//! elaboration is `{}`. An atom still **collocates**. `apply` declares nothing and is declared by
//! nothing, and its face at the artifact grain is `{assumption, exactCarrier, Prop}` — founded by
//! co-presentation alone, with no declaration in the deposit and no richer material.
//!
//! ## Every count here measures; none governs
//!
//! An extent is `Π`, the lived construction: counted, returned whole, and never a filter.
//! [`CoPresentation::forced_passages`] returns **every** forced passage the material carries, each
//! carrying the regions that refused its target **by name**, and nothing is ranked or dropped. The
//! one probability in the organ is [`ForcedPassage::quotient`], and it is `Q` in the precise sense
//! `CLAUDE.md` §13 rule 2 requires — *a declared quotient over what the receiver does not carry*:
//!
//! ```text
//!             C(|ext(b)|, |ext(a)|)         the placements of a's extent that land inside b's
//!   Q(a=>b) = ---------------------         ----------------------------------------------------
//!               C(n, |ext(a)|)              all placements of an extent of that size among n
//! ```
//!
//! It is an exact `Rat` over `BigUint` binomials, it is reported on every passage and consulted by
//! nothing, and **its loss is exhibitable**: what `Q` quotients away is the pairing, and
//! [`CollocationDeposit::null_bind`] realizes that quotient by destroying the pairing while holding
//! both marginals bit-exact. The two instruments are independent and they agree — see the driver.
//!
//! ## The null-bind is a control, never production law
//!
//! [`NullBind`] re-pairs the incidence by **double-edge swaps under a declared integer schedule**.
//! There is no random number generator: the schedule is a list of strides and the traversal is
//! `j -> (j + stride) mod m` over the canonically ordered incidence. A swap is applied only when it
//! is legal, so **every region keeps its exact size and every item keeps its exact count** — the
//! construction refuses itself with [`CollocationRefusal::NullBindMovedMarginals`] if either moves.
//! It is an exterior falsifier for this organ's own returns and is offered as no part of any law.
//!
//! ## No float
//!
//! Extents and populations are `usize`; the complex's coefficients are `ComparativeMultiplicity`
//! over `BigUint`; `Q` is `relational_geometry::Rat`. Nothing in this module constructs, compares,
//! or stores an IEEE scalar.

use std::collections::{BTreeMap, BTreeSet};

use num_bigint::{BigInt, BigUint};
use num_traits::One;
use relational_geometry::Rat;
use serde::{Deserialize, Serialize};

use crate::algebraic::{
    CausalAlgebraicError, CausalCellId, CausalChain, ComparativeMultiplicity, GradedCausalComplex,
};
use crate::causal::EventId;

/// The separator written between the items of a face when it is named as a cell. A Lean identifier
/// cannot carry it, so a face name can never collide with an item name.
pub const FACE_ITEM_SEPARATOR: &str = " \u{00b7} ";

// -------------------------------------------------------------------------------------------------
// The deposit
// -------------------------------------------------------------------------------------------------

/// One co-presentation: the items one aperture of one source presented together.
///
/// `source` is the referent law's *one source*. Two items never relate here because they appeared
/// in two regions of two sources; they relate because **one** region presented both.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct Presentation {
    /// The one source this region belongs to. Every relation this region founds is confined to it.
    pub source: String,
    /// What this region is, at the grain it was carved at. Unique across the deposit.
    pub region: String,
    /// What was presented together. A set: an item presented twice in one region was presented
    /// together with itself, which is not a relation.
    pub items: BTreeSet<String>,
}

/// A population of co-presentations at one declared grain.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CollocationDeposit {
    /// What "presented together" means for this deposit. Stated, never inferred.
    grain: String,
    presentations: Vec<Presentation>,
}

impl CollocationDeposit {
    /// Found a deposit at a declared grain.
    ///
    /// The regions are stored in the order given; that order is the deposit's only interior
    /// sequence and it is what the null-bind's declared strides walk. A region carrying no item
    /// presents nothing and is refused rather than silently skipped.
    pub fn found(
        grain: impl Into<String>,
        presentations: Vec<Presentation>,
    ) -> Result<Self, CollocationRefusal> {
        if presentations.is_empty() {
            return Err(CollocationRefusal::EmptyDeposit);
        }
        let mut seen = BTreeSet::new();
        for presentation in &presentations {
            if presentation.items.is_empty() {
                return Err(CollocationRefusal::RegionPresentsNothing {
                    region: presentation.region.clone(),
                });
            }
            if !seen.insert(presentation.region.clone()) {
                return Err(CollocationRefusal::RegionNamedTwice {
                    region: presentation.region.clone(),
                });
            }
        }
        Ok(Self {
            grain: grain.into(),
            presentations,
        })
    }

    pub fn grain(&self) -> &str {
        &self.grain
    }

    pub fn presentations(&self) -> &[Presentation] {
        &self.presentations
    }

    pub fn regions(&self) -> usize {
        self.presentations.len()
    }

    /// Every source the deposit carries, in name order.
    pub fn sources(&self) -> BTreeSet<&str> {
        self.presentations
            .iter()
            .map(|carried| carried.source.as_str())
            .collect()
    }

    /// Every item any region presented, in name order. Nothing is bounded away.
    pub fn items(&self) -> BTreeSet<&str> {
        self.presentations
            .iter()
            .flat_map(|carried| carried.items.iter().map(String::as_str))
            .collect()
    }

    /// The canonically ordered incidence: one `(region ordinal, item)` per presented item.
    pub fn incidence(&self) -> Vec<(usize, &str)> {
        let mut out = Vec::new();
        for (ordinal, presentation) in self.presentations.iter().enumerate() {
            for item in &presentation.items {
                out.push((ordinal, item.as_str()));
            }
        }
        out
    }

    /// The exact per-region sizes and per-item counts. Both are what a null-bind must not move.
    pub fn marginals(&self) -> (Vec<usize>, BTreeMap<&str, usize>) {
        let sizes = self
            .presentations
            .iter()
            .map(|carried| carried.items.len())
            .collect();
        let mut counts: BTreeMap<&str, usize> = BTreeMap::new();
        for presentation in &self.presentations {
            for item in &presentation.items {
                *counts.entry(item.as_str()).or_insert(0) += 1;
            }
        }
        (sizes, counts)
    }

    /// **THE NULL-BIND.** The same items, the same counts, the pairing destroyed.
    ///
    /// Double-edge swaps over the canonically ordered incidence under a declared stride schedule.
    /// For each stride `s` and each incidence position `j`, the pair `(j, (j + s) mod m)` is offered
    /// and the swap is applied when it is legal — the two incidences must sit in different regions,
    /// carry different items, and neither destination pair may already be present. An illegal offer
    /// is **refused and counted**, never worked around.
    ///
    /// Both marginals are preserved by construction and verified before returning; a violation is a
    /// refusal, not a warning.
    pub fn null_bind(
        &self,
        schedule: &[usize],
        scope: NullBindScope,
    ) -> Result<NullBind, CollocationRefusal> {
        if schedule.is_empty() {
            return Err(CollocationRefusal::EmptyNullBindSchedule);
        }
        let mut incidence: Vec<(usize, String)> = self
            .incidence()
            .into_iter()
            .map(|(region, item)| (region, item.to_owned()))
            .collect();
        let span = incidence.len();
        let mut present: BTreeSet<(usize, String)> = incidence.iter().cloned().collect();
        let source_of: Vec<&str> = self
            .presentations
            .iter()
            .map(|carried| carried.source.as_str())
            .collect();

        let mut applied = 0usize;
        let mut refused = 0usize;
        for stride in schedule {
            for left in 0..span {
                let right = (left + stride) % span;
                if left == right {
                    refused += 1;
                    continue;
                }
                let (left_region, left_item) = incidence[left].clone();
                let (right_region, right_item) = incidence[right].clone();
                if left_region == right_region || left_item == right_item {
                    refused += 1;
                    continue;
                }
                if scope == NullBindScope::WithinSource
                    && source_of[left_region] != source_of[right_region]
                {
                    refused += 1;
                    continue;
                }
                if present.contains(&(left_region, right_item.clone()))
                    || present.contains(&(right_region, left_item.clone()))
                {
                    refused += 1;
                    continue;
                }
                present.remove(&(left_region, left_item.clone()));
                present.remove(&(right_region, right_item.clone()));
                present.insert((left_region, right_item.clone()));
                present.insert((right_region, left_item.clone()));
                incidence[left] = (left_region, right_item);
                incidence[right] = (right_region, left_item);
                applied += 1;
            }
        }

        let mut rebuilt: Vec<BTreeSet<String>> = vec![BTreeSet::new(); self.presentations.len()];
        for (region, item) in &incidence {
            rebuilt[*region].insert(item.clone());
        }
        let presentations: Vec<Presentation> = self
            .presentations
            .iter()
            .zip(rebuilt)
            .map(|(original, items)| Presentation {
                source: original.source.clone(),
                region: original.region.clone(),
                items,
            })
            .collect();
        let shuffled = Self {
            grain: self.grain.clone(),
            presentations,
        };

        let (before_sizes, before_counts) = self.marginals();
        let (after_sizes, after_counts) = shuffled.marginals();
        if before_sizes != after_sizes {
            return Err(CollocationRefusal::NullBindMovedMarginals {
                what: "region sizes".to_owned(),
            });
        }
        if before_counts != after_counts {
            return Err(CollocationRefusal::NullBindMovedMarginals {
                what: "item counts".to_owned(),
            });
        }

        let regions_moved = self
            .presentations
            .iter()
            .zip(shuffled.presentations.iter())
            .filter(|(before, after)| before.items != after.items)
            .count();

        Ok(NullBind {
            schedule: schedule.to_vec(),
            scope,
            applied,
            refused,
            regions_moved,
            deposit: shuffled,
        })
    }
}

/// How far a null-bind is permitted to re-pair.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum NullBindScope {
    /// Any two regions may exchange, including across sources.
    WholeDeposit,
    /// Only regions of the same source may exchange. The **stronger** control: it destroys the
    /// pairing while leaving the referent law's *one source* structure exactly where it was, so a
    /// separation that survives it cannot be an artifact of source identity.
    WithinSource,
}

/// A realized re-pairing: the same items, the same counts, the pairing destroyed.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct NullBind {
    /// The declared stride schedule. No random number generator is involved.
    pub schedule: Vec<usize>,
    pub scope: NullBindScope,
    /// Swaps applied.
    pub applied: usize,
    /// Offers refused as illegal. Counted so the schedule's own reach is visible.
    pub refused: usize,
    /// Regions whose item set is not what it was. A null-bind that moves nothing is not a control,
    /// and this is the number that says so.
    pub regions_moved: usize,
    deposit: CollocationDeposit,
}

impl NullBind {
    pub fn deposit(&self) -> &CollocationDeposit {
        &self.deposit
    }
}

// -------------------------------------------------------------------------------------------------
// The reading
// -------------------------------------------------------------------------------------------------

/// One forced passage, with everything that decides whether it is worth anything.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ForcedPassage {
    /// The item whose presence forces.
    pub from: String,
    /// The item its presence forces.
    pub to: String,
    /// How many regions presented `from`. `Π`, the lived construction.
    pub extent_from: usize,
    /// How many regions presented `to`.
    pub extent_to: usize,
    /// The regions that presented **neither**, by name: every region that could have carried
    /// `from` and refused `to`. An empty refusal population means `to` is universal and the
    /// passage is vacuous — the null cone, carried rather than hidden.
    pub refusing: Vec<String>,
    /// The sources in which the passage was witnessed. Two or more is a **cross-source
    /// invariant** in the referent law's sense.
    pub sources: BTreeSet<String>,
    /// `Q` — the exact share of placements of an extent of size `|ext(from)|` among the regions
    /// that would have landed inside `ext(to)` anyway. A measurement, consulted by nothing.
    pub quotient: Rat,
}

impl ForcedPassage {
    /// Whether the passage was presented more than once. *"Across time"* is the law's own phrase and
    /// one presentation is not across anything.
    pub fn across_time(&self) -> bool {
        self.extent_from >= 2
    }

    /// Whether the target is universal, in which case the passage is forced by nothing.
    pub fn is_vacuous(&self) -> bool {
        self.refusing.is_empty()
    }
}

/// What one deposit's co-presentation founds. Every item it measured is in here.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CoPresentation {
    grain: String,
    regions: usize,
    items: Vec<String>,
    region_names: Vec<String>,
    region_sources: Vec<String>,
    region_items: Vec<BTreeSet<String>>,
    extent: BTreeMap<String, BTreeSet<usize>>,
    closure: BTreeMap<String, BTreeSet<String>>,
    universal: BTreeSet<String>,
}

impl CoPresentation {
    /// Read a deposit. Nothing is consulted that the deposit does not carry.
    pub fn read(deposit: &CollocationDeposit) -> Self {
        let items: Vec<String> = deposit.items().into_iter().map(str::to_owned).collect();
        let region_items: Vec<BTreeSet<String>> = deposit
            .presentations()
            .iter()
            .map(|carried| carried.items.clone())
            .collect();
        let regions = region_items.len();

        let mut extent: BTreeMap<String, BTreeSet<usize>> = BTreeMap::new();
        for item in &items {
            let carried: BTreeSet<usize> = region_items
                .iter()
                .enumerate()
                .filter(|(_, present)| present.contains(item))
                .map(|(ordinal, _)| ordinal)
                .collect();
            extent.insert(item.clone(), carried);
        }

        let universal: BTreeSet<String> = items
            .iter()
            .filter(|item| extent[*item].len() == regions)
            .cloned()
            .collect();

        // int(ext(a)): the items every region presenting `a` also presented.
        let mut closure: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
        for item in &items {
            let mut carried: Option<BTreeSet<String>> = None;
            for ordinal in &extent[item] {
                carried = Some(match carried {
                    None => region_items[*ordinal].clone(),
                    Some(so_far) => so_far
                        .intersection(&region_items[*ordinal])
                        .cloned()
                        .collect(),
                });
            }
            closure.insert(item.clone(), carried.unwrap_or_default());
        }

        Self {
            grain: deposit.grain().to_owned(),
            regions,
            items,
            region_names: deposit
                .presentations()
                .iter()
                .map(|carried| carried.region.clone())
                .collect(),
            region_sources: deposit
                .presentations()
                .iter()
                .map(|carried| carried.source.clone())
                .collect(),
            region_items,
            extent,
            closure,
            universal,
        }
    }

    pub fn grain(&self) -> &str {
        &self.grain
    }

    pub fn regions(&self) -> usize {
        self.regions
    }

    /// Every item, in name order. The return's own aperture: what is here is everything measured.
    pub fn items(&self) -> &[String] {
        &self.items
    }

    /// The regions that presented `item`, by ordinal. `Π`, whole.
    pub fn extent(&self, item: &str) -> BTreeSet<usize> {
        self.extent.get(item).cloned().unwrap_or_default()
    }

    /// The same, by region name.
    pub fn extent_names(&self, item: &str) -> Vec<String> {
        self.extent(item)
            .into_iter()
            .map(|ordinal| self.region_names[ordinal].clone())
            .collect()
    }

    /// The sources that presented `item`.
    pub fn sources_of(&self, item: &str) -> BTreeSet<String> {
        self.extent(item)
            .into_iter()
            .map(|ordinal| self.region_sources[ordinal].clone())
            .collect()
    }

    /// `int(ext(item))` — everything presenting `item` forces, including `item` and the universals.
    pub fn closure(&self, item: &str) -> BTreeSet<String> {
        self.closure.get(item).cloned().unwrap_or_default()
    }

    /// Items present in every region. They relate to nothing because they distinguish nothing: this
    /// is the vacuous difference, and a complex carrying one is a **cone** over it and therefore
    /// contractible whatever the material does. Named so a homology reading cannot be tautological.
    pub fn universal(&self) -> &BTreeSet<String> {
        &self.universal
    }

    /// **THE FACE OF AN ITEM.** Its closure, less itself and less the vacuous.
    ///
    /// This is what co-presentation founds on an item that declares nothing and is declared by
    /// nothing. An atom's recruitment closure is empty; this is not.
    pub fn face(&self, item: &str) -> BTreeSet<String> {
        let mut carried = self.closure(item);
        carried.remove(item);
        for vacuous in &self.universal {
            carried.remove(vacuous);
        }
        carried
    }

    /// Every item's face, so a caller cannot read one without the population it sits in.
    pub fn faces(&self) -> BTreeMap<String, BTreeSet<String>> {
        self.items
            .iter()
            .map(|item| (item.clone(), self.face(item)))
            .collect()
    }

    /// The items grouped by identical face. **This is the separation.** Two items in one class are
    /// undiscriminable by collocation at this grain; the class count against the item count is what
    /// the organ returned that recruitment could not.
    pub fn separation_classes(&self) -> BTreeMap<BTreeSet<String>, BTreeSet<String>> {
        let mut classes: BTreeMap<BTreeSet<String>, BTreeSet<String>> = BTreeMap::new();
        for item in &self.items {
            classes
                .entry(self.face(item))
                .or_default()
                .insert(item.clone());
        }
        classes
    }

    /// **THE EMERGENT REGIONS, part one.** The maximal co-presented sets: a region's items that no
    /// other region's items contain. Derived from what was presented; nothing declares them.
    pub fn facets(&self) -> BTreeSet<BTreeSet<String>> {
        let distinct: BTreeSet<BTreeSet<String>> = self.region_items.iter().cloned().collect();
        distinct
            .iter()
            .filter(|candidate| {
                !distinct
                    .iter()
                    .any(|other| other.len() > candidate.len() && candidate.is_subset(other))
            })
            .cloned()
            .collect()
    }

    /// **THE EMERGENT REGIONS, part two.** The fixed points of the closure operator — every set of
    /// items that is exactly what its own extent presents. This is the Moore family the
    /// co-presentation founds, and it is the region population in the law's sense: emergent,
    /// never designed, and closed under intersection because an intersection of extents is an
    /// extent.
    pub fn closed_regions(&self) -> BTreeSet<BTreeSet<String>> {
        let full: BTreeSet<String> = self.items.iter().cloned().collect();
        let mut closed: BTreeSet<BTreeSet<String>> = BTreeSet::new();
        closed.insert(full);
        for region in &self.region_items {
            let mut grown: BTreeSet<BTreeSet<String>> = BTreeSet::new();
            for carried in &closed {
                grown.insert(carried.intersection(region).cloned().collect());
            }
            closed.extend(grown);
            closed.insert(region.clone());
        }
        closed
    }

    /// **EVERY** forced passage the material carries, each with its refusal population by name, the
    /// sources that witnessed it, and its exact `Q`. Nothing is filtered and nothing is ranked.
    pub fn forced_passages(&self) -> Vec<ForcedPassage> {
        let mut out = Vec::new();
        for from in &self.items {
            for to in self.face(from) {
                let extent_from = self.extent[from].len();
                let extent_to = self.extent[&to].len();
                let refusing: Vec<String> = (0..self.regions)
                    .filter(|ordinal| !self.region_items[*ordinal].contains(&to))
                    .map(|ordinal| self.region_names[ordinal].clone())
                    .collect();
                out.push(ForcedPassage {
                    from: from.clone(),
                    to: to.clone(),
                    extent_from,
                    extent_to,
                    refusing,
                    sources: self.sources_of(from),
                    quotient: placement_quotient(self.regions, extent_from, extent_to),
                });
            }
        }
        out
    }

    /// The reading with every universal item deleted from every region.
    ///
    /// A universal item is a cone point, so a complex carrying one is contractible by construction
    /// and its homology *could not have come out otherwise* — the tautology `CLAUDE.md` §8 says a
    /// grade must detect. This returns the link, where the homology is a fact about the material.
    /// Regions left carrying nothing are **named** rather than dropped.
    pub fn without_universal(&self) -> (Self, Vec<String>) {
        let mut kept = Vec::new();
        let mut emptied = Vec::new();
        for ordinal in 0..self.regions {
            let items: BTreeSet<String> = self.region_items[ordinal]
                .difference(&self.universal)
                .cloned()
                .collect();
            if items.is_empty() {
                emptied.push(self.region_names[ordinal].clone());
                continue;
            }
            kept.push(Presentation {
                source: self.region_sources[ordinal].clone(),
                region: self.region_names[ordinal].clone(),
                items,
            });
        }
        let deposit = CollocationDeposit {
            grain: format!("{} (universal deleted)", self.grain),
            presentations: kept,
        };
        (Self::read(&deposit), emptied)
    }

    /// Every nonempty co-presented set: the faces of the complex, as item vectors in name order.
    ///
    /// Refuses with the population it would have enumerated rather than truncating it.
    pub fn co_presented_faces(
        &self,
        enumeration_aperture: usize,
    ) -> Result<BTreeSet<Vec<String>>, CollocationRefusal> {
        let mut faces: BTreeSet<Vec<String>> = BTreeSet::new();
        for facet in self.facets() {
            let members: Vec<String> = facet.into_iter().collect();
            let span = members.len();
            if span >= usize::BITS as usize {
                return Err(CollocationRefusal::FacetTooWideToEnumerate { items: span });
            }
            for mask in 1u64..(1u64 << span) {
                let face: Vec<String> = (0..span)
                    .filter(|slot| mask & (1u64 << slot) != 0)
                    .map(|slot| members[slot].clone())
                    .collect();
                faces.insert(face);
                if faces.len() > enumeration_aperture {
                    return Err(CollocationRefusal::FacePopulationExceedsAperture {
                        declared: enumeration_aperture,
                    });
                }
            }
        }
        Ok(faces)
    }

    /// The complete f-vector of the co-presentation complex: how many co-presented sets of each
    /// size. Grade `g` counts sets of `g + 1` items.
    pub fn f_vector(
        &self,
        enumeration_aperture: usize,
    ) -> Result<BTreeMap<u32, usize>, CollocationRefusal> {
        let mut counts: BTreeMap<u32, usize> = BTreeMap::new();
        for face in self.co_presented_faces(enumeration_aperture)? {
            *counts.entry(face.len() as u32 - 1).or_insert(0) += 1;
        }
        Ok(counts)
    }

    /// **FACES GROW FROM COLLOCATION.** The co-presentation complex, in the tree's own carrier.
    ///
    /// One cell per co-presented set, at grade `|set| - 1`, with the standard simplicial boundary
    /// — the alternating sum of the sets obtained by removing one item. `found_cell` verifies
    /// `∂² = 0` on every one of them, so the carrier itself certifies that the incidence is a chain
    /// complex rather than a table of pairs.
    ///
    /// The aperture is declared and what fell outside it is returned by grade, exactly.
    pub fn complex(
        &self,
        aperture: ComplexAperture,
        enumeration_aperture: usize,
    ) -> Result<CoPresentationComplex, CollocationRefusal> {
        let all = self.co_presented_faces(enumeration_aperture)?;
        let mut complex = GradedCausalComplex::default();
        let mut cell_of: BTreeMap<Vec<String>, CausalCellId> = BTreeMap::new();
        let mut founded: BTreeMap<u32, usize> = BTreeMap::new();
        let mut outside: BTreeMap<u32, usize> = BTreeMap::new();
        let mut occasion = 0u64;

        let deepest = all.iter().map(|face| face.len()).max().unwrap_or(0);
        for size in 1..=deepest {
            let grade = size as u32 - 1;
            for face in all.iter().filter(|face| face.len() == size) {
                if !aperture.admits(grade) {
                    *outside.entry(grade).or_insert(0) += 1;
                    continue;
                }
                occasion += 1;
                let mut boundary = CausalChain::default();
                if grade > 0 {
                    for (slot, _) in face.iter().enumerate() {
                        let mut lower = face.clone();
                        lower.remove(slot);
                        let carried = *cell_of.get(&lower).ok_or_else(|| {
                            CollocationRefusal::FaceNotDownwardClosed {
                                face: lower.join(FACE_ITEM_SEPARATOR),
                            }
                        })?;
                        let coefficient = if slot % 2 == 0 {
                            ComparativeMultiplicity::positive(1u32)
                        } else {
                            ComparativeMultiplicity::negative(1u32)
                        };
                        boundary.add_term(carried, coefficient);
                    }
                }
                let id = complex.found_cell(
                    face.join(FACE_ITEM_SEPARATOR),
                    BTreeSet::from([EventId(occasion)]),
                    grade,
                    boundary,
                )?;
                cell_of.insert(face.clone(), id);
                *founded.entry(grade).or_insert(0) += 1;
            }
        }

        Ok(CoPresentationComplex {
            complex,
            aperture,
            founded,
            outside,
            cell_of,
        })
    }
}

/// How deep a co-presentation complex may be founded.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum ComplexAperture {
    /// Found every co-presented set.
    Exhausted,
    /// Found nothing above this grade. `β_k` of the complex is exact for every `k` strictly below
    /// the bound, because a `k`-cycle and its fillings live in grades `k` and `k + 1`.
    ToGrade(u32),
}

impl ComplexAperture {
    pub const fn admits(&self, grade: u32) -> bool {
        match self {
            Self::Exhausted => true,
            Self::ToGrade(limit) => grade <= *limit,
        }
    }

    /// The highest grade whose Betti number this aperture computes exactly.
    pub const fn exact_to_grade(&self) -> Option<u32> {
        match self {
            Self::Exhausted => None,
            Self::ToGrade(limit) => Some(limit.saturating_sub(1)),
        }
    }
}

/// The complex, its aperture, and what fell outside it.
#[derive(Clone, Debug)]
pub struct CoPresentationComplex {
    complex: GradedCausalComplex,
    aperture: ComplexAperture,
    founded: BTreeMap<u32, usize>,
    outside: BTreeMap<u32, usize>,
    cell_of: BTreeMap<Vec<String>, CausalCellId>,
}

impl CoPresentationComplex {
    pub fn complex(&self) -> &GradedCausalComplex {
        &self.complex
    }

    pub fn aperture(&self) -> ComplexAperture {
        self.aperture
    }

    /// Cells founded, by grade.
    pub fn founded(&self) -> &BTreeMap<u32, usize> {
        &self.founded
    }

    /// Co-presented sets the aperture refused, by grade. Named as a population, not discarded.
    pub fn outside_aperture(&self) -> &BTreeMap<u32, usize> {
        &self.outside
    }

    pub fn cell_of(&self, face: &[String]) -> Option<CausalCellId> {
        self.cell_of.get(face).copied()
    }
}

// -------------------------------------------------------------------------------------------------
// The exact quotient
// -------------------------------------------------------------------------------------------------

/// `C(n, k)` exactly.
pub fn binomial(n: usize, k: usize) -> BigUint {
    if k > n {
        return BigUint::from(0u32);
    }
    let k = k.min(n - k);
    let mut carried = BigUint::one();
    for step in 0..k {
        carried *= BigUint::from(n - step);
        carried /= BigUint::from(step + 1);
    }
    carried
}

/// `Q` — the share of placements of an extent of size `extent_from` among `regions` that would have
/// landed inside an extent of size `extent_to` **whatever the pairing was**.
///
/// This is the exact declared quotient the null-bind realizes. A passage with `Q` near one is
/// forced by arithmetic; a passage with `Q` near zero is forced by the material. Reported on every
/// passage, consulted by nothing.
pub fn placement_quotient(regions: usize, extent_from: usize, extent_to: usize) -> Rat {
    let total = binomial(regions, extent_from);
    if total == BigUint::from(0u32) {
        return Rat::new(BigInt::from(0), BigInt::from(1));
    }
    Rat::new(
        BigInt::from(binomial(extent_to, extent_from)),
        BigInt::from(total),
    )
}

// -------------------------------------------------------------------------------------------------
// Refusals
// -------------------------------------------------------------------------------------------------

/// Why a collocation reading refused.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CollocationRefusal {
    EmptyDeposit,
    RegionPresentsNothing { region: String },
    RegionNamedTwice { region: String },
    EmptyNullBindSchedule,
    NullBindMovedMarginals { what: String },
    FacetTooWideToEnumerate { items: usize },
    FacePopulationExceedsAperture { declared: usize },
    FaceNotDownwardClosed { face: String },
    Algebra(CausalAlgebraicError),
}

impl std::fmt::Display for CollocationRefusal {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::EmptyDeposit => write!(formatter, "the deposit carries no region"),
            Self::RegionPresentsNothing { region } => {
                write!(formatter, "region {region} presents no item")
            }
            Self::RegionNamedTwice { region } => {
                write!(formatter, "region {region} is named twice")
            }
            Self::EmptyNullBindSchedule => {
                write!(
                    formatter,
                    "a null-bind schedule with no stride re-pairs nothing"
                )
            }
            Self::NullBindMovedMarginals { what } => write!(
                formatter,
                "the null-bind moved {what}; it is not the same material with the pairing destroyed"
            ),
            Self::FacetTooWideToEnumerate { items } => write!(
                formatter,
                "a facet carries {items} items and its faces cannot be enumerated by mask"
            ),
            Self::FacePopulationExceedsAperture { declared } => write!(
                formatter,
                "the co-presented population exceeds the declared enumeration aperture {declared}"
            ),
            Self::FaceNotDownwardClosed { face } => write!(
                formatter,
                "the face {face} was reached before it was founded; the enumeration is not downward closed"
            ),
            Self::Algebra(inner) => write!(formatter, "{inner}"),
        }
    }
}

impl std::error::Error for CollocationRefusal {}

impl From<CausalAlgebraicError> for CollocationRefusal {
    fn from(inner: CausalAlgebraicError) -> Self {
        Self::Algebra(inner)
    }
}

// -------------------------------------------------------------------------------------------------
// Reading declared textual material into regions
// -------------------------------------------------------------------------------------------------

/// The identifier items of one line of a Lean artifact.
///
/// The rule is [`crate::derivation_atlas::read_derivation`]'s, restated at line granularity because
/// that reader takes a whole artifact and this organ needs a finer grain. The three exclusions are
/// the same three and they are taken from the same two public tables, so **the vocabularies** cannot
/// drift apart; `line_items_agree_with_read_derivation` pins the agreement on real material.
///
/// **That sentence was carried as though it covered the tokenizer and it never did.** A shared
/// public table cannot drift; a hand-copied expression can, and the split rule was hand-copied here
/// and in `derivation_capacitance::named_lines` while both docs claimed otherwise. It drifted on
/// 2026-08-09, when [`crate::derivation_atlas::identifier_tokens`] learned `'`, `!` and `?` and
/// these two copies did not. The tokenizer is now called rather than restated, which is what makes
/// the claim true instead of merely written.
pub fn lean_line_items(line: &str) -> BTreeSet<String> {
    let trimmed = line.trim();
    if trimmed == "end" || trimmed.starts_with("end ") {
        return BTreeSet::new();
    }
    let read = if trimmed == "have" || trimmed.starts_with("have ") {
        match trimmed.split_once(":=") {
            Some((_, right)) => right,
            None => return BTreeSet::new(),
        }
    } else {
        trimmed
    };

    let mut items = BTreeSet::new();
    let mut founds_next = false;
    // The tokenizer is `derivation_atlas`'s, called and not restated. This line carried a hand copy
    // of the old single-class `split` until 2026-08-09, while the doc above claimed the two readings
    // "cannot drift apart" — true of the vocabularies, which are shared public tables, and never of
    // the tokenizer, which was not one. `contrapose!` returned here as `contrapose`.
    for token in crate::derivation_atlas::identifier_tokens(read) {
        if founds_next {
            founds_next = false;
            continue;
        }
        if crate::derivation_atlas::DECLARATION_FORMERS.contains(&token) {
            founds_next = true;
            continue;
        }
        if crate::derivation_atlas::CODEC_KEYWORDS.contains(&token) {
            continue;
        }
        if token.chars().count() <= 1 {
            continue;
        }
        items.insert(token.to_owned());
    }
    items
}

/// Every identifier item of a whole Lean artifact.
pub fn lean_artifact_items(text: &str) -> BTreeSet<String> {
    text.lines().flat_map(lean_line_items).collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn presentation(source: &str, region: &str, items: &[&str]) -> Presentation {
        Presentation {
            source: source.to_owned(),
            region: region.to_owned(),
            items: items.iter().map(|item| (*item).to_owned()).collect(),
        }
    }

    /// A material where the pairing is real: `a` never appears without `b`, and `c` never with `b`.
    fn paired() -> CollocationDeposit {
        CollocationDeposit::found(
            "test",
            vec![
                presentation("one", "r0", &["a", "b", "u"]),
                presentation("one", "r1", &["a", "b", "u"]),
                presentation("one", "r2", &["c", "d", "u"]),
                presentation("two", "r3", &["c", "d", "u"]),
            ],
        )
        .expect("declared material")
    }

    #[test]
    fn a_deposit_with_no_region_is_refused() {
        assert_eq!(
            CollocationDeposit::found("test", Vec::new()),
            Err(CollocationRefusal::EmptyDeposit)
        );
    }

    #[test]
    fn a_region_presenting_nothing_is_refused_by_name() {
        assert_eq!(
            CollocationDeposit::found("test", vec![presentation("one", "r0", &[])]),
            Err(CollocationRefusal::RegionPresentsNothing {
                region: "r0".to_owned()
            })
        );
    }

    #[test]
    fn a_region_named_twice_is_refused() {
        assert_eq!(
            CollocationDeposit::found(
                "test",
                vec![
                    presentation("one", "r0", &["a"]),
                    presentation("one", "r0", &["b"]),
                ]
            ),
            Err(CollocationRefusal::RegionNamedTwice {
                region: "r0".to_owned()
            })
        );
    }

    #[test]
    fn the_universal_item_is_named_and_excluded_from_every_face() {
        let reading = CoPresentation::read(&paired());
        assert_eq!(
            reading.universal(),
            &BTreeSet::from(["u".to_owned()]),
            "u is in every region"
        );
        assert!(
            reading.faces().values().all(|face| !face.contains("u")),
            "a universal item forces nothing because it distinguishes nothing"
        );
        assert!(
            reading.closure("a").contains("u"),
            "the raw closure keeps it; only the face removes it"
        );
    }

    #[test]
    fn collocation_founds_a_face_on_an_item_that_declares_nothing() {
        let reading = CoPresentation::read(&paired());
        assert_eq!(reading.face("a"), BTreeSet::from(["b".to_owned()]));
        assert_eq!(reading.face("c"), BTreeSet::from(["d".to_owned()]));
        assert!(
            !reading.face("a").contains("c"),
            "a and c never co-occur, so no passage between them is founded"
        );
    }

    #[test]
    fn the_regions_are_emergent_and_nothing_declared_them() {
        let reading = CoPresentation::read(&paired());
        assert_eq!(
            reading.facets(),
            BTreeSet::from([
                BTreeSet::from(["a".to_owned(), "b".to_owned(), "u".to_owned()]),
                BTreeSet::from(["c".to_owned(), "d".to_owned(), "u".to_owned()]),
            ]),
            "two maximal co-presented sets, derived from four regions"
        );
        // The Moore family: the two facets, their intersection, and the full item set.
        assert!(
            reading
                .closed_regions()
                .contains(&BTreeSet::from(["u".to_owned()]))
        );
    }

    #[test]
    fn every_item_measured_appears_in_the_return() {
        let reading = CoPresentation::read(&paired());
        let faces = reading.faces();
        for item in reading.items() {
            assert!(faces.contains_key(item), "{item} fell out of the return");
            assert!(
                !reading.extent(item).is_empty(),
                "{item} has an empty extent yet was measured"
            );
        }
        assert_eq!(reading.items().len(), 5);
    }

    #[test]
    fn a_forced_passage_carries_its_refusal_population_by_name() {
        let reading = CoPresentation::read(&paired());
        let passages = reading.forced_passages();
        let carried = passages
            .iter()
            .find(|passage| passage.from == "a" && passage.to == "b")
            .expect("a forces b");
        assert_eq!(carried.refusing, vec!["r2".to_owned(), "r3".to_owned()]);
        assert!(!carried.is_vacuous());
        assert!(carried.across_time(), "a was presented twice");
        assert_eq!(carried.sources, BTreeSet::from(["one".to_owned()]));
    }

    #[test]
    fn a_passage_witnessed_in_two_sources_is_a_cross_source_invariant() {
        let reading = CoPresentation::read(&paired());
        let passages = reading.forced_passages();
        let carried = passages
            .iter()
            .find(|passage| passage.from == "c" && passage.to == "d")
            .expect("c forces d");
        assert_eq!(
            carried.sources,
            BTreeSet::from(["one".to_owned(), "two".to_owned()]),
            "the referent law's cross-source invariant, returned rather than assumed"
        );
    }

    #[test]
    fn the_quotient_is_exact_and_one_when_the_target_is_universal() {
        // ext(u) = 4 of 4, ext(a) = 2: every placement of a lands inside u.
        assert_eq!(placement_quotient(4, 2, 4), Rat::new(1.into(), 1.into()));
        // ext(b) = 2 of 4, ext(a) = 2: one placement of six.
        assert_eq!(placement_quotient(4, 2, 2), Rat::new(1.into(), 6.into()));
        // The running quotient is exact at every step because a product of `j` consecutive
        // integers is divisible by `j!`. Pinned against a value no float can hold.
        assert_eq!(binomial(103, 14).to_string(), "68811463134684900");
        assert_eq!(binomial(103, 2).to_string(), "5253");
        assert_eq!(binomial(101, 91).to_string(), "19212541264840");
        assert_eq!(binomial(3, 5), BigUint::from(0u32));
    }

    #[test]
    fn the_null_bind_holds_both_marginals_bit_exact() {
        let deposit = paired();
        let bound = deposit
            .null_bind(&[1, 2, 3], NullBindScope::WholeDeposit)
            .expect("declared schedule");
        assert_eq!(deposit.marginals(), bound.deposit().marginals());
        assert_eq!(deposit.regions(), bound.deposit().regions());
        assert_eq!(deposit.items(), bound.deposit().items());
    }

    #[test]
    fn the_null_bind_destroys_a_real_pairing() {
        let deposit = paired();
        let bound = deposit
            .null_bind(&[1, 2, 3, 5], NullBindScope::WholeDeposit)
            .expect("declared schedule");
        assert!(
            bound.applied > 0,
            "a null-bind that swaps nothing is not a control"
        );
        assert!(bound.regions_moved > 0);
        let after = CoPresentation::read(bound.deposit());
        assert_ne!(
            CoPresentation::read(&deposit).faces(),
            after.faces(),
            "the same items and the same counts must not found the same faces"
        );
    }

    #[test]
    fn a_within_source_null_bind_never_moves_an_item_across_sources() {
        let deposit = paired();
        let bound = deposit
            .null_bind(&[1, 2, 3], NullBindScope::WithinSource)
            .expect("declared schedule");
        for (before, after) in deposit
            .presentations()
            .iter()
            .zip(bound.deposit().presentations())
        {
            assert_eq!(before.source, after.source);
        }
        // `two` carries one region, so no within-source swap is legal there and `r3` cannot move.
        assert_eq!(
            deposit.presentations()[3],
            bound.deposit().presentations()[3]
        );
    }

    #[test]
    fn an_empty_null_bind_schedule_is_refused() {
        assert_eq!(
            paired().null_bind(&[], NullBindScope::WholeDeposit),
            Err(CollocationRefusal::EmptyNullBindSchedule)
        );
    }

    #[test]
    fn faces_grow_from_collocation_and_the_complex_certifies_itself() {
        let reading = CoPresentation::read(&paired());
        let built = reading
            .complex(ComplexAperture::Exhausted, 100_000)
            .expect("the material is small");
        // Two 3-item facets sharing one item: 7 + 7 - 1 = 13 co-presented sets.
        assert_eq!(built.complex().cells().len(), 13);
        assert_eq!(
            built.founded(),
            &BTreeMap::from([(0u32, 5usize), (1, 6), (2, 2)])
        );
        assert!(built.outside_aperture().is_empty());
        // `found_cell` refuses a nonzero d^2, so a complex that built at all is a chain complex.
        built.complex().validate().expect("a valid complex");
    }

    #[test]
    fn a_declared_complex_aperture_names_what_fell_outside_it() {
        let reading = CoPresentation::read(&paired());
        let built = reading
            .complex(ComplexAperture::ToGrade(1), 100_000)
            .expect("the material is small");
        assert_eq!(built.founded(), &BTreeMap::from([(0u32, 5usize), (1, 6)]));
        assert_eq!(built.outside_aperture(), &BTreeMap::from([(2u32, 2usize)]));
        assert_eq!(built.aperture().exact_to_grade(), Some(0));
    }

    #[test]
    fn the_f_vector_counts_the_whole_complex_whatever_the_complex_aperture_is() {
        let reading = CoPresentation::read(&paired());
        assert_eq!(
            reading.f_vector(100_000).expect("small"),
            BTreeMap::from([(0u32, 5usize), (1, 6), (2, 2)])
        );
    }

    #[test]
    fn an_enumeration_aperture_refuses_rather_than_truncates() {
        let reading = CoPresentation::read(&paired());
        assert_eq!(
            reading.co_presented_faces(4),
            Err(CollocationRefusal::FacePopulationExceedsAperture { declared: 4 })
        );
    }

    #[test]
    fn deleting_the_universal_item_leaves_the_link_and_names_what_emptied() {
        let reading = CoPresentation::read(&paired());
        let (link, emptied) = reading.without_universal();
        assert!(
            emptied.is_empty(),
            "every region carried more than the cone point"
        );
        assert!(link.universal().is_empty());
        assert_eq!(link.items().len(), 4);
        // The cone is contractible; the link is two disjoint edges.
        let built = link
            .complex(ComplexAperture::Exhausted, 100_000)
            .expect("small");
        assert_eq!(built.complex().cells().len(), 6);
    }

    #[test]
    fn a_region_emptied_by_deleting_the_universal_is_named_not_dropped() {
        let deposit = CollocationDeposit::found(
            "test",
            vec![
                presentation("one", "r0", &["u"]),
                presentation("one", "r1", &["u", "a"]),
            ],
        )
        .expect("declared");
        let (link, emptied) = CoPresentation::read(&deposit).without_universal();
        assert_eq!(emptied, vec!["r0".to_owned()]);
        assert_eq!(link.regions(), 1);
    }

    #[test]
    fn separation_classes_group_exactly_the_items_collocation_cannot_tell_apart() {
        let reading = CoPresentation::read(&paired());
        let classes = reading.separation_classes();
        // a<->b and c<->d are mutually forcing; u forces nothing.
        assert_eq!(classes.len(), 5, "five items, five distinct faces");
        let (_, together) = classes
            .iter()
            .find(|(face, _)| face.contains("b"))
            .expect("a forces b");
        assert_eq!(together, &BTreeSet::from(["a".to_owned()]));
    }

    #[test]
    fn two_grains_read_the_same_material_differently() {
        // Coarse: one region carrying everything. Fine: three regions.
        let coarse = CollocationDeposit::found(
            "coarse",
            vec![presentation("one", "whole", &["a", "b", "c"])],
        )
        .expect("declared");
        let fine = CollocationDeposit::found(
            "fine",
            vec![
                presentation("one", "l0", &["a", "b"]),
                presentation("one", "l1", &["a", "c"]),
                presentation("one", "l2", &["b", "c"]),
            ],
        )
        .expect("declared");
        let coarse = CoPresentation::read(&coarse);
        let fine = CoPresentation::read(&fine);
        assert_eq!(
            coarse.universal().len(),
            3,
            "one region makes everything universal"
        );
        assert!(coarse.face("a").is_empty());
        assert!(
            fine.face("a").is_empty(),
            "a occurs with b and with c, forcing neither"
        );
        assert_eq!(coarse.facets().len(), 1);
        assert_eq!(
            fine.facets().len(),
            3,
            "the fine grain founds three facets, not one"
        );
    }

    #[test]
    fn line_items_agree_with_read_derivation_on_a_deposited_artifact() {
        // `contrapose!` and `h'` are in this fixture because it previously carried no `'`, `!` or
        // `?` at all, so the two readers agreed by carrying one identical defect and the assertion
        // could not fail. `CLAUDE.md` §8: a check whose material cannot vary the property under test
        // is the same defect as a check that cannot fail, wearing a passing result.
        let text = "namespace Soma\n\
                    def exactCarrier (P : Prop) : Prop := P\n\
                    variable (P : Prop)\n\
                    theorem formal_carry (h : P) : exactCarrier P := by\n  \
                      contrapose! h'\n  \
                      apply exact_chart_carry\n  \
                      assumption\n\
                    end Soma\n";
        let derivation = crate::derivation_atlas::read_derivation(text)
            .expect("the artifact declares a theorem");
        let collocated = lean_artifact_items(text);
        let recruited: BTreeSet<String> = derivation.recruited.keys().cloned().collect();
        assert_eq!(
            collocated, recruited,
            "the line reader and the artifact reader must not drift apart"
        );
        assert!(collocated.contains("apply"), "an atom is still presented");
        assert!(
            !collocated.contains("formal_carry"),
            "the file founds it, it does not recruit it"
        );
        // The two that make the parity assertion able to fail. Under the hand-copied rule this
        // reader returned `contrapose` and dropped `h'` to a single glyph, while the artifact
        // reader returned `contrapose!` and `h'` — the drift, exhibited as its own separating words.
        assert!(
            collocated.contains("contrapose!"),
            "the token carries its own `!`"
        );
        assert!(
            collocated.contains("h'"),
            "a primed binder is one token, not a deleted glyph"
        );
    }

    #[test]
    fn a_have_line_binds_on_the_left_at_line_grain_too() {
        assert_eq!(
            lean_line_items("  have generated := exact_chart_carry P"),
            BTreeSet::from(["exact_chart_carry".to_owned()])
        );
        assert!(lean_line_items("end Soma").is_empty());
    }

    #[test]
    fn the_quotient_and_the_null_bind_are_independent_and_agree_on_declared_material() {
        // `a => b` is forced with a small Q; `a => u` is forced with Q exactly one.
        let deposit = paired();
        let reading = CoPresentation::read(&deposit);
        let closure_of_a = reading.closure("a");
        assert!(closure_of_a.contains("u") && closure_of_a.contains("b"));
        assert_eq!(placement_quotient(4, 2, 4), Rat::new(1.into(), 1.into()));
        assert!(placement_quotient(4, 2, 2) < placement_quotient(4, 2, 4));
        // The null-bind cannot break a passage whose Q is one: u is in every region however the
        // incidence is re-paired, because its count equals the region population.
        let bound = deposit
            .null_bind(&[1, 2, 3, 5, 7], NullBindScope::WholeDeposit)
            .expect("declared");
        assert!(
            CoPresentation::read(bound.deposit())
                .closure("a")
                .contains("u")
        );
    }
}

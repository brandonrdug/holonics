//! **Local keys glued on overlaps: the turn menu read per region of a cover, its keys glued through
//! the rotor gauge, and the repair run per glued region** (THE_REBUILD U6, "The task is repair, not
//! continuation", its **Text** item; the
//! [record](../../../../../research/records/2026-10-05_TEXT_REPAIR_BY_LOCAL_KEYS_GLUED_ON_OVERLAPS.md)).
//!
//! [definition; agent-inferred, October 5] A passage whose relation is not one stationary turn over its
//! whole clock may still be one locally. The key is then a section over a cover, not a global key.
//!
//! - **The cover** ([`Cover`]): regions of `ℓ` cells at stride `s`, overlapping in `ω = ℓ − s`, read
//!   at the distances `δ ∈ [1, r]`. A turn menu at `δ` publishes its map only when each of the `δ`
//!   residue chains of `ℤ/δ` carries an edge, `2δ` cells; so each overlap certifies every read
//!   distance when `ω ≥ 2r` (the restriction of a region's key to its overlap is itself a certified
//!   reading), and then every pair `(t − δ, t)`, `δ ≤ r`, lies inside one region.
//! - **A region's fibre** ([`survivors`]): one [`TurnMenu`] a distance over the region's intact
//!   pairs, in clock order; its surviving distances with their readings. Its key ([`LocalKey`]):
//!   unread (no edge), empty (no survivor), one (the windings law locates one generator,
//!   [`super::generator`]) or plural.
//! - **The gluing** ([`Join`], Lean `Foundation/ContinuingTower.GluingResult`, total by
//!   `gluingResult_total`): two regions' fibres at `δ` glue exactly when the joint menu over both
//!   regions' edges admits a turn. The rotor gauge `(k, s) ↦ (k + 1, ρ⁻¹ ∘ s)` keeps every turn, so a
//!   compatible section over both regions, up to the gauge, is a candidate `(c, S)` of the joint menu.
//!   Unique: the joint survivors locate one generator; plural: nonempty, not one class; obstructed:
//!   both regions keyed and no joint survivor; open: a side with no key.
//! - **Glued regions** ([`locate`]): along the clock, a region extends the glued region before it
//!   while the joint menus over all of them locate one generator (every join on the way unique);
//!   otherwise it opens a new one, so a plural region whose neighbour resolves it is glued into a
//!   located key. A glued region's **member** is its generator when its key is one, read as a
//!   [`PairRelation`] on the classes; a plural glued region keeps its fibre and restricts nothing.
//!   [agent-inferred, the record's §0 amendment] An unpublished survivor's read pairs are one-edge
//!   readings of the passage at a distance: restricting through them reads `x_t` from a pair seen
//!   once elsewhere at the same distance, the skip-relation index THE_REBUILD U6 refuses, and on
//!   development text every cell released that way was wrong.
//! - **The restriction** ([`LocalRepair::families`]): per glued region, each member's
//!   [`super::repair::restrict`] over the glued region's cells (the relation holds at every station,
//!   opening `0`); a member whose restriction empties a family is refused by the passage, an exact
//!   zero; the glued region's family at a cell is the union over its surviving members' families,
//!   which is the projection of the joint fibre over its members, certified when every surviving
//!   member's restriction is ([`super::Restriction::support`]). A cell that two keyed glued regions
//!   both restrict (an overlap across a join that did not glue) takes the intersection, an enclosure
//!   of the joint projection and not a certificate (the union of two forests may close a cycle), so
//!   it is held.
//! - **The release** ([`LocalRepair::release`]): `receiver::release` at tolerance zero, released
//!   when the family is certified and one class, held with it otherwise (the repair owner's one
//!   decision).
//! - **The codec** ([`LocalRepair::residual_code`], [`LocalRepair::reopen`]): the Fold's side
//!   residual with the members fixed: while an erased cell is held, the truth's index in the first
//!   held family in `⌈log₂ |F_t|⌉` bits, that cell pinned and the restriction re-run (a member the pin
//!   refuses leaves). The keys are located from the damaged passage's own intact cells, so a decoder
//!   holding it relocates them.
//!
//! | Law | Lean | Rust |
//! |---|---|---|
//! | the turn menu's fibre per region, up to the rotor gauge | owed (#62), as `compression::keys::TurnMenu` | [`survivors`] |
//! | a class of windings is one key | owed (#62) | [`super::generator`] |
//! | the gluing trichotomy | `Foundation/ContinuingTower.GluingResult`, `gluingResult_total` | [`Join`] |
//! | a glued region's family is the union of its members' projections | owed (#62), with the repair's projection law | [`LocalRepair::families`], checked by the owner's brute-force test |
//! | release at width zero, held otherwise | `Foundation/ReceiverRelease.ReleaseLaw.sound` | [`LocalRepair::release`] |
//! | the residual reopens the passage | `Transport/Fold.reopen_apply_fold` | [`LocalRepair::reopen`] |

use std::ops::Range;

use num_bigint::BigUint;

use super::repair::{decide, restrict};
use super::{CellRelease, DamagedPassage, PairRelation, TurnMenu, TurnReading, generator};
use crate::compression::CompressionError;
use crate::compression::cost::{ceil_log2, read_index, write_index};

/// [definition] **A cover of a passage** (module header): regions of `ℓ` cells at stride `s`, read
/// at the distances `δ ∈ [1, r]`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Cover {
    length: usize,
    region: usize,
    stride: usize,
    reach: usize,
}

impl Cover {
    /// A cover of a passage of `length` cells; refused unless `r ≥ 1`, `0 < s < ℓ ≤ length`, the
    /// overlap certifies every read distance (`ℓ − s ≥ 2r`), and the regions tile the passage
    /// (`s` divides `length − ℓ`).
    pub fn declare(
        length: usize,
        region: usize,
        stride: usize,
        reach: usize,
    ) -> Result<Self, CompressionError> {
        let refused = |expected: usize, found: usize| CompressionError::Extent {
            what: "a cover whose overlaps certify every read distance and tile the passage",
            expected,
            found,
        };
        if reach == 0 || stride == 0 || stride >= region || region > length {
            return Err(refused(region, stride));
        }
        if region - stride < 2 * reach {
            return Err(refused(2 * reach, region - stride));
        }
        if (length - region) % stride != 0 {
            return Err(refused(0, (length - region) % stride));
        }
        Ok(Self {
            length,
            region,
            stride,
            reach,
        })
    }

    /// The regions, in clock order.
    pub fn regions(&self) -> Vec<Range<usize>> {
        (0..=(self.length - self.region) / self.stride)
            .map(|i| i * self.stride..i * self.stride + self.region)
            .collect()
    }

    /// `r`.
    pub fn reach(&self) -> usize {
        self.reach
    }
}

/// **The menus over a span of cells**: one [`TurnMenu`] on `period` ports a distance `δ ∈ [1, r]`,
/// each reading every pair `(t − δ, t)` inside the span whose two cells are intact, in clock order.
pub fn menus(cells: &[Option<usize>], span: &Range<usize>, reach: usize, period: usize) -> Vec<TurnMenu> {
    (1..=reach)
        .map(|offset| {
            let mut menu = TurnMenu::open(period as u64);
            for t in span.start + offset..span.end {
                if let (Some(from), Some(to)) = (cells[t - offset], cells[t]) {
                    menu.observe(from, to);
                }
            }
            menu
        })
        .collect()
}

/// **A fibre**: the distances read (an edge each), and each surviving distance with its reading,
/// in increasing order.
pub fn survivors(menus: &[TurnMenu]) -> (usize, Vec<(usize, TurnReading)>) {
    let read = menus.iter().filter(|menu| menu.edges() > 0).count();
    let alive = menus
        .iter()
        .enumerate()
        .filter(|(_, menu)| menu.edges() > 0 && menu.alive())
        .map(|(index, menu)| (index + 1, menu.reading()))
        .filter(|(_, reading)| !reading.turns.is_empty())
        .collect();
    (read, alive)
}

/// [definition] **A local key** (module header): a fibre read as unread, empty, one generator (its
/// distance) or plural (its surviving distances).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LocalKey {
    Unread,
    Empty,
    One(usize),
    Plural(Vec<usize>),
}

impl LocalKey {
    /// The key of a fibre.
    pub fn of(read: usize, alive: &[(usize, TurnReading)]) -> Self {
        if read == 0 {
            Self::Unread
        } else if alive.is_empty() {
            Self::Empty
        } else if let Some((offset, _)) = generator(alive) {
            Self::One(*offset)
        } else {
            Self::Plural(alive.iter().map(|(offset, _)| *offset).collect())
        }
    }

    /// Whether some key survives.
    pub fn keyed(&self) -> bool {
        matches!(self, Self::One(_) | Self::Plural(_))
    }

}

/// [definition] **A join of two adjacent regions** (module header; Lean
/// `Foundation/ContinuingTower.GluingResult`, with `Open` where a side has no section).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Join {
    Unique,
    Plural,
    Obstructed,
    Open,
}

/// [definition] **A glued region**: the regions it joins (their indices), its span of cells, its
/// key over the joint menus, and its members as relations.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GluedRegion {
    pub regions: Range<usize>,
    pub span: Range<usize>,
    pub key: LocalKey,
    pub members: Vec<PairRelation>,
}

/// [definition] **The local keys of a damaged passage**: each region's key, each adjacent join, and
/// the glued regions.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LocalRepair {
    pub keys: Vec<LocalKey>,
    pub joins: Vec<Join>,
    pub glued: Vec<GluedRegion>,
}

/// [definition] **The families after the restriction**: each cell's family, whether it is
/// certified, the glued regions that restricted it, and per glued region the members its passage
/// refused.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Families {
    pub families: Vec<Vec<usize>>,
    pub certified: Vec<bool>,
    pub restricted_by: Vec<usize>,
    pub refused: Vec<usize>,
}

/// **A menu's relation on the classes**: each read port with its consequence, every other class
/// unread (for a published map, the map).
pub fn relation(menu: &TurnMenu, offset: usize, classes: usize) -> Result<PairRelation, CompressionError> {
    let mut map = vec![None; classes];
    for (from, to) in menu.relation() {
        if from < classes && to < classes {
            map[from] = Some(to);
        }
    }
    PairRelation::new(offset, map)
}

/// **The joint fibre over a span**: its menus and its key.
pub fn fibre(
    cells: &[Option<usize>],
    span: &Range<usize>,
    reach: usize,
    period: usize,
) -> (Vec<TurnMenu>, LocalKey) {
    let menus = menus(cells, span, reach, period);
    let (read, alive) = survivors(&menus);
    let key = LocalKey::of(read, &alive);
    (menus, key)
}

/// **Locate the local keys of a damaged passage over a cover** (module header), on a ring of
/// `period` ports holding the passage's classes one to a port. Refused when the cover is not the
/// passage's or a port cannot hold the classes.
pub fn locate(
    passage: &DamagedPassage,
    cover: &Cover,
    period: usize,
) -> Result<LocalRepair, CompressionError> {
    let cells = passage.cells();
    if cover.length != cells.len() || period < passage.classes() {
        return Err(CompressionError::Extent {
            what: "a cover of the passage on a ring holding its classes one to a port",
            expected: cells.len(),
            found: cover.length,
        });
    }
    let regions = cover.regions();
    let keys: Vec<LocalKey> = regions
        .iter()
        .map(|region| fibre(cells, region, cover.reach, period).1)
        .collect();
    let joins = (0..regions.len().saturating_sub(1))
        .map(|i| {
            if !keys[i].keyed() || !keys[i + 1].keyed() {
                return Join::Open;
            }
            match fibre(cells, &(regions[i].start..regions[i + 1].end), cover.reach, period).1 {
                LocalKey::One(_) => Join::Unique,
                LocalKey::Plural(_) => Join::Plural,
                LocalKey::Unread | LocalKey::Empty => Join::Obstructed,
            }
        })
        .collect();
    let mut glued = Vec::new();
    let mut first = 0;
    while first < regions.len() {
        let mut last = first;
        while last + 1 < regions.len()
            && matches!(
                fibre(cells, &(regions[first].start..regions[last + 1].end), cover.reach, period).1,
                LocalKey::One(_)
            )
        {
            last += 1;
        }
        let span = regions[first].start..regions[last].end;
        let (menus, key) = fibre(cells, &span, cover.reach, period);
        let members = match key {
            LocalKey::One(offset) => vec![relation(&menus[offset - 1], offset, passage.classes())?],
            _ => Vec::new(),
        };
        glued.push(GluedRegion {
            regions: first..last + 1,
            span,
            key,
            members,
        });
        first = last + 1;
    }
    Ok(LocalRepair {
        keys,
        joins,
        glued,
    })
}

impl LocalRepair {
    /// **The families** (module header, "The restriction") of a passage under these keys: the
    /// damaged passage they were located from, or the same passage with cells pinned.
    pub fn families(&self, passage: &DamagedPassage) -> Result<Families, CompressionError> {
        let cells = passage.cells();
        let classes = passage.classes();
        let mut families: Vec<Vec<usize>> = cells
            .iter()
            .map(|cell| match cell {
                Some(class) => vec![*class],
                None => (0..classes).collect(),
            })
            .collect();
        let mut certified = vec![true; cells.len()];
        let mut restricted_by = vec![0usize; cells.len()];
        let mut refused = Vec::with_capacity(self.glued.len());
        for glued in &self.glued {
            let local = DamagedPassage::new(cells[glued.span.clone()].to_vec(), classes, 0)?;
            let mut union: Vec<Vec<usize>> = vec![Vec::new(); glued.span.len()];
            let mut all_certified = vec![true; glued.span.len()];
            let mut surviving = 0usize;
            for member in &glued.members {
                let restriction = match restrict(&local, member) {
                    Ok(restriction) => restriction,
                    Err(CompressionError::Contradicted { .. }) => continue,
                    Err(other) => return Err(other),
                };
                surviving += 1;
                let support = restriction.support();
                for (t, family) in restriction.families().iter().enumerate() {
                    all_certified[t] &= support[t] == *family;
                    for &class in family {
                        if !union[t].contains(&class) {
                            union[t].push(class);
                        }
                    }
                }
            }
            refused.push(glued.members.len() - surviving);
            if surviving == 0 {
                continue;
            }
            for (offset, mut family) in union.into_iter().enumerate() {
                let t = glued.span.start + offset;
                family.sort_unstable();
                restricted_by[t] += 1;
                if restricted_by[t] == 1 {
                    families[t] = family;
                    certified[t] = all_certified[offset];
                } else {
                    // Two keyed glued regions: the intersection encloses the joint projection.
                    let meet: Vec<usize> =
                        families[t].iter().copied().filter(|c| family.contains(c)).collect();
                    if !meet.is_empty() {
                        families[t] = meet;
                    } else {
                        families[t].extend(family);
                        families[t].sort_unstable();
                        families[t].dedup();
                    }
                    certified[t] = false;
                }
            }
        }
        for (t, cell) in cells.iter().enumerate() {
            if cell.is_none() && restricted_by[t] == 0 {
                certified[t] = false;
            }
        }
        Ok(Families {
            families,
            certified,
            restricted_by,
            refused,
        })
    }

    /// **The release** (module header): each erased cell decided by `receiver::release` at
    /// tolerance zero; intact cells as read.
    pub fn release(&self, passage: &DamagedPassage) -> Result<Vec<CellRelease>, CompressionError> {
        let read = self.families(passage)?;
        passage
            .cells()
            .iter()
            .enumerate()
            .map(|(t, cell)| match cell {
                Some(class) => Ok(CellRelease::Intact(*class)),
                None => decide(t, &read.families[t], read.certified[t]),
            })
            .collect()
    }

    /// **The residual's code** (module header, "The codec"): the coder holds the truth; refused
    /// when the truth leaves a held family or a released cell differs from it.
    pub fn residual_code(
        &self,
        truth: &[usize],
        passage: &DamagedPassage,
    ) -> Result<Vec<bool>, CompressionError> {
        let mut code = Vec::new();
        let mut current = passage.clone();
        loop {
            let releases = self.release(&current)?;
            let held = releases.iter().enumerate().find_map(|(t, release)| match release {
                CellRelease::Held(family) => Some((t, family.clone())),
                _ => None,
            });
            let Some((t, family)) = held else {
                if releases.iter().zip(truth).any(|(release, truth)| release.class() != Some(*truth)) {
                    return Err(CompressionError::NotRegenerated {
                        length: truth.len(),
                    });
                }
                return Ok(code);
            };
            let index = family
                .iter()
                .position(|&class| class == truth[t])
                .ok_or(CompressionError::Contradicted { cell: t })?;
            write_index(&mut code, index, ceil_log2(&BigUint::from(family.len())));
            current = pinned(&current, t, truth[t])?;
        }
    }

    /// **Reopen a damaged passage** from its residual: reads exactly the bits
    /// [`LocalRepair::residual_code`] wrote.
    pub fn reopen(
        &self,
        passage: &DamagedPassage,
        residual: &mut impl Iterator<Item = bool>,
    ) -> Result<Vec<usize>, CompressionError> {
        let mut current = passage.clone();
        loop {
            let releases = self.release(&current)?;
            let held = releases.iter().enumerate().find_map(|(t, release)| match release {
                CellRelease::Held(family) => Some((t, family.clone())),
                _ => None,
            });
            let Some((t, family)) = held else {
                return Ok(releases
                    .iter()
                    .map(|release| release.class().expect("no cell is held"))
                    .collect());
            };
            let index = read_index(residual, ceil_log2(&BigUint::from(family.len())), family.len())?;
            current = pinned(&current, t, family[index])?;
        }
    }
}

/// The passage with cell `t` read as `class` (a residual's patch).
fn pinned(passage: &DamagedPassage, t: usize, class: usize) -> Result<DamagedPassage, CompressionError> {
    let mut cells = passage.cells().to_vec();
    cells[t] = Some(class);
    DamagedPassage::new(cells, passage.classes(), passage.opening())
}

#[cfg(test)]
mod tests;

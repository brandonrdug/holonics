//! **Repair by reflection: a located pair restricts a damaged passage's compatible family from both
//! sides** (THE_REBUILD U6, "The task is repair, not continuation"; the
//! [record](../../../../../research/records/2026-10-05_REPAIR_BY_REFLECTION_THE_LOCATED_PAIR_RESTRICTS_THE_ERASED_CELLS_FROM_BOTH_SIDES.md)).
//!
//! [definition; agent-inferred, October 5] Generation is the progressive restriction of a
//! compatible family, `F_(k+1) = T_(g_k)(F_k) ∩ C_k` (Lean `Transport/ArtifactRelease.step`).
//! Key location reads a menu of pair contacts and returns the key; repair reads the same relation
//! the other way: the key is known and the passage's damaged cells are unknown. It is the Bombe run
//! as decryption, so it lives beside the turn menu that locates the pair ([`super::TurnMenu`]).
//!
//! - **The relation** ([`PairRelation`]): a located pair `(δ, f)` read as `x_t = f(x_(t−δ))` on the
//!   passage's classes. A class whose consequence was never read restricts nothing (the turn menu's
//!   publication law: a consequence never read stays plural), so the relation is
//!   `R(a, b) :⇔ f(a) unread ∨ f(a) = b`.
//! - **Where it holds**: at the passage's stations `t ≥ o` (its declared opening), where the relation
//!   was read; a cell before the opening is joined only as an antecedent. The edges `(t − δ, t)`,
//!   `t ∈ [max(o, δ), L)`, join each residue class of `ℤ/δ` into chains: the relation graph is a
//!   forest of paths, with no cycle.
//! - **The restriction** ([`restrict`]): every cell's family starts at its class if intact and at
//!   the whole alphabet if erased, and each sweep intersects it with what its antecedent admits
//!   through `f` and what its consequent admits through `f⁻¹`,
//!
//! ```text
//! F_t ← F_t ∩ R(F_(t−δ)) ∩ R⁻¹(F_(t+δ)),     R(F) = {b : ∃a ∈ F, R(a, b)},  R⁻¹(G) = {a : ∃b ∈ G, R(a, b)}
//! ```
//!
//!   until no family changes, each sweep running through the passage along its clock and then
//!   back. Families only shrink, so it stops; an emptied family is the key's refusal (the key does
//!   not fit the passage).
//! - **The certificate** ([`Restriction::support`]): on a forest of binary relations the fixed point
//!   is the joint fibre's projection at every cell [proved-derived; arc consistency on an acyclic
//!   constraint graph is global consistency, Freuder 1982; Lean owed, #62]. It is checked exactly,
//!   not assumed: along each chain the members holding class `a` at cell `t` are counted as the
//!   product of the chain's forward and backward counts, and a cell's family is certified when
//!   every class in it is held by at least one member of the nonempty joint fibre.
//! - **The release** ([`Restriction::release`]): each erased cell's class reading over the joint
//!   fibre has width zero exactly when its certified family is one class (the discrete metric), and
//!   is decided by the one decision law, [`crate::receiver::release::release`], at tolerance zero:
//!   released, or held with its plural family. Nothing is guessed.
//! - **The codec** ([`key_code`], [`residual_code`], [`reopen`]): the Fold's side residual (Lean
//!   `Transport/Fold.reopen_apply_fold`, `residual_injective_on_fibre`). The damage is the
//!   transition that drops the erased cells; the key and the residual reopen them exactly. The key
//!   is `δ − 1` in `⌈log₂(d − 1)⌉` bits (`d` the ring's period, the distance's population) and each
//!   class's consequence, or "unread", in `⌈log₂(|A| + 1)⌉` bits. The residual names, while some
//!   cell is held, the truth's index in the first held cell's family in `⌈log₂ |F_t|⌉` bits; that
//!   cell is pinned and the restriction re-run, so one patch reopens a whole held chain when `f`
//!   is a bijection. Over the joint fibre (`N` members, [`Restriction::joint`]) the residuals are a
//!   prefix code: each reopens its member and reads no further, so Kraft's sum is at most one and
//!   the longest residual is at least `⌈log₂ N⌉` (the Fold's injectivity on the fibre); a member
//!   reached by an early patch can take fewer bits.
//!
//! | Law | Lean | Rust |
//! |---|---|---|
//! | `F_(k+1) = T(F_k) ∩ C_k`, restriction never widens | `Transport/ArtifactRelease.step`, `restriction_never_widens` | [`restrict`] |
//! | the fixed point on a forest is the joint fibre's projection | owed (#62) | [`Restriction::support`], checked by the owner's brute-force test |
//! | release at width zero, held otherwise | `Foundation/ReceiverRelease.width_eq_zero_iff`, `ReleaseLaw.sound` | [`Restriction::release`] |
//! | the residual reopens the source; the residuals are a prefix code over the joint fibre, the longest at least `⌈log₂ N⌉` | `Transport/Fold.reopen_apply_fold`, `residual_injective_on_fibre` | [`reopen`], [`residual_code`] |

use num_bigint::BigUint;
use num_traits::{One, Zero};

use crate::compression::CompressionError;
use crate::compression::cost::{ceil_log2, read_index, write_index};
use crate::ratio::Rat;
use crate::receiver::face::{DiameterNorm, ReceiverWidth, WidthWitness};
use crate::receiver::release::{
    BeyondTolerance, DecisionRule, LawfulOptions, ReleaseReturn, WithinTolerance, release,
};

/// [definition] **A pair relation on a passage's classes** (module header): the distance `δ ≥ 1`
/// and each class's consequence, `None` where it was never read.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PairRelation {
    offset: usize,
    map: Vec<Option<usize>>,
}

impl PairRelation {
    /// The relation `x_t = f(x_(t−δ))`; refused at `δ = 0` or with a consequence outside the
    /// classes.
    pub fn new(offset: usize, map: Vec<Option<usize>>) -> Result<Self, CompressionError> {
        if offset == 0 {
            return Err(CompressionError::ZeroOffset);
        }
        if let Some(&image) = map.iter().flatten().find(|&&image| image >= map.len()) {
            return Err(CompressionError::IndexOutside {
                index: image,
                population: map.len(),
            });
        }
        Ok(Self { offset, map })
    }

    /// `δ`.
    pub fn offset(&self) -> usize {
        self.offset
    }

    /// Each class's consequence, `None` unread.
    pub fn map(&self) -> &[Option<usize>] {
        &self.map
    }

    /// `|A|`.
    pub fn classes(&self) -> usize {
        self.map.len()
    }

    /// `R(a, b)`: `a`'s consequence unread, or read as `b`.
    pub fn joins(&self, antecedent: usize, consequence: usize) -> bool {
        self.map[antecedent].is_none_or(|image| image == consequence)
    }

    /// `R(F)`: every class some member of `F` admits as its consequence.
    fn forward(&self, family: &[usize]) -> Vec<usize> {
        (0..self.classes())
            .filter(|&b| family.iter().any(|&a| self.joins(a, b)))
            .collect()
    }

    /// `R⁻¹(G)`: every class that admits some member of `G` as its consequence.
    fn backward(&self, family: &[usize]) -> Vec<usize> {
        (0..self.classes())
            .filter(|&a| family.iter().any(|&b| self.joins(a, b)))
            .collect()
    }
}

/// [definition] **A damaged passage**: each cell's class, `None` where erased, over `|A|` classes,
/// with its declared opening `o` (the first station: the relation is read at `t ≥ o`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DamagedPassage {
    cells: Vec<Option<usize>>,
    classes: usize,
    opening: usize,
}

impl DamagedPassage {
    /// A passage; refused with a class outside `A` or an opening past its end.
    pub fn new(
        cells: Vec<Option<usize>>,
        classes: usize,
        opening: usize,
    ) -> Result<Self, CompressionError> {
        if let Some(&class) = cells.iter().flatten().find(|&&class| class >= classes) {
            return Err(CompressionError::IndexOutside {
                index: class,
                population: classes,
            });
        }
        if opening > cells.len() {
            return Err(CompressionError::Extent {
                what: "a passage's opening within its cells",
                expected: cells.len(),
                found: opening,
            });
        }
        Ok(Self {
            cells,
            classes,
            opening,
        })
    }

    /// The cells.
    pub fn cells(&self) -> &[Option<usize>] {
        &self.cells
    }

    /// `|A|`.
    pub fn classes(&self) -> usize {
        self.classes
    }

    /// `o`.
    pub fn opening(&self) -> usize {
        self.opening
    }

    /// The erased cells, in order.
    pub fn erased(&self) -> Vec<usize> {
        (0..self.cells.len())
            .filter(|&t| self.cells[t].is_none())
            .collect()
    }

    /// The passage with cell `t` read as `class` (a residual's patch).
    fn pinned(&self, t: usize, class: usize) -> Self {
        let mut pinned = self.clone();
        pinned.cells[t] = Some(class);
        pinned
    }
}

/// [definition] **One cell's reading after the restriction**: intact, released at width zero, or
/// held with its plural family.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CellRelease {
    Intact(usize),
    Released(usize),
    Held(Vec<usize>),
}

impl CellRelease {
    /// The cell's class, when it has one.
    pub fn class(&self) -> Option<usize> {
        match self {
            Self::Intact(class) | Self::Released(class) => Some(*class),
            Self::Held(_) => None,
        }
    }
}

/// [definition] **The restriction's fixed point** (module header): every cell's family, the sweeps
/// it took (the last changes nothing), and the passage and relation it read.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Restriction {
    families: Vec<Vec<usize>>,
    sweeps: u64,
    passage: DamagedPassage,
    relation: PairRelation,
}

/// **Restrict a damaged passage through a pair relation** (module header), jointly from both
/// sides until no family changes. Refused when the relation's classes are not the passage's, or
/// when a family empties: the key does not fit the passage at that cell.
pub fn restrict(
    passage: &DamagedPassage,
    relation: &PairRelation,
) -> Result<Restriction, CompressionError> {
    if relation.classes() != passage.classes {
        return Err(CompressionError::Extent {
            what: "a pair relation over the passage's classes",
            expected: passage.classes,
            found: relation.classes(),
        });
    }
    let length = passage.cells.len();
    let delta = relation.offset;
    let mut families: Vec<Vec<usize>> = passage
        .cells
        .iter()
        .map(|cell| match cell {
            Some(class) => vec![*class],
            None => (0..passage.classes).collect(),
        })
        .collect();
    let joined = |to: usize| to < length && to >= passage.opening && to >= delta;
    let mut sweeps = 0u64;
    loop {
        sweeps += 1;
        let mut changed = false;
        // One sweep runs through the passage forward and then back: the antecedent's side carries
        // along the clock, the consequent's against it.
        for t in (0..length).chain((0..length).rev()) {
            let mut family = families[t].clone();
            if joined(t) {
                let admitted = relation.forward(&families[t - delta]);
                family.retain(|class| admitted.contains(class));
            }
            if joined(t + delta) {
                let admitted = relation.backward(&families[t + delta]);
                family.retain(|class| admitted.contains(class));
            }
            if family.is_empty() {
                return Err(CompressionError::Contradicted { cell: t });
            }
            if family != families[t] {
                families[t] = family;
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }
    Ok(Restriction {
        families,
        sweeps,
        passage: passage.clone(),
        relation: relation.clone(),
    })
}

impl Restriction {
    /// Every cell's family, sorted.
    pub fn families(&self) -> &[Vec<usize>] {
        &self.families
    }

    /// The sweeps the fixed point took.
    pub fn sweeps(&self) -> u64 {
        self.sweeps
    }

    /// Whether the relation joins cell `t` to its consequent `t + δ`.
    fn joins_next(&self, t: usize) -> bool {
        let to = t + self.relation.offset;
        to < self.families.len() && to >= self.passage.opening
    }

    /// **The chains**: each maximal run of cells joined consecutively by the relation, one residue
    /// class of `ℤ/δ` at a time (a cell no edge reaches is a chain of one).
    pub fn chains(&self) -> Vec<Vec<usize>> {
        let delta = self.relation.offset;
        let mut chains = Vec::new();
        for start in 0..delta.min(self.families.len()) {
            let mut chain = vec![start];
            let mut t = start;
            while t + delta < self.families.len() {
                if !self.joins_next(t) {
                    chains.push(std::mem::take(&mut chain));
                }
                t += delta;
                chain.push(t);
            }
            chains.push(chain);
        }
        chains
    }

    /// One chain's members by class at each of its cells (forward count times backward count), and
    /// the chain's member total.
    fn chain_members(&self, chain: &[usize]) -> (Vec<Vec<BigUint>>, BigUint) {
        let classes = self.passage.classes;
        let indicator = |t: usize| -> Vec<BigUint> {
            (0..classes)
                .map(|class| {
                    if self.families[t].contains(&class) {
                        BigUint::one()
                    } else {
                        BigUint::zero()
                    }
                })
                .collect()
        };
        let step = |counts: &[BigUint], to: usize, forward: bool| -> Vec<BigUint> {
            let allowed = indicator(to);
            (0..classes)
                .map(|class| {
                    if allowed[class].is_zero() {
                        return BigUint::zero();
                    }
                    (0..classes)
                        .filter(|&other| {
                            if forward {
                                self.relation.joins(other, class)
                            } else {
                                self.relation.joins(class, other)
                            }
                        })
                        .map(|other| counts[other].clone())
                        .sum()
                })
                .collect()
        };
        let mut forward = vec![indicator(chain[0])];
        for &t in &chain[1..] {
            let next = step(forward.last().expect("a count"), t, true);
            forward.push(next);
        }
        let mut backward = vec![indicator(chain[chain.len() - 1])];
        for &t in chain[..chain.len() - 1].iter().rev() {
            let next = step(backward.last().expect("a count"), t, false);
            backward.push(next);
        }
        backward.reverse();
        let members: Vec<Vec<BigUint>> = forward
            .iter()
            .zip(&backward)
            .map(|(f, b)| f.iter().zip(b).map(|(x, y)| x * y).collect())
            .collect();
        let total = forward.last().expect("a count").iter().sum();
        (members, total)
    }

    /// **The joint fibre's size** `N`: the passages every cell of which lies in its family and every
    /// joined pair of which the relation admits; the product of the chains' totals.
    pub fn joint(&self) -> BigUint {
        self.chains()
            .iter()
            .map(|chain| self.chain_members(chain).1)
            .product()
    }

    /// **The certificate at every cell** (module header): the classes held by at least one member of
    /// the joint fibre. The restriction is certified at `t` when this equals `F_t`.
    pub fn support(&self) -> Vec<Vec<usize>> {
        let mut support = vec![Vec::new(); self.families.len()];
        if self.joint().is_zero() {
            return support;
        }
        for chain in self.chains() {
            let (members, _) = self.chain_members(&chain);
            for (position, &t) in chain.iter().enumerate() {
                support[t] = (0..self.passage.classes)
                    .filter(|&class| !members[position][class].is_zero())
                    .collect();
            }
        }
        support
    }

    /// **The release** (module header): each erased cell decided by `receiver::release` at
    /// tolerance zero on its class reading over the joint fibre, width zero exactly when its
    /// certified family is one class; intact cells as read.
    pub fn release(&self) -> Result<Vec<CellRelease>, CompressionError> {
        let support = self.support();
        let rule = DecisionRule::new(
            "the repair's commit at tolerance zero",
            WithinTolerance::Release,
            BeyondTolerance::Hold,
        );
        let law = |refusal: crate::receiver::face::WidthRefusal| {
            CompressionError::ReleaseLaw(refusal.to_string())
        };
        (0..self.families.len())
            .map(|t| {
                if let Some(class) = self.passage.cells[t] {
                    return Ok(CellRelease::Intact(class));
                }
                let family = &self.families[t];
                let certified = support[t] == *family;
                let (diameter, attaining, read) = if certified && family.len() == 1 {
                    (Rat::zero(), WidthWitness::Point, 1)
                } else {
                    (
                        Rat::one(),
                        WidthWitness::Pair { left: 0, right: 1 },
                        family.len().max(2),
                    )
                };
                let width = ReceiverWidth::declared(
                    format!("the repaired cell {t}"),
                    "the cell's class over the joint compatible family of the located pair",
                    DiameterNorm::Supremum,
                    diameter,
                    attaining,
                    read,
                )
                .map_err(law)?;
                let options =
                    LawfulOptions::assemble(&width, Rat::zero(), None, true).map_err(law)?;
                Ok(match release(&rule, &options).map_err(law)? {
                    ReleaseReturn::Released { .. } => CellRelease::Released(family[0]),
                    _ => CellRelease::Held(family.clone()),
                })
            })
            .collect()
    }
}

/// The first held cell of a release, with its family.
fn first_held(releases: &[CellRelease]) -> Option<(usize, &[usize])> {
    releases.iter().enumerate().find_map(|(t, release)| match release {
        CellRelease::Held(family) => Some((t, family.as_slice())),
        _ => None,
    })
}

/// **The key's code** (module header): `δ − 1` in `⌈log₂(d − 1)⌉` bits, then each class's
/// consequence (`|A|` for unread) in `⌈log₂(|A| + 1)⌉` bits. Refused when `δ ≥ d`.
pub fn key_code(relation: &PairRelation, period: usize) -> Result<Vec<bool>, CompressionError> {
    if relation.offset >= period {
        return Err(CompressionError::IndexOutside {
            index: relation.offset,
            population: period,
        });
    }
    let classes = relation.classes();
    let mut code = Vec::new();
    write_index(&mut code, relation.offset - 1, ceil_log2(&BigUint::from(period - 1)));
    let width = ceil_log2(&BigUint::from(classes + 1));
    for image in &relation.map {
        write_index(&mut code, image.unwrap_or(classes), width);
    }
    Ok(code)
}

/// **Read a key's code** back ([`key_code`]) over `|A|` classes and the period `d`.
pub fn read_key(
    code: &mut impl Iterator<Item = bool>,
    classes: usize,
    period: usize,
) -> Result<PairRelation, CompressionError> {
    let offset = read_index(code, ceil_log2(&BigUint::from(period - 1)), period - 1)? + 1;
    let width = ceil_log2(&BigUint::from(classes + 1));
    let map = (0..classes)
        .map(|_| {
            let image = read_index(code, width, classes + 1)?;
            Ok((image < classes).then_some(image))
        })
        .collect::<Result<Vec<_>, CompressionError>>()?;
    PairRelation::new(offset, map)
}

/// **The residual's code** for one passage (module header): while a cell is held, the truth's
/// index in the first held cell's family in `⌈log₂ |F_t|⌉` bits, that cell pinned and the
/// restriction re-run. The coder holds the truth; refused when the truth leaves a family
/// (the key does not fit it) or a released cell differs from it.
pub fn residual_code(
    truth: &[usize],
    passage: &DamagedPassage,
    relation: &PairRelation,
) -> Result<Vec<bool>, CompressionError> {
    if truth.len() != passage.cells.len() {
        return Err(CompressionError::Extent {
            what: "the truth over the passage's cells",
            expected: passage.cells.len(),
            found: truth.len(),
        });
    }
    let mut code = Vec::new();
    let mut current = passage.clone();
    loop {
        let releases = restrict(&current, relation)?.release()?;
        let Some((t, family)) = first_held(&releases) else {
            let reopened: Vec<Option<usize>> = releases.iter().map(CellRelease::class).collect();
            if reopened.iter().zip(truth).any(|(class, truth)| *class != Some(*truth)) {
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
        current = current.pinned(t, truth[t]);
    }
}

/// **Reopen a damaged passage** from its key and its residual (Lean `Transition.reopen`): the
/// restriction, and while a cell is held, its patch read from the residual, pinned and the
/// restriction re-run. Reads exactly the bits [`residual_code`] wrote.
pub fn reopen(
    passage: &DamagedPassage,
    relation: &PairRelation,
    residual: &mut impl Iterator<Item = bool>,
) -> Result<Vec<usize>, CompressionError> {
    let mut current = passage.clone();
    loop {
        let releases = restrict(&current, relation)?.release()?;
        let Some((t, family)) = first_held(&releases) else {
            return Ok(releases
                .iter()
                .map(|release| release.class().expect("no cell is held"))
                .collect());
        };
        let index = read_index(residual, ceil_log2(&BigUint::from(family.len())), family.len())?;
        current = current.pinned(t, family[index]);
    }
}

#[cfg(test)]
mod tests;

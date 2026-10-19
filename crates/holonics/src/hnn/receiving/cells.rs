//! **The release at class grain: the receiver's scored family decided cell by cell** (the
//! integrated design's second loop, L2; the release redesign of October 15; #73, #148, #386).
//!
//! [definition; agent-inferred, October 16] **What a release emits is decided by the one decision
//! law on the face the receiver scores.** The receiver scores a cell by its population over the
//! landmark tree's face and the combined face (`hnn::receiving::score`, ruling A): phase `j` reads
//! `q_j(c) = Σ_f w_f P_(f,j)(c | c_<j)`, the tree read at the address after the epoch's earlier
//! cells and the population after receiving them. The release reads that same family, so
//!
//! ```text
//! P_release(c_j | c_<j) = P_scored(c_j | c_<j)                     the release reads the scored face
//! c_j = inverseCDF_(q_j)(u_j)                                      the draw arm, one declared key a cell
//! c_j = the one class whose lower bound exceeds every other's upper  the commit arm (a unique answer)
//! ```
//!
//! and the classes it releases are received by the local population exactly as the scorer receives
//! a target (`ReceivingStep::faces`), so the next phase reads the scorer's next face. Both arms are
//! [`crate::receiver::release`]'s ([`draw`], [`commit`]), decided through its `release` at
//! tolerance zero: nothing here decides.
//!
//! [definition; agent-inferred, October 16] **Demand refinement: refine, never loosen.** A class's
//! scored face is an exact enclosure: the tree's face is a dyadic point, the combined face's mass
//! lies in `ℚ(θ)` and is read through its real chart at the reading bits, and the population's
//! weights are kept at its precision. A key the enclosure straddles is not forced into a class: the
//! combined face is read again at the bits the decision demands, doubling from the declared reading
//! bits (`ratio::exponentiated::READING_BITS`) to the population's kept precision
//! (`receiver::population::PRECISION`), past which a finer chart reading cannot narrow the
//! population's face. Each finer reading nests inside the coarser (`PhaseField::enclosure_at`).
//! At that declared grain a straddle that remains is `Unresolved`, with its crossing classes and
//! their exact bounds; a commit whose enclosure leaves two classes maximal is `Hold`. The tolerance
//! is never widened, and the release teaches nothing: no deposit reads it.
//!
//! [definition; agent-inferred, October 16] **One key a cell.** The redesign reads one key through
//! nested intervals, `u_(j+1) = (u_j − F(c_j))/p(c_j)`. Over an enclosed face the cell `F(c_j)`,
//! `p(c_j)` is itself only enclosed, so that residual would depend on the depth at which each earlier
//! cell was certified. The cells instead read independent keys of the declared stream: the key of
//! an epoch is the point `(u_0, …, u_(A−1))` of `[0, 1)^A`, and the placement `w` owns the box
//! `Π_j [F_j(c_j), F_j(c_j) + p_j(c_j))`, whose volume is `P_scored(w)`, the nested intervals'
//! measure in the product chart. A fixed key stream then gives the identical release at every
//! demand depth. Each drawn cell returns its certified cell `[prior_upper, through_lower)`, inside
//! its true cell, so the certified mass `Π_j (through_lower − prior_upper)` is at most
//! `P_scored(w)`, and equals it on a point face ([`CellRelease::certified_mass`]).
//!
//! The computational object is the helical pair interaction read at the receiving port. Of the
//! winding guide's six general objects this owner touches **faces and placement** (each class's
//! scored face and the released placement) and the **tower thread** (the demand refinement is a
//! restriction of the real chart to a finer grain, and phase `j` reads the restriction after the
//! epoch's earlier cells); the helix, the pair, the cell holonomy and the tube stay attached through
//! the receiving phases and the combined face's own owners.
//!
//! | Lean | Rust |
//! |---|---|
//! | `Compression/Landmark/Context/Population.{certified_inverseCDF_class, certified_draw_is_released_at_zero_tolerance, plural_draw_is_held}` | the draw arm ([`draw`]) |
//! | `Compression/Landmark/Context/Population.population_mixture_enclosed` | the scored face read ([`PortPopulation::face_of`]) |
//! | owed (#62): the release reads the scorer's face (`P_release = P_scored`), and the class commit's certificate | [`release_cells`], [`commit`] |

use num_traits::One;

use crate::compression::landmark::context::LandmarkFace;
use crate::hnn::HnnError;
use crate::hnn::pending::Against;
use crate::hnn::ratio::Face;
use crate::ratio::Rat;
use crate::ratio::algebraic::ExactInterval;
use crate::ratio::exponentiated::READING_BITS;
use crate::receiver::population::{PRECISION, PortPopulation};
use crate::receiver::release::{DrawRefusal, KeyStream, ReleaseReturn, commit, draw};

use super::{face_enclosure, face_enclosure_at, population_refusal};

/// **The arm a release at class grain decides by.**
#[derive(Debug)]
pub enum CellLaw<'k> {
    /// The commit of a unique answer (an answer, an action with a consequence): no key.
    Commit,
    /// The certified draw: each cell reads the declared stream's next key.
    Draw(&'k mut KeyStream),
}

/// Exterior evidence of the complete producing operands of a scored face, before reception.
/// Equality certifies the same face expression, not merely overlapping numerical bounds.
/// Unequal operands do not by themselves prove different probabilities. No receipt is fed
/// back into the population, the release law or the key stream.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ScoredFaceReading {
    pub population: PortPopulation,
    pub tree_probabilities: Vec<Rat>,
    pub combined: Face,
}

impl ScoredFaceReading {
    pub(super) fn new(population: &PortPopulation, tree: &LandmarkFace, combined: &Face) -> Self {
        Self {
            population: population.clone(),
            tree_probabilities: tree.probabilities.clone(),
            combined: combined.clone(),
        }
    }

    /// Re-read these immutable operands at a common explicit precision. This does not draw,
    /// receive a class, update a chart or consume a key.
    pub fn masses_at(&self, bits: u32) -> Result<Vec<ExactInterval>, HnnError> {
        (0..self.tree_probabilities.len())
            .map(|class| {
                scored_mass(
                    &self.population,
                    &self.tree_probabilities,
                    &self.combined,
                    class,
                    bits,
                )
            })
            .collect()
    }
}

/// **One cell's decision.**
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CellDecision {
    /// The receiving phase.
    pub phase: usize,
    /// The arm's return: `Released` or `Hold` (the commit), `Drawn` or `Unresolved` (the draw), or
    /// `NoContinuationBridges` when the declared key stream has no key left.
    pub release: ReleaseReturn,
    /// The released class, or the plural classes kept: the ones that may be maximal (a commit's
    /// hold) or the ones whose cells cross the key (an unresolved draw).
    pub classes: Vec<usize>,
    /// The key the cell read, with its index in the declared stream (the draw arm).
    pub key: Option<(usize, Rat)>,
    /// The demand depth that decided it: the bits the combined face's real chart was read at.
    pub bits: u32,
    /// Every class's scored face at that depth, before this cell is received.
    pub face: Vec<ExactInterval>,
    /// Exact producing operands; absent only when no key permits a face decision.
    pub scored_face: Option<ScoredFaceReading>,
}

impl CellDecision {
    /// The class the cell released, if it released one.
    pub fn class(&self) -> Option<usize> {
        match (&self.release, self.classes.as_slice()) {
            (ReleaseReturn::Released { .. }, [class]) => Some(*class),
            (ReleaseReturn::Drawn(certified), _) => Some(certified.class),
            _ => None,
        }
    }
}

/// **A release at class grain**: its cells in phase order, through the first that emits nothing.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CellRelease {
    /// The decided cells.
    pub cells: Vec<CellDecision>,
    /// The epoch's aperture.
    pub aperture: usize,
}

impl CellRelease {
    /// The released placement, when every phase released.
    pub fn classes(&self) -> Option<Vec<usize>> {
        if self.cells.len() != self.aperture {
            return None;
        }
        self.cells.iter().map(CellDecision::class).collect()
    }

    /// **The certified mass of a drawn placement**, `Π_j (through_lower − prior_upper)`: the volume
    /// of the key box every key of which releases it, at most `P_scored(w)` and equal to it on a point
    /// face. None unless every phase was drawn.
    pub fn certified_mass(&self) -> Option<Rat> {
        if self.cells.len() != self.aperture {
            return None;
        }
        self.cells
            .iter()
            .map(|cell| match &cell.release {
                ReleaseReturn::Drawn(certified) => {
                    Some(&certified.through_lower - &certified.prior_upper)
                }
                _ => None,
            })
            .try_fold(Rat::one(), |mass, width| width.map(|width| mass * width))
    }
}

/// **The demand ladder**: the reading bits a straddled cell is read at in turn, doubling from the
/// declared reading bits and ending at the population's kept precision (module header).
pub fn demand_ladder() -> Vec<u32> {
    let last = u32::try_from(PRECISION).expect("the population's precision fits u32");
    let mut ladder = vec![READING_BITS];
    while let Some(&bits) = ladder.last() {
        if bits >= last {
            break;
        }
        ladder.push((2 * bits).min(last));
    }
    ladder
}

/// One class's scored face: the population's face over the tree's point face and the combined
/// face's enclosure at `bits`, in the receiver's family order (`TREE`, `COMBINED`).
fn scored_face(
    population: &PortPopulation,
    tree: &LandmarkFace,
    combined: &Face,
    class: usize,
    bits: u32,
) -> Result<ExactInterval, HnnError> {
    scored_mass(population, &tree.probabilities, combined, class, bits)
}

fn scored_mass(
    population: &PortPopulation,
    tree: &[Rat],
    combined: &Face,
    class: usize,
    bits: u32,
) -> Result<ExactInterval, HnnError> {
    let point = tree.get(class).ok_or(HnnError::CellOutside {
        code: class,
        alphabet: tree.len(),
    })?;
    population
        .face_of(&[
            ExactInterval::point(point.clone()),
            face_enclosure_at(combined, class, bits)?,
        ])
        .map_err(population_refusal)
}

fn draw_refusal(refusal: DrawRefusal) -> HnnError {
    HnnError::Unadmitted {
        reason: match refusal {
            DrawRefusal::EmptyFace => "a scored face with at least one class",
            DrawRefusal::InvalidNormalization { .. } => "a scored face enclosing a normalized face",
            DrawRefusal::KeyOutOfRange { .. } | DrawRefusal::KeyWidth => "a declared key in [0, 1)",
            DrawRefusal::Law(_) => "the release law's own decision at tolerance zero",
            _ => "a scored face's bounds ordered inside [0, 1]",
        },
    }
}

/// **Release an epoch at class grain** (module header): phase by phase, the scored face of every
/// class read at the demanded depth, decided by the declared arm, and a released class received by
/// the local population as the scorer receives a target. `against_at(known)` returns the epoch's
/// combined and tree faces with the earlier released classes known (`PendingRatio::against`); phase
/// `j` reads its own. The population is the receiver's (`ConstitutionRead::population`), cloned.
/// Refused at a face of the wrong shape; a straddle at the declared grain, a held commit and a key
/// stream that ran out are decisions, returned as the epoch's last cell.
pub fn release_cells(
    population: &PortPopulation,
    aperture: usize,
    mut against_at: impl FnMut(&[usize]) -> Result<Against, HnnError>,
    mut law: CellLaw<'_>,
) -> Result<CellRelease, HnnError> {
    let ladder = demand_ladder();
    let mut local = population.clone();
    let mut released: Vec<usize> = Vec::with_capacity(aperture);
    let mut cells = Vec::with_capacity(aperture);
    for phase in 0..aperture {
        let against = against_at(&released)?;
        let (Some(combined), Some(tree)) =
            (against.faces.faces.get(phase), against.trees.get(phase))
        else {
            return Err(HnnError::Shape {
                what: "one combined face and one tree face per receiving phase",
                expected: aperture,
                found: against.faces.faces.len().min(against.trees.len()),
            });
        };
        let alphabet = combined.cells().len();
        if tree.probabilities.len() != alphabet {
            return Err(HnnError::Shape {
                what: "the tree face's classes against the combined face's",
                expected: alphabet,
                found: tree.probabilities.len(),
            });
        }
        let key = match &mut law {
            CellLaw::Commit => None,
            CellLaw::Draw(keys) => {
                let index = keys.keys_read();
                match keys.next_key() {
                    Some(key) => Some((index, key)),
                    None => {
                        cells.push(CellDecision {
                            phase,
                            release: ReleaseReturn::NoContinuationBridges {
                                reason: "the declared key stream has no key left".to_owned(),
                            },
                            classes: Vec::new(),
                            key: None,
                            bits: READING_BITS,
                            face: Vec::new(),
                            scored_face: None,
                        });
                        break;
                    }
                }
            }
        };
        let mut decided: Option<CellDecision> = None;
        for &bits in &ladder {
            let face = (0..alphabet)
                .map(|class| scored_face(&local, tree, combined, class, bits))
                .collect::<Result<Vec<_>, HnnError>>()?;
            let (release, classes) = match &key {
                None => {
                    let committed = commit(&face).map_err(draw_refusal)?;
                    (committed.release, committed.classes)
                }
                Some((_, key)) => {
                    let drawn = draw(&face, key).map_err(draw_refusal)?;
                    let classes = match &drawn {
                        ReleaseReturn::Drawn(certified) => vec![certified.class],
                        ReleaseReturn::Unresolved(unresolved) => {
                            unresolved.crossings.iter().map(|c| c.class).collect()
                        }
                        _ => Vec::new(),
                    };
                    (drawn, classes)
                }
            };
            let emits = matches!(
                release,
                ReleaseReturn::Released { .. } | ReleaseReturn::Drawn(_)
            );
            decided = Some(CellDecision {
                phase,
                release,
                classes,
                key: key.clone(),
                bits,
                face,
                scored_face: Some(ScoredFaceReading::new(&local, tree, combined)),
            });
            if emits {
                break;
            }
        }
        let cell = decided.expect("the demand ladder holds the declared reading bits");
        let class = cell.class();
        cells.push(cell);
        let Some(class) = class else {
            break;
        };
        // The released class is received as the scorer receives a target (`score`): the tree's
        // point face and the combined face at the declared reading bits.
        local
            .receive(&[
                ExactInterval::point(tree.probabilities[class].clone()),
                face_enclosure(combined, class)?,
            ])
            .map_err(population_refusal)?;
        released.push(class);
    }
    Ok(CellRelease { cells, aperture })
}

#[cfg(test)]
mod tests;

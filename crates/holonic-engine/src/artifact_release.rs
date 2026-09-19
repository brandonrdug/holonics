//! **T3 — release over an edited artifact family.**
//!
//! [definition] This module is the executable owner of item **T3** of
//! `docs/plans/THE_TUBE_CARRIES_RELEASE_THROUGH_NECKS_FOLDS_AND_JUNCTIONS.md`. Its Lean
//! counterpart is
//! `formal/elementary-holonics/ElementaryHolonics/Transport/ArtifactRelease.lean`
//! (namespace `Soma.Holonics.Transport.ArtifactRelease`), and the correspondence is the
//! deliverable:
//!
//! | Lean | Rust |
//! |---|---|
//! | `Artifact`, `Region`, `AgreeOn` | [`Artifact`], [`Region`], [`Region::agree_on`] |
//! | `Releasable` | [`ArtifactFamily::region_released`] |
//! | `step`, `stepMulti` | [`step`] over a [`Swing`], single-branch or many |
//! | `SupportedOff`, `SupportedOffMulti` | [`Swing::support`] and [`Swing::check_support`] |
//! | `release_preserved_by_edit_supported_off` | `release_is_preserved_by_an_edit_supported_off_the_region` |
//! | `release_preserved_by_swing_supported_off` | `release_is_preserved_by_a_many_branch_swing_supported_off_the_region` |
//! | `an_edit_supported_off_a_released_region_cannot_change_its_face` | `an_edit_off_the_region_cannot_change_its_released_face` |
//! | `reopening_from_outside_is_an_emptying` | `reopening_a_released_region_from_outside_is_an_emptying` |
//! | `only_an_edit_touching_the_region_can_change_its_face` | `only_an_edit_on_the_region_changes_its_face` |
//! | `restriction_never_widens` | `pure_restriction_never_widens_the_section` |
//! | `width_is_not_monotone_along_edits`, `the_swing_enlarges_the_family` | `the_swing_widens_the_cross_section_and_width_is_not_monotone_along_edits` |
//! | `releasable_iff_every_coordinate_width_is_zero` | [`ArtifactFamily::region_width`], which **is** `receiver_release::width_enumerated` |
//! | `regionTower` | [`RegionTower`], [`RegionFace`] |
//! | `positionwise` | [`EditAction::is_chartwise`] |
//! | `rotationTube` | [`RevisionCircuit`] |
//! | `the_rotation_tube_carries_no_holonomy` | [`circuit_holonomy`], `a_circuit_whose_intentions_cancel_returns_the_identity` |
//! | `the_entangled_edit_is_not_chartwise` | [`check_commuting_square`] on [`RevisionCircuit`], `the_entangled_edit_fails_the_two_axis_square` |
//! | `the_commutator_of_the_entangled_pair_is_a_translation` | `the_commutator_of_the_entangled_pair_is_a_translation` |
//! | `the_commutator_circuit_has_a_defect` | [`circuit_holonomy`], `a_circuit_with_a_residual_returns_its_holonomy` |
//! | `windingCircuit`, `the_two_edit_circuits_commute` | [`EditTorus`], [`EditTorus::winding`] |
//! | `periplus`, `periplusResidual`, `residual_empty_iff_the_draft_returns` | [`periplus_residual`], [`PeriplusResidual`] |
//! | `CircuitOutcome` | [`CircuitOutcome`], [`StopReplaying`] |
//! | `no_defect_on_a_declared_face_is_not_cancellation` | [`CircuitOutcome::NoDefectWithinBound`] |
//! | `Disposition`, `dispositionOf` | [`ArtifactDisposition`], [`disposition`] |
//! | `no_candidate_carries_the_disposition` | `no_candidate_carries_the_disposition` |
//! | `EditableDraft`, `IrrevocableUtterance` | [`EditableDraft`], [`IrrevocableUtterance`] |
//! | `no_sequence_of_corrections_retracts` | `no_sequence_of_corrections_changes_the_committed_boundary` |
//! | `draftRung` | [`draft_rung`] |
//! | `Foundation/ReceiverRelease.lean::Horizon` (T5, adopted) | [`ArtifactFamily::region_width_at`], [`ArtifactFamily::index_distance`], [`ArtifactFamily::horizon_of`] |
//!
//! # The object
//!
//! [definition] An [`Artifact`] is an exact assignment of integer token codes to declared
//! positions. A [`Region`] is a set of positions and `π_B` is [`RegionTower`]'s own `restrict`. A
//! family is carried **enumerated** ([`EnumeratedFamily`]) or **enclosed**
//! ([`EnclosedFamily`], a per-position admitted set whose cardinality is an exact `BigUint`
//! product and is never materialized). With `g` a [`Swing`] and `C` a [`Constraint`],
//!
//! ```text
//! F_{k+1} = T_{g_k}(F_k) ∩ C_k
//! ```
//!
//! is [`step`]: longitudinal transport, then transverse restriction. The visible draft is one
//! member, never the state.
//!
//! # The cross-section shrinks and widens
//!
//! [implemented-exact] A swing may carry one artifact to several admitted results, so the family
//! can **grow**: `the_swing_widens_the_cross_section` exhibits a one-member family whose name
//! region has width `0` becoming a two-member family whose name region has width `1`. Pure
//! restriction is the monotone half — `pure_restriction_never_widens_the_section` is
//! `receiver_release`'s `width_mono` at the constraint, cited and not rebuilt.
//!
//! # Release, and what a later edit can do to it
//!
//! [implemented-exact] A region is released when its width is zero, which is
//! `receiver_release::width_enumerated` at a [`RegionReading`]; inside a declared tolerance it is
//! that owner's `Releasable`. An edit whose **checked** support misses the region cannot change
//! its released face, so a later edit supported elsewhere either leaves the face standing or
//! empties the family: [`StepOutcome::Emptied`] is the only reopening, and the resolution is an
//! edit supported *on* the region — a correction.
//!
//! # Three different relations, not one
//!
//! [established-bounded] "Independent versus entangled" is three relations and this module keeps
//! them apart. [`commutator_verdict`] decides order-immateriality exactly on a finite family.
//! [`EditAction::is_chartwise`] and [`check_commuting_square`] decide chartwise locality — an edit
//! that reads another position admits no chartwise transport and exhibits a
//! [`SquareVerdict::Defect`] at the region that cannot see its trigger. And **constraint
//! entanglement** is neither: `dog → cat` and `is → why` are both positionwise substitutions at
//! distinct slots, so both commute and both are chartwise; only the admitted role constraint
//! separates them.
//!
//! # No floats, and every declared size is bounded before it is used
//!
//! [implemented-exact] Tokens are `u32` codes, widths and tolerances are exact `Rat`
//! (`BigRational`), windings are `BigInt` and cardinalities are `BigUint`. No `f32`/`f64` appears
//! anywhere in this module. Every caller-declared extent — artifact length, family size, swing
//! branch count, edit-word length, circuit length, history length and their products — is checked
//! with checked arithmetic against a named ceiling **before** the allocation or loop it sizes, and
//! exceeding one is a typed [`ArtifactRefusal`], never a panic.
//!
//! # This is an illustration of the law, not a language model
//!
//! [definition] The six-slot object in the tests is a **role frame**: six declared positions, a
//! handful of exact token codes and two decidable role-agreement constraints. It illustrates the
//! law; it is not a model of English, of grammar or of meaning, and no statistic, corpus or
//! learned parameter appears anywhere in this module.

use std::collections::{BTreeMap, BTreeSet};

use num_bigint::{BigInt, BigUint};
use num_traits::{One, Zero};
use relational_geometry::Rat;
use serde::Serialize;
use thiserror::Error;

use crate::continuing_tower::{Tower, TowerFaceOutcome, TowerRefusal};
use crate::continuing_tube::{
    HolonomyVerdict, SquareVerdict, StationedTower, TubeOutcome, TubeRefusal,
    check_circuit_holonomy, check_commuting_square,
};

use crate::receiver_release::{
    CompatibleFamily, DecisionLaw, DiameterNorm, ExactFace, Horizon, LawfulOptions, Reading,
    ReceiverWidth, ReleaseReturn, WidthRefusal, release, width_enumerated, width_over_readings,
};
use crate::relation_ladder::Rung;

// -------------------------------------------------------------------------------------------
// Declared ceilings
// -------------------------------------------------------------------------------------------

/// The longest artifact a caller may declare.
pub const POSITION_CEILING: usize = 1024;
/// The largest admitted token set one position of an enclosure may declare.
pub const ALPHABET_CEILING: usize = 1 << 16;
/// The largest enumerated family a caller may declare.
pub const FAMILY_CEILING: usize = 4096;
/// The largest number of admitted results one swing may declare.
pub const SWING_BRANCH_CEILING: usize = 64;
/// The longest edit word a caller may declare.
pub const EDIT_WORD_CEILING: usize = 256;
/// The longest declared revision circuit.
pub const CIRCUIT_CEILING: usize = 256;
/// The largest `family × branches × positions` product one [`step`] may perform.
pub const STEP_WORK_CEILING: usize = 1 << 22;
/// The longest route history a loop search may carry.
pub const ROUTE_HISTORY_CEILING: usize = 1024;
/// The largest number of rules one declared constraint may carry.
pub const CONSTRAINT_RULE_CEILING: usize = 256;
/// The largest probe a support claim may be checked over.
pub const SUPPORT_PROBE_CEILING: usize = 1024;

/// The product of declared extents, or `None` when it overflows the machine integer counting it.
fn declared_work(factors: &[usize]) -> Option<usize> {
    factors
        .iter()
        .try_fold(1usize, |carried, factor| carried.checked_mul((*factor).max(1)))
}

// -------------------------------------------------------------------------------------------
// Typed refusals
// -------------------------------------------------------------------------------------------

/// Every way this module declines to answer. A refusal is content; nothing here panics.
#[derive(Clone, Debug, PartialEq, Eq, Error)]
pub enum ArtifactRefusal {
    /// An artifact with no position carries no face.
    #[error("an artifact of zero positions carries no face")]
    EmptyArtifact,
    /// A declared extent exceeded its named ceiling. Nothing was allocated.
    #[error("{what} declared {declared}, above the ceiling {ceiling}; nothing was allocated")]
    DeclarationAboveCeiling {
        /// What was declared.
        what: &'static str,
        /// The declared extent.
        declared: usize,
        /// The ceiling it exceeded.
        ceiling: usize,
    },
    /// The work a declaration asks for does not fit the machine integer counting it.
    #[error("the work {what} asks for overflows the machine integer counting it; nothing ran")]
    WorkOverflows {
        /// What was declared.
        what: &'static str,
    },
    /// A position outside the declared artifact length.
    #[error("position {position} lies outside an artifact of {length} positions")]
    PositionOutsideArtifact {
        /// The position asked for.
        position: usize,
        /// The declared length.
        length: usize,
    },
    /// Two declared lengths do not agree.
    #[error("an artifact of {declared} positions does not pair with one of {found}")]
    LengthMismatch {
        /// What was declared.
        declared: usize,
        /// What was found.
        found: usize,
    },
    /// An enumerated family with no member has no width.
    #[error("an artifact family with no member has no width and no released face")]
    EmptyFamily,
    /// A declared cyclic alphabet of modulus zero.
    #[error("the edit {edit:?} declares a cyclic alphabet of modulus zero, which has no rotation")]
    ZeroModulus {
        /// The edit that declared it.
        edit: String,
    },
    /// A swing with no branch transports nothing.
    #[error("the swing {swing:?} declares no admitted result, so it transports nothing")]
    EmptySwing {
        /// The swing that declared it.
        swing: String,
    },
    /// A support claim was offered with no artifact to check it on.
    #[error("the swing {swing:?} offers a support claim over an empty probe; a claim checked on no artifact is not a checked claim")]
    EmptySupportProbe {
        /// The swing.
        swing: String,
    },
    /// A declared support claim is refuted by an exhibited artifact and position.
    #[error(
        "the swing {swing:?} claims support {claimed:?} and writes position {position} on the \
         probe, so the claim is refused rather than repaired"
    )]
    SupportClaimRefuted {
        /// The swing.
        swing: String,
        /// The support it claimed.
        claimed: Vec<usize>,
        /// The position it actually wrote.
        position: usize,
    },
    /// A non-positionwise constraint was applied to an enclosure.
    #[error(
        "the constraint {constraint:?} couples positions {left} and {right}, so it does not act \
         positionwise on an enclosure; enumerate the family or declare a positionwise constraint"
    )]
    ConstraintNotPositionwiseOnEnclosure {
        /// The constraint.
        constraint: String,
        /// The first coupled position.
        left: usize,
        /// The second.
        right: usize,
    },
    /// Restricting an enclosure left a position with no admitted token.
    #[error("restricting the enclosure left position {position} with no admitted token")]
    EnclosureEmptied {
        /// The position that emptied.
        position: usize,
    },
    /// An enclosure position declared no admitted token at all.
    #[error("position {position} of the declared enclosure admits no token")]
    EmptyEnclosurePosition {
        /// The position.
        position: usize,
    },
    /// The width owner refused.
    #[error(transparent)]
    Width(#[from] WidthRefusalBox),
    /// A declared two-axis horizon's index coordinate is not the region's own distance from the
    /// whole-artifact chart.
    #[error(
        "the declared horizon reaches {declared} steps through the index, and the region {region:?}          sits {actual} steps from the whole-artifact chart; the horizon is refused rather than          silently re-declared"
    )]
    HorizonIndexMismatch {
        /// The region that was read.
        region: Vec<usize>,
        /// The index coordinate the caller declared.
        declared: usize,
        /// The region's own index distance.
        actual: usize,
    },
    /// A region reading was asked of an enclosed family, which carries no enumerated members.
    #[error(
        "the region reading {receiver:?} needs an enumerated family; an enclosure is refused \
         rather than materialized"
    )]
    EnclosureHasNoEnumeratedMembers {
        /// The receiver that refused.
        receiver: String,
    },
}

/// The width owner's refusal, wrapped so that [`ArtifactRefusal`] stays `Clone` and `Eq`.
#[derive(Clone, Debug, Error)]
#[error("{0}")]
pub struct WidthRefusalBox(String);

impl PartialEq for WidthRefusalBox {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

impl Eq for WidthRefusalBox {}

impl From<WidthRefusal> for ArtifactRefusal {
    fn from(refusal: WidthRefusal) -> Self {
        Self::Width(WidthRefusalBox(refusal.to_string()))
    }
}

// -------------------------------------------------------------------------------------------
// T3 (a) — the artifact, the region and the family
// -------------------------------------------------------------------------------------------

/// One exact token code. Tokens are integer addresses into a declared vocabulary; no float and no
/// embedding participates.
pub type Token = u32;

/// **An artifact**: an exact assignment of token codes to declared positions.
///
/// Lean counterpart: `Transport/ArtifactRelease.lean::Artifact`. The field is private and the only
/// constructor is [`Artifact::declared`], which bounds the declared length before allocating.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize)]
pub struct Artifact {
    tokens: Vec<Token>,
}

impl Artifact {
    /// An artifact from a declared token vector, bounded by [`POSITION_CEILING`].
    pub fn declared(tokens: Vec<Token>) -> Result<Self, ArtifactRefusal> {
        if tokens.is_empty() {
            return Err(ArtifactRefusal::EmptyArtifact);
        }
        if tokens.len() > POSITION_CEILING {
            return Err(ArtifactRefusal::DeclarationAboveCeiling {
                what: "an artifact length",
                declared: tokens.len(),
                ceiling: POSITION_CEILING,
            });
        }
        Ok(Self { tokens })
    }

    /// The declared length.
    pub fn length(&self) -> usize {
        self.tokens.len()
    }

    /// The exact tokens, in position order.
    pub fn tokens(&self) -> &[Token] {
        &self.tokens
    }

    /// The token at one position, or a typed refusal.
    pub fn at(&self, position: usize) -> Result<Token, ArtifactRefusal> {
        self.tokens
            .get(position)
            .copied()
            .ok_or(ArtifactRefusal::PositionOutsideArtifact {
                position,
                length: self.tokens.len(),
            })
    }

    /// The artifact as an exact rational vector, which is what `receiver_release`'s readings
    /// consume. Every entry is an exact integer carried as a `Rat`; nothing is rounded.
    pub fn as_exact_vector(&self) -> Vec<Rat> {
        self.tokens
            .iter()
            .map(|token| Rat::from_integer(BigInt::from(*token)))
            .collect()
    }
}

/// **A region of an artifact**: the positions one receiver reads.
///
/// Lean counterpart: `Transport/ArtifactRelease.lean::Region`. Every position is checked against
/// the declared length at construction, so `π_B` cannot index outside the artifact.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize)]
pub struct Region {
    length: usize,
    positions: BTreeSet<usize>,
}

impl Region {
    /// A region over an artifact of declared length.
    pub fn declared(
        length: usize,
        positions: impl IntoIterator<Item = usize>,
    ) -> Result<Self, ArtifactRefusal> {
        if length == 0 {
            return Err(ArtifactRefusal::EmptyArtifact);
        }
        if length > POSITION_CEILING {
            return Err(ArtifactRefusal::DeclarationAboveCeiling {
                what: "an artifact length",
                declared: length,
                ceiling: POSITION_CEILING,
            });
        }
        // The declared iterator is caller-sized, so each element is checked **as it is inserted**
        // and the set can never grow past the artifact length. A hostile iterator is refused at
        // its first out-of-range element rather than after it has been materialized.
        let mut carried: BTreeSet<usize> = BTreeSet::new();
        for position in positions {
            if position >= length {
                return Err(ArtifactRefusal::PositionOutsideArtifact { position, length });
            }
            carried.insert(position);
        }
        Ok(Self {
            length,
            positions: carried,
        })
    }

    /// The whole artifact as one region.
    pub fn whole(length: usize) -> Result<Self, ArtifactRefusal> {
        Self::declared(length, 0..length)
    }

    /// The artifact length this region is declared over.
    pub fn length(&self) -> usize {
        self.length
    }

    /// The positions, in order.
    pub fn positions(&self) -> &BTreeSet<usize> {
        &self.positions
    }

    /// Whether this region is contained in the other. The transverse order of [`RegionTower`].
    pub fn is_contained_in(&self, other: &Self) -> bool {
        self.length == other.length && self.positions.is_subset(&other.positions)
    }

    /// **`π_B`**: the face this region reads off an artifact.
    pub fn read(&self, artifact: &Artifact) -> Result<RegionFace, ArtifactRefusal> {
        if artifact.length() != self.length {
            return Err(ArtifactRefusal::LengthMismatch {
                declared: self.length,
                found: artifact.length(),
            });
        }
        let mut values = BTreeMap::new();
        for position in &self.positions {
            values.insert(*position, artifact.at(*position)?);
        }
        Ok(RegionFace {
            region: self.clone(),
            values,
        })
    }

    /// Whether two artifacts agree on this region.
    ///
    /// Lean counterpart: `AgreeOn`.
    pub fn agree_on(&self, left: &Artifact, right: &Artifact) -> Result<bool, ArtifactRefusal> {
        Ok(self.read(left)? == self.read(right)?)
    }
}

/// The face one region presents: the assignment restricted to its positions.
///
/// Lean counterpart: `(regionTower n T).Face B`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct RegionFace {
    region: Region,
    values: BTreeMap<usize, Token>,
}

impl RegionFace {
    /// The region this face is presented at.
    pub fn region(&self) -> &Region {
        &self.region
    }

    /// The exact assignment.
    pub fn values(&self) -> &BTreeMap<usize, Token> {
        &self.values
    }

    /// How many exact entries this face carries — the population the tube checks bound their work
    /// against.
    pub fn population(&self) -> usize {
        self.values.len()
    }
}

/// **The transverse ladder of an artifact.** The face at a region is the assignment on that
/// region, and `restrict` is `π_B`.
///
/// Lean counterpart: `Transport/ArtifactRelease.lean::regionTower`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RegionTower {
    length: usize,
}

impl RegionTower {
    /// The region tower of artifacts of one declared length.
    pub fn declared(length: usize) -> Result<Self, ArtifactRefusal> {
        if length == 0 {
            return Err(ArtifactRefusal::EmptyArtifact);
        }
        if length > POSITION_CEILING {
            return Err(ArtifactRefusal::DeclarationAboveCeiling {
                what: "an artifact length",
                declared: length,
                ceiling: POSITION_CEILING,
            });
        }
        Ok(Self { length })
    }

    /// The declared artifact length.
    pub fn length(&self) -> usize {
        self.length
    }
}

impl Tower for RegionTower {
    type Index = Region;
    type Face = RegionFace;

    fn refines(&self, coarse: &Region, fine: &Region) -> bool {
        coarse.length == self.length && fine.length == self.length && coarse.is_contained_in(fine)
    }

    fn carries(&self, chart: &Region, face: &RegionFace) -> bool {
        &face.region == chart
            && chart.length == self.length
            && face.values.keys().copied().collect::<BTreeSet<_>>() == chart.positions
    }

    fn restrict(
        &self,
        coarse: &Region,
        fine: &Region,
        face: &RegionFace,
    ) -> TowerFaceOutcome<Self> {
        if !self.refines(coarse, fine) {
            return Err(TowerRefusal::NotARefinement {
                coarse: coarse.clone(),
                fine: fine.clone(),
            });
        }
        if !self.carries(fine, face) {
            return Err(TowerRefusal::FaceNotCarried {
                chart: fine.clone(),
                face: face.clone(),
            });
        }
        let mut values = BTreeMap::new();
        for position in &coarse.positions {
            match face.values.get(position) {
                Some(token) => {
                    values.insert(*position, *token);
                }
                None => {
                    return Err(TowerRefusal::FaceNotCarried {
                        chart: fine.clone(),
                        face: face.clone(),
                    });
                }
            }
        }
        Ok(RegionFace {
            region: coarse.clone(),
            values,
        })
    }
}

// -------------------------------------------------------------------------------------------
// T3 (b) — edits and swings
// -------------------------------------------------------------------------------------------

/// What one edit does. Every arm is exact and total off its trigger.
///
/// Lean counterpart: the positionwise arms are `positionwise`'s `p`; [`Self::CopyFrom`] and
/// [`Self::Conditioned`] are the entangled `shear`, which admits no chartwise migration.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(tag = "edit", rename_all = "kebab-case")]
pub enum EditAction {
    /// Set one position to a declared token.
    Set {
        /// The position written.
        position: usize,
        /// The token written.
        token: Token,
    },
    /// Substitute one token for another at a position; the identity where the token does not match.
    Substitute {
        /// The position written.
        position: usize,
        /// The token replaced.
        from: Token,
        /// The token written.
        to: Token,
    },
    /// Rotate the token at a position inside a declared cyclic alphabet — an exact rotation by a
    /// rational angle `step / modulus` of a turn.
    Rotate {
        /// The position written.
        position: usize,
        /// The cyclic alphabet's modulus.
        modulus: Token,
        /// How many steps around it.
        step: Token,
    },
    /// Copy the token at `source` into `target`. This reads a position it does not write, so it is
    /// **not** chartwise.
    CopyFrom {
        /// The position read.
        source: usize,
        /// The position written.
        target: usize,
    },
    /// Write `token` at `target` when `source` holds `trigger`. Also reads a position it does not
    /// write: the entangled move.
    Conditioned {
        /// The position read.
        source: usize,
        /// The token that triggers the rewrite.
        trigger: Token,
        /// The position written.
        target: usize,
        /// The token written.
        token: Token,
    },
}

impl EditAction {
    /// The position this action writes.
    pub fn writes(&self) -> usize {
        match self {
            Self::Set { position, .. }
            | Self::Substitute { position, .. }
            | Self::Rotate { position, .. } => *position,
            Self::CopyFrom { target, .. } | Self::Conditioned { target, .. } => *target,
        }
    }

    /// The positions this action reads.
    pub fn reads(&self) -> BTreeSet<usize> {
        match self {
            Self::Set { .. } => BTreeSet::new(),
            Self::Substitute { position, .. } | Self::Rotate { position, .. } => {
                BTreeSet::from([*position])
            }
            Self::CopyFrom { source, target } => BTreeSet::from([*source, *target]),
            Self::Conditioned { source, target, .. } => BTreeSet::from([*source, *target]),
        }
    }

    /// **Whether the action is chartwise**: whether the value it writes at a position depends only
    /// on the old value at that same position.
    ///
    /// Lean counterpart: `positionwise` is a `ChartwiseMigration` and
    /// `the_entangled_edit_is_not_chartwise` is the refutation for the other arms.
    pub fn is_chartwise(&self) -> bool {
        let written = self.writes();
        self.reads().iter().all(|position| *position == written)
    }

    fn apply_in_place(&self, tokens: &mut [Token], name: &str) -> Result<(), ArtifactRefusal> {
        let length = tokens.len();
        for position in self.reads().iter().chain(std::iter::once(&self.writes())) {
            if *position >= length {
                return Err(ArtifactRefusal::PositionOutsideArtifact {
                    position: *position,
                    length,
                });
            }
        }
        match self {
            Self::Set { position, token } => tokens[*position] = *token,
            Self::Substitute { position, from, to } => {
                if tokens[*position] == *from {
                    tokens[*position] = *to;
                }
            }
            Self::Rotate {
                position,
                modulus,
                step,
            } => {
                if *modulus == 0 {
                    return Err(ArtifactRefusal::ZeroModulus {
                        edit: name.to_owned(),
                    });
                }
                let carried = u64::from(tokens[*position]) + u64::from(*step);
                // `modulus` is nonzero and both operands are `u32` widened to `u64`, so the
                // remainder fits `u32` without truncation.
                tokens[*position] = (carried % u64::from(*modulus)) as Token;
            }
            Self::CopyFrom { source, target } => tokens[*target] = tokens[*source],
            Self::Conditioned {
                source,
                trigger,
                target,
                token,
            } => {
                if tokens[*source] == *trigger {
                    tokens[*target] = *token;
                }
            }
        }
        Ok(())
    }

    /// The action read **chartwise**: applied to a face that may not carry every position it
    /// reads. A position the face does not carry is a position the chart cannot see, and the value
    /// is left unchanged rather than invented — which is exactly why the two-axis square fails for
    /// a non-chartwise action.
    fn apply_chartwise(&self, face: &mut BTreeMap<usize, Token>, name: &str) -> Result<(), ArtifactRefusal> {
        let written = self.writes();
        if !face.contains_key(&written) {
            return Ok(());
        }
        for position in self.reads() {
            if !face.contains_key(&position) {
                return Ok(());
            }
        }
        match self {
            Self::Set { token, .. } => {
                face.insert(written, *token);
            }
            Self::Substitute { position, from, to } => {
                if face.get(position) == Some(from) {
                    face.insert(written, *to);
                }
            }
            Self::Rotate {
                position,
                modulus,
                step,
            } => {
                if *modulus == 0 {
                    return Err(ArtifactRefusal::ZeroModulus {
                        edit: name.to_owned(),
                    });
                }
                let current = face.get(position).copied().unwrap_or_default();
                let carried = u64::from(current) + u64::from(*step);
                face.insert(written, (carried % u64::from(*modulus)) as Token);
            }
            Self::CopyFrom { source, .. } => {
                let value = face.get(source).copied().unwrap_or_default();
                face.insert(written, value);
            }
            Self::Conditioned {
                source,
                trigger,
                token,
                ..
            } => {
                if face.get(source) == Some(trigger) {
                    face.insert(written, *token);
                }
            }
        }
        Ok(())
    }
}

/// **One declared edit**: a name and an action.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct Edit {
    name: String,
    action: EditAction,
}

impl Edit {
    /// Declare an edit. A rotation of modulus zero is refused by name.
    pub fn declared(name: impl Into<String>, action: EditAction) -> Result<Self, ArtifactRefusal> {
        let name = name.into();
        if let EditAction::Rotate { modulus: 0, .. } = action {
            return Err(ArtifactRefusal::ZeroModulus { edit: name });
        }
        Ok(Self { name, action })
    }

    /// The edit's declared name.
    pub fn name(&self) -> &str {
        &self.name
    }

    /// The action.
    pub fn action(&self) -> &EditAction {
        &self.action
    }

    /// Apply the edit to a whole artifact.
    pub fn apply(&self, artifact: &Artifact) -> Result<Artifact, ArtifactRefusal> {
        let mut tokens = artifact.tokens.clone();
        self.action.apply_in_place(&mut tokens, &self.name)?;
        Ok(Artifact { tokens })
    }
}

/// **A swing with sub-swings**: one edit step carrying each artifact to the finite family of
/// admitted results. A single-branch swing is an ordinary edit; a swing that opens alternatives is
/// why the tube's cross-section can widen.
///
/// Lean counterpart: `stepMulti`'s `g : Artifact n → Finset (Artifact n)`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct Swing {
    name: String,
    branches: Vec<Edit>,
}

impl Swing {
    /// Declare a swing, bounded by [`SWING_BRANCH_CEILING`] before any branch is read.
    pub fn declared(name: impl Into<String>, branches: Vec<Edit>) -> Result<Self, ArtifactRefusal> {
        let name = name.into();
        if branches.is_empty() {
            return Err(ArtifactRefusal::EmptySwing { swing: name });
        }
        if branches.len() > SWING_BRANCH_CEILING {
            return Err(ArtifactRefusal::DeclarationAboveCeiling {
                what: "a swing branch count",
                declared: branches.len(),
                ceiling: SWING_BRANCH_CEILING,
            });
        }
        Ok(Self { name, branches })
    }

    /// One edit read as a single-branch swing.
    pub fn single(edit: Edit) -> Result<Self, ArtifactRefusal> {
        let name = edit.name.clone();
        Self::declared(name, vec![edit])
    }

    /// The swing's declared name.
    pub fn name(&self) -> &str {
        &self.name
    }

    /// The admitted branches.
    pub fn branches(&self) -> &[Edit] {
        &self.branches
    }

    /// **The positions this swing writes**, taken from its branches' actions.
    ///
    /// Lean counterpart: the `B` of `SupportedOffMulti`.
    pub fn support(&self) -> BTreeSet<usize> {
        self.branches
            .iter()
            .map(|branch| branch.action.writes())
            .collect()
    }

    /// Whether the support misses a declared region.
    pub fn is_supported_off(&self, region: &Region) -> bool {
        self.support().is_disjoint(&region.positions)
    }

    /// **Check the support claim on a declared probe family** rather than assume it. A branch that
    /// writes a position outside the claimed support on some member is returned by name.
    pub fn check_support(
        &self,
        claimed: &BTreeSet<usize>,
        probe: &[Artifact],
    ) -> Result<(), ArtifactRefusal> {
        // A claim checked on no artifact is not a checked claim: an empty probe would pass the
        // loop below vacuously, including for the claim that the swing writes nothing at all.
        if probe.is_empty() {
            return Err(ArtifactRefusal::EmptySupportProbe {
                swing: self.name.clone(),
            });
        }
        if probe.len() > SUPPORT_PROBE_CEILING {
            return Err(ArtifactRefusal::DeclarationAboveCeiling {
                what: "a support-claim probe",
                declared: probe.len(),
                ceiling: SUPPORT_PROBE_CEILING,
            });
        }
        let length = probe.first().map_or(0, Artifact::length);
        let work = declared_work(&[probe.len(), self.branches.len(), length]).ok_or(
            ArtifactRefusal::WorkOverflows {
                what: "a support-claim check",
            },
        )?;
        if work > STEP_WORK_CEILING {
            return Err(ArtifactRefusal::DeclarationAboveCeiling {
                what: "a support-claim work product",
                declared: work,
                ceiling: STEP_WORK_CEILING,
            });
        }
        for artifact in probe {
            for branch in &self.branches {
                let after = branch.apply(artifact)?;
                for position in 0..artifact.length() {
                    if artifact.at(position)? != after.at(position)? && !claimed.contains(&position)
                    {
                        return Err(ArtifactRefusal::SupportClaimRefuted {
                            swing: self.name.clone(),
                            claimed: claimed.iter().copied().collect(),
                            position,
                        });
                    }
                }
            }
        }
        Ok(())
    }
}

// -------------------------------------------------------------------------------------------
// T3 (c) — constraints and the admitted family
// -------------------------------------------------------------------------------------------

/// One admitted receiver condition.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(tag = "rule", rename_all = "kebab-case")]
pub enum ConstraintRule {
    /// The token at one position must lie in the declared admitted set.
    Positionwise {
        /// The position constrained.
        position: usize,
        /// The admitted tokens.
        admitted: BTreeSet<Token>,
    },
    /// **A role agreement**: if `position` holds `trigger`, then `dependent` must hold `required`.
    /// This is the rule that couples two positions, and it is why `Hermes` reopens the pronoun.
    RoleAgreement {
        /// The triggering position.
        position: usize,
        /// The triggering token.
        trigger: Token,
        /// The position that must agree.
        dependent: usize,
        /// The token it must hold.
        required: Token,
    },
}

impl ConstraintRule {
    /// Whether this rule acts on one position alone.
    pub fn is_positionwise(&self) -> bool {
        matches!(self, Self::Positionwise { .. })
    }

    fn admits(&self, artifact: &Artifact) -> Result<bool, ArtifactRefusal> {
        match self {
            Self::Positionwise { position, admitted } => {
                Ok(admitted.contains(&artifact.at(*position)?))
            }
            Self::RoleAgreement {
                position,
                trigger,
                dependent,
                required,
            } => {
                if artifact.at(*position)? == *trigger {
                    Ok(artifact.at(*dependent)? == *required)
                } else {
                    Ok(true)
                }
            }
        }
    }
}

/// **The admitted constraint `C_k`**: a named conjunction of rules.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct Constraint {
    name: String,
    rules: Vec<ConstraintRule>,
}

impl Constraint {
    /// Declare a constraint. The rule count is caller-declared and is bounded against
    /// [`CONSTRAINT_RULE_CEILING`] before any rule is read or any family is filtered by it.
    pub fn declared(
        name: impl Into<String>,
        rules: Vec<ConstraintRule>,
    ) -> Result<Self, ArtifactRefusal> {
        if rules.len() > CONSTRAINT_RULE_CEILING {
            return Err(ArtifactRefusal::DeclarationAboveCeiling {
                what: "a constraint rule count",
                declared: rules.len(),
                ceiling: CONSTRAINT_RULE_CEILING,
            });
        }
        Ok(Self {
            name: name.into(),
            rules,
        })
    }

    /// The constraint that admits everything — the identity of the transverse restriction.
    pub fn unconstrained(name: impl Into<String>) -> Self {
        Self {
            name: name.into(),
            rules: Vec::new(),
        }
    }

    /// The constraint's declared name.
    pub fn name(&self) -> &str {
        &self.name
    }

    /// The rules.
    pub fn rules(&self) -> &[ConstraintRule] {
        &self.rules
    }

    /// Whether every rule acts on one position alone.
    pub fn is_positionwise(&self) -> bool {
        self.rules.iter().all(ConstraintRule::is_positionwise)
    }

    /// Whether this constraint admits an artifact.
    pub fn admits(&self, artifact: &Artifact) -> Result<bool, ArtifactRefusal> {
        for rule in &self.rules {
            if !rule.admits(artifact)? {
                return Ok(false);
            }
        }
        Ok(true)
    }
}

/// **An enumerated artifact family**: the compatible constructions, listed.
///
/// Every field is private; [`EnumeratedFamily::declared`] bounds the declared size against
/// [`FAMILY_CEILING`], forms the pair count with checked arithmetic, and refuses an empty family
/// or a member of the wrong length by name.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EnumeratedFamily {
    lineage: String,
    length: usize,
    members: Vec<Artifact>,
}

impl EnumeratedFamily {
    /// Declare a family. Members are deduplicated in a stable order, so the family is a set.
    pub fn declared(
        lineage: impl Into<String>,
        members: Vec<Artifact>,
    ) -> Result<Self, ArtifactRefusal> {
        if members.is_empty() {
            return Err(ArtifactRefusal::EmptyFamily);
        }
        if members.len() > FAMILY_CEILING {
            return Err(ArtifactRefusal::DeclarationAboveCeiling {
                what: "an artifact family size",
                declared: members.len(),
                ceiling: FAMILY_CEILING,
            });
        }
        let count = members.len();
        count
            .checked_mul(count.saturating_sub(1))
            .ok_or(ArtifactRefusal::WorkOverflows {
                what: "the unordered pairs of an artifact family",
            })?;
        let length = members[0].length();
        for member in &members {
            if member.length() != length {
                return Err(ArtifactRefusal::LengthMismatch {
                    declared: length,
                    found: member.length(),
                });
            }
        }
        let mut seen: BTreeSet<Artifact> = BTreeSet::new();
        let mut unique = Vec::with_capacity(members.len());
        for member in members {
            if seen.insert(member.clone()) {
                unique.push(member);
            }
        }
        Ok(Self {
            lineage: lineage.into(),
            length,
            members: unique,
        })
    }

    /// What this family is the family of.
    pub fn lineage(&self) -> &str {
        &self.lineage
    }

    /// The declared artifact length.
    pub fn length(&self) -> usize {
        self.length
    }

    /// The members.
    pub fn members(&self) -> &[Artifact] {
        &self.members
    }

    /// How many members.
    pub fn len(&self) -> usize {
        self.members.len()
    }

    /// Whether the family has no member. It never does: the constructor refuses one.
    pub fn is_empty(&self) -> bool {
        self.members.is_empty()
    }

    /// Whether a declared artifact is a member.
    pub fn contains(&self, artifact: &Artifact) -> bool {
        self.members.contains(artifact)
    }
}

/// **An enclosed artifact family**: a per-position admitted token set, whose members are its
/// product. The cardinality is an exact `BigUint` and is never materialized, so an enclosure of
/// astronomically many compatible artifacts costs one set per position.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EnclosedFamily {
    lineage: String,
    admitted: Vec<BTreeSet<Token>>,
}

impl EnclosedFamily {
    /// Declare an enclosure. Each position must admit at least one token, and both the position
    /// count and each admitted set are bounded before anything is allocated.
    pub fn declared(
        lineage: impl Into<String>,
        admitted: Vec<BTreeSet<Token>>,
    ) -> Result<Self, ArtifactRefusal> {
        if admitted.is_empty() {
            return Err(ArtifactRefusal::EmptyArtifact);
        }
        if admitted.len() > POSITION_CEILING {
            return Err(ArtifactRefusal::DeclarationAboveCeiling {
                what: "an artifact length",
                declared: admitted.len(),
                ceiling: POSITION_CEILING,
            });
        }
        for (position, tokens) in admitted.iter().enumerate() {
            if tokens.is_empty() {
                return Err(ArtifactRefusal::EmptyEnclosurePosition { position });
            }
            if tokens.len() > ALPHABET_CEILING {
                return Err(ArtifactRefusal::DeclarationAboveCeiling {
                    what: "an enclosure alphabet",
                    declared: tokens.len(),
                    ceiling: ALPHABET_CEILING,
                });
            }
        }
        Ok(Self {
            lineage: lineage.into(),
            admitted,
        })
    }

    /// What this enclosure is the enclosure of.
    pub fn lineage(&self) -> &str {
        &self.lineage
    }

    /// The declared artifact length.
    pub fn length(&self) -> usize {
        self.admitted.len()
    }

    /// The admitted tokens at one position.
    pub fn admitted_at(&self, position: usize) -> Result<&BTreeSet<Token>, ArtifactRefusal> {
        self.admitted
            .get(position)
            .ok_or(ArtifactRefusal::PositionOutsideArtifact {
                position,
                length: self.admitted.len(),
            })
    }

    /// **The exact cardinality**, as a `BigUint` product. Nothing is enumerated.
    pub fn cardinality(&self) -> BigUint {
        self.admitted
            .iter()
            .fold(BigUint::one(), |carried, tokens| {
                carried * BigUint::from(tokens.len())
            })
    }

    /// **Whether a region is released**: exactly when every position of the region admits one
    /// token. Decided without enumerating the family.
    pub fn region_released(&self, region: &Region) -> Result<bool, ArtifactRefusal> {
        if region.length() != self.length() {
            return Err(ArtifactRefusal::LengthMismatch {
                declared: self.length(),
                found: region.length(),
            });
        }
        for position in region.positions() {
            if self.admitted_at(*position)?.len() != 1 {
                return Ok(false);
            }
        }
        Ok(true)
    }

    /// Intersect with a declared constraint. A constraint coupling two positions does not act on
    /// an enclosure and is refused by name rather than approximated.
    pub fn restricted(&self, constraint: &Constraint) -> Result<Self, ArtifactRefusal> {
        let mut admitted = self.admitted.clone();
        for rule in constraint.rules() {
            match rule {
                ConstraintRule::Positionwise {
                    position,
                    admitted: allowed,
                } => {
                    if *position >= admitted.len() {
                        return Err(ArtifactRefusal::PositionOutsideArtifact {
                            position: *position,
                            length: admitted.len(),
                        });
                    }
                    let kept: BTreeSet<Token> = admitted[*position]
                        .intersection(allowed)
                        .copied()
                        .collect();
                    if kept.is_empty() {
                        return Err(ArtifactRefusal::EnclosureEmptied {
                            position: *position,
                        });
                    }
                    admitted[*position] = kept;
                }
                ConstraintRule::RoleAgreement {
                    position,
                    dependent,
                    ..
                } => {
                    return Err(ArtifactRefusal::ConstraintNotPositionwiseOnEnclosure {
                        constraint: constraint.name().to_owned(),
                        left: *position,
                        right: *dependent,
                    });
                }
            }
        }
        Ok(Self {
            lineage: self.lineage.clone(),
            admitted,
        })
    }
}

/// How the compatible family is carried: enumerated, or enclosed and exact.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ArtifactFamily {
    /// The members listed.
    Enumerated(EnumeratedFamily),
    /// A per-position admitted set whose product is the family.
    Enclosed(EnclosedFamily),
}

impl ArtifactFamily {
    /// The declared artifact length.
    pub fn length(&self) -> usize {
        match self {
            Self::Enumerated(family) => family.length(),
            Self::Enclosed(family) => family.length(),
        }
    }

    /// What this family is the family of.
    pub fn lineage(&self) -> &str {
        match self {
            Self::Enumerated(family) => family.lineage(),
            Self::Enclosed(family) => family.lineage(),
        }
    }

    /// The enumerated members, when the family is enumerated.
    pub fn members(&self) -> Option<&[Artifact]> {
        match self {
            Self::Enumerated(family) => Some(family.members()),
            Self::Enclosed(_) => None,
        }
    }

    /// **The exact cardinality.** For an enumerated family the member count; for an enclosure the
    /// product, formed without materializing a single member.
    pub fn cardinality(&self) -> BigUint {
        match self {
            Self::Enumerated(family) => BigUint::from(family.len()),
            Self::Enclosed(family) => family.cardinality(),
        }
    }

    /// **Whether a region is released**: whether every compatible artifact presents the same face
    /// there.
    ///
    /// Lean counterpart: `Releasable`.
    pub fn region_released(&self, region: &Region) -> Result<bool, ArtifactRefusal> {
        match self {
            Self::Enumerated(family) => {
                let width = self.region_width(region, family.lineage())?;
                Ok(width.is_zero())
            }
            Self::Enclosed(family) => family.region_released(region),
        }
    }

    /// **The region's width**, which *is* `receiver_release::width_enumerated` at a
    /// [`RegionReading`]. Nothing is rebuilt: the diameter, its attaining pair and its tolerance
    /// comparison all belong to that owner.
    pub fn region_width(
        &self,
        region: &Region,
        receiver: &str,
    ) -> Result<ReceiverWidth, ArtifactRefusal> {
        let Some(members) = self.members() else {
            return Err(ArtifactRefusal::EnclosureHasNoEnumeratedMembers {
                receiver: receiver.to_owned(),
            });
        };
        if region.length() != self.length() {
            return Err(ArtifactRefusal::LengthMismatch {
                declared: self.length(),
                found: region.length(),
            });
        }
        let vectors: Vec<Vec<Rat>> = members
            .iter()
            .map(Artifact::as_exact_vector)
            .collect();
        let family = CompatibleFamily::enumerated(self.lineage(), vectors)?;
        let reading = RegionReading {
            receiver: receiver.to_owned(),
            positions: region.positions().iter().copied().collect(),
        };
        Ok(width_enumerated(&reading, &family, DiameterNorm::Supremum)?)
    }

    /// **The region's distance through the transverse index**: how many positions `π_B` drops
    /// relative to the whole-artifact chart.
    ///
    /// The region ladder *is* the transverse axis of the tube, so this is the `k` coordinate of
    /// `receiver_release::Horizon` — T5's second axis, read on an artifact.
    pub fn index_distance(&self, region: &Region) -> Result<usize, ArtifactRefusal> {
        if region.length() != self.length() {
            return Err(ArtifactRefusal::LengthMismatch {
                declared: self.length(),
                found: region.length(),
            });
        }
        Ok(self.length() - region.positions().len())
    }

    /// **The width at a declared two-axis horizon.**
    ///
    /// [implemented-exact] This adopts `receiver_release::Horizon` and `width_over_readings`, the
    /// two-axis owner T5 returned. The horizon's longitudinal coordinate is how many edit steps
    /// the family has already taken; its index coordinate must be the region's own distance
    /// through the transverse ladder, and a horizon declaring another is refused by name rather
    /// than silently re-declared. The diameter itself is `width_over_readings`, so this founds no
    /// second width.
    pub fn region_width_at(
        &self,
        region: &Region,
        receiver: &str,
        horizon: &Horizon,
    ) -> Result<ReceiverWidth, ArtifactRefusal> {
        let actual = self.index_distance(region)?;
        if horizon.index() != actual {
            return Err(ArtifactRefusal::HorizonIndexMismatch {
                region: region.positions().iter().copied().collect(),
                declared: horizon.index(),
                actual,
            });
        }
        let Some(members) = self.members() else {
            return Err(ArtifactRefusal::EnclosureHasNoEnumeratedMembers {
                receiver: receiver.to_owned(),
            });
        };
        let faces = members
            .iter()
            .map(|member| {
                region.read(member).map(|face| {
                    ExactFace::Vector(
                        face.values()
                            .values()
                            .map(|token| Rat::from_integer(BigInt::from(*token)))
                            .collect(),
                    )
                })
            })
            .collect::<Result<Vec<_>, _>>()?;
        Ok(width_over_readings(
            receiver,
            self.lineage(),
            &faces,
            DiameterNorm::Supremum,
        )?)
    }

    /// The horizon a region sits at after `steps` edit steps: `(steps, index_distance)`.
    pub fn horizon_of(&self, region: &Region, steps: usize) -> Result<Horizon, ArtifactRefusal> {
        Ok(Horizon::declare(steps, self.index_distance(region)?)?)
    }
}

/// The receiver that reads a region's coordinates as an exact rational vector. This is the
/// `Reading` `receiver_release` consumes, so the width of a region is that owner's width.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RegionReading {
    /// The receiver's declared name.
    pub receiver: String,
    /// The positions it reads, in order.
    pub positions: Vec<usize>,
}

impl Reading for RegionReading {
    fn name(&self) -> &str {
        &self.receiver
    }

    fn read(&self, state: &[Rat]) -> Result<ExactFace, WidthRefusal> {
        let mut values = Vec::with_capacity(self.positions.len());
        for position in &self.positions {
            match state.get(*position) {
                Some(value) => values.push(value.clone()),
                None => {
                    return Err(WidthRefusal::DimensionMismatch {
                        declared: state.len(),
                        found: *position,
                    });
                }
            }
        }
        Ok(ExactFace::Vector(values))
    }
}

// -------------------------------------------------------------------------------------------
// T3 (d) — the step `F_{k+1} = T_g(F_k) ∩ C_k`
// -------------------------------------------------------------------------------------------

/// What one step of the generation law returned.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum StepOutcome {
    /// The family continues.
    Continued(ArtifactFamily),
    /// **The admitted constraint emptied the family.** This is the only way a released region is
    /// reopened by an edit supported elsewhere, and it is returned as content with the swing and
    /// the constraint that did it.
    Emptied {
        /// The swing that transported.
        swing: String,
        /// The constraint that restricted.
        constraint: String,
        /// How many transported artifacts the constraint refused.
        refused: usize,
    },
}

impl StepOutcome {
    /// The continued family, when there is one.
    pub fn family(&self) -> Option<&ArtifactFamily> {
        match self {
            Self::Continued(family) => Some(family),
            Self::Emptied { .. } => None,
        }
    }
}

/// **`F_{k+1} = T_g(F_k) ∩ C_k`** — longitudinal transport, then transverse restriction.
///
/// # Declared-size guard
///
/// [implemented-exact] The work is `members × branches × length`. All three come from caller
/// declarations, the product is formed with checked arithmetic and compared against
/// [`STEP_WORK_CEILING`] **before** the first branch is applied, and the result family is bounded
/// again by [`EnumeratedFamily::declared`].
pub fn step(
    family: &ArtifactFamily,
    swing: &Swing,
    constraint: &Constraint,
) -> Result<StepOutcome, ArtifactRefusal> {
    let Some(members) = family.members() else {
        // An enclosure transports positionwise and restricts positionwise; a swing over an
        // enclosure is refused here rather than materialized, and `EnclosedFamily::restricted`
        // is the lawful route for the restriction half.
        return Err(ArtifactRefusal::EnclosureHasNoEnumeratedMembers {
            receiver: swing.name().to_owned(),
        });
    };
    let work = declared_work(&[members.len(), swing.branches().len(), family.length()]).ok_or(
        ArtifactRefusal::WorkOverflows {
            what: "a family step",
        },
    )?;
    if work > STEP_WORK_CEILING {
        return Err(ArtifactRefusal::DeclarationAboveCeiling {
            what: "a family step work product",
            declared: work,
            ceiling: STEP_WORK_CEILING,
        });
    }
    // Deduplication goes through an ordered set rather than a linear scan: the number of
    // transported artifacts is `members × branches`, which the work ceiling above bounds, and a
    // scan would square it.
    let mut transported: BTreeSet<Artifact> = BTreeSet::new();
    let mut kept: Vec<Artifact> = Vec::new();
    for member in members {
        for branch in swing.branches() {
            let after = branch.apply(member)?;
            if transported.insert(after.clone()) && constraint.admits(&after)? {
                kept.push(after);
            }
        }
    }
    if kept.is_empty() {
        return Ok(StepOutcome::Emptied {
            swing: swing.name().to_owned(),
            constraint: constraint.name().to_owned(),
            refused: transported.len(),
        });
    }
    let lineage = format!("{}|{}∩{}", family.lineage(), swing.name(), constraint.name());
    Ok(StepOutcome::Continued(ArtifactFamily::Enumerated(
        EnumeratedFamily::declared(lineage, kept)?,
    )))
}

/// **Pure restriction never widens the section.** The kept family is a subfamily, so every
/// receiver width is monotone along it — `receiver_release`'s `width_mono`, cited.
///
/// Returns the family that survives the constraint, or [`StepOutcome::Emptied`].
pub fn restrict_only(
    family: &ArtifactFamily,
    constraint: &Constraint,
) -> Result<StepOutcome, ArtifactRefusal> {
    match family {
        ArtifactFamily::Enumerated(enumerated) => {
            let kept: Vec<Artifact> = enumerated
                .members()
                .iter()
                .filter_map(|member| match constraint.admits(member) {
                    Ok(true) => Some(Ok(member.clone())),
                    Ok(false) => None,
                    Err(refusal) => Some(Err(refusal)),
                })
                .collect::<Result<Vec<_>, _>>()?;
            if kept.is_empty() {
                return Ok(StepOutcome::Emptied {
                    swing: "identity".to_owned(),
                    constraint: constraint.name().to_owned(),
                    refused: enumerated.len(),
                });
            }
            let lineage = format!("{}∩{}", enumerated.lineage(), constraint.name());
            Ok(StepOutcome::Continued(ArtifactFamily::Enumerated(
                EnumeratedFamily::declared(lineage, kept)?,
            )))
        }
        ArtifactFamily::Enclosed(enclosed) => Ok(StepOutcome::Continued(
            ArtifactFamily::Enclosed(enclosed.restricted(constraint)?),
        )),
    }
}

/// What a released region's face was, and whether a later step kept it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ReleasePreservation {
    /// The region is still released and presents the same face.
    Stands {
        /// The face that stands.
        face: RegionFace,
    },
    /// The region is still released and presents a **different** face. An edit supported off the
    /// region can never produce this arm; only an edit supported on it can.
    Changed {
        /// The face before the step.
        before: RegionFace,
        /// The face after it.
        after: RegionFace,
    },
    /// The family is empty: the release was refuted, not rewritten.
    RefutedByEmptying {
        /// The swing that transported.
        swing: String,
        /// The constraint that emptied it.
        constraint: String,
    },
    /// The region is no longer released — which requires an edit supported **on** it.
    Reopened {
        /// The width the region now carries.
        width: Rat,
    },
}

/// **Whether a released region survives one step**, and how.
///
/// Lean counterpart: `release_preserved_by_edit_supported_off`, whose Rust obligation is that a
/// swing supported off the region returns [`ReleasePreservation::Stands`] or
/// [`ReleasePreservation::RefutedByEmptying`] and never [`ReleasePreservation::Reopened`].
pub fn release_after_step(
    before: &ArtifactFamily,
    region: &Region,
    outcome: &StepOutcome,
    receiver: &str,
) -> Result<ReleasePreservation, ArtifactRefusal> {
    match outcome {
        StepOutcome::Emptied {
            swing, constraint, ..
        } => Ok(ReleasePreservation::RefutedByEmptying {
            swing: swing.clone(),
            constraint: constraint.clone(),
        }),
        StepOutcome::Continued(after) => {
            let width = after.region_width(region, receiver)?;
            if !width.is_zero() {
                return Ok(ReleasePreservation::Reopened {
                    width: width.diameter().clone(),
                });
            }
            let Some(members) = after.members() else {
                return Err(ArtifactRefusal::EnclosureHasNoEnumeratedMembers {
                    receiver: receiver.to_owned(),
                });
            };
            let after_face = region.read(&members[0])?;
            let before_width = before.region_width(region, receiver)?;
            if before_width.is_zero()
                && let Some(before_members) = before.members()
            {
                let before_face = region.read(&before_members[0])?;
                if before_face != after_face {
                    return Ok(ReleasePreservation::Changed {
                        before: before_face,
                        after: after_face,
                    });
                }
            }
            Ok(ReleasePreservation::Stands { face: after_face })
        }
    }
}

// -------------------------------------------------------------------------------------------
// T3 (e) — independence, entanglement and the two-axis square
// -------------------------------------------------------------------------------------------

/// Whether two edits commute on a declared family, decided exactly.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CommutatorVerdict {
    /// The two orders agree on every member of the declared family.
    Commutes {
        /// The first edit.
        left: String,
        /// The second.
        right: String,
        /// How many members were checked.
        checked: usize,
    },
    /// One member on which the two orders disagree, carrying both results.
    Entangled {
        /// The first edit.
        left: String,
        /// The second.
        right: String,
        /// The member that separates them.
        witness: Artifact,
        /// What `left ∘ right` returned.
        left_then_right: Artifact,
        /// What `right ∘ left` returned.
        right_then_left: Artifact,
    },
}

impl CommutatorVerdict {
    /// Whether the two edits commuted over the declared family.
    pub fn commutes(&self) -> bool {
        matches!(self, Self::Commutes { .. })
    }
}

/// **Decide order-immateriality exactly on a finite family.**
///
/// Two edits are *independent* in this sense when applying them in either order returns the same
/// artifact for every member. The family is already bounded by [`EnumeratedFamily::declared`], so
/// the work is `2 × members` edit applications.
pub fn commutator_verdict(
    family: &EnumeratedFamily,
    left: &Edit,
    right: &Edit,
) -> Result<CommutatorVerdict, ArtifactRefusal> {
    for member in family.members() {
        let left_then_right = right.apply(&left.apply(member)?)?;
        let right_then_left = left.apply(&right.apply(member)?)?;
        if left_then_right != right_then_left {
            return Ok(CommutatorVerdict::Entangled {
                left: left.name().to_owned(),
                right: right.name().to_owned(),
                witness: member.clone(),
                left_then_right,
                right_then_left,
            });
        }
    }
    Ok(CommutatorVerdict::Commutes {
        left: left.name().to_owned(),
        right: right.name().to_owned(),
        checked: family.len(),
    })
}

/// **The declared revision circuit as a tube.** Stations are positions in the declared edit word;
/// `follows` is total, as in `continuing_tube::FlipTube`, so the word `[0, 1, …, n−1, 0]` is a
/// genuine closed circuit whose holonomy is the composite of every edit in it.
///
/// Lean counterpart: `rotationTube` for the functorial case — where
/// `tube_circuit_has_no_defect` applies — and the declared `Circuit` for this one.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RevisionCircuit {
    lineage: String,
    section: RegionTower,
    word: Vec<Edit>,
}

impl RevisionCircuit {
    /// Declare a circuit over an edit word, bounded by [`EDIT_WORD_CEILING`].
    pub fn declared(
        lineage: impl Into<String>,
        length: usize,
        word: Vec<Edit>,
    ) -> Result<Self, ArtifactRefusal> {
        if word.is_empty() {
            return Err(ArtifactRefusal::DeclarationAboveCeiling {
                what: "an edit word length",
                declared: 0,
                ceiling: EDIT_WORD_CEILING,
            });
        }
        if word.len() > EDIT_WORD_CEILING {
            return Err(ArtifactRefusal::DeclarationAboveCeiling {
                what: "an edit word length",
                declared: word.len(),
                ceiling: EDIT_WORD_CEILING,
            });
        }
        Ok(Self {
            lineage: lineage.into(),
            section: RegionTower::declared(length)?,
            word,
        })
    }

    /// What this circuit revises.
    pub fn lineage(&self) -> &str {
        &self.lineage
    }

    /// The declared edit word.
    pub fn word(&self) -> &[Edit] {
        &self.word
    }

    /// The declared artifact length.
    pub fn length(&self) -> usize {
        self.section.length()
    }

    /// The closed circuit word over the stations: `[0, 1, …, n−1, 0]`.
    pub fn closed_word(&self) -> Result<Vec<usize>, ArtifactRefusal> {
        let steps = self
            .word
            .len()
            .checked_add(1)
            .ok_or(ArtifactRefusal::WorkOverflows {
                what: "a circuit word",
            })?;
        if steps > CIRCUIT_CEILING {
            return Err(ArtifactRefusal::DeclarationAboveCeiling {
                what: "a circuit length",
                declared: steps,
                ceiling: CIRCUIT_CEILING,
            });
        }
        let mut circuit: Vec<usize> = (0..self.word.len()).collect();
        circuit.push(0);
        Ok(circuit)
    }

    /// **Whether every edit of the word is chartwise.** A word that is entirely chartwise admits a
    /// chartwise transport at every region; a word carrying a [`EditAction::CopyFrom`] or
    /// [`EditAction::Conditioned`] does not, and its square fails at the region that cannot see
    /// the trigger.
    pub fn is_chartwise(&self) -> bool {
        self.word.iter().all(|edit| edit.action().is_chartwise())
    }

    /// Apply the whole word to an artifact, in order.
    pub fn apply_word(&self, artifact: &Artifact) -> Result<Artifact, ArtifactRefusal> {
        let mut carried = artifact.clone();
        for edit in &self.word {
            carried = edit.apply(&carried)?;
        }
        Ok(carried)
    }
}

impl StationedTower for RevisionCircuit {
    type Station = usize;
    type Section = RegionTower;

    fn follows(&self, _earlier: &usize, _later: &usize) -> bool {
        true
    }

    fn section(&self, _station: &usize) -> Option<&RegionTower> {
        Some(&self.section)
    }

    fn declared_face_population(&self, _chart: &Region, face: &RegionFace) -> usize {
        face.population()
    }

    fn transport(
        &self,
        earlier: &usize,
        later: &usize,
        chart: &Region,
        face: &RegionFace,
    ) -> TubeOutcome<Self, RegionFace> {
        if &face.region != chart {
            return Err(TubeRefusal::Section(TowerRefusal::FaceNotCarried {
                chart: chart.clone(),
                face: face.clone(),
            }));
        }
        let steps = self.word.len();
        if steps == 0 {
            return Ok(face.clone());
        }
        // Stations index the word cyclically. A step to a later station applies the edits between
        // them; a step to an earlier station, or to the same one, closes the lap — which is what
        // makes `[0, 1, …, n−1, 0]` a circuit whose holonomy is the composite of the whole word.
        let earlier = earlier % steps;
        let later = later % steps;
        let span = if later > earlier {
            later - earlier
        } else {
            steps - earlier + later
        };
        let mut values = face.values.clone();
        for offset in 0..span {
            let index = (earlier + offset) % steps;
            let edit = &self.word[index];
            edit.action()
                .apply_chartwise(&mut values, edit.name())
                .map_err(|_| {
                    TubeRefusal::Section(TowerRefusal::FaceNotCarried {
                        chart: chart.clone(),
                        face: face.clone(),
                    })
                })?;
        }
        Ok(RegionFace {
            region: face.region.clone(),
            values,
        })
    }
}

/// The square verdict a [`RevisionCircuit`] returns, in this module's own station, region and face
/// types.
pub type ArtifactSquareVerdict = SquareVerdict<usize, Region, RegionFace>;

/// The holonomy verdict a [`RevisionCircuit`] returns, likewise.
pub type ArtifactHolonomyVerdict = HolonomyVerdict<usize, Region, RegionFace>;

/// The tube owner's refusal in this module's types, boxed because it carries a whole face and
/// would otherwise widen every `Result` here.
pub type BoxedTubeRefusal = Box<TubeRefusal<usize, Region, RegionFace>>;

/// Ask the two-axis square of a declared revision circuit over a declared region aperture.
///
/// This is `continuing_tube::check_commuting_square` applied to [`RevisionCircuit`]; nothing is
/// rebuilt and the verdict is that owner's own [`SquareVerdict`].
pub fn circuit_square(
    circuit: &RevisionCircuit,
    earlier: usize,
    later: usize,
    charts: &[Region],
    faces: &[(Region, RegionFace)],
) -> Result<ArtifactSquareVerdict, BoxedTubeRefusal> {
    // The tube owner's refusal carries a whole face, so it is boxed here rather than widened into
    // every `Result` this module returns. The verdict itself — including its defect — is the `Ok`
    // arm and is carried unboxed.
    check_commuting_square(circuit, &earlier, &later, charts, faces).map_err(Box::new)
}

/// Read the holonomy of a declared revision circuit at declared regions and faces.
///
/// This is `continuing_tube::check_circuit_holonomy`. **"The intentions cancel" is exactly
/// [`HolonomyVerdict::Identity`] at the declared receivers**, and nothing weaker affirms it.
pub fn circuit_holonomy(
    circuit: &RevisionCircuit,
    charts: &[Region],
    faces: &[(Region, RegionFace)],
) -> Result<ArtifactHolonomyVerdict, CircuitRefusal> {
    let word = circuit.closed_word().map_err(CircuitRefusal::Artifact)?;
    check_circuit_holonomy(circuit, &word, charts, faces).map_err(|refusal| {
        CircuitRefusal::Tube(refusal.to_string())
    })
}

/// Why a circuit reading was refused.
#[derive(Clone, Debug, PartialEq, Eq, Error)]
pub enum CircuitRefusal {
    /// This module refused.
    #[error(transparent)]
    Artifact(#[from] ArtifactRefusal),
    /// The tube owner refused; its message is carried whole.
    #[error("{0}")]
    Tube(String),
}

// -------------------------------------------------------------------------------------------
// T3 (f) — periplus, route classes and the revision loop
// -------------------------------------------------------------------------------------------

/// **The residual `(P − I)x`**: the positions at which the returned artifact differs from the one
/// that went out, with both tokens.
///
/// Lean counterpart: `periplusResidual`, with `residual_empty_iff_the_draft_returns`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct PeriplusResidual {
    entries: BTreeMap<usize, (Token, Token)>,
}

impl PeriplusResidual {
    /// The positions that did not return, with `(before, after)`.
    pub fn entries(&self) -> &BTreeMap<usize, (Token, Token)> {
        &self.entries
    }

    /// Whether the composite returned the artifact exactly.
    pub fn is_zero(&self) -> bool {
        self.entries.is_empty()
    }

    /// How many positions did not return.
    pub fn len(&self) -> usize {
        self.entries.len()
    }

    /// Whether nothing moved.
    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }
}

/// **`P = R F`** — the outward edit word, the returning observation-and-revision word, and the
/// residual of the composite.
pub fn periplus_residual(
    outward: &[Edit],
    returning: &[Edit],
    x: &Artifact,
) -> Result<PeriplusResidual, ArtifactRefusal> {
    let total = outward
        .len()
        .checked_add(returning.len())
        .ok_or(ArtifactRefusal::WorkOverflows {
            what: "a periplus word",
        })?;
    if total > EDIT_WORD_CEILING {
        return Err(ArtifactRefusal::DeclarationAboveCeiling {
            what: "a periplus word length",
            declared: total,
            ceiling: EDIT_WORD_CEILING,
        });
    }
    let mut carried = x.clone();
    for edit in outward.iter().chain(returning.iter()) {
        carried = edit.apply(&carried)?;
    }
    let mut entries = BTreeMap::new();
    for position in 0..x.length() {
        let before = x.at(position)?;
        let after = carried.at(position)?;
        if before != after {
            entries.insert(position, (before, after));
        }
    }
    Ok(PeriplusResidual { entries })
}

/// **The route class of a traversal**: the sequence of edit names it ran, which is what "the same
/// route again" means. It is a presentation of the route, not a hash of it.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize)]
pub struct RouteClass {
    edits: Vec<String>,
}

impl RouteClass {
    /// The route class of a declared word, bounded by [`EDIT_WORD_CEILING`].
    pub fn of(word: &[Edit]) -> Result<Self, ArtifactRefusal> {
        if word.len() > EDIT_WORD_CEILING {
            return Err(ArtifactRefusal::DeclarationAboveCeiling {
                what: "a route class length",
                declared: word.len(),
                ceiling: EDIT_WORD_CEILING,
            });
        }
        Ok(Self {
            edits: word.iter().map(|edit| edit.name().to_owned()).collect(),
        })
    }

    /// The edit names, in order.
    pub fn edits(&self) -> &[String] {
        &self.edits
    }
}

/// **The return of a revision loop**: the route class that repeated and the residual it carried.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StopReplaying {
    /// The route class that repeated.
    pub route_class: RouteClass,
    /// The residual of the composite, which is nonzero.
    pub residual: PeriplusResidual,
    /// How many times the route class was traversed inside the declared bound.
    pub traversals: usize,
}

/// What a declared draft–observe–revise circuit returned.
///
/// Lean counterpart: `CircuitOutcome`. The three substantive arms are the plan's three; the fourth
/// is the honest bounded return, and it is never reported as cancellation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CircuitOutcome {
    /// **Progress**: the declared receiver's face changed. The relation between the two drafts is
    /// a continuation — rung 2 — and is *not* receiver equality.
    Progress {
        /// The receiver whose face changed.
        receiver: String,
        /// The face before.
        before: RegionFace,
        /// The face after.
        after: RegionFace,
        /// The rung the two drafts stand on.
        rung: Rung,
    },
    /// **A neutral rechart**: the artifact differs and the declared receivers do not see it. The
    /// rung is stated: receiver equality, rung 4 — never identity and never equal potential, which
    /// a bounded check cannot affirm.
    NeutralRechart {
        /// The receivers that were read.
        receivers: Vec<String>,
        /// The rung the two drafts stand on at those receivers.
        rung: Rung,
    },
    /// **A revision loop**: the visible face returned, the residual is nonzero and the same route
    /// class repeated inside the declared bound.
    RevisionLoop(StopReplaying),
    /// **No defect within the bound.** The declared circuit returned every declared face at every
    /// declared region. This is the scope of the check, not a proof that the intentions cancel at
    /// any undeclared receiver.
    NoDefectWithinBound {
        /// The bound the search ran under.
        bound: usize,
        /// How many regions were declared.
        charts_checked: usize,
        /// How many `(region, face)` pairs were presented.
        faces_checked: usize,
    },
}

/// A bounded history of traversals, for loop detection.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct RevisionHistory {
    entries: Vec<(RouteClass, PeriplusResidual)>,
}

impl RevisionHistory {
    /// An empty history.
    pub fn new() -> Self {
        Self::default()
    }

    /// Record one traversal, bounded by [`ROUTE_HISTORY_CEILING`] before the push.
    pub fn record(
        &mut self,
        route_class: RouteClass,
        residual: PeriplusResidual,
    ) -> Result<(), ArtifactRefusal> {
        if self.entries.len() >= ROUTE_HISTORY_CEILING {
            return Err(ArtifactRefusal::DeclarationAboveCeiling {
                what: "a revision history length",
                declared: self.entries.len() + 1,
                ceiling: ROUTE_HISTORY_CEILING,
            });
        }
        self.entries.push((route_class, residual));
        Ok(())
    }

    /// The recorded traversals.
    pub fn entries(&self) -> &[(RouteClass, PeriplusResidual)] {
        &self.entries
    }

    /// How many times a route class was traversed.
    pub fn traversals_of(&self, route_class: &RouteClass) -> usize {
        self.entries
            .iter()
            .filter(|(class, _)| class == route_class)
            .count()
    }
}

/// **One traversal of a declared revision circuit**, as the bundle the classification reads. Each
/// component is already a validated value of its own owner; this type adds no invariant of its own
/// and is a plain aggregate.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Traversal {
    /// The region the receiver actually reads.
    pub visible: Region,
    /// The draft before the traversal.
    pub before: Artifact,
    /// The draft after it.
    pub after: Artifact,
    /// The route the traversal ran.
    pub route_class: RouteClass,
    /// The residual `(P − I)x` of the composite.
    pub residual: PeriplusResidual,
}

/// **Classify one traversal of a declared revision circuit.**
///
/// The three substantive arms need all of their conditions:
/// *progress* needs a changed receiver face; *neutral rechart* needs an unchanged receiver face
/// with a changed artifact; *revision loop* needs the visible face returned, a nonzero residual
/// **and** the same route class traversed at least `bound` times. When none holds, the return is
/// [`CircuitOutcome::NoDefectWithinBound`], which affirms nothing.
pub fn classify_traversal(
    traversal: &Traversal,
    history: &RevisionHistory,
    bound: usize,
    receiver: &str,
) -> Result<CircuitOutcome, ArtifactRefusal> {
    let Traversal {
        visible,
        before,
        after,
        route_class,
        residual,
    } = traversal;
    let before_face = visible.read(before)?;
    let after_face = visible.read(after)?;
    if before_face != after_face {
        return Ok(CircuitOutcome::Progress {
            receiver: receiver.to_owned(),
            before: before_face,
            after: after_face,
            rung: draft_rung(visible, before, after)?,
        });
    }
    let traversals = history.traversals_of(route_class);
    if !residual.is_zero() && traversals >= bound && bound > 0 {
        return Ok(CircuitOutcome::RevisionLoop(StopReplaying {
            route_class: route_class.clone(),
            residual: residual.clone(),
            traversals,
        }));
    }
    if before != after {
        return Ok(CircuitOutcome::NeutralRechart {
            receivers: vec![receiver.to_owned()],
            rung: draft_rung(visible, before, after)?,
        });
    }
    Ok(CircuitOutcome::NoDefectWithinBound {
        bound,
        charts_checked: 1,
        faces_checked: 1,
    })
}

/// **The rung two drafts stand on** at a declared region.
///
/// Lean counterpart: `draftRung`. Identity when the artifacts coincide; receiver equality (rung 4)
/// when they agree on the region; continuation (rung 2) otherwise. Equal potential is **not**
/// returned here: a bounded comparison cannot affirm it, which is `relation_ladder`'s own finding.
pub fn draft_rung(
    region: &Region,
    before: &Artifact,
    after: &Artifact,
) -> Result<Rung, ArtifactRefusal> {
    if before == after {
        return Ok(Rung::Identity);
    }
    if region.agree_on(before, after)? {
        Ok(Rung::ReceiverEqual)
    } else {
        Ok(Rung::Continuation)
    }
}

// -------------------------------------------------------------------------------------------
// T3 (g) — the typed disposition
// -------------------------------------------------------------------------------------------

/// The declared chart a receiver reads in, and the one the artifact is presented in.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct DeclaredChart {
    required: String,
    present: String,
}

impl DeclaredChart {
    /// Declare the pair.
    pub fn declared(required: impl Into<String>, present: impl Into<String>) -> Self {
        Self {
            required: required.into(),
            present: present.into(),
        }
    }

    /// The chart the receiver requires.
    pub fn required(&self) -> &str {
        &self.required
    }

    /// The chart the artifact is presented in.
    pub fn present(&self) -> &str {
        &self.present
    }

    /// Whether the two agree.
    pub fn agrees(&self) -> bool {
        self.required == self.present
    }
}

/// **The chart change a `Reframe` requires**, returned as a migration requirement rather than a
/// choice among badly posed alternatives.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct RequiredChartChange {
    /// The chart the receiver requires.
    pub required: String,
    /// The chart the artifact is presented in.
    pub present: String,
    /// The migration that would establish the common receiver.
    pub migration: String,
}

/// **Why a `Refuse` refuses**, returned as the actual obstruction.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(tag = "obstruction", rename_all = "kebab-case")]
pub enum CausalObstruction {
    /// No admitted artifact survives the transport and the constraint.
    EmptyPreimageFibre {
        /// The swing that transported.
        swing: String,
        /// The constraint that emptied it.
        constraint: String,
        /// How many transported artifacts the constraint refused.
        refused: usize,
    },
    /// A transport is obstructed at a declared position.
    ObstructedTransport {
        /// The edit that could not run.
        edit: String,
        /// Where.
        position: usize,
        /// Why, named.
        reason: String,
    },
}

/// **The typed disposition of the whole construction.**
///
/// [`Self::Release`] is `receiver_release::ReleaseReturn` whole — `Emit` is its `Released`, and
/// `Hold`, `Widen`, `Ask`, `ReleaseCoarser` and `NoContinuationBridges` are that owner's other
/// arms. Only the two arms that owner does not carry are added here.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ArtifactDisposition {
    /// The release owner's return, unchanged.
    Release(ReleaseReturn),
    /// The obstacle is an incompatible chart, codec or audience receiver.
    Reframe(RequiredChartChange),
    /// The requested target has no admitted construction, or a transport is obstructed.
    Refuse(CausalObstruction),
}

/// The decision law this module declares for a region: release inside the tolerance, hold
/// otherwise. It is one declared law among the many `receiver_release` admits, and it is passed
/// through that owner's `release`, which checks it.
#[derive(Clone, Debug)]
struct RegionReleaseLaw {
    name: String,
}

impl DecisionLaw for RegionReleaseLaw {
    fn name(&self) -> &str {
        &self.name
    }

    fn decide(&self, options: &LawfulOptions) -> ReleaseReturn {
        if options.width() <= options.tolerance() {
            ReleaseReturn::Released {
                width: options.width().clone(),
                tolerance: options.tolerance().clone(),
            }
        } else {
            ReleaseReturn::Hold
        }
    }
}

/// **The disposition is a function of the family and the declared receivers.**
///
/// It is computed from the step outcome, the declared chart and the region's width; no candidate
/// competes, no `NONE` is added to a candidate set, and no normalization appears. When the family
/// continues, the release arm is produced by `receiver_release::release` against a declared
/// tolerance, so the one obligation that owner enforces — a `Released` return is inside the
/// tolerance — is enforced here too.
pub fn disposition(
    outcome: &StepOutcome,
    region: &Region,
    chart: &DeclaredChart,
    receiver: &str,
    tolerance: &Rat,
) -> Result<ArtifactDisposition, ArtifactRefusal> {
    match outcome {
        StepOutcome::Emptied {
            swing,
            constraint,
            refused,
        } => Ok(ArtifactDisposition::Refuse(
            CausalObstruction::EmptyPreimageFibre {
                swing: swing.clone(),
                constraint: constraint.clone(),
                refused: *refused,
            },
        )),
        StepOutcome::Continued(family) => {
            if !chart.agrees() {
                return Ok(ArtifactDisposition::Reframe(RequiredChartChange {
                    required: chart.required().to_owned(),
                    present: chart.present().to_owned(),
                    migration: format!("{} -> {}", chart.present(), chart.required()),
                }));
            }
            let width = family.region_width(region, receiver)?;
            let options = LawfulOptions::assemble(&width, tolerance.clone(), None, None, true)?;
            let law = RegionReleaseLaw {
                name: format!("region-release@{receiver}"),
            };
            Ok(ArtifactDisposition::Release(release(&law, &options)?))
        }
    }
}

// -------------------------------------------------------------------------------------------
// T3 (h) — two media, typed differently, with no coercion
// -------------------------------------------------------------------------------------------

/// **An editable medium**: the whole artifact may be revised before it is consumed.
///
/// There is no conversion between this type and [`IrrevocableUtterance`]: the two media are typed
/// differently on purpose, and neither coerces into the other.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EditableDraft {
    lineage: String,
    artifact: Artifact,
}

impl EditableDraft {
    /// Found a draft.
    pub fn found(lineage: impl Into<String>, artifact: Artifact) -> Self {
        Self {
            lineage: lineage.into(),
            artifact,
        }
    }

    /// What this draft is a draft of.
    pub fn lineage(&self) -> &str {
        &self.lineage
    }

    /// The artifact in front of the writer.
    pub fn artifact(&self) -> &Artifact {
        &self.artifact
    }

    /// Revise it. Any position may change, which is what makes the medium editable.
    pub fn revise(&self, edit: &Edit) -> Result<Self, ArtifactRefusal> {
        Ok(Self {
            lineage: self.lineage.clone(),
            artifact: edit.apply(&self.artifact)?,
        })
    }
}

/// **An irrevocable medium**: what has been emitted is a committed boundary, and the only
/// operation is to append a correction passage.
///
/// There is no method that changes [`Self::committed`], and no conversion from
/// [`EditableDraft`]. *Speech cannot retract, only correct.*
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct IrrevocableUtterance {
    lineage: String,
    committed: Vec<Token>,
    appended: Vec<Token>,
}

impl IrrevocableUtterance {
    /// Emit a committed boundary. Its length is bounded by [`POSITION_CEILING`].
    pub fn emitted(
        lineage: impl Into<String>,
        committed: Vec<Token>,
    ) -> Result<Self, ArtifactRefusal> {
        if committed.len() > POSITION_CEILING {
            return Err(ArtifactRefusal::DeclarationAboveCeiling {
                what: "an emitted boundary length",
                declared: committed.len(),
                ceiling: POSITION_CEILING,
            });
        }
        Ok(Self {
            lineage: lineage.into(),
            committed,
            appended: Vec::new(),
        })
    }

    /// What this utterance is an utterance of.
    pub fn lineage(&self) -> &str {
        &self.lineage
    }

    /// **The committed boundary.** Nothing in this type changes it.
    pub fn committed(&self) -> &[Token] {
        &self.committed
    }

    /// The corrections appended after it.
    pub fn appended(&self) -> &[Token] {
        &self.appended
    }

    /// Everything that has left the mouth: the committed boundary followed by every correction.
    pub fn stream(&self) -> Vec<Token> {
        let mut stream = self.committed.clone();
        stream.extend_from_slice(&self.appended);
        stream
    }

    /// **Append a correction passage.** The committed boundary is untouched; the correction is a
    /// later passage, not a retraction. The total length is bounded before the append.
    pub fn correct(&self, correction: &[Token]) -> Result<Self, ArtifactRefusal> {
        let total = self
            .committed
            .len()
            .checked_add(self.appended.len())
            .and_then(|carried| carried.checked_add(correction.len()))
            .ok_or(ArtifactRefusal::WorkOverflows {
                what: "a correction passage",
            })?;
        if total > POSITION_CEILING {
            return Err(ArtifactRefusal::DeclarationAboveCeiling {
                what: "an emitted stream length",
                declared: total,
                ceiling: POSITION_CEILING,
            });
        }
        let mut appended = self.appended.clone();
        appended.extend_from_slice(correction);
        Ok(Self {
            lineage: self.lineage.clone(),
            committed: self.committed.clone(),
            appended,
        })
    }
}

// -------------------------------------------------------------------------------------------
// T3 (i) — the torus of edit phases
// -------------------------------------------------------------------------------------------

/// **Two independent edit circuits**: exact rotations by rational angles in two declared regions.
///
/// Lean counterpart: `windingCircuit`, with `the_two_edit_circuits_commute`. The phases form the
/// finite group `Z/order₀ × Z/order₁` exactly; a cycle returning the visible face with a winding
/// that is not `(0, 0)` is the torus reading.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EditTorus {
    lineage: String,
    positions: [usize; 2],
    modulus: Token,
    steps: [Token; 2],
}

impl EditTorus {
    /// Declare the torus. The two positions must differ and the modulus must be nonzero; each
    /// step must divide the modulus, so the circuit has an exact finite order.
    pub fn declared(
        lineage: impl Into<String>,
        positions: [usize; 2],
        modulus: Token,
        steps: [Token; 2],
    ) -> Result<Self, ArtifactRefusal> {
        let lineage = lineage.into();
        if modulus == 0 {
            return Err(ArtifactRefusal::ZeroModulus { edit: lineage });
        }
        if positions[0] == positions[1] {
            return Err(ArtifactRefusal::PositionOutsideArtifact {
                position: positions[0],
                length: positions[1],
            });
        }
        for step in steps {
            if step == 0 || !modulus.is_multiple_of(step) {
                return Err(ArtifactRefusal::ZeroModulus {
                    edit: format!("{lineage}: step {step} does not divide modulus {modulus}"),
                });
            }
        }
        Ok(Self {
            lineage,
            positions,
            modulus,
            steps,
        })
    }

    /// What this torus is the torus of.
    pub fn lineage(&self) -> &str {
        &self.lineage
    }

    /// The exact order of each circuit: `modulus / step`.
    pub fn orders(&self) -> [Token; 2] {
        [self.modulus / self.steps[0], self.modulus / self.steps[1]]
    }

    /// The edit that turns one circuit once.
    pub fn turn(&self, axis: usize) -> Result<Edit, ArtifactRefusal> {
        let axis = axis.min(1);
        Edit::declared(
            format!("{}#turn{axis}", self.lineage),
            EditAction::Rotate {
                position: self.positions[axis],
                modulus: self.modulus,
                step: self.steps[axis],
            },
        )
    }

    /// The edit word turning the first circuit `a` times and the second `b` times, bounded by
    /// [`EDIT_WORD_CEILING`] before the word is built.
    pub fn word(&self, a: usize, b: usize) -> Result<Vec<Edit>, ArtifactRefusal> {
        let total = a.checked_add(b).ok_or(ArtifactRefusal::WorkOverflows {
            what: "a torus edit word",
        })?;
        if total > EDIT_WORD_CEILING {
            return Err(ArtifactRefusal::DeclarationAboveCeiling {
                what: "a torus edit word length",
                declared: total,
                ceiling: EDIT_WORD_CEILING,
            });
        }
        let mut word = Vec::with_capacity(total);
        for _ in 0..a {
            word.push(self.turn(0)?);
        }
        for _ in 0..b {
            word.push(self.turn(1)?);
        }
        Ok(word)
    }

    /// **The winding of a declared word**: how many turns each circuit took, as exact integers.
    pub fn winding(&self, word: &[Edit]) -> Result<[BigInt; 2], ArtifactRefusal> {
        if word.len() > EDIT_WORD_CEILING {
            return Err(ArtifactRefusal::DeclarationAboveCeiling {
                what: "a torus edit word length",
                declared: word.len(),
                ceiling: EDIT_WORD_CEILING,
            });
        }
        let mut winding = [BigInt::zero(), BigInt::zero()];
        for edit in word {
            if let EditAction::Rotate {
                position,
                modulus,
                step,
            } = edit.action()
                && *modulus == self.modulus
            {
                for (axis, turns) in winding.iter_mut().enumerate() {
                    if *position == self.positions[axis] && *step == self.steps[axis] {
                        *turns += BigInt::one();
                    }
                }
            }
        }
        Ok(winding)
    }

    /// **Whether a declared word returns the visible face**: exactly when each winding is a
    /// multiple of that circuit's order.
    pub fn returns_the_visible_face(&self, word: &[Edit]) -> Result<bool, ArtifactRefusal> {
        let winding = self.winding(word)?;
        let orders = self.orders();
        Ok((0..2).all(|axis| (&winding[axis] % BigInt::from(orders[axis])).is_zero()))
    }
}

#[cfg(test)]
#[path = "artifact_release/tests.rs"]
mod tests;

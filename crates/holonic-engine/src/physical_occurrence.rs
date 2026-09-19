//! **The typed environment index, situated occurrences, and what a contact edge's status is.**
//!
//! [definition] This module owns items **B3** and **B4** of
//! `docs/plans/THE_BIOLOGICAL_ECOLOGY_INSTANTIATES_THE_CARRIER.md`.
//!
//! [`crate::physical_intake`] already refuses to found an occurrence without an
//! [`crate::physical_intake::EnvironmentIndex`]. That index is the *presented* one: the ten arrays
//! a released prediction wire happens to carry. This module builds the **typed** environment on top
//! of it — species and homolog, target conformation, oligomeric state, pH with its protonation
//! assumption, membrane or soluble context, cofactors and ligands, assay format, and intended and
//! unintended partners — and states the two laws the typed version makes available.
//!
//! # B3: the environment index, and the law that transport is typed
//!
//! 1. **Every coordinate is declared with a ground or explicitly undeclared. Nothing is defaulted.**
//!    [`Coordinate`] has exactly two constructors, both of which refuse an empty ground or an empty
//!    statement of why, and there is no `Default` implementation for it or for any coordinate
//!    carrier. [`Environment::found`] refuses unless **every** name in [`CoordinateName::ALL`] is
//!    present exactly once, so an environment with an unstated axis is not a value of this type.
//! 2. **An [`Occurrence`] is a structure face situated at one environment index.** Its single
//!    constructor takes the environment by value and [`Occurrence::environment`] is total.
//! 3. **A reading taken at environment `e` is a claim at `e` only.** [`compare_here`] compares two
//!    situated families and returns [`EnvironmentRefusal::EnvironmentsDiffer`] — naming the
//!    coordinates the two environments diverge in — unless the two environments are the same value.
//!    Carrying a claim from `e` to `e'` needs a supplied [`EnvironmentPassage`], which is a
//!    [`crate::continuing_tower::Transition`] whose residual **is** the environment the claim was
//!    read at. There is no other path: [`compare_through`] takes the passage by reference.
//! 4. **Environments are the vertical index of the carrier.** [`EnvironmentTower`] instantiates
//!    [`crate::continuing_tower::Tower`] on the refinement order of *declared coordinate sets*, so
//!    refining the environment around one object is a restriction with a residual
//!    ([`EnvironmentRestriction`]) and not a change of object. Varying the object at one
//!    environment is the separate, separately typed [`HorizontalFamily`]; varying the environment
//!    around one object is [`VerticalFamily`]. Neither constructor admits the other's population.
//!
//! [definition] Two coordinates **agree** only when both are declared and the declared values are
//! equal. Two undeclared coordinates do not agree: neither states anything, so nothing licenses the
//! claim that the two readings were taken under the same condition there. A consequence worth
//! naming: an environment does not agree with *itself* at an undeclared axis, and
//! [`Environment::disagreement`] against itself returns exactly the undeclared axes. That is the
//! honest reading, and it is why [`compare_here`] tests value identity of the environment rather
//! than coordinate-wise agreement — the two are different relations and both are available.
//!
//! # B4: a contact edge is not a boolean
//!
//! [`ContactStatus`] has six states with six different evidence requirements.
//!
//! | State | What it takes |
//! |---|---|
//! | [`ContactStatus::Formed`] | the exact interval's upper bound at or below the aperture |
//! | [`ContactStatus::Excluded`] | the exact interval's lower bound strictly above it |
//! | [`ContactStatus::Open`] | an interval that straddles the aperture; the reading stays plural |
//! | [`ContactStatus::KineticallyInaccessible`] | an [`ExteriorDeclaration`] with a stated ground |
//! | [`ContactStatus::EnvironmentDependent`] | one ordered pair read differently across a [`VerticalFamily`] |
//! | [`ContactStatus::Competing`] | a [`ValenceDeclaration`] the formed contenders exceed |
//!
//! [proved-derived; implemented-exact] [`static_status`] — the only function from a static
//! structure to a status — has exactly `{Formed, Excluded, Open}` in its image and attains all
//! three. The other three states are unreachable from it *by type*:
//! [`ContactStatus::KineticallyInaccessible`] carries an [`ExteriorDeclaration`] whose fields are
//! private and whose [`ExteriorDeclaration::declare`] refuses an empty statement, so no path from a
//! `.cif` file to that variant exists; [`ContactStatus::EnvironmentDependent`] is the return of
//! [`VerticalFamily::status_across`], which needs several environments; and
//! [`ContactStatus::Competing`] is the return of [`site_occupancy`], which needs a declared
//! valence.
//!
//! [definition] **The exclusion this owner computes is a declared valence at one site.** A site
//! with declared valence `k` cannot carry more than `k` formed contacts at once, so
//! `formed_contenders > k` is a competition and `formed_contenders <= k` is not. The alternative —
//! steric exclusion derived from the exact distance law between two partners of the same site — is
//! a *different* exclusion with different evidence, and this module deliberately does not compute
//! it or blend it in. Open contenders at the site are retained separately in
//! [`SiteOccupancy::open`] and never counted as formed, so a competition is never derived from an
//! undecided reading.
//!
//! [definition] **Directional uncertainty is retained per ordered pair and never symmetrized.**
//! `PAE(i→j)` and `PAE(j→i)` differ in general. [`DirectionalUncertainty`] carries both exact
//! values with their separate units in the last place, and this module exposes no mean, minimum,
//! maximum or any other symmetric summary of them. [`DirectionalUncertainty::transposed`] exists so
//! a caller can *exhibit* the asymmetry; it is an involution and it is not the identity on an
//! asymmetric reading.
//!
//! # B5 and B6, in this owner's own submodules
//!
//! [definition] [`plural_fibre`] owns **B5** — the n-way fibre over one candidate, the complete
//! separator set between every pair and across the family, the partition of contacts into
//! unanimous-formed, unanimous-excluded, separating and open-carrying, and the exact minimal
//! separating sets under a declared bound. [`passage`] owns **B6** —
//! `(K,Theta)_{t+} = Phi_e((K,Theta)_{t-})` as a typed event carrying receipts, with vertical and
//! horizontal passages as two types and no coercion between them.
//!
//! [definition] Both are **this** owner rather than a new one. B5's population is a population of
//! [`SituatedFamily`], the object [`VerticalFamily`] and [`HorizontalFamily`] already index in two
//! directions; the fibre is the join of those two indices restricted to one object, and neither
//! existing constructor admits it — a vertical family refuses two members at one environment and a
//! horizontal one refuses two members at two environments. B6's three vertical events are built
//! **on** [`EnvironmentPassage`], which already refuses an unaccounted divergent axis; a
//! [`passage::Passage`] adds the two occurrences, the exact delta in the constraint complex, the
//! residual and the cost receipt that type does not carry.
//!
//! # The remount law: no value of this module has a second constructor
//!
//! [definition] **Every type here with a checked constructor is unreachable except through it**,
//! including from a wire. There are exactly two shapes, and which one a type takes is decided by
//! whether any consumer round-trips it:
//!
//! 1. **No `Deserialize` at all.** [`ContactStatus`], [`ExteriorDeclaration`],
//!    [`ValenceDeclaration`], [`Competition`], [`SituatedAt`], [`EnvironmentDependence`] and
//!    [`SiteOccupancy`] derive `Serialize` and not `Deserialize`. They are written out as
//!    receipts; they are re-founded through their constructors, never remounted.
//! 2. **`Deserialize` routed through the constructor.** [`Coordinate`], [`Environment`],
//!    [`EnvironmentPassage`], [`VerticalFamily`] and [`HorizontalFamily`] *are* round-tripped by
//!    consumers, so they keep `Deserialize` — but through `#[serde(try_from = "…")]` and a private
//!    wire type, so the value serde builds is handed to [`Coordinate::declared`] /
//!    [`Coordinate::undeclared`], [`Environment::found`], [`EnvironmentPassage::declare`],
//!    [`VerticalFamily::over_one_object`] or [`HorizontalFamily::at_one_environment`], and every
//!    check those perform is performed on the wire. A wire missing an axis, repeating one, filing
//!    a value under the wrong axis, carrying an empty ground or an empty undeclaration reason,
//!    leaving a divergent axis unaccounted, repeating an environment along the vertical index, or
//!    naming a schema this owner does not found, is a **typed refusal at the boundary**. The
//!    derives formerly reconstructed the private fields directly, which was exactly the bypass
//!    shape (1) exists to close.
//!
//! [definition] The same reading applies to the other bypass shapes. There is no `Default` on any
//! type with a checked constructor. The fields a constructor establishes — `Environment`'s
//! `coordinates` and `presented`, `EnvironmentPassage`'s `from`/`to`/`accounted`,
//! `VerticalFamily`'s and `HorizontalFamily`'s `members`, `Occurrence`'s `environment`/`face`,
//! `ExteriorDeclaration`'s and `ValenceDeclaration`'s contents — are **private**, so no
//! clone-then-mutate path reaches them either. The public fields that remain (`schema`, `lineage`,
//! and the fields of the receipt structs) are testimony no constructor checks, and the wire types
//! check `schema` against the one the constructor stamps.
//!
//! [definition] [`SituatedFamily`] and [`SituatedPairReading`] are deliberately plain records with
//! public fields and **no** checked constructor: they are the readings a family carries, built by
//! [`Occurrence::enacted_family`] / [`Occurrence::founded_family`] from an exact complex, and
//! nothing about them is a claim a constructor could check. The families that *do* carry a law
//! over them — vertical and horizontal — are the two in shape (2).
//!
//! # The paired Lean owner
//!
//! `formal/elementary-holonics/ElementaryHolonics/Foundation/PhysicalOccurrence.lean`, namespace
//! `Soma.Holonics.Foundation.PhysicalOccurrence`, which names this file and every item below.
//!
//! | Lean declaration | Rust owner |
//! |---|---|
//! | `Coordinate`, `Coordinate.declared`, `Coordinate.undeclared` | [`Coordinate`] with its two checked constructors |
//! | `Coordinate.agrees`, `agrees_iff` | [`Coordinate::agrees`] |
//! | `Coordinate.agreement_is_declared_on_both_sides` | [`Coordinate::agrees`] returning `false` whenever either side is undeclared |
//! | `Coordinate.no_third_state` | [`Coordinate`] has two variants and no `Default` |
//! | `CoordinateName`, `allCoordinates`, `mem_allCoordinates` | [`CoordinateName`], [`CoordinateName::ALL`] |
//! | `CoordinateType` | [`CoordinateValue`], whose [`CoordinateValue::name`] is the axis it belongs to |
//! | `EnvironmentIndex` | [`Environment`], whose [`Environment::found`] refuses an incomplete product |
//! | `disagreement`, `mem_disagreement_iff`, `disagreement_eq_nil_iff` | [`Environment::disagreement`] |
//! | `disagreement_self_is_exactly_the_undeclared` | [`Environment::disagreement`] against itself |
//! | `Occurrence`, `Occurrence.environment` | [`Occurrence`], [`Occurrence::environment`] |
//! | `Passage`, `Passage.complete` | [`EnvironmentPassage::declare`] |
//! | `compareHere`, `compareReadings` | [`compare_here`] |
//! | `compareAcross` | [`compare_through`], which takes the passage by reference |
//! | `compareReadings_refuses_naming_the_coordinates` | [`EnvironmentRefusal::EnvironmentsDiffer`] |
//! | `passage_accounts_for_the_refusal` | [`EnvironmentPassage::accounts_for`] |
//! | `ContactStatus` | [`ContactStatus`] |
//! | `staticStatus`, `staticStatusOfInterval` | [`static_status`] |
//! | `static_law_reaches_exactly_three` | `physical_occurrence/tests.rs::the_static_exact_law_reaches_exactly_three_states` |
//! | `ExteriorGround`, `kinetic_requires_exterior_ground` | [`ExteriorDeclaration`] |
//! | `acrossEnvironments`, `acrossEnvironments_constant`, `acrossEnvironments_dependent_of_two_classes` | [`VerticalFamily::status_across`] |
//! | `valenceCompetition`, `competing_iff_contenders_exceed_valence` | [`site_occupancy`] |
//! | `DirectionalReading`, `swap`, `FactorsThroughSymmetrization` | [`DirectionalUncertainty`], [`DirectionalUncertainty::transposed`] |
//! | `symmetrization_merges_a_distinguishable_pair` | the measured asymmetric pair counts in `tests.rs` |
//! | `occurrence_contract` | the whole module contract |

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

use relational_geometry::Rat;
use serde::{Deserialize, Serialize};
use thiserror::Error;

use crate::continuing_tower::{Tower, TowerFaceOutcome, TowerRefusal, Transition};
use crate::exact_value::ExactInterval;
use crate::physical_constraint_complex::{
    ConstraintComponentId, ConstraintEdge, ConstraintError, ConstraintVertexId, ContactClass,
    DistanceAperture, PairUncertainty, PhysicalConstraintComplex,
};
use crate::physical_intake::{
    EnvironmentIndex as PresentedEnvironmentIndex, IntakeRefusal, enacted_classes,
};

// ---------------------------------------------------------------------------------------------
// B3: the coordinate axes
// ---------------------------------------------------------------------------------------------

/// The declared coordinate axes of an environment.
///
/// [definition] The list is closed. An environment cannot quietly acquire an axis, and
/// [`Environment::found`] refuses unless every one of them is present.
///
/// Lean counterpart: `Foundation/PhysicalOccurrence.lean::CoordinateName`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum CoordinateName {
    /// Species and homolog of the target.
    Species,
    /// Which conformational form of the target was presented.
    Conformation,
    /// The oligomeric state, as exact per-entity copy counts.
    OligomericState,
    /// pH, together with the protonation assumption the reading depends on.
    Acidity,
    /// Membrane or soluble context.
    Solvation,
    /// Cofactors and ligands present, with exact copy counts.
    Cofactors,
    /// The assay or prediction format the reading was taken in.
    Assay,
    /// Intended and unintended partners.
    Partners,
}

impl CoordinateName {
    /// Every axis, once. The order is the declaration order and is stable.
    ///
    /// Lean counterpart: `allCoordinates`, with `mem_allCoordinates` as its completeness.
    pub const ALL: [CoordinateName; 8] = [
        CoordinateName::Species,
        CoordinateName::Conformation,
        CoordinateName::OligomericState,
        CoordinateName::Acidity,
        CoordinateName::Solvation,
        CoordinateName::Cofactors,
        CoordinateName::Assay,
        CoordinateName::Partners,
    ];

    /// The axis's name, for receipts and refusals.
    pub const fn label(self) -> &'static str {
        match self {
            Self::Species => "species and homolog",
            Self::Conformation => "target conformation",
            Self::OligomericState => "oligomeric state",
            Self::Acidity => "pH and protonation assumption",
            Self::Solvation => "membrane or soluble context",
            Self::Cofactors => "cofactors and ligands",
            Self::Assay => "assay format",
            Self::Partners => "intended and unintended partners",
        }
    }
}

impl fmt::Display for CoordinateName {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(self.label())
    }
}

/// Species and homolog of the target.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct SpeciesHomolog {
    /// The species the target was taken from.
    pub species: String,
    /// The homolog or isoform within that species.
    pub homolog: String,
}

/// The oligomeric state, as an exact copy count per entity. No float and no "approximately".
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct OligomericState {
    /// Entity label to exact copy count.
    pub copies: BTreeMap<String, u32>,
}

/// pH together with the protonation assumption the reading depends on.
///
/// [definition] The pH is an [`ExactInterval`] of rationals, never a float: a measured or declared
/// pH is an enclosure, and the assumption it licenses about which residues are protonated travels
/// with it rather than being inferred downstream.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Acidity {
    /// The declared pH enclosure.
    pub p_h: ExactInterval,
    /// The protonation assumption the reading was taken under.
    pub protonation_assumption: String,
}

/// Membrane or soluble context.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub enum Solvation {
    /// Soluble, in a declared buffer.
    Soluble {
        /// The buffer.
        buffer: String,
    },
    /// Embedded in a declared lipid environment.
    MembraneEmbedded {
        /// The lipid environment.
        lipid: String,
    },
    /// Associated with a declared leaflet without being embedded.
    MembraneAssociated {
        /// The leaflet.
        leaflet: String,
    },
}

/// Cofactors and ligands present, with exact copy counts.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct LigandComplement {
    /// Chemical component identifier to exact copy count.
    pub copies: BTreeMap<String, u32>,
}

/// The format the reading was taken in.
///
/// [definition] A structure prediction and a surface binding measurement are different formats, and
/// the difference is carried rather than erased into "a number about this design".
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub enum AssayFormat {
    /// A structure predictor at a declared seed.
    InSilicoPrediction {
        /// The predictor.
        predictor: String,
        /// The sampling seed.
        seed: String,
    },
    /// A surface measurement with a declared immobilization and analyte valency.
    SurfaceMeasurement {
        /// What was immobilized and how.
        immobilization: String,
        /// The analyte valency, exact.
        analyte_valency: u32,
    },
    /// Any other format, named.
    Declared {
        /// The format.
        description: String,
    },
}

/// Intended and unintended partners, kept apart.
///
/// [definition] A partner one designed against and a partner one must not bind are different
/// testimony, and collapsing them into "partners present" loses the whole selectivity question.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct PartnerPanel {
    /// Partners the occurrence was intended to engage.
    pub intended: BTreeSet<String>,
    /// Partners the occurrence must not engage, declared.
    pub unintended: BTreeSet<String>,
}

/// The typed value of one coordinate axis.
///
/// Lean counterpart: `Foundation/PhysicalOccurrence.lean::CoordinateType`, the dependent carrier of
/// each axis.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum CoordinateValue {
    /// Species and homolog.
    Species(SpeciesHomolog),
    /// The presented conformational form.
    Conformation(String),
    /// The oligomeric state.
    OligomericState(OligomericState),
    /// pH and protonation assumption.
    Acidity(Acidity),
    /// Membrane or soluble context.
    Solvation(Solvation),
    /// Cofactors and ligands.
    Cofactors(LigandComplement),
    /// The assay format.
    Assay(AssayFormat),
    /// Intended and unintended partners.
    Partners(PartnerPanel),
}

impl CoordinateValue {
    /// Which axis this value belongs to.
    pub const fn name(&self) -> CoordinateName {
        match self {
            Self::Species(_) => CoordinateName::Species,
            Self::Conformation(_) => CoordinateName::Conformation,
            Self::OligomericState(_) => CoordinateName::OligomericState,
            Self::Acidity(_) => CoordinateName::Acidity,
            Self::Solvation(_) => CoordinateName::Solvation,
            Self::Cofactors(_) => CoordinateName::Cofactors,
            Self::Assay(_) => CoordinateName::Assay,
            Self::Partners(_) => CoordinateName::Partners,
        }
    }
}

/// One environment coordinate: a value **declared together with its ground**, or an explicit
/// statement that the axis was not declared.
///
/// [definition] There is no third state and no `Default`. Both constructors refuse an empty string,
/// because an unstated ground is not a declaration and an unstated reason is not an undeclaration —
/// both are defaults wearing a name.
///
/// Lean counterpart: `Foundation/PhysicalOccurrence.lean::Coordinate`, with
/// `Coordinate.no_third_state`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(try_from = "CoordinateWire")]
pub enum Coordinate {
    /// Declared, with the ground that licenses the declaration.
    Declared {
        /// The typed value.
        value: CoordinateValue,
        /// Why this value is claimed, retained as testimony.
        ground: String,
    },
    /// Explicitly not declared, with the statement of why.
    Undeclared {
        /// Why it was not declared.
        why: String,
    },
}

impl Coordinate {
    /// Declare a coordinate. An empty ground is refused.
    pub fn declared(
        value: CoordinateValue,
        ground: impl Into<String>,
    ) -> Result<Self, EnvironmentRefusal> {
        let ground = ground.into();
        if ground.trim().is_empty() {
            return Err(EnvironmentRefusal::GroundNotStated { name: value.name() });
        }
        Ok(Self::Declared { value, ground })
    }

    /// State that a coordinate is not declared. An empty reason is refused.
    pub fn undeclared(why: impl Into<String>) -> Result<Self, EnvironmentRefusal> {
        let why = why.into();
        if why.trim().is_empty() {
            return Err(EnvironmentRefusal::UndeclarationNotStated);
        }
        Ok(Self::Undeclared { why })
    }

    /// Whether the coordinate was declared at all.
    pub const fn is_declared(&self) -> bool {
        matches!(self, Self::Declared { .. })
    }

    /// The declared value, when there is one.
    pub const fn value(&self) -> Option<&CoordinateValue> {
        match self {
            Self::Declared { value, .. } => Some(value),
            Self::Undeclared { .. } => None,
        }
    }

    /// Which axis a declared coordinate belongs to.
    pub const fn name(&self) -> Option<CoordinateName> {
        match self {
            Self::Declared { value, .. } => Some(value.name()),
            Self::Undeclared { .. } => None,
        }
    }

    /// **Agreement requires a declaration on both sides.** Two undeclared coordinates do not agree:
    /// neither states anything, so nothing licenses the claim that they name the same condition.
    ///
    /// Lean counterpart: `Coordinate.agrees` with
    /// `Coordinate.agreement_is_declared_on_both_sides`.
    pub fn agrees(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Declared { value: left, .. }, Self::Declared { value: right, .. }) => {
                left == right
            }
            _ => false,
        }
    }

    /// A rendering for refusal messages. Testimony, never an identity.
    pub fn render(&self) -> String {
        match self {
            Self::Declared { value, ground } => format!("declared {value:?} on the ground {ground:?}"),
            Self::Undeclared { why } => format!("explicitly undeclared: {why}"),
        }
    }
}

// ---------------------------------------------------------------------------------------------
// B3: the environment index
// ---------------------------------------------------------------------------------------------

/// The typed environment one reading was taken at.
///
/// [definition] A product of optioned coordinates over the closed axis list, sitting **on top of**
/// the presented [`PresentedEnvironmentIndex`] that `physical_intake` already refuses to found an
/// occurrence without. Both are required: the presented index says what the wire recorded, and the
/// typed coordinates say what the run was actually a claim about.
///
/// Lean counterpart: `Foundation/PhysicalOccurrence.lean::EnvironmentIndex`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(try_from = "EnvironmentWire")]
pub struct Environment {
    /// The schema this environment serializes under.
    pub schema: String,
    /// Exterior lineage, retained as testimony.
    pub lineage: String,
    presented: PresentedEnvironmentIndex,
    coordinates: BTreeMap<CoordinateName, Coordinate>,
}

impl Environment {
    /// Found a typed environment. Refuses unless every axis in [`CoordinateName::ALL`] is present
    /// exactly once and every declared value belongs to the axis it is filed under.
    pub fn found(
        lineage: impl Into<String>,
        presented: PresentedEnvironmentIndex,
        coordinates: impl IntoIterator<Item = (CoordinateName, Coordinate)>,
    ) -> Result<Self, EnvironmentRefusal> {
        let mut map: BTreeMap<CoordinateName, Coordinate> = BTreeMap::new();
        for (name, coordinate) in coordinates {
            if let Some(declared) = coordinate.name()
                && declared != name
            {
                return Err(EnvironmentRefusal::CoordinateMisfiled {
                    filed_under: name,
                    belongs_to: declared,
                });
            }
            if map.insert(name, coordinate).is_some() {
                return Err(EnvironmentRefusal::CoordinateRepeated { name });
            }
        }
        let absent = CoordinateName::ALL
            .iter()
            .copied()
            .filter(|name| !map.contains_key(name))
            .collect::<Vec<_>>();
        if !absent.is_empty() {
            return Err(EnvironmentRefusal::CoordinatesAbsent { absent });
        }
        Ok(Self {
            schema: "holonic-engine.typed-environment-index.v1".to_owned(),
            lineage: lineage.into(),
            presented,
            coordinates: map,
        })
    }

    /// The presented index this typed environment refines. Total.
    pub const fn presented(&self) -> &PresentedEnvironmentIndex {
        &self.presented
    }

    /// One axis.
    ///
    /// [definition] Total in practice: [`Environment::found`] refuses an environment missing any
    /// axis, and the `Deserialize` impl is routed through it, so no `Environment` exists with an
    /// absent axis. The `Result` is retained as the shape of the answer rather than a panic — a
    /// future axis added to [`CoordinateName::ALL`] would make already-serialized wires incomplete,
    /// and the refusal names the axis instead of indexing past it.
    pub fn coordinate(&self, name: CoordinateName) -> Result<&Coordinate, EnvironmentRefusal> {
        self.coordinates
            .get(&name)
            .ok_or(EnvironmentRefusal::CoordinatesAbsent {
                absent: vec![name],
            })
    }

    /// Every axis, in axis order.
    pub const fn coordinates(&self) -> &BTreeMap<CoordinateName, Coordinate> {
        &self.coordinates
    }

    /// The axes that carry a declaration.
    pub fn declared_names(&self) -> BTreeSet<CoordinateName> {
        self.coordinates
            .iter()
            .filter(|(_, coordinate)| coordinate.is_declared())
            .map(|(name, _)| *name)
            .collect()
    }

    /// The axes explicitly left undeclared. Named, never filled in.
    pub fn undeclared_names(&self) -> BTreeSet<CoordinateName> {
        self.coordinates
            .iter()
            .filter(|(_, coordinate)| !coordinate.is_declared())
            .map(|(name, _)| *name)
            .collect()
    }

    /// **The coordinates in which this environment and another are not certified to agree.**
    ///
    /// An axis either side left undeclared is in the set: nothing licenses the claim that the two
    /// readings were taken under the same condition there. Against itself, the return is therefore
    /// exactly [`Self::undeclared_names`].
    ///
    /// Lean counterpart: `disagreement`, with `mem_disagreement_iff`,
    /// `disagreement_eq_nil_iff` and `disagreement_self_is_exactly_the_undeclared`.
    pub fn disagreement(&self, other: &Self) -> EnvironmentDisagreement {
        let mut coordinates = Vec::new();
        for name in CoordinateName::ALL {
            let left = self.coordinates.get(&name);
            let right = other.coordinates.get(&name);
            let agrees = match (left, right) {
                (Some(left), Some(right)) => left.agrees(right),
                _ => false,
            };
            if !agrees {
                coordinates.push(CoordinateDivergence {
                    name,
                    left: left.map_or_else(|| "absent".to_owned(), Coordinate::render),
                    right: right.map_or_else(|| "absent".to_owned(), Coordinate::render),
                });
            }
        }
        EnvironmentDisagreement {
            schema: "holonic-engine.environment-disagreement.v1".to_owned(),
            left_lineage: self.lineage.clone(),
            right_lineage: other.lineage.clone(),
            coordinates,
        }
    }
}

/// One axis at which two environments are not certified to agree.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CoordinateDivergence {
    /// The axis.
    pub name: CoordinateName,
    /// What the left environment says there, rendered.
    pub left: String,
    /// What the right environment says there, rendered.
    pub right: String,
}

/// The complete set of axes at which two environments are not certified to agree.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct EnvironmentDisagreement {
    /// The schema this disagreement serializes under.
    pub schema: String,
    /// The left environment's lineage.
    pub left_lineage: String,
    /// The right environment's lineage.
    pub right_lineage: String,
    /// The divergent axes, in axis order.
    pub coordinates: Vec<CoordinateDivergence>,
}

impl EnvironmentDisagreement {
    /// Whether every axis is certified to agree.
    pub fn is_empty(&self) -> bool {
        self.coordinates.is_empty()
    }

    /// The divergent axis names.
    pub fn names(&self) -> BTreeSet<CoordinateName> {
        self.coordinates.iter().map(|divergence| divergence.name).collect()
    }
}

// ---------------------------------------------------------------------------------------------
// B3: the vertical index — environments as a tower over one object
// ---------------------------------------------------------------------------------------------

/// A chart of the vertical index: **which axes are declared**.
///
/// [definition] One environment refines another when it declares at least as many axes. This is the
/// vertical direction of the carrier: refining the environment *around one object*. Varying the
/// object at a fixed environment is the horizontal direction and is a different type,
/// [`HorizontalFamily`].
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct EnvironmentAperture(pub BTreeSet<CoordinateName>);

impl EnvironmentAperture {
    /// The aperture at which every axis is declared.
    pub fn complete() -> Self {
        Self(CoordinateName::ALL.into_iter().collect())
    }

    /// The aperture declaring exactly the named axes.
    pub fn of(names: impl IntoIterator<Item = CoordinateName>) -> Self {
        Self(names.into_iter().collect())
    }
}

/// The stated reason a restriction leaves behind. A fixed string, so restricting twice and
/// restricting once produce the *same* face and `restrict_trans` holds exactly.
const FORGOTTEN_BY_RESTRICTION: &str =
    "forgotten by restriction to a coarser environment aperture; the value is retained in the \
     restriction's residual and is reopened from it";

/// The environment tower: the vertical index of the carrier.
///
/// Lean counterpart: the refinement order this instantiates is
/// `Foundation/ContinuingTower.lean::Tower.Refines`; the Rust trait is
/// [`crate::continuing_tower::Tower`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EnvironmentTower {
    /// Exterior lineage of the tower, retained as testimony.
    pub lineage: String,
}

impl Tower for EnvironmentTower {
    type Index = EnvironmentAperture;
    type Face = Environment;

    fn refines(&self, coarse: &Self::Index, fine: &Self::Index) -> bool {
        coarse.0.is_subset(&fine.0)
    }

    fn carries(&self, chart: &Self::Index, face: &Self::Face) -> bool {
        face.declared_names() == chart.0
    }

    fn restrict(
        &self,
        coarse: &Self::Index,
        fine: &Self::Index,
        face: &Self::Face,
    ) -> TowerFaceOutcome<Self> {
        if !self.carries(fine, face) {
            return Err(TowerRefusal::FaceNotCarried {
                chart: fine.clone(),
                face: face.clone(),
            });
        }
        if !self.refines(coarse, fine) {
            return Err(TowerRefusal::NotARefinement {
                coarse: coarse.clone(),
                fine: fine.clone(),
            });
        }
        Ok(forget_outside(face, &coarse.0))
    }
}

/// The face with every *declared* coordinate outside `keep` turned into an explicit undeclaration.
/// An already-undeclared coordinate is left exactly as it is, so restricting to the face's own
/// aperture is the identity.
fn forget_outside(face: &Environment, keep: &BTreeSet<CoordinateName>) -> Environment {
    let mut restricted = face.clone();
    for (name, coordinate) in &mut restricted.coordinates {
        if coordinate.is_declared() && !keep.contains(name) {
            *coordinate = Coordinate::Undeclared {
                why: FORGOTTEN_BY_RESTRICTION.to_owned(),
            };
        }
    }
    restricted
}

/// Restriction along the vertical index, as a [`Transition`] carrying its residual.
///
/// [definition] The residual is the **declared coordinates that were dropped, with their grounds**,
/// and [`Transition::reopen`] puts them back exactly. `reopen(apply(x), residual(x)) = x` is
/// therefore an equality on this axis and not a bound — which is the environment instance of
/// `Foundation/ContinuingTower.lean::Transition.reopen_apply`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EnvironmentRestriction {
    /// The axes retained.
    pub coarse: EnvironmentAperture,
    /// Exterior lineage of the restriction, retained as testimony.
    pub lineage: String,
}

impl Transition for EnvironmentRestriction {
    type Source = Environment;
    type Target = Environment;
    type Residual = BTreeMap<CoordinateName, Coordinate>;

    fn apply(&self, source: &Self::Source) -> Self::Target {
        forget_outside(source, &self.coarse.0)
    }

    fn residual(&self, source: &Self::Source) -> Self::Residual {
        source
            .coordinates
            .iter()
            .filter(|(name, coordinate)| coordinate.is_declared() && !self.coarse.0.contains(name))
            .map(|(name, coordinate)| (*name, coordinate.clone()))
            .collect()
    }

    fn reopen(&self, target: &Self::Target, residual: &Self::Residual) -> Self::Source {
        let mut reopened = target.clone();
        for (name, coordinate) in residual {
            reopened.coordinates.insert(*name, coordinate.clone());
        }
        reopened
    }
}

// ---------------------------------------------------------------------------------------------
// B3: the passage, and what transport drops
// ---------------------------------------------------------------------------------------------

/// One reading situated at the environment it was taken at.
///
/// Lean counterpart: `Foundation/PhysicalOccurrence.lean::SituatedReading`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct SituatedReading {
    /// Where the reading was taken.
    pub environment: Environment,
    /// Which addressed pair.
    pub pair: (u32, u32),
    /// What was read there.
    pub class: ContactClass,
}

/// **A typed passage between two environments.**
///
/// [definition] It carries a stated ground and must account for every axis the two environments
/// diverge in. [`Self::declare`] refuses a passage that omits one, so there is no partially
/// justified transport.
///
/// As a [`Transition`], its residual is the environment the claim was **read at** — exactly the
/// thing transport drops. Two claims read at two different environments with the same class become
/// the same transported claim, and [`Transition::separating_residuals`] returns the two
/// environments that still tell them apart.
///
/// Lean counterpart: `Foundation/PhysicalOccurrence.lean::Passage`, whose `complete` field is this
/// constructor's check.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(try_from = "EnvironmentPassageWire")]
pub struct EnvironmentPassage {
    /// The schema this passage serializes under.
    pub schema: String,
    /// The stated ground on which the passage is admitted.
    pub ground: String,
    from: Environment,
    to: Environment,
    accounted: BTreeSet<CoordinateName>,
}

impl EnvironmentPassage {
    /// Declare a passage. Refuses an unstated ground, and refuses any divergent axis the
    /// declaration does not account for, naming it.
    pub fn declare(
        ground: impl Into<String>,
        from: Environment,
        to: Environment,
        accounted: impl IntoIterator<Item = CoordinateName>,
    ) -> Result<Self, EnvironmentRefusal> {
        let ground = ground.into();
        if ground.trim().is_empty() {
            return Err(EnvironmentRefusal::PassageGroundNotStated);
        }
        let accounted = accounted.into_iter().collect::<BTreeSet<_>>();
        let disagreement = from.disagreement(&to);
        let unaccounted = disagreement
            .names()
            .into_iter()
            .filter(|name| !accounted.contains(name))
            .collect::<Vec<_>>();
        if !unaccounted.is_empty() {
            return Err(EnvironmentRefusal::CoordinatesUnaccounted { unaccounted });
        }
        Ok(Self {
            schema: "holonic-engine.environment-passage.v1".to_owned(),
            ground,
            from,
            to,
            accounted,
        })
    }

    /// The environment the passage leaves.
    pub const fn from(&self) -> &Environment {
        &self.from
    }

    /// The environment it arrives at.
    pub const fn to(&self) -> &Environment {
        &self.to
    }

    /// The axes it accounts for.
    pub const fn accounted(&self) -> &BTreeSet<CoordinateName> {
        &self.accounted
    }

    /// Whether this passage accounts for one axis.
    pub fn accounts_for(&self, name: CoordinateName) -> bool {
        self.accounted.contains(&name)
    }
}

impl Transition for EnvironmentPassage {
    type Source = SituatedReading;
    type Target = SituatedReading;
    type Residual = Environment;

    fn apply(&self, source: &Self::Source) -> Self::Target {
        SituatedReading {
            environment: self.to.clone(),
            pair: source.pair,
            class: source.class,
        }
    }

    fn residual(&self, source: &Self::Source) -> Self::Residual {
        source.environment.clone()
    }

    fn reopen(&self, target: &Self::Target, residual: &Self::Residual) -> Self::Source {
        SituatedReading {
            environment: residual.clone(),
            pair: target.pair,
            class: target.class,
        }
    }
}

// ---------------------------------------------------------------------------------------------
// B3: the occurrence
// ---------------------------------------------------------------------------------------------

/// An occurrence's identity in one population.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct OccurrenceId(pub u64);

/// How an occurrence came to exist. A designed structure, a prediction and a measurement are
/// different testimony and are never merged into "a structure".
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum OccurrenceKind {
    /// Emitted by a design generator.
    Designed {
        /// The generator.
        generator: String,
        /// How many rounds it ran.
        rounds: u32,
    },
    /// Emitted by a structure predictor at a declared seed.
    Predicted {
        /// The predictor.
        predictor: String,
        /// The sampling seed.
        seed: String,
    },
    /// Returned by an exterior apparatus.
    Measured {
        /// The apparatus.
        apparatus: String,
    },
}

/// **A structure face situated at one environment index.**
///
/// [definition] There is one constructor and it takes the environment by value. There is no path in
/// this module to an occurrence whose environment is absent, defaulted or inferred.
///
/// Lean counterpart: `Foundation/PhysicalOccurrence.lean::Occurrence`, the dependent pair
/// `Σ e, Face e`, whose `environment` is the first projection.
#[derive(Debug, Serialize, Deserialize)]
pub struct Occurrence {
    /// The schema this occurrence serializes under.
    pub schema: String,
    /// Its identity in the population.
    pub id: OccurrenceId,
    /// How it came to exist.
    pub kind: OccurrenceKind,
    /// Exterior lineage, retained as testimony.
    pub lineage: String,
    environment: Environment,
    face: PhysicalConstraintComplex,
}

impl Occurrence {
    /// Found the occurrence.
    pub fn found(
        id: OccurrenceId,
        kind: OccurrenceKind,
        lineage: impl Into<String>,
        environment: Environment,
        face: PhysicalConstraintComplex,
    ) -> Self {
        Self {
            schema: "holonic-engine.situated-physical-occurrence.v1".to_owned(),
            id,
            kind,
            lineage: lineage.into(),
            environment,
            face,
        }
    }

    /// The environment index. Total, because the occurrence cannot exist without it.
    pub const fn environment(&self) -> &Environment {
        &self.environment
    }

    /// The exact structure face.
    pub const fn face(&self) -> &PhysicalConstraintComplex {
        &self.face
    }

    /// The situated family of one declared cross population, classified by enacting the exact
    /// interval law against the supplied aperture.
    ///
    /// This is the path for an occurrence whose predictor emitted no uncertainty array: the classes
    /// are exact geometry and the uncertainty of each pair is `None` rather than fabricated.
    ///
    /// [definition] **Cross populations only.** `left == right` is refused by name: this reading
    /// enacts every pair of the product, and on the diagonal that product contains `(i, i)`, whose
    /// squared distance is zero and which every aperture therefore reads `Formed`. An occurrence
    /// is not in contact with itself, and co-presence is not contact. A within-component
    /// population is founded by the constraint owner under a declared sequence separation
    /// (`PhysicalConstraintComplex::found_within_component_contact_family`) and read here through
    /// [`Self::founded_family`], which takes it with its addressed pairs and its uncertainty.
    pub fn enacted_family(
        &self,
        left: ConstraintComponentId,
        right: ConstraintComponentId,
        aperture: &DistanceAperture,
    ) -> Result<SituatedFamily, StatusRefusal> {
        if left == right {
            return Err(StatusRefusal::EnactedFamilyIsCross { component: left });
        }
        let left_component = self.face.component(left)?;
        let right_component = self.face.component(right)?;
        let left_sequence = left_component.sequence.clone();
        let right_sequence = right_component.sequence.clone();
        let left_vertices = left_component.vertices.clone();
        let right_vertices = right_component.vertices.clone();
        let classes = enacted_classes(&self.face, left, right, aperture)?;
        let mut readings = Vec::with_capacity(classes.len());
        for (left_at, left_vertex) in left_vertices.iter().enumerate() {
            for (right_at, right_vertex) in right_vertices.iter().enumerate() {
                let at = left_at * right_vertices.len() + right_at;
                let squared_distance = self.face.vertices[left_vertex]
                    .position
                    .squared_distance(&self.face.vertices[right_vertex].position);
                readings.push(SituatedPairReading {
                    pair: (left_at as u32 + 1, right_at as u32 + 1),
                    class: classes[at],
                    squared_distance,
                    uncertainty: None,
                });
            }
        }
        Ok(SituatedFamily {
            schema: "holonic-engine.situated-contact-family.v1".to_owned(),
            occurrence: self.id,
            lineage: format!("{} / enacted against {}", self.lineage, aperture.lineage),
            environment: self.environment.clone(),
            left,
            right,
            left_sequence,
            right_sequence,
            aperture: aperture.clone(),
            readings,
        })
    }

    /// The situated family of a population the complex already carries as a founded contact
    /// family, so the directional uncertainty of every addressed pair travels with it.
    ///
    /// [definition] Both population laws reach this reading. `left == right` addresses the
    /// **within-component** family — the intra-chain contacts of one presented chain at a declared
    /// sequence separation — and its readings arrive with exactly the addressed pairs, classes,
    /// intervals and directional uncertainty the constraint owner founded them with. Nothing about
    /// this function distinguishes the two laws, because the contact law does not.
    pub fn founded_family(
        &self,
        receiver: impl Into<String>,
        left: ConstraintComponentId,
        right: ConstraintComponentId,
    ) -> Result<SituatedFamily, StatusRefusal> {
        let receiver = receiver.into();
        let family = self.face.contact_family(left, right)?;
        let left_sequence = self.face.component(left)?.sequence.clone();
        let right_sequence = self.face.component(right)?.sequence.clone();
        let readings = family
            .readings
            .iter()
            .map(|reading| SituatedPairReading {
                pair: (reading.left_ordinal, reading.right_ordinal),
                class: reading.class,
                squared_distance: reading.squared_distance.clone(),
                uncertainty: reading
                    .uncertainty
                    .as_ref()
                    .map(|pair| DirectionalUncertainty::from_pair(receiver.clone(), pair)),
            })
            .collect();
        Ok(SituatedFamily {
            schema: "holonic-engine.situated-contact-family.v1".to_owned(),
            occurrence: self.id,
            lineage: format!("{} / founded family", self.lineage),
            environment: self.environment.clone(),
            left,
            right,
            left_sequence,
            right_sequence,
            aperture: family.aperture.clone(),
            readings,
        })
    }
}

/// One addressed pair's reading within a situated family.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct SituatedPairReading {
    /// The one-based ordinals `found_contact_family` addresses.
    pub pair: (u32, u32),
    /// The exact geometric class. Authoritative and never overwritten by a status.
    pub class: ContactClass,
    /// The exact squared-distance interval it was classified from.
    pub squared_distance: ExactInterval,
    /// The directional uncertainty of the pair, when a receiver supplied one.
    pub uncertainty: Option<DirectionalUncertainty>,
}

/// One contact population, situated at one environment. `left == right` is the
/// within-component population of one presented chain, and any other pair is a cross population.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct SituatedFamily {
    /// The schema this family serializes under.
    pub schema: String,
    /// Which occurrence it belongs to.
    pub occurrence: OccurrenceId,
    /// Exterior lineage, retained as testimony.
    pub lineage: String,
    /// The environment every reading below is a claim at, and at no other site.
    pub environment: Environment,
    /// The left component.
    pub left: ConstraintComponentId,
    /// The right component.
    pub right: ConstraintComponentId,
    /// The left component's ordered monomer sequence, the kinship witness.
    pub left_sequence: Vec<String>,
    /// The right component's ordered monomer sequence.
    pub right_sequence: Vec<String>,
    /// The aperture the classes were taken against.
    pub aperture: DistanceAperture,
    /// Every addressed pair.
    pub readings: Vec<SituatedPairReading>,
}

impl SituatedFamily {
    /// The object this family is about: the two ordered monomer sequences. Equal kinship is what
    /// makes two families comparable at all; it never identifies the occurrences.
    pub fn kinship(&self) -> ObjectKinship {
        ObjectKinship {
            left_sequence: self.left_sequence.clone(),
            right_sequence: self.right_sequence.clone(),
        }
    }

    /// Every reading as a claim carrying the environment it was taken at.
    pub fn situated_readings(&self) -> Vec<SituatedReading> {
        self.readings
            .iter()
            .map(|reading| SituatedReading {
                environment: self.environment.clone(),
                pair: reading.pair,
                class: reading.class,
            })
            .collect()
    }
}

/// The object two families are about.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ObjectKinship {
    /// The left component's ordered monomers.
    pub left_sequence: Vec<String>,
    /// The right component's ordered monomers.
    pub right_sequence: Vec<String>,
}

// ---------------------------------------------------------------------------------------------
// B3: comparison, refused and lawful
// ---------------------------------------------------------------------------------------------

/// One addressed pair on which two families were compared.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct PairVerdict {
    /// The addressed pair.
    pub pair: (u32, u32),
    /// What the left family read.
    pub left: ContactClass,
    /// What the right family read.
    pub right: ContactClass,
}

/// The return of a comparison between two families **at one environment**.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ComparisonAtOneEnvironment {
    /// The schema this comparison serializes under.
    pub schema: String,
    /// The environment both claims are at.
    pub environment_lineage: String,
    /// How many pairs were compared.
    pub pairs: usize,
    /// How many read the same class.
    pub agreeing: usize,
    /// Every pair on which the two readings differ. The complete set, not the first one.
    pub separating: Vec<PairVerdict>,
}

/// The return of a comparison **carried across** environments by a supplied passage.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct TransportedComparison {
    /// The schema this comparison serializes under.
    pub schema: String,
    /// The environment the left claim was read at — the passage's own residual, retained rather
    /// than dropped by the transport.
    pub read_at: Environment,
    /// The environment it was carried to.
    pub carried_to: Environment,
    /// The ground the passage was admitted on.
    pub ground: String,
    /// The axes the passage accounted for.
    pub accounted: Vec<CoordinateName>,
    /// The comparison, once both claims sit at the same site.
    pub comparison: ComparisonAtOneEnvironment,
}

/// **Compare two situated families with no passage.**
///
/// Lawful only when both families are claims at the *same* environment value. Otherwise the return
/// is [`EnvironmentRefusal::EnvironmentsDiffer`] carrying the complete disagreement set.
///
/// Lean counterpart: `compareHere` and `compareReadings`, with
/// `compareReadings_refuses_naming_the_coordinates`.
pub fn compare_here(
    left: &SituatedFamily,
    right: &SituatedFamily,
) -> Result<ComparisonAtOneEnvironment, EnvironmentRefusal> {
    if left.environment != right.environment {
        return Err(EnvironmentRefusal::EnvironmentsDiffer {
            disagreement: Box::new(left.environment.disagreement(&right.environment)),
        });
    }
    compare_populations(left, right, &left.environment.lineage)
}

/// **Compare two situated families across environments, through a supplied passage.**
///
/// The passage must leave the left family's environment and arrive at the right family's, and it
/// must already account for every divergent axis — [`EnvironmentPassage::declare`] enforced that.
/// Every left reading is carried by [`Transition::apply`], and the environment it was read at comes
/// back from [`Transition::residual`] rather than being re-derived, so the claim's site is retained
/// in the return.
///
/// Lean counterpart: `compareAcross`, which takes the passage as an argument.
pub fn compare_through(
    left: &SituatedFamily,
    right: &SituatedFamily,
    passage: &EnvironmentPassage,
) -> Result<TransportedComparison, EnvironmentRefusal> {
    if passage.from() != &left.environment {
        return Err(EnvironmentRefusal::PassageDoesNotLeaveThisEnvironment {
            disagreement: Box::new(passage.from().disagreement(&left.environment)),
        });
    }
    if passage.to() != &right.environment {
        return Err(EnvironmentRefusal::PassageDoesNotArriveAtThisEnvironment {
            disagreement: Box::new(passage.to().disagreement(&right.environment)),
        });
    }
    let carried = left
        .situated_readings()
        .iter()
        .map(|reading| passage.apply(reading))
        .collect::<Vec<_>>();
    let read_at = left
        .situated_readings()
        .first()
        .map(|reading| passage.residual(reading))
        .unwrap_or_else(|| left.environment.clone());
    let carried_family = SituatedFamily {
        schema: left.schema.clone(),
        occurrence: left.occurrence,
        lineage: format!("{} / carried by {}", left.lineage, passage.ground),
        environment: passage.to().clone(),
        left: left.left,
        right: left.right,
        left_sequence: left.left_sequence.clone(),
        right_sequence: left.right_sequence.clone(),
        aperture: left.aperture.clone(),
        readings: left
            .readings
            .iter()
            .zip(&carried)
            .map(|(reading, situated)| SituatedPairReading {
                pair: situated.pair,
                class: situated.class,
                squared_distance: reading.squared_distance.clone(),
                uncertainty: reading.uncertainty.clone(),
            })
            .collect(),
    };
    let comparison =
        compare_populations(&carried_family, right, &right.environment.lineage)?;
    Ok(TransportedComparison {
        schema: "holonic-engine.transported-comparison.v1".to_owned(),
        read_at,
        carried_to: right.environment.clone(),
        ground: passage.ground.clone(),
        accounted: passage.accounted().iter().copied().collect(),
        comparison,
    })
}

fn compare_populations(
    left: &SituatedFamily,
    right: &SituatedFamily,
    environment_lineage: &str,
) -> Result<ComparisonAtOneEnvironment, EnvironmentRefusal> {
    if left.kinship() != right.kinship() {
        return Err(EnvironmentRefusal::ObjectKinshipDiffers);
    }
    if left.readings.len() != right.readings.len() {
        return Err(EnvironmentRefusal::PairPopulationDisagrees {
            left: left.readings.len(),
            right: right.readings.len(),
        });
    }
    let mut agreeing = 0_usize;
    let mut separating = Vec::new();
    for (a, b) in left.readings.iter().zip(&right.readings) {
        if a.pair != b.pair {
            return Err(EnvironmentRefusal::PairOrderDisagrees {
                left: a.pair,
                right: b.pair,
            });
        }
        if a.class == b.class {
            agreeing += 1;
        } else {
            separating.push(PairVerdict {
                pair: a.pair,
                left: a.class,
                right: b.class,
            });
        }
    }
    Ok(ComparisonAtOneEnvironment {
        schema: "holonic-engine.comparison-at-one-environment.v1".to_owned(),
        environment_lineage: environment_lineage.to_owned(),
        pairs: left.readings.len(),
        agreeing,
        separating,
    })
}

// ---------------------------------------------------------------------------------------------
// B3: vertical and horizontal families, kept apart by type
// ---------------------------------------------------------------------------------------------

/// **One object, several environments.** The vertical index of the carrier.
///
/// [definition] Every member is about the same object — equal ordered monomer sequences — and every
/// member sits at a *different* environment value. This constructor is the only way to a
/// [`ContactStatus::EnvironmentDependent`], so environment dependence cannot be derived from a
/// population that varies the object.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(try_from = "VerticalFamilyWire")]
pub struct VerticalFamily {
    /// The schema this family serializes under.
    pub schema: String,
    /// The object every member is about.
    pub object: ObjectKinship,
    members: Vec<SituatedFamily>,
}

impl VerticalFamily {
    /// Found the vertical family. Refuses an empty population, a member about a different object,
    /// and two members at the same environment value.
    pub fn over_one_object(members: Vec<SituatedFamily>) -> Result<Self, StatusRefusal> {
        let Some(first) = members.first() else {
            return Err(StatusRefusal::EmptyFamily);
        };
        let object = first.kinship();
        for member in &members {
            if member.kinship() != object {
                return Err(StatusRefusal::ObjectDiffersAlongTheVerticalIndex {
                    occurrence: member.occurrence,
                });
            }
        }
        for (at, member) in members.iter().enumerate() {
            for other in &members[at + 1..] {
                if member.environment == other.environment {
                    return Err(StatusRefusal::EnvironmentRepeatedAlongTheVerticalIndex {
                        left: member.occurrence,
                        right: other.occurrence,
                    });
                }
            }
        }
        Ok(Self {
            schema: "holonic-engine.vertical-environment-family.v1".to_owned(),
            object,
            members,
        })
    }

    /// The members, in declaration order.
    pub fn members(&self) -> &[SituatedFamily] {
        &self.members
    }

    /// **The status of every addressed pair across the family's environments.**
    ///
    /// A pair every member reads the same way takes that member's own static status. A pair read
    /// differently by two members is [`ContactStatus::EnvironmentDependent`], with the three
    /// environment lists naming exactly where each class was read.
    ///
    /// Lean counterpart: `acrossEnvironments`, with `acrossEnvironments_constant` and
    /// `acrossEnvironments_dependent_of_two_classes`.
    pub fn status_across(&self) -> Result<BTreeMap<(u32, u32), ContactStatus>, StatusRefusal> {
        let first = self.members.first().ok_or(StatusRefusal::EmptyFamily)?;
        for member in &self.members {
            if member.readings.len() != first.readings.len() {
                return Err(StatusRefusal::PairPopulationDisagrees {
                    left: first.occurrence,
                    right: member.occurrence,
                });
            }
        }
        let mut status = BTreeMap::new();
        for (at, reading) in first.readings.iter().enumerate() {
            let pair = reading.pair;
            let mut formed_at = Vec::new();
            let mut excluded_at = Vec::new();
            let mut open_at = Vec::new();
            let mut uniform = true;
            for member in &self.members {
                let member_reading = &member.readings[at];
                if member_reading.pair != pair {
                    return Err(StatusRefusal::PairOrderDisagrees {
                        left: first.occurrence,
                        right: member.occurrence,
                        pair,
                    });
                }
                if member_reading.class != reading.class {
                    uniform = false;
                }
                let situated = SituatedAt {
                    occurrence: member.occurrence,
                    environment_lineage: member.environment.lineage.clone(),
                };
                match member_reading.class {
                    ContactClass::Inside => formed_at.push(situated),
                    ContactClass::Outside => excluded_at.push(situated),
                    ContactClass::Open => open_at.push(situated),
                }
            }
            let derived = if uniform {
                static_status(
                    reading.class,
                    &first.aperture.squared,
                    &reading.squared_distance,
                )
            } else {
                ContactStatus::EnvironmentDependent(EnvironmentDependence {
                    pair,
                    formed_at,
                    excluded_at,
                    open_at,
                })
            };
            status.insert(pair, derived);
        }
        Ok(status)
    }

    /// The addressed pairs whose status is environment-dependent.
    pub fn environment_dependent_pairs(&self) -> Result<Vec<(u32, u32)>, StatusRefusal> {
        Ok(self
            .status_across()?
            .into_iter()
            .filter(|(_, status)| matches!(status, ContactStatus::EnvironmentDependent(_)))
            .map(|(pair, _)| pair)
            .collect())
    }
}

/// **One environment, several objects.** The horizontal index of the carrier.
///
/// [definition] Every member sits at the same environment value and they may be about different
/// objects. This is the direction a design population varies in, and it is deliberately a different
/// type from [`VerticalFamily`]: nothing here can produce an environment-dependent status, because
/// there is only one environment.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(try_from = "HorizontalFamilyWire")]
pub struct HorizontalFamily {
    /// The schema this family serializes under.
    pub schema: String,
    /// The environment every member is a claim at.
    pub environment: Environment,
    members: Vec<SituatedFamily>,
}

impl HorizontalFamily {
    /// Found the horizontal family. Refuses an empty population and any member at a different
    /// environment value, naming the axes it diverges in.
    pub fn at_one_environment(members: Vec<SituatedFamily>) -> Result<Self, StatusRefusal> {
        let Some(first) = members.first() else {
            return Err(StatusRefusal::EmptyFamily);
        };
        let environment = first.environment.clone();
        for member in &members {
            if member.environment != environment {
                return Err(StatusRefusal::Environment(
                    EnvironmentRefusal::EnvironmentsDiffer {
                        disagreement: Box::new(environment.disagreement(&member.environment)),
                    },
                ));
            }
        }
        Ok(Self {
            schema: "holonic-engine.horizontal-object-family.v1".to_owned(),
            environment,
            members,
        })
    }

    /// The members, in declaration order.
    pub fn members(&self) -> &[SituatedFamily] {
        &self.members
    }
}

// ---------------------------------------------------------------------------------------------
// B4: the contact status
// ---------------------------------------------------------------------------------------------

/// An exterior declaration with the ground that licenses it.
///
/// [definition] The fields are private and [`Self::declare`] refuses an empty statement, so this
/// value cannot be produced from a structure file, a distance, or nothing. `Deserialize` is
/// deliberately not derived: it would be a second constructor that bypasses the check.
///
/// Lean counterpart: `Foundation/PhysicalOccurrence.lean::ExteriorGround`, whose `stated` field is
/// this check carried as a proof.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct ExteriorDeclaration {
    statement: String,
    apparatus: String,
}

impl ExteriorDeclaration {
    /// Declare an exterior fact. Refuses an unstated statement or an unnamed apparatus.
    pub fn declare(
        statement: impl Into<String>,
        apparatus: impl Into<String>,
    ) -> Result<Self, StatusRefusal> {
        let statement = statement.into();
        let apparatus = apparatus.into();
        if statement.trim().is_empty() || apparatus.trim().is_empty() {
            return Err(StatusRefusal::ExteriorDeclarationNotStated);
        }
        Ok(Self {
            statement,
            apparatus,
        })
    }

    /// What is declared.
    pub fn statement(&self) -> &str {
        &self.statement
    }

    /// What apparatus or authority declared it.
    pub fn apparatus(&self) -> &str {
        &self.apparatus
    }
}

/// Where one class of a pair was read.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct SituatedAt {
    /// Which occurrence.
    pub occurrence: OccurrenceId,
    /// That occurrence's environment lineage, retained as testimony.
    pub environment_lineage: String,
}

/// One ordered pair read differently at different environments.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct EnvironmentDependence {
    /// The addressed pair.
    pub pair: (u32, u32),
    /// Where it read `Inside`.
    pub formed_at: Vec<SituatedAt>,
    /// Where it read `Outside`.
    pub excluded_at: Vec<SituatedAt>,
    /// Where it read `Open`.
    pub open_at: Vec<SituatedAt>,
}

/// A declared valence at one site: how many contacts that site can carry at once.
///
/// [definition] This is the exclusion this owner computes, and it is stated rather than inferred.
/// `Deserialize` is not derived, for the same reason as [`ExteriorDeclaration`].
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct ValenceDeclaration {
    /// The site.
    pub site: ConstraintVertexId,
    /// How many contacts it can carry at once.
    pub valence: u32,
    /// The ground the valence is declared on.
    ground: String,
}

impl ValenceDeclaration {
    /// Declare a valence. A valence of zero is admitted — it is the statement that the site carries
    /// no contact at all — but an unstated ground is not.
    pub fn declare(
        site: ConstraintVertexId,
        valence: u32,
        ground: impl Into<String>,
    ) -> Result<Self, StatusRefusal> {
        let ground = ground.into();
        if ground.trim().is_empty() {
            return Err(StatusRefusal::ValenceGroundNotStated { site });
        }
        Ok(Self {
            site,
            valence,
            ground,
        })
    }

    /// The ground.
    pub fn ground(&self) -> &str {
        &self.ground
    }
}

/// A competition at one site: more formed contenders than the declared valence can carry.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct Competition {
    /// The site.
    pub site: ConstraintVertexId,
    /// The declared valence.
    pub declared_valence: u32,
    /// Every formed contender. All of them compete; none is privileged.
    pub contenders: Vec<ConstraintEdge>,
    /// The ground the valence was declared on, carried into the verdict.
    pub ground: String,
}

/// What one site actually carries, with the open contenders retained apart from the formed ones.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct SiteOccupancy {
    /// The site.
    pub site: ConstraintVertexId,
    /// The declared valence.
    pub declared_valence: u32,
    /// The contacts at this site whose status is `Formed`.
    pub formed: Vec<ConstraintEdge>,
    /// The contacts at this site whose status is `Open`. Never counted as formed, and never
    /// dropped: an undecided reading can neither create nor dissolve a competition.
    pub open: Vec<ConstraintEdge>,
    /// The competition, when the formed contenders exceed the valence.
    pub competition: Option<Competition>,
}

/// **The status of one contact edge.** Six states with six different evidence requirements.
///
/// [definition] `Deserialize` is deliberately not derived. See the module header.
///
/// Lean counterpart: `Foundation/PhysicalOccurrence.lean::ContactStatus`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub enum ContactStatus {
    /// The exact interval's upper bound is at or below the aperture.
    Formed,
    /// The exact interval's lower bound is strictly above the aperture.
    Excluded,
    /// The exact interval straddles the aperture. The reading stays plural and carries what would
    /// be needed to decide it.
    Open {
        /// The aperture that could not decide it.
        aperture_squared: Rat,
        /// The exact interval.
        squared_distance: ExactInterval,
    },
    /// Admitted **only** from an exterior declaration. No static structure produces it.
    KineticallyInaccessible(ExteriorDeclaration),
    /// The same ordered pair reads differently at different environments.
    EnvironmentDependent(EnvironmentDependence),
    /// The contact competes for a site whose declared valence cannot carry every contender.
    Competing(Competition),
}

impl ContactStatus {
    /// Admit a kinetic inaccessibility from an exterior declaration. This is the only constructor
    /// of that variant that exists outside a pattern match, and it takes the declaration by value.
    pub const fn kinetically_inaccessible(declaration: ExteriorDeclaration) -> Self {
        Self::KineticallyInaccessible(declaration)
    }

    /// A short name for receipts.
    pub const fn label(&self) -> &'static str {
        match self {
            Self::Formed => "formed",
            Self::Excluded => "excluded",
            Self::Open { .. } => "open",
            Self::KineticallyInaccessible(_) => "kinetically-inaccessible",
            Self::EnvironmentDependent(_) => "environment-dependent",
            Self::Competing(_) => "competing",
        }
    }

    /// Whether this status was reachable from a static structure alone.
    pub const fn is_static(&self) -> bool {
        matches!(self, Self::Formed | Self::Excluded | Self::Open { .. })
    }
}

/// **The static exact law.** The only function in this module from a static structure to a status.
///
/// [proved-derived] Its image is exactly `{Formed, Excluded, Open}`; it attains all three, and it
/// reaches none of the other three states. `Open` is derived from the exact interval contact law
/// and carries both the aperture and the interval, so nothing downstream has to go back to the
/// complex to re-decide it.
///
/// Lean counterpart: `staticStatus` and `staticStatusOfInterval`, with
/// `static_law_reaches_exactly_three`.
pub fn static_status(
    class: ContactClass,
    aperture_squared: &Rat,
    squared_distance: &ExactInterval,
) -> ContactStatus {
    match class {
        ContactClass::Inside => ContactStatus::Formed,
        ContactClass::Outside => ContactStatus::Excluded,
        ContactClass::Open => ContactStatus::Open {
            aperture_squared: aperture_squared.clone(),
            squared_distance: squared_distance.clone(),
        },
    }
}

/// **What one site carries under a declared valence, and whether that is a competition.**
///
/// The contenders are the edges incident to the site whose status is [`ContactStatus::Formed`].
/// Competition holds exactly when there are more of them than the valence admits. Edges whose
/// status is [`ContactStatus::Open`] are retained in [`SiteOccupancy::open`] and are never counted:
/// an undecided reading neither creates nor dissolves a competition.
///
/// Lean counterpart: `valenceCompetition`, with `competing_iff_contenders_exceed_valence` and
/// `no_competition_within_valence`.
pub fn site_occupancy(
    declaration: &ValenceDeclaration,
    statuses: &BTreeMap<ConstraintEdge, ContactStatus>,
) -> SiteOccupancy {
    let mut formed = Vec::new();
    let mut open = Vec::new();
    for (edge, status) in statuses {
        if edge.lower != declaration.site && edge.upper != declaration.site {
            continue;
        }
        match status {
            ContactStatus::Formed => formed.push(*edge),
            ContactStatus::Open { .. } => open.push(*edge),
            _ => {}
        }
    }
    let competition = if formed.len() as u64 > u64::from(declaration.valence) {
        Some(Competition {
            site: declaration.site,
            declared_valence: declaration.valence,
            contenders: formed.clone(),
            ground: declaration.ground.clone(),
        })
    } else {
        None
    };
    SiteOccupancy {
        site: declaration.site,
        declared_valence: declaration.valence,
        formed,
        open,
        competition,
    }
}

// ---------------------------------------------------------------------------------------------
// B4: directional uncertainty
// ---------------------------------------------------------------------------------------------

/// The directional uncertainty of one **ordered** pair.
///
/// [definition] `PAE(i→j)` and `PAE(j→i)` differ in general, so both are carried whole with their
/// own units in the last place. This type exposes no mean, no minimum, no maximum and no other
/// symmetric summary: every such function factors through a symmetrization and merges two readings
/// the predictor kept apart.
///
/// Lean counterpart: `DirectionalReading`, with `symmetrization_merges_a_distinguishable_pair`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct DirectionalUncertainty {
    /// Which receiver supplied it.
    pub receiver: String,
    /// Exterior lineage of the source, retained as testimony.
    pub source_lineage: String,
    /// The reading in the presented direction, exact.
    pub forward: ExactInterval,
    /// One unit in the last place of the format the forward reading was stored in.
    pub forward_ulp: Rat,
    /// The reading in the opposite direction, exact.
    pub reverse: ExactInterval,
    /// One unit in the last place of the format the reverse reading was stored in.
    pub reverse_ulp: Rat,
}

impl DirectionalUncertainty {
    /// Read one from the wire type `physical_constraint_complex` carries.
    pub fn from_pair(receiver: impl Into<String>, pair: &PairUncertainty) -> Self {
        Self {
            receiver: receiver.into(),
            source_lineage: pair.source_lineage.clone(),
            forward: pair.row_given_column.clone(),
            forward_ulp: pair.row_given_column_ulp.clone(),
            reverse: pair.column_given_row.clone(),
            reverse_ulp: pair.column_given_row_ulp.clone(),
        }
    }

    /// The same reading with the ordered pair swapped. An involution, and **not** the identity on
    /// an asymmetric reading — which is how a caller exhibits the asymmetry rather than erasing it.
    pub fn transposed(&self) -> Self {
        Self {
            receiver: self.receiver.clone(),
            source_lineage: self.source_lineage.clone(),
            forward: self.reverse.clone(),
            forward_ulp: self.reverse_ulp.clone(),
            reverse: self.forward.clone(),
            reverse_ulp: self.forward_ulp.clone(),
        }
    }

    /// Whether the two directions carry different values.
    pub fn is_asymmetric(&self) -> bool {
        self.forward != self.reverse
    }
}

// ---------------------------------------------------------------------------------------------
// Refusals
// ---------------------------------------------------------------------------------------------

/// Why an environment, a passage or a comparison refused.
#[derive(Clone, Debug, PartialEq, Eq, Error)]
pub enum EnvironmentRefusal {
    /// A coordinate was declared with no ground. A value with no ground is a default.
    #[error("the {name} coordinate was declared with no stated ground, which is a default")]
    GroundNotStated {
        /// The axis.
        name: CoordinateName,
    },
    /// A coordinate was left undeclared with no statement of why.
    #[error("an undeclared coordinate needs a stated reason; an empty one is a default")]
    UndeclarationNotStated,
    /// A declared value was filed under an axis it does not belong to.
    #[error("a {belongs_to} value was filed under the {filed_under} coordinate")]
    CoordinateMisfiled {
        /// Where it was filed.
        filed_under: CoordinateName,
        /// Where it belongs.
        belongs_to: CoordinateName,
    },
    /// An axis was supplied twice.
    #[error("the {name} coordinate was supplied twice")]
    CoordinateRepeated {
        /// The axis.
        name: CoordinateName,
    },
    /// An environment was founded without every axis.
    #[error(
        "the environment leaves {absent:?} unstated. Every coordinate must be declared with a \
         ground or explicitly undeclared with a reason; there is no default"
    )]
    CoordinatesAbsent {
        /// Every absent axis, named.
        absent: Vec<CoordinateName>,
    },
    /// A passage was declared with no ground.
    #[error("a passage between two environments needs a stated ground")]
    PassageGroundNotStated,
    /// A passage does not account for an axis the two environments diverge in.
    #[error(
        "the passage does not account for {unaccounted:?}; a claim cannot be carried across a \
         coordinate the passage says nothing about"
    )]
    CoordinatesUnaccounted {
        /// Every unaccounted axis, named.
        unaccounted: Vec<CoordinateName>,
    },
    /// Two claims were compared without a passage, and they are at different environments.
    #[error(
        "these are claims at two environments and no passage was supplied; they diverge in \
         {}. A reading taken at one environment is a claim at that environment only",
        render_names(&disagreement.names())
    )]
    EnvironmentsDiffer {
        /// The complete divergence.
        disagreement: Box<EnvironmentDisagreement>,
    },
    /// A passage was supplied that does not leave the left claim's environment.
    #[error(
        "the supplied passage does not leave this claim's environment; they diverge in {}",
        render_names(&disagreement.names())
    )]
    PassageDoesNotLeaveThisEnvironment {
        /// The divergence between the passage's source and the claim's environment.
        disagreement: Box<EnvironmentDisagreement>,
    },
    /// A passage was supplied that does not arrive at the right claim's environment.
    #[error(
        "the supplied passage does not arrive at this claim's environment; they diverge in {}",
        render_names(&disagreement.names())
    )]
    PassageDoesNotArriveAtThisEnvironment {
        /// The divergence between the passage's target and the claim's environment.
        disagreement: Box<EnvironmentDisagreement>,
    },
    /// Two families are about different objects, so there is nothing to compare.
    #[error("the two families are about different objects; their ordered monomers disagree")]
    ObjectKinshipDiffers,
    /// Two families address different numbers of pairs.
    #[error("the two families address {left} and {right} pairs")]
    PairPopulationDisagrees {
        /// How many the left family addresses.
        left: usize,
        /// How many the right family addresses.
        right: usize,
    },
    /// Two families are not in the same addressed pair order.
    #[error("the two families are not in the same pair order: {left:?} against {right:?}")]
    PairOrderDisagrees {
        /// The left family's pair.
        left: (u32, u32),
        /// The right family's pair.
        right: (u32, u32),
    },
    /// A wire named a schema this owner does not found.
    #[error("the wire names schema {presented:?}; this owner founds {expected:?}")]
    SchemaNotThisOwner {
        /// The schema the constructor stamps.
        expected: &'static str,
        /// The schema the wire carried.
        presented: String,
    },
}

// ---------------------------------------------------------------------------------------------
// The remount law: every deserialization goes through the same constructor a founding does
// ---------------------------------------------------------------------------------------------

/// The wire shape of a [`Coordinate`].  It is the *only* thing serde builds directly; the value it
/// is converted into is built by [`Coordinate::declared`] / [`Coordinate::undeclared`], so a wire
/// carrying an empty ground or an empty undeclaration reason is refused at the boundary rather
/// than becoming a `Coordinate` no constructor would have admitted.
#[derive(Deserialize)]
enum CoordinateWire {
    Declared {
        value: CoordinateValue,
        ground: String,
    },
    Undeclared {
        why: String,
    },
}

impl TryFrom<CoordinateWire> for Coordinate {
    type Error = EnvironmentRefusal;

    fn try_from(wire: CoordinateWire) -> Result<Self, Self::Error> {
        match wire {
            CoordinateWire::Declared { value, ground } => Coordinate::declared(value, ground),
            CoordinateWire::Undeclared { why } => Coordinate::undeclared(why),
        }
    }
}

/// The wire shape of an [`Environment`].  Converted through [`Environment::found`], so a wire
/// missing an axis, repeating one, or filing a value under the wrong axis is refused.
#[derive(Deserialize)]
struct EnvironmentWire {
    schema: String,
    lineage: String,
    presented: PresentedEnvironmentIndex,
    coordinates: BTreeMap<CoordinateName, Coordinate>,
}

impl TryFrom<EnvironmentWire> for Environment {
    type Error = EnvironmentRefusal;

    fn try_from(wire: EnvironmentWire) -> Result<Self, Self::Error> {
        let founded = Environment::found(wire.lineage, wire.presented, wire.coordinates)?;
        if wire.schema != founded.schema {
            return Err(EnvironmentRefusal::SchemaNotThisOwner {
                expected: "holonic-engine.typed-environment-index.v1",
                presented: wire.schema,
            });
        }
        Ok(founded)
    }
}

/// The wire shape of an [`EnvironmentPassage`].  Converted through
/// [`EnvironmentPassage::declare`], so a wire with an unstated ground, or one that leaves a
/// divergent axis unaccounted, is refused.
#[derive(Deserialize)]
struct EnvironmentPassageWire {
    schema: String,
    ground: String,
    from: Environment,
    to: Environment,
    accounted: BTreeSet<CoordinateName>,
}

impl TryFrom<EnvironmentPassageWire> for EnvironmentPassage {
    type Error = EnvironmentRefusal;

    fn try_from(wire: EnvironmentPassageWire) -> Result<Self, Self::Error> {
        let declared =
            EnvironmentPassage::declare(wire.ground, wire.from, wire.to, wire.accounted)?;
        if wire.schema != declared.schema {
            return Err(EnvironmentRefusal::SchemaNotThisOwner {
                expected: "holonic-engine.environment-passage.v1",
                presented: wire.schema,
            });
        }
        Ok(declared)
    }
}

/// The wire shape of a [`VerticalFamily`].  Converted through [`VerticalFamily::over_one_object`],
/// so a wire with no members, with a member about a different object, or with two members at the
/// same environment value is refused — and the `object` the wire claims must be the kinship the
/// members actually carry.
#[derive(Deserialize)]
struct VerticalFamilyWire {
    schema: String,
    object: ObjectKinship,
    members: Vec<SituatedFamily>,
}

impl TryFrom<VerticalFamilyWire> for VerticalFamily {
    type Error = StatusRefusal;

    fn try_from(wire: VerticalFamilyWire) -> Result<Self, Self::Error> {
        let founded = VerticalFamily::over_one_object(wire.members)?;
        if wire.schema != founded.schema || wire.object != founded.object {
            return Err(StatusRefusal::Environment(
                EnvironmentRefusal::SchemaNotThisOwner {
                    expected: "holonic-engine.vertical-environment-family.v1",
                    presented: wire.schema,
                },
            ));
        }
        Ok(founded)
    }
}

/// The wire shape of a [`HorizontalFamily`].  Converted through
/// [`HorizontalFamily::at_one_environment`], so a wire with no members or with a member at a
/// different environment value is refused, naming the axes it diverges in.
#[derive(Deserialize)]
struct HorizontalFamilyWire {
    schema: String,
    environment: Environment,
    members: Vec<SituatedFamily>,
}

impl TryFrom<HorizontalFamilyWire> for HorizontalFamily {
    type Error = StatusRefusal;

    fn try_from(wire: HorizontalFamilyWire) -> Result<Self, Self::Error> {
        let founded = HorizontalFamily::at_one_environment(wire.members)?;
        if wire.schema != founded.schema || wire.environment != founded.environment {
            return Err(StatusRefusal::Environment(
                EnvironmentRefusal::SchemaNotThisOwner {
                    expected: "holonic-engine.horizontal-object-family.v1",
                    presented: wire.schema,
                },
            ));
        }
        Ok(founded)
    }
}

/// Render a set of axis names for a refusal message.
fn render_names(names: &BTreeSet<CoordinateName>) -> String {
    if names.is_empty() {
        return "no coordinate".to_owned();
    }
    names
        .iter()
        .map(|name| name.label())
        .collect::<Vec<_>>()
        .join(", ")
}

/// Why a status derivation or a family refused.
#[derive(Clone, Debug, PartialEq, Eq, Error)]
pub enum StatusRefusal {
    /// A family was founded over no members.
    #[error("a family over no members is not a measurement")]
    EmptyFamily,
    /// An enacted family was addressed at one component against itself.
    #[error(
        "component {component:?} was addressed against itself; an enacted family reads every pair \
         of the product, and on the diagonal that includes an occurrence against itself, which \
         every aperture reads as a contact. Found the within-component family on the constraint \
         complex under a declared sequence separation and read it through founded_family"
    )]
    EnactedFamilyIsCross {
        /// The component addressed against itself.
        component: ConstraintComponentId,
    },
    /// A vertical family was offered a member about a different object.
    #[error(
        "occurrence {occurrence:?} is about a different object; the vertical index varies the \
         environment around one object and never the object"
    )]
    ObjectDiffersAlongTheVerticalIndex {
        /// The offending member.
        occurrence: OccurrenceId,
    },
    /// A vertical family was offered two members at the same environment.
    #[error(
        "occurrences {left:?} and {right:?} sit at the same environment, so they are not two \
         points of the vertical index"
    )]
    EnvironmentRepeatedAlongTheVerticalIndex {
        /// The first member.
        left: OccurrenceId,
        /// The second.
        right: OccurrenceId,
    },
    /// Two members of a family address different numbers of pairs.
    #[error("occurrences {left:?} and {right:?} address different pair populations")]
    PairPopulationDisagrees {
        /// The first member.
        left: OccurrenceId,
        /// The second.
        right: OccurrenceId,
    },
    /// Two members of a family are not in the same addressed pair order.
    #[error("occurrences {left:?} and {right:?} disagree on the pair at {pair:?}")]
    PairOrderDisagrees {
        /// The first member.
        left: OccurrenceId,
        /// The second.
        right: OccurrenceId,
        /// The pair the first member addresses there.
        pair: (u32, u32),
    },
    /// An exterior declaration carried no statement or no apparatus.
    #[error(
        "kinetic inaccessibility is not a geometric fact; it is admitted only from an exterior \
         declaration carrying both a statement and the apparatus that made it"
    )]
    ExteriorDeclarationNotStated,
    /// A valence was declared with no ground.
    #[error("the valence declared at site {site:?} carries no stated ground")]
    ValenceGroundNotStated {
        /// The site.
        site: ConstraintVertexId,
    },
    /// The environment owner refused.
    #[error("the environment refused: {0}")]
    Environment(#[from] EnvironmentRefusal),
    /// The exact constraint complex refused.
    #[error("the constraint complex refused: {0}")]
    Constraint(#[from] ConstraintError),
    /// The library intake refused.
    #[error("the intake refused: {0}")]
    Intake(#[from] IntakeRefusal),
}

// ---------------------------------------------------------------------------------------------
// B5 and B6: the plural fibre and the typed passage, in this owner's own submodules
// ---------------------------------------------------------------------------------------------

// Reachable from `design_selection`'s tests too: B8's real-data exhibition is the same three
// M5 presentations, and a second copy of those builders is exactly the drift this module exists to
// prevent.
#[cfg(test)]
pub(crate) mod fixture;
pub mod passage;
pub mod plural_fibre;

pub use passage::{
    ConstraintDelta, EXACT_CLASS_FIBRE_CEILING, EnvironmentDelta, Horizontal, OccurrenceFace,
    PairTransition, Passage, PassageAxis, PassageEnd, PassageEvent, PassageRefusal,
    PassageResidual, PassageStep, Vertical, exact_class_fibre_admits,
};
pub use plural_fibre::{
    ContactRole, DecidedClass, FibrePartition, FibreRefusal, HittingSetBound, MinimalSeparation,
    PairwiseSeparator, PluralFibre, RealizationProof, SeparatingContact, UnanimityReceipt,
};

#[cfg(test)]
#[path = "physical_occurrence/tests.rs"]
mod tests;

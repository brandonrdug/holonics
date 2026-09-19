//! **The physicochemical receiver: what a static structure and a declared parameter table can say.**
//!
//! [definition] This module is the remaining half of item **B7** of
//! `docs/plans/THE_BIOLOGICAL_ECOLOGY_INSTANTIATES_THE_CARRIER.md`, beside
//! [`crate::rigidity_receiver`] (R4) and [`crate::topological_receiver`] (R5). It reads the exact
//! contact complex [`crate::physical_constraint_complex`] founds, together with a **declared**
//! chemical parameter table, and returns residue-class contact composition, hydrogen-bond
//! *candidates*, steric overlaps, a burial *proxy*, exact interface counts and ratios, and an
//! electrostatic sum carried as an exact enclosure.
//!
//! It is a receiver in the sense of
//! `docs/plans/THE_RECEIVER_ATLAS_SEPARATES_WHAT_ONE_FACE_CANNOT.md`: a participating Holon, every
//! reading carrying its source, and a reading never the identity of its source.
//!
//! # What this receiver refuses to pretend
//!
//! AGENTS.md: *physical claims owe typed units/charts, constitutive and boundary laws, chronology
//! and calibrated receivers*, and *name scientific work affirmatively at its realized scope,
//! describing its equations, degrees of freedom and approximations.* Four consequences are built
//! into the types here.
//!
//! 1. **Every reading is available with its unit, and every magnitude that combines with another
//!    carries one.** [`UnitedInterval`] is an [`ExactInterval`] together with a [`Dimension`] over
//!    a declared [`BaseUnits`], and [`UnitedInterval::sum`] refuses two unlike dimensions by name.
//!    A reading whose wire is a bare exact integer or a bare exact rational — a count, a declared
//!    radius, a threshold — publishes its dimensioned form beside it
//!    ([`CompositionReading::admitted_count`], [`BurialProxyReading::radius_quantity`],
//!    [`StericOverlap::threshold_quantity`], [`RadiusTable::radius_of`],
//!    [`FormalChargeTable::charge_of`]), and the laws are stated on the dimensioned form. The unit algebra is not founded here: it is
//!    [`crate::quantity`], which already owns `BaseUnits`, `Dimension`, `Quantity` and `Cast`.
//!    The concretely absent object was the *enclosure*-valued quantity — `Quantity` carries a
//!    point magnitude and every magnitude this receiver returns is an interval — so
//!    `UnitedInterval` is that one composition and nothing more.
//! 2. **No table is built in.** Residue classes, formal charges at a declared protonation state,
//!    hydrogen-bond donor and acceptor atom names, van der Waals radii and the dielectric are each
//!    an exterior declaration with a [`TableGround`] naming its source and its scope, carried by
//!    value into every reading exactly as `physical_intake::EnvironmentIndex` is. This owner ships
//!    *named* declarations the caller chooses among; it supplies no default. A reading taken with
//!    one [`ParameterTables`] is **not** comparable with one taken with another without a supplied
//!    [`TablePassage`] — the same no-silent-transport law
//!    `physical_occurrence::EnvironmentPassage` enforces across environments.
//! 3. **A charged reading needs a declared pH.** The classes `PositivelyCharged` and
//!    `NegativelyCharged`, and every formal charge, are claims about a protonation state. When the
//!    occurrence's environment leaves the acidity axis undeclared, [`protonation_basis`] returns
//!    [`PhysicochemicalRefusal::AcidityUndeclared`] naming the coordinate and carrying the
//!    environment's own stated reason. **On the M5 release that refusal is the primary result**:
//!    neither the designed structure nor either Protenix prediction records a pH anywhere. The
//!    reading is then obtained only under an explicitly declared assumption whose ground travels
//!    with it ([`ProtonationBasis::DeclaredAssumption`]).
//! 4. **The names say what the readings are.** There is no `HydrogenBond` type in this module,
//!    only [`HydrogenBondCandidate`]: a static heavy-atom model carries no hydrogen and cannot
//!    certify the geometry of a bond. There is no `solvent_accessible_surface_area`, because a
//!    rolling-probe area is a numerical integral and this library takes none; what is offered
//!    instead is [`neighbour_count_proxy`], an exact integer count named a proxy, and
//!    [`half_sphere_exposure`], the exact count of neighbours on each side of the plane through a
//!    site normal to a declared reference direction. Neither is an area and neither is called one.
//!
//! # The exact laws
//!
//! [proved-derived; implemented-exact] Every distance question goes through
//! [`DistanceAperture::classify`] — the one exact `Inside`/`Outside`/`Open` interval law the
//! constraint owner already enacts — so an undecided reading is undecided here too and is carried,
//! never rounded. A composition over a family carrying `Open` contacts is therefore a **family of
//! readings** between [`CompositionReading::refusing_bound`] and
//! [`CompositionReading::admitting_bound`], exactly as `physical_constraint_grading` carries the
//! incidence plurally.
//!
//! Readings are additive over disjoint contact families ([`CompositionReading::sum`]), so an
//! interface family and a within-component fold family decompose exactly — their populations are
//! disjoint by `Foundation/AperturedGradedComplex.lean::withinPairs_disjoint_crossPairs`.
//!
//! [proved-derived; implemented-exact] **Rigid motion.** Every reading is a function of the
//! pairwise squared distances and the declared site chemistry alone, so it is unchanged by any
//! motion preserving those distances. Two statements are separated here rather than merged:
//! a **translation** by an exact rational vector preserves an interval coordinate box exactly and
//! is therefore an invariance of every reading on every presentation; a **rotation** maps an
//! axis-aligned box to a set that is not an axis-aligned box, so the full rigid-motion invariance
//! is stated at *point* configurations, which is the same domain
//! `rigidity_receiver::ExactConfiguration::from_presented` admits. This owner re-encloses nothing
//! silently.
//!
//! # The electrostatic model, at its realized scope
//!
//! [established-bounded; implemented-exact] [`electrostatic_enclosure`] returns
//!
//! ```text
//! U = Σ_{i<j} q_i q_j / (ε r_ij)
//! ```
//!
//! over a **declared** pair population, with `q` read from a declared [`FormalChargeTable`] at a
//! declared protonation basis, `ε` a declared [`Dielectric`] with its ground, and the result
//! carried in the unit `e² Å⁻¹` — a [`UnitedInterval`], not a number. `1/r` is irrational for a
//! rational `r²`, so it is carried as an exact enclosure: certified rational bounds from
//! `exact_value::AlgebraicRoot::reciprocal_square_root`, which isolates `1/√s` with a Sturm
//! certificate. Nothing is rounded and no float appears.
//!
//! Its approximations, stated affirmatively: point charges at the declared sites and nowhere else;
//! one uniform declared relative permittivity; no solvent and no ions; no polarization and no
//! induced dipoles; no charge screening beyond the dielectric; and the sum runs over the declared
//! pair population only, so a declared cutoff is part of the model and is carried in the reading.
//! It is a **declared finite electrostatic model**, and the reading says so in
//! [`ElectrostaticReading::approximations`]. Converting it to an energy is a
//! [`quantity::Cast`] the caller supplies — [`declared_coulomb_cast`] is one named declaration —
//! and the chart change is returned as a [`CastApplication`] rather than performed silently.
//!
//! # The remount law, and what has no literal
//!
//! [definition] **No type in this module derives `Deserialize` and none has a `Default`**, so no
//! wire and no default reconstructs any of them: a declaration is re-founded through its
//! constructor or it does not exist. Every declaration type keeps its fields private behind a
//! checked constructor — [`TableGround`], [`ResidueClassTable`], [`FormalChargeTable`],
//! [`HydrogenBondTable`], [`RadiusTable`], [`Dielectric`], [`ParameterTables`], [`TablePassage`],
//! [`PairWorkBound`], [`HydrogenBondWindow`], [`SiteTable`], [`ReferenceDirections`],
//! [`RigidMotion`] and [`UnitedInterval`] — and the reading types are receipts with public fields,
//! written out and re-founded by the functions that produce them.
//!
//! [definition] Two arms have **no literal anywhere**, which is the shape
//! `receiver_atlas::Recomputed` already uses. [`ProtonationBasis::FromEnvironment`] carries a
//! [`DeclaredAcidity`] whose only constructor is private to this module and is reached only from
//! [`protonation_basis`], so that arm cannot be written by a caller who did not read an
//! environment declaring the axis; and [`ProtonationBasis::DeclaredAssumption`] carries
//! `physical_occurrence::ExteriorDeclaration`, whose `declare` refuses an empty statement or an
//! unnamed apparatus. There is no third way to a charged reading.
//!
//! # Declared sizes are bounded before the work they size
//!
//! [definition] Two caller declarations size work here and both are checked first. A
//! [`PairPopulation`]'s extent — `n(n−1)/2` over a declared site set, `|S|·n` for a set against a
//! presentation — is taken with checked arithmetic and admitted by a declared [`PairWorkBound`]
//! **before** any pair is enumerated or any vector exists. The dyadic grain of a reciprocal square
//! root sizes an integer square root's `1 << 2·octaves` shift, so it is checked against
//! [`OCTAVE_CEILING`] before the shift is taken.
//!
//! # The paired Lean owner
//!
//! `formal/elementary-holonics/ElementaryHolonics/Foundation/PhysicochemicalReceiver.lean`,
//! namespace `Soma.Holonics.Foundation.PhysicochemicalReceiver`.
//!
//! | Lean declaration | Rust owner |
//! |---|---|
//! | `Dim`, `Dim.add`, `Dim.sub`, `Dim.zero` | [`Dimension`] over [`physicochemical_base`] |
//! | `United`, `United.sum?`, `united_sum_requires_equal_dimension` | [`UnitedInterval`], [`UnitedInterval::sum`] |
//! | `United.contains`, `united_sum_contains_sum` | [`UnitedInterval::contains`], interval addition |
//! | `united_contains_of_narrower` | [`UnitedInterval::contained_in`] |
//! | `ResidueClass`, `ClassPair`, `classPair`, `classPair_symm` | [`ResidueClass`], [`ClassPair`], [`ClassPair::of`] |
//! | `Table`, `classOf`, `tables_change_the_reading` | [`ResidueClassTable`], [`ResidueClassTable::class_of`] |
//! | `Admission`, `admit`, `Presentation` | [`ContactClass`], [`DistanceAperture::classify`] |
//! | `composition`, `composition_additive_of_disjoint` | [`CompositionReading`], [`CompositionReading::sum`] |
//! | `admittingComposition`, `openComposition`, `refusing_le_admitting` | [`CompositionReading::refusing_bound`], [`CompositionReading::admitting_bound`] |
//! | `admitting_eq_refusing_add_open`, `admitting_eq_refusing_of_no_undecided` | the open family of readings |
//! | `composition_invariant_under_relabelling` | the addressed-relabelling law of [`CompositionReading`] |
//! | `composition_invariant_under_isometry`, `derivedAdmit` | the rigid-motion law, [`RigidMotion`] |
//! | `Geometry`, `candidate`, `candidate_ignores_hydrogen_geometry` | [`HydrogenBondCandidate`], which carries no hydrogen |
//! | `two_geometries_one_candidate_reading` | there is no `HydrogenBond` type in this module |
//! | `invEnclosure_contains`, `invEnclosure_narrows` | [`reciprocal_distance_enclosure`] |
//! | `coulombTerm`, `coulombSum`, `coulombSum_enclosed`, `coulombSum_additive` | [`electrostatic_enclosure`]. `coulombSum_enclosed` is proved for nonnegative charges only; the signed sum this function takes is enclosed by `ExactInterval::times`' four-corner product, implemented-exact and tested on mixed-sign material, without a Lean counterpart |
//! | `ProtonationBasis`, `chargedReading`, `no_charged_reading_without_a_declared_acidity` | [`ProtonationBasis`], [`protonation_basis`] |
//! | `physicochemical_contract` | the whole module contract |

use std::collections::{BTreeMap, BTreeSet};

use num_bigint::BigInt;
use num_traits::{One, Signed, Zero};
use relational_geometry::Rat;
use serde::Serialize;
use thiserror::Error;

use crate::exact_value::{AlgebraicRoot, ExactInterval, ExactValueError};
use crate::EventId;
use crate::physical_constraint_complex::{
    ComponentMaterial, ConstraintComponentId, ConstraintError, ConstraintVertexId, ContactClass,
    ContactFamilyKind, CoordinateBox3, DistanceAperture, PairUncertainty,
    PhysicalConstraintComplex, ResidueMaterial,
};
use crate::physical_intake::mmcif::{AtomOccurrence, ChainOccurrence, DecimalToken, ResidueOccurrence};
use crate::physical_intake::{
    ComponentGrain, IntakeRefusal, PresentedFamily, found_constraint_complex,
};
use crate::physical_occurrence::{
    Coordinate, CoordinateName, CoordinateValue, Environment, ExteriorDeclaration, Occurrence,
    StatusRefusal,
};
use crate::quantity::{BaseUnits, Cast, CastApplication, Dimension, Quantity, QuantityError};

// ---------------------------------------------------------------------------------------------
// 1. Typed units, composed from `quantity.rs`
// ---------------------------------------------------------------------------------------------

/// The length unit this receiver declares: the angstrom.
pub const LENGTH_SYMBOL: &str = "angstrom";
/// The charge unit: the elementary charge.
pub const CHARGE_SYMBOL: &str = "elementary-charge";
/// The energy unit, named but never given a magnitude here: a caller supplies the
/// [`Cast`] that converts a `e² angstrom⁻¹` reading into it.
pub const ENERGY_SYMBOL: &str = "declared-energy";

/// **The base this receiver's readings are dimensioned over.**
///
/// [definition] `quantity.rs` names no unit anywhere on purpose — a caller declares its own base —
/// so this function is that declaration, made once and used by every reading below. Three
/// generators and no fourth: a length in angstroms, a charge in elementary charges, and an energy
/// whose magnitude enters only through a declared [`Cast`]. A count is the identity word and is
/// dimensionless.
pub fn physicochemical_base() -> BaseUnits {
    BaseUnits::declare([LENGTH_SYMBOL, CHARGE_SYMBOL, ENERGY_SYMBOL])
        .expect("three distinct non-empty symbols")
}

/// The dimension `angstrom`.
pub fn length_dimension() -> Dimension {
    physicochemical_base()
        .unit(LENGTH_SYMBOL)
        .expect("the declared base carries its own length generator")
}

/// The dimension `elementary-charge`.
pub fn charge_dimension() -> Dimension {
    physicochemical_base()
        .unit(CHARGE_SYMBOL)
        .expect("the declared base carries its own charge generator")
}

/// The dimension `declared-energy`.
pub fn energy_dimension() -> Dimension {
    physicochemical_base()
        .unit(ENERGY_SYMBOL)
        .expect("the declared base carries its own energy generator")
}

/// The identity word: a dimensionless count or ratio.
pub fn count_dimension() -> Dimension {
    physicochemical_base().dimensionless()
}

/// The dimension of a Coulomb sum at a dimensionless relative permittivity: `e² angstrom⁻¹`.
pub fn coulomb_dimension() -> Dimension {
    let base = physicochemical_base();
    base.dimension_of(&[
        (CHARGE_SYMBOL, Rat::from_integer(BigInt::from(2))),
        (LENGTH_SYMBOL, -Rat::one()),
    ])
    .expect("both generators belong to the declared base")
}

/// **An exact enclosure together with the dimension it is an enclosure of.**
///
/// [definition] `quantity::Quantity` is an exact *point* magnitude carrying a
/// `quantity::Dimension`. Every magnitude this receiver returns is an enclosure — `1/r` is
/// irrational, a coordinate is a box one last place wide — so the one composition this module
/// founds is the interval-valued quantity. It founds nothing else: the dimension algebra, the
/// refusal on unlike dimensions and the cast machinery are all `quantity.rs`'s.
///
/// Addition refuses two unlike dimensions by name ([`PhysicochemicalRefusal::UnlikeUnits`]); it
/// never coerces and never drops a unit.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct UnitedInterval {
    enclosure: ExactInterval,
    dimension: Dimension,
}

impl UnitedInterval {
    /// An enclosure of a declared dimension.
    pub const fn found(enclosure: ExactInterval, dimension: Dimension) -> Self {
        Self {
            enclosure,
            dimension,
        }
    }

    /// An exact point reading.
    pub fn point(value: Rat, dimension: Dimension) -> Self {
        Self::found(ExactInterval::point(value), dimension)
    }

    /// An exact dimensionless count.
    pub fn count(value: u64) -> Self {
        Self::point(Rat::from_integer(BigInt::from(value)), count_dimension())
    }

    /// The enclosure.
    pub const fn enclosure(&self) -> &ExactInterval {
        &self.enclosure
    }

    /// The dimension.
    pub const fn dimension(&self) -> &Dimension {
        &self.dimension
    }

    /// The lower endpoint as a [`Quantity`], so a consumer cannot take the magnitude alone.
    pub fn lower(&self) -> Quantity {
        Quantity::new(self.enclosure.lower.clone(), self.dimension.clone())
    }

    /// The upper endpoint as a [`Quantity`].
    pub fn upper(&self) -> Quantity {
        Quantity::new(self.enclosure.upper.clone(), self.dimension.clone())
    }

    /// The exact width of the enclosure, as a bare rational of the same dimension.
    pub fn width(&self) -> Rat {
        &self.enclosure.upper - &self.enclosure.lower
    }

    /// **Addition. Refuses two unlike dimensions by name.**
    pub fn sum(&self, other: &Self) -> Result<Self, PhysicochemicalRefusal> {
        if self.dimension != other.dimension {
            return Err(PhysicochemicalRefusal::UnlikeUnits {
                operation: "addition",
                left: self.dimension.render(),
                right: other.dimension.render(),
            });
        }
        Ok(Self {
            enclosure: ExactInterval {
                lower: &self.enclosure.lower + &other.enclosure.lower,
                upper: &self.enclosure.upper + &other.enclosure.upper,
            },
            dimension: self.dimension.clone(),
        })
    }

    /// Multiplication: the enclosures multiply as sets and the exponent words add.
    pub fn times(&self, other: &Self) -> Result<Self, PhysicochemicalRefusal> {
        Ok(Self {
            enclosure: self.enclosure.times(&other.enclosure)?,
            dimension: self.dimension.product(&other.dimension)?,
        })
    }

    /// Whether this enclosure contains a declared quantity of the same dimension. A quantity of a
    /// different dimension is not outside the enclosure; the question has no answer, and the
    /// refusal says so.
    pub fn contains(&self, value: &Quantity) -> Result<bool, PhysicochemicalRefusal> {
        let (magnitude, dimension) = value.parts();
        if *dimension != self.dimension {
            return Err(PhysicochemicalRefusal::UnlikeUnits {
                operation: "containment",
                left: self.dimension.render(),
                right: dimension.render(),
            });
        }
        Ok(self.enclosure.lower <= *magnitude && *magnitude <= self.enclosure.upper)
    }

    /// Whether this enclosure lies inside another of the same dimension.
    pub fn contained_in(&self, other: &Self) -> Result<bool, PhysicochemicalRefusal> {
        if self.dimension != other.dimension {
            return Err(PhysicochemicalRefusal::UnlikeUnits {
                operation: "containment",
                left: self.dimension.render(),
                right: other.dimension.render(),
            });
        }
        Ok(other.enclosure.lower <= self.enclosure.lower
            && self.enclosure.upper <= other.enclosure.upper)
    }

    /// A rendering for receipts. Testimony, never an identity.
    pub fn render(&self) -> String {
        format!(
            "[{}, {}] [{}]",
            relational_geometry::format_rat(&self.enclosure.lower),
            relational_geometry::format_rat(&self.enclosure.upper),
            self.dimension.render()
        )
    }
}

// ---------------------------------------------------------------------------------------------
// 2. Declared parameter tables, never defaults
// ---------------------------------------------------------------------------------------------

/// **The ground of an exterior parameter declaration: where it came from and what it covers.**
///
/// [definition] Both fields are required and both are refused empty. A table with no named source
/// is not a declaration, and a table with no stated scope is a claim about everything — which is
/// the shape a default takes when it is given a name. `Deserialize` is deliberately not derived:
/// it would be a second constructor bypassing the check.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize)]
pub struct TableGround {
    source: String,
    scope: String,
}

impl TableGround {
    /// Declare the ground. Refuses an unstated source or an unstated scope.
    pub fn declare(
        source: impl Into<String>,
        scope: impl Into<String>,
    ) -> Result<Self, PhysicochemicalRefusal> {
        let source = source.into();
        let scope = scope.into();
        if source.trim().is_empty() || scope.trim().is_empty() {
            return Err(PhysicochemicalRefusal::TableGroundNotStated);
        }
        Ok(Self { source, scope })
    }

    /// The named source table.
    pub fn source(&self) -> &str {
        &self.source
    }

    /// What the declaration covers, and what it does not.
    pub fn scope(&self) -> &str {
        &self.scope
    }
}

/// The residue classes this receiver reads a contact composition over.
///
/// [definition] The list is closed and the assignment of a residue to a class is **not** in this
/// enum: it is in a declared [`ResidueClassTable`], because the assignment is exactly the part
/// that differs between one published grouping and another.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize)]
pub enum ResidueClass {
    /// An apolar side chain.
    Hydrophobic,
    /// A neutral side chain carrying a hydrogen-bonding heteroatom.
    Polar,
    /// A side chain carrying a positive formal charge at the table's declared protonation.
    PositivelyCharged,
    /// A side chain carrying a negative formal charge at the table's declared protonation.
    NegativelyCharged,
    /// An aromatic side chain.
    Aromatic,
    /// Glycine, proline, cysteine in a disulphide, a modified residue, a ligand: named apart
    /// rather than pressed into one of the five above.
    Special,
}

impl ResidueClass {
    /// A short name for receipts.
    pub const fn label(self) -> &'static str {
        match self {
            Self::Hydrophobic => "hydrophobic",
            Self::Polar => "polar",
            Self::PositivelyCharged => "positively-charged",
            Self::NegativelyCharged => "negatively-charged",
            Self::Aromatic => "aromatic",
            Self::Special => "special",
        }
    }

    /// Whether this class is a claim about a protonation state.
    pub const fn is_charged(self) -> bool {
        matches!(self, Self::PositivelyCharged | Self::NegativelyCharged)
    }
}

/// An unordered pair of residue classes: the key a contact composition counts over.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize)]
pub struct ClassPair(ResidueClass, ResidueClass);

impl ClassPair {
    /// The canonical unordered pair. `of(a, b) == of(b, a)` by construction.
    pub fn of(left: ResidueClass, right: ResidueClass) -> Self {
        if left <= right {
            Self(left, right)
        } else {
            Self(right, left)
        }
    }

    /// The two classes, in canonical order.
    pub const fn classes(&self) -> (ResidueClass, ResidueClass) {
        (self.0, self.1)
    }

    /// Whether this pair is a salt-bridge *candidate*: one positive and one negative class. It is
    /// a candidate and not a salt bridge — the class pair says nothing about the side-chain atom
    /// geometry, and this receiver reads the addressed representative's separation only.
    pub const fn is_salt_bridge_candidate(&self) -> bool {
        matches!(
            (self.0, self.1),
            (
                ResidueClass::PositivelyCharged,
                ResidueClass::NegativelyCharged
            ) | (
                ResidueClass::NegativelyCharged,
                ResidueClass::PositivelyCharged
            )
        )
    }

    /// Whether this pair is a like-charge contact: two positive or two negative classes.
    pub const fn is_like_charge(&self) -> bool {
        matches!(
            (self.0, self.1),
            (
                ResidueClass::PositivelyCharged,
                ResidueClass::PositivelyCharged
            ) | (
                ResidueClass::NegativelyCharged,
                ResidueClass::NegativelyCharged
            )
        )
    }

    /// Whether either class is a claim about a protonation state.
    pub const fn mentions_charge(&self) -> bool {
        self.0.is_charged() || self.1.is_charged()
    }

    /// A rendering for receipts.
    pub fn render(&self) -> String {
        format!("{}--{}", self.0.label(), self.1.label())
    }
}

/// **A declared assignment of residue names to classes.**
///
/// [definition] The table carries its own name and its [`TableGround`], and both travel into every
/// reading taken with it. A residue the table does not name is a refusal by name
/// ([`PhysicochemicalRefusal::ResidueNotInTable`]) and never a silent `Special`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct ResidueClassTable {
    name: String,
    ground: TableGround,
    classes: BTreeMap<String, ResidueClass>,
}

impl ResidueClassTable {
    /// Declare a table. Refuses an unnamed table, an empty population and an empty residue key.
    pub fn declare(
        name: impl Into<String>,
        ground: TableGround,
        classes: impl IntoIterator<Item = (String, ResidueClass)>,
    ) -> Result<Self, PhysicochemicalRefusal> {
        let name = name.into();
        if name.trim().is_empty() {
            return Err(PhysicochemicalRefusal::TableNotNamed);
        }
        let classes: BTreeMap<String, ResidueClass> = classes.into_iter().collect();
        if classes.is_empty() {
            return Err(PhysicochemicalRefusal::TableIsEmpty { table: name });
        }
        if classes.keys().any(|residue| residue.trim().is_empty()) {
            return Err(PhysicochemicalRefusal::TableIsEmpty { table: name });
        }
        Ok(Self {
            name,
            ground,
            classes,
        })
    }

    /// The table's name.
    pub fn name(&self) -> &str {
        &self.name
    }

    /// Its ground.
    pub const fn ground(&self) -> &TableGround {
        &self.ground
    }

    /// Every named residue.
    pub const fn classes(&self) -> &BTreeMap<String, ResidueClass> {
        &self.classes
    }

    /// The class of one residue. A residue the table does not name is refused, never defaulted.
    pub fn class_of(&self, residue: &str) -> Result<ResidueClass, PhysicochemicalRefusal> {
        self.classes.get(residue).copied().ok_or_else(|| {
            PhysicochemicalRefusal::ResidueNotInTable {
                table: self.name.clone(),
                residue: residue.to_owned(),
            }
        })
    }

    /// The residues at which two tables assign different classes.
    pub fn divergence(&self, other: &Self) -> BTreeSet<String> {
        let mut divergent = BTreeSet::new();
        for residue in self.classes.keys().chain(other.classes.keys()) {
            if self.classes.get(residue) != other.classes.get(residue) {
                divergent.insert(residue.clone());
            }
        }
        divergent
    }
}

/// **A declared formal charge per residue, at a declared protonation state.**
///
/// The charge is an exact rational in elementary charges; the protonation state it holds at is an
/// `physical_occurrence::ExteriorDeclaration`, whose constructor already refuses an empty
/// statement or an unnamed apparatus.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct FormalChargeTable {
    name: String,
    ground: TableGround,
    protonation: ExteriorDeclaration,
    charges: BTreeMap<String, Rat>,
}

impl FormalChargeTable {
    /// Declare the table.
    pub fn declare(
        name: impl Into<String>,
        ground: TableGround,
        protonation: ExteriorDeclaration,
        charges: impl IntoIterator<Item = (String, Rat)>,
    ) -> Result<Self, PhysicochemicalRefusal> {
        let name = name.into();
        if name.trim().is_empty() {
            return Err(PhysicochemicalRefusal::TableNotNamed);
        }
        let charges: BTreeMap<String, Rat> = charges.into_iter().collect();
        if charges.is_empty() {
            return Err(PhysicochemicalRefusal::TableIsEmpty { table: name });
        }
        Ok(Self {
            name,
            ground,
            protonation,
            charges,
        })
    }

    /// The table's name.
    pub fn name(&self) -> &str {
        &self.name
    }

    /// Its ground.
    pub const fn ground(&self) -> &TableGround {
        &self.ground
    }

    /// The protonation state the charges hold at.
    pub const fn protonation(&self) -> &ExteriorDeclaration {
        &self.protonation
    }

    /// The formal charge of one residue in elementary charges, as a dimensioned quantity.
    pub fn charge_of(&self, residue: &str) -> Result<Quantity, PhysicochemicalRefusal> {
        let value = self.charges.get(residue).cloned().ok_or_else(|| {
            PhysicochemicalRefusal::ResidueNotInTable {
                table: self.name.clone(),
                residue: residue.to_owned(),
            }
        })?;
        Ok(Quantity::new(value, charge_dimension()))
    }

    /// Every named residue and its exact charge.
    pub const fn charges(&self) -> &BTreeMap<String, Rat> {
        &self.charges
    }
}

/// **The declared hydrogen-bond donor and acceptor heavy atoms, per residue.**
///
/// [definition] These are *heavy-atom* roles. A donor here is a nitrogen, oxygen or sulphur whose
/// attached hydrogen the model does not carry; an acceptor is a nitrogen, oxygen or sulphur with a
/// lone pair. The table names atoms, not bonds.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct HydrogenBondTable {
    name: String,
    ground: TableGround,
    donors: BTreeMap<String, BTreeSet<String>>,
    acceptors: BTreeMap<String, BTreeSet<String>>,
}

impl HydrogenBondTable {
    /// Declare the table.
    pub fn declare(
        name: impl Into<String>,
        ground: TableGround,
        donors: impl IntoIterator<Item = (String, BTreeSet<String>)>,
        acceptors: impl IntoIterator<Item = (String, BTreeSet<String>)>,
    ) -> Result<Self, PhysicochemicalRefusal> {
        let name = name.into();
        if name.trim().is_empty() {
            return Err(PhysicochemicalRefusal::TableNotNamed);
        }
        let donors: BTreeMap<String, BTreeSet<String>> = donors.into_iter().collect();
        let acceptors: BTreeMap<String, BTreeSet<String>> = acceptors.into_iter().collect();
        if donors.is_empty() && acceptors.is_empty() {
            return Err(PhysicochemicalRefusal::TableIsEmpty { table: name });
        }
        Ok(Self {
            name,
            ground,
            donors,
            acceptors,
        })
    }

    /// The table's name.
    pub fn name(&self) -> &str {
        &self.name
    }

    /// Its ground.
    pub const fn ground(&self) -> &TableGround {
        &self.ground
    }

    /// Whether the named atom of the named residue is a declared donor.
    pub fn is_donor(&self, residue: &str, atom: &str) -> bool {
        self.donors
            .get(residue)
            .is_some_and(|atoms| atoms.contains(atom))
    }

    /// Whether the named atom of the named residue is a declared acceptor.
    pub fn is_acceptor(&self, residue: &str, atom: &str) -> bool {
        self.acceptors
            .get(residue)
            .is_some_and(|atoms| atoms.contains(atom))
    }
}

/// **A declared van der Waals radius per element symbol, in angstroms.**
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct RadiusTable {
    name: String,
    ground: TableGround,
    radii: BTreeMap<String, Rat>,
}

impl RadiusTable {
    /// Declare the table. A non-positive radius is refused by name.
    pub fn declare(
        name: impl Into<String>,
        ground: TableGround,
        radii: impl IntoIterator<Item = (String, Rat)>,
    ) -> Result<Self, PhysicochemicalRefusal> {
        let name = name.into();
        if name.trim().is_empty() {
            return Err(PhysicochemicalRefusal::TableNotNamed);
        }
        let radii: BTreeMap<String, Rat> = radii.into_iter().collect();
        if radii.is_empty() {
            return Err(PhysicochemicalRefusal::TableIsEmpty { table: name });
        }
        for (element, radius) in &radii {
            if !radius.is_positive() {
                return Err(PhysicochemicalRefusal::RadiusNotPositive {
                    table: name,
                    element: element.clone(),
                });
            }
        }
        Ok(Self {
            name,
            ground,
            radii,
        })
    }

    /// The table's name.
    pub fn name(&self) -> &str {
        &self.name
    }

    /// Its ground.
    pub const fn ground(&self) -> &TableGround {
        &self.ground
    }

    /// The radius of one element, in angstroms, as a dimensioned quantity.
    pub fn radius_of(&self, element: &str) -> Result<Quantity, PhysicochemicalRefusal> {
        let value = self.radii.get(element).cloned().ok_or_else(|| {
            PhysicochemicalRefusal::ElementNotInTable {
                table: self.name.clone(),
                element: element.to_owned(),
            }
        })?;
        Ok(Quantity::new(value, length_dimension()))
    }

    /// The exact rational radius of one element in angstroms.
    pub fn raw_radius(&self, element: &str) -> Result<Rat, PhysicochemicalRefusal> {
        self.radii.get(element).cloned().ok_or_else(|| {
            PhysicochemicalRefusal::ElementNotInTable {
                table: self.name.clone(),
                element: element.to_owned(),
            }
        })
    }
}

/// **A declared uniform relative permittivity.**
///
/// [definition] This is the constitutive parameter of the electrostatic model and it is declared,
/// not chosen here. It is dimensionless — the relative permittivity — and non-positive values are
/// refused by name.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct Dielectric {
    relative: Rat,
    ground: TableGround,
}

impl Dielectric {
    /// Declare it. Refuses a non-positive value.
    pub fn declare(relative: Rat, ground: TableGround) -> Result<Self, PhysicochemicalRefusal> {
        if !relative.is_positive() {
            return Err(PhysicochemicalRefusal::DielectricNotPositive);
        }
        Ok(Self { relative, ground })
    }

    /// The exact relative permittivity.
    pub const fn relative(&self) -> &Rat {
        &self.relative
    }

    /// Its ground.
    pub const fn ground(&self) -> &TableGround {
        &self.ground
    }
}

/// **The complete declared parameter set one reading is taken under.**
///
/// [definition] Carried by value into every reading, exactly as `physical_intake::EnvironmentIndex`
/// is carried into an occurrence. Two readings taken under different [`ParameterTables`] are not
/// comparable without a supplied [`TablePassage`].
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct ParameterTables {
    name: String,
    residue_class: ResidueClassTable,
    formal_charge: FormalChargeTable,
    hydrogen_bond: HydrogenBondTable,
    radii: RadiusTable,
    dielectric: Dielectric,
}

impl ParameterTables {
    /// Declare the set.
    pub fn declare(
        name: impl Into<String>,
        residue_class: ResidueClassTable,
        formal_charge: FormalChargeTable,
        hydrogen_bond: HydrogenBondTable,
        radii: RadiusTable,
        dielectric: Dielectric,
    ) -> Result<Self, PhysicochemicalRefusal> {
        let name = name.into();
        if name.trim().is_empty() {
            return Err(PhysicochemicalRefusal::TableNotNamed);
        }
        Ok(Self {
            name,
            residue_class,
            formal_charge,
            hydrogen_bond,
            radii,
            dielectric,
        })
    }

    /// The set's name.
    pub fn name(&self) -> &str {
        &self.name
    }

    /// The residue-class table.
    pub const fn residue_class(&self) -> &ResidueClassTable {
        &self.residue_class
    }

    /// The formal-charge table.
    pub const fn formal_charge(&self) -> &FormalChargeTable {
        &self.formal_charge
    }

    /// The hydrogen-bond donor and acceptor table.
    pub const fn hydrogen_bond(&self) -> &HydrogenBondTable {
        &self.hydrogen_bond
    }

    /// The van der Waals radius table.
    pub const fn radii(&self) -> &RadiusTable {
        &self.radii
    }

    /// The declared dielectric.
    pub const fn dielectric(&self) -> &Dielectric {
        &self.dielectric
    }

    /// **The identity every reading carries, so a cross-table comparison is visible.**
    pub fn identity(&self) -> TableIdentity {
        TableIdentity {
            tables: self.name.clone(),
            residue_class: self.residue_class.name.clone(),
            formal_charge: self.formal_charge.name.clone(),
            protonation: self.formal_charge.protonation.statement().to_owned(),
            hydrogen_bond: self.hydrogen_bond.name.clone(),
            radii: self.radii.name.clone(),
            dielectric: relational_geometry::format_rat(&self.dielectric.relative),
        }
    }
}

/// The identity of a declared parameter set, carried by every reading.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize)]
pub struct TableIdentity {
    /// The parameter set's name.
    pub tables: String,
    /// The residue-class table's name.
    pub residue_class: String,
    /// The formal-charge table's name.
    pub formal_charge: String,
    /// The protonation statement the charges hold at.
    pub protonation: String,
    /// The hydrogen-bond table's name.
    pub hydrogen_bond: String,
    /// The radius table's name.
    pub radii: String,
    /// The declared relative permittivity, rendered.
    pub dielectric: String,
}

/// **A declared passage between two parameter sets.**
///
/// [definition] The same shape and the same law as `physical_occurrence::EnvironmentPassage`:
/// a stated ground, and every residue the two residue-class tables disagree at must be accounted
/// for by name. A passage that omits one is refused. Without a passage, [`compare_across_tables`]
/// refuses two readings taken under different sets — a composition under one grouping is not a
/// composition under another, and equal totals do not make them one reading.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct TablePassage {
    ground: String,
    from: TableIdentity,
    to: TableIdentity,
    accounted: BTreeSet<String>,
}

impl TablePassage {
    /// Declare the passage. Refuses an unstated ground and any divergent residue the declaration
    /// does not account for, naming it.
    pub fn declare(
        ground: impl Into<String>,
        from: &ParameterTables,
        to: &ParameterTables,
        accounted: impl IntoIterator<Item = String>,
    ) -> Result<Self, PhysicochemicalRefusal> {
        let ground = ground.into();
        if ground.trim().is_empty() {
            return Err(PhysicochemicalRefusal::PassageGroundNotStated);
        }
        let accounted: BTreeSet<String> = accounted.into_iter().collect();
        let divergence = from.residue_class.divergence(&to.residue_class);
        let unaccounted = divergence
            .into_iter()
            .filter(|residue| !accounted.contains(residue))
            .collect::<Vec<_>>();
        if !unaccounted.is_empty() {
            return Err(PhysicochemicalRefusal::ResiduesUnaccounted { unaccounted });
        }
        Ok(Self {
            ground,
            from: from.identity(),
            to: to.identity(),
            accounted,
        })
    }

    /// The stated ground.
    pub fn ground(&self) -> &str {
        &self.ground
    }

    /// The set the passage leaves.
    pub const fn from(&self) -> &TableIdentity {
        &self.from
    }

    /// The set it arrives at.
    pub const fn to(&self) -> &TableIdentity {
        &self.to
    }

    /// The residues it accounts for.
    pub const fn accounted(&self) -> &BTreeSet<String> {
        &self.accounted
    }
}

// ---------------------------------------------------------------------------------------------
// The named declarations this owner ships
// ---------------------------------------------------------------------------------------------

fn residue_class_entries(histidine: ResidueClass) -> Vec<(String, ResidueClass)> {
    use ResidueClass::{
        Aromatic, Hydrophobic, NegativelyCharged, Polar, PositivelyCharged, Special,
    };
    [
        ("ALA", Hydrophobic),
        ("VAL", Hydrophobic),
        ("LEU", Hydrophobic),
        ("ILE", Hydrophobic),
        ("MET", Hydrophobic),
        ("PHE", Aromatic),
        ("TRP", Aromatic),
        ("TYR", Aromatic),
        ("SER", Polar),
        ("THR", Polar),
        ("ASN", Polar),
        ("GLN", Polar),
        ("ASP", NegativelyCharged),
        ("GLU", NegativelyCharged),
        ("LYS", PositivelyCharged),
        ("ARG", PositivelyCharged),
        ("GLY", Special),
        ("PRO", Special),
        ("CYS", Special),
    ]
    .into_iter()
    .map(|(residue, class)| (residue.to_owned(), class))
    .chain(std::iter::once(("HIS".to_owned(), histidine)))
    .collect()
}

/// **Named declaration A: histidine filed polar.**
///
/// [definition] The nineteen standard residues beside histidine are grouped by side-chain
/// character as the interface literature commonly does, and histidine is filed **polar**, which is
/// the grouping appropriate above its side-chain acidity. Glycine, proline and cysteine are
/// `Special` rather than pressed into one of the five: glycine has no side chain, proline's is
/// fused to its own backbone nitrogen, and cysteine's role depends on whether it is in a
/// disulphide, which a static heavy-atom model does not record.
pub fn residue_classes_histidine_polar() -> ResidueClassTable {
    let ground = TableGround::declare(
        "the twenty standard amino-acid residue templates of the chemical component dictionary, \
         grouped by side-chain character as the protein-interface literature commonly does",
        "the twenty standard residues only. A modified residue, a nucleotide, a ligand and a metal \
         are not named by this table and are refused by name rather than filed Special. Histidine \
         is filed polar, which is the grouping appropriate where its side chain is not protonated",
    )
    .expect("a stated source and scope");
    ResidueClassTable::declare(
        "standard-twenty/histidine-polar",
        ground,
        residue_class_entries(ResidueClass::Polar),
    )
    .expect("a named non-empty table")
}

/// **Named declaration B: histidine filed positively charged.**
///
/// [definition] The same nineteen assignments with histidine filed **positively charged**, which
/// is the grouping appropriate below its side-chain acidity. A reading taken under A and one taken
/// under B differ wherever a histidine takes part, and they are not comparable without a
/// [`TablePassage`] accounting for `HIS`. That is the point of shipping two: the histidine
/// assignment is a pH claim, and this owner makes the pH claim visible instead of choosing.
pub fn residue_classes_histidine_positive() -> ResidueClassTable {
    let ground = TableGround::declare(
        "the same twenty standard residue templates with histidine filed as positively charged, \
         which is the grouping appropriate below its side-chain acidity",
        "the twenty standard residues only, and only under a declared protonation in which the \
         histidine imidazole carries a proton",
    )
    .expect("a stated source and scope");
    ResidueClassTable::declare(
        "standard-twenty/histidine-positive",
        ground,
        residue_class_entries(ResidueClass::PositivelyCharged),
    )
    .expect("a named non-empty table")
}

fn integer(value: i64) -> Rat {
    Rat::from_integer(BigInt::from(value))
}

fn hundredths(value: i64) -> Rat {
    Rat::new(BigInt::from(value), BigInt::from(100))
}

fn charge_entries(histidine: i64) -> Vec<(String, Rat)> {
    [
        ("ALA", 0),
        ("VAL", 0),
        ("LEU", 0),
        ("ILE", 0),
        ("MET", 0),
        ("PHE", 0),
        ("TRP", 0),
        ("TYR", 0),
        ("SER", 0),
        ("THR", 0),
        ("ASN", 0),
        ("GLN", 0),
        ("ASP", -1),
        ("GLU", -1),
        ("LYS", 1),
        ("ARG", 1),
        ("GLY", 0),
        ("PRO", 0),
        ("CYS", 0),
    ]
    .into_iter()
    .map(|(residue, charge)| (residue.to_owned(), integer(charge)))
    .chain(std::iter::once((
        "HIS".to_owned(),
        integer(histidine),
    )))
    .collect()
}

/// **Named declaration: integral formal charges at a declared neutral protonation.**
///
/// Aspartate and glutamate carry `−1`, lysine and arginine `+1`, histidine `0`, every other
/// standard residue `0`. Termini are not charged by this table, because a terminus is a property
/// of the presented chain and not of the residue; the table says so in its scope.
pub fn formal_charges_neutral_protonation() -> FormalChargeTable {
    let ground = TableGround::declare(
        "integral side-chain formal charges of the twenty standard residues at a protonation state \
         in which aspartate and glutamate are deprotonated, lysine and arginine are protonated and \
         histidine is neutral",
        "side chains only. Chain termini carry no charge in this table, because a terminus is a \
         property of the presented chain rather than of the residue; a caller that wants them must \
         declare a table that names them",
    )
    .expect("a stated source and scope");
    let protonation = ExteriorDeclaration::declare(
        "every aspartate and glutamate side chain is deprotonated, every lysine and arginine side \
         chain is protonated, and every histidine side chain is neutral",
        "a declared protonation state, not a measurement: no titration was performed and no pKa \
         was computed",
    )
    .expect("a stated declaration");
    FormalChargeTable::declare(
        "integral-side-chain/neutral-histidine",
        ground,
        protonation,
        charge_entries(0),
    )
    .expect("a named non-empty table")
}

/// **Named declaration: the same integral charges with histidine protonated.**
pub fn formal_charges_protonated_histidine() -> FormalChargeTable {
    let ground = TableGround::declare(
        "the same integral side-chain formal charges with the histidine imidazole protonated",
        "side chains only, and only under a declared protonation below the histidine side-chain \
         acidity",
    )
    .expect("a stated source and scope");
    let protonation = ExteriorDeclaration::declare(
        "every aspartate and glutamate side chain is deprotonated, every lysine, arginine and \
         histidine side chain is protonated",
        "a declared protonation state, not a measurement",
    )
    .expect("a stated declaration");
    FormalChargeTable::declare(
        "integral-side-chain/protonated-histidine",
        ground,
        protonation,
        charge_entries(1),
    )
    .expect("a named non-empty table")
}

fn atom_set(atoms: &[&str]) -> BTreeSet<String> {
    atoms.iter().map(|atom| (*atom).to_owned()).collect()
}

/// **Named declaration: heavy-atom hydrogen-bond donors and acceptors of the standard residues.**
///
/// [definition] Backbone `N` is a donor and backbone `O` an acceptor in every residue but proline,
/// whose backbone nitrogen carries no hydrogen. The side-chain roles are the usual ones. The table
/// names **atoms**; the geometry of an actual bond needs the hydrogen, which the model does not
/// carry, which is why the reading built on this table is a *candidate* reading.
pub fn heavy_atom_hydrogen_bond_roles() -> HydrogenBondTable {
    let ground = TableGround::declare(
        "the backbone amide nitrogen and carbonyl oxygen of every standard residue, with proline's \
         backbone nitrogen excluded as a donor because it carries no hydrogen, together with the \
         usual side-chain donor and acceptor heavy atoms",
        "heavy atoms only. No hydrogen position is declared, so this table supports a candidate \
         reading and no bond claim; a residue the table does not name contributes no donor and no \
         acceptor",
    )
    .expect("a stated source and scope");
    let backbone_donor = ["N"];
    let backbone_acceptor = ["O", "OXT"];
    let side_donors: [(&str, &[&str]); 9] = [
        ("SER", &["OG"]),
        ("THR", &["OG1"]),
        ("TYR", &["OH"]),
        ("ASN", &["ND2"]),
        ("GLN", &["NE2"]),
        ("LYS", &["NZ"]),
        ("ARG", &["NE", "NH1", "NH2"]),
        ("TRP", &["NE1"]),
        ("HIS", &["ND1", "NE2"]),
    ];
    let side_acceptors: [(&str, &[&str]); 8] = [
        ("SER", &["OG"]),
        ("THR", &["OG1"]),
        ("TYR", &["OH"]),
        ("ASN", &["OD1"]),
        ("GLN", &["OE1"]),
        ("ASP", &["OD1", "OD2"]),
        ("GLU", &["OE1", "OE2"]),
        ("HIS", &["ND1", "NE2"]),
    ];
    let residues = [
        "ALA", "ARG", "ASN", "ASP", "CYS", "GLN", "GLU", "GLY", "HIS", "ILE", "LEU", "LYS", "MET",
        "PHE", "PRO", "SER", "THR", "TRP", "TYR", "VAL",
    ];
    let mut donors = BTreeMap::new();
    let mut acceptors = BTreeMap::new();
    for residue in residues {
        let mut donor_atoms = if residue == "PRO" {
            BTreeSet::new()
        } else {
            atom_set(&backbone_donor)
        };
        if let Some((_, atoms)) = side_donors.iter().find(|(name, _)| *name == residue) {
            donor_atoms.extend(atom_set(atoms));
        }
        let mut acceptor_atoms = atom_set(&backbone_acceptor);
        if let Some((_, atoms)) = side_acceptors.iter().find(|(name, _)| *name == residue) {
            acceptor_atoms.extend(atom_set(atoms));
        }
        donors.insert(residue.to_owned(), donor_atoms);
        acceptors.insert(residue.to_owned(), acceptor_atoms);
    }
    HydrogenBondTable::declare(
        "standard-twenty/heavy-atom-roles",
        ground,
        donors,
        acceptors,
    )
    .expect("a named non-empty table")
}

/// **Named declaration: van der Waals radii in angstroms, as exact hundredths.**
///
/// The five element symbols a protein heavy-atom model presents, each an exact rational: carbon
/// `170/100`, nitrogen `155/100`, oxygen `152/100`, sulphur `180/100`, zinc `139/100`. An element
/// the table does not name is refused by name, never given a default radius.
pub fn van_der_waals_radii() -> RadiusTable {
    let ground = TableGround::declare(
        "the tabulated van der Waals radii of carbon, nitrogen, oxygen, sulphur and zinc, taken to \
         two decimal places and retained as exact hundredths of an angstrom",
        "those five elements only. The two-decimal truncation is part of the declaration; an \
         element the table does not name is refused rather than given a default radius",
    )
    .expect("a stated source and scope");
    RadiusTable::declare(
        "heavy-atom/hundredths-of-an-angstrom",
        ground,
        [
            ("C".to_owned(), hundredths(170)),
            ("N".to_owned(), hundredths(155)),
            ("O".to_owned(), hundredths(152)),
            ("S".to_owned(), hundredths(180)),
            ("ZN".to_owned(), hundredths(139)),
        ],
    )
    .expect("a named non-empty table")
}

/// **Named declaration: a uniform relative permittivity of four.**
///
/// [definition] The protein interior is commonly modelled with a uniform relative permittivity
/// between two and twenty; four is one declaration inside that range and is stated as such. It is
/// a constitutive parameter of the model and not a measured property of these structures.
pub fn uniform_dielectric_four() -> Dielectric {
    let ground = TableGround::declare(
        "a uniform relative permittivity of 4, one common declaration for a protein interior",
        "a constitutive parameter of the declared electrostatic model. It is not a measurement of \
         these structures, it does not vary with position, and it carries no solvent, no ionic \
         strength and no polarization",
    )
    .expect("a stated source and scope");
    Dielectric::declare(integer(4), ground).expect("a positive permittivity")
}

/// **The parameter set with histidine polar and neutral.**
pub fn tables_histidine_neutral() -> ParameterTables {
    ParameterTables::declare(
        "histidine-neutral",
        residue_classes_histidine_polar(),
        formal_charges_neutral_protonation(),
        heavy_atom_hydrogen_bond_roles(),
        van_der_waals_radii(),
        uniform_dielectric_four(),
    )
    .expect("a named parameter set")
}

/// **The parameter set with histidine positively charged and protonated.**
pub fn tables_histidine_protonated() -> ParameterTables {
    ParameterTables::declare(
        "histidine-protonated",
        residue_classes_histidine_positive(),
        formal_charges_protonated_histidine(),
        heavy_atom_hydrogen_bond_roles(),
        van_der_waals_radii(),
        uniform_dielectric_four(),
    )
    .expect("a named parameter set")
}

/// **A named declaration of the Coulomb constant as a [`Cast`] into the declared energy unit.**
///
/// [definition] `quantity::Cast::declare` refuses a dimensionless cast by name, which is exactly
/// the rule that keeps this from being an erasure: the cast's dimension is
/// `declared-energy · angstrom · elementary-charge⁻²`, so applying it to an `e² angstrom⁻¹`
/// reading returns a `declared-energy` reading and the chart change appears in the return.
///
/// The magnitude is the conventional `332.0637 kcal·Å·mol⁻¹·e⁻²` truncated to four decimal places
/// and retained as the exact rational `3320637/10000`. **The truncation is declared, not hidden**,
/// and the declared energy unit is therefore kilocalories per mole for a caller that uses this
/// cast.
pub fn declared_coulomb_cast() -> Result<Cast, PhysicochemicalRefusal> {
    let base = physicochemical_base();
    let dimension = base
        .dimension_of(&[
            (ENERGY_SYMBOL, Rat::one()),
            (LENGTH_SYMBOL, Rat::one()),
            (CHARGE_SYMBOL, -Rat::from_integer(BigInt::from(2))),
        ])
        .map_err(PhysicochemicalRefusal::Quantity)?;
    let magnitude = Rat::new(BigInt::from(3_320_637_i64), BigInt::from(10_000_i64));
    Cast::declare(
        "coulomb-constant/kcal-per-mole-angstrom-per-square-elementary-charge",
        Quantity::new(magnitude, dimension),
    )
    .map_err(PhysicochemicalRefusal::Quantity)
}

// ---------------------------------------------------------------------------------------------
// The pH gate
// ---------------------------------------------------------------------------------------------

/// **On what ground a charged reading is taken.**
///
/// [definition] There are exactly two lawful grounds and no third. Either the occurrence's
/// environment declares its acidity axis, or a caller declares the protonation assumption
/// explicitly and its ground travels with the reading. There is no path to a charged reading
/// without one of the two.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub enum ProtonationBasis {
    /// The occurrence's own environment declares the acidity axis. The payload has no literal:
    /// [`DeclaredAcidity`]'s only constructor is private to this module and is reached only from
    /// [`protonation_basis`], so this arm cannot be written by a caller who did not read an
    /// environment that declared the axis.
    FromEnvironment(DeclaredAcidity),
    /// The environment leaves the axis undeclared and a caller supplies the assumption. Its
    /// payload is `physical_occurrence::ExteriorDeclaration`, whose fields are likewise private
    /// and whose `declare` refuses an empty statement or an unnamed apparatus.
    DeclaredAssumption(ExteriorDeclaration),
}

mod acidity {
    use super::ExactInterval;
    use serde::Serialize;

    /// **What an environment that declared its acidity axis says, read off that environment.**
    ///
    /// [definition] Its fields are private to this module and its only constructor is
    /// `pub(super)`, so no struct literal of this type can be written anywhere — and therefore
    /// [`super::ProtonationBasis::FromEnvironment`] cannot be written as a literal either. The only
    /// way to obtain one is to call [`super::protonation_basis`] on an environment that really
    /// declares the axis. This is the shape `receiver_atlas::Recomputed` already uses to make a
    /// `Satisfied` row unwritable.
    #[derive(Clone, Debug, PartialEq, Eq, Serialize)]
    pub struct DeclaredAcidity {
        p_h: ExactInterval,
        assumption: String,
        ground: String,
    }

    impl DeclaredAcidity {
        /// Record what an environment's declared acidity coordinate says. Reachable only from this
        /// module's own reader.
        pub(super) fn read(p_h: ExactInterval, assumption: String, ground: String) -> Self {
            Self {
                p_h,
                assumption,
                ground,
            }
        }

        /// The declared pH enclosure.
        pub const fn p_h(&self) -> &ExactInterval {
            &self.p_h
        }

        /// The protonation assumption the environment carries.
        pub fn assumption(&self) -> &str {
            &self.assumption
        }

        /// The ground the environment declared the axis on.
        pub fn ground(&self) -> &str {
            &self.ground
        }
    }
}

pub use acidity::DeclaredAcidity;

impl ProtonationBasis {
    /// A rendering for receipts.
    pub fn render(&self) -> String {
        match self {
            Self::FromEnvironment(acidity) => format!(
                "the occurrence's own declared acidity: pH in [{}, {}] under the assumption {:?}, \
                 declared on the ground {:?}",
                relational_geometry::format_rat(&acidity.p_h().lower),
                relational_geometry::format_rat(&acidity.p_h().upper),
                acidity.assumption(),
                acidity.ground()
            ),
            Self::DeclaredAssumption(declaration) => format!(
                "an exterior declaration, because the occurrence's environment leaves the acidity \
                 axis undeclared: {:?}, declared by {:?}",
                declaration.statement(),
                declaration.apparatus()
            ),
        }
    }
}

/// **Read the protonation basis off an occurrence's environment, or refuse naming the axis.**
///
/// [definition] This is the pH gate. `physical_occurrence::Environment` carries every axis as
/// either declared-with-a-ground or explicitly-undeclared-with-a-reason, so the refusal can carry
/// the environment's own stated reason rather than a generic message. On the M5 release the
/// acidity axis is undeclared — "no pH and no protonation assumption is recorded anywhere in this
/// release" — so this refusal is the truthful primary result there, and a charged reading is
/// obtained only through [`ProtonationBasis::DeclaredAssumption`].
pub fn protonation_basis(
    environment: &Environment,
) -> Result<ProtonationBasis, PhysicochemicalRefusal> {
    let coordinate = environment
        .coordinate(CoordinateName::Acidity)
        .map_err(StatusRefusal::Environment)?;
    match coordinate {
        Coordinate::Declared { value, ground } => match value {
            CoordinateValue::Acidity(acidity) => Ok(ProtonationBasis::FromEnvironment(
                DeclaredAcidity::read(
                    acidity.p_h.clone(),
                    acidity.protonation_assumption.clone(),
                    ground.clone(),
                ),
            )),
            other => Err(PhysicochemicalRefusal::AcidityMisfiled {
                found: format!("{other:?}"),
            }),
        },
        Coordinate::Undeclared { why } => Err(PhysicochemicalRefusal::AcidityUndeclared {
            axis: CoordinateName::Acidity,
            why: why.clone(),
            lineage: environment.lineage.clone(),
        }),
    }
}

/// A charged reading taken under an explicitly declared assumption, for an occurrence whose
/// environment leaves the acidity axis undeclared.
pub fn declared_protonation(declaration: ExteriorDeclaration) -> ProtonationBasis {
    ProtonationBasis::DeclaredAssumption(declaration)
}

// ---------------------------------------------------------------------------------------------
// 3. The site table
// ---------------------------------------------------------------------------------------------

/// **One addressed site's chemistry, as the presentation declares it.**
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct ChemicalSite {
    /// The occurrence this site is.
    pub vertex: ConstraintVertexId,
    /// Which presented component it belongs to.
    pub component: ConstraintComponentId,
    /// Its residue's one-based ordinal within that component's chain.
    pub residue_ordinal: u32,
    /// The residue's three-letter monomer name.
    pub residue: String,
    /// The atom label. At atom grain it is the presented atom; at representative grain it is the
    /// **declared representative's** label, because that selection is a choice of atom and
    /// `grain_tower::GrainSelection` already proves a selection is not a restriction. `None` only
    /// where a caller builds a site by hand; [`SiteTable::found`] always supplies one.
    pub atom: Option<String>,
    /// The element symbol the presentation carried, upper-cased. `None` where the presentation
    /// carried no `type_symbol` column.
    pub element: Option<String>,
}

/// **The chemistry of every addressed site of one presentation.**
///
/// [definition] Built from the presented chains and cross-checked against the complex the
/// constraint owner founded: the site population must have the same extent per component and the
/// same residue name at every vertex, or the founding is refused by name. That check is what makes
/// this a composition of `physical_intake::component_material`'s ordering law rather than a second
/// copy of it: if the two ever part, the receiver refuses instead of reading the wrong chemistry
/// onto the right geometry.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct SiteTable {
    /// The schema this table serializes under.
    pub schema: String,
    /// Exterior lineage, retained as testimony.
    pub lineage: String,
    /// The declared grain the sites were read at.
    pub grain: String,
    sites: BTreeMap<ConstraintVertexId, ChemicalSite>,
}

impl SiteTable {
    /// Found the table from the presented chains, in the order the complex founded its components.
    pub fn found(
        lineage: impl Into<String>,
        complex: &PhysicalConstraintComplex,
        chains: &[&ChainOccurrence],
        grain: &ComponentGrain,
    ) -> Result<Self, PhysicochemicalRefusal> {
        let lineage = lineage.into();
        if chains.len() != complex.components.len() {
            return Err(PhysicochemicalRefusal::ComponentPopulationDisagrees {
                presented: chains.len(),
                founded: complex.components.len(),
            });
        }
        let mut sites = BTreeMap::new();
        for (at, chain) in chains.iter().enumerate() {
            let component = ConstraintComponentId(at as u64 + 1);
            let vertices = complex.component(component)?.vertices.clone();
            let mut produced: Vec<(u32, String, Option<String>, Option<String>)> = Vec::new();
            for (residue_at, residue) in chain.residues.iter().enumerate() {
                let residue_ordinal = residue_at as u32 + 1;
                match grain {
                    ComponentGrain::Atom => {
                        for atom in &residue.atoms {
                            produced.push((
                                residue_ordinal,
                                residue.monomer.clone(),
                                Some(atom.label.clone()),
                                atom.element.as_ref().map(|symbol| symbol.to_uppercase()),
                            ));
                        }
                    }
                    ComponentGrain::Representative { atom_label } => {
                        let Some(at) = residue
                            .labelled_atom(atom_label)
                            .map_err(|_| PhysicochemicalRefusal::RepresentativeNotUnique {
                                residue: residue.source_ordinal,
                                label: atom_label.clone(),
                            })?
                        else {
                            return Err(PhysicochemicalRefusal::RepresentativeAbsent {
                                residue: residue.source_ordinal,
                                label: atom_label.clone(),
                            });
                        };
                        produced.push((
                            residue_ordinal,
                            residue.monomer.clone(),
                            Some(atom_label.clone()),
                            residue.atoms[at]
                                .element
                                .as_ref()
                                .map(|symbol| symbol.to_uppercase()),
                        ));
                    }
                }
            }
            if produced.len() != vertices.len() {
                return Err(PhysicochemicalRefusal::SitePopulationDisagrees {
                    component,
                    presented: produced.len(),
                    founded: vertices.len(),
                });
            }
            for (vertex, (residue_ordinal, residue, atom, element)) in
                vertices.iter().zip(produced)
            {
                let founded = &complex.vertices[vertex];
                let expected = match (&atom, grain) {
                    (Some(label), ComponentGrain::Atom) => format!("{residue}:{label}"),
                    _ => residue.clone(),
                };
                if founded.monomer != expected {
                    return Err(PhysicochemicalRefusal::SiteChemistryDisagrees {
                        vertex: *vertex,
                        founded: founded.monomer.clone(),
                        presented: expected,
                    });
                }
                sites.insert(
                    *vertex,
                    ChemicalSite {
                        vertex: *vertex,
                        component,
                        residue_ordinal,
                        residue,
                        atom: match grain {
                            ComponentGrain::Atom => atom,
                            ComponentGrain::Representative { .. } => atom,
                        },
                        element,
                    },
                );
            }
        }
        Ok(Self {
            schema: SITE_TABLE_SCHEMA.to_owned(),
            lineage,
            grain: grain.name(),
            sites,
        })
    }

    /// One site. A vertex the table does not carry is refused by name.
    pub fn site(&self, vertex: ConstraintVertexId) -> Result<&ChemicalSite, PhysicochemicalRefusal> {
        self.sites
            .get(&vertex)
            .ok_or(PhysicochemicalRefusal::SiteAbsent { vertex })
    }

    /// Every site, in address order.
    pub const fn sites(&self) -> &BTreeMap<ConstraintVertexId, ChemicalSite> {
        &self.sites
    }

    /// How many sites the table carries.
    pub fn extent(&self) -> usize {
        self.sites.len()
    }

    /// The sites of one component, in address order.
    pub fn of_component(&self, component: ConstraintComponentId) -> Vec<ConstraintVertexId> {
        self.sites
            .values()
            .filter(|site| site.component == component)
            .map(|site| site.vertex)
            .collect()
    }
}

// ---------------------------------------------------------------------------------------------
// Declared pair populations and their bounds
// ---------------------------------------------------------------------------------------------

/// **A declared ceiling on the pair population a reading may enumerate.**
///
/// [definition] Every entry point below takes one. The population is a product of caller-declared
/// extents — `n(n−1)/2` over a declared site set, `|S|·n` for a site set against a presentation —
/// so the count is taken with checked arithmetic and compared against the ceiling **before** any
/// vector is sized or any loop is entered.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct PairWorkBound {
    ceiling: u64,
    ground: String,
}

impl PairWorkBound {
    /// Declare the ceiling. Refuses a zero ceiling and an unstated ground.
    pub fn declare(
        ceiling: u64,
        ground: impl Into<String>,
    ) -> Result<Self, PhysicochemicalRefusal> {
        let ground = ground.into();
        if ceiling == 0 || ground.trim().is_empty() {
            return Err(PhysicochemicalRefusal::WorkBoundNotStated);
        }
        Ok(Self { ceiling, ground })
    }

    /// The ceiling.
    pub const fn ceiling(&self) -> u64 {
        self.ceiling
    }

    /// Its ground.
    pub fn ground(&self) -> &str {
        &self.ground
    }

    /// Admit a declared population, or refuse naming both counts.
    pub fn admit(&self, pairs: u64, population: &str) -> Result<(), PhysicochemicalRefusal> {
        if pairs > self.ceiling {
            return Err(PhysicochemicalRefusal::PairPopulationTooWide {
                population: population.to_owned(),
                pairs,
                ceiling: self.ceiling,
                ground: self.ground.clone(),
            });
        }
        Ok(())
    }
}

/// **Which pairs a distance reading runs over. Declared, with no default.**
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub enum PairPopulation {
    /// Every unordered pair among a declared site set, excluding pairs of one component whose
    /// residue ordinals differ by less than `minimum_residue_separation`.
    ///
    /// A declared separation of `0` admits two atoms of the same residue, which for a steric
    /// reading means every covalent bond is read as an overlap. That consequence is the caller's
    /// declaration and this owner states it rather than choosing a separation.
    AmongSites {
        /// The declared site set.
        sites: BTreeSet<ConstraintVertexId>,
        /// The declared intra-component residue separation exclusion.
        minimum_residue_separation: u32,
    },
    /// Every pair of a declared site set against every site of the presentation, under the same
    /// exclusion.
    SitesAgainstPresentation {
        /// The declared site set.
        sites: BTreeSet<ConstraintVertexId>,
        /// The declared intra-component residue separation exclusion.
        minimum_residue_separation: u32,
    },
}

impl PairPopulation {
    /// A short name for receipts and refusals.
    pub fn label(&self) -> String {
        match self {
            Self::AmongSites {
                sites,
                minimum_residue_separation,
            } => format!(
                "every pair among {} declared sites at residue separation at least \
                 {minimum_residue_separation}",
                sites.len()
            ),
            Self::SitesAgainstPresentation {
                sites,
                minimum_residue_separation,
            } => format!(
                "{} declared sites against the whole presentation at residue separation at least \
                 {minimum_residue_separation}",
                sites.len()
            ),
        }
    }

    /// The declared population's exact extent, before anything is sized by it.
    fn extent(&self, table: &SiteTable) -> Result<u64, PhysicochemicalRefusal> {
        let overflow = || PhysicochemicalRefusal::PairCountOverflows;
        match self {
            Self::AmongSites { sites, .. } => {
                let n = sites.len() as u64;
                n.checked_mul(n.saturating_sub(1))
                    .map(|product| product / 2)
                    .ok_or_else(overflow)
            }
            Self::SitesAgainstPresentation { sites, .. } => (sites.len() as u64)
                .checked_mul(table.extent() as u64)
                .ok_or_else(overflow),
        }
    }

    /// The declared exclusion.
    const fn separation(&self) -> u32 {
        match self {
            Self::AmongSites {
                minimum_residue_separation,
                ..
            }
            | Self::SitesAgainstPresentation {
                minimum_residue_separation,
                ..
            } => *minimum_residue_separation,
        }
    }

    /// The pairs themselves, after the bound has admitted the extent.
    fn pairs(
        &self,
        table: &SiteTable,
        bound: &PairWorkBound,
    ) -> Result<Vec<(ConstraintVertexId, ConstraintVertexId)>, PhysicochemicalRefusal> {
        let extent = self.extent(table)?;
        bound.admit(extent, &self.label())?;
        let separation = self.separation();
        let admits = |left: ConstraintVertexId,
                      right: ConstraintVertexId|
         -> Result<bool, PhysicochemicalRefusal> {
            if left == right {
                return Ok(false);
            }
            let a = table.site(left)?;
            let b = table.site(right)?;
            if a.component != b.component {
                return Ok(true);
            }
            let gap = a.residue_ordinal.abs_diff(b.residue_ordinal);
            Ok(gap >= separation)
        };
        let mut pairs = Vec::new();
        match self {
            Self::AmongSites { sites, .. } => {
                let ordered = sites.iter().copied().collect::<Vec<_>>();
                for (at, left) in ordered.iter().enumerate() {
                    for right in &ordered[at + 1..] {
                        if admits(*left, *right)? {
                            pairs.push((*left, *right));
                        }
                    }
                }
            }
            Self::SitesAgainstPresentation { sites, .. } => {
                let mut seen = BTreeSet::new();
                for left in sites {
                    for right in table.sites.keys() {
                        let key = if left <= right {
                            (*left, *right)
                        } else {
                            (*right, *left)
                        };
                        if !seen.insert(key) {
                            continue;
                        }
                        if admits(key.0, key.1)? {
                            pairs.push(key);
                        }
                    }
                }
            }
        }
        Ok(pairs)
    }
}

// ---------------------------------------------------------------------------------------------
// 3a. Contact composition over a founded family
// ---------------------------------------------------------------------------------------------

/// Which family a composition was read over: the interface, or the fold.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize)]
pub enum FamilyRole {
    /// A cross family of two distinct components: the interface.
    Interface,
    /// A within-component family at a declared sequence separation: the fold.
    Fold {
        /// The declared sequence separation the family was founded at.
        minimum_separation: u32,
    },
}

impl FamilyRole {
    fn of(kind: ContactFamilyKind) -> Self {
        match kind {
            ContactFamilyKind::Cross => Self::Interface,
            ContactFamilyKind::WithinComponent { minimum_separation } => Self::Fold {
                minimum_separation,
            },
        }
    }

    /// A short name for receipts.
    pub fn label(self) -> String {
        match self {
            Self::Interface => "interface (cross-component)".to_owned(),
            Self::Fold { minimum_separation } => {
                format!("fold (within-component at sequence separation {minimum_separation})")
            }
        }
    }
}

/// **The residue-class composition of one founded contact family.**
///
/// [definition] `admitted` counts the family's `Inside` readings by unordered residue-class pair;
/// `open` counts its `Open` readings the same way and is reported **apart**, never added in. The
/// two bounds of the family of readings are [`Self::refusing_bound`] — the composition of the
/// member that refuses every open contact, which is the presented complex's own incidence — and
/// [`Self::admitting_bound`], the member that founds them all.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct CompositionReading {
    /// The schema this reading serializes under.
    pub schema: String,
    /// Exterior lineage, retained as testimony.
    pub lineage: String,
    /// Which family, and at what separation where that applies.
    pub role: FamilyRole,
    /// The aperture the classes were read against, by its own lineage.
    pub aperture_lineage: String,
    /// The declared tables the reading was taken under. A reading under another set is a different
    /// reading and [`compare_across_tables`] refuses to compare them without a passage.
    pub tables: TableIdentity,
    /// On what ground the charged classes were admitted.
    pub protonation: ProtonationBasis,
    /// `Inside` readings, by unordered class pair.
    pub admitted: BTreeMap<ClassPair, u64>,
    /// `Open` readings, by unordered class pair. Counted on neither side.
    pub open: BTreeMap<ClassPair, u64>,
    /// How many pairs the family addresses in total.
    pub population: u64,
    /// How many of them read `Inside`.
    pub admitted_total: u64,
    /// How many read `Open`.
    pub open_total: u64,
    /// How many read `Outside`.
    pub excluded_total: u64,
}

impl CompositionReading {
    /// The lower bound of the family of readings: every open contact refused.
    pub fn refusing_bound(&self) -> BTreeMap<ClassPair, u64> {
        self.admitted.clone()
    }

    /// The upper bound: every open contact founded.
    pub fn admitting_bound(&self) -> BTreeMap<ClassPair, u64> {
        let mut bound = self.admitted.clone();
        for (key, count) in &self.open {
            *bound.entry(*key).or_default() += *count;
        }
        bound
    }

    /// Whether the two bounds differ, so the composition is genuinely plural on this presentation.
    pub fn bounds_differ(&self) -> bool {
        self.open_total > 0
    }

    /// The admitted count of one class pair.
    pub fn count(&self, pair: ClassPair) -> u64 {
        self.admitted.get(&pair).copied().unwrap_or_default()
    }

    /// The admitted salt-bridge candidates: `+`/`−` class pairs.
    pub fn salt_bridge_candidates(&self) -> u64 {
        self.admitted
            .iter()
            .filter(|(pair, _)| pair.is_salt_bridge_candidate())
            .map(|(_, count)| *count)
            .sum()
    }

    /// The admitted like-charge contacts: `+`/`+` and `−`/`−` class pairs.
    pub fn like_charge_contacts(&self) -> u64 {
        self.admitted
            .iter()
            .filter(|(pair, _)| pair.is_like_charge())
            .map(|(_, count)| *count)
            .sum()
    }

    /// The admitted hydrophobic–hydrophobic contacts.
    pub fn hydrophobic_pairs(&self) -> u64 {
        self.count(ClassPair::of(
            ResidueClass::Hydrophobic,
            ResidueClass::Hydrophobic,
        ))
    }

    /// The admitted aromatic–aromatic contacts.
    pub fn aromatic_pairs(&self) -> u64 {
        self.count(ClassPair::of(ResidueClass::Aromatic, ResidueClass::Aromatic))
    }

    /// The admitted polar–polar contacts.
    pub fn polar_pairs(&self) -> u64 {
        self.count(ClassPair::of(ResidueClass::Polar, ResidueClass::Polar))
    }

    /// **An exact rational ratio of two counts, or `None` when the denominator is zero.**
    ///
    /// A ratio with no denominator is not zero and is not one; it is absent, and this returns
    /// `None` rather than a number standing in for it. No scalar returned here is the identity of
    /// the interface: every ratio carries the two counts it came from.
    pub fn ratio(numerator: u64, denominator: u64) -> Option<Rat> {
        if denominator == 0 {
            return None;
        }
        Some(Rat::new(
            BigInt::from(numerator),
            BigInt::from(denominator),
        ))
    }

    /// The exact rational fraction of admitted contacts that are hydrophobic–hydrophobic.
    pub fn hydrophobic_fraction(&self) -> Option<Rat> {
        Self::ratio(self.hydrophobic_pairs(), self.admitted_total)
    }

    /// The exact rational ratio of salt-bridge candidates to like-charge contacts.
    pub fn charge_complementarity(&self) -> Option<Rat> {
        Self::ratio(self.salt_bridge_candidates(), self.like_charge_contacts())
    }

    /// **Additivity over disjoint contact families.**
    ///
    /// The interface family and a within-component fold family of one presentation address
    /// disjoint pair populations, which is
    /// `Foundation/AperturedGradedComplex.lean::withinPairs_disjoint_crossPairs`, so their
    /// compositions add exactly. Two readings taken
    /// under different parameter tables are refused by name, and so are two readings of the same
    /// family, because that would double-count.
    pub fn sum(&self, other: &Self) -> Result<Self, PhysicochemicalRefusal> {
        if self.tables != other.tables {
            return Err(PhysicochemicalRefusal::TablesDiffer {
                left: Box::new(self.tables.clone()),
                right: Box::new(other.tables.clone()),
            });
        }
        let mut admitted = self.admitted.clone();
        for (key, count) in &other.admitted {
            *admitted.entry(*key).or_default() += *count;
        }
        let mut open = self.open.clone();
        for (key, count) in &other.open {
            *open.entry(*key).or_default() += *count;
        }
        Ok(Self {
            schema: self.schema.clone(),
            lineage: format!("{} + {}", self.lineage, other.lineage),
            role: self.role,
            aperture_lineage: self.aperture_lineage.clone(),
            tables: self.tables.clone(),
            protonation: self.protonation.clone(),
            admitted,
            open,
            population: self.population + other.population,
            admitted_total: self.admitted_total + other.admitted_total,
            open_total: self.open_total + other.open_total,
            excluded_total: self.excluded_total + other.excluded_total,
        })
    }

    /// The admitted contacts as a dimensionless count carrying its unit.
    pub fn admitted_count(&self) -> UnitedInterval {
        UnitedInterval::count(self.admitted_total)
    }

    /// The undecided contacts as a dimensionless count carrying its unit.
    pub fn open_count(&self) -> UnitedInterval {
        UnitedInterval::count(self.open_total)
    }

    /// The excluded contacts as a dimensionless count carrying its unit.
    pub fn excluded_count(&self) -> UnitedInterval {
        UnitedInterval::count(self.excluded_total)
    }

    /// The addressed population as a dimensionless count carrying its unit.
    pub fn population_count(&self) -> UnitedInterval {
        UnitedInterval::count(self.population)
    }
}

/// **The composition of one founded contact family, under a declared protonation basis.**
///
/// `founding` indexes `PhysicalConstraintComplex::contact_families` in founding order, so a cross
/// family and a within-component family are read by the same function through the same path — the
/// contact law does not distinguish them and neither does this receiver.
pub fn composition_under_declared_protonation(
    complex: &PhysicalConstraintComplex,
    sites: &SiteTable,
    tables: &ParameterTables,
    basis: &ProtonationBasis,
    founding: usize,
) -> Result<CompositionReading, PhysicochemicalRefusal> {
    let family = complex
        .contact_families
        .get(founding)
        .ok_or(PhysicochemicalRefusal::NoSuchFounding { founding })?;
    let mut admitted: BTreeMap<ClassPair, u64> = BTreeMap::new();
    let mut open: BTreeMap<ClassPair, u64> = BTreeMap::new();
    let mut admitted_total = 0_u64;
    let mut open_total = 0_u64;
    let mut excluded_total = 0_u64;
    for reading in &family.readings {
        let left = sites.site(reading.left)?;
        let right = sites.site(reading.right)?;
        let pair = ClassPair::of(
            tables.residue_class.class_of(&left.residue)?,
            tables.residue_class.class_of(&right.residue)?,
        );
        match reading.class {
            ContactClass::Inside => {
                *admitted.entry(pair).or_default() += 1;
                admitted_total += 1;
            }
            ContactClass::Open => {
                *open.entry(pair).or_default() += 1;
                open_total += 1;
            }
            ContactClass::Outside => excluded_total += 1,
        }
    }
    Ok(CompositionReading {
        schema: COMPOSITION_SCHEMA.to_owned(),
        lineage: format!(
            "{} / founding {founding} / {}",
            complex.presentation_lineage,
            FamilyRole::of(family.kind).label()
        ),
        role: FamilyRole::of(family.kind),
        aperture_lineage: family.aperture.lineage.clone(),
        tables: tables.identity(),
        protonation: basis.clone(),
        admitted,
        open,
        population: family.readings.len() as u64,
        admitted_total,
        open_total,
        excluded_total,
    })
}

/// **The composition of one founded family of a situated occurrence.**
///
/// This is the entry point that enforces the pH gate: the protonation basis is read off the
/// occurrence's own environment, and an undeclared acidity axis is
/// [`PhysicochemicalRefusal::AcidityUndeclared`] naming the axis and carrying the environment's own
/// stated reason. A caller that wants the reading anyway declares the assumption and calls
/// [`composition_under_declared_protonation`], and the declaration travels with the reading.
pub fn situated_composition(
    occurrence: &Occurrence,
    sites: &SiteTable,
    tables: &ParameterTables,
    founding: usize,
) -> Result<CompositionReading, PhysicochemicalRefusal> {
    let basis = protonation_basis(occurrence.environment())?;
    composition_under_declared_protonation(occurrence.face(), sites, tables, &basis, founding)
}

/// **Compare two compositions. Refuses across parameter sets without a supplied passage.**
///
/// Lawful only when both readings were taken under the same [`TableIdentity`], or when a
/// [`TablePassage`] leaving the first and arriving at the second is supplied. The refusal names
/// both sets.
pub fn compare_across_tables(
    left: &CompositionReading,
    right: &CompositionReading,
    passage: Option<&TablePassage>,
) -> Result<CompositionComparison, PhysicochemicalRefusal> {
    if left.tables != right.tables {
        let Some(passage) = passage else {
            return Err(PhysicochemicalRefusal::TablesDiffer {
                left: Box::new(left.tables.clone()),
                right: Box::new(right.tables.clone()),
            });
        };
        if passage.from != left.tables || passage.to != right.tables {
            return Err(PhysicochemicalRefusal::PassageDoesNotJoinTheseTables {
                from: Box::new(passage.from.clone()),
                to: Box::new(passage.to.clone()),
            });
        }
    }
    let mut divergence = BTreeMap::new();
    for pair in left.admitted.keys().chain(right.admitted.keys()) {
        let a = left.count(*pair);
        let b = right.count(*pair);
        if a != b {
            divergence.insert(*pair, (a, b));
        }
    }
    Ok(CompositionComparison {
        schema: COMPOSITION_COMPARISON_SCHEMA.to_owned(),
        left_lineage: left.lineage.clone(),
        right_lineage: right.lineage.clone(),
        carried_by: passage.map(|passage| passage.ground.clone()),
        divergence,
        left_admitted: left.admitted_total,
        right_admitted: right.admitted_total,
    })
}

/// What a composition comparison returned.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct CompositionComparison {
    /// The schema this comparison serializes under.
    pub schema: String,
    /// The left reading's lineage.
    pub left_lineage: String,
    /// The right reading's lineage.
    pub right_lineage: String,
    /// The ground of the passage that carried the comparison, when one was needed.
    pub carried_by: Option<String>,
    /// Every class pair at which the two admitted counts differ.
    pub divergence: BTreeMap<ClassPair, (u64, u64)>,
    /// The left reading's admitted total.
    pub left_admitted: u64,
    /// The right reading's admitted total.
    pub right_admitted: u64,
}

impl CompositionComparison {
    /// Whether the two readings agree on every class pair and on the total.
    pub fn agrees(&self) -> bool {
        self.divergence.is_empty() && self.left_admitted == self.right_admitted
    }
}

// ---------------------------------------------------------------------------------------------
// 3b. Hydrogen-bond candidates
// ---------------------------------------------------------------------------------------------

/// **A declared heavy-atom distance window for a hydrogen-bond candidate, in angstroms.**
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct HydrogenBondWindow {
    lower: Rat,
    upper: Rat,
    ground: TableGround,
}

impl HydrogenBondWindow {
    /// Declare the window. Refuses a non-positive lower bound and a reversed window.
    pub fn declare(
        lower: Rat,
        upper: Rat,
        ground: TableGround,
    ) -> Result<Self, PhysicochemicalRefusal> {
        if !lower.is_positive() || upper < lower {
            return Err(PhysicochemicalRefusal::WindowNotOrdered);
        }
        Ok(Self {
            lower,
            upper,
            ground,
        })
    }

    /// The conventional heavy-atom donor–acceptor separation window, `[5/2, 7/2]` angstroms.
    pub fn conventional() -> Self {
        let ground = TableGround::declare(
            "the conventional heavy-atom donor-acceptor separation window for a hydrogen bond, \
             taken as the exact rationals 5/2 and 7/2 angstroms",
            "a distance window only. It carries no angular criterion, because an angle at the \
             donor needs the hydrogen, which a heavy-atom model does not place",
        )
        .expect("a stated source and scope");
        Self::declare(
            Rat::new(BigInt::from(5), BigInt::from(2)),
            Rat::new(BigInt::from(7), BigInt::from(2)),
            ground,
        )
        .expect("an ordered positive window")
    }

    /// The window's lower and upper bounds, as dimensioned quantities.
    pub fn bounds(&self) -> (Quantity, Quantity) {
        (
            Quantity::new(self.lower.clone(), length_dimension()),
            Quantity::new(self.upper.clone(), length_dimension()),
        )
    }

    /// Its ground.
    pub const fn ground(&self) -> &TableGround {
        &self.ground
    }

    fn near_aperture(&self) -> DistanceAperture {
        DistanceAperture {
            lineage: format!(
                "hydrogen-bond candidate window upper bound {}",
                relational_geometry::format_rat(&self.upper)
            ),
            squared: &self.upper * &self.upper,
        }
    }

    fn far_aperture(&self) -> DistanceAperture {
        DistanceAperture {
            lineage: format!(
                "hydrogen-bond candidate window lower bound {}",
                relational_geometry::format_rat(&self.lower)
            ),
            squared: &self.lower * &self.lower,
        }
    }
}

/// **One donor–acceptor heavy-atom pair inside the declared window.**
///
/// [definition] This is a **candidate** and there is deliberately no `HydrogenBond` type in this
/// module. A heavy-atom model carries no hydrogen, so no angle at the donor can be computed and no
/// bond can be certified; what the geometry supports is exactly "these two declared heavy atoms
/// are separated by a distance inside the declared window", which is what this type says.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct HydrogenBondCandidate {
    /// The declared donor heavy atom.
    pub donor: ConstraintVertexId,
    /// The declared acceptor heavy atom.
    pub acceptor: ConstraintVertexId,
    /// The donor's residue and atom label.
    pub donor_atom: String,
    /// The acceptor's residue and atom label.
    pub acceptor_atom: String,
    /// The exact squared-distance interval the admission was decided from.
    pub squared_distance: ExactInterval,
}

impl StericOverlap {
    /// The sum of the two declared radii as a dimensioned quantity in angstroms.
    pub fn radius_sum_quantity(&self) -> Quantity {
        Quantity::new(self.radius_sum.clone(), length_dimension())
    }

    /// The threshold `radius_sum − tolerance` as a dimensioned quantity in angstroms.
    pub fn threshold_quantity(&self) -> Quantity {
        Quantity::new(self.threshold.clone(), length_dimension())
    }
}

/// **Every donor–acceptor heavy-atom pair inside a declared window, with the undecided ones apart.**
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct HydrogenBondCandidateReading {
    /// The schema this reading serializes under.
    pub schema: String,
    /// Exterior lineage, retained as testimony.
    pub lineage: String,
    /// The declared tables.
    pub tables: TableIdentity,
    /// The declared window.
    pub window: HydrogenBondWindow,
    /// The declared population the reading ran over.
    pub population: String,
    /// The candidates.
    pub candidates: Vec<HydrogenBondCandidate>,
    /// Pairs whose exact interval straddles a bound of the window: undecided, carried apart, and
    /// counted on neither side.
    pub undecided: Vec<HydrogenBondCandidate>,
    /// How many pairs were read.
    pub pairs_read: u64,
    /// What a candidate is, and what it is not, retained in the artifact so a consumer reads it.
    pub reading_law: String,
}

impl HydrogenBondCandidateReading {
    /// The candidate count as a dimensionless reading carrying its unit.
    pub fn candidate_count(&self) -> UnitedInterval {
        UnitedInterval::count(self.candidates.len() as u64)
    }
}

/// **The hydrogen-bond candidate reading over a declared pair population.**
pub fn hydrogen_bond_candidates(
    complex: &PhysicalConstraintComplex,
    sites: &SiteTable,
    tables: &ParameterTables,
    window: &HydrogenBondWindow,
    population: &PairPopulation,
    bound: &PairWorkBound,
) -> Result<HydrogenBondCandidateReading, PhysicochemicalRefusal> {
    let pairs = population.pairs(sites, bound)?;
    let near = window.near_aperture();
    let far = window.far_aperture();
    let mut candidates = Vec::new();
    let mut undecided = Vec::new();
    for (left, right) in &pairs {
        let a = sites.site(*left)?;
        let b = sites.site(*right)?;
        let (Some(a_atom), Some(b_atom)) = (a.atom.as_ref(), b.atom.as_ref()) else {
            return Err(PhysicochemicalRefusal::AtomGrainRequired {
                reading: "hydrogen-bond candidates",
                grain: sites.grain.clone(),
            });
        };
        let forward = tables.hydrogen_bond.is_donor(&a.residue, a_atom)
            && tables.hydrogen_bond.is_acceptor(&b.residue, b_atom);
        let backward = tables.hydrogen_bond.is_donor(&b.residue, b_atom)
            && tables.hydrogen_bond.is_acceptor(&a.residue, a_atom);
        if !forward && !backward {
            continue;
        }
        let (donor, acceptor, donor_atom, acceptor_atom) = if forward {
            (
                *left,
                *right,
                format!("{}:{a_atom}", a.residue),
                format!("{}:{b_atom}", b.residue),
            )
        } else {
            (
                *right,
                *left,
                format!("{}:{b_atom}", b.residue),
                format!("{}:{a_atom}", a.residue),
            )
        };
        let squared = squared_distance(complex, *left, *right)?;
        let inside_near = near.classify(&squared);
        let inside_far = far.classify(&squared);
        let candidate = HydrogenBondCandidate {
            donor,
            acceptor,
            donor_atom,
            acceptor_atom,
            squared_distance: squared,
        };
        match (inside_near, inside_far) {
            // Inside the upper bound and strictly beyond the lower bound: a candidate.
            (ContactClass::Inside, ContactClass::Outside) => candidates.push(candidate),
            // Beyond the upper bound, or at or inside the lower bound: not a candidate.
            (ContactClass::Outside, _) | (_, ContactClass::Inside) => {}
            // The interval straddles a bound of the window: undecided, and carried as such.
            _ => undecided.push(candidate),
        }
    }
    Ok(HydrogenBondCandidateReading {
        schema: HYDROGEN_BOND_SCHEMA.to_owned(),
        lineage: format!("{} / hydrogen-bond candidates", complex.presentation_lineage),
        tables: tables.identity(),
        window: window.clone(),
        population: population.label(),
        candidates,
        undecided,
        pairs_read: pairs.len() as u64,
        reading_law: "a candidate is a declared donor heavy atom and a declared acceptor heavy \
                      atom whose exact separation lies inside the declared window. It is not a \
                      hydrogen bond: the model carries no hydrogen, so no angle at the donor is \
                      computed and none is claimed"
            .to_owned(),
    })
}

// ---------------------------------------------------------------------------------------------
// 3c. Steric overlap
// ---------------------------------------------------------------------------------------------

/// **One pair closer than the sum of its declared radii less a declared tolerance.**
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct StericOverlap {
    /// The left site.
    pub left: ConstraintVertexId,
    /// The right site.
    pub right: ConstraintVertexId,
    /// The left site's residue and atom label.
    pub left_atom: String,
    /// The right site's residue and atom label.
    pub right_atom: String,
    /// The exact sum of the two declared radii, in angstroms.
    pub radius_sum: Rat,
    /// The exact threshold `radius_sum − tolerance`.
    pub threshold: Rat,
    /// The exact squared-distance interval the admission was decided from.
    pub squared_distance: ExactInterval,
}

/// **The steric overlap reading: pairs inside the declared threshold, with the undecided apart.**
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct StericOverlapReading {
    /// The schema this reading serializes under.
    pub schema: String,
    /// Exterior lineage, retained as testimony.
    pub lineage: String,
    /// The declared tables.
    pub tables: TableIdentity,
    /// The declared tolerance subtracted from each radius sum, in angstroms.
    pub tolerance: Rat,
    /// The declared population.
    pub population: String,
    /// The overlaps.
    pub clashes: Vec<StericOverlap>,
    /// Pairs whose exact interval straddles the threshold. Undecided, carried apart.
    pub undecided: Vec<StericOverlap>,
    /// How many pairs were read.
    pub pairs_read: u64,
    /// What an overlap is, retained in the artifact.
    pub reading_law: String,
}

/// **The steric overlap reading over a declared pair population.**
///
/// [definition] The threshold is `r_i + r_j − tolerance` and the admission goes through
/// [`DistanceAperture::classify`], whose `Inside` arm is `d² ≤ t²`. The boundary case `d = t` is
/// therefore counted as an overlap; that is the owner's own contact convention and it is declared
/// here rather than silently chosen.
pub fn steric_overlaps(
    complex: &PhysicalConstraintComplex,
    sites: &SiteTable,
    tables: &ParameterTables,
    tolerance: &Rat,
    population: &PairPopulation,
    bound: &PairWorkBound,
) -> Result<StericOverlapReading, PhysicochemicalRefusal> {
    if tolerance.is_negative() {
        return Err(PhysicochemicalRefusal::ToleranceIsNegative);
    }
    let pairs = population.pairs(sites, bound)?;
    let mut clashes = Vec::new();
    let mut undecided = Vec::new();
    for (left, right) in &pairs {
        let a = sites.site(*left)?;
        let b = sites.site(*right)?;
        let (Some(a_element), Some(b_element)) = (a.element.as_ref(), b.element.as_ref()) else {
            return Err(PhysicochemicalRefusal::ElementAbsent {
                vertex: if a.element.is_none() { *left } else { *right },
            });
        };
        let radius_sum = &tables.radii.raw_radius(a_element)? + &tables.radii.raw_radius(b_element)?;
        let threshold = &radius_sum - tolerance;
        if !threshold.is_positive() {
            return Err(PhysicochemicalRefusal::ToleranceExceedsRadii {
                radius_sum: relational_geometry::format_rat(&radius_sum),
                tolerance: relational_geometry::format_rat(tolerance),
            });
        }
        let aperture = DistanceAperture {
            lineage: format!(
                "steric threshold {} = {} - {}",
                relational_geometry::format_rat(&threshold),
                relational_geometry::format_rat(&radius_sum),
                relational_geometry::format_rat(tolerance)
            ),
            squared: &threshold * &threshold,
        };
        let squared = squared_distance(complex, *left, *right)?;
        let overlap = StericOverlap {
            left: *left,
            right: *right,
            left_atom: format!("{}:{}", a.residue, a.atom.clone().unwrap_or_default()),
            right_atom: format!("{}:{}", b.residue, b.atom.clone().unwrap_or_default()),
            radius_sum,
            threshold,
            squared_distance: squared.clone(),
        };
        match aperture.classify(&squared) {
            ContactClass::Inside => clashes.push(overlap),
            ContactClass::Open => undecided.push(overlap),
            ContactClass::Outside => {}
        }
    }
    Ok(StericOverlapReading {
        schema: STERIC_SCHEMA.to_owned(),
        lineage: format!("{} / steric overlaps", complex.presentation_lineage),
        tables: tables.identity(),
        tolerance: tolerance.clone(),
        population: population.label(),
        clashes,
        undecided,
        pairs_read: pairs.len() as u64,
        reading_law: "an overlap is a pair whose exact separation is at or below the sum of its \
                      two declared van der Waals radii less a declared tolerance. It reads two \
                      atoms that are too close; it is structurally blind to an atom that is too \
                      far from where its covalent geometry would put it"
            .to_owned(),
    })
}

// ---------------------------------------------------------------------------------------------
// 3d. Burial proxy and half-sphere exposure
// ---------------------------------------------------------------------------------------------

/// **The exact neighbour count of one site within a declared radius.**
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize)]
pub struct NeighbourCount {
    /// Neighbours the exact law decides are inside the declared radius.
    pub inside: u64,
    /// Neighbours the exact law leaves undecided. Carried apart, counted on neither side.
    pub undecided: u64,
}

impl NeighbourCount {
    /// The decided count as a dimensionless reading carrying its unit.
    pub fn decided_count(self) -> UnitedInterval {
        UnitedInterval::count(self.inside)
    }

    /// The undecided count as a dimensionless reading carrying its unit.
    pub fn undecided_count(self) -> UnitedInterval {
        UnitedInterval::count(self.undecided)
    }
}

/// **The burial proxy: an exact integer neighbour count per site.**
///
/// [definition] This is a **proxy** and the name is the claim. It is not a solvent-accessible
/// surface area: a rolling-probe area is a numerical integral and this library takes none. What is
/// returned is the exact count of addressed sites within a declared radius, which is an integer,
/// is exact, and correlates with burial without being it.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct BurialProxyReading {
    /// The schema this reading serializes under.
    pub schema: String,
    /// Exterior lineage, retained as testimony.
    pub lineage: String,
    /// The declared radius, in angstroms.
    pub radius: Rat,
    /// The declared population.
    pub population: String,
    /// The neighbour count of every site the declared population addresses.
    pub per_site: BTreeMap<ConstraintVertexId, NeighbourCount>,
    /// How many pairs were read.
    pub pairs_read: u64,
    /// What the proxy is, and what it is not.
    pub reading_law: String,
}

impl BurialProxyReading {
    /// The declared radius as a dimensioned quantity in angstroms.
    pub fn radius_quantity(&self) -> Quantity {
        Quantity::new(self.radius.clone(), length_dimension())
    }

    /// The least and greatest decided neighbour count, and the site each is attained at.
    pub fn extremes(&self) -> Option<((ConstraintVertexId, u64), (ConstraintVertexId, u64))> {
        let mut entries = self
            .per_site
            .iter()
            .map(|(vertex, count)| (*vertex, count.inside))
            .collect::<Vec<_>>();
        entries.sort_by_key(|(vertex, count)| (*count, *vertex));
        let first = *entries.first()?;
        let last = *entries.last()?;
        Some((first, last))
    }
}

/// **The burial proxy over a declared pair population and radius.**
pub fn neighbour_count_proxy(
    complex: &PhysicalConstraintComplex,
    sites: &SiteTable,
    radius: &Rat,
    population: &PairPopulation,
    bound: &PairWorkBound,
) -> Result<BurialProxyReading, PhysicochemicalRefusal> {
    if !radius.is_positive() {
        return Err(PhysicochemicalRefusal::RadiusNotPositive {
            table: "the declared burial radius".to_owned(),
            element: relational_geometry::format_rat(radius),
        });
    }
    let pairs = population.pairs(sites, bound)?;
    let aperture = DistanceAperture {
        lineage: format!(
            "declared burial radius {}",
            relational_geometry::format_rat(radius)
        ),
        squared: radius * radius,
    };
    let mut per_site: BTreeMap<ConstraintVertexId, NeighbourCount> = BTreeMap::new();
    let addressed: BTreeSet<ConstraintVertexId> = match population {
        PairPopulation::AmongSites { sites, .. }
        | PairPopulation::SitesAgainstPresentation { sites, .. } => sites.clone(),
    };
    for vertex in &addressed {
        per_site.insert(
            *vertex,
            NeighbourCount {
                inside: 0,
                undecided: 0,
            },
        );
    }
    for (left, right) in &pairs {
        let squared = squared_distance(complex, *left, *right)?;
        let class = aperture.classify(&squared);
        for vertex in [left, right] {
            let Some(entry) = per_site.get_mut(vertex) else {
                continue;
            };
            match class {
                ContactClass::Inside => entry.inside += 1,
                ContactClass::Open => entry.undecided += 1,
                ContactClass::Outside => {}
            }
        }
    }
    Ok(BurialProxyReading {
        schema: BURIAL_SCHEMA.to_owned(),
        lineage: format!("{} / burial proxy", complex.presentation_lineage),
        radius: radius.clone(),
        population: population.label(),
        per_site,
        pairs_read: pairs.len() as u64,
        reading_law: "the exact count of addressed sites within a declared radius. It is a proxy \
                      for burial and it is not a solvent-accessible surface area: no probe is \
                      rolled, no area is computed and no numerical integral is taken anywhere in \
                      this module"
            .to_owned(),
    })
}

/// **A declared reference direction per site, as an exact interval vector.**
///
/// [definition] The direction is the difference of two presented coordinate boxes, so it is an
/// interval vector whenever the boxes have width — which is what a deposited decimal coordinate
/// gives. Nothing is collapsed to a centre.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct ReferenceDirections {
    /// The schema this declaration serializes under.
    pub schema: String,
    /// Exterior lineage.
    pub lineage: String,
    /// The atom the direction starts at.
    pub from_atom: String,
    /// The atom it points to.
    pub to_atom: String,
    directions: BTreeMap<ConstraintVertexId, [ExactInterval; 3]>,
    /// Residues that carry no such direction, named rather than given one.
    pub undirected: Vec<ConstraintVertexId>,
}

impl ReferenceDirections {
    /// The direction at one site.
    pub fn direction(
        &self,
        vertex: ConstraintVertexId,
    ) -> Result<&[ExactInterval; 3], PhysicochemicalRefusal> {
        self.directions
            .get(&vertex)
            .ok_or(PhysicochemicalRefusal::NoReferenceDirection { vertex })
    }

    /// Every directed site.
    pub const fn directions(&self) -> &BTreeMap<ConstraintVertexId, [ExactInterval; 3]> {
        &self.directions
    }
}

/// **The side-chain reference direction of every residue carrying both declared atoms.**
///
/// A residue that carries only one of them — glycine has no `CB` — is named in
/// [`ReferenceDirections::undirected`] and is given no direction. Nothing is imputed.
pub fn side_chain_directions(
    complex: &PhysicalConstraintComplex,
    sites: &SiteTable,
    from_atom: &str,
    to_atom: &str,
) -> Result<ReferenceDirections, PhysicochemicalRefusal> {
    let mut by_residue: BTreeMap<(ConstraintComponentId, u32), (Option<ConstraintVertexId>, Option<ConstraintVertexId>)> =
        BTreeMap::new();
    for site in sites.sites.values() {
        let Some(atom) = site.atom.as_ref() else {
            continue;
        };
        let entry = by_residue
            .entry((site.component, site.residue_ordinal))
            .or_insert((None, None));
        if atom == from_atom {
            entry.0 = Some(site.vertex);
        }
        if atom == to_atom {
            entry.1 = Some(site.vertex);
        }
    }
    let mut directions = BTreeMap::new();
    let mut undirected = Vec::new();
    for (from, to) in by_residue.into_values() {
        match (from, to) {
            (Some(from), Some(to)) => {
                let tail = position(complex, from)?;
                let head = position(complex, to)?;
                directions.insert(
                    from,
                    [
                        interval_difference(&head.x, &tail.x),
                        interval_difference(&head.y, &tail.y),
                        interval_difference(&head.z, &tail.z),
                    ],
                );
            }
            (Some(from), None) => undirected.push(from),
            _ => {}
        }
    }
    Ok(ReferenceDirections {
        schema: DIRECTIONS_SCHEMA.to_owned(),
        lineage: format!("{} / {from_atom} to {to_atom}", complex.presentation_lineage),
        from_atom: from_atom.to_owned(),
        to_atom: to_atom.to_owned(),
        directions,
        undirected,
    })
}

/// **The exact half-sphere exposure of one site.**
///
/// [definition] Precisely: the number of addressed sites within the declared radius whose
/// displacement from this site has an exactly positive inner product with the declared reference
/// direction (`up`), the number whose inner product is exactly negative (`down`), and the number
/// for which the exact interval arithmetic decides neither (`undecided_side`). It is a *count*,
/// not an area, and it is not a solvent-accessible surface: no sphere is triangulated, no probe is
/// rolled and no integral is taken. The plane it splits on is the one through the site normal to
/// the declared direction.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize)]
pub struct HalfSphereCount {
    /// Neighbours on the side the reference direction points to.
    pub up: u64,
    /// Neighbours on the opposite side.
    pub down: u64,
    /// Neighbours inside the radius whose side the exact interval arithmetic does not decide.
    pub undecided_side: u64,
    /// Neighbours whose membership of the radius itself is undecided.
    pub undecided_radius: u64,
}

/// **The half-sphere exposure reading.**
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct HalfSphereExposureReading {
    /// The schema this reading serializes under.
    pub schema: String,
    /// Exterior lineage.
    pub lineage: String,
    /// The declared radius, in angstroms.
    pub radius: Rat,
    /// The declared reference direction's two atoms.
    pub direction: String,
    /// The count at every directed site the population addresses.
    pub per_site: BTreeMap<ConstraintVertexId, HalfSphereCount>,
    /// Sites the population addresses that carry no declared direction.
    pub undirected: Vec<ConstraintVertexId>,
    /// How many pairs were read.
    pub pairs_read: u64,
    /// Precisely what the reading is.
    pub reading_law: String,
}

impl HalfSphereExposureReading {
    /// The declared radius as a dimensioned quantity in angstroms.
    pub fn radius_quantity(&self) -> Quantity {
        Quantity::new(self.radius.clone(), length_dimension())
    }
}

/// **The exact half-sphere exposure over a declared site set and radius.**
pub fn half_sphere_exposure(
    complex: &PhysicalConstraintComplex,
    sites: &SiteTable,
    directions: &ReferenceDirections,
    radius: &Rat,
    population: &PairPopulation,
    bound: &PairWorkBound,
) -> Result<HalfSphereExposureReading, PhysicochemicalRefusal> {
    if !radius.is_positive() {
        return Err(PhysicochemicalRefusal::RadiusNotPositive {
            table: "the declared half-sphere radius".to_owned(),
            element: relational_geometry::format_rat(radius),
        });
    }
    let pairs = population.pairs(sites, bound)?;
    let aperture = DistanceAperture {
        lineage: format!(
            "declared half-sphere radius {}",
            relational_geometry::format_rat(radius)
        ),
        squared: radius * radius,
    };
    let addressed: BTreeSet<ConstraintVertexId> = match population {
        PairPopulation::AmongSites { sites, .. }
        | PairPopulation::SitesAgainstPresentation { sites, .. } => sites.clone(),
    };
    let mut per_site: BTreeMap<ConstraintVertexId, HalfSphereCount> = BTreeMap::new();
    let mut undirected = Vec::new();
    for vertex in &addressed {
        if directions.directions.contains_key(vertex) {
            per_site.insert(
                *vertex,
                HalfSphereCount {
                    up: 0,
                    down: 0,
                    undecided_side: 0,
                    undecided_radius: 0,
                },
            );
        } else {
            undirected.push(*vertex);
        }
    }
    for (left, right) in &pairs {
        let squared = squared_distance(complex, *left, *right)?;
        let class = aperture.classify(&squared);
        if class == ContactClass::Outside {
            continue;
        }
        for (site, neighbour) in [(*left, *right), (*right, *left)] {
            let Some(entry) = per_site.get_mut(&site) else {
                continue;
            };
            if class == ContactClass::Open {
                entry.undecided_radius += 1;
                continue;
            }
            // `per_site` carries only directed sites, so this lookup stands by construction; it
            // is taken by `get` and refused by name rather than unwrapped, so the reading is total
            // whatever a caller hands it.
            let direction = directions
                .directions
                .get(&site)
                .ok_or(PhysicochemicalRefusal::NoReferenceDirection { vertex: site })?;
            let here = position(complex, site)?;
            let there = position(complex, neighbour)?;
            let displacement = [
                interval_difference(&there.x, &here.x),
                interval_difference(&there.y, &here.y),
                interval_difference(&there.z, &here.z),
            ];
            let mut pairing = ExactInterval::point(Rat::zero());
            for axis in 0..3 {
                let term = direction[axis].times(&displacement[axis])?;
                pairing = ExactInterval {
                    lower: &pairing.lower + &term.lower,
                    upper: &pairing.upper + &term.upper,
                };
            }
            if pairing.lower.is_positive() {
                entry.up += 1;
            } else if pairing.upper.is_negative() {
                entry.down += 1;
            } else {
                entry.undecided_side += 1;
            }
        }
    }
    Ok(HalfSphereExposureReading {
        schema: HALF_SPHERE_SCHEMA.to_owned(),
        lineage: format!("{} / half-sphere exposure", complex.presentation_lineage),
        radius: radius.clone(),
        direction: format!("{} -> {}", directions.from_atom, directions.to_atom),
        per_site,
        undirected,
        pairs_read: pairs.len() as u64,
        reading_law: "the exact count of addressed sites within the declared radius on each side \
                      of the plane through the site normal to the declared reference direction, \
                      with a site the exact interval arithmetic cannot place carried apart. It is \
                      a count of neighbours, not an area, and it is not a solvent-accessible \
                      surface area"
            .to_owned(),
    })
}

// ---------------------------------------------------------------------------------------------
// 3e. The declared finite electrostatic model
// ---------------------------------------------------------------------------------------------

/// **The ceiling on the declared dyadic grain of a reciprocal square root.**
///
/// [definition] `octaves` is a caller declaration that *sizes the work*: the certificate's bracket
/// is taken from an integer square root at `2 · octaves` binary places, so the shift
/// `1 << (2 · octaves)` is a `BigUint` whose extent the declaration alone decides. The ceiling is
/// checked before the shift is taken and a declaration above it is
/// [`PhysicochemicalRefusal::OctavesTooWide`], never a silent allocation. Four thousand ninety-six
/// octaves is about twelve hundred decimal places, far beyond any coordinate this library reads.
pub const OCTAVE_CEILING: u32 = 4_096;

/// **A certified rational enclosure of `1/r` from the exact interval on `r²`.**
///
/// [definition] `1/r` is irrational for almost every rational `r²`, so it is carried as an exact
/// enclosure and never rounded. The bounds come from
/// `exact_value::AlgebraicRoot::reciprocal_square_root`, which isolates `1/√s` with a Sturm
/// certificate at a declared dyadic grain: the lower bound of the enclosure of `1/√(r²_upper)` and
/// the upper bound of the enclosure of `1/√(r²_lower)` bracket `1/r` for every `r` the interval
/// admits. A squared distance whose lower bound is zero is refused by name — two coincident sites
/// have no Coulomb term, and this owner returns the refusal rather than an infinity.
pub fn reciprocal_distance_enclosure(
    squared_distance: &ExactInterval,
    octaves: u32,
) -> Result<UnitedInterval, PhysicochemicalRefusal> {
    if octaves == 0 || octaves > OCTAVE_CEILING {
        return Err(PhysicochemicalRefusal::OctavesTooWide {
            declared: octaves,
            ceiling: OCTAVE_CEILING,
        });
    }
    if !squared_distance.lower.is_positive() {
        return Err(PhysicochemicalRefusal::CoincidentSites);
    }
    let low = AlgebraicRoot::reciprocal_square_root(&squared_distance.upper, octaves)?;
    let high = AlgebraicRoot::reciprocal_square_root(&squared_distance.lower, octaves)?;
    let enclosure = ExactInterval::new(
        low.enclosure().lower.clone(),
        high.enclosure().upper.clone(),
    )?;
    Ok(UnitedInterval::found(
        enclosure,
        length_dimension().inverted(),
    ))
}

/// **The declared finite electrostatic model's reading.**
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct ElectrostaticReading {
    /// The schema this reading serializes under.
    pub schema: String,
    /// Exterior lineage, retained as testimony.
    pub lineage: String,
    /// The declared tables.
    pub tables: TableIdentity,
    /// On what ground the charges were admitted.
    pub protonation: ProtonationBasis,
    /// The declared relative permittivity.
    pub dielectric: Rat,
    /// The declared dyadic grain of the reciprocal square roots.
    pub octaves: u32,
    /// The declared pair population.
    pub population: String,
    /// The sum, as an exact enclosure carrying its unit `e² angstrom⁻¹`.
    pub enclosure: UnitedInterval,
    /// How many pairs were read.
    pub pairs_read: u64,
    /// How many of them carried a nonzero charge product and therefore contributed a term.
    pub contributing_pairs: u64,
    /// The model's approximations, stated affirmatively.
    pub approximations: Vec<String>,
    /// The equation, retained in the artifact.
    pub equation: String,
}

impl ElectrostaticReading {
    /// The reading carried into a declared energy unit by a supplied [`Cast`]. The chart change is
    /// returned rather than performed silently, at each endpoint of the enclosure.
    pub fn cast_into_energy(
        &self,
        cast: &Cast,
    ) -> Result<(CastApplication, CastApplication), PhysicochemicalRefusal> {
        let power = Rat::one();
        let first = cast.apply(&self.enclosure.lower(), &power)?;
        let second = cast.apply(&self.enclosure.upper(), &power)?;
        // The name is a contract: the result is an energy, and the pair is (lower, upper). A cast
        // of another dimension is refused, and a negative cast — lawful in `quantity` — reverses
        // the endpoints, so they are returned in the order the enclosure's name promises.
        let energy = energy_dimension();
        for application in [&first, &second] {
            if application.to != energy {
                return Err(PhysicochemicalRefusal::UnlikeUnits {
                    operation: "a cast into the declared energy unit",
                    left: format!("{:?}", application.to),
                    right: format!("{energy:?}"),
                });
            }
        }
        if first.returned.parts().0 <= second.returned.parts().0 {
            Ok((first, second))
        } else {
            Ok((second, first))
        }
    }
}

/// **The declared finite electrostatic model, as an exact enclosure.**
///
/// ```text
/// U = Σ_{i<j} q_i q_j / (ε r_ij)
/// ```
///
/// [established-bounded; implemented-exact] Its degrees of freedom are the declared site positions
/// and nothing else; its constitutive parameters are the declared formal charges and the declared
/// uniform relative permittivity; and its stated approximations travel in
/// [`ElectrostaticReading::approximations`]. It is a declared finite electrostatic model at that
/// scope and it is not a free-energy calculation, a force field or a solvated simulation.
pub fn electrostatic_enclosure(
    complex: &PhysicalConstraintComplex,
    sites: &SiteTable,
    tables: &ParameterTables,
    basis: &ProtonationBasis,
    population: &PairPopulation,
    bound: &PairWorkBound,
    octaves: u32,
) -> Result<ElectrostaticReading, PhysicochemicalRefusal> {
    if octaves == 0 || octaves > OCTAVE_CEILING {
        return Err(PhysicochemicalRefusal::OctavesTooWide {
            declared: octaves,
            ceiling: OCTAVE_CEILING,
        });
    }
    let pairs = population.pairs(sites, bound)?;
    let permittivity = tables.dielectric.relative.clone();
    let mut total = UnitedInterval::found(
        ExactInterval::point(Rat::zero()),
        coulomb_dimension(),
    );
    let mut contributing = 0_u64;
    for (left, right) in &pairs {
        let a = sites.site(*left)?;
        let b = sites.site(*right)?;
        let product = tables.formal_charge.charge_of(&a.residue)?.product(
            &tables.formal_charge.charge_of(&b.residue)?,
        )?;
        let (magnitude, _) = product.parts();
        if magnitude.is_zero() {
            continue;
        }
        contributing += 1;
        let squared = squared_distance(complex, *left, *right)?;
        let reciprocal = reciprocal_distance_enclosure(&squared, octaves)?;
        let coefficient = magnitude / &permittivity;
        let term = UnitedInterval::found(
            ExactInterval::point(coefficient),
            charge_dimension().powed(&Rat::from_integer(BigInt::from(2))),
        )
        .times(&reciprocal)?;
        total = total.sum(&term)?;
    }
    Ok(ElectrostaticReading {
        schema: ELECTROSTATIC_SCHEMA.to_owned(),
        lineage: format!("{} / electrostatic enclosure", complex.presentation_lineage),
        tables: tables.identity(),
        protonation: basis.clone(),
        dielectric: permittivity,
        octaves,
        population: population.label(),
        enclosure: total,
        pairs_read: pairs.len() as u64,
        contributing_pairs: contributing,
        approximations: electrostatic_approximations(),
        equation: "U = sum over the declared pair population of q_i q_j / (epsilon r_ij), with q \
                   in elementary charges, r in angstroms and epsilon the declared dimensionless \
                   relative permittivity, so U carries the unit e^2 angstrom^-1"
            .to_owned(),
    })
}

/// The approximations of the declared finite electrostatic model, stated affirmatively.
pub fn electrostatic_approximations() -> Vec<String> {
    [
        "point charges sit at the declared sites and nowhere else: a residue's formal charge is \
         carried entirely at its addressed site, with no charge distribution and no multipole",
        "one uniform declared relative permittivity everywhere, with no position dependence and no \
         distinct solvent region",
        "no solvent and no ions: there is no explicit water, no Poisson-Boltzmann screening and no \
         ionic strength",
        "no polarization: no induced dipole, no electronic response and no conformational \
         relaxation under the field",
        "the sum runs over the declared pair population only, so a declared cutoff is part of the \
         model and is carried in the reading rather than applied silently",
        "the formal charges hold at the declared protonation state, which is a declaration and not \
         a titration measurement",
    ]
    .into_iter()
    .map(str::to_owned)
    .collect()
}

// ---------------------------------------------------------------------------------------------
// The exact rigid motions this receiver's laws are stated under
// ---------------------------------------------------------------------------------------------

/// **An exact rational rigid motion of space: a rational orthogonal rotation and a translation.**
///
/// [definition] The rotation is stored as a `3 × 3` exact rational matrix and its orthogonality is
/// *checked* by the constructor — `RᵀR = I` entry by entry over `Q` — so no float and no
/// approximate rotation can reach a reading. [`Self::rotation_free`] is the pure translation,
/// which is the one that acts exactly on an interval coordinate box: a rotation maps an
/// axis-aligned box to a set that is not an axis-aligned box, so [`Self::act`] refuses a box with
/// width rather than re-enclosing it silently.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct RigidMotion {
    rotation: [[Rat; 3]; 3],
    translation: [Rat; 3],
}

impl RigidMotion {
    /// Declare the motion. The rotation is checked orthogonal exactly.
    pub fn declare(
        rotation: [[Rat; 3]; 3],
        translation: [Rat; 3],
    ) -> Result<Self, PhysicochemicalRefusal> {
        for row in 0..3 {
            for column in 0..3 {
                let mut entry = Rat::zero();
                for axis in &rotation {
                    entry += &axis[row] * &axis[column];
                }
                let expected = if row == column { Rat::one() } else { Rat::zero() };
                if entry != expected {
                    return Err(PhysicochemicalRefusal::RotationNotOrthogonal { row, column });
                }
            }
        }
        Ok(Self {
            rotation,
            translation,
        })
    }

    /// A pure translation, which acts exactly on an interval coordinate box.
    pub fn rotation_free(translation: [Rat; 3]) -> Self {
        let zero = Rat::zero();
        let one = Rat::one();
        Self {
            rotation: [
                [one.clone(), zero.clone(), zero.clone()],
                [zero.clone(), one.clone(), zero.clone()],
                [zero.clone(), zero, one],
            ],
            translation,
        }
    }

    /// Whether this motion is a pure translation.
    pub fn is_translation(&self) -> bool {
        for row in 0..3 {
            for column in 0..3 {
                let expected = if row == column { Rat::one() } else { Rat::zero() };
                if self.rotation[row][column] != expected {
                    return false;
                }
            }
        }
        true
    }

    /// **A named exact rational rotation.** The product of the two Pythagorean rotations
    /// `R_z(3/5, 4/5)` and `R_x(5/13, 12/13)`, composed with a translation. Every entry is
    /// rational, the orthogonality is exact, and the constructor checks it.
    pub fn declared_pythagorean(translation: [Rat; 3]) -> Result<Self, PhysicochemicalRefusal> {
        let f = |numerator: i64, denominator: i64| {
            Rat::new(BigInt::from(numerator), BigInt::from(denominator))
        };
        let z = [
            [f(3, 5), f(-4, 5), Rat::zero()],
            [f(4, 5), f(3, 5), Rat::zero()],
            [Rat::zero(), Rat::zero(), Rat::one()],
        ];
        let x = [
            [Rat::one(), Rat::zero(), Rat::zero()],
            [Rat::zero(), f(5, 13), f(-12, 13)],
            [Rat::zero(), f(12, 13), f(5, 13)],
        ];
        let mut rotation = [
            [Rat::zero(), Rat::zero(), Rat::zero()],
            [Rat::zero(), Rat::zero(), Rat::zero()],
            [Rat::zero(), Rat::zero(), Rat::zero()],
        ];
        for row in 0..3 {
            for column in 0..3 {
                let mut entry = Rat::zero();
                for axis in 0..3 {
                    entry += &z[row][axis] * &x[axis][column];
                }
                rotation[row][column] = entry;
            }
        }
        Self::declare(rotation, translation)
    }

    /// Act on one presented coordinate box.
    ///
    /// A pure translation acts exactly on a box of any width. A rotation maps an axis-aligned box
    /// to a set that is **not** an axis-aligned box, so a box with width is refused by name rather
    /// than re-enclosed: re-enclosing would widen the presentation, and a widened presentation is
    /// a different occurrence.
    pub fn act(&self, place: &CoordinateBox3) -> Result<CoordinateBox3, PhysicochemicalRefusal> {
        let axes = [&place.x, &place.y, &place.z];
        if !self.is_translation() && axes.iter().any(|axis| !axis.is_point()) {
            return Err(PhysicochemicalRefusal::RotationOfABoxIsNotABox);
        }
        if self.is_translation() {
            return Ok(CoordinateBox3 {
                x: place.x.translated(&self.translation[0]),
                y: place.y.translated(&self.translation[1]),
                z: place.z.translated(&self.translation[2]),
            });
        }
        let source = [
            place.x.lower.clone(),
            place.y.lower.clone(),
            place.z.lower.clone(),
        ];
        let mut moved = [Rat::zero(), Rat::zero(), Rat::zero()];
        for (row, target) in moved.iter_mut().enumerate() {
            let mut entry = self.translation[row].clone();
            for (axis, coordinate) in source.iter().enumerate() {
                entry += &self.rotation[row][axis] * coordinate;
            }
            *target = entry;
        }
        let [x, y, z] = moved;
        Ok(CoordinateBox3::point(x, y, z))
    }
}


// ---------------------------------------------------------------------------------------------
// The worked exact witness this receiver's atlas contracts are verified on
// ---------------------------------------------------------------------------------------------

/// **One worked exact presentation, its chemistry and its declared tables.**
///
/// [definition] This is the material `receiver_atlas`'s contract ledger recomputes this receiver's
/// rows against, and it is public rather than test-local for exactly that reason: a `Satisfied`
/// row is a verifier that ran, and the verifier must be able to build its witness from the library.
/// Every coordinate is an exact **point**, which is the domain the rigid-motion law is stated on.
#[derive(Debug)]
pub struct WorkedPresentation {
    /// The exact contact complex, with one cross family founded at the declared aperture.
    pub complex: PhysicalConstraintComplex,
    /// The chemistry of every addressed site.
    pub sites: SiteTable,
    /// The declared parameter set.
    pub tables: ParameterTables,
    /// The declared protonation basis: an explicit assumption, because the witness declares no pH.
    pub basis: ProtonationBasis,
}

/// The four binder and four target residues of the worked witness, at exact integer places.
const WORKED_SITES: [(&str, &str, [i64; 3], [i64; 3]); 4] = [
    ("LEU", "ILE", [0, 0, 0], [3, 0, 0]),
    ("ASP", "LYS", [0, 6, 0], [3, 6, 0]),
    ("LYS", "ASP", [0, 12, 0], [3, 12, 0]),
    ("SER", "PHE", [0, 18, 0], [3, 18, 0]),
];

fn worked_chain(label: &str, left: bool) -> ChainOccurrence {
    let token = DecimalToken::parse("0.0").expect("a plain decimal token");
    let residues = WORKED_SITES
        .iter()
        .enumerate()
        .map(|(at, (binder, target, _, _))| ResidueOccurrence {
            source_ordinal: at as i32 + 1,
            monomer: if left { (*binder).to_owned() } else { (*target).to_owned() },
            atoms: vec![AtomOccurrence {
                label: "CA".to_owned(),
                element: Some("C".to_owned()),
                alternate: None,
                x: token.clone(),
                y: token.clone(),
                z: token.clone(),
                occupancy: None,
                temperature_factor: None,
            }],
        })
        .collect::<Vec<_>>();
    ChainOccurrence {
        label_asym_id: label.to_owned(),
        entity: None,
        atom_occurrences: residues.len(),
        residues,
    }
}

fn worked_material(
    lineage: &str,
    left: bool,
    motion: Option<&RigidMotion>,
) -> Result<ComponentMaterial, PhysicochemicalRefusal> {
    let mut residues = Vec::with_capacity(WORKED_SITES.len());
    for (at, (binder, target, binder_place, target_place)) in WORKED_SITES.iter().enumerate() {
        let place = if left { binder_place } else { target_place };
        let position = CoordinateBox3::point(
            Rat::from_integer(BigInt::from(place[0])),
            Rat::from_integer(BigInt::from(place[1])),
            Rat::from_integer(BigInt::from(place[2])),
        );
        let position = match motion {
            Some(motion) => motion.act(&position)?,
            None => position,
        };
        residues.push(ResidueMaterial {
            source_ordinal: at as i32 + 1,
            monomer: if left { (*binder).to_owned() } else { (*target).to_owned() },
            position,
        });
    }
    Ok(ComponentMaterial {
        lineage: lineage.to_owned(),
        residues,
    })
}

/// The worked witness, optionally carried by an exact rational rigid motion.
///
/// The aperture is squared `16` and the two columns sit `3` apart, so the four facing pairs are
/// `Inside` and every other pair is `Outside` — a determinate presentation whose reading a rigid
/// motion must leave exactly where it was.
pub fn worked_presentation(
    motion: Option<&RigidMotion>,
) -> Result<WorkedPresentation, PhysicochemicalRefusal> {
    let grain = ComponentGrain::Representative {
        atom_label: "CA".to_owned(),
    };
    let aperture = DistanceAperture {
        lineage: "the worked witness's declared aperture, squared 16".to_owned(),
        squared: Rat::from_integer(BigInt::from(16)),
    };
    let extent = WORKED_SITES.len();
    let mut uncertainty = BTreeMap::new();
    for left in 1..=extent as u32 {
        for right in 1..=extent as u32 {
            uncertainty.insert(
                (left, right),
                PairUncertainty {
                    source_lineage: "the worked witness reads no uncertainty".to_owned(),
                    row_given_column_bits: 0,
                    column_given_row_bits: 0,
                    row_given_column: ExactInterval::point(Rat::zero()),
                    column_given_row: ExactInterval::point(Rat::zero()),
                    row_given_column_ulp: Rat::zero(),
                    column_given_row_ulp: Rat::zero(),
                },
            );
        }
    }
    let complex = found_constraint_complex(
        "physicochemical worked witness",
        EventId(1),
        vec![
            worked_material("binder", true, motion)?,
            worked_material("target", false, motion)?,
        ],
        vec![PresentedFamily {
            left: ConstraintComponentId(1),
            right: ConstraintComponentId(2),
            aperture,
            uncertainty,
        }],
    )?;
    let binder = worked_chain("A", true);
    let target = worked_chain("B", false);
    let sites = SiteTable::found(
        "physicochemical worked witness",
        &complex,
        &[&binder, &target],
        &grain,
    )?;
    let basis = declared_protonation(ExteriorDeclaration::declare(
        "the worked witness declares no pH, so the charged classes are admitted under the stated \
         assumption that aspartate and glutamate are deprotonated and lysine and arginine are \
         protonated",
        "declared by the worked witness, not by any measurement",
    )?);
    Ok(WorkedPresentation {
        complex,
        sites,
        tables: tables_histidine_neutral(),
        basis,
    })
}

// ---------------------------------------------------------------------------------------------
// Shared exact helpers
// ---------------------------------------------------------------------------------------------

fn position(
    complex: &PhysicalConstraintComplex,
    vertex: ConstraintVertexId,
) -> Result<&CoordinateBox3, PhysicochemicalRefusal> {
    complex
        .vertices
        .get(&vertex)
        .map(|presented| &presented.position)
        .ok_or(PhysicochemicalRefusal::SiteAbsent { vertex })
}

fn squared_distance(
    complex: &PhysicalConstraintComplex,
    left: ConstraintVertexId,
    right: ConstraintVertexId,
) -> Result<ExactInterval, PhysicochemicalRefusal> {
    Ok(position(complex, left)?.squared_distance(position(complex, right)?))
}

fn interval_difference(left: &ExactInterval, right: &ExactInterval) -> ExactInterval {
    ExactInterval {
        lower: &left.lower - &right.upper,
        upper: &left.upper - &right.lower,
    }
}

// ---------------------------------------------------------------------------------------------
// Schemas and refusals
// ---------------------------------------------------------------------------------------------

/// The schema a [`SiteTable`] declares.
pub const SITE_TABLE_SCHEMA: &str = "holonic-engine.physicochemical-site-table.v1";
/// The schema a [`CompositionReading`] declares.
pub const COMPOSITION_SCHEMA: &str = "holonic-engine.physicochemical-composition.v1";
/// The schema a [`CompositionComparison`] declares.
pub const COMPOSITION_COMPARISON_SCHEMA: &str =
    "holonic-engine.physicochemical-composition-comparison.v1";
/// The schema a [`HydrogenBondCandidateReading`] declares.
pub const HYDROGEN_BOND_SCHEMA: &str = "holonic-engine.physicochemical-hydrogen-bond-candidates.v1";
/// The schema a [`StericOverlapReading`] declares.
pub const STERIC_SCHEMA: &str = "holonic-engine.physicochemical-steric-overlaps.v1";
/// The schema a [`BurialProxyReading`] declares.
pub const BURIAL_SCHEMA: &str = "holonic-engine.physicochemical-burial-proxy.v1";
/// The schema a [`ReferenceDirections`] declares.
pub const DIRECTIONS_SCHEMA: &str = "holonic-engine.physicochemical-reference-directions.v1";
/// The schema a [`HalfSphereExposureReading`] declares.
pub const HALF_SPHERE_SCHEMA: &str = "holonic-engine.physicochemical-half-sphere-exposure.v1";
/// The schema an [`ElectrostaticReading`] declares.
pub const ELECTROSTATIC_SCHEMA: &str = "holonic-engine.physicochemical-electrostatic.v1";

/// Why a physicochemical reading refused. Every arm names what was wrong; no path panics on input.
#[derive(Clone, Debug, PartialEq, Eq, Error)]
pub enum PhysicochemicalRefusal {
    /// Two readings of unlike dimension were combined.
    #[error("{operation} of a {left} reading and a {right} reading: unlike units do not combine")]
    UnlikeUnits {
        /// Which operation.
        operation: &'static str,
        /// The left dimension, rendered.
        left: String,
        /// The right dimension, rendered.
        right: String,
    },
    /// A table ground carried no source or no scope.
    #[error(
        "a parameter table needs both a named source and a stated scope; a table with neither is a \
         default wearing a name"
    )]
    TableGroundNotStated,
    /// A table was declared with no name.
    #[error("a parameter table must be named, so a reading can say which table it was taken under")]
    TableNotNamed,
    /// A table was declared empty.
    #[error("the table {table} is empty, so it declares nothing")]
    TableIsEmpty {
        /// The table.
        table: String,
    },
    /// A residue the table does not name.
    #[error(
        "the table {table} does not name the residue {residue}, so its class is not declared. A \
         residue outside a table's scope is refused, never defaulted"
    )]
    ResidueNotInTable {
        /// The table.
        table: String,
        /// The residue.
        residue: String,
    },
    /// An element the radius table does not name.
    #[error("the table {table} does not name the element {element}, so its radius is not declared")]
    ElementNotInTable {
        /// The table.
        table: String,
        /// The element.
        element: String,
    },
    /// A radius that is not positive.
    #[error("{table} declares a non-positive radius for {element}")]
    RadiusNotPositive {
        /// The table.
        table: String,
        /// The element or value.
        element: String,
    },
    /// A non-positive relative permittivity.
    #[error("a relative permittivity must be positive")]
    DielectricNotPositive,
    /// A passage between two parameter sets carried no ground.
    #[error("a passage between two parameter sets needs a stated ground")]
    PassageGroundNotStated,
    /// A passage left a divergent residue unaccounted.
    #[error(
        "the passage does not account for {unaccounted:?}; a reading cannot be carried across a \
         residue the two tables class differently and the passage says nothing about"
    )]
    ResiduesUnaccounted {
        /// Every unaccounted residue.
        unaccounted: Vec<String>,
    },
    /// Two readings taken under different parameter sets were compared with no passage.
    #[error(
        "these readings were taken under two parameter sets and no passage was supplied: {left:?} \
         against {right:?}. A composition under one grouping is not a composition under another"
    )]
    TablesDiffer {
        /// The left set.
        left: Box<TableIdentity>,
        /// The right set.
        right: Box<TableIdentity>,
    },
    /// A supplied passage does not join the two sets it was supplied for.
    #[error("the supplied passage joins {from:?} to {to:?}, which are not these two readings' sets")]
    PassageDoesNotJoinTheseTables {
        /// The passage's source.
        from: Box<TableIdentity>,
        /// Its target.
        to: Box<TableIdentity>,
    },
    /// The occurrence's environment leaves the acidity axis undeclared.
    #[error(
        "the environment {lineage} leaves the {axis} coordinate undeclared, so no charged-state \
         reading is a claim about it. The environment's own stated reason is: {why}. Supply an \
         explicit protonation declaration if the reading is wanted under a stated assumption"
    )]
    AcidityUndeclared {
        /// The axis.
        axis: CoordinateName,
        /// The environment's stated reason for leaving it undeclared.
        why: String,
        /// The environment's lineage.
        lineage: String,
    },
    /// A value of another axis was filed under acidity.
    #[error("a {found} value is filed under the acidity coordinate")]
    AcidityMisfiled {
        /// What was found there.
        found: String,
    },
    /// A work bound was declared with no ceiling or no ground.
    #[error("a pair work bound needs a positive ceiling and a stated ground")]
    WorkBoundNotStated,
    /// A declared pair population exceeds its declared ceiling.
    #[error(
        "the declared population — {population} — has {pairs} pairs, above the declared ceiling \
         {ceiling} ({ground}). The count is taken before anything is sized by it"
    )]
    PairPopulationTooWide {
        /// The population, named.
        population: String,
        /// Its exact extent.
        pairs: u64,
        /// The declared ceiling.
        ceiling: u64,
        /// The ceiling's ground.
        ground: String,
    },
    /// A declared pair population's extent leaves the exact machine integer.
    #[error("the declared pair population's extent leaves the exact integer wire")]
    PairCountOverflows,
    /// A reading that needs an atom label was asked of a site carrying none. [`SiteTable::found`]
    /// supplies one at every grain, so this arm exists to keep the reading total rather than to
    /// `unwrap`; it is reachable only from a hand-built site.
    #[error("{reading} needs a site carrying an atom label; this table was read at grain {grain}")]
    AtomGrainRequired {
        /// Which reading.
        reading: &'static str,
        /// The grain the table carries.
        grain: String,
    },
    /// A site carries no element symbol.
    #[error(
        "occurrence {vertex:?} carries no element symbol, so its declared radius cannot be looked \
         up; the presentation had no type_symbol column"
    )]
    ElementAbsent {
        /// The site.
        vertex: ConstraintVertexId,
    },
    /// A site the table does not carry.
    #[error("occurrence {vertex:?} carries no declared chemistry in this site table")]
    SiteAbsent {
        /// The site.
        vertex: ConstraintVertexId,
    },
    /// A site carries no declared reference direction.
    #[error("occurrence {vertex:?} carries no declared reference direction; none is imputed")]
    NoReferenceDirection {
        /// The site.
        vertex: ConstraintVertexId,
    },
    /// The presented chains and the founded components disagree in number.
    #[error("{presented} presented chains against {founded} founded components")]
    ComponentPopulationDisagrees {
        /// How many chains were presented.
        presented: usize,
        /// How many components the complex founded.
        founded: usize,
    },
    /// The presented site population and the founded vertex population disagree.
    #[error(
        "component {component:?} presents {presented} sites where the complex founded {founded} \
         occurrences; the site table and the constraint complex read the same chain differently"
    )]
    SitePopulationDisagrees {
        /// The component.
        component: ConstraintComponentId,
        /// How many sites were produced.
        presented: usize,
        /// How many vertices the complex carries.
        founded: usize,
    },
    /// A founded vertex's monomer disagrees with the presented site's chemistry.
    #[error(
        "occurrence {vertex:?} carries the founded monomer {founded} where the presentation \
         produces {presented}"
    )]
    SiteChemistryDisagrees {
        /// The site.
        vertex: ConstraintVertexId,
        /// What the complex carries.
        founded: String,
        /// What the presentation produces.
        presented: String,
    },
    /// A residue carries several atoms with the declared representative label.
    #[error("residue {residue} carries several atoms labelled {label}; a representative is one")]
    RepresentativeNotUnique {
        /// The residue's source ordinal.
        residue: i32,
        /// The declared label.
        label: String,
    },
    /// A residue carries no atom with the declared representative label.
    #[error("residue {residue} carries no atom labelled {label}")]
    RepresentativeAbsent {
        /// The residue's source ordinal.
        residue: i32,
        /// The declared label.
        label: String,
    },
    /// There is no founded family at the addressed index.
    #[error("there is no founded contact family at index {founding}")]
    NoSuchFounding {
        /// The index.
        founding: usize,
    },
    /// A hydrogen-bond window was declared reversed or non-positive.
    #[error("a hydrogen-bond window needs a positive lower bound and an upper bound above it")]
    WindowNotOrdered,
    /// A negative steric tolerance.
    #[error("a steric tolerance is subtracted from a radius sum and may not be negative")]
    ToleranceIsNegative,
    /// A steric tolerance at or above the radius sum.
    #[error(
        "the declared tolerance {tolerance} is at or above the radius sum {radius_sum}, so the \
         threshold is not positive and no overlap is defined"
    )]
    ToleranceExceedsRadii {
        /// The radius sum, rendered.
        radius_sum: String,
        /// The tolerance, rendered.
        tolerance: String,
    },
    /// Two sites at the same place carry no Coulomb term.
    #[error(
        "two sites are coincident, so their separation encloses zero and 1/r is unbounded; the \
         Coulomb term is refused rather than returned as an infinity"
    )]
    CoincidentSites,
    /// The declared dyadic grain of the reciprocal square roots is zero or above its ceiling.
    #[error(
        "the declared dyadic grain of the reciprocal square roots is {declared}; it must be \
         positive and at most {ceiling}, because the grain alone sizes the integer square root's \
         shift and the bound is taken before the shift is"
    )]
    OctavesTooWide {
        /// What was declared.
        declared: u32,
        /// The ceiling.
        ceiling: u32,
    },
    /// A declared rotation is not orthogonal over the rationals.
    #[error("the declared rotation is not orthogonal: entry ({row},{column}) of RᵀR is wrong")]
    RotationNotOrthogonal {
        /// The row.
        row: usize,
        /// The column.
        column: usize,
    },
    /// A rotation was applied to an interval coordinate box.
    #[error(
        "a rotation maps an axis-aligned coordinate box to a set that is not an axis-aligned box; \
         re-enclosing it would widen the presentation, so the rotation is refused on a box with \
         width. A translation acts exactly on a box of any width"
    )]
    RotationOfABoxIsNotABox,
    /// The exact constraint complex refused.
    #[error("the constraint complex refused: {0}")]
    Constraint(#[from] ConstraintError),
    /// The library intake refused.
    #[error("the intake refused: {0}")]
    Intake(#[from] IntakeRefusal),
    /// The typed environment or occurrence owner refused.
    #[error("the occurrence owner refused: {0}")]
    Status(#[from] StatusRefusal),
    /// The exact value owner refused.
    #[error("the exact value owner refused: {0}")]
    ExactValue(#[from] ExactValueError),
    /// The typed-unit owner refused.
    #[error("the quantity owner refused: {0}")]
    Quantity(#[from] QuantityError),
}

#[cfg(test)]
#[path = "physicochemical_receiver/tests.rs"]
mod tests;

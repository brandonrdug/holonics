//! A lattice gauge configuration over the body's own structure group, and the exact spectrum of
//! its transfer operator.
//!
//! # Why this exists
//!
//! [`crate::structure_group`] already carries the discrete `a ∧ a`: a connection valued in a
//! declared finite group, holonomy as a group element, the basepoint-free conjugacy class, and
//! [`crate::structure_group::StructureConnection::curvature_commutator`]. What it does **not**
//! carry, and what `canon/THE_MILLENNIUM_FRAME.md`'s Yang–Mills row was corrected on 2026-08-11 to
//! say precisely, is *"a representation, a Wilson plaquette action, a transfer operator"*. Each of
//! those is a **receiver** on a connection, not a new geometry, so building them beside
//! `structure_group` would be the explorative failure `canon/THE_EXPLORATIVE_FAILURE.md` names. This
//! module is a **mouth**: every group operation below is `structure_group`'s, and what is added is
//! the reading — a lattice, a representation, an action, and one operator whose spectrum is exact.
//!
//! # What is here, and each is exact
//!
//! 1. **An integral representation.** [`IntegralRepresentation`] carries one exact integer matrix
//!    per group element. The quaternion carrier's is left multiplication on `ℤ⁴` in the basis
//!    `(1, i, j, k)`, so `Q₈` acquires a faithful four-dimensional representation with **no root of
//!    unity, no complex number and no float**; the permutation carrier's is the permutation matrix.
//!    The homomorphism law is **checked by exhaustion over every pair at construction**, not
//!    asserted, and faithfulness is measured rather than declared.
//! 2. **The plaquette holonomy.** A declared closed walk of oriented links, read through
//!    `structure_group`'s own `holonomy`. Under a gauge transformation it conjugates.
//! 3. **The Wilson action**, in **group-character form**: `S = Σ_p (1 − χ(U_p)/dim)`. The character
//!    of an integral representation is an integer, so the whole action is an exact rational. This is
//!    what keeps the action off the floating point that `1 − Re tr U / N` normally needs.
//! 4. **A transfer operator and its exact spectrum.** The configuration's own plaquette holonomies
//!    supply an empirical **class distribution** `w`, which is a class function, hence central in
//!    `ℚ[G]`, hence acts as a scalar on each isotypic block. The operator `T[g][h] = w(g⁻¹h)` on
//!    `ℚ[G]` therefore has a spectrum computable exactly: the characteristic polynomial by
//!    Faddeev–LeVerrier over `Rat`, then the **complete** rational-root census, with anything left
//!    over returned as a named unresolved factor instead of approximated.
//!
//! # The bar this module runs under — no gap claim, and the reason is not caution
//!
//! **The word "mass gap" does not appear as a claim anywhere in this module and may not be added.**
//! A finite matrix having a gap between its largest and its next eigenvalue is nearly automatic — an
//! `8 × 8` rational matrix with two distinct eigenvalues has one by arithmetic — and the Yang–Mills
//! problem is about a **family**: a continuum limit carrying lattice spacing, volume, and the
//! scaling of a correlation length. This construction carries none of those three. It has one
//! lattice, one spacing that is not a parameter at all, and no volume sequence. What it returns is
//! [`ExactSpectrum`]: the eigenvalues, their multiplicities, and the exact intervals between
//! consecutive ones. **An interval is a measurement of this operator on this configuration and is
//! not evidence about any limit.** `CLAUDE.md` §8: a receipt that could not have come out otherwise
//! carries no evidence.
//!
//! # The controls this module owes, and why each can fail
//!
//! - **A gauge-equivalent pair returns the identical action and the identical spectrum.** It can
//!   fail: the transform is applied to the links and the plaquettes are re-read, so a wrong hand on
//!   the conjugation moves both. And the pair is required to **actually differ** on some link, or
//!   the agreement is one configuration compared with itself — `CLAUDE.md` §8's vacuous gauge.
//! - **An altered plaquette moves both.** It can fail: an alteration that permutes the holonomy
//!   classes among the plaquettes leaves the class distribution fixed, so the spectrum does not
//!   move and only the action does. That is a real property of this receiver and the driver exhibits
//!   it rather than choosing an alteration that hides it.
//! - **An abelian control erases the commutator contribution.** Restricting the connection to a
//!   cyclic subgroup makes every commutator the identity and empties
//!   [`crate::structure_group::StructureConnection::separating_pairs`], while the action and the
//!   spectrum remain non-trivial — so the erasure is of the commutator and not of the reading.

use std::collections::{BTreeMap, BTreeSet};

use num_bigint::BigInt;
use num_traits::{One, Zero};
use relational_geometry::Rat;

use crate::exact_linear::{ExactLinearError, ExactRatMatrix};
use crate::rational_polynomial::{
    rational_root_census, ExactPolynomialError, RationalPolynomial,
};
use crate::structure_group::{
    GroupElement, OrientedEdge, SeparatedPair, StructureConnection, StructureGroup,
    StructureGroupRefusal,
};

// -------------------------------------------------------------------------------------------------
// refusals
// -------------------------------------------------------------------------------------------------

/// Why a lattice, a representation, or a reading was refused. Every variant names the material that
/// failed rather than reporting a position.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LatticeGaugeRefusal {
    /// The declared group did not close, or a walk left it.
    Group(StructureGroupRefusal),
    /// An exact linear operation failed on the representation's matrices.
    Linear(ExactLinearError),
    /// The characteristic polynomial could not be censused.
    Polynomial(ExactPolynomialError),
    /// A plaquette names a link the lattice does not carry.
    PlaquetteNamesAnUncarriedLink { plaquette: u64, link: u64 },
    /// A plaquette's walk does not close: step `at` departs a vertex the previous step did not
    /// reach, or the last step does not return to the first step's tail.
    PlaquetteDoesNotClose { plaquette: u64, at: usize },
    /// A plaquette carries no steps at all, so its holonomy is the identity by declaration rather
    /// than by the material. Refused for the same reason `spine_cut` refuses an empty load.
    PlaquetteIsEmpty { plaquette: u64 },
    /// Two links were declared with one identity.
    LinkDeclaredTwice { link: u64 },
    /// A link carries no group element, so the connection is not defined on the lattice.
    LinkCarriesNothing { link: u64 },
    /// A gauge transformation left a vertex unnamed. Refused rather than filled with the identity:
    /// an unnamed vertex is an undeclared transformation, not a trivial one.
    VertexCarriesNoGaugeElement { vertex: u64 },
    /// The declared representation is not a homomorphism: `rep(a·b) ≠ rep(a)·rep(b)` for the named
    /// pair. Checked by exhaustion at construction.
    RepresentationIsNotAHomomorphism { left: GroupElement, right: GroupElement },
    /// The representation sends every element to the same matrix, so its character separates
    /// nothing and no action built on it can read the configuration.
    RepresentationIsConstant,
    /// The transfer operator's dimension is zero, so there is no spectrum to return.
    NothingToDiagonalize,
}

impl std::fmt::Display for LatticeGaugeRefusal {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Group(refusal) => write!(formatter, "{refusal}"),
            Self::Linear(error) => write!(formatter, "{error}"),
            Self::Polynomial(error) => write!(formatter, "{error}"),
            Self::PlaquetteNamesAnUncarriedLink { plaquette, link } => write!(
                formatter,
                "plaquette {plaquette} names link {link}, which the lattice does not carry"
            ),
            Self::PlaquetteDoesNotClose { plaquette, at } => {
                write!(formatter, "plaquette {plaquette} does not close at step {at}")
            }
            Self::PlaquetteIsEmpty { plaquette } => write!(
                formatter,
                "plaquette {plaquette} carries no steps, so its holonomy would be a declaration"
            ),
            Self::LinkDeclaredTwice { link } => {
                write!(formatter, "link {link} was declared twice")
            }
            Self::LinkCarriesNothing { link } => {
                write!(formatter, "link {link} carries no group element")
            }
            Self::VertexCarriesNoGaugeElement { vertex } => write!(
                formatter,
                "vertex {vertex} carries no gauge element, and an unnamed vertex is undeclared \
                 rather than trivial"
            ),
            Self::RepresentationIsNotAHomomorphism { left, right } => write!(
                formatter,
                "the representation is not a homomorphism at ({left:?}, {right:?})"
            ),
            Self::RepresentationIsConstant => write!(
                formatter,
                "the representation's character separates nothing"
            ),
            Self::NothingToDiagonalize => {
                write!(formatter, "the transfer operator has extent zero")
            }
        }
    }
}

impl std::error::Error for LatticeGaugeRefusal {}

impl From<StructureGroupRefusal> for LatticeGaugeRefusal {
    fn from(refusal: StructureGroupRefusal) -> Self {
        Self::Group(refusal)
    }
}

impl From<ExactLinearError> for LatticeGaugeRefusal {
    fn from(error: ExactLinearError) -> Self {
        Self::Linear(error)
    }
}

impl From<ExactPolynomialError> for LatticeGaugeRefusal {
    fn from(error: ExactPolynomialError) -> Self {
        Self::Polynomial(error)
    }
}

// -------------------------------------------------------------------------------------------------
// the representation
// -------------------------------------------------------------------------------------------------

/// The exact integer matrix a group element acts by, in the carrier's own natural module.
///
/// - **Quaternion** — left multiplication on `ℤ⁴` in the basis `(1, i, j, k)`. `L_a ∘ L_b = L_{ab}`,
///   so this is a homomorphism for `then`'s ordered product, and it is faithful because `L_q(1) = q`
///   recovers the element. Four dimensions, integer entries, no root of unity.
/// - **Permutation** — the matrix `R` with `R[i][p(i)] = 1`, which satisfies
///   `R_p · R_q = R_{p then q}` for the same reason: `then` applies `p` first.
///
/// Both are exact over `ℤ` and therefore over `Rat`. Neither is chosen from a catalogue: the
/// dimension is read off the element's own carrier.
fn natural_matrix(element: &GroupElement) -> Result<ExactRatMatrix, LatticeGaugeRefusal> {
    let rows = match element {
        GroupElement::Permutation(images) => {
            let extent = images.len();
            let mut rows = vec![vec![Rat::zero(); extent]; extent];
            for (index, image) in images.iter().enumerate() {
                let target = usize::from(*image);
                if target >= extent {
                    return Err(LatticeGaugeRefusal::Group(
                        StructureGroupRefusal::CarriersDisagree,
                    ));
                }
                rows[index][target] = Rat::one();
            }
            rows
        }
        GroupElement::Quaternion(coefficients) => {
            let unit = |value: i8| Rat::from_integer(BigInt::from(value));
            let (a, b, c, d) = (
                coefficients[0],
                coefficients[1],
                coefficients[2],
                coefficients[3],
            );
            // Columns are the images of `1, i, j, k` under left multiplication by `a+bi+cj+dk`.
            vec![
                vec![unit(a), unit(-b), unit(-c), unit(-d)],
                vec![unit(b), unit(a), unit(-d), unit(c)],
                vec![unit(c), unit(d), unit(a), unit(-b)],
                vec![unit(d), unit(-c), unit(b), unit(a)],
            ]
        }
    };
    Ok(ExactRatMatrix::new(rows)?)
}

/// **An exact integral representation of a declared finite group, with the homomorphism law checked
/// by exhaustion.**
///
/// Nothing here is authored: the dimension is the carrier's, the matrices are computed from the
/// elements, and the two measured properties — faithfulness and how many values the character takes
/// — are returned so a caller can see whether the representation can read anything at all before
/// building an action on it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct IntegralRepresentation {
    dimension: usize,
    images: BTreeMap<GroupElement, ExactRatMatrix>,
    characters: BTreeMap<GroupElement, Rat>,
    faithful: bool,
}

impl IntegralRepresentation {
    /// Build the natural representation of a declared group, refusing a set of matrices that does
    /// not compose the way the group does.
    ///
    /// The homomorphism check is `|G|²` exact matrix products. It is the whole reason this is a
    /// constructor rather than a function: a representation whose law was never checked is a table.
    pub fn natural(group: &StructureGroup) -> Result<Self, LatticeGaugeRefusal> {
        let mut images = BTreeMap::new();
        let mut characters = BTreeMap::new();
        let mut dimension = 0usize;
        for element in group.elements() {
            let matrix = natural_matrix(element)?;
            dimension = matrix.rows();
            let mut trace = Rat::zero();
            for index in 0..matrix.rows() {
                trace += matrix.get(index, index)?;
            }
            characters.insert(element.clone(), trace);
            images.insert(element.clone(), matrix);
        }

        for left in group.elements() {
            for right in group.elements() {
                let product = left
                    .then(right)
                    .ok_or(StructureGroupRefusal::ProductLeftTheCarrier)?;
                let (Some(image), Some(l), Some(r)) = (
                    images.get(&product),
                    images.get(left),
                    images.get(right),
                ) else {
                    return Err(LatticeGaugeRefusal::Group(
                        StructureGroupRefusal::ElementIsNotInTheGroup,
                    ));
                };
                if *image != l.multiply(r)? {
                    return Err(LatticeGaugeRefusal::RepresentationIsNotAHomomorphism {
                        left: left.clone(),
                        right: right.clone(),
                    });
                }
            }
        }

        let distinct: BTreeSet<Rat> = characters.values().cloned().collect();
        if distinct.len() < 2 && group.order() > 1 {
            return Err(LatticeGaugeRefusal::RepresentationIsConstant);
        }
        let matrices: Vec<&ExactRatMatrix> = images.values().collect();
        let faithful = matrices
            .iter()
            .enumerate()
            .all(|(index, matrix)| matrices[index + 1..].iter().all(|other| *matrix != *other));

        Ok(Self { dimension, images, characters, faithful })
    }

    pub const fn dimension(&self) -> usize {
        self.dimension
    }

    /// Whether distinct elements act by distinct matrices. **Measured.** A representation that is
    /// not faithful is still lawful; it just cannot separate the elements it identifies, and a
    /// caller reading a Wilson action off it should know which it has.
    pub const fn is_faithful(&self) -> bool {
        self.faithful
    }

    pub fn matrix(&self, element: &GroupElement) -> Option<&ExactRatMatrix> {
        self.images.get(element)
    }

    /// `χ(g) = tr ρ(g)`, exactly. An integer for both carriers, carried as `Rat` because everything
    /// downstream divides by the dimension.
    pub fn character(&self, element: &GroupElement) -> Option<&Rat> {
        self.characters.get(element)
    }

    /// How many distinct values the character takes. A character taking one value reads nothing; the
    /// constructor refuses that case, and this is what a driver prints to show it did not happen by
    /// luck.
    pub fn distinct_character_values(&self) -> usize {
        self.characters
            .values()
            .cloned()
            .collect::<BTreeSet<Rat>>()
            .len()
    }

    /// `1 − χ(g)/dim` — the Wilson weight of one plaquette whose holonomy is `g`. Zero exactly at
    /// the identity of a faithful representation, and a class function because `χ` is.
    pub fn plaquette_weight(&self, element: &GroupElement) -> Option<Rat> {
        let character = self.characters.get(element)?;
        Some(Rat::one() - character / Rat::from_integer(BigInt::from(self.dimension as i64)))
    }
}

// -------------------------------------------------------------------------------------------------
// the lattice
// -------------------------------------------------------------------------------------------------

/// One oriented link of the lattice: `tail → head`, with its own identity.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct Link {
    pub id: u64,
    pub tail: u64,
    pub head: u64,
}

/// A declared closed walk of oriented links. **The walk is the caller's**, exactly as
/// `structure_group` refuses to root its own spanning tree: a plaquette is a choice of face and the
/// incidence belongs to whoever owns it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Plaquette {
    pub id: u64,
    pub walk: Vec<OrientedEdge>,
}

/// The links and the faces, with closure checked rather than assumed.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Lattice {
    links: BTreeMap<u64, Link>,
    plaquettes: Vec<Plaquette>,
}

impl Lattice {
    /// Declare a lattice, refusing an open plaquette and an unknown link by name.
    pub fn declare(
        links: impl IntoIterator<Item = Link>,
        plaquettes: impl IntoIterator<Item = Plaquette>,
    ) -> Result<Self, LatticeGaugeRefusal> {
        let mut carried: BTreeMap<u64, Link> = BTreeMap::new();
        for link in links {
            if carried.insert(link.id, link).is_some() {
                return Err(LatticeGaugeRefusal::LinkDeclaredTwice { link: link.id });
            }
        }
        let plaquettes: Vec<Plaquette> = plaquettes.into_iter().collect();
        for plaquette in &plaquettes {
            if plaquette.walk.is_empty() {
                return Err(LatticeGaugeRefusal::PlaquetteIsEmpty {
                    plaquette: plaquette.id,
                });
            }
            let mut standing: Option<u64> = None;
            let mut opened: Option<u64> = None;
            for (at, step) in plaquette.walk.iter().enumerate() {
                let link = carried.get(&step.edge).ok_or(
                    LatticeGaugeRefusal::PlaquetteNamesAnUncarriedLink {
                        plaquette: plaquette.id,
                        link: step.edge,
                    },
                )?;
                let (from, to) = if step.forward {
                    (link.tail, link.head)
                } else {
                    (link.head, link.tail)
                };
                if let Some(at_vertex) = standing {
                    if at_vertex != from {
                        return Err(LatticeGaugeRefusal::PlaquetteDoesNotClose {
                            plaquette: plaquette.id,
                            at,
                        });
                    }
                } else {
                    opened = Some(from);
                }
                standing = Some(to);
            }
            if standing != opened {
                return Err(LatticeGaugeRefusal::PlaquetteDoesNotClose {
                    plaquette: plaquette.id,
                    at: plaquette.walk.len(),
                });
            }
        }
        Ok(Self { links: carried, plaquettes })
    }

    pub fn links(&self) -> impl Iterator<Item = &Link> {
        self.links.values()
    }

    pub fn plaquettes(&self) -> &[Plaquette] {
        &self.plaquettes
    }

    pub fn vertices(&self) -> BTreeSet<u64> {
        self.links
            .values()
            .flat_map(|link| [link.tail, link.head])
            .collect()
    }
}

// -------------------------------------------------------------------------------------------------
// the configuration
// -------------------------------------------------------------------------------------------------

/// **What the abelian reading of a configuration cannot see**, as a returned population rather than
/// a flag.
///
/// The commutator of two plaquette holonomies is `structure_group`'s discrete `a ∧ a`. On an abelian
/// group every entry here is empty **by construction**, which is exactly why the abelian control is
/// a control and not a demonstration: it is the direction in which the reading is required to return
/// nothing.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CommutatorContribution {
    /// Unordered plaquette pairs read.
    pub pairs_read: usize,
    /// The pairs whose holonomies do not commute, each carrying `[F(σ), F(τ)]` itself.
    pub nonidentity: Vec<(usize, usize, GroupElement)>,
    /// The plaquettes the abelianization `G → G/[G,G]` identifies and the group separates —
    /// `structure_group`'s own falsifier, evaluated on this lattice's faces.
    pub separated: Vec<SeparatedPair>,
    /// Whether the declared group commutes at all. Measured over the closure, not declared.
    pub group_is_abelian: bool,
}

impl CommutatorContribution {
    /// Whether the group contributed anything the abelian reading could not carry.
    pub fn is_empty(&self) -> bool {
        self.nonidentity.is_empty() && self.separated.is_empty()
    }
}

/// A gauge field on a lattice: one group element per link.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GaugeConfiguration {
    lattice: Lattice,
    connection: StructureConnection,
}

impl GaugeConfiguration {
    /// Declare a configuration. Every link of the lattice must carry an element, and refusing a
    /// silent identity is the point: an unassigned link is an undeclared field, not a flat one.
    pub fn declare(
        lattice: Lattice,
        group: StructureGroup,
        assignment: impl IntoIterator<Item = (u64, GroupElement)>,
    ) -> Result<Self, LatticeGaugeRefusal> {
        let connection = StructureConnection::declare(group, assignment)?;
        for link in lattice.links() {
            connection.across(OrientedEdge::forward(link.id)).map_err(|_| {
                LatticeGaugeRefusal::LinkCarriesNothing { link: link.id }
            })?;
        }
        Ok(Self { lattice, connection })
    }

    pub const fn lattice(&self) -> &Lattice {
        &self.lattice
    }

    pub const fn connection(&self) -> &StructureConnection {
        &self.connection
    }

    /// What one link carries, by its own identity.
    pub fn carried(&self, link: u64) -> Result<GroupElement, LatticeGaugeRefusal> {
        Ok(self.connection.across(OrientedEdge::forward(link))?)
    }

    /// The holonomy of every declared plaquette, in declaration order.
    pub fn plaquette_holonomies(&self) -> Result<Vec<GroupElement>, LatticeGaugeRefusal> {
        self.lattice
            .plaquettes
            .iter()
            .map(|plaquette| Ok(self.connection.holonomy(&plaquette.walk)?))
            .collect()
    }

    /// The **basepoint-free** reading: each plaquette's holonomy class. This is the gauge-invariant
    /// one, and everything below that must be gauge invariant is built from it.
    pub fn plaquette_classes(&self) -> Result<Vec<GroupElement>, LatticeGaugeRefusal> {
        self.lattice
            .plaquettes
            .iter()
            .map(|plaquette| Ok(self.connection.holonomy_class(&plaquette.walk)?))
            .collect()
    }

    /// **The Wilson action, `S = Σ_p (1 − χ(U_p)/dim)`, exactly over `Rat`.**
    ///
    /// The character is a class function, so `S` does not depend on where a plaquette is based, and
    /// it is gauge invariant for the same reason. It is zero exactly when every plaquette holonomy
    /// lies in the kernel of the character's own separation — for a faithful representation, when
    /// the configuration is flat on the declared faces.
    pub fn wilson_action(
        &self,
        representation: &IntegralRepresentation,
    ) -> Result<Rat, LatticeGaugeRefusal> {
        let mut action = Rat::zero();
        for holonomy in self.plaquette_holonomies()? {
            let weight = representation.plaquette_weight(&holonomy).ok_or(
                LatticeGaugeRefusal::Group(StructureGroupRefusal::ElementIsNotInTheGroup),
            )?;
            action += weight;
        }
        Ok(action)
    }

    /// **The gauge transformation `U_e ↦ g_tail⁻¹ · U_e · g_head`.**
    ///
    /// Every vertex of the lattice must be named. An unnamed vertex is refused rather than filled
    /// with the identity, because a partial transformation and a transformation that is trivial
    /// somewhere are different declarations and only one of them was made.
    ///
    /// On a closed walk this conjugates the holonomy by the walk's own basepoint element, which is
    /// why the class, the action and the spectrum below cannot move under it — and why a driver must
    /// check that some link *did* move, or the invariance is vacuous.
    pub fn gauge_transformed(
        &self,
        gauge: &BTreeMap<u64, GroupElement>,
    ) -> Result<Self, LatticeGaugeRefusal> {
        let group = self.connection.group().clone();
        let mut assignment = Vec::new();
        for link in self.lattice.links() {
            let at_tail = gauge.get(&link.tail).ok_or(
                LatticeGaugeRefusal::VertexCarriesNoGaugeElement { vertex: link.tail },
            )?;
            let at_head = gauge.get(&link.head).ok_or(
                LatticeGaugeRefusal::VertexCarriesNoGaugeElement { vertex: link.head },
            )?;
            for element in [at_tail, at_head] {
                if !group.contains(element) {
                    return Err(LatticeGaugeRefusal::Group(
                        StructureGroupRefusal::ElementIsNotInTheGroup,
                    ));
                }
            }
            let carried = self.carried(link.id)?;
            let moved = at_tail
                .inverse()
                .and_then(|inverse| inverse.then(&carried))
                .and_then(|partial| partial.then(at_head))
                .ok_or(StructureGroupRefusal::ProductLeftTheCarrier)?;
            assignment.push((link.id, moved));
        }
        Self::declare(self.lattice.clone(), group, assignment)
    }

    /// A configuration with one link's element replaced. The alteration is the caller's declaration
    /// and is refused when the element is not in the group.
    pub fn with_link(
        &self,
        link: u64,
        element: GroupElement,
    ) -> Result<Self, LatticeGaugeRefusal> {
        let group = self.connection.group().clone();
        if !group.contains(&element) {
            return Err(LatticeGaugeRefusal::Group(
                StructureGroupRefusal::ElementIsNotInTheGroup,
            ));
        }
        let mut assignment = Vec::new();
        for carried in self.lattice.links() {
            let value = if carried.id == link {
                element.clone()
            } else {
                self.carried(carried.id)?
            };
            assignment.push((carried.id, value));
        }
        Self::declare(self.lattice.clone(), group, assignment)
    }

    /// The commutator population of the declared faces. See [`CommutatorContribution`].
    pub fn commutator_contribution(&self) -> Result<CommutatorContribution, LatticeGaugeRefusal> {
        let group = self.connection.group();
        let derived = group.commutator_subgroup()?;
        let walks: Vec<Vec<OrientedEdge>> = self
            .lattice
            .plaquettes
            .iter()
            .map(|plaquette| plaquette.walk.clone())
            .collect();
        let mut nonidentity = Vec::new();
        let mut pairs_read = 0usize;
        for left in 0..walks.len() {
            for right in (left + 1)..walks.len() {
                pairs_read += 1;
                let commutator = self
                    .connection
                    .curvature_commutator(&walks[left], &walks[right])?;
                if !commutator.is_identity() {
                    nonidentity.push((left, right, commutator));
                }
            }
        }
        Ok(CommutatorContribution {
            pairs_read,
            nonidentity,
            separated: self.connection.separating_pairs(&walks, &derived)?,
            group_is_abelian: group.is_abelian(),
        })
    }

    /// **The empirical class distribution of the declared plaquettes**, exactly: the share of
    /// plaquettes whose holonomy lies in each conjugacy class.
    ///
    /// A class function, hence central in `ℚ[G]`, hence a scalar on every isotypic block — which is
    /// the whole reason the spectrum below is exactly computable. Gauge invariant because a class is.
    pub fn class_distribution(&self) -> Result<BTreeMap<GroupElement, Rat>, LatticeGaugeRefusal> {
        let classes = self.plaquette_classes()?;
        let total = Rat::from_integer(BigInt::from(classes.len() as i64));
        let mut counts: BTreeMap<GroupElement, Rat> = BTreeMap::new();
        for class in classes {
            *counts.entry(class).or_insert_with(Rat::zero) += Rat::one();
        }
        if total.is_zero() {
            return Ok(counts);
        }
        Ok(counts
            .into_iter()
            .map(|(class, count)| (class, count / &total))
            .collect())
    }

    /// **The transfer operator `T[g][h] = w(g⁻¹ · h)` on `ℚ[G]`**, where `w` is
    /// [`GaugeConfiguration::class_distribution`] extended by zero.
    ///
    /// The one-step operator of the configuration's own plaquette population: the amplitude to pass
    /// from the link value `g` to the link value `h` is the share of declared faces whose holonomy
    /// is the class of the difference `g⁻¹h`. Rows and columns are indexed by the group's own
    /// `BTreeSet` order, which is a **receiver coordinate** and is returned beside the matrix rather
    /// than folded into it.
    pub fn transfer_operator(
        &self,
    ) -> Result<(Vec<GroupElement>, ExactRatMatrix), LatticeGaugeRefusal> {
        let group = self.connection.group();
        let distribution = self.class_distribution()?;
        let order: Vec<GroupElement> = group.elements().cloned().collect();
        let mut rows = Vec::with_capacity(order.len());
        for left in &order {
            let inverse = left
                .inverse()
                .ok_or(StructureGroupRefusal::ProductLeftTheCarrier)?;
            let mut row = Vec::with_capacity(order.len());
            for right in &order {
                let difference = inverse
                    .then(right)
                    .ok_or(StructureGroupRefusal::ProductLeftTheCarrier)?;
                let class = group
                    .conjugacy_class(&difference)
                    .ok_or(StructureGroupRefusal::ProductLeftTheCarrier)?;
                row.push(distribution.get(&class).cloned().unwrap_or_else(Rat::zero));
            }
            rows.push(row);
        }
        Ok((order, ExactRatMatrix::new(rows)?))
    }

    /// The exact spectrum of [`GaugeConfiguration::transfer_operator`].
    pub fn transfer_spectrum(&self) -> Result<ExactSpectrum, LatticeGaugeRefusal> {
        let (_, operator) = self.transfer_operator()?;
        exact_spectrum(&operator)
    }
}

// -------------------------------------------------------------------------------------------------
// the spectrum
// -------------------------------------------------------------------------------------------------

/// **What an exact diagonalization returns, including what it could not resolve.**
///
/// The rational eigenvalues are **complete** — the census underneath is exhaustive, not a search —
/// and every root that is not rational is left in [`ExactSpectrum::unresolved`] rather than
/// approximated. A spectrum that reports `is_completely_rational` has accounted for every direction
/// of the operator; one that does not says exactly how many are missing and in what factor.
///
/// [`ExactSpectrum::intervals`] is the gap between consecutive **distinct** eigenvalues, ascending.
/// It is a measurement of this operator and nothing else — see this module's head on why no gap
/// here is evidence about a limit.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExactSpectrum {
    pub extent: usize,
    pub characteristic: RationalPolynomial,
    /// Distinct rational eigenvalues, ascending, each with its multiplicity in the characteristic
    /// polynomial.
    pub rational_eigenvalues: Vec<(Rat, usize)>,
    /// The factor of the characteristic polynomial left after dividing out every rational
    /// eigenvalue with its multiplicity. Constant exactly when the spectrum is entirely rational.
    pub unresolved: RationalPolynomial,
    /// Gaps between consecutive distinct rational eigenvalues, ascending.
    pub intervals: Vec<Rat>,
}

impl ExactSpectrum {
    /// Whether every direction of the operator is accounted for by a rational eigenvalue.
    pub fn is_completely_rational(&self) -> bool {
        self.unresolved.degree().is_none_or(|degree| degree == 0)
    }

    /// The sum of the multiplicities — how many of the operator's directions are placed exactly.
    pub fn accounted(&self) -> usize {
        self.rational_eigenvalues
            .iter()
            .map(|(_, multiplicity)| *multiplicity)
            .sum()
    }

    /// The largest eigenvalue, when the spectrum has one.
    pub fn largest(&self) -> Option<&Rat> {
        self.rational_eigenvalues.last().map(|(value, _)| value)
    }
}

/// The characteristic polynomial of an exact rational matrix, by Faddeev–LeVerrier.
///
/// `M₀ = 0`, `c₀ = 1`; then `M_k = A·M_{k−1} + c_{k−1}·I` and `c_k = −tr(A·M_k)/k`. Every step is a
/// matrix product and a trace over `Rat`, so the whole computation is exact and needs no pivoting,
/// no determinant expansion and no polynomial matrix. The return is monic of degree `n`.
pub fn characteristic_polynomial(
    operator: &ExactRatMatrix,
) -> Result<RationalPolynomial, LatticeGaugeRefusal> {
    if !operator.is_square() {
        return Err(LatticeGaugeRefusal::Linear(ExactLinearError::NonsquareMatrix));
    }
    let extent = operator.rows();
    if extent == 0 {
        return Err(LatticeGaugeRefusal::NothingToDiagonalize);
    }
    let identity = ExactRatMatrix::identity(extent)?;
    let mut coefficients = vec![Rat::one()];
    let mut standing = ExactRatMatrix::zero(extent, extent)?;
    for step in 1..=extent {
        let last = coefficients
            .last()
            .cloned()
            .ok_or(LatticeGaugeRefusal::NothingToDiagonalize)?;
        standing = operator.multiply(&standing)?.add(&identity.scaled(&last))?;
        let product = operator.multiply(&standing)?;
        let mut trace = Rat::zero();
        for index in 0..extent {
            trace += product.get(index, index)?;
        }
        coefficients.push(-trace / Rat::from_integer(BigInt::from(step as i64)));
    }
    // `coefficients[k]` multiplies `x^(extent-k)`; `RationalPolynomial` is ascending.
    coefficients.reverse();
    Ok(RationalPolynomial::new(coefficients))
}

/// **The exact spectrum of a rational matrix**: the complete rational eigenvalue population with
/// multiplicities, and the unresolved factor returned by name.
pub fn exact_spectrum(operator: &ExactRatMatrix) -> Result<ExactSpectrum, LatticeGaugeRefusal> {
    let characteristic = characteristic_polynomial(operator)?;
    let census = rational_root_census(&characteristic)?;
    let mut remaining = characteristic.clone();
    let mut placed: Vec<(Rat, usize)> = Vec::new();
    for root in &census.rational_roots {
        let divisor = RationalPolynomial::new(vec![-root.clone(), Rat::one()]);
        let mut multiplicity = 0usize;
        loop {
            let Ok((quotient, remainder)) = remaining.divided_by(&divisor) else {
                break;
            };
            if !remainder.is_zero() {
                break;
            }
            remaining = quotient;
            multiplicity += 1;
        }
        if multiplicity > 0 {
            placed.push((root.clone(), multiplicity));
        }
    }
    placed.sort_by(|left, right| left.0.cmp(&right.0));
    let intervals = placed
        .windows(2)
        .map(|pair| &pair[1].0 - &pair[0].0)
        .collect();
    Ok(ExactSpectrum {
        extent: operator.rows(),
        characteristic,
        rational_eigenvalues: placed,
        unresolved: remaining,
        intervals,
    })
}

// -------------------------------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    /// `Q₈`, from the two quaternion generators `i` and `j`. Non-abelian, order eight, and the
    /// smallest group carrying a faithful integral representation with a central involution.
    fn quaternion_group() -> StructureGroup {
        StructureGroup::close(
            [
                GroupElement::Quaternion([0, 1, 0, 0]),
                GroupElement::Quaternion([0, 0, 1, 0]),
            ],
            8,
        )
        .expect("Q8 closes at order eight")
    }

    /// `⟨i⟩ ≅ ℤ/4` — the abelian control, a subgroup of the same carrier so the two readings differ
    /// only in the group and never in the material.
    fn cyclic_four() -> StructureGroup {
        StructureGroup::close([GroupElement::Quaternion([0, 1, 0, 0])], 4)
            .expect("<i> closes at order four")
    }

    fn quaternion(coefficients: [i8; 4]) -> GroupElement {
        GroupElement::Quaternion(coefficients)
    }

    /// The `extent × extent` periodic lattice: `extent²` vertices, two links per vertex, one Wilson
    /// face per vertex `U_x(v) · U_y(v+x̂) · U_x(v+ŷ)⁻¹ · U_y(v)⁻¹`.
    ///
    /// The extent is the **caller's declaration**, which is why it is an argument and not a constant
    /// in this module: `canon/THE_AUTHORED_LEVEL.md`. Vertices are `(row, column)` folded as
    /// `extent·row + column`, so the torus wraps in both directions and the incidence is read off
    /// that folding rather than declared twice.
    fn torus(extent: u64) -> Lattice {
        let vertex = move |row: u64, column: u64| extent * (row % extent) + (column % extent);
        let x_link = move |row: u64, column: u64| 100 + vertex(row, column);
        let y_link = move |row: u64, column: u64| 200 + vertex(row, column);
        let mut links = Vec::new();
        let mut plaquettes = Vec::new();
        for row in 0..extent {
            for column in 0..extent {
                links.push(Link {
                    id: x_link(row, column),
                    tail: vertex(row, column),
                    head: vertex(row, column + 1),
                });
                links.push(Link {
                    id: y_link(row, column),
                    tail: vertex(row, column),
                    head: vertex(row + 1, column),
                });
                plaquettes.push(Plaquette {
                    id: vertex(row, column),
                    walk: vec![
                        OrientedEdge::forward(x_link(row, column)),
                        OrientedEdge::forward(y_link(row, column + 1)),
                        OrientedEdge::backward(x_link(row + 1, column)),
                        OrientedEdge::backward(y_link(row, column)),
                    ],
                });
            }
        }
        Lattice::declare(links, plaquettes).expect("the torus closes")
    }

    /// Build a configuration on the `3 × 3` torus from a declared list of non-identity links, every
    /// other link carrying the identity of the group's own carrier.
    fn configuration(
        group: StructureGroup,
        carried: &[(u64, GroupElement)],
    ) -> GaugeConfiguration {
        let lattice = torus(3);
        let identity = group.identity().clone();
        let assignment: Vec<(u64, GroupElement)> = lattice
            .links()
            .map(|link| {
                let element = carried
                    .iter()
                    .find(|(id, _)| *id == link.id)
                    .map_or_else(|| identity.clone(), |(_, element)| element.clone());
                (link.id, element)
            })
            .collect();
        GaugeConfiguration::declare(lattice, group, assignment).expect("every link carries")
    }

    /// **A configuration whose plaquette holonomies do not all commute, and which also carries both
    /// `1` and `−1`** — so the commutator population and `separating_pairs` are both non-empty.
    ///
    /// Both together need at least nine faces. On the `2 × 2` torus the abelianized holonomies of
    /// the four faces multiply to the identity, so carrying `1` and `−1` (the only pair `Q₈`'s
    /// abelianization identifies) forces the remaining two into one abelianized class, hence into
    /// one cyclic subgroup, hence to commute. That is a property of the lattice and not of the
    /// group, and it is why the fixture is `3 × 3`.
    fn twisted() -> GaugeConfiguration {
        configuration(
            quaternion_group(),
            &[
                (100, quaternion([0, 1, 0, 0])),
                (201, quaternion([0, 0, 1, 0])),
                (104, quaternion([-1, 0, 0, 0])),
            ],
        )
    }

    fn rat(value: i64) -> Rat {
        Rat::from_integer(BigInt::from(value))
    }

    // ---------------------------------------------------------------------------------------------
    // the representation

    /// The homomorphism law is **checked**, not asserted, and the character is the one an integral
    /// representation of `Q₈` actually has: `χ(1) = 4`, `χ(−1) = −4`, `χ = 0` on the six others.
    #[test]
    fn the_quaternion_representation_is_a_faithful_integral_homomorphism() {
        let group = quaternion_group();
        assert_eq!(group.order(), 8);
        assert!(!group.is_abelian());
        let representation = IntegralRepresentation::natural(&group).expect("the law holds");
        assert_eq!(representation.dimension(), 4);
        assert!(representation.is_faithful());
        assert_eq!(representation.distinct_character_values(), 3);
        assert_eq!(*representation.character(&quaternion([1, 0, 0, 0])).unwrap(), rat(4));
        assert_eq!(*representation.character(&quaternion([-1, 0, 0, 0])).unwrap(), rat(-4));
        assert_eq!(*representation.character(&quaternion([0, 1, 0, 0])).unwrap(), rat(0));
        // The Wilson weight is zero at the identity and maximal at the half turn -- `-1 = e^{iπ}`
        // as a group element, `CLAUDE.md` §2b.
        assert_eq!(
            representation.plaquette_weight(&quaternion([1, 0, 0, 0])).unwrap(),
            Rat::zero()
        );
        assert_eq!(
            representation.plaquette_weight(&quaternion([-1, 0, 0, 0])).unwrap(),
            rat(2)
        );
    }

    /// The permutation carrier's representation composes in the same order `then` does. Without
    /// this the two carriers would disagree about which of `R_p R_q` and `R_q R_p` the product is,
    /// and only one of them is a homomorphism.
    #[test]
    fn the_permutation_representation_composes_in_the_order_the_group_does() {
        let symmetric_three = StructureGroup::close(
            [
                GroupElement::Permutation(vec![1, 2, 0]),
                GroupElement::Permutation(vec![1, 0, 2]),
            ],
            6,
        )
        .expect("S3 closes");
        assert_eq!(symmetric_three.order(), 6);
        let representation =
            IntegralRepresentation::natural(&symmetric_three).expect("the law holds");
        assert_eq!(representation.dimension(), 3);
        assert!(representation.is_faithful());
        // The character of the natural permutation representation is the fixed-point count.
        assert_eq!(
            *representation
                .character(&GroupElement::Permutation(vec![1, 0, 2]))
                .unwrap(),
            rat(1)
        );
    }

    // ---------------------------------------------------------------------------------------------
    // the lattice

    #[test]
    fn a_plaquette_that_does_not_close_is_refused_by_the_step_that_opens_it() {
        let links = [
            Link { id: 1, tail: 0, head: 1 },
            Link { id: 2, tail: 1, head: 2 },
        ];
        let open = Plaquette {
            id: 7,
            walk: vec![OrientedEdge::forward(1), OrientedEdge::forward(2)],
        };
        assert_eq!(
            Lattice::declare(links, [open]),
            Err(LatticeGaugeRefusal::PlaquetteDoesNotClose { plaquette: 7, at: 2 })
        );
        let unknown = Plaquette { id: 9, walk: vec![OrientedEdge::forward(5)] };
        assert_eq!(
            Lattice::declare(links, [unknown]),
            Err(LatticeGaugeRefusal::PlaquetteNamesAnUncarriedLink { plaquette: 9, link: 5 })
        );
        let empty = Plaquette { id: 11, walk: Vec::new() };
        assert_eq!(
            Lattice::declare(links, [empty]),
            Err(LatticeGaugeRefusal::PlaquetteIsEmpty { plaquette: 11 })
        );
    }

    // ---------------------------------------------------------------------------------------------
    // the three controls

    /// **Control one: a gauge-equivalent pair returns the identical action and the identical
    /// spectrum** — and the pair is required to differ on a link first, or the agreement is one
    /// configuration compared with itself.
    #[test]
    fn a_gauge_transformation_moves_the_links_and_moves_neither_the_action_nor_the_spectrum() {
        let configuration = twisted();
        let representation =
            IntegralRepresentation::natural(configuration.connection().group()).expect("the law");
        let turns = [
            quaternion([1, 0, 0, 0]),
            quaternion([0, 1, 0, 0]),
            quaternion([0, 0, 1, 0]),
            quaternion([0, 0, 0, 1]),
            quaternion([-1, 0, 0, 0]),
        ];
        let gauge: BTreeMap<u64, GroupElement> = configuration
            .lattice()
            .vertices()
            .into_iter()
            .map(|vertex| (vertex, turns[vertex as usize % turns.len()].clone()))
            .collect();
        let moved = configuration.gauge_transformed(&gauge).expect("every vertex is named");

        let differing: Vec<u64> = configuration
            .lattice()
            .links()
            .filter(|link| {
                configuration.carried(link.id).ok() != moved.carried(link.id).ok()
            })
            .map(|link| link.id)
            .collect();
        assert!(
            !differing.is_empty(),
            "a gauge transformation that moved no link proves nothing"
        );

        assert_eq!(
            configuration.wilson_action(&representation).unwrap(),
            moved.wilson_action(&representation).unwrap(),
            "the Wilson action is a class function of the holonomy"
        );
        assert_eq!(
            configuration.transfer_spectrum().unwrap(),
            moved.transfer_spectrum().unwrap(),
            "the class distribution is gauge invariant, so its convolution is"
        );
        // And the holonomies themselves DID move -- the invariance is of the class, not of the
        // element, which is the whole reason `holonomy_class` exists.
        assert_ne!(
            configuration.plaquette_holonomies().unwrap(),
            moved.plaquette_holonomies().unwrap()
        );
        assert_eq!(
            configuration.plaquette_classes().unwrap(),
            moved.plaquette_classes().unwrap()
        );
    }

    /// **Control two: a deliberately altered plaquette moves both.**
    #[test]
    fn an_altered_link_moves_the_action_and_the_spectrum() {
        let configuration = twisted();
        let representation =
            IntegralRepresentation::natural(configuration.connection().group()).expect("the law");
        let altered = configuration
            .with_link(200, quaternion([0, 1, 0, 0]))
            .expect("i is in Q8");
        assert_ne!(
            configuration.wilson_action(&representation).unwrap(),
            altered.wilson_action(&representation).unwrap()
        );
        assert_ne!(
            configuration.transfer_spectrum().unwrap(),
            altered.transfer_spectrum().unwrap()
        );
    }

    /// **Control three: the abelian reading erases the commutator contribution and nothing else.**
    ///
    /// The same lattice, the same link pattern, the connection restricted to `⟨i⟩ ≅ ℤ/4`. The
    /// commutator population empties; the action and the spectrum stay non-trivial, so what was
    /// erased is the commutator and not the reading.
    #[test]
    fn the_cyclic_subgroup_erases_the_commutator_and_leaves_the_action_standing() {
        let twisted_configuration = twisted();
        let contribution = twisted_configuration
            .commutator_contribution()
            .expect("the group closes");
        assert!(!contribution.group_is_abelian);
        assert!(
            !contribution.nonidentity.is_empty(),
            "a non-abelian control that returned no commutator has shown the group doing nothing"
        );
        assert!(
            !contribution.separated.is_empty(),
            "the abelianization must identify two faces the group separates, or the falsifier is \
             not firing on this material"
        );

        assert!(cyclic_four().is_abelian());
        let abelian = configuration(
            cyclic_four(),
            &[
                (100, quaternion([0, 1, 0, 0])),
                (104, quaternion([-1, 0, 0, 0])),
            ],
        );
        let erased = abelian.commutator_contribution().expect("the group closes");
        assert!(erased.group_is_abelian);
        assert_eq!(erased.pairs_read, contribution.pairs_read, "the same faces are read");
        assert!(erased.is_empty(), "an abelian group contributes no commutator");

        let representation =
            IntegralRepresentation::natural(abelian.connection().group()).expect("the law");
        assert!(
            !abelian.wilson_action(&representation).unwrap().is_zero(),
            "the abelian configuration must not be flat, or the erasure is of nothing"
        );
        let spectrum = abelian.transfer_spectrum().unwrap();
        assert!(spectrum.rational_eigenvalues.len() > 1, "{spectrum:?}");
    }

    // ---------------------------------------------------------------------------------------------
    // the spectrum

    /// Faddeev–LeVerrier against a matrix whose characteristic polynomial is known by hand, and
    /// then the census: `diag(1, 2, 2)` has `(x−1)(x−2)²`, so the multiplicity has to come out of
    /// the division rather than out of the root count.
    #[test]
    fn the_characteristic_polynomial_and_the_multiplicities_are_exact() {
        let matrix = ExactRatMatrix::from_diagonal(vec![rat(1), rat(2), rat(2)]).unwrap();
        let spectrum = exact_spectrum(&matrix).expect("a diagonal matrix diagonalizes");
        assert_eq!(spectrum.extent, 3);
        assert_eq!(
            spectrum.rational_eigenvalues,
            vec![(rat(1), 1), (rat(2), 2)]
        );
        assert_eq!(spectrum.accounted(), 3);
        assert!(spectrum.is_completely_rational());
        assert_eq!(spectrum.intervals, vec![rat(1)]);
        assert_eq!(*spectrum.largest().unwrap(), rat(2));
    }

    /// **The unresolved factor is returned, not approximated.** `[[0,1],[1,0]]` has eigenvalues
    /// `±1` and is fine; `[[0,1],[2,0]]` has `±√2`, which is not rational, and the spectrum must say
    /// so by name rather than produce a decimal.
    #[test]
    fn an_irrational_spectrum_is_returned_as_an_unresolved_factor() {
        let rational = ExactRatMatrix::new(vec![
            vec![Rat::zero(), Rat::one()],
            vec![Rat::one(), Rat::zero()],
        ])
        .unwrap();
        let spectrum = exact_spectrum(&rational).unwrap();
        assert_eq!(spectrum.rational_eigenvalues, vec![(rat(-1), 1), (rat(1), 1)]);
        assert!(spectrum.is_completely_rational());
        assert_eq!(spectrum.intervals, vec![rat(2)]);

        let irrational = ExactRatMatrix::new(vec![
            vec![Rat::zero(), Rat::one()],
            vec![rat(2), Rat::zero()],
        ])
        .unwrap();
        let spectrum = exact_spectrum(&irrational).unwrap();
        assert!(spectrum.rational_eigenvalues.is_empty());
        assert!(!spectrum.is_completely_rational());
        assert_eq!(spectrum.accounted(), 0);
        assert_eq!(spectrum.unresolved.degree(), Some(2));
    }

    /// The transfer operator's rows are a probability-shaped class function: every row sums to the
    /// same total, because `w` is summed over the whole group either way. That is a property of the
    /// construction and it can fail if the conjugacy class lookup is wrong.
    #[test]
    fn every_row_of_the_transfer_operator_carries_the_same_total() {
        let configuration = twisted();
        let (order, operator) = configuration.transfer_operator().unwrap();
        assert_eq!(order.len(), 8);
        let mut totals = BTreeSet::new();
        for row in 0..operator.rows() {
            let total = operator
                .row(row)
                .unwrap()
                .iter()
                .fold(Rat::zero(), |sum, entry| sum + entry);
            totals.insert(total);
        }
        assert_eq!(totals.len(), 1, "the rows disagree: {totals:?}");
        let spectrum = configuration.transfer_spectrum().unwrap();
        assert_eq!(spectrum.extent, 8);
        assert!(
            spectrum.is_completely_rational(),
            "Q8 has a rational character table, so a rational class function has a rational \
             spectrum: {spectrum:?}"
        );
        assert_eq!(spectrum.accounted(), 8);
    }

    /// An unnamed vertex is refused rather than filled with the identity: a partial transformation
    /// and a transformation that is trivial somewhere are different declarations.
    #[test]
    fn a_gauge_transformation_missing_a_vertex_is_refused_by_name() {
        let configuration = twisted();
        let partial = BTreeMap::from([(0, quaternion([0, 1, 0, 0]))]);
        let refusal = configuration.gauge_transformed(&partial);
        assert!(
            matches!(
                refusal,
                Err(LatticeGaugeRefusal::VertexCarriesNoGaugeElement { .. })
            ),
            "{refusal:?}"
        );
    }

    /// A link the configuration never assigned is refused, so a connection cannot be half declared.
    #[test]
    fn a_link_carrying_nothing_is_refused_by_name() {
        let lattice = torus(3);
        let group = quaternion_group();
        let assignment = vec![(100u64, quaternion([0, 1, 0, 0]))];
        assert_eq!(
            GaugeConfiguration::declare(lattice, group, assignment),
            Err(LatticeGaugeRefusal::LinkCarriesNothing { link: 101 })
        );
    }
}

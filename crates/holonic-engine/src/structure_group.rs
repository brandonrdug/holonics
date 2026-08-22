//! A connection valued in a declared finite group, and the two things an integer holonomy cannot say.
//!
//! ## Why this exists
//!
//! Every curvature owner in this body is abelian. `discrete_curvature` carries one `Rat` per hinge;
//! `curvature_bridge` projects a `RatVec3` onto an edge vector and keeps the scalar, naming that
//! conversion *"genuinely lossy in the direction that matters"*; `algebraic`'s coefficients group-
//! complete to `ℤ`; `gluing` is Mayer–Vietoris over integer ranks; `running_integral::holonomy`
//! returns a `BigInt`. So the body computes `F = da` and has no term for `a ∧ a`.
//!
//! `FORMULA §CII` (BRANDON-RATIFIED 2026-07-19) says exactly what is missing:
//!
//! > *"For Holon `H` and a declared transformation family `G`, the enacted representation
//! > `U_H : G -> Aut(H)` is the carried transport law. **Spin is its rotational class, charge its
//! > weight and hand under an internal gauge connection**, and mass the invariant of its complete
//! > spacetime-translation current."*
//!
//! and the live registry states the bar, `papers/source/holonics/mathematical-physics.typ` `H.0461`,
//! `grade: "definition"`:
//!
//! > *"Charge, spin, and mass are not derived merely from triangle orientation, polarity, or
//! > gyration. **A specific symmetry group and representation law are required.**"*
//!
//! Brandon's own formulation is the other half of that bar rather than a competitor to it —
//! *"there is no such fundamental property of charge… they speak to their **local position relative
//! to other composing particles**"*, and *"these vertices are opposite to each other"*. A relative
//! position is only well posed once you declare **what may move the configuration without changing
//! the answer**. That family is `G`. The group is what makes "opposite" survive moving the picture.
//!
//! ## What this organ returns that no owner returns
//!
//! 1. **A holonomy that is a group element, not an integer** — and, basepoint-free, a *conjugacy
//!    class*. A basepoint is receiver-visible; promoting it into an invariant is `CLAUDE.md` §0's
//!    fourth lesson, so [`StructureConnection::holonomy`] is explicitly frame-relative and
//!    [`StructureConnection::holonomy_class`] is the invariant.
//! 2. **The commutator of two curvatures.** `[F(σ), F(τ)] ≠ e` is the discrete `a ∧ a`, and it is
//!    what the body currently records only as the flag `OPEN`. `OPEN` says *the two transports
//!    disagree*; this says **by how much, and in which direction**.
//! 3. **The population the abelian reading collapses.** [`StructureConnection::separating_pairs`]
//!    returns the cycles that the abelianization `G → G/[G,G]` identifies and the group separates.
//!    That is `receiver_exact_compression`'s exact loss, at the altitude of a structure group.
//! 4. **A cycle that closes below and does not close above** — [`CentralDoubleCover::lift`]. That is
//!    spin-½ as a computed object: a loop returning `z` rather than `e`, where `z² = e` and `z` is
//!    central. `CLAUDE.md` §2b says the ontology; this makes it a return.
//!
//! ## The declared falsifier, and the control that must fail
//!
//! **A gauge whose group acts trivially on the declared material is not a gauge** (`CLAUDE.md` §8,
//! and the instance that convicted `PivotRule::ALL`). So this organ is required to exhibit its own
//! orbit: [`StructureConnection::separating_pairs`] must be **non-empty** on non-abelian material,
//! and **empty** on an abelian group, where the two readings agree by construction. Both directions
//! are driven. A run reporting no separating pair on a non-abelian group has not shown the group
//! doing anything, and must say so rather than presenting flatness as a result.
//!
//! ## What this organ does NOT author
//!
//! - **The group is declared by the caller** and closed by exhaustion of the declared generators
//!   inside a finite carrier. There is no authored order, no cap, and no catalogue: `canon/THE_AUTHORED_LEVEL.md`.
//! - **The complex is not this organ's.** It evaluates holonomy on **cycles the caller declares**.
//!   `simplicial` and `running_integral` each root a spanning tree over their own material; a third
//!   would be the restatement this project convicts, and the incidence belongs to whoever owns it.
//! - **No representation is chosen.** A weight requires a representation, and §CII leaves the
//!   amplitude representation open. This organ returns the group element; what reads it is a
//!   separate question and is not decided here.

use std::collections::{BTreeMap, BTreeSet, VecDeque};

// -------------------------------------------------------------------------------------------------
// The element — two exact carriers, both finite, both integer
// -------------------------------------------------------------------------------------------------

/// One element of a declared finite group, in an exact carrier.
///
/// Two carriers, because the two returns this organ owes need different material and neither needs
/// a float:
///
/// - **`Permutation`** — one-line notation, the shape `arithmetic_monodromy` already uses for the
///   transitive subgroups of `S_5`. `A_5` lives here, and it is where the non-abelian holonomy and
///   the commutator come from.
/// - **`Quaternion`** — a unit Lipschitz quaternion `(a,b,c,d) ∈ ℤ⁴` with `a²+b²+c²+d² = 1`, so the
///   eight units are exactly `Q_8`. `Q_8 → Q_8/{±1} ≅ V_4` is the smallest exact double cover, and
///   `−1` is the element a `2π` turn returns. That is `CLAUDE.md` §2b's half-turn as a group element
///   rather than a doctrine: `−1 = e^{iπ}`.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub enum GroupElement {
    /// `p[i]` is the image of `i`. The extent is read off the vector; no degree is authored.
    Permutation(Vec<u8>),
    /// `a + bi + cj + dk`, integer coefficients.
    Quaternion([i8; 4]),
}

impl GroupElement {
    /// The identity of the carrier this element lives in. Carrier-relative because the extent of a
    /// permutation is material, not a level.
    ///
    /// **Returns `None` past the carrier's reach rather than wrapping.** `Vec<u8>` addresses 256
    /// points and holds any number of entries, so a permutation of degree 1,200 is *constructible*
    /// — and the first form of this wrote `index as u8`, which silently reduced mod 256 and returned
    /// a vector that is not a permutation at all. Every later comparison was then against garbage.
    /// The tree's two sibling permutation sites already refuse cleanly at this boundary —
    /// `arithmetic_monodromy` through `u8::try_from` into `CarrierOverflow`, and
    /// `founded_receiver` through `.ok()?` — and this one corrupted instead.
    pub fn identity_like(&self) -> Option<Self> {
        Some(match self {
            Self::Permutation(p) => Self::Permutation(
                (0..p.len())
                    .map(u8::try_from)
                    .collect::<Result<Vec<u8>, _>>()
                    .ok()?,
            ),
            Self::Quaternion(_) => Self::Quaternion([1, 0, 0, 0]),
        })
    }

    /// `self` then `next` — the ordered product, written so a walk composes left to right.
    ///
    /// Returns `None` when the two do not share a carrier or an extent. **Refused rather than
    /// coerced**: two permutations of different degree are not two elements of one group, and
    /// silently padding one would author the degree.
    pub fn then(&self, next: &Self) -> Option<Self> {
        match (self, next) {
            (Self::Permutation(first), Self::Permutation(second)) => {
                if first.len() != second.len() {
                    return None;
                }
                // Apply `first`, then `second`: `(first then second)[i] = second[first[i]]`.
                Some(Self::Permutation(
                    first
                        .iter()
                        .map(|image| second.get(usize::from(*image)).copied())
                        .collect::<Option<Vec<u8>>>()?,
                ))
            }
            (Self::Quaternion(l), Self::Quaternion(r)) => {
                let (a1, b1, c1, d1) = (l[0] as i16, l[1] as i16, l[2] as i16, l[3] as i16);
                let (a2, b2, c2, d2) = (r[0] as i16, r[1] as i16, r[2] as i16, r[3] as i16);
                let product = [
                    a1 * a2 - b1 * b2 - c1 * c2 - d1 * d2,
                    a1 * b2 + b1 * a2 + c1 * d2 - d1 * c2,
                    a1 * c2 - b1 * d2 + c1 * a2 + d1 * b2,
                    a1 * d2 + b1 * c2 - c1 * b2 + d1 * a2,
                ];
                let mut narrowed = [0i8; 4];
                for (slot, value) in product.iter().enumerate() {
                    narrowed[slot] = i8::try_from(*value).ok()?;
                }
                Some(Self::Quaternion(narrowed))
            }
            _ => None,
        }
    }

    /// The inverse. Exact in both carriers and never a search.
    pub fn inverse(&self) -> Option<Self> {
        match self {
            Self::Permutation(p) => {
                let mut image = vec![0u8; p.len()];
                for (index, target) in p.iter().enumerate() {
                    // Same boundary as `identity_like`: refuse past the carrier's reach rather
                    // than reduce mod 256 and return a vector that is not a permutation.
                    *image.get_mut(usize::from(*target))? = u8::try_from(index).ok()?;
                }
                Some(Self::Permutation(image))
            }
            // A unit quaternion's inverse is its conjugate, since the norm is 1.
            Self::Quaternion([a, b, c, d]) => Some(Self::Quaternion([
                *a,
                b.checked_neg()?,
                c.checked_neg()?,
                d.checked_neg()?,
            ])),
        }
    }

    /// Whether this element is the identity of its own carrier. An element past the carrier's
    /// reach has no identity to be, so it is not one.
    pub fn is_identity(&self) -> bool {
        self.identity_like()
            .is_some_and(|identity| *self == identity)
    }
}

// -------------------------------------------------------------------------------------------------
// The group — closed by exhaustion of declared generators
// -------------------------------------------------------------------------------------------------

/// Why a declared generating set did not close into a finite group.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum StructureGroupRefusal {
    /// No generator was declared, so there is nothing to close and no carrier to read.
    NoGeneratorDeclared,
    /// Two declared generators do not share a carrier or an extent.
    CarriersDisagree,
    /// A declared generator's degree exceeds what the permutation carrier can address, so its
    /// identity is not representable. Refused rather than reduced: a wrapped index is not a
    /// permutation, and every later comparison would be against a vector that is not one.
    CarrierOverflowed,
    /// A product left the carrier — an integer quaternion coefficient overflowed `i8`, which means
    /// the declared generators are not units and the set is not finite in this carrier.
    ProductLeftTheCarrier,
    /// The closure passed the declared bound. **The bound is the caller's**, and the refusal names
    /// what was reached so the caller can raise it against the material rather than guess.
    ClosureExceededDeclaredBound { reached: usize, bound: usize },
    /// An edge was given a group element from a different carrier than the group's.
    ElementIsNotInTheGroup,
    /// A declared walk names an edge the connection does not carry.
    WalkNamesAnUncarriedEdge(OrientedEdge),
    /// The declared centre element is not central, or is not of order two.
    CentreIsNotAnInvolution,
    /// The declared cover does not surject onto the base, or its kernel is not `{e, z}`.
    CoverIsNotDouble { kernel_order: usize },
}

impl std::fmt::Display for StructureGroupRefusal {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::NoGeneratorDeclared => write!(formatter, "no generator was declared"),
            Self::CarrierOverflowed => write!(
                formatter,
                "a declared generator's degree exceeds what the permutation carrier addresses"
            ),
            Self::CarriersDisagree => {
                write!(
                    formatter,
                    "the declared generators do not share one carrier"
                )
            }
            Self::ProductLeftTheCarrier => write!(
                formatter,
                "a product left the integer carrier: the declared generators are not units"
            ),
            Self::ClosureExceededDeclaredBound { reached, bound } => write!(
                formatter,
                "the closure reached {reached} elements past the caller's bound of {bound}"
            ),
            Self::ElementIsNotInTheGroup => {
                write!(
                    formatter,
                    "an edge carries an element outside the declared group"
                )
            }
            Self::WalkNamesAnUncarriedEdge(edge) => {
                write!(
                    formatter,
                    "the walk names edge {edge:?}, which the connection does not carry"
                )
            }
            Self::CentreIsNotAnInvolution => {
                write!(
                    formatter,
                    "the declared centre element is not central of order two"
                )
            }
            Self::CoverIsNotDouble { kernel_order } => {
                write!(
                    formatter,
                    "the cover's kernel has order {kernel_order}, not 2"
                )
            }
        }
    }
}

impl std::error::Error for StructureGroupRefusal {}

/// A finite group, given by declared generators and closed by exhaustion.
///
/// **Nothing here is authored.** The elements are whatever the declared generators generate; the
/// order is whatever that closure reaches; the carrier and its extent are read off the generators.
/// The one number the caller supplies is a **bound on the closure**, and it is the caller's
/// declaration rather than this organ's — `canon/THE_AUTHORED_LEVEL.md`: a level is read off the
/// material or declared by the caller, never authored inside the organ. Exceeding it is a typed
/// refusal naming what was reached, not a truncation.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct StructureGroup {
    elements: BTreeSet<GroupElement>,
    generators: Vec<GroupElement>,
    identity: GroupElement,
}

impl StructureGroup {
    /// Close the declared generators into a group.
    pub fn close(
        generators: impl IntoIterator<Item = GroupElement>,
        closure_bound: usize,
    ) -> Result<Self, StructureGroupRefusal> {
        let generators: Vec<GroupElement> = generators.into_iter().collect();
        let seed = generators
            .first()
            .ok_or(StructureGroupRefusal::NoGeneratorDeclared)?;
        // A generator past the carrier's reach is refused HERE, before any product is formed,
        // rather than silently reduced into a vector that is not a permutation.
        let identity = seed
            .identity_like()
            .ok_or(StructureGroupRefusal::CarrierOverflowed)?;
        for generator in &generators {
            if generator.identity_like().as_ref() != Some(&identity) {
                return Err(StructureGroupRefusal::CarriersDisagree);
            }
        }

        let mut elements = BTreeSet::from([identity.clone()]);
        let mut frontier = VecDeque::from([identity.clone()]);
        while let Some(at) = frontier.pop_front() {
            for generator in &generators {
                let next = at
                    .then(generator)
                    .ok_or(StructureGroupRefusal::ProductLeftTheCarrier)?;
                if elements.insert(next.clone()) {
                    if elements.len() > closure_bound {
                        return Err(StructureGroupRefusal::ClosureExceededDeclaredBound {
                            reached: elements.len(),
                            bound: closure_bound,
                        });
                    }
                    frontier.push_back(next);
                }
            }
        }
        Ok(Self {
            elements,
            generators,
            identity,
        })
    }

    pub fn order(&self) -> usize {
        self.elements.len()
    }

    pub fn identity(&self) -> &GroupElement {
        &self.identity
    }

    pub fn elements(&self) -> impl Iterator<Item = &GroupElement> {
        self.elements.iter()
    }

    pub fn declared_generators(&self) -> &[GroupElement] {
        &self.generators
    }

    pub fn contains(&self, element: &GroupElement) -> bool {
        self.elements.contains(element)
    }

    /// Whether every pair commutes. **Measured, not declared** — this is what decides whether the
    /// group can do anything an integer holonomy cannot, and it is checked rather than assumed.
    pub fn is_abelian(&self) -> bool {
        self.elements.iter().all(|left| {
            self.elements
                .iter()
                .all(|right| left.then(right) == right.then(left))
        })
    }

    /// `[a, b] = a b a⁻¹ b⁻¹`. The identity exactly when the two commute, so a non-identity
    /// commutator **is** the failure of two transports to agree, carried as a group element rather
    /// than reported as a flag.
    pub fn commutator(&self, left: &GroupElement, right: &GroupElement) -> Option<GroupElement> {
        left.then(right)?
            .then(&left.inverse()?)?
            .then(&right.inverse()?)
    }

    /// The derived subgroup `[G, G]`, by exhaustion over all pairs and closure.
    pub fn commutator_subgroup(&self) -> Result<BTreeSet<GroupElement>, StructureGroupRefusal> {
        let mut seeds = Vec::new();
        for left in &self.elements {
            for right in &self.elements {
                let commutator = self
                    .commutator(left, right)
                    .ok_or(StructureGroupRefusal::ProductLeftTheCarrier)?;
                if !commutator.is_identity() {
                    seeds.push(commutator);
                }
            }
        }
        if seeds.is_empty() {
            return Ok(BTreeSet::from([self.identity.clone()]));
        }
        let closed = Self::close(seeds, self.order())?;
        Ok(closed.elements)
    }

    /// The coset of `element` in `G/[G,G]`, named by its least member.
    ///
    /// **This is the abelianization, and it is the reading this organ exists to be differenced
    /// against.** An integer holonomy sees exactly this much; the group sees more, and
    /// [`StructureConnection::separating_pairs`] returns the population that difference collapses.
    pub fn abelianized_class(
        &self,
        element: &GroupElement,
        derived: &BTreeSet<GroupElement>,
    ) -> Option<GroupElement> {
        derived.iter().filter_map(|d| element.then(d)).min()
    }

    /// The conjugacy class of `element`, named by its least member.
    ///
    /// **Basepoint-free.** Holonomy around a loop depends on where the loop is based; its conjugacy
    /// class does not. A basepoint is a receiver-visible coordinate and promoting it into an
    /// invariant is `CLAUDE.md` §0's fourth lesson, so this is the invariant and
    /// [`StructureConnection::holonomy`] is the frame-relative reading.
    pub fn conjugacy_class(&self, element: &GroupElement) -> Option<GroupElement> {
        self.elements
            .iter()
            .filter_map(|g| g.then(element)?.then(&g.inverse()?))
            .min()
    }
}

// -------------------------------------------------------------------------------------------------
// The connection
// -------------------------------------------------------------------------------------------------

/// One traversal of a declared edge, with its hand.
///
/// The **hand is the whole content**: `g(reverse) = g(edge)⁻¹` is enforced by construction rather
/// than stored twice, so a connection cannot hold two inconsistent directions. That is the same law
/// `algebraic`'s `ComparativeMultiplicity` repair was about — a carrier that reduces on construction
/// has decided for every consumer which distinctions are invisible.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub struct OrientedEdge {
    pub edge: u64,
    pub forward: bool,
}

impl OrientedEdge {
    pub const fn forward(edge: u64) -> Self {
        Self {
            edge,
            forward: true,
        }
    }

    pub const fn backward(edge: u64) -> Self {
        Self {
            edge,
            forward: false,
        }
    }

    pub const fn reversed(self) -> Self {
        Self {
            edge: self.edge,
            forward: !self.forward,
        }
    }
}

/// An assignment of a group element to each declared edge: the discrete connection `a`.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct StructureConnection {
    group: StructureGroup,
    carried: BTreeMap<u64, GroupElement>,
}

/// What a declared cycle returned, at both readings.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct CycleReturn {
    /// The ordered product along the walk, from the walk's own first vertex. **Frame-relative.**
    pub holonomy: GroupElement,
    /// Its conjugacy class. **The invariant.**
    pub class: GroupElement,
    /// Its class in `G/[G,G]` — everything an integer holonomy could have seen.
    pub abelianized: GroupElement,
    /// The walk returned to where it started with nothing carried.
    pub is_trivial: bool,
}

/// Two declared cycles the abelian reading identifies and the group separates.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct SeparatedPair {
    pub left: usize,
    pub right: usize,
    /// Equal at this reading — which is all an integer holonomy carries.
    pub shared_abelianized: GroupElement,
    /// Distinct at this one.
    pub left_class: GroupElement,
    pub right_class: GroupElement,
}

impl StructureConnection {
    /// Declare a connection. Every carried element must lie in the group.
    pub fn declare(
        group: StructureGroup,
        assignment: impl IntoIterator<Item = (u64, GroupElement)>,
    ) -> Result<Self, StructureGroupRefusal> {
        let mut carried = BTreeMap::new();
        for (edge, element) in assignment {
            if !group.contains(&element) {
                return Err(StructureGroupRefusal::ElementIsNotInTheGroup);
            }
            carried.insert(edge, element);
        }
        Ok(Self { group, carried })
    }

    pub fn group(&self) -> &StructureGroup {
        &self.group
    }

    /// What this connection carries across one oriented traversal.
    pub fn across(&self, step: OrientedEdge) -> Result<GroupElement, StructureGroupRefusal> {
        let carried = self
            .carried
            .get(&step.edge)
            .ok_or(StructureGroupRefusal::WalkNamesAnUncarriedEdge(step))?;
        if step.forward {
            Ok(carried.clone())
        } else {
            carried
                .inverse()
                .ok_or(StructureGroupRefusal::ProductLeftTheCarrier)
        }
    }

    /// The ordered product along a declared walk. **Order is the content**: reversing the walk
    /// inverts the result, and in a non-abelian group reordering it changes the result.
    pub fn holonomy(&self, walk: &[OrientedEdge]) -> Result<GroupElement, StructureGroupRefusal> {
        let mut carried = self.group.identity().clone();
        for step in walk {
            carried = carried
                .then(&self.across(*step)?)
                .ok_or(StructureGroupRefusal::ProductLeftTheCarrier)?;
        }
        Ok(carried)
    }

    /// The basepoint-free invariant of a declared cycle.
    pub fn holonomy_class(
        &self,
        walk: &[OrientedEdge],
    ) -> Result<GroupElement, StructureGroupRefusal> {
        let element = self.holonomy(walk)?;
        self.group
            .conjugacy_class(&element)
            .ok_or(StructureGroupRefusal::ProductLeftTheCarrier)
    }

    /// Read one declared cycle at every reading this organ carries.
    pub fn read_cycle(
        &self,
        walk: &[OrientedEdge],
        derived: &BTreeSet<GroupElement>,
    ) -> Result<CycleReturn, StructureGroupRefusal> {
        let holonomy = self.holonomy(walk)?;
        let class = self
            .group
            .conjugacy_class(&holonomy)
            .ok_or(StructureGroupRefusal::ProductLeftTheCarrier)?;
        let abelianized = self
            .group
            .abelianized_class(&holonomy, derived)
            .ok_or(StructureGroupRefusal::ProductLeftTheCarrier)?;
        Ok(CycleReturn {
            is_trivial: holonomy.is_identity(),
            holonomy,
            class,
            abelianized,
        })
    }

    /// **The curvature `a ∧ a`, as a return rather than a flag.**
    ///
    /// The commutator of two cycles' holonomies. In an abelian group this is the identity for every
    /// pair, which is precisely why an integer-valued curvature cannot carry it. A non-identity
    /// return says the two transports disagree **by this element, in this direction** — where the
    /// body's `OPEN` disposition currently says only *that* they disagree.
    pub fn curvature_commutator(
        &self,
        left: &[OrientedEdge],
        right: &[OrientedEdge],
    ) -> Result<GroupElement, StructureGroupRefusal> {
        let a = self.holonomy(left)?;
        let b = self.holonomy(right)?;
        self.group
            .commutator(&a, &b)
            .ok_or(StructureGroupRefusal::ProductLeftTheCarrier)
    }

    /// **The falsifier.** The declared cycles that the abelianization identifies and the group
    /// separates — the population an integer holonomy collapses.
    ///
    /// This is `receiver_exact_compression`'s exact loss at the altitude of a structure group: the
    /// collapsed pairs, exhibited, each carrying both readings. **Empty on an abelian group by
    /// construction**, which is the control that proves the instrument is measuring the group and
    /// not itself.
    pub fn separating_pairs(
        &self,
        cycles: &[Vec<OrientedEdge>],
        derived: &BTreeSet<GroupElement>,
    ) -> Result<Vec<SeparatedPair>, StructureGroupRefusal> {
        let readings: Vec<CycleReturn> = cycles
            .iter()
            .map(|cycle| self.read_cycle(cycle, derived))
            .collect::<Result<_, _>>()?;
        let mut separated = Vec::new();
        for left in 0..readings.len() {
            for right in (left + 1)..readings.len() {
                if readings[left].abelianized == readings[right].abelianized
                    && readings[left].class != readings[right].class
                {
                    separated.push(SeparatedPair {
                        left,
                        right,
                        shared_abelianized: readings[left].abelianized.clone(),
                        left_class: readings[left].class.clone(),
                        right_class: readings[right].class.clone(),
                    });
                }
            }
        }
        Ok(separated)
    }

    /// Every declared cycle returns the identity.
    pub fn is_flat_on(&self, cycles: &[Vec<OrientedEdge>]) -> Result<bool, StructureGroupRefusal> {
        for cycle in cycles {
            if !self.holonomy(cycle)?.is_identity() {
                return Ok(false);
            }
        }
        Ok(true)
    }
}

// -------------------------------------------------------------------------------------------------
// The double cover — spin-1/2 as a computed return
// -------------------------------------------------------------------------------------------------

/// What a cycle did when lifted through a central double cover.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Lift {
    /// It closed above as well as below.
    Closed,
    /// **It closed below and returned the central element above.** A `2π` turn that comes back
    /// carrying `−1`. Traversing it twice closes, because `z² = e`.
    ReturnsCentre,
    /// It did not close below either, so the question was not asked.
    DidNotCloseBelow,
}

/// A double cover `π : G̃ → G` with central kernel `{e, z}`.
///
/// **This is where a sign stops being a state.** `CLAUDE.md` §2b: *"there is no separate species of
/// quantity called negative; there is rotation, and `−1` is the half-turn"*, and `√x = x^{2^{-1}}`
/// because squaring erases exactly the turn the `±` would have named. Here `z` **is** that half-turn,
/// as a group element, and a loop that returns it has kept a turn the base group deleted.
///
/// The smallest exact instance is `Q_8 → Q_8/{±1} ≅ V_4`, carried in integer quaternions with `z =
/// −1`. No irrationality, no float, no continuum.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct CentralDoubleCover {
    total: StructureGroup,
    centre: GroupElement,
}

impl CentralDoubleCover {
    /// Declare the cover. Refuses unless `z ≠ e`, `z² = e`, and `z` commutes with everything —
    /// **checked over the whole group, not asserted.**
    pub fn declare(
        total: StructureGroup,
        centre: GroupElement,
    ) -> Result<Self, StructureGroupRefusal> {
        if !total.contains(&centre) || centre.is_identity() {
            return Err(StructureGroupRefusal::CentreIsNotAnInvolution);
        }
        let squared = centre
            .then(&centre)
            .ok_or(StructureGroupRefusal::ProductLeftTheCarrier)?;
        if !squared.is_identity() {
            return Err(StructureGroupRefusal::CentreIsNotAnInvolution);
        }
        for element in total.elements() {
            if element.then(&centre) != centre.then(element) {
                return Err(StructureGroupRefusal::CentreIsNotAnInvolution);
            }
        }
        let kernel = BTreeSet::from([total.identity().clone(), centre.clone()]);
        if kernel.len() != 2 {
            return Err(StructureGroupRefusal::CoverIsNotDouble {
                kernel_order: kernel.len(),
            });
        }
        Ok(Self { total, centre })
    }

    pub fn total(&self) -> &StructureGroup {
        &self.total
    }

    pub fn centre(&self) -> &GroupElement {
        &self.centre
    }

    /// The base group's element that `above` projects to, named by the least member of its coset
    /// `{g, gz}`. This is `π`.
    pub fn project(&self, above: &GroupElement) -> Option<GroupElement> {
        let partner = above.then(&self.centre)?;
        Some(above.clone().min(partner))
    }

    /// **The return this whole organ was built for.**
    ///
    /// Take a cycle's holonomy in the cover. Project it. If it closes below — the projection is the
    /// base identity's coset — then ask whether it closed **above**. A loop that closes below and
    /// returns `z` above is a `2π` rotation that came back with a sign, and traversing it twice
    /// closes.
    pub fn lift(&self, holonomy_above: &GroupElement) -> Result<Lift, StructureGroupRefusal> {
        let identity = self.total.identity();
        let below_identity = self
            .project(identity)
            .ok_or(StructureGroupRefusal::ProductLeftTheCarrier)?;
        let projected = self
            .project(holonomy_above)
            .ok_or(StructureGroupRefusal::ProductLeftTheCarrier)?;
        if projected != below_identity {
            return Ok(Lift::DidNotCloseBelow);
        }
        if holonomy_above.is_identity() {
            Ok(Lift::Closed)
        } else {
            Ok(Lift::ReturnsCentre)
        }
    }
}

// -------------------------------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    /// `A_5`, from the generators `arithmetic_monodromy` already declares as material for the
    /// alternating quintic group: a 5-cycle and a 3-cycle.
    fn alternating_five() -> StructureGroup {
        StructureGroup::close(
            [
                GroupElement::Permutation(vec![1, 2, 3, 4, 0]),
                GroupElement::Permutation(vec![1, 2, 0, 3, 4]),
            ],
            60,
        )
        .expect("A_5 closes")
    }

    /// `Q_8`, the eight unit Lipschitz quaternions, from `i` and `j`.
    fn quaternion_eight() -> StructureGroup {
        StructureGroup::close(
            [
                GroupElement::Quaternion([0, 1, 0, 0]),
                GroupElement::Quaternion([0, 0, 1, 0]),
            ],
            8,
        )
        .expect("Q_8 closes")
    }

    /// `ℤ/5`, the abelian control.
    fn cyclic_five() -> StructureGroup {
        StructureGroup::close([GroupElement::Permutation(vec![1, 2, 3, 4, 0])], 5)
            .expect("Z/5 closes")
    }

    #[test]
    fn the_declared_generators_close_to_the_orders_the_mathematics_says() {
        assert_eq!(alternating_five().order(), 60);
        assert_eq!(quaternion_eight().order(), 8);
        assert_eq!(cyclic_five().order(), 5);
    }

    #[test]
    fn abelian_is_measured_not_declared() {
        assert!(!alternating_five().is_abelian());
        assert!(!quaternion_eight().is_abelian());
        assert!(cyclic_five().is_abelian());
    }

    #[test]
    fn the_closure_bound_is_the_callers_and_exceeding_it_names_what_was_reached() {
        match StructureGroup::close(
            [
                GroupElement::Permutation(vec![1, 2, 3, 4, 0]),
                GroupElement::Permutation(vec![1, 2, 0, 3, 4]),
            ],
            12,
        ) {
            Err(StructureGroupRefusal::ClosureExceededDeclaredBound { reached, bound }) => {
                assert_eq!(bound, 12);
                assert!(reached > 12, "the refusal names what it reached");
            }
            other => panic!("a bound below the order must refuse by name, got {other:?}"),
        }
    }

    #[test]
    fn generators_of_different_extent_are_refused_rather_than_padded() {
        assert_eq!(
            StructureGroup::close(
                [
                    GroupElement::Permutation(vec![1, 0]),
                    GroupElement::Permutation(vec![1, 2, 0, 3, 4]),
                ],
                60,
            ),
            Err(StructureGroupRefusal::CarriersDisagree)
        );
    }

    #[test]
    fn a_permutation_and_a_quaternion_do_not_share_a_group() {
        assert_eq!(
            StructureGroup::close(
                [
                    GroupElement::Permutation(vec![1, 0]),
                    GroupElement::Quaternion([0, 1, 0, 0]),
                ],
                8,
            ),
            Err(StructureGroupRefusal::CarriersDisagree)
        );
    }

    #[test]
    fn every_element_has_an_inverse_and_the_group_law_holds_over_the_whole_closure() {
        for group in [alternating_five(), quaternion_eight(), cyclic_five()] {
            for element in group.elements() {
                let inverse = element.inverse().expect("an inverse exists");
                assert!(
                    group.contains(&inverse),
                    "the closure is closed under inverse"
                );
                assert!(
                    element.then(&inverse).expect("composes").is_identity(),
                    "g g^-1 = e"
                );
            }
        }
    }

    /// `A_5` is simple and non-abelian, so `[A_5, A_5] = A_5` and its abelianization is trivial:
    /// **an integer holonomy on an `A_5` connection carries nothing at all.** That is the sharpest
    /// statement of what this organ adds, and it is a theorem rather than a measurement.
    #[test]
    fn the_abelianization_of_a_five_is_trivial_so_an_integer_reading_carries_nothing() {
        let group = alternating_five();
        let derived = group.commutator_subgroup().expect("closes");
        assert_eq!(derived.len(), 60, "A_5 is perfect: [G,G] = G");
        let classes: BTreeSet<GroupElement> = group
            .elements()
            .filter_map(|element| group.abelianized_class(element, &derived))
            .collect();
        assert_eq!(classes.len(), 1, "every element lands in one abelian class");
    }

    #[test]
    fn a_commutator_is_the_identity_exactly_when_the_two_commute() {
        let group = quaternion_eight();
        let i = GroupElement::Quaternion([0, 1, 0, 0]);
        let j = GroupElement::Quaternion([0, 0, 1, 0]);
        let minus_one = GroupElement::Quaternion([-1, 0, 0, 0]);
        assert_eq!(group.commutator(&i, &j), Some(minus_one.clone()));
        assert!(group.commutator(&i, &i).expect("composes").is_identity());
        // ijk = -1, the defining relation, so the carrier is Q_8 and not something that merely has
        // eight elements.
        let k = GroupElement::Quaternion([0, 0, 0, 1]);
        assert_eq!(i.then(&j).and_then(|ij| ij.then(&k)), Some(minus_one));
    }

    /// Two triangles sharing an edge. The connection carries `i` and `j` on the two chords, so the
    /// two loops' holonomies do not commute.
    fn two_loops_over(
        group: StructureGroup,
        left: GroupElement,
        right: GroupElement,
    ) -> (StructureConnection, Vec<Vec<OrientedEdge>>) {
        let connection = StructureConnection::declare(
            group.clone(),
            [(0, left), (1, right), (2, group.identity().clone())],
        )
        .expect("declares");
        let cycles = vec![
            vec![OrientedEdge::forward(0), OrientedEdge::forward(2)],
            vec![OrientedEdge::forward(1), OrientedEdge::forward(2)],
        ];
        (connection, cycles)
    }

    #[test]
    fn the_curvature_commutator_is_non_identity_on_a_non_abelian_connection() {
        let group = quaternion_eight();
        let (connection, cycles) = two_loops_over(
            group,
            GroupElement::Quaternion([0, 1, 0, 0]),
            GroupElement::Quaternion([0, 0, 1, 0]),
        );
        let commutator = connection
            .curvature_commutator(&cycles[0], &cycles[1])
            .expect("composes");
        assert!(!commutator.is_identity(), "a wedge a is not zero here");
        assert_eq!(commutator, GroupElement::Quaternion([-1, 0, 0, 0]));
    }

    /// **The control that must return nothing.** On an abelian group every commutator is the
    /// identity, so the curvature this organ adds is identically trivial and an integer reading
    /// loses nothing. If this ever returned non-identity the instrument would be measuring itself.
    #[test]
    fn the_curvature_commutator_is_always_identity_on_an_abelian_connection() {
        let group = cyclic_five();
        let rotation = GroupElement::Permutation(vec![1, 2, 3, 4, 0]);
        let twice = rotation.then(&rotation).expect("composes");
        let (connection, cycles) = two_loops_over(group, rotation, twice);
        assert!(
            connection
                .curvature_commutator(&cycles[0], &cycles[1])
                .expect("composes")
                .is_identity()
        );
    }

    #[test]
    fn reversing_a_walk_inverts_its_holonomy_and_the_hand_is_not_stored_twice() {
        let group = quaternion_eight();
        let i = GroupElement::Quaternion([0, 1, 0, 0]);
        let connection = StructureConnection::declare(group, [(0, i.clone())]).expect("declares");
        let forward = connection
            .holonomy(&[OrientedEdge::forward(0)])
            .expect("composes");
        let backward = connection
            .holonomy(&[OrientedEdge::backward(0)])
            .expect("composes");
        assert_eq!(backward, i.inverse().expect("inverts"));
        assert!(forward.then(&backward).expect("composes").is_identity());
    }

    /// **The falsifier, on non-abelian material — and the population it returns is the spin pair.**
    ///
    /// An earlier form of this test asked for `i` against `j` and returned **zero**, correctly: in
    /// `Q_8` the abelianization `Q_8 → V_4` is four-to-one onto four classes and separates `i` from
    /// `j` perfectly well. The pair the abelian reading genuinely collapses is `1` against `−1` —
    /// both sit in the derived subgroup, so both abelianize to the identity coset, while their
    /// conjugacy classes `{1}` and `{−1}` are distinct.
    ///
    /// So the two cycles below are **a loop that closed** and **a loop that came back with a
    /// half-turn**, and the integer reading cannot tell them apart. `CLAUDE.md` §2b is the whole
    /// content: *a float keeps the magnitude and discards the residual; a sign keeps the magnitude
    /// and discards the turn.* An abelianized holonomy discards exactly this turn, and here that
    /// discarded population is exhibited rather than argued.
    #[test]
    fn the_group_separates_the_loop_that_closed_from_the_loop_that_came_back_with_a_half_turn() {
        let group = quaternion_eight();
        let derived = group.commutator_subgroup().expect("closes");
        assert_eq!(derived.len(), 2, "[Q_8, Q_8] = {{1, -1}}");
        let connection = StructureConnection::declare(
            group.clone(),
            [(0, GroupElement::Quaternion([0, 1, 0, 0]))],
        )
        .expect("declares");
        let cycles = vec![
            // out and back: closes, carrying nothing
            vec![OrientedEdge::forward(0), OrientedEdge::backward(0)],
            // twice around: closes below, returns -1
            vec![OrientedEdge::forward(0), OrientedEdge::forward(0)],
        ];
        let readings: Vec<CycleReturn> = cycles
            .iter()
            .map(|cycle| connection.read_cycle(cycle, &derived).expect("reads"))
            .collect();
        assert!(readings[0].is_trivial);
        assert!(!readings[1].is_trivial);
        assert_eq!(
            readings[1].holonomy,
            GroupElement::Quaternion([-1, 0, 0, 0])
        );

        let separated = connection
            .separating_pairs(&cycles, &derived)
            .expect("reads");
        assert_eq!(separated.len(), 1, "the two cycles are one collapsed pair");
        assert_eq!(
            separated[0].shared_abelianized, readings[0].abelianized,
            "the abelian reading calls both of them the trivial loop"
        );
        assert_ne!(
            separated[0].left_class, separated[0].right_class,
            "and the group says one of them came back with a sign"
        );

        // And the same two cycles at the cover: closed, against returning the centre.
        let cover = CentralDoubleCover::declare(group, GroupElement::Quaternion([-1, 0, 0, 0]))
            .expect("declares");
        assert_eq!(
            cover.lift(&readings[0].holonomy).expect("lifts"),
            Lift::Closed
        );
        assert_eq!(
            cover.lift(&readings[1].holonomy).expect("lifts"),
            Lift::ReturnsCentre
        );
    }

    /// **The control.** On an abelian group the two readings agree by construction, so the separated
    /// population is empty. A gauge whose group acts trivially on the declared material is not a
    /// gauge (`CLAUDE.md` §8), and this is the direction that proves the test above is not vacuous.
    #[test]
    fn an_abelian_group_separates_nothing_because_there_is_nothing_to_separate() {
        let group = cyclic_five();
        let derived = group.commutator_subgroup().expect("closes");
        assert_eq!(
            derived.len(),
            1,
            "an abelian group has trivial derived subgroup"
        );
        let rotation = GroupElement::Permutation(vec![1, 2, 3, 4, 0]);
        let connection = StructureConnection::declare(
            group,
            [
                (0, rotation.clone()),
                (1, rotation.then(&rotation).expect("composes")),
            ],
        )
        .expect("declares");
        let cycles = vec![
            vec![OrientedEdge::forward(0)],
            vec![OrientedEdge::forward(1)],
        ];
        assert!(
            connection
                .separating_pairs(&cycles, &derived)
                .expect("reads")
                .is_empty()
        );
    }

    #[test]
    fn a_centre_that_is_not_an_involution_is_refused() {
        let group = quaternion_eight();
        assert_eq!(
            CentralDoubleCover::declare(group.clone(), group.identity().clone()),
            Err(StructureGroupRefusal::CentreIsNotAnInvolution)
        );
        // `i` has order four, not two.
        assert_eq!(
            CentralDoubleCover::declare(group, GroupElement::Quaternion([0, 1, 0, 0])),
            Err(StructureGroupRefusal::CentreIsNotAnInvolution)
        );
    }

    /// **Spin-½, computed.** `Q_8 → Q_8/{±1} ≅ V_4`. A loop carrying `i` closes below — `i` and `−i`
    /// are one coset — and returns `−1` above. Traversing it twice closes, because `z² = e`.
    ///
    /// That is `2π` returning a sign and `4π` returning identity, as a group computation with no
    /// continuum, no float, and no rotation matrix anywhere.
    #[test]
    fn a_loop_closes_below_and_returns_the_centre_above() {
        let cover = CentralDoubleCover::declare(
            quaternion_eight(),
            GroupElement::Quaternion([-1, 0, 0, 0]),
        )
        .expect("declares");
        let i = GroupElement::Quaternion([0, 1, 0, 0]);
        let once = i.clone();
        let twice = i.then(&i).expect("composes");
        let four_times = twice.then(&twice).expect("composes");

        // One turn does not close below.
        assert_eq!(cover.lift(&once).expect("lifts"), Lift::DidNotCloseBelow);
        // Two turns close below and return the centre: the 2*pi sign.
        assert_eq!(cover.lift(&twice).expect("lifts"), Lift::ReturnsCentre);
        assert_eq!(twice, *cover.centre());
        // Four turns close above as well: 4*pi returns identity.
        assert_eq!(cover.lift(&four_times).expect("lifts"), Lift::Closed);
        assert!(four_times.is_identity());
    }

    /// The projection is two-to-one and its fibres are exactly `{g, gz}`.
    #[test]
    fn the_cover_is_two_to_one_over_its_base() {
        let cover = CentralDoubleCover::declare(
            quaternion_eight(),
            GroupElement::Quaternion([-1, 0, 0, 0]),
        )
        .expect("declares");
        let below: BTreeSet<GroupElement> = cover
            .total()
            .elements()
            .filter_map(|element| cover.project(element))
            .collect();
        assert_eq!(cover.total().order(), 8);
        assert_eq!(
            below.len(),
            4,
            "Q_8 / {{+-1}} has order four — the Klein group"
        );
    }

    /// The conjugacy class does not move when the loop is re-based, and the raw holonomy does.
    /// **That is why the class is the invariant and the element is the frame-relative reading.**
    #[test]
    fn the_class_is_basepoint_free_where_the_element_is_not() {
        let group = quaternion_eight();
        let i = GroupElement::Quaternion([0, 1, 0, 0]);
        let j = GroupElement::Quaternion([0, 0, 1, 0]);
        let rebased = j
            .then(&i)
            .and_then(|left| left.then(&j.inverse().expect("inverts")))
            .expect("composes");
        assert_ne!(rebased, i, "conjugating moved the element");
        assert_eq!(
            group.conjugacy_class(&rebased),
            group.conjugacy_class(&i),
            "and left the class alone"
        );
    }
}

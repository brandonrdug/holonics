import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import ElementaryHolonics.Millennium.Gluing
import ElementaryHolonics.Millennium.Turn

/-!
# The coupling — the remainders are positions on one chain, and a sectioning is a choice

The previous record asked whether four remainders were one object or four.  **That was the wrong
question.**  They are distinct and they are coupled, and the object that couples them is a chain.

**Section 1.**  A two-step transport whose composite vanishes has *five* named positions: what the
incoming transport collapses, what it realizes, what the outgoing transport retains, the quotient
between those two, and what the outgoing transport fails to reach.  **The theorem is that a chain
is an additive passage** — its realized population sits inside its retained one by the composite
law alone — and therefore its obstruction group is its homology.  (That gluing *coincides* with
exactness is definitional, since `toPassage` lines the two vocabularies up on purpose; the content
is `realized_le_retained`.)

So the collapse at the source and the obstruction at the middle are not rival objects.  They are
two positions of one chain, and the homology is what neither reaches nor collapses.

**Section 2.**  How many remainders one names is a **sectioning of the receiver**, and a sectioning
is free.  What is not free is which sectionings return rational values.  Quadrants do; octets do
not, and the first value past the quadrant is the half power.  The two first refusals of the
rational table are the golden reciprocal at five and the half power at eight.

Every `theorem` here is discharged.
-/

namespace Soma.Holonics.Millennium.Coupling

open Soma.Holonics.Millennium

universe u

/-! ## 1. A chain has five positions, and the composite law makes it a passage -/

variable {A B C : Type u} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]

/-- A **two-step transport chain**: material arrives, is carried on, and the composite returns
nothing.  The vanishing composite is the whole hypothesis. -/
structure TransportChain (A B C : Type u) [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] where
  /-- What arrives. -/
  into : A →+ B
  /-- What is carried on. -/
  outOf : B →+ C
  /-- The composite returns nothing. -/
  composite_zero : ∀ a : A, outOf (into a) = 0

namespace TransportChain

variable (T : TransportChain A B C)

/-- **What the incoming transport collapses** — the population it cannot distinguish. -/
def collapsed : AddSubgroup A := T.into.ker

/-- **What the incoming transport realizes** — the population it pays for. -/
def realized : AddSubgroup B := T.into.range

/-- **What the outgoing transport retains** — the population it cannot see past. -/
def retained : AddSubgroup B := T.outOf.ker

/-- **The composite law alone puts the realized inside the retained.**  Nothing else is assumed,
and this is what makes a chain a passage. -/
theorem realized_le_retained : T.realized ≤ T.retained := by
  rintro b hb
  obtain ⟨a, rfl⟩ := hb
  exact T.composite_zero a

/-- **A transport chain is an additive passage.**

Local admissibility is what the outgoing transport retains; realization is what the incoming one
supplies; and the containment is free.  So every chain carries an obstruction group, and it is the
homology at the middle. -/
def toPassage : AdditivePassage where
  Candidate := B
  Realized := T.realized
  LocallyAdmissible := T.retained
  realized_le := T.realized_le_retained

/-- Gluing coincides with exactness at the middle.

**DEFINITIONAL — `Iff.rfl`.**  `toPassage` was constructed with `Realized := realized` and
`LocallyAdmissible := retained`, so this records that the two vocabularies were lined up on
purpose; it is a naming fact and not a finding.  **The content is `realized_le_retained`**, which
is proved from the vanishing composite and is what makes the passage exist at all. -/
theorem theChainGluesIffItIsExactAtTheMiddle :
    T.toPassage.Glues ↔ T.retained ≤ T.realized := Iff.rfl

/-- **And therefore the coupling remainder is the homology.**

The obstruction group of the passage — what is locally admissible and unrealized — is the quotient
of what the outgoing transport retains by what the incoming one realized. That quotient is the
homology at the middle, and it vanishes exactly when the chain glues. -/
theorem theCouplingRemainderIsTheHomology :
    T.toPassage.Glues ↔ Subsingleton T.toPassage.ObstructionGroup :=
  AdditivePassage.glues_iff_obstruction_subsingleton _

/-- **What the incoming transport collapses reaches nothing downstream.**  The source-side
remainder and the middle obstruction are different positions and neither is the other. -/
theorem theCollapsedPopulationSuppliesNothing {a : A} (ha : a ∈ T.collapsed) : T.into a = 0 := ha

/-- **A collapsed element is realized only as zero**, so the collapse is exactly the failure of the
incoming transport to be a faithful supply. -/
theorem theCollapseIsTheFailureToSupplyFaithfully :
    (∀ a : A, a ∈ T.collapsed → a = 0) ↔ Function.Injective T.into :=
  ⟨fun h => (AddMonoidHom.ker_eq_bot_iff T.into).mp
      (AddSubgroup.eq_bot_iff_forall _ |>.mpr h),
   fun h a ha => by
     apply h
     change T.into a = 0 at ha
     simpa using ha⟩

/-- **A chain whose incoming transport is onto its retained population glues.**  The converse of
the containment, stated so the gluing condition has a supply-side reading as well as a quotient
one. -/
theorem theOntoSupplyGlues (h : T.retained ≤ T.realized) : T.toPassage.Glues := h

end TransportChain

/-! ## 2. A sectioning of the receiver is free; which sectionings are rational is not

How many parts one divides a turn into is a receiver's choice.  Four parts give quadrants; eight
give octets; nothing forbids either.  What is *not* free is the value the sectioning returns: only
five orders return a rational, and the first two refusals are the golden reciprocal and the half
power. -/

/-- The value a **sectioning of the turn into `n` parts** returns.

*Aside: `2cos(2π/n)`, the circulant eigenvalue at the first step of the `n`-cycle.* -/
noncomputable def sectionValue (n : ℕ) : ℝ := 2 * Real.cos (2 * Real.pi / n)

/-- **The whole sectioning returns two.** -/
theorem theWholeSectioningIsTwo : sectionValue 1 = 2 := by
  simp [sectionValue]

/-- **The half sectioning returns minus two.** -/
theorem theHalfSectioningIsMinusTwo : sectionValue 2 = -2 := by
  rw [sectionValue]
  norm_num

/-- **The third sectioning returns minus one.** -/
theorem theThirdSectioningIsMinusOne : sectionValue 3 = -1 := by
  rw [sectionValue, show (2 : ℝ) * Real.pi / (3 : ℕ) = Real.pi - Real.pi / 3 by push_cast; ring,
    Real.cos_pi_sub, Real.cos_pi_div_three]
  norm_num

/-- **The quadrant sectioning returns nothing at all: the value is flat.**

Four is where the two axes cross, and the crossing returns zero — which is why a quadrant
decomposition costs nothing and can always be taken. -/
theorem theQuadrantSectioningIsFlat : sectionValue 4 = 0 := by
  rw [sectionValue, show (2 : ℝ) * Real.pi / (4 : ℕ) = Real.pi / 2 by push_cast; ring,
    Real.cos_pi_div_two]
  norm_num

/-- **The sixth sectioning returns one.**  With the four above this is the whole rational table. -/
theorem theSixthSectioningIsOne : sectionValue 6 = 1 := by
  rw [sectionValue, show (2 : ℝ) * Real.pi / (6 : ℕ) = Real.pi / 3 by push_cast; ring,
    Real.cos_pi_div_three]
  norm_num

/-- **The fifth sectioning returns the golden reciprocal** — the first refusal of the rational
table, in the odd direction. -/
theorem theFifthSectioningIsTheGoldenReciprocal :
    sectionValue 5 = (Real.sqrt 5 - 1) / 2 := by
  rw [sectionValue, show (2 : ℝ) * Real.pi / (5 : ℕ) = 2 * Real.pi / 5 by push_cast; ring]
  exact Turn.theDoubledFifthTurnIsTheOtherRoot

/-- **The octet sectioning returns the half power** — the first refusal in the even direction.

Halving the quadrant is the first sectioning whose value leaves the rationals, and what it lands on
is exactly `2^{1/2}`.  So an octet is not an arbitrary finer division: it is the first one that
costs an irrationality, and the irrationality it costs is the half exponent. -/
theorem theOctetSectioningIsTheHalfPower : sectionValue 8 = Real.sqrt 2 := by
  rw [sectionValue, show (2 : ℝ) * Real.pi / (8 : ℕ) = Real.pi / 4 by push_cast; ring,
    Real.cos_pi_div_four]
  rw [mul_div_assoc']
  rw [mul_comm]
  rw [mul_div_assoc]
  norm_num

/-- **The octet value squares to the whole sectioning's value.**  `(2^{1/2})² = 2`: the octet is
the square root of the whole turn's return, which is what halving a turn means in this coordinate. -/
theorem theOctetValueSquaresToTheWhole : sectionValue 8 ^ 2 = sectionValue 1 := by
  rw [theOctetSectioningIsTheHalfPower, theWholeSectioningIsTwo]
  exact Real.sq_sqrt (by norm_num)

end Soma.Holonics.Millennium.Coupling

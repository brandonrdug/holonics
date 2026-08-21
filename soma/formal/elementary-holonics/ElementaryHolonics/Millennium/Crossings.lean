import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.Tactic
import ElementaryHolonics.Millennium.Lines

/-!
# Crossings — the net is not the population, and the helicity reading is blind to the nonlinearity

Two exact readings of one pairing, and a finite crossing population that separates a net from
the thing it is a net *of*.

**What is proved here.**

* **The two faces are exact complements.**  Over any commutative ring, `(u ⬝ w)² + |u ⨯ w|² =
  |u|²|w|²` — Lagrange's identity, taken from mathlib's `cross_dot_cross`.  Read on a velocity
  and its curl, the first term is the helicity density and the second is the squared Lamb vector,
  which *is* the nonlinearity of the flow equation.  So a receiver reading only the helicity
  density is reading the cosine face of a pairing whose sine face carries the transport, and the
  blindness is exhibited: a declared one-reading family of the helicity density does not separate
  a pair on which the Lamb vector vanishes from one on which it does not, so by
  `Lines.ReceiverFamily.blindFamilyCarriesNoVerdict` no function whatsoever of that reading
  decides whether the nonlinearity is present.  The degenerate locus is exhibited too (the
  Beltrami witness `u = w = (1,2,3)`: Lamb vector zero, complementarity saturated).
* **The stretching term is a commutator, and its vanishing in the planar case is exact.**  For
  linear fields the bracket is the matrix commutator; and for any velocity gradient with a zero
  third column — the exact algebraic content of "the velocity does not depend on the third
  coordinate" — the stretching of a vorticity along the third axis is identically zero, with a
  witness showing it is not zero once the column is not.  That is the planar/spatial split of the
  named line, stated as an identity rather than as a slogan.
* **The two arms of a signed crossing population, and the classical inequality between them.**
  `net` is the difference of the two arms, `total` their sum, `|net| ≤ total` always, and equality
  holds *exactly* when one arm is empty.  The gap is cancellation, exhibited by address.
* **The net carries no verdict about whether anything crossed.**  A cancelling pair and the empty
  population agree on every reading of the net family and of the pairwise-linking family, and
  differ in whether the population is inhabited.  On three strands the witness is the standard
  Borromean crossing table: six crossings, every pairwise linking reading zero.
* **The declared hands can fail, and the control shows it.**  Flipping one hand in that table
  makes the linking family separate it from the empty table — so the vanishing above is a
  consequence of the declared data and not a restatement of it.
* **What ratchets and what does not.**  A reconnection sequence takes the table `6 → 4 → 2 → 0`
  while every one of the nine linking readings stands at zero throughout; and the cancelling-pair
  insertion — the representational move — takes it `6 → 8` while every reading again stands
  still.  So the population is monotone under the declared physical move family and provably
  **not** invariant under the representational one.  The second is the control: without it the
  first is a receipt that could not have come out otherwise.
* **A reconnection retains its remainder exactly.**  Removing the crossing at a site and keeping
  it as the remainder preserves both arms: totals add and nets add.  This is a partition identity
  and is stated as one; the content is that the discarded branch is retained by address rather
  than deleted.

**What is refused, and this is the boundary.**  Nothing here is a claim about the Navier–Stokes
existence and smoothness question, and nothing here moves the row `Lines.theLines` records for it
(`obstructionGroupKnown := false`).  In particular:

* No fluid appears.  Sections on the pairing and the stretching term are pointwise algebra over
  `ℚ` on `Fin 3 → ℚ`; there is no measure, no derivative, no solution, and no time.  The scaling
  section is exponent bookkeeping only: the change of variables that produces those exponents is
  imported and not proved here.
* **No link appears either.**  The crossing population is a finite table of addressed signed
  crossings.  This file builds no planar diagram and therefore no Reidemeister move, so every
  blindness theorem below is a statement about *diagrams*, not about links.  The reading that
  would survive ambient isotopy and still separate the Borromean table from the empty one is
  recorded as a demand — `ATangleReadingSeparatesWhatTheLinkingNumbersCannot` — parameterized by
  an isotopy relation this file does not construct.  Classically that demand is met (Milnor 1954's
  μ̄₁₂₃ = ±1 for the Borromean rings, and the Jones polynomial of L6a4); it is not met here.
  Making the population invariant costs a minimization or a limit, and this file supplies neither.
* **The primary falsifier of the reading that occasioned this file is not addressed here and
  cannot be, at this grain.**  It is: an averaged bilinear operator satisfying *both* the energy
  cancellation Tao's construction requires (Tao 2016, JAMS 29, whose abstract imposes only
  `⟨B(u,u),u⟩ = 0`, "which is equivalent to the energy identity") *and* a vortex-transport
  cancellation — helicity conservation, Kelvin circulation on material loops, or frozen-in
  transport — while still admitting finite-time blowup.  If such an averaging exists, the
  population reading is blind exactly where the energy reading is.  Stating that requires the
  analytic apparatus; it is recorded as prose, not as a `Prop`, because a `Prop` that abstracts
  it far enough to typecheck would be satisfiable for reasons having nothing to do with fluids.
* Two further concessions, carried because they are unanswered rather than because they are
  small.  Every population-to-energy result in the literature (Arnold 1974; Freedman–He 1991,
  Annals 134(1); Komendarczyk) is a *lower* bound on energy, while regularity needs upper bounds
  on critical norms — and the leading blowup scenarios are topologically trivial, so a crossing
  population returns zero on exactly the candidates that matter.  And in Waleffe's helical chart
  (1992) the natural "population" refinement of helicity is twice the energy, so a population
  proposed in that chart is the supercritical magnitude under another name.

**Classical results cited in prose and used nowhere in a proof:** Lagrange's identity (mathlib,
`cross_dot_cross`); Călugăreanu–White–Fuller and Moffatt–Ricca 1992 (helicity of a vortex tube is
writhe plus twist, so the net is a signed crossing sum and the average crossing number is the
unsigned one, with `|Wr| ≤ ACN`); Milnor 1954 and Mellor–Melvin 2003 (the triple linking number as
a signed diagrammatic count); Constantin–Fefferman 1993 (a regularity criterion carried entirely
by the vorticity *direction*); Beale–Kato–Majda 1984; Tao 2016.

**Measured 2026-08-21** over `Mathlib` at `v4.27.0`, manifest rev `a3a10db0e9`, under
`soma/formal/elementary-holonics/.lake/packages/mathlib`: `grep -rli "linking number" Mathlib
--include='*.lean'` → 0 files; `grep -rliE "jones polynomial|kauffman" Mathlib --include='*.lean'`
→ 0 files; `grep -rliE "helicity|vorticity|navier" Mathlib --include='*.lean'` → 0 files.  Those
commands measure those names over that scope and are not a claim that no related content exists
under another name; every crossing-theoretic object below is built here from a finite carrier
because of them.  The Rust side of the same gap is recorded in `canon/TABLET_THE_TURN.md` §13.3 —
*"Nothing converts a crossing into a `Substitution`"* — and is untouched by this file, which is
Lean only and edits nothing outside itself.

Every `theorem` is discharged and none depends on `sorryAx`.  This file does not claim, and may
not be cited as, movement on the Navier–Stokes line or on any other named question; what it
contains is exact algebra on `ℚ` and exact combinatorics on a finite table.
-/

namespace Soma.Holonics.Millennium.Crossings

open Matrix

/-! ## 1. The two faces of one pairing

`u ⬝ᵥ w` and `u ⨯₃ w` are the cosine and sine faces of the same pairing, and Lagrange's identity
says they are exact complements.  Read on a velocity and its curl, the first is the helicity
density and the second is the Lamb vector — the nonlinearity itself. -/

/-- **The two faces are complementary.**

`(u ⬝ w)² + |u ⨯ w|² = |u|²|w|²`, over `ℚ`.  One line from mathlib's `cross_dot_cross`, which
holds over any commutative ring; the specialization to `ℚ` is the carrier this file uses
everywhere else.

Nothing about a fluid is asserted: `u` and `w` are two vectors, and the reading that calls the
first term a helicity density and the second a squared Lamb vector is exterior to the theorem. -/
theorem theTwoFacesAreComplementary (u w : Fin 3 → ℚ) :
    (u ⬝ᵥ w) ^ 2 + (u ⨯₃ w) ⬝ᵥ (u ⨯₃ w) = (u ⬝ᵥ u) * (w ⬝ᵥ w) := by
  have h := cross_dot_cross u w u w
  have hc : w ⬝ᵥ u = u ⬝ᵥ w := dotProduct_comm w u
  rw [h, hc]
  ring

/-- **The Beltrami witness kills the sine face.**

`u = w = (1,2,3)`: the cross product is zero, the dot product is `14`, and the complementarity of
the previous theorem saturates at `196 = 196`.  This is the degenerate locus — the alignment at
which the Lamb vector vanishes and the pairing is carried entirely by the cosine face — exhibited
rather than described. -/
theorem theBeltramiWitnessKillsTheSineFace :
    (![1, 2, 3] : Fin 3 → ℚ) ⨯₃ ![1, 2, 3] = 0 ∧
      (![1, 2, 3] : Fin 3 → ℚ) ⬝ᵥ ![1, 2, 3] = 14 := by
  constructor
  · funext i
    fin_cases i <;> simp
  · simp [dotProduct, Fin.sum_univ_three]
    norm_num

/-- The declared helicity-density family: one reading of a pair of vectors, their dot product. -/
def helicityDensityFamily : Lines.ReceiverFamily ((Fin 3 → ℚ) × (Fin 3 → ℚ)) ℚ where
  Index := Unit
  read := fun _ p => p.1 ⬝ᵥ p.2

/-- **The helicity-density family is blind to the sine face.**

`((1,0,0),(1,0,0))` and `((1,0,0),(1,1,0))` have the same dot product, `1`.  The first has cross
product zero and the second does not.  So the declared reading does not separate the pair that the
vanishing of the sine face distinguishes. -/
theorem theHelicityDensityFamilyIsBlindToTheSineFace :
    helicityDensityFamily.Blind (fun p => p.1 ⨯₃ p.2 = 0) := by
  refine ⟨(![1, 0, 0], ![1, 0, 0]), (![1, 0, 0], ![1, 1, 0]), ?_, ?_, ?_⟩
  · funext i
    fin_cases i <;> simp
  · intro h
    have h2 : ((![1, 0, 0] : Fin 3 → ℚ) ⨯₃ ![1, 1, 0]) 2 = 0 := by rw [h]; rfl
    simp [cross_apply] at h2
  · intro _
    simp [helicityDensityFamily, dotProduct, Fin.sum_univ_three]

/-- **Therefore the helicity density carries no verdict about the nonlinearity.**

The abstract barrier theorem of `Lines`, applied to the witness above: no function whatsoever of
the helicity-density reading decides whether the Lamb vector vanishes.  The obstruction is the
aperture, not the difficulty — and the Lamb vector is the term that drives the flow. -/
theorem theHelicityDensityCarriesNoVerdictAboutTheSineFace :
    ¬ ∃ verdict : (helicityDensityFamily.Index → ℚ) → Prop,
        ∀ p : (Fin 3 → ℚ) × (Fin 3 → ℚ),
          p.1 ⨯₃ p.2 = 0 ↔ verdict (fun i => helicityDensityFamily.read i p) :=
  helicityDensityFamily.blindFamilyCarriesNoVerdict _ theHelicityDensityFamilyIsBlindToTheSineFace

/-! ## 2. The stretching term is a commutator, and the planar case is exactly its vanishing

For vector fields `X` and `Y`, `(X·∇)Y − (Y·∇)X` is the Lie bracket.  For *linear* fields
`X x = A x` and `Y x = B x` it is the matrix commutator, and the whole of the planar/spatial split
of the named line is that in the planar case one half of it vanishes identically.

`Chronology.orderBlind_iff_commute` is the general form: a chronology exists exactly when the
transports fail to commute. -/

/-- **The bracket of two linear fields is the matrix commutator.**

`[A·, B·] x = (B A − A B) x`, with the convention `[X,Y] = (X·∇)Y − (Y·∇)X`. -/
theorem theStretchingIsTheMatrixCommutator (A B : Matrix (Fin 3) (Fin 3) ℚ) (x : Fin 3 → ℚ) :
    B *ᵥ (A *ᵥ x) - A *ᵥ (B *ᵥ x) = (B * A - A * B) *ᵥ x := by
  simp [Matrix.sub_mulVec]

/-- **Commuting fields carry no bracket.**  The control on the theorem above: when the two
transports commute the whole term is zero, so it is non-commutation and nothing else that puts a
stretching term into the equation. -/
theorem theCommutingFieldsCarryNoBracket (A B : Matrix (Fin 3) (Fin 3) ℚ) (h : A * B = B * A)
    (x : Fin 3 → ℚ) : B *ᵥ (A *ᵥ x) - A *ᵥ (B *ᵥ x) = 0 := by
  rw [theStretchingIsTheMatrixCommutator, h, sub_self, Matrix.zero_mulVec]

/-- The stretching term `(w·∇)u`, written as the velocity gradient applied to the vorticity:
`(Du) w`, where `(Du) i j = ∂_j u_i`. -/
def stretching (Du : Matrix (Fin 3) (Fin 3) ℚ) (w : Fin 3 → ℚ) : Fin 3 → ℚ := Du *ᵥ w

/-- **The planar case has no stretching, exactly.**

A velocity that does not depend on the third coordinate has a velocity gradient whose third column
is zero; a planar vorticity points along the third axis.  Then the stretching term vanishes
identically, for every gradient with that column and every strength `c`.  No estimate and no
smallness: an identity. -/
theorem thePlanarCaseHasNoStretching (Du : Matrix (Fin 3) (Fin 3) ℚ)
    (h : ∀ i, Du i 2 = 0) (c : ℚ) : stretching Du ![0, 0, c] = 0 := by
  funext i
  simp [stretching, Matrix.mulVec, dotProduct, Fin.sum_univ_three, h i]

/-- **And the spatial case does not.**

One velocity gradient whose third column is not zero, and the same vorticity direction: the
stretching term is `(1,0,0)`.  Without this witness the theorem above would be compatible with the
term vanishing always, which is the shape of a check that cannot fail. -/
theorem theSpatialWitnessStretches :
    stretching (Matrix.of ![![0, 0, 1], ![0, 0, 0], ![0, 0, 0]]) ![0, 0, 1] ≠ 0 := by
  intro h
  have h0 : stretching (Matrix.of ![![0, 0, 1], ![0, 0, 0], ![0, 0, 0]]) ![0, 0, (1 : ℚ)] 0 = 0 := by
    rw [h]; rfl
  simp [stretching, Matrix.mulVec, dotProduct, Fin.sum_univ_three] at h0

/-! ## 3. The exponent bookkeeping of the scaling

Under `u_λ(x,t) = λ u(λx, λ²t)` the vorticity carries one power more than the velocity, because a
gradient carries one.  Integrating a density of homogeneity `d` over three spatial dimensions
subtracts three.  Everything in this section is integer arithmetic on those weights; the change of
variables that produces them is imported and is not proved here. -/

/-- The velocity carries one power of the scaling. -/
def velocityWeight : ℤ := 1

/-- Each gradient carries one more. -/
def gradientWeight : ℤ := 1

/-- The vorticity is a curl, so it carries the velocity's weight plus a gradient's.  Derived, not
declared: this is the one row that decides the section. -/
def vorticityWeight : ℤ := velocityWeight + gradientWeight

/-- Integrating over three spatial dimensions subtracts three from a density's weight. -/
def integralWeight (d : ℤ) : ℤ := d - 3

/-- **The helicity sits at the invariant grain and the energy does not.**

The energy density has weight `2` and its integral weight `−1`: the energy is supercritical, which
is the whole reason it is the wrong reading to refine.  The helicity density has weight
`1 + 2 = 3` and its integral weight `0`: exactly scale-invariant.  The cubic density has weight
`3` and integral weight `0` too — the critical norm.

So the defect of the helicity reading is *not* that it sits at the wrong grain.  It sits at the
right one and is a signed net; that is a different defect, and it is the one section 4 makes
exact. -/
theorem theHelicityWeightIsZeroAndTheEnergyWeightIsMinusOne :
    integralWeight (velocityWeight + vorticityWeight) = 0 ∧
      integralWeight (2 * velocityWeight) = -1 ∧
      integralWeight (3 * velocityWeight) = 0 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [integralWeight, velocityWeight, vorticityWeight, gradientWeight]

/-! ## 4. A signed crossing population, its two arms, and its net

The carrier is a finite table of addressed signed crossings.  There is no geometry here: the
projection that would produce such a table from filaments in `ℚ³` is not built, and the table is
declared. -/

/-- The hand of a crossing.  Two values, and the sign is the reading of them — never the carrier,
so the population can be asked what it holds after the sign has been taken. -/
inductive CrossingHand where
  /-- The strand turns with the declared orientation through this crossing. -/
  | withTheTurn
  /-- Against it. -/
  | againstTheTurn
  deriving DecidableEq, Repr

/-- Three strands: the material the Borromean table needs, and no more. -/
abbrev Strand := Fin 3

/-- One crossing, retained **by address**: which strand passes over, which under, at what site,
with which hand. -/
structure Crossing where
  /-- The strand that passes over. -/
  overStrand : Strand
  /-- The strand that passes under. -/
  underStrand : Strand
  /-- The address of the crossing.  Distinct crossings sit at distinct sites. -/
  site : ℕ
  /-- The hand. -/
  hand : CrossingHand
  deriving DecidableEq, Repr

/-- A crossing **population**: the crossings, retained, not their count. -/
abbrev Population := List Crossing

/-- The sign of a hand.  This is where the turn is deleted; everything before this line still
holds it. -/
def handSign : CrossingHand → ℤ
  | .withTheTurn => 1
  | .againstTheTurn => -1

/-- Is this hand the one that turns with the orientation? -/
def isWith : CrossingHand → Bool
  | .withTheTurn => true
  | .againstTheTurn => false

/-- **The net** — the signed sum.  This is the arm a helicity-shaped reading returns. -/
def net (p : Population) : ℤ := (p.map fun c => handSign c.hand).sum

/-- **The population count** — the unsigned total.  The other arm. -/
def total (p : Population) : ℕ := p.length

/-- The crossings that turn with the orientation, retained by address. -/
def withArm (p : Population) : Population := p.filter fun c => isWith c.hand

/-- The crossings that turn against it, retained by address. -/
def againstArm (p : Population) : Population := p.filter fun c => !isWith c.hand

@[simp] theorem net_nil : net [] = 0 := rfl

@[simp] theorem net_cons (c : Crossing) (p : Population) :
    net (c :: p) = handSign c.hand + net p := by
  simp [net]

/-- **The net is the difference of the two arms.**  The population is prior; the net is one
reading of it. -/
theorem theNetIsTheDifferenceOfTheArms (p : Population) :
    net p = ((withArm p).length : ℤ) - ((againstArm p).length : ℤ) := by
  induction p with
  | nil => rfl
  | cons c p ih =>
      cases hc : c.hand <;>
        simp [withArm, againstArm, isWith, handSign, hc] at ih ⊢ <;>
        omega

/-- **The population is the sum of the two arms.**  The same two numbers, added instead of
subtracted — which is the entire difference between a net and a population. -/
theorem thePopulationIsTheSumOfTheArms (p : Population) :
    total p = (withArm p).length + (againstArm p).length := by
  induction p with
  | nil => rfl
  | cons c p ih =>
      cases hc : c.hand <;>
        simp [total, withArm, againstArm, isWith, hc] at ih ⊢ <;>
        omega

/-- **The net never exceeds the population.**

*Aside: this is `|Wr| ≤ ACN` at the finite grain — the signed crossing sum is bounded by the
unsigned crossing count.* -/
theorem theNetNeverExceedsThePopulation (p : Population) : (net p).natAbs ≤ total p := by
  rw [theNetIsTheDifferenceOfTheArms, thePopulationIsTheSumOfTheArms]
  omega

/-- **And it meets the population exactly when one arm is empty.**

The gap between the two readings is precisely cancellation: the net equals the population in
magnitude only where nothing cancelled.  So a net that is small says nothing at all about the
population unless one arm is known to be empty, and that is not a quantity — it is a condition on
the retained addresses. -/
theorem theNetMeetsThePopulationExactlyWhenOneArmIsEmpty (p : Population) :
    (net p).natAbs = total p ↔ withArm p = [] ∨ againstArm p = [] := by
  rw [theNetIsTheDifferenceOfTheArms, thePopulationIsTheSumOfTheArms,
    ← List.length_eq_zero_iff (l := withArm p), ← List.length_eq_zero_iff (l := againstArm p)]
  omega

/-! ## 5. The net carries no verdict about whether anything crossed -/

/-- The declared net family: one reading of a population, its signed sum. -/
def netFamily : Lines.ReceiverFamily Population ℤ where
  Index := Unit
  read := fun _ p => net p

/-- A cancelling pair: two crossings between the same two strands, at distinct addresses, with
opposite hands. -/
def cancellingPair : Population :=
  [⟨0, 1, 0, .withTheTurn⟩, ⟨1, 0, 1, .againstTheTurn⟩]

/-- **The net family is blind to whether anything crossed.**

The cancelling pair and the empty population return the same net, `0`, and differ in whether the
population is inhabited.  The blindness is not an artifact of a coarse encoding: the two arms are
both present in the first and both absent in the second, and the reading deletes exactly that. -/
theorem theNetFamilyIsBlindToWhetherAnythingCrossed :
    netFamily.Blind (fun p => total p ≠ 0) :=
  ⟨cancellingPair, [], by decide, by decide, fun _ => rfl⟩

/-- **Therefore no function of the net decides whether anything crossed.**

The barrier theorem of `Lines`, applied.  This is the sharp form of "the population is not the
net": not that the map from populations to nets fails to be injective — which could not have come
out otherwise — but that the *whole* net reading carries no verdict about the inhabitedness of
what it is a net of. -/
theorem theNetCarriesNoVerdictAboutWhetherAnythingCrossed :
    ¬ ∃ verdict : (netFamily.Index → ℤ) → Prop,
        ∀ p : Population, total p ≠ 0 ↔ verdict (fun i => netFamily.read i p) :=
  netFamily.blindFamilyCarriesNoVerdict _ theNetFamilyIsBlindToWhetherAnythingCrossed

/-! ## 6. Three strands: the pairwise linking readings, and the control that could have failed -/

/-- Does this crossing join the two named strands, in either order? -/
def meets (c : Crossing) (i j : Strand) : Bool :=
  (c.overStrand == i && c.underStrand == j) || (c.overStrand == j && c.underStrand == i)

/-- The pairwise linking reading: the net taken over the crossings joining two strands.

*Aside: the classical linking number is half this signed sum over the crossings between two
components; the factor is a normalization and is omitted, since every statement below is about
vanishing and about separation.* -/
def linkingNet (p : Population) (i j : Strand) : ℤ := net (p.filter fun c => meets c i j)

/-- The declared pairwise-linking family: one reading per ordered pair of strands. -/
def linkingFamily : Lines.ReceiverFamily Population ℤ where
  Index := Strand × Strand
  read := fun ij p => linkingNet p ij.1 ij.2

/-- **The Borromean crossing table.**  Six crossings; each of the three pairs of strands meets
twice, with opposite hands.

This is declared data.  That it is the crossing table of the standard six-crossing Borromean
diagram is an import (the alternating diagram `L6a4`), not a theorem: no projection of any curve
in `ℚ³` is computed anywhere in this file. -/
def borromeanTable : Population :=
  [ ⟨0, 1, 0, .withTheTurn⟩, ⟨1, 0, 1, .againstTheTurn⟩,
    ⟨0, 2, 2, .withTheTurn⟩, ⟨2, 0, 3, .againstTheTurn⟩,
    ⟨1, 2, 4, .withTheTurn⟩, ⟨2, 1, 5, .againstTheTurn⟩ ]

/-- The empty table: three strands and nothing between them. -/
def unlinkTable : Population := []

/-- **Every pairwise linking reading vanishes on the Borromean table, and the table holds six
crossings.**  The two facts together are the whole point: the readings are all zero and the thing
they read is not. -/
theorem theLinkingReadingsVanishWhileSixCrossingsStand :
    (∀ i j : Strand, linkingNet borromeanTable i j = 0) ∧ total borromeanTable = 6 := by
  refine ⟨?_, ?_⟩ <;> decide

/-- **Every pairwise reading of the Borromean table agrees with the empty table.**  All nine of
them, checked rather than asserted.  This is the separation half of the blindness below, taken out
so that it stands as its own statement. -/
theorem everyPairwiseReadingAgreesWithTheEmptyTable :
    ∀ ij : Strand × Strand,
      linkingNet borromeanTable ij.1 ij.2 = linkingNet unlinkTable ij.1 ij.2 := by
  decide

/-- **The pairwise-linking family is blind to whether anything crossed.**

All nine readings agree between the Borromean table and the empty one, and the two differ in
whether the population is inhabited.  So the blindness of section 5 is not a consequence of having
declared only one reading: adjoining a reading for every ordered pair of strands does not break
it. -/
theorem theLinkingFamilyIsBlindToWhetherAnythingCrossed :
    linkingFamily.Blind (fun p => total p ≠ 0) :=
  ⟨borromeanTable, unlinkTable, by decide, by decide,
    everyPairwiseReadingAgreesWithTheEmptyTable⟩

/-- **Therefore no function of the pairwise linking readings decides whether anything crossed.** -/
theorem theLinkingCarriesNoVerdictAboutWhetherAnythingCrossed :
    ¬ ∃ verdict : (linkingFamily.Index → ℤ) → Prop,
        ∀ p : Population, total p ≠ 0 ↔ verdict (fun i => linkingFamily.read i p) :=
  linkingFamily.blindFamilyCarriesNoVerdict _ theLinkingFamilyIsBlindToWhetherAnythingCrossed

/-- The same table with one hand flipped: the second crossing now turns with the orientation. -/
def borromeanSameHandVariant : Population :=
  [ ⟨0, 1, 0, .withTheTurn⟩, ⟨1, 0, 1, .withTheTurn⟩,
    ⟨0, 2, 2, .withTheTurn⟩, ⟨2, 0, 3, .againstTheTurn⟩,
    ⟨1, 2, 4, .withTheTurn⟩, ⟨2, 1, 5, .againstTheTurn⟩ ]

/-- **The control: the declared hands decide the class, and varying one moves the tables apart.**

Flipping a single hand makes the first pairwise reading return `2`, and the linking family
separates the variant from the empty table.  So the vanishing proved above is a consequence of the
declared data rather than a restatement of it, and the blindness theorem is not a check whose
material could not have varied the property under test. -/
theorem theFlippedHandIsSeparatedByTheLinkingFamily :
    linkingFamily.Separates borromeanSameHandVariant unlinkTable := by
  refine ⟨(0, 1), ?_⟩
  decide

/-! ## 7. Two move families: what ratchets, and what refuses to -/

/-- A **reconnection**: remove the crossing at one address. -/
def reconnect (p : Population) (s : ℕ) : Population := p.filter fun c => !(c.site == s)

/-- What the reconnection discarded, retained by address rather than deleted. -/
def remainder (p : Population) (s : ℕ) : Population := p.filter fun c => c.site == s

/-- **A reconnection retains its remainder exactly.**

Both arms reconstruct: the totals add and the nets add.  This is a partition identity and is
stated as one — the content is not that the arithmetic works but that the discarded branch is kept
at its address, so the compression can be reopened. -/
theorem theReconnectionRetainsItsRemainderExactly (p : Population) (s : ℕ) :
    total (reconnect p s) + total (remainder p s) = total p ∧
      net (reconnect p s) + net (remainder p s) = net p := by
  induction p with
  | nil => exact ⟨rfl, rfl⟩
  | cons c p ih =>
      obtain ⟨ih₁, ih₂⟩ := ih
      by_cases h : c.site = s <;>
        simp [reconnect, remainder, total, h] at ih₁ ih₂ ⊢ <;>
        omega

/-- The declared reconnection of a cancelling pair of crossings at two consecutive addresses. -/
def reconnectPair (p : Population) (s : ℕ) : Population := reconnect (reconnect p s) (s + 1)

/-- **The population ratchets while every reading stands still.**

Three reconnections take the Borromean table `6 → 4 → 2 → 0`, and at every one of the four stages
all nine pairwise linking readings are zero.  The net receiver reports that nothing happened,
four times, while the population is emptied. -/
theorem thePopulationRatchetsWhileEveryReadingStandsStill :
    total borromeanTable = 6 ∧
      total (reconnectPair borromeanTable 0) = 4 ∧
      total (reconnectPair (reconnectPair borromeanTable 0) 2) = 2 ∧
      total (reconnectPair (reconnectPair (reconnectPair borromeanTable 0) 2) 4) = 0 ∧
      ∀ i j : Strand,
        linkingNet borromeanTable i j = 0 ∧
          linkingNet (reconnectPair borromeanTable 0) i j = 0 ∧
          linkingNet (reconnectPair (reconnectPair borromeanTable 0) 2) i j = 0 ∧
          linkingNet (reconnectPair (reconnectPair (reconnectPair borromeanTable 0) 2) 4) i j
            = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- The **representational** move: insert a cancelling pair of crossings between two strands at a
fresh pair of addresses.  Nothing about the configuration changes; the diagram does. -/
def insertCancellingPair (p : Population) (i j : Strand) (s : ℕ) : Population :=
  ⟨i, j, s, .withTheTurn⟩ :: ⟨j, i, s + 1, .againstTheTurn⟩ :: p

/-- **A cancelling pair is invisible to every linking reading.**

Whatever pair of strands the reading is taken over, the two inserted crossings are kept together
by the filter or dropped together — meeting is symmetric in the two strands of a crossing — and
their signs then cancel.  Stated for every population, every inserted pair and every reading, not
only for the table below. -/
theorem theInsertedPairIsInvisibleToEveryLinkingReading
    (p : Population) (i j : Strand) (s : ℕ) (a b : Strand) :
    linkingNet (insertCancellingPair p i j s) a b = linkingNet p a b := by
  have hsym : meets ⟨j, i, s + 1, CrossingHand.againstTheTurn⟩ a b
      = meets ⟨i, j, s, CrossingHand.withTheTurn⟩ a b := by
    simp only [meets]
    cases hia : (i == a) <;> cases hib : (i == b) <;> cases hja : (j == a) <;>
      cases hjb : (j == b) <;> simp
  simp only [linkingNet, insertCancellingPair, List.filter_cons, hsym]
  cases hm : meets ⟨i, j, s, CrossingHand.withTheTurn⟩ a b <;> simp [handSign]

/-- **The population is not invariant under it, and that is the control.**

The inserted pair takes the Borromean table from six crossings to eight while every reading stands
still.  So the ratchet of the previous theorem is monotone under the declared reconnection family
and provably **not** invariant under the representational one, and any monotonicity claim about a
crossing population owes this witness.

The consequence is the honest boundary of the whole construction: the population is a reading of a
*diagram*, and making it a reading of the configuration costs a minimization or a limit that this
file does not supply. -/
theorem theInsertedPairMovesThePopulationAndNoReading :
    total (insertCancellingPair borromeanTable 0 1 6) = 8 ∧
      net (insertCancellingPair borromeanTable 0 1 6) = net borromeanTable ∧
      ∀ i j : Strand,
        linkingNet (insertCancellingPair borromeanTable 0 1 6) i j
          = linkingNet borromeanTable i j := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-! ## 8. The demand this file does not meet -/

/-- **The reading that would survive the moves and still separate the tables.**

Parameterized by an isotopy relation, because this file constructs none: there is no planar
diagram here and therefore no Reidemeister move, only the one representational move of section 7.
For the genuine relation this is a substantive demand, and classically it is met — Milnor's
triple linking number is `±1` on the Borromean rings and `0` on the unlink, and the Jones
polynomial of `L6a4` is not that of the three-component unlink.  It is **not** met here, and the
missing piece is exactly an adapter from a crossing to a move — the absence `canon/TABLET_THE_TURN.md`
§13.3 already records for the Rust side, re-measured there 2026-08-15.

Stated as a demand rather than as an open question: the mathematics is known; the construction is
absent. -/
def ATangleReadingSeparatesWhatTheLinkingNumbersCannot
    (Isotopy : Population → Population → Prop) : Prop :=
  ∃ f : Population → ℤ,
    (∀ p q : Population, Isotopy p q → f p = f q) ∧ f borromeanTable ≠ f unlinkTable

/-! ## 9. What is here and what is not

Sections 1 to 3 are exact algebra over `ℚ` on three-component vectors and integer weights.
Sections 4 to 7 are exact combinatorics on a finite declared table.  No fluid, no solution, no
link, and no conjecture is formalized anywhere in this file.

The three blindness theorems are the load-bearing content, and each is an instance of one
abstract theorem that lives in `Lines`: a declared family that fails to separate a distinguished
pair carries no verdict about the property distinguishing it.  Applied here to the helicity density
against the Lamb vector, to the one-reading net family against the crossing population, and to the
nine-reading pairwise-linking family against the same population — the third being the one that
shows the blindness is not an artifact of having declared too few readings.

What would falsify the reading that occasioned this file is stated in the header and is not
formalizable at this grain.  What would falsify the file itself is smaller and sharper: if the
declared Borromean table had a nonzero pairwise reading the blindness witness would not be a
witness, and if the inserted pair did not raise the population the model would be
misimplemented.  Both are decided above, by `decide`. -/

end Soma.Holonics.Millennium.Crossings

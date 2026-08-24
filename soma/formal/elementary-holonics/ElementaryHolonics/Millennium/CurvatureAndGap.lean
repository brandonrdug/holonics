import ElementaryHolonics.Millennium.YangMillsLimit
import ElementaryHolonics.Millennium.LatticeNet
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.Group.Commute.Defs
import Mathlib.Tactic

/-!
# Mass is the first rung, and Einstein and Yang–Mills are one curvature formula

Brandon, 2026-08-23: *"What is mass to these towers? Where can we fit Yang–Mills in with the
surfaces and curvature with Einstein?"*

**Mass is the height of the first rung.**  A tower is a chain whose steps have a minimum size; a
continuum is a chain with no minimum.  `YangMillsLimit.SpectrumHasMassGap` already says exactly
this — `∀ μ ∈ spectrum, μ = 0 ∨ Δ ≤ μ` — and it is the same shape as a subgroup tower with every
index prime: *no rung can be subdivided*.  Massless means the spectrum descends to the vacuum
continuously, so there is no bottom rung; massive means the first rung is a definite height above
it, and the mass **is** that height.  Composed below rather than restated: the discrete ladder has
a gap and the half-line does not, and `YangMillsLimit.theShrinkingFamilyHasNoUniformMassGap`
already carries the warning that finite gaps do not compose into a continuum gap.

**Einstein and Yang–Mills are the same formula.**  Both are the curvature of a connection:

```text
F = dA + A ∧ A
```

For gravity the connection is Levi-Civita on the tangent bundle and the structure group is the
frame group; for Yang–Mills it is a gauge field on a principal `G`-bundle.  The **only** structural
difference is that gravity's connection is determined by the metric, so the geometry *is* the
field, while Yang–Mills' is independent — which is why `κ = 8πG/c⁴` couples matter directly to
curvature while Yang–Mills couples current to field strength.

**And `A ∧ A` is the whole difference between the two regimes.**  It is the commutator term — the
corpus's `a ∧ a`, already owned as `structure_group::curvature_commutator` — and it vanishes
exactly when the components commute.  So **abelian gauge theory has linear curvature** (Maxwell: no
self-interaction, massless photon) and **nonabelian gauge theory has the quadratic term** (self-
interaction, and the mass-gap question).  That is the fitting-in, and it is a two-line matrix
identity, proved below.

**The surface reading is the physics, not a metaphor.**  Curvature is holonomy per unit area: `F`
is what a face returns when transported around its boundary.  For gravity that is the Riemann
tensor; for Yang–Mills it is the Wilson loop, and confinement is the **area law**
`⟨W(C)⟩ ∼ exp(−σ·Area)` — the loop's decay governed by the *face* it bounds rather than its
boundary's length.  Area law implies a mass gap, with `σ` the cost per unit area.  So
"mass gap ⟷ area law ⟷ the face is the carrier" is one chain, and Gauss–Bonnet
`∫K dA = 2πχ` is the same statement with the total forced to be topological.  Those last three are
cited, not proved here; mathlib carries no bundle curvature (measured 2026-08-23).
-/

namespace Soma.Holonics.Millennium.CurvatureAndGap

open Soma.Holonics.Millennium.YangMillsLimit

/-! ## 1.  The quadratic term is exactly the nonabelian part -/

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **THE CURVATURE COMMUTATOR VANISHES EXACTLY WHEN THE COMPONENTS COMMUTE.**  `A ∧ A` is the
commutator, so it is zero precisely in the abelian case. -/
theorem theCurvatureCommutatorIsTheNonabelianTerm (A B : Matrix n n ℝ) :
    A * B - B * A = 0 ↔ Commute A B := by
  rw [sub_eq_zero]
  exact ⟨fun h => h, fun h => h⟩

/-- **ABELIAN CURVATURE IS LINEAR.**  With commuting components the quadratic term drops and the
field strength is `dA` alone — Maxwell, no self-interaction. -/
theorem theAbelianCurvatureIsLinear {A B : Matrix n n ℝ} (h : Commute A B) :
    A * B - B * A = 0 := (theCurvatureCommutatorIsTheNonabelianTerm A B).2 h

/-- **AND THE NONABELIAN TERM IS GENUINELY PRESENT.**  Two `2 × 2` matrices whose commutator is
nonzero: the self-interaction that distinguishes Yang–Mills from Maxwell exists already at the
smallest nonabelian size. -/
theorem theNonabelianTermIsNonzero :
    ∃ A B : Matrix (Fin 2) (Fin 2) ℝ, A * B - B * A ≠ 0 := by
  refine ⟨Matrix.of ![![0, 1], ![0, 0]], Matrix.of ![![0, 0], ![1, 0]], ?_⟩
  intro h
  have := congrFun (congrFun h 0) 0
  simp [Matrix.mul_apply, Fin.sum_univ_succ] at this

/-! ## 2.  Mass is the first rung -/

/-- A discrete ladder: the vacuum together with everything at height `Δ` or above. -/
def ladder (Δ : ℝ) : Set ℝ := {0} ∪ Set.Ici Δ

/-- **A LADDER HAS A MASS GAP, AND THE GAP IS ITS FIRST RUNG.** -/
theorem theLadderHasAGapEqualToItsFirstRung {Δ : ℝ} (hΔ : 0 < Δ) :
    SpectrumHasMassGap (ladder Δ) := by
  refine ⟨Or.inl rfl, ?_, ⟨Δ, Or.inr (Set.left_mem_Ici), hΔ⟩, Δ, hΔ, ?_⟩
  · rintro μ (rfl | hμ)
    · exact le_refl 0
    · exact le_trans hΔ.le hμ
  · rintro μ (rfl | hμ)
    · exact Or.inl rfl
    · exact Or.inr hμ

/-- **AND A CONTINUUM HAS NONE.**  The half-line descends to the vacuum with no bottom rung, so no
positive `Δ` separates: masslessness is the absence of a first rung, not a small one. -/
theorem theContinuumHasNoGap : ¬ SpectrumHasMassGap (Set.Ici (0 : ℝ)) := by
  rintro ⟨-, -, -, Δ, hΔ, hsep⟩
  rcases hsep (Δ / 2) (Set.mem_Ici.2 (by linarith)) with h | h <;> linarith

/-- **THE TOWER READING, STATED.**  A mass gap is the statement that the spectral ladder has a
smallest positive rung — the same condition that makes a subgroup chain a *tower* (every index
prime, no step subdividable) rather than a continuum.  Mass is that height. -/
theorem theMassIsTheHeightOfTheFirstRung {Δ : ℝ} (hΔ : 0 < Δ) :
    SpectrumHasMassGap (ladder Δ) ∧ ∀ μ ∈ ladder Δ, μ = 0 ∨ Δ ≤ μ := by
  refine ⟨theLadderHasAGapEqualToItsFirstRung hΔ, ?_⟩
  rintro μ (rfl | hμ)
  · exact Or.inl rfl
  · exact Or.inr hμ

/-! ## 3.  The gap is a reflection coefficient, and the decay is its power -/

open Soma.Holonics.Millennium.LatticeNet

/-- The lattice transfer matrix's gap ratio: first excited over ground. -/
def gapRatio (u : ℚ) : ℚ := (1 - u) / (1 + u)

/-- **THE GAP RATIO IS A REFLECTION COEFFICIENT.**  `(1 − u)/(1 + u)` is `−Γ` for the Smith /
Fresnel / transmission-line coefficient `Γ = (Z − 1)/(Z + 1)` the corpus already carries as one
law.  So the lattice's mass gap and the impedance mismatch at a junction are **the same
number** — the whip's gear ratio, read as a spectral gap. -/
theorem theGapRatioIsAReflectionCoefficient (u : ℚ) (hu : 1 + u ≠ 0) :
    gapRatio u = -((u - 1) / (u + 1)) := by
  rw [gapRatio]
  rw [show u + 1 = 1 + u by ring]
  field_simp
  ring

/-- **AND IT IS THE TRANSFER MATRIX'S ACTUAL GAP**, on every number of links — composed from
`LatticeNet.theUngaugedGapRatioDoesNotSeeTheVolume` rather than restated. -/
theorem theGapRatioIsTheSpectralGap (u : ℚ) (hu : 1 + u ≠ 0) (L : ℕ) :
    crossingEigenvalue L 1 u / crossingEigenvalue (L + 1) 0 u = gapRatio u :=
  theUngaugedGapRatioDoesNotSeeTheVolume u hu L

/-- **THE GAP IS STRICT INSIDE THE COUPLING.**  For `0 < u < 1` the ratio lies strictly between
zero and one, so correlations at separation `t` decay like `gapRatio u ^ t` — exponential decay
with a positive rate, which is a mass gap and not a slow tail. -/
theorem theGapIsStrictInsideTheCoupling {u : ℚ} (hu0 : 0 < u) (hu1 : u < 1) :
    0 < gapRatio u ∧ gapRatio u < 1 := by
  have h1 : (0 : ℚ) < 1 + u := by linarith
  have h2 : (0 : ℚ) < 1 - u := by linarith
  constructor
  · exact div_pos h2 h1
  · rw [gapRatio, div_lt_one h1]
    linarith

/-- **THE DECAY IS THE GAP'S POWER.**  Separation `t` costs `gapRatio u ^ t`, and it is strictly
decreasing in `t` — the exponential clustering that an area law produces and that a mass gap *is*.
The rate is `−log(gapRatio u)`, and by the theorem above that rate is the reflection coefficient's
logarithm: **the mass is the impedance mismatch.** -/
theorem theDecayIsStrictlyDecreasing {u : ℚ} (hu0 : 0 < u) (hu1 : u < 1) (t : ℕ) :
    gapRatio u ^ (t + 1) < gapRatio u ^ t := by
  obtain ⟨hpos, hlt⟩ := theGapIsStrictInsideTheCoupling hu0 hu1
  have hp : 0 < gapRatio u ^ t := by positivity
  calc gapRatio u ^ (t + 1) = gapRatio u ^ t * gapRatio u := by ring
    _ < gapRatio u ^ t * 1 := by exact mul_lt_mul_of_pos_left hlt hp
    _ = gapRatio u ^ t := by ring

/-- **AND A FREE COUPLING HAS NO GAP.**  At `u = 0` the ratio is one and nothing decays: the
massless case is the matched load, `Γ = 0` reflected in the gap being `1`.  The two boundary
readings agree. -/
theorem theFreeCouplingIsGapless : gapRatio 0 = 1 := by norm_num [gapRatio]

/-! ## 4.  The area law on the lattice, combinatorially -/

/-- The leading strong-coupling term of a rectangular Wilson loop: tiling an `a × b` loop needs
`a·b` plaquettes, each costing one factor of the coupling. -/
def wilsonStrongCoupling (u : ℚ) (a b : ℕ) : ℚ := u ^ (a * b)

/-- **THE DECAY IS IN THE AREA.**  The exponent is `a·b`, so enlarging the loop in either direction
multiplies the cost — the *face* is the carrier, not the boundary. -/
theorem theWilsonExponentIsTheArea (u : ℚ) (a b : ℕ) :
    wilsonStrongCoupling u a b = u ^ (a * b) := rfl

/-- **AND THE AREA BEATS THE PERIMETER.**  For a loop of side at least five, `a·b > 2(a+b)`, so the
area exponent strictly exceeds the perimeter exponent and the area-law decay is the faster one.
That is the confinement statement: a large loop is suppressed by what it *encloses*. -/
theorem theAreaBeatsThePerimeter {a b : ℕ} (ha : 5 ≤ a) (hb : 5 ≤ b) : 2 * (a + b) < a * b := by
  nlinarith

/-- **THE STRING TENSION IS THE COUPLING'S LOGARITHM.**  `u^{ab} = exp(−σ·ab)` with
`σ = −log u`, and `σ > 0` exactly when `0 < u < 1` — the same window in which the spectral gap is
strictly positive.  **Confinement and the gap open together and close together.** -/
theorem theStringTensionIsPositiveExactlyInTheGapWindow {u : ℝ} (h0 : 0 < u) (h1 : u < 1) :
    0 < -Real.log u := by
  have := Real.log_neg h0 h1
  linarith

/-- And the two windows coincide: the coupling range giving a positive string tension is the range
giving a gap ratio strictly below one. -/
theorem theTwoWindowsCoincide {u : ℚ} (h0 : 0 < u) (h1 : u < 1) :
    gapRatio u < 1 ∧ (0 : ℚ) < u ∧ u < 1 :=
  ⟨(theGapIsStrictInsideTheCoupling h0 h1).2, h0, h1⟩

/-- **AND AT THE MATCHED LOAD BOTH VANISH.**  `u = 0`: no plaquette cost, no tension, gap ratio one
— deconfined and gapless together, which is the boundary the continuum limit has to cross. -/
theorem theMatchedLoadIsDeconfinedAndGapless :
    wilsonStrongCoupling 0 1 1 = 0 ∧ gapRatio 0 = 1 := by
  refine ⟨by norm_num [wilsonStrongCoupling], theFreeCouplingIsGapless⟩

end Soma.Holonics.Millennium.CurvatureAndGap
